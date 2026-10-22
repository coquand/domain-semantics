{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- MIN.Syntax.ConfluenceTest
--
-- Non-vacuity checks for MIN.Syntax.Confluence: concrete reductions and
-- a genuine diamond (one where the two one-step reducts really differ,
-- because the contracted redex duplicates its argument), joined by the
-- proof of Church-Rosser, and a chain of two beta conversions whose
-- common reducts genuinely differ, so that transitivity has to invoke
-- confluence.  Everything is checked by `refl`, so the witnesses really
-- are the terms named below.
------------------------------------------------------------------------

module MIN.Syntax.ConfluenceTest where

open import MIN.Domain.Basic using (Nat ; suc ; Eq ; refl ; fst ; snd ; mkSigma ; Pair ; Empty)
open import MIN.Syntax.Raw using (Fin ; fzero ; fsuc ;
  Expr ; Var ; U ; Pi ; Lam ; App)
open import MIN.Syntax.Confluence

------------------------------------------------------------------------
-- Two free variables to compute with
------------------------------------------------------------------------

a : Expr 2
a = Var fzero

b : Expr 2
b = Var (fsuc fzero)

------------------------------------------------------------------------
-- Test 1.  K a b  reduces to  a  in two steps
--
-- The domain annotations are irrelevant to beta reduction, so `U` is
-- used throughout.
------------------------------------------------------------------------

K : Expr 2
K = Lam U (Lam U (Var (fsuc fzero)))

test-K : Beta (App (App K a) b) a
test-K = beta-step (beta-App1 beta) (beta-step beta beta-refl)

------------------------------------------------------------------------
-- Test 2.  A real diamond
--
--   D = \x. x x        I = \x. x
--
--   tm = D (I a)  reduces in one step both to  (I a) (I a)  and to  D a,
--   and these two terms are distinct.  Both reduce to  a a.
------------------------------------------------------------------------

D : Expr 2
D = Lam U (App (Var fzero) (Var fzero))

I : Expr 2
I = Lam U (Var fzero)

tm : Expr 2
tm = App D (App I a)

-- contracting the outer redex duplicates the argument
step-out : Beta1 tm (App (App I a) (App I a))
step-out = beta

-- contracting the inner redex does not
step-in : Beta1 tm (App D a)
step-in = beta-App2 beta

-- the two reducts are joined at  a a
join-left : Beta (App (App I a) (App I a)) (App a a)
join-left = beta-step (beta-App1 beta) (beta-step (beta-App2 beta) beta-refl)

join-right : Beta (App D a) (App a a)
join-right = beta-step beta beta-refl

-- and the proof of confluence finds a common reduct of its own
diamond : CommonBeta (App (App I a) (App I a)) (App D a)
diamond = Beta-confluent (Beta-one step-out) (Beta-one step-in)

test-diamond : Eq (fst diamond) (App a a)
test-diamond = refl

------------------------------------------------------------------------
-- Test 3.  Church-Rosser applied to a conversion built by hand
--
--   (I a) (I a)  =  D a   is derivable in Conv without ever mentioning
--   a common reduct; church-rosser produces one.
------------------------------------------------------------------------

-- the middle term of the zig-zag is `tm` itself; its implicit arguments
-- are given, since transitivity does not determine them
cnv : Conv (App (App I a) (App I a)) (App D a)
cnv =
  conv-trans
    (conv-sym (conv-beta {A = U} {M = App (Var fzero) (Var fzero)} {N = App I a}))
    (conv-App conv-refl (conv-beta {A = U} {M = Var fzero} {N = a}))

test-cr : Eq (fst (church-rosser cnv)) (App a a)
test-cr = refl

------------------------------------------------------------------------
-- Test 4.  Transitivity of beta conversion really needs confluence
--
-- Two conversions are chained whose common reducts are DIFFERENT terms:
--
--     (I a) (I a)     D a     I (D a)
--              \      / \      /
--               v    v   v    v
--                 a a       D a
--
-- so the middle terms  a a  and  D a  cannot simply be identified, and
-- BConv-trans has to call Beta-confluent at  D a  to close the square.
-- It does, and the reduct it produces is  a a.
------------------------------------------------------------------------

-- (I a) (I a)  and  D a  meet at  a a
cnv1 : BConv (App (App I a) (App I a)) (App D a)
cnv1 = mkSigma (App a a) (mkSigma join-left join-right)

-- D a  and  I (D a)  meet at  D a
cnv2 : BConv (App D a) (App I (App D a))
cnv2 = mkSigma (App D a) (mkSigma beta-refl (Beta-one beta))

-- the two meeting points are not the same term
test-middles-differ : Eq (fst cnv1) (App a a)
test-middles-differ = refl

test-middles-differ2 : Eq (fst cnv2) (App D a)
test-middles-differ2 = refl

-- and transitivity still produces a common reduct
cnv3 : BConv (App (App I a) (App I a)) (App I (App D a))
cnv3 = BConv-trans cnv1 cnv2

test-trans : Eq (fst cnv3) (App a a)
test-trans = refl

------------------------------------------------------------------------
-- Test 5.  Reflexivity, symmetry, and agreement with Conv
------------------------------------------------------------------------

test-refl : Eq (fst (BConv-refl {M = tm})) tm
test-refl = refl

test-sym : Eq (fst (BConv-sym cnv1)) (App a a)
test-sym = refl

-- BConv and Conv are interderivable
test-to-Conv : Conv (App (App I a) (App I a)) (App I (App D a))
test-to-Conv = BConv-Conv cnv3

test-from-Conv : Eq (fst (Conv-BConv test-to-Conv)) (App a a)
test-from-Conv = refl

------------------------------------------------------------------------
-- Test 6.  Normal forms
--
-- `NF` is a negative definition, so it is worth checking on both sides
-- that it says what it should: that it is inhabited on terms that are
-- visibly normal, and refutable on a term that is visibly not.
------------------------------------------------------------------------

-- (NF-U is in MIN.Syntax.Confluence, where Conv-U-Pi needs it)
NF-Var : {n : Nat} {i : Fin n} -> NF (Var i)
NF-Var _ ()

-- a a  is normal: neither side of the application can move, and the
-- application itself is not a redex because  a  is not a Lam
NF-aa : NF (App a a)
NF-aa _ (beta-App1 s) = NF-Var _ s
NF-aa _ (beta-App2 s) = NF-Var _ s

-- tm = D (I a)  is not normal
not-NF-tm : NF tm -> Empty
not-NF-tm nf = nf _ step-out

------------------------------------------------------------------------
-- Test 7.  Uniqueness of normal forms, on the diamond of Test 2
--
--   tm  reduces to  a a  by two different routes (through (I a)(I a)
--   and through D a).  NF-unique says the endpoints must coincide.
------------------------------------------------------------------------

route-left : Beta tm (App a a)
route-left = Beta-trans (Beta-one step-out) join-left

route-right : Beta tm (App a a)
route-right = Beta-trans (Beta-one step-in) join-right

-- the two routes are genuinely different: they pass through different
-- intermediate terms, and neither is a prefix of the other
test-routes-differ : Eq (fst (Beta-confluent (Beta-one step-out) (Beta-one step-in)))
                        (App a a)
test-routes-differ = refl

uniq : Eq (App a a) (App a a)
uniq = NF-unique route-left route-right NF-aa NF-aa

test-uniq : Eq uniq refl
test-uniq = refl

-- and via convertibility, which is the general form
uniq-conv : Eq (App a a) (App a a)
uniq-conv = NF-unique-Conv conv-refl NF-aa NF-aa

test-uniq-conv : Eq uniq-conv refl
test-uniq-conv = refl

------------------------------------------------------------------------
-- Test 8.  Injectivity of Pi
--
--   P1 = Pi (I a) (I' x)      P2 = Pi a x
--
-- with both components genuine redexes, so the two products are
-- convertible without being equal.
------------------------------------------------------------------------

I3 : Expr 3
I3 = Lam U (Var fzero)

-- a redex in the codomain, reducing to  x = Var fzero
B1 : Expr 3
B1 = App I3 (Var fzero)

P1 : Expr 2
P1 = Pi (App I a) B1

P2 : Expr 2
P2 = Pi a (Var fzero)

cPi : Conv P1 P2
cPi =
  conv-Pi (conv-beta {A = U} {M = Var fzero} {N = a})
          (conv-beta {A = U} {M = Var fzero} {N = Var fzero})

-- injectivity gives back the component conversions
test-pi-inj : Pair (Conv (App I a) a) (Conv B1 (Var fzero))
test-pi-inj = Pi-inj cPi

-- and in the sharp form, the components' common reducts are named
test-pi-domain : Eq (fst (fst (Pi-inj-BConv cPi))) a
test-pi-domain = refl

test-pi-codomain : Eq (fst (snd (Pi-inj-BConv cPi))) (Var fzero)
test-pi-codomain = refl

------------------------------------------------------------------------
-- Test 9.  Why induction on the Conv derivation cannot work
--
-- The same two products, but converted through the middle term
--
--     mid = I (Pi a x)
--
-- which is NOT a product.  Any induction on the shape of the Conv
-- derivation loses the product form at that transitivity step; only
-- confluence recovers it.
------------------------------------------------------------------------

mid : Expr 2
mid = App I P2

detour : Conv P2 P2
detour =
  conv-trans (conv-sym (conv-beta {A = U} {M = Var fzero} {N = P2}))
             (conv-beta {A = U} {M = Var fzero} {N = P2})

cPi2 : Conv P1 P2
cPi2 = conv-trans cPi detour

test-pi-detour : Eq (fst (fst (Pi-inj-BConv cPi2))) a
test-pi-detour = refl

test-pi-inj-detour : Pair (Conv (App I a) a) (Conv B1 (Var fzero))
test-pi-inj-detour = Pi-inj cPi2

------------------------------------------------------------------------
-- Test 10.  A universe is never convertible to a product
------------------------------------------------------------------------

test-U-not-Pi : Conv (U {2}) P2 -> Empty
test-U-not-Pi = Conv-U-Pi
