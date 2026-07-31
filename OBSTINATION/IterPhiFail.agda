{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.IterPhiFail
--
-- A COUNTEREXAMPLE.  For mutual iteration, the case-3 witness phi need be
-- neither eventually constant nor strictly increasing -- so `Property.PhiOK`
-- (= `Or (ConstFrom k phi) (StrictIncFrom k phi)`) is FALSE in the mutual
-- setting, and the ultimate-obstination property cannot be ported to
-- mutual iteration with its Case 3 unchanged.
--
-- The block (r = 2, no parameters), with both step components ordinary PR
-- projections/successor -- as simple as a mutual block can be:
--
--   f_1(0) = 0            f_1(S(x)) = f_2(x)
--   f_2(0) = 0            f_2(S(x)) = S(f_1(x))
--
-- i.e. the step is  H<z_1,z_2> = <z_2, S(z_1)> = <evalF (proj 1), evalF succ>.
-- Extensionally f_1 = floor(n/2), f_2 = ceil(n/2).
--
-- Iterating from <bot,bot> gives (`iterate-formula`)
--
--   iterVec (S^m(bot)) = < S^{half m}(bot) , S^{half (m+1)}(bot) >
--
-- so the case-3 witness of the first component is  phi_1(m) = floor(m/2):
--
--   m      : 0 1 2 3 4 5 6 ...
--   phi_1 m: 0 0 1 1 2 2 3 ...
--
-- non-decreasing and unbounded, but it stalls on every other step, so it is
-- NOT strictly increasing from any threshold, and being unbounded it is not
-- eventually constant either (`notPhiOK`).
--
-- WHY THE UNARY PROOF DOES NOT SEE THIS.  For `prec g h` there is a single
-- chain and `USeq.uSeq-stab` forces it to be strictly increasing up to the
-- point where it stabilises and constant afterwards -- hence PhiOK.  With
-- two mutually defined components, `uVec-stab` constrains only the PAIR: one
-- component may stall while the other advances, and then resume.  That is
-- exactly the 0,0,1,1,2,2 pattern above.
--
-- WHAT SURVIVES.  The manuscript's own statement -- the SEQUENTIALITY INDEX
-- is eventually constant -- is untouched: here the index is constantly the
-- recursion argument.  What fails is the stronger phi-shape that
-- `Property.agda` records.  For `uoValue` (the point of Case 3: computing the
-- extension) all that is needed is
--
--   sup_m S^{phi(m)}(bot)  =  S^{sup phi}(bot) if phi bounded, else S^omega(bot)
--
-- so the repair is to weaken PhiOK from `Or ConstFrom StrictIncFrom` to
-- `Or (Bounded phi) (Unbounded phi)` for monotone phi -- which is what the
-- read-graph criterion of `IterGraph2` decides, and which `floor(m/2)`
-- satisfies (it is unbounded).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.IterPhiFail where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR using (PR ; proj ; succ ; evalF)
open import OBSTINATION.Property using (ConstFrom ; StrictIncFrom ; PhiOK)
open import OBSTINATION.StabExclude using (LeN-suc-not)
open import OBSTINATION.IterFun using (iterVec ; appF ; botF ; MonoT ; StableT)
open import OBSTINATION.Meet using (cons-eq)
open import OBSTINATION.Mono using (evalF-mono)
open import OBSTINATION.Stability using (stable)
open import OBSTINATION.Arity using (guard ; guard-mono ; guard-stable)
open import OBSTINATION.PropertyVec using (UOMall)
open import OBSTINATION.Prop1 using (AllWf)
open import OBSTINATION.PropertyVecTest using (evalTup ; block-UOM)

two : Nat
two = suc (suc zero)

------------------------------------------------------------------------
-- The block:  H<z1,z2> = <z2, S(z1)>,  base <0,0>
------------------------------------------------------------------------

Gc : FTup -> FTup
Gc Y = cons (fcpl zero) (cons (fcpl zero) nil)

-- component 0 reads recursion slot 1; component 1 is the successor of slot 0
Hc : FTup -> FTup
Hc X = cons (evalF (proj (suc zero)) X) (cons (evalF succ X) nil)

------------------------------------------------------------------------
-- halving
------------------------------------------------------------------------

half : Nat -> Nat
half zero                = zero
half (suc zero)          = zero
half (suc (suc m))       = suc (half m)

dbl : Nat -> Nat
dbl zero    = zero
dbl (suc j) = suc (suc (dbl j))

half-dbl : (j : Nat) -> Eq (half (dbl j)) j
half-dbl zero    = refl
half-dbl (suc j) = Eq-cong suc (half-dbl j)

half-suc-dbl : (j : Nat) -> Eq (half (suc (dbl j))) j
half-suc-dbl zero    = refl
half-suc-dbl (suc j) = Eq-cong suc (half-suc-dbl j)

half-le : (n : Nat) -> LeN (half n) n
half-le zero          = tt
half-le (suc zero)    = tt
half-le (suc (suc m)) =
  LeN-trans {half m} {m} {suc m} (half-le m) (LeN-suc m)

dbl-ge : (j : Nat) -> LeN j (dbl j)
dbl-ge zero    = tt
dbl-ge (suc j) =
  LeN-trans {j} {dbl j} {suc (dbl j)} (dbl-ge j) (LeN-suc (dbl j))

-- k <= dbl (suc k)
k-le-dbl-suc : (k : Nat) -> LeN k (dbl (suc k))
k-le-dbl-suc k =
  LeN-trans {k} {dbl k} {suc (suc (dbl k))} (dbl-ge k)
    (LeN-trans {dbl k} {suc (dbl k)} {suc (suc (dbl k))}
      (LeN-suc (dbl k)) (LeN-suc (suc (dbl k))))

------------------------------------------------------------------------
-- The iterates: < S^{half m}(bot) , S^{half (m+1)}(bot) >
--
-- The step is definitional: reading slot 1 shifts the second component into
-- the first, and the successor of slot 0 gives  suc (half m) = half (m+2).
------------------------------------------------------------------------

iterate-formula : (m : Nat) ->
  Eq (iterVec Gc Hc two (fbot m) nil)
     (cons (fbot (half m)) (cons (fbot (half (suc m))) nil))
iterate-formula zero    = refl
iterate-formula (suc m) = Eq-cong (\ Z -> Hc (appF Z nil)) (iterate-formula m)

-- the first few, by computation
check0 : Eq (iterVec Gc Hc two (fbot zero) nil)
            (cons (fbot zero) (cons (fbot zero) nil))
check0 = refl

check1 : Eq (iterVec Gc Hc two (fbot (suc zero)) nil)
            (cons (fbot zero) (cons (fbot (suc zero)) nil))
check1 = refl

check2 : Eq (iterVec Gc Hc two (fbot (suc (suc zero))) nil)
            (cons (fbot (suc zero)) (cons (fbot (suc zero)) nil))
check2 = refl

check3 : Eq (iterVec Gc Hc two (fbot (suc (suc (suc zero)))) nil)
            (cons (fbot (suc zero)) (cons (fbot (suc (suc zero))) nil))
check3 = refl

check4 : Eq (iterVec Gc Hc two (fbot (suc (suc (suc (suc zero))))) nil)
            (cons (fbot (suc (suc zero))) (cons (fbot (suc (suc zero))) nil))
check4 = refl

------------------------------------------------------------------------
-- phi_1 = half is neither eventually constant nor strictly increasing
------------------------------------------------------------------------

-- unbounded: half (dbl (k+1)) = k+1 > k >= half k
notConst : (k : Nat) -> ConstFrom k half -> Empty
notConst k cst = LeN-suc-not k (Eq-transport (\ z -> LeN z k) (Eq-sym e3) (half-le k))
  where
    e3 : Eq (suc k) (half k)
    e3 = Eq-trans (Eq-sym (half-dbl (suc k))) (cst (dbl (suc k)) (k-le-dbl-suc k))

-- it stalls at every even step: half (dbl k) = half (suc (dbl k)) = k
notInc : (k : Nat) -> StrictIncFrom k half -> Empty
notInc k sinc = LeN-suc-not k bad
  where
    s : LeN (suc (half (dbl k))) (half (suc (dbl k)))
    s = sinc (dbl k) (dbl-ge k)

    bad : LeN (suc k) k
    bad = Eq-transport (\ z -> LeN (suc z) k) (half-dbl k)
            (Eq-transport (\ z -> LeN (suc (half (dbl k))) z) (half-suc-dbl k) s)

-- hence: no threshold makes half a legal case-3 witness
notPhiOK : (k : Nat) -> PhiOK k half -> Empty
notPhiOK k (inl c) = notConst k c
notPhiOK k (inr s) = notInc k s

------------------------------------------------------------------------
-- The same for ANY phi that agrees with half above its threshold
--
-- Case 3 constrains phi only for m >= k, so ruling out `half` itself is
-- not enough: this is the statement that actually refutes Case 3 here.
------------------------------------------------------------------------

Agrees : Nat -> (Nat -> Nat) -> Set
Agrees k phi = (m : Nat) -> LeN k m -> Eq (phi m) (half m)

notConst-agree : (k : Nat) (phi : Nat -> Nat) ->
  Agrees k phi -> ConstFrom k phi -> Empty
notConst-agree k phi ag cst =
  LeN-suc-not k (Eq-transport (\ z -> LeN z k) (Eq-sym e4) (half-le k))
  where
    m0 : Nat
    m0 = dbl (suc k)

    km0 : LeN k m0
    km0 = k-le-dbl-suc k

    -- half m0 = phi m0 = phi k = half k
    e4 : Eq (suc k) (half k)
    e4 = Eq-trans (Eq-sym (half-dbl (suc k)))
           (Eq-trans (Eq-sym (ag m0 km0))
             (Eq-trans (cst m0 km0) (ag k (LeN-refl k))))

notInc-agree : (k : Nat) (phi : Nat -> Nat) ->
  Agrees k phi -> StrictIncFrom k phi -> Empty
notInc-agree k phi ag sinc = LeN-suc-not k bad
  where
    kd : LeN k (dbl k)
    kd = dbl-ge k

    ksd : LeN k (suc (dbl k))
    ksd = LeN-trans {k} {dbl k} {suc (dbl k)} kd (LeN-suc (dbl k))

    s : LeN (suc (phi (dbl k))) (phi (suc (dbl k)))
    s = sinc (dbl k) kd

    -- rewrite both sides through `Agrees`, then through half-dbl / half-suc-dbl
    bad : LeN (suc k) k
    bad =
      Eq-transport (\ z -> LeN (suc z) k) (half-dbl k)
        (Eq-transport (\ z -> LeN (suc (half (dbl k))) z) (half-suc-dbl k)
          (Eq-transport (\ z -> LeN (suc (half (dbl k))) z) (ag (suc (dbl k)) ksd)
            (Eq-transport (\ z -> LeN (suc z) (phi (suc (dbl k)))) (ag (dbl k) kd) s)))

notPhiOK-agree : (k : Nat) (phi : Nat -> Nat) ->
  Agrees k phi -> PhiOK k phi -> Empty
notPhiOK-agree k phi ag (inl c) = notConst-agree k phi ag c
notPhiOK-agree k phi ag (inr s) = notInc-agree k phi ag s

------------------------------------------------------------------------
-- THE BLOCK IS LEGITIMATE
--
-- Everything above used the raw `Hc`.  Here is the same block built from
-- the PR terms through the standard guard machinery, so that its joint
-- obstination is DERIVED from `Prop1.prop1` rather than assumed -- and the
-- iterates are unchanged, because the guard is transparent at length 2,
-- which is the only length at which the recursion applies it.
------------------------------------------------------------------------

ps : List PR
ps = cons (proj (suc zero)) (cons succ nil)

-- Wf (proj 1) 2 = LeN 2 2 = Top ; Wf succ 2 = LeN 1 2 = Top
awf : AllWf ps two
awf = mkSigma tt (mkSigma tt tt)

Hg : FTup -> FTup
Hg = evalTup two ps

-- joint obstination, straight out of Proposition 1
uoHg : UOMall Hg two
uoHg = block-UOM two ps awf

monoHg : MonoT Hg
monoHg le =
  mkSigma (guard-mono two (evalF (proj (suc zero))) (evalF-mono (proj (suc zero))) le)
    (mkSigma (guard-mono two (evalF succ) (evalF-mono succ) le) tt)

stableHg : StableT Hg
stableHg bd =
  cons-eq (guard-stable two (evalF (proj (suc zero))) (stable (proj (suc zero))) bd)
    (cons-eq (guard-stable two (evalF succ) (stable succ) bd) refl)

-- the guarded block has exactly the same iterates
iterate-formula-g : (m : Nat) ->
  Eq (iterVec Gc Hg two (fbot m) nil)
     (cons (fbot (half m)) (cons (fbot (half (suc m))) nil))
iterate-formula-g zero    = refl
iterate-formula-g (suc m) = Eq-cong (\ Z -> Hg (appF Z nil)) (iterate-formula-g m)
