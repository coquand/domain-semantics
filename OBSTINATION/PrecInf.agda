{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecInf
--
-- Primitive recursion at the INFINITE first argument, the assembly of the
-- fixpoint-sequence machinery towards  UO (prec g h) (cons inf Y).
--
-- Two pieces built here:
--
--   * `f-le-uSeq` (the BRIDGE): the finite-argument value
--       f(S^m(bot), X')  is dominated by the sequence term  u_m,
--     for every finite  X' <= Y.  Proof by induction on m: the step of
--     the sequence uses  S^omega(bot)  in h's first slot where f's
--     recursion uses only  S^{m-1}(bot),  so `ext-ub` (f A0 <= ext f A)
--     applied to  A0 = <S^{m-1}(bot), f(S^{m-1}(bot),X'), X'>  <=
--     A = <S^omega(bot), u_{m-1}, Y>  closes the induction.
--
--   * `prec-inf-Case1` (the COMPLETE sub-case of the first principal
--     case): if the limit is realised at a finite stage by a COMPLETE
--     value, f(S^n(bot), Y1) = S^p(0), then f is Case 1 at (S^omega(bot),
--     Y) -- directly, because a complete value is maximal.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecInf where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.ExtMono using (ext-ub)
open import OBSTINATION.USeq using (uSeq ; uSeq-stab)
open import OBSTINATION.USeqProp2 using (uSeq-prop2)
open import OBSTINATION.Extension using (embed-inj)
open import OBSTINATION.Prop1Base using (fcpl-max)
open import OBSTINATION.PrecFun using (RecData ; PF ; PF-mono)

module _ (rd : RecData) where
  open RecData rd

  ------------------------------------------------------------------------
  -- The bridge: finite-argument f is dominated by the sequence
  ------------------------------------------------------------------------

  f-le-uSeq : (Y : Tup)
    (m : Nat) (X' : FTup) -> Below X' Y ->
    LeD (embed (PF G H (cons (fbot m) X'))) (uSeq rd Y m)
  f-le-uSeq Y zero    X' bel = tt
  f-le-uSeq Y (suc m) X' bel =
    ext-ub H monoH uoh
      (cons inf (cons (uSeq rd Y m) Y))
      (cons (fbot m) (cons (PF G H (cons (fbot m) X')) X'))
      (mkSigma tt (mkSigma (f-le-uSeq Y m X' bel) bel))

  ------------------------------------------------------------------------
  -- First principal case, complete sub-case: a complete finite realiser
  -- gives Case 1 at the infinite point.
  ------------------------------------------------------------------------

  prec-inf-Case1 : (Y : Tup) (n : Nat) (Y1 : FTup) (p : Nat) ->
    Below Y1 Y -> Eq (PF G H (cons (fbot n) Y1)) (fcpl p) ->
    UO (PF G H) (cons inf Y)
  prec-inf-Case1 Y n Y1 p belY1 eqv =
    uo1 (mkSigma (cons (fbot n) Y1)
          (mkSigma (mkSigma tt belY1) (mkSigma p univ)))
    where
      univ : (X : FTup) -> LeFTup (cons (fbot n) Y1) X ->
             Eq (PF G H X) (fcpl p)
      univ X leX =
        fcpl-max p (PF G H X)
          (Eq-transport (\ z -> LeF z (PF G H X)) eqv
            (PF-mono G H monoG monoH {cons (fbot n) Y1} {X} leX))

  ------------------------------------------------------------------------
  -- From a stabilised sequence to a finite realiser of its (finite) limit
  ------------------------------------------------------------------------

  -- If the sequence has stabilised at k with (finite) limit value  embed w,
  -- then that value is realised exactly at a finite stage of f:
  --   f(S^n(bot), Y1) = w  for some  n  and finite  Y1 <= Y.
  -- Lower bound from uSeq-prop2, upper bound from the bridge + uSeq-stab,
  -- squeezed by antisymmetry.
  realise-limit : (Y : Tup)
    (k : Nat) (e : Eq (uSeq rd Y k) (uSeq rd Y (suc k)))
    (w : FEl) (ew : Eq (uSeq rd Y k) (embed w)) ->
    Sigma Nat (\ n -> Sigma FTup (\ Y1 ->
      Pair (Below Y1 Y) (Eq (PF G H (cons (fbot n) Y1)) w)))
  realise-limit Y k e w ew =
    mkSigma n (mkSigma Y1 (mkSigma belY1 eqfn))
    where
      w-le-uk : LeD (embed w) (uSeq rd Y k)
      w-le-uk = Eq-transport (\ z -> LeD (embed w) z) (Eq-sym ew) (LeD-refl (embed w))
      pr  = uSeq-prop2 rd Y k w w-le-uk
      m0  = fst pr
      Y1  = fst (snd pr)
      belY1 = fst (snd (snd pr))
      wLe = snd (snd (snd pr))            -- LeF w (f(cons(fbot m0)Y1))
      n = maxN m0 k
      un-eq : Eq (uSeq rd Y n) (embed w)
      un-eq = Eq-trans (Eq-sym (uSeq-stab rd Y k e n (maxN-le-r m0 k))) ew
      lower : LeD (embed w) (embed (PF G H (cons (fbot n) Y1)))
      lower = LeD-trans {embed w}
                {embed (PF G H (cons (fbot m0) Y1))}
                {embed (PF G H (cons (fbot n) Y1))}
                wLe
                (PF-mono G H monoG monoH {cons (fbot m0) Y1} {cons (fbot n) Y1}
                  (mkSigma (maxN-le-l m0 k) (LeFTup-refl Y1)))
      upper : LeD (embed (PF G H (cons (fbot n) Y1))) (embed w)
      upper = Eq-transport (\ z -> LeD (embed (PF G H (cons (fbot n) Y1))) z)
                un-eq (f-le-uSeq Y n Y1 belY1)
      eqfn : Eq (PF G H (cons (fbot n) Y1)) w
      eqfn = embed-inj (LeD-antisym {embed (PF G H (cons (fbot n) Y1))} {embed w}
               upper lower)

  ------------------------------------------------------------------------
  -- First principal case, COMPLETE limit: fully assembled.
  ------------------------------------------------------------------------

  -- If the fixpoint limit at (S^omega(bot), Y) is a complete value S^p(0),
  -- then f is ultimate-obstinate there (Case 1).
  prec-inf-complete : (Y : Tup)
    (k : Nat) (e : Eq (uSeq rd Y k) (uSeq rd Y (suc k)))
    (p : Nat) (ew : Eq (uSeq rd Y k) (cpl p)) ->
    UO (PF G H) (cons inf Y)
  prec-inf-complete Y k e p ew =
    prec-inf-Case1 Y n Y1 p belY1 eqfn
    where
      rl = realise-limit Y k e (fcpl p) ew
      n     = fst rl
      Y1    = fst (snd rl)
      belY1 = fst (snd (snd rl))
      eqfn  = snd (snd (snd rl))

  ------------------------------------------------------------------------
  -- Second principal case, the enabling fact: the recursion result
  -- reaches level k0.
  ------------------------------------------------------------------------

  -- If  S^{k0}(bot) <= u_{k0}  (the second principal case), then there are
  -- n0 and a finite Y0 <= Y such that, on the whole region  n >= n0,
  -- X >= Y0,  the recursion value  f(S^n(bot), X)  is at least S^{k0}(bot).
  -- This is what makes h's coordinate-1 (recursion-result) condition
  -- satisfiable everywhere on the region, unlocking all five sub-cases.
  f-reaches : (Y : Tup) (k0 : Nat) ->
    LeD (bot k0) (uSeq rd Y k0) ->
    Sigma Nat (\ n0 -> Sigma FTup (\ Y0 -> Pair (Below Y0 Y)
      ((a : FEl) (X : FTup) -> LeF (fbot n0) a -> LeFTup Y0 X ->
         LeD (bot k0) (embed (PF G H (cons a X))))))
  f-reaches Y k0 le =
    mkSigma n0 (mkSigma Y0 (mkSigma belY0 reach))
    where
      pr    = uSeq-prop2 rd Y k0 (fbot k0) le
      m0    = fst pr
      Y0    = fst (snd pr)
      belY0 = fst (snd (snd pr))
      kLe   = snd (snd (snd pr))    -- LeF (fbot k0) (f(cons(fbot m0)Y0))
      n0 = maxN m0 k0
      reach : (a : FEl) (X : FTup) -> LeF (fbot n0) a -> LeFTup Y0 X ->
              LeD (bot k0) (embed (PF G H (cons a X)))
      reach a X n0a Y0X =
        LeD-trans {bot k0}
          {embed (PF G H (cons (fbot m0) Y0))}
          {embed (PF G H (cons a X))}
          kLe
          (PF-mono G H monoG monoH {cons (fbot m0) Y0} {cons a X}
            (mkSigma (LeD-trans {bot m0} {bot n0} {embed a} (maxN-le-l m0 k0) n0a) Y0X))

  ------------------------------------------------------------------------
  -- The core recurrence engine (shared by all five sub-cases of the second
  -- principal case): if h's germ takes a constant value v on the region
  -- (given the recursion result reaches k0), then f takes value v there.
  ------------------------------------------------------------------------

  -- Fixed X.  `reach` says the recursion result is >= S^{k0}(bot); `hgerm`
  -- says h returns v whenever coord 0 >= S^{n0}(bot) and coord 1 >= S^{k0}
  -- (bot).  Then f(S(a), X) = v for every a of height >= n0.
  f-const : (v : FEl) (n0 k0 : Nat) (X : FTup)
    (reach : (a : FEl) -> LeF (fbot n0) a ->
               LeD (bot k0) (embed (PF G H (cons a X))))
    (hgerm : (a r : FEl) -> LeF (fbot n0) a -> LeD (bot k0) (embed r) ->
               Eq (H (cons a (cons r X))) v)
    (a : FEl) -> LeF (fbot (suc n0)) a -> Eq (PF G H (cons a X)) v
  f-const v n0 k0 X reach hgerm (fbot zero)    ()
  f-const v n0 k0 X reach hgerm (fbot (suc q)) le =
    hgerm (fbot q) (PF G H (cons (fbot q) X)) le (reach (fbot q) le)
  f-const v n0 k0 X reach hgerm (fcpl zero)    ()
  f-const v n0 k0 X reach hgerm (fcpl (suc q)) le =
    hgerm (fcpl q) (PF G H (cons (fcpl q) X)) le (reach (fcpl q) le)

  -- Depth-tracking variant (sub-case 5: h is Case 3 at coordinate 0, the
  -- recursion depth, so the value grows as S^{phi(n)}(bot) with the depth).
  -- The recursion argument is incomplete (S^{n+1}(bot)); complete arguments
  -- do not arise at the infinite point's coordinate-0 region.
  f-depth : (phi : Nat -> Nat) (n0 k0 : Nat) (X : FTup)
    (reach : (a : FEl) -> LeF (fbot n0) a ->
               LeD (bot k0) (embed (PF G H (cons a X))))
    (hgerm : (n : Nat) (r : FEl) -> LeN n0 n -> LeD (bot k0) (embed r) ->
               Eq (H (cons (fbot n) (cons r X))) (fbot (phi n)))
    (n : Nat) -> LeN n0 n ->
    Eq (PF G H (cons (fbot (suc n)) X)) (fbot (phi n))
  f-depth phi n0 k0 X reach hgerm n n0n =
    hgerm n (PF G H (cons (fbot n) X)) n0n (reach (fbot n) n0n)
