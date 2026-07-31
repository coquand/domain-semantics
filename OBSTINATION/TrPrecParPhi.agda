{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.TrPrecParPhi
--
-- **THE RECURSION UNROLLED A FIXED NUMBER OF TIMES, WITH THE PARAMETERS
-- MOVING: THE VERDICT, WITHOUT PROPOSITION 1.**
--
--     PAR.unroll : (c : Nat) -> VerdictFrom zero (\ t -> R.Vd p Th (Lt t) c)
--
-- This is the sub-case of MP1's value clause for `precTr` in which `f`'s
-- own walk eventually raises a PARAMETER: the recursion depth is then
-- frozen at some `c`, and `ovP` runs along a family of parameter levels
-- `Lt` in which each coordinate is either constant or grows by one per
-- step.  For `f(S x,y) = g(x, f(x,y), y)` that is
--
--     f(S^c(bot), S^(l+t)(bot))   as `t` grows,
--
-- i.e. `g` applied `c` times over, and the induction is on `c`.
--
-- EACH LAYER IS A FED TRACE.  Layer `c+1` is `g` applied to
--
--     ( S^c(bot) , layer c , S^(Lt t 1)(bot) , ... ) ,
--
-- and every coordinate has one of `TrFeedR`'s two regimes: the recursion
-- argument and the frozen parameters never move (`FixC`), a growing
-- parameter grows at every step and is never complete (`GroC`), and the
-- middle coordinate -- the previous layer -- is whichever its own verdict
-- says (`vf-reg`).  So `TrFeedR.fedR` applies, and it is `fedR` rather
-- than `TrCompVerdict.fedV` that is needed here, precisely because nothing
-- tells us in advance which coordinate `g` ends up waiting on.
--
-- No Proposition 1.  No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.TrPrecParPhi where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain using (FEl ; fbot ; fcpl ; LeF ; LeF-refl)
open import OBSTINATION.Tuples using (FTup)
open import OBSTINATION.MP1 using (ConstFrom ; StrictIncFrom ; PhiOK)
open import OBSTINATION.TraceDef
open import OBSTINATION.TrSat using
  (IsCpl ; cpl-max ; LeX ; MonoF ; MonoTr)
open import OBSTINATION.TrDen using (Den)
open import OBSTINATION.TrMP1 using (Never ; Verdict ; MP1T)
open import OBSTINATION.TrPrec using (module R)
open import OBSTINATION.TrPrecDec using (Vd-mono-L)
open import OBSTINATION.TrCompVerdict using (VerdictFrom ; IsCpl-dec ; notCpl-of)
open import OBSTINATION.TrPrecChain using (Bt ; notCpl-bt)
open import OBSTINATION.TrFeedR using (FixC ; GroC ; Reg ; fedR)

------------------------------------------------------------------------
-- A TAIL VERDICT IS A REGIME
--
-- `TrFeedR` asks of each coordinate that its VALUE settle or its HEIGHT
-- grow at every step, and that is exactly what a `VerdictFrom` says once
-- the two `PhiOK` branches are unpacked: a complete value is maximal, an
-- incomplete one with a constant height is constant, and an incomplete
-- one with a strictly increasing height is the growing case.
------------------------------------------------------------------------

FixU : (Nat -> FEl) -> Nat -> Set
FixU u kc = (t t' : Nat) -> LeN kc t -> LeN t t' -> Eq (u t') (u t)

GroU : (Nat -> FEl) -> Nat -> Set
GroU u kc =
  Pair ((t : Nat) -> Not (IsCpl (u t)))
       ((t : Nat) -> LeN kc t -> LeN (suc (hgt (u t))) (hgt (u (suc t))))

vf-reg : (u : Nat -> FEl)
       -> ((t t' : Nat) -> LeN t t' -> LeF (u t) (u t'))
       -> (K : Nat) -> VerdictFrom K u
       -> Sigma Nat (\ kc -> Or (FixU u kc) (GroU u kc))
vf-reg u mo K (mkSigma K' (mkSigma lK r)) = route r
  where
    ----------------------------------------------------------------------
    -- a complete value never moves again
    ----------------------------------------------------------------------
    route : Or (IsCpl (u K'))
               (Pair ((k : Nat) -> LeN K' k -> Bt (u k)) (PhiOK (\ k -> hgt (u k))))
          -> Sigma Nat (\ kc -> Or (FixU u kc) (GroU u kc))
    route (inl ic) = mkSigma K' (inl go)
      where
        at : (t : Nat) -> LeN K' t -> Eq (u t) (u K')
        at t lt = Eq-sym (cpl-max (u K') (u t) (mo K' t lt) ic)

        go : FixU u K'
        go t t' lt le =
          Eq-trans (at t' (LeN-trans {K'} {t} {t'} lt le)) (Eq-sym (at t lt))
    route (inr (mkSigma nv (mkSigma kk pk))) = split pk
      where
        M : Nat
        M = maxN kk K'

        lKM : LeN K' M
        lKM = maxN-le-r kk K'

        lkM : LeN kk M
        lkM = maxN-le-l kk K'

        -- an incomplete value below an incomplete one is incomplete
        ncAll : (t : Nat) -> Not (IsCpl (u t))
        ncAll t = pick (LeN-dec K' t)
          where
            pick : Dec (LeN K' t) -> Not (IsCpl (u t))
            pick (yes l)  = notCpl-of (u t) (nv t l)
            pick (no  nl) = go
              where
                ltK : LeN t K'
                ltK = LeN-trans {t} {suc t} {K'} (LeN-suc t) (nle-lt K' t nl)
                  where
                    nle-lt : (x y : Nat) -> Not (LeN x y) -> LeN (suc y) x
                    nle-lt zero    y       n = Empty-elim (n tt)
                    nle-lt (suc x) zero    n = tt
                    nle-lt (suc x) (suc y) n = nle-lt x y n

                go : Not (IsCpl (u t))
                go ic =
                  notCpl-of (u K') (nv K' (LeN-refl K'))
                    (Eq-transport (\ z -> IsCpl z) (cpl-max (u t) (u K') (mo t K' ltK) ic) ic)

        --------------------------------------------------------------
        -- incomplete with a constant height IS constant
        --------------------------------------------------------------
        split : Or (ConstFrom kk (\ k -> hgt (u k))) (StrictIncFrom kk (\ k -> hgt (u k)))
              -> Sigma Nat (\ kc -> Or (FixU u kc) (GroU u kc))
        split (inl cf) = mkSigma M (inl go)
          where
            at : (t : Nat) -> LeN M t -> Eq (u t) (fbot (hgt (u kk)))
            at t lt =
              Eq-trans (nv t (LeN-trans {K'} {M} {t} lKM lt))
                (Eq-cong fbot (cf t (LeN-trans {kk} {M} {t} lkM lt)))

            go : FixU u M
            go t t' lt le =
              Eq-trans (at t' (LeN-trans {M} {t} {t'} lt le)) (Eq-sym (at t lt))
        --------------------------------------------------------------
        -- incomplete with a strictly increasing height IS the growing case
        --------------------------------------------------------------
        split (inr si) = mkSigma kk (inr (mkSigma ncAll si))

------------------------------------------------------------------------
-- THE UNROLLING
------------------------------------------------------------------------

module PAR (p : Nat)
           (Th : Tr (suc (suc p)))
           (mth : MonoTr (suc (suc p)) Th)
           (m1th : MP1T (suc (suc p)) Th)
           (g h : FTup -> FEl)
           (dh : Den (suc (suc p)) Th h)
           (mg : MonoF p g)
           (mh : MonoF (suc (suc p)) h)
           (Lt : Nat -> Nat -> Nat)
           (Lt-mono : (t t' : Nat) -> LeN t t' -> (i : Nat) -> LeN (Lt t i) (Lt t' i))
           (Lt-reg : (i : Nat)
                   -> Sigma Nat (\ ki ->
                        Or ((t t' : Nat) -> LeN ki t -> LeN t t' -> Eq (Lt t' i) (Lt t i))
                           ((t : Nat) -> LeN ki t -> LeN (suc (Lt t i)) (Lt (suc t) i))))
           where

  a : Nat
  a = suc (suc p)

  U : Nat -> Nat -> FEl
  U c t = R.Vd p Th (Lt t) c

  -- the recursion is monotone in the parameter levels
  U-mono : (c t t' : Nat) -> LeN t t' -> LeF (U c t) (U c t')
  U-mono c t t' le =
    Vd-mono-L p Th g h dh mg mh (Lt t) (Lt t')
      (\ i -> Lt-mono t t' le (suc i)) c

  ----------------------------------------------------------------------
  -- the argument tuple of one layer, coordinate by coordinate
  ----------------------------------------------------------------------

  AV : Nat -> Nat -> FTup
  AV c t = R.avT p Th (Lt t) c

  av-nth : (c t d : Nat) -> LeN (suc d) a
         -> Eq (nth (fbot zero) d (AV c t)) (R.avf p Th (Lt t) c d)
  av-nth c t d ld = tup-nth a (R.avf p Th (Lt t) c) d ld

  av-out : (c t d : Nat) -> Not (LeN (suc d) a)
         -> Eq (nth (fbot zero) d (AV c t)) (fbot zero)
  av-out c t d nd = tup-out a (R.avf p Th (Lt t) c) d nd

  AV-mono : (c t t' : Nat) -> LeN t t' -> LeX (AV c t) (AV c t')
  AV-mono c t t' le d = route (LeN-dec (suc d) a)
    where
      route : Dec (LeN (suc d) a)
            -> LeF (nth (fbot zero) d (AV c t)) (nth (fbot zero) d (AV c t'))
      route (no nd) =
        Eq-transport (\ z -> LeF z (nth (fbot zero) d (AV c t')))
          (Eq-sym (av-out c t d nd))
          (Eq-transport (\ z -> LeF (fbot zero) z)
            (Eq-sym (av-out c t' d nd)) (LeF-refl (fbot zero)))
      route (yes ld) =
        Eq-transport (\ z -> LeF z (nth (fbot zero) d (AV c t')))
          (Eq-sym (av-nth c t d ld))
          (Eq-transport (\ z -> LeF (R.avf p Th (Lt t) c d) z)
            (Eq-sym (av-nth c t' d ld)) (shape d))
        where
          shape : (e : Nat) -> LeF (R.avf p Th (Lt t) c e) (R.avf p Th (Lt t') c e)
          shape zero            = LeF-refl (fbot c)
          shape (suc zero)      = U-mono c t t' le
          shape (suc (suc i))   = Lt-mono t t' le (suc i)

  ----------------------------------------------------------------------
  -- THE INDUCTION ON THE UNROLLING DEPTH
  ----------------------------------------------------------------------

  unroll : (c : Nat) -> VerdictFrom zero (U c)
  ----------------------------------------------------------------------
  -- depth 0: the recursion has not started
  ----------------------------------------------------------------------
  unroll zero =
    mkSigma zero (mkSigma tt
      (inr (mkSigma (\ k lk -> refl) (mkSigma zero (inl (\ m lm -> refl))))))
  ----------------------------------------------------------------------
  -- depth c+1: one application of the step term to the layer below
  ----------------------------------------------------------------------
  unroll (suc c) = fedR a Th mth m1th (AV c) (AV-mono c) zero reg
    where
      ih : Sigma Nat (\ kc -> Or (FixU (U c) kc) (GroU (U c) kc))
      ih = vf-reg (U c) (U-mono c) zero (unroll c)

      reg : Reg (AV c)
      reg d = route (LeN-dec (suc d) a)
        where
          Res : Set
          Res = Sigma Nat (\ kc -> Or (FixC (AV c) kc d) (GroC (AV c) kc d))

          --------------------------------------------------------------
          -- out of range: the coordinate is `bot`, for ever
          --------------------------------------------------------------
          route : Dec (LeN (suc d) a) -> Res
          route (no nd) = mkSigma zero (inl go)
            where
              go : FixC (AV c) zero d
              go t t' lt le =
                Eq-trans (av-out c t' d nd) (Eq-sym (av-out c t d nd))
          route (yes ld) = shape d ld
            where
              --------------------------------------------------------
              -- 0: the recursion argument, frozen at `S^c(bot)`
              --------------------------------------------------------
              shape : (e : Nat) -> LeN (suc e) a
                    -> Sigma Nat (\ kc -> Or (FixC (AV c) kc e) (GroC (AV c) kc e))
              shape zero le' = mkSigma zero (inl go)
                where
                  go : FixC (AV c) zero zero
                  go t t' lt le =
                    Eq-trans (av-nth c t' zero le') (Eq-sym (av-nth c t zero le'))
              --------------------------------------------------------
              -- 1: the layer below -- the induction hypothesis
              --------------------------------------------------------
              shape (suc zero) le' = mkSigma (fst ih) (tr (snd ih))
                where
                  eu : (t : Nat) -> Eq (nth (fbot zero) (suc zero) (AV c t)) (U c t)
                  eu t = av-nth c t (suc zero) le'

                  tr : Or (FixU (U c) (fst ih)) (GroU (U c) (fst ih))
                     -> Or (FixC (AV c) (fst ih) (suc zero))
                           (GroC (AV c) (fst ih) (suc zero))
                  tr (inl fx) =
                    inl (\ t t' lt le ->
                           Eq-trans (eu t') (Eq-trans (fx t t' lt le) (Eq-sym (eu t))))
                  tr (inr (mkSigma nc gr)) =
                    inr (mkSigma
                          (\ t ic -> nc t (Eq-transport (\ z -> IsCpl z) (eu t) ic))
                          (\ t lt ->
                             Eq-transport
                               (\ z -> LeN (suc (hgt z))
                                          (hgt (nth (fbot zero) (suc zero) (AV c (suc t)))))
                               (Eq-sym (eu t))
                               (Eq-transport (\ z -> LeN (suc (hgt (U c t))) (hgt z))
                                 (Eq-sym (eu (suc t))) (gr t lt))))
              --------------------------------------------------------
              -- 2+i: a parameter, constant or growing by one per step
              --------------------------------------------------------
              shape (suc (suc i)) le' = mkSigma (fst (Lt-reg (suc i))) (tr (snd (Lt-reg (suc i))))
                where
                  ep : (t : Nat)
                     -> Eq (nth (fbot zero) (suc (suc i)) (AV c t)) (fbot (Lt t (suc i)))
                  ep t = av-nth c t (suc (suc i)) le'

                  tr : Or ((t t' : Nat) -> LeN (fst (Lt-reg (suc i))) t -> LeN t t'
                             -> Eq (Lt t' (suc i)) (Lt t (suc i)))
                          ((t : Nat) -> LeN (fst (Lt-reg (suc i))) t
                             -> LeN (suc (Lt t (suc i))) (Lt (suc t) (suc i)))
                     -> Or (FixC (AV c) (fst (Lt-reg (suc i))) (suc (suc i)))
                           (GroC (AV c) (fst (Lt-reg (suc i))) (suc (suc i)))
                  tr (inl fx) =
                    inl (\ t t' lt le ->
                           Eq-trans (ep t')
                             (Eq-trans (Eq-cong fbot (fx t t' lt le)) (Eq-sym (ep t))))
                  tr (inr gr) =
                    inr (mkSigma nc go)
                    where
                      nc : (t : Nat) -> Not (IsCpl (nth (fbot zero) (suc (suc i)) (AV c t)))
                      nc t ic =
                        Eq-transport (\ z -> IsCpl z) (ep t) ic

                      go : (t : Nat) -> LeN (fst (Lt-reg (suc i))) t
                         -> LeN (suc (hgt (nth (fbot zero) (suc (suc i)) (AV c t))))
                                (hgt (nth (fbot zero) (suc (suc i)) (AV c (suc t))))
                      go t lt =
                        Eq-transport
                          (\ z -> LeN (suc (hgt z))
                                     (hgt (nth (fbot zero) (suc (suc i)) (AV c (suc t)))))
                          (Eq-sym (ep t))
                          (Eq-transport
                            (\ z -> LeN (suc (Lt t (suc i))) (hgt z))
                            (Eq-sym (ep (suc t))) (gr t lt))
