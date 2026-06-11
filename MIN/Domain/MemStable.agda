{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- FinMemStageStable.agda  (MIN/ — Pi + U fragment)
--
-- STABILITY of the stage-stratified membership: for stages above the
-- canonical RANK level the membership stops changing.  `MemStabPack n`
-- bundles the six one-step transports (fwd/bwd for finMem/finMemAllU/
-- finMemFun) at stage n; proved by induction on n (goodMemStab), exactly
-- like the order's goodStab.  The suc-step uses the IH (predecessor) only
-- for the dropped FinEl-memberships; the same-stage FinFun recursions
-- (faS*/ffS*) are ordinary structural recursions on the list.
--
-- Bound convention (mirrors goodStab's lei-st / lef-st):
--   * fm  (FinEl level): two bounds  Le (RANK u) n, Le (RANK a) n.
--   * fa/ff (FinFun level): one bound with a leading suc, since their
--     contents live at the predecessor stage.
--
-- Then the stage-shift (finMem-shift etc.) and the public collapse hooks.
--
-- NO postulates.
------------------------------------------------------------------------

module MIN.Domain.MemStable where

open import MIN.Domain.Basic
  using ( Top ; tt ; Empty
        ; Nat ; zero ; suc ; max
        ; Le ; Le-refl ; Le-suc ; Le-trans ; Le-max-l ; Le-max-r
        ; Pair ; mkSigma ; fst ; snd ; Sigma
        ; Eq ; refl ; Eq-sym ; Eq-transport
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; nil ; cons )
open import MIN.Domain.Order
  using ( RANK ; RANKFun ; EvalFun ; CoherentFunTail
        ; Le-max-lub ; max-mono ; RANK-ev ; ev-bridge ; module OB )
open import MIN.Domain.MemStage

private
  max-Le-l : (a b c : Nat) -> Le (max a b) c -> Le a c
  max-Le-l a b c h = Le-trans a (max a b) c (Le-max-l a b) h

  max-Le-r : (a b c : Nat) -> Le (max a b) c -> Le b c
  max-Le-r a b c h = Le-trans b (max a b) c (Le-max-r a b) h

  rk-key : (a b cps : Nat) -> Le a (max a (max b cps))
  rk-key a b cps = Le-max-l a (max b cps)

  rk-val : (a b cps : Nat) -> Le b (max a (max b cps))
  rk-val a b cps = Le-trans b (max b cps) (max a (max b cps))
                     (Le-max-l b cps) (Le-max-r a (max b cps))

  rk-tail : (a b cps : Nat) -> Le cps (max a (max b cps))
  rk-tail a b cps = Le-trans cps (max b cps) (max a (max b cps))
                      (Le-max-r b cps) (Le-max-r a (max b cps))

  -- RANK of a structural EvalFun result, via the order's ev-bridge + RANK-ev.
  RANK-EvalFun : (h : FinFun) (u : FinEl) -> Le (RANK (EvalFun h u)) (RANKFun h)
  RANK-EvalFun h u =
    let M = max (RANKFun h) (RANK u)
    in Eq-transport (\ x -> Le (RANK x) (RANKFun h))
         (Eq-sym (ev-bridge M h u (Le-refl M)))
         (RANK-ev (suc M) h u)

  Le0 : (m : Nat) -> Le zero m
  Le0 m = tt

------------------------------------------------------------------------
-- Per-stage stability pack.
------------------------------------------------------------------------

record MemStabPack (n : Nat) : Set where
  field
    fm-fwd : (u a : FinEl) -> Le (RANK u) n -> Le (RANK a) n ->
             MB.finMem n u a -> MB.finMem (suc n) u a
    fm-bwd : (u a : FinEl) -> Le (RANK u) n -> Le (RANK a) n ->
             MB.finMem (suc n) u a -> MB.finMem n u a
    fa-fwd : (f : FinFun) (a : FinEl) ->
             Le (suc (max (RANKFun f) (RANK a))) n ->
             MB.finMemAllU n f a -> MB.finMemAllU (suc n) f a
    fa-bwd : (f : FinFun) (a : FinEl) ->
             Le (suc (max (RANKFun f) (RANK a))) n ->
             MB.finMemAllU (suc n) f a -> MB.finMemAllU n f a
    ff-fwd : (g : FinFun) (a : FinEl) (f : FinFun) ->
             Le (suc (max (RANKFun g) (max (RANK a) (RANKFun f)))) n ->
             MB.finMemFun n g a f -> MB.finMemFun (suc n) g a f
    ff-bwd : (g : FinFun) (a : FinEl) (f : FinFun) ->
             Le (suc (max (RANKFun g) (max (RANK a) (RANKFun f)))) n ->
             MB.finMemFun (suc n) g a f -> MB.finMemFun n g a f

------------------------------------------------------------------------
-- goodMemStab : (n) -> MemStabPack n, by induction on n.
------------------------------------------------------------------------

goodMemStab : (n : Nat) -> MemStabPack n
goodMemStab zero =
  record { fm-fwd = fmF ; fm-bwd = fmB
         ; fa-fwd = faF ; fa-bwd = faB
         ; ff-fwd = ffF ; ff-bwd = ffB }
  where
    fmF : (u a : FinEl) -> Le (RANK u) zero -> Le (RANK a) zero ->
          MB.finMem zero u a -> MB.finMem (suc zero) u a
    fmF Bot          Bot          bu ba mem = mem
    fmF Bot          UCode        bu ba mem = mem
    fmF Bot          (FunEl g)    bu ()
    fmF Bot          (PiCode a f) bu ()
    fmF UCode        Bot          bu ba mem = mem
    fmF UCode        UCode        bu ba mem = mem
    fmF UCode        (FunEl g)    bu ()
    fmF UCode        (PiCode a f) bu ()
    fmF (FunEl g)    a            ()
    fmF (PiCode a f) a'           ()

    fmB : (u a : FinEl) -> Le (RANK u) zero -> Le (RANK a) zero ->
          MB.finMem (suc zero) u a -> MB.finMem zero u a
    fmB Bot          Bot          bu ba mem = mem
    fmB Bot          UCode        bu ba mem = mem
    fmB Bot          (FunEl g)    bu ()
    fmB Bot          (PiCode a f) bu ()
    fmB UCode        Bot          bu ba mem = mem
    fmB UCode        UCode        bu ba mem = mem
    fmB UCode        (FunEl g)    bu ()
    fmB UCode        (PiCode a f) bu ()
    fmB (FunEl g)    a            ()
    fmB (PiCode a f) a'           ()

    faF : (f : FinFun) (a : FinEl) ->
          Le (suc (max (RANKFun f) (RANK a))) zero ->
          MB.finMemAllU zero f a -> MB.finMemAllU (suc zero) f a
    faF f a ()

    faB : (f : FinFun) (a : FinEl) ->
          Le (suc (max (RANKFun f) (RANK a))) zero ->
          MB.finMemAllU (suc zero) f a -> MB.finMemAllU zero f a
    faB f a ()

    ffF : (g : FinFun) (a : FinEl) (f : FinFun) ->
          Le (suc (max (RANKFun g) (max (RANK a) (RANKFun f)))) zero ->
          MB.finMemFun zero g a f -> MB.finMemFun (suc zero) g a f
    ffF g a f ()

    ffB : (g : FinFun) (a : FinEl) (f : FinFun) ->
          Le (suc (max (RANKFun g) (max (RANK a) (RANKFun f)))) zero ->
          MB.finMemFun (suc zero) g a f -> MB.finMemFun zero g a f
    ffB g a f ()

goodMemStab (suc m) =
  record { fm-fwd = fmF ; fm-bwd = fmB
         ; fa-fwd = faF ; fa-bwd = faB
         ; ff-fwd = ffF ; ff-bwd = ffB }
  where
    open MemStabPack (goodMemStab m)
      renaming ( fm-fwd to ihmF ; fm-bwd to ihmB )

    ----------------------------------------------------------------
    -- same-stage FinFun recursions (structural on the list)
    ----------------------------------------------------------------
    faF : (f : FinFun) (a : FinEl) ->
          Le (suc (max (RANKFun f) (RANK a))) (suc m) ->
          MB.finMemAllU (suc m) f a -> MB.finMemAllU (suc (suc m)) f a
    faF nil         a bnd mem = tt
    faF (cons p ps) a bnd mem =
      let bf = max-Le-l (RANKFun (cons p ps)) (RANK a) m bnd
          ba = max-Le-r (RANKFun (cons p ps)) (RANK a) m bnd
          bk = Le-trans (RANK (fst p)) (RANKFun (cons p ps)) m
                 (rk-key (RANK (fst p)) (RANK (snd p)) (RANKFun ps)) bf
          bv = Le-trans (RANK (snd p)) (RANKFun (cons p ps)) m
                 (rk-val (RANK (fst p)) (RANK (snd p)) (RANKFun ps)) bf
          bt = Le-trans (RANKFun ps) (RANKFun (cons p ps)) m
                 (rk-tail (RANK (fst p)) (RANK (snd p)) (RANKFun ps)) bf
      in mkSigma
           (mkSigma (ihmF (fst p) a bk ba (fst (fst mem)))
                    (ihmF (snd p) UCode bv (Le0 m) (snd (fst mem))))
           (faF ps a (Le-max-lub (RANKFun ps) (RANK a) m bt ba) (snd mem))

    faB : (f : FinFun) (a : FinEl) ->
          Le (suc (max (RANKFun f) (RANK a))) (suc m) ->
          MB.finMemAllU (suc (suc m)) f a -> MB.finMemAllU (suc m) f a
    faB nil         a bnd mem = tt
    faB (cons p ps) a bnd mem =
      let bf = max-Le-l (RANKFun (cons p ps)) (RANK a) m bnd
          ba = max-Le-r (RANKFun (cons p ps)) (RANK a) m bnd
          bk = Le-trans (RANK (fst p)) (RANKFun (cons p ps)) m
                 (rk-key (RANK (fst p)) (RANK (snd p)) (RANKFun ps)) bf
          bv = Le-trans (RANK (snd p)) (RANKFun (cons p ps)) m
                 (rk-val (RANK (fst p)) (RANK (snd p)) (RANKFun ps)) bf
          bt = Le-trans (RANKFun ps) (RANKFun (cons p ps)) m
                 (rk-tail (RANK (fst p)) (RANK (snd p)) (RANKFun ps)) bf
      in mkSigma
           (mkSigma (ihmB (fst p) a bk ba (fst (fst mem)))
                    (ihmB (snd p) UCode bv (Le0 m) (snd (fst mem))))
           (faB ps a (Le-max-lub (RANKFun ps) (RANK a) m bt ba) (snd mem))

    ffF : (g : FinFun) (a : FinEl) (f : FinFun) ->
          Le (suc (max (RANKFun g) (max (RANK a) (RANKFun f)))) (suc m) ->
          MB.finMemFun (suc m) g a f -> MB.finMemFun (suc (suc m)) g a f
    ffF nil         a f bnd mem = tt
    ffF (cons p ps) a f bnd mem =
      let bg  = max-Le-l (RANKFun (cons p ps)) (max (RANK a) (RANKFun f)) m bnd
          baf = max-Le-r (RANKFun (cons p ps)) (max (RANK a) (RANKFun f)) m bnd
          ba  = max-Le-l (RANK a) (RANKFun f) m baf
          bf  = max-Le-r (RANK a) (RANKFun f) m baf
          bk  = Le-trans (RANK (fst p)) (RANKFun (cons p ps)) m
                  (rk-key (RANK (fst p)) (RANK (snd p)) (RANKFun ps)) bg
          bv  = Le-trans (RANK (snd p)) (RANKFun (cons p ps)) m
                  (rk-val (RANK (fst p)) (RANK (snd p)) (RANKFun ps)) bg
          bt  = Le-trans (RANKFun ps) (RANKFun (cons p ps)) m
                  (rk-tail (RANK (fst p)) (RANK (snd p)) (RANKFun ps)) bg
          bev = Le-trans (RANK (EvalFun f (fst p))) (RANKFun f) m
                  (RANK-EvalFun f (fst p)) bf
      in mkSigma
           (mkSigma (ihmF (fst p) a bk ba (fst (fst mem)))
                    (ihmF (snd p) (EvalFun f (fst p)) bv bev (snd (fst mem))))
           (ffF ps a f
             (Le-max-lub (RANKFun ps) (max (RANK a) (RANKFun f)) m bt baf)
             (snd mem))

    ffB : (g : FinFun) (a : FinEl) (f : FinFun) ->
          Le (suc (max (RANKFun g) (max (RANK a) (RANKFun f)))) (suc m) ->
          MB.finMemFun (suc (suc m)) g a f -> MB.finMemFun (suc m) g a f
    ffB nil         a f bnd mem = tt
    ffB (cons p ps) a f bnd mem =
      let bg  = max-Le-l (RANKFun (cons p ps)) (max (RANK a) (RANKFun f)) m bnd
          baf = max-Le-r (RANKFun (cons p ps)) (max (RANK a) (RANKFun f)) m bnd
          ba  = max-Le-l (RANK a) (RANKFun f) m baf
          bf  = max-Le-r (RANK a) (RANKFun f) m baf
          bk  = Le-trans (RANK (fst p)) (RANKFun (cons p ps)) m
                  (rk-key (RANK (fst p)) (RANK (snd p)) (RANKFun ps)) bg
          bv  = Le-trans (RANK (snd p)) (RANKFun (cons p ps)) m
                  (rk-val (RANK (fst p)) (RANK (snd p)) (RANKFun ps)) bg
          bt  = Le-trans (RANKFun ps) (RANKFun (cons p ps)) m
                  (rk-tail (RANK (fst p)) (RANK (snd p)) (RANKFun ps)) bg
          bev = Le-trans (RANK (EvalFun f (fst p))) (RANKFun f) m
                  (RANK-EvalFun f (fst p)) bf
      in mkSigma
           (mkSigma (ihmB (fst p) a bk ba (fst (fst mem)))
                    (ihmB (snd p) (EvalFun f (fst p)) bv bev (snd (fst mem))))
           (ffB ps a f
             (Le-max-lub (RANKFun ps) (max (RANK a) (RANKFun f)) m bt baf)
             (snd mem))

    ----------------------------------------------------------------
    -- the fm stability at suc m: IH (predecessor) on the dropped
    -- FinEl-memberships, same-stage faF/ffF on the FinFun-facts.
    ----------------------------------------------------------------
    fmF : (u a : FinEl) -> Le (RANK u) (suc m) -> Le (RANK a) (suc m) ->
          MB.finMem (suc m) u a -> MB.finMem (suc (suc m)) u a
    fmF Bot          Bot          bu ba mem = mem
    fmF Bot          UCode        bu ba mem = mem
    fmF Bot          (FunEl g)    bu ba ()
    fmF Bot          (PiCode a f) bu ba mem =
      let bd = max-Le-l (RANK a) (RANKFun f) m ba
          bk = max-Le-r (RANK a) (RANKFun f) m ba
      in mkSigma (ihmF a UCode bd (Le0 m) (fst mem))
                 (mkSigma (faF f a (Le-max-lub (RANKFun f) (RANK a) m bk bd)
                            (fst (snd mem)))
                          (snd (snd mem)))
    fmF UCode        Bot          bu ba ()
    fmF UCode        UCode        bu ba mem = mem
    fmF UCode        (FunEl g)    bu ba ()
    fmF UCode        (PiCode a f) bu ba ()
    fmF (FunEl g)    Bot          bu ba ()
    fmF (FunEl g)    UCode        bu ba ()
    fmF (FunEl g)    (FunEl h)    bu ba ()
    fmF (FunEl g)    (PiCode a f) bu ba mem =
      let bg = bu                                     -- Le (suc (RANKFun g))(suc m) ≡ Le (RANKFun g) m
          bd = max-Le-l (RANK a) (RANKFun f) m ba
          bk = max-Le-r (RANK a) (RANKFun f) m ba
      in mkSigma
           (ffF g a f
             (Le-max-lub (RANKFun g) (max (RANK a) (RANKFun f)) m bg
               (Le-max-lub (RANK a) (RANKFun f) m bd bk))
             (fst mem))
           (mkSigma (fst (snd mem))
                    (mkSigma (ihmF a UCode bd (Le0 m) (fst (snd (snd mem))))
                             (mkSigma (faF f a (Le-max-lub (RANKFun f) (RANK a) m bk bd)
                                        (fst (snd (snd (snd mem)))))
                                      (snd (snd (snd (snd mem)))))))
    fmF (PiCode a f) Bot          bu ba ()
    fmF (PiCode a f) UCode        bu ba mem =
      let bd = max-Le-l (RANK a) (RANKFun f) m bu
          bk = max-Le-r (RANK a) (RANKFun f) m bu
      in mkSigma (ihmF a UCode bd (Le0 m) (fst mem))
                 (mkSigma (faF f a (Le-max-lub (RANKFun f) (RANK a) m bk bd)
                            (fst (snd mem)))
                          (snd (snd mem)))
    fmF (PiCode a f) (FunEl g)    bu ba ()
    fmF (PiCode a f) (PiCode b g) bu ba ()

    fmB : (u a : FinEl) -> Le (RANK u) (suc m) -> Le (RANK a) (suc m) ->
          MB.finMem (suc (suc m)) u a -> MB.finMem (suc m) u a
    fmB Bot          Bot          bu ba mem = mem
    fmB Bot          UCode        bu ba mem = mem
    fmB Bot          (FunEl g)    bu ba ()
    fmB Bot          (PiCode a f) bu ba mem =
      let bd = max-Le-l (RANK a) (RANKFun f) m ba
          bk = max-Le-r (RANK a) (RANKFun f) m ba
      in mkSigma (ihmB a UCode bd (Le0 m) (fst mem))
                 (mkSigma (faB f a (Le-max-lub (RANKFun f) (RANK a) m bk bd)
                            (fst (snd mem)))
                          (snd (snd mem)))
    fmB UCode        Bot          bu ba ()
    fmB UCode        UCode        bu ba mem = mem
    fmB UCode        (FunEl g)    bu ba ()
    fmB UCode        (PiCode a f) bu ba ()
    fmB (FunEl g)    Bot          bu ba ()
    fmB (FunEl g)    UCode        bu ba ()
    fmB (FunEl g)    (FunEl h)    bu ba ()
    fmB (FunEl g)    (PiCode a f) bu ba mem =
      let bg = bu
          bd = max-Le-l (RANK a) (RANKFun f) m ba
          bk = max-Le-r (RANK a) (RANKFun f) m ba
      in mkSigma
           (ffB g a f
             (Le-max-lub (RANKFun g) (max (RANK a) (RANKFun f)) m bg
               (Le-max-lub (RANK a) (RANKFun f) m bd bk))
             (fst mem))
           (mkSigma (fst (snd mem))
                    (mkSigma (ihmB a UCode bd (Le0 m) (fst (snd (snd mem))))
                             (mkSigma (faB f a (Le-max-lub (RANKFun f) (RANK a) m bk bd)
                                        (fst (snd (snd (snd mem)))))
                                      (snd (snd (snd (snd mem)))))))
    fmB (PiCode a f) Bot          bu ba ()
    fmB (PiCode a f) UCode        bu ba mem =
      let bd = max-Le-l (RANK a) (RANKFun f) m bu
          bk = max-Le-r (RANK a) (RANKFun f) m bu
      in mkSigma (ihmB a UCode bd (Le0 m) (fst mem))
                 (mkSigma (faB f a (Le-max-lub (RANKFun f) (RANK a) m bk bd)
                            (fst (snd mem)))
                          (snd (snd mem)))
    fmB (PiCode a f) (FunEl g)    bu ba ()
    fmB (PiCode a f) (PiCode b g) bu ba ()
