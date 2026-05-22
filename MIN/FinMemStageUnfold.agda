{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- FinMemStageUnfold.agda  (MIN/ — Pi + U fragment)
--
-- The EXPECTED COMPUTATION RULES of the public collapsed membership,
-- as propositional iso pairs (the stage-collapsed finMemC has no
-- definitional unfolding).  These replace the old defeq
-- `FinMem (PiCode a f) UCode = triple` etc.
--
--   * canonical access     finMemC-to/-from (and AllU/Fun versions)
--   * swap                 finMemC-bot-to/-from   (DEFEQ: free)
--   * Pi-type-wf           finMemC-piU-{dom,allU,cft,mk}
--   * FunEl                finMemC-funel-{fun,coh,wf,mk}
--   * finMemFun cons/nil   finMemFunC-{hd,hv,tl,mk,nil}
--   * finMemAllU cons/nil  finMemAllUC-{hd,hv,tl,mk,nil}
--   * projections          FinMem-coh-u/-a-in-U/-coh-a/coh-from-aU
--
-- NO TERMINATING, NO postulates.
------------------------------------------------------------------------

module MIN.FinMemStageUnfold where

open import MIN.Basic
  using ( Top ; tt ; Empty
        ; Nat ; zero ; suc ; max
        ; Le ; Le-refl ; Le-suc ; Le-trans ; Le-max-l ; Le-max-r
        ; Pair ; mkSigma ; fst ; snd
        ; Eq ; Eq-sym ; Eq-transport
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; nil ; cons )
open import MIN.PaperOrder
  using ( RANK ; RANKFun ; EvalFun
        ; Coherent ; CoherentFun ; CoherentFunTail
        ; Le-max-lub ; ev-bridge ; RANK-ev )
open import MIN.FinMemStage
open import MIN.FinMemStageShift

private
  Le0 : (n : Nat) -> Le zero n
  Le0 n = tt

  -- RANK of a structural EvalFun result (kept private in Stable).
  RANK-EvalFun : (h : FinFun) (u : FinEl) -> Le (RANK (EvalFun h u)) (RANKFun h)
  RANK-EvalFun h u =
    let M = max (RANKFun h) (RANK u)
    in Eq-transport (\ x -> Le (RANK x) (RANKFun h))
         (Eq-sym (ev-bridge M h u (Le-refl M)))
         (RANK-ev (suc M) h u)

  canL : (u a : FinEl) -> Le (RANK u) (suc (max (RANK u) (RANK a)))
  canL u a = Le-suc (RANK u) (max (RANK u) (RANK a)) (Le-max-l (RANK u) (RANK a))

  canR : (u a : FinEl) -> Le (RANK a) (suc (max (RANK u) (RANK a)))
  canR u a = Le-suc (RANK a) (max (RANK u) (RANK a)) (Le-max-r (RANK u) (RANK a))

------------------------------------------------------------------------
-- canonical access
------------------------------------------------------------------------

finMemC-to : (n : Nat) (u a : FinEl) -> Le (RANK u) n -> Le (RANK a) n ->
  finMemC u a -> MB.finMem n u a
finMemC-to n u a bu ba mem =
  finMem-shift (suc (max (RANK u) (RANK a))) n u a (canL u a) (canR u a) bu ba mem

finMemC-from : (n : Nat) (u a : FinEl) -> Le (RANK u) n -> Le (RANK a) n ->
  MB.finMem n u a -> finMemC u a
finMemC-from n u a bu ba mem =
  finMem-shift n (suc (max (RANK u) (RANK a))) u a bu ba (canL u a) (canR u a) mem

finMemAllUC-from : (n : Nat) (f : FinFun) (a : FinEl) ->
  Le (suc (max (RANKFun f) (RANK a))) n -> MB.finMemAllU n f a -> finMemAllUC f a
finMemAllUC-from n f a bnd mem =
  finMemAllU-shift n (suc (max (RANKFun f) (RANK a))) f a bnd
    (Le-refl (suc (max (RANKFun f) (RANK a)))) mem

finMemAllUC-to : (n : Nat) (f : FinFun) (a : FinEl) ->
  Le (suc (max (RANKFun f) (RANK a))) n -> finMemAllUC f a -> MB.finMemAllU n f a
finMemAllUC-to n f a bnd mem =
  finMemAllU-shift (suc (max (RANKFun f) (RANK a))) n f a
    (Le-refl (suc (max (RANKFun f) (RANK a)))) bnd mem

finMemFunC-from : (n : Nat) (g : FinFun) (a : FinEl) (f : FinFun) ->
  Le (suc (max (RANKFun g) (max (RANK a) (RANKFun f)))) n ->
  MB.finMemFun n g a f -> finMemFunC g a f
finMemFunC-from n g a f bnd mem =
  finMemFun-shift n (suc (max (RANKFun g) (max (RANK a) (RANKFun f)))) g a f bnd
    (Le-refl (suc (max (RANKFun g) (max (RANK a) (RANKFun f))))) mem

finMemFunC-to : (n : Nat) (g : FinFun) (a : FinEl) (f : FinFun) ->
  Le (suc (max (RANKFun g) (max (RANK a) (RANKFun f)))) n ->
  finMemFunC g a f -> MB.finMemFun n g a f
finMemFunC-to n g a f bnd mem =
  finMemFun-shift (suc (max (RANKFun g) (max (RANK a) (RANKFun f)))) n g a f
    (Le-refl (suc (max (RANKFun g) (max (RANK a) (RANKFun f))))) bnd mem

------------------------------------------------------------------------
-- Swap  finMemC Bot a  <->  finMemC a UCode   (definitionally free:
-- the canonical levels coincide and fm' Bot (PiCode a f) / fm' (PiCode a f)
-- UCode have identical RHS).
------------------------------------------------------------------------

finMemC-bot-to : (a : FinEl) -> finMemC Bot a -> finMemC a UCode
finMemC-bot-to Bot          mem = mem
finMemC-bot-to UCode        mem = mem
finMemC-bot-to (FunEl g)    mem = mem
finMemC-bot-to (PiCode a f) mem = mem

finMemC-bot-from : (a : FinEl) -> finMemC a UCode -> finMemC Bot a
finMemC-bot-from Bot          mem = mem
finMemC-bot-from UCode        mem = mem
finMemC-bot-from (FunEl g)    mem = mem
finMemC-bot-from (PiCode a f) mem = mem

------------------------------------------------------------------------
-- bounds for the Pi / FunEl unfoldings
------------------------------------------------------------------------

private
  -- RANK a <= RANK (PiCode a f)
  bDomP : (a : FinEl) (f : FinFun) -> Le (RANK a) (RANK (PiCode a f))
  bDomP a f = Le-suc (RANK a) (max (RANK a) (RANKFun f)) (Le-max-l (RANK a) (RANKFun f))

  -- suc (max (RANKFun f) (RANK a))  <=  suc (RANK (PiCode a f))
  bAllUP : (a : FinEl) (f : FinFun) ->
    Le (suc (max (RANKFun f) (RANK a))) (suc (RANK (PiCode a f)))
  bAllUP a f =
    Le-max-lub (RANKFun f) (RANK a) (RANK (PiCode a f))
      (Le-suc (RANKFun f) (max (RANK a) (RANKFun f)) (Le-max-r (RANK a) (RANKFun f)))
      (Le-suc (RANK a) (max (RANK a) (RANKFun f)) (Le-max-l (RANK a) (RANKFun f)))

------------------------------------------------------------------------
-- Pi-type well-formedness
--   finMemC (PiCode a f) UCode  =  MB.finMem (suc (RANK (PiCode a f))) ...
--     = Pair (MB.finMem (RANK (PiCode a f)) a UCode)
--            (Pair (MB.finMemAllU (suc (RANK (PiCode a f))) f a) (CoherentFunTail f))
------------------------------------------------------------------------

finMemC-piU-dom : (a : FinEl) (f : FinFun) -> finMemC (PiCode a f) UCode -> finMemC a UCode
finMemC-piU-dom a f mem =
  finMemC-from (RANK (PiCode a f)) a UCode (bDomP a f) (Le0 (RANK (PiCode a f))) (fst mem)

finMemC-piU-allU : (a : FinEl) (f : FinFun) -> finMemC (PiCode a f) UCode -> finMemAllUC f a
finMemC-piU-allU a f mem =
  finMemAllUC-from (suc (RANK (PiCode a f))) f a (bAllUP a f) (fst (snd mem))

finMemC-piU-cft : (a : FinEl) (f : FinFun) -> finMemC (PiCode a f) UCode -> CoherentFunTail f
finMemC-piU-cft a f mem = snd (snd mem)

finMemC-piU-mk : (a : FinEl) (f : FinFun) ->
  finMemC a UCode -> finMemAllUC f a -> CoherentFunTail f -> finMemC (PiCode a f) UCode
finMemC-piU-mk a f dom allU cft =
  mkSigma (finMemC-to (RANK (PiCode a f)) a UCode (bDomP a f) (Le0 (RANK (PiCode a f))) dom)
          (mkSigma (finMemAllUC-to (suc (RANK (PiCode a f))) f a (bAllUP a f) allU) cft)

------------------------------------------------------------------------
-- FunEl membership
--   finMemC (FunEl g) (PiCode a f)  =  MB.finMem (suc L) (FunEl g)(PiCode a f),
--     L = max (RANK (FunEl g)) (RANK (PiCode a f))
--   = Pair (MB.finMemFun (suc L) g a f)
--          (Pair (CoherentFun g) (MB.finMem (suc L) (PiCode a f) UCode))
------------------------------------------------------------------------

private
  Lfp : (g : FinFun) (a : FinEl) (f : FinFun) -> Nat
  Lfp g a f = max (RANK (FunEl g)) (RANK (PiCode a f))

  -- suc (max (RANKFun g) (max (RANK a) (RANKFun f)))  <=  suc (Lfp g a f)
  bFunFP : (g : FinFun) (a : FinEl) (f : FinFun) ->
    Le (suc (max (RANKFun g) (max (RANK a) (RANKFun f)))) (suc (Lfp g a f))
  bFunFP g a f =
    Le-max-lub (RANKFun g) (max (RANK a) (RANKFun f)) (Lfp g a f)
      (Le-trans (RANKFun g) (RANK (FunEl g)) (Lfp g a f)
        (Le-suc (RANKFun g) (RANKFun g) (Le-refl (RANKFun g)))
        (Le-max-l (RANK (FunEl g)) (RANK (PiCode a f))))
      (Le-trans (max (RANK a) (RANKFun f)) (RANK (PiCode a f)) (Lfp g a f)
        (Le-suc (max (RANK a) (RANKFun f)) (max (RANK a) (RANKFun f)) (Le-refl (max (RANK a) (RANKFun f))))
        (Le-max-r (RANK (FunEl g)) (RANK (PiCode a f))))

  -- RANK (PiCode a f)  <=  suc (Lfp g a f)
  bWfFP : (g : FinFun) (a : FinEl) (f : FinFun) ->
    Le (RANK (PiCode a f)) (suc (Lfp g a f))
  bWfFP g a f =
    Le-suc (RANK (PiCode a f)) (Lfp g a f) (Le-max-r (RANK (FunEl g)) (RANK (PiCode a f)))

finMemC-funel-fun : (g : FinFun) (a : FinEl) (f : FinFun) ->
  finMemC (FunEl g) (PiCode a f) -> finMemFunC g a f
finMemC-funel-fun g a f mem =
  finMemFunC-from (suc (Lfp g a f)) g a f (bFunFP g a f) (fst mem)

finMemC-funel-coh : (g : FinFun) (a : FinEl) (f : FinFun) ->
  finMemC (FunEl g) (PiCode a f) -> CoherentFun g
finMemC-funel-coh g a f mem = fst (snd mem)

finMemC-funel-wf : (g : FinFun) (a : FinEl) (f : FinFun) ->
  finMemC (FunEl g) (PiCode a f) -> finMemC (PiCode a f) UCode
finMemC-funel-wf g a f mem =
  finMemC-from (suc (Lfp g a f)) (PiCode a f) UCode (bWfFP g a f) (Le0 (suc (Lfp g a f))) (snd (snd mem))

finMemC-funel-mk : (g : FinFun) (a : FinEl) (f : FinFun) ->
  finMemFunC g a f -> CoherentFun g -> finMemC (PiCode a f) UCode ->
  finMemC (FunEl g) (PiCode a f)
finMemC-funel-mk g a f fun coh wf =
  mkSigma (finMemFunC-to (suc (Lfp g a f)) g a f (bFunFP g a f) fun)
          (mkSigma coh
                   (finMemC-to (suc (Lfp g a f)) (PiCode a f) UCode (bWfFP g a f) (Le0 (suc (Lfp g a f))) wf))

------------------------------------------------------------------------
-- finMemFun cons/nil
--   finMemFunC (cons p ps) a f = MB.finMemFun (suc M0) (cons p ps) a f,
--     M0 = max (RANKFun (cons p ps)) (max (RANK a) (RANKFun f))
--   = Pair (Pair (MB.finMem M0 (fst p) a) (MB.finMem M0 (snd p) (EvalFun f (fst p))))
--          (MB.finMemFun (suc M0) ps a f)
------------------------------------------------------------------------

private
  M0f : (p : Pair FinEl FinEl) (ps : FinFun) (a : FinEl) (f : FinFun) -> Nat
  M0f p ps a f = max (RANKFun (cons p ps)) (max (RANK a) (RANKFun f))

  -- RANK (fst p) <= M0f
  bKeyF : (p : Pair FinEl FinEl) (ps : FinFun) (a : FinEl) (f : FinFun) ->
    Le (RANK (fst p)) (M0f p ps a f)
  bKeyF p ps a f =
    Le-trans (RANK (fst p)) (RANKFun (cons p ps)) (M0f p ps a f)
      (Le-max-l (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps)))
      (Le-max-l (RANKFun (cons p ps)) (max (RANK a) (RANKFun f)))

  -- RANK (snd p) <= M0f
  bValF : (p : Pair FinEl FinEl) (ps : FinFun) (a : FinEl) (f : FinFun) ->
    Le (RANK (snd p)) (M0f p ps a f)
  bValF p ps a f =
    Le-trans (RANK (snd p)) (RANKFun (cons p ps)) (M0f p ps a f)
      (Le-trans (RANK (snd p)) (max (RANK (snd p)) (RANKFun ps)) (RANKFun (cons p ps))
        (Le-max-l (RANK (snd p)) (RANKFun ps))
        (Le-max-r (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps))))
      (Le-max-l (RANKFun (cons p ps)) (max (RANK a) (RANKFun f)))

  -- RANK a <= M0f
  bArgF : (p : Pair FinEl FinEl) (ps : FinFun) (a : FinEl) (f : FinFun) ->
    Le (RANK a) (M0f p ps a f)
  bArgF p ps a f =
    Le-trans (RANK a) (max (RANK a) (RANKFun f)) (M0f p ps a f)
      (Le-max-l (RANK a) (RANKFun f))
      (Le-max-r (RANKFun (cons p ps)) (max (RANK a) (RANKFun f)))

  bEvF : (p : Pair FinEl FinEl) (ps : FinFun) (a : FinEl) (f : FinFun) ->
    Le (RANK (EvalFun f (fst p))) (M0f p ps a f)
  bEvF p ps a f =
    Le-trans (RANK (EvalFun f (fst p))) (RANKFun f) (M0f p ps a f)
      (RANK-EvalFun f (fst p))
      (Le-trans (RANKFun f) (max (RANK a) (RANKFun f)) (M0f p ps a f)
        (Le-max-r (RANK a) (RANKFun f))
        (Le-max-r (RANKFun (cons p ps)) (max (RANK a) (RANKFun f))))

  -- suc (max (RANKFun ps) (max (RANK a) (RANKFun f))) <= suc M0f
  bTlF : (p : Pair FinEl FinEl) (ps : FinFun) (a : FinEl) (f : FinFun) ->
    Le (suc (max (RANKFun ps) (max (RANK a) (RANKFun f)))) (suc (M0f p ps a f))
  bTlF p ps a f =
    Le-max-lub (RANKFun ps) (max (RANK a) (RANKFun f)) (M0f p ps a f)
      (Le-trans (RANKFun ps) (RANKFun (cons p ps)) (M0f p ps a f)
        (Le-trans (RANKFun ps) (max (RANK (snd p)) (RANKFun ps)) (RANKFun (cons p ps))
          (Le-max-r (RANK (snd p)) (RANKFun ps))
          (Le-max-r (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps))))
        (Le-max-l (RANKFun (cons p ps)) (max (RANK a) (RANKFun f))))
      (Le-max-r (RANKFun (cons p ps)) (max (RANK a) (RANKFun f)))

finMemFunC-nil : (a : FinEl) (f : FinFun) -> finMemFunC nil a f
finMemFunC-nil a f = tt

finMemFunC-hd-key : (p : Pair FinEl FinEl) (ps : FinFun) (a : FinEl) (f : FinFun) ->
  finMemFunC (cons p ps) a f -> finMemC (fst p) a
finMemFunC-hd-key p ps a f mem =
  finMemC-from (M0f p ps a f) (fst p) a (bKeyF p ps a f) (bArgF p ps a f) (fst (fst mem))

finMemFunC-hd-val : (p : Pair FinEl FinEl) (ps : FinFun) (a : FinEl) (f : FinFun) ->
  finMemFunC (cons p ps) a f -> finMemC (snd p) (EvalFun f (fst p))
finMemFunC-hd-val p ps a f mem =
  finMemC-from (M0f p ps a f) (snd p) (EvalFun f (fst p))
    (bValF p ps a f) (bEvF p ps a f) (snd (fst mem))

finMemFunC-tl : (p : Pair FinEl FinEl) (ps : FinFun) (a : FinEl) (f : FinFun) ->
  finMemFunC (cons p ps) a f -> finMemFunC ps a f
finMemFunC-tl p ps a f mem =
  finMemFunC-from (suc (M0f p ps a f)) ps a f (bTlF p ps a f) (snd mem)

finMemFunC-mk : (p : Pair FinEl FinEl) (ps : FinFun) (a : FinEl) (f : FinFun) ->
  finMemC (fst p) a -> finMemC (snd p) (EvalFun f (fst p)) -> finMemFunC ps a f ->
  finMemFunC (cons p ps) a f
finMemFunC-mk p ps a f key val tl =
  mkSigma (mkSigma (finMemC-to (M0f p ps a f) (fst p) a (bKeyF p ps a f) (bArgF p ps a f) key)
                   (finMemC-to (M0f p ps a f) (snd p) (EvalFun f (fst p))
                     (bValF p ps a f) (bEvF p ps a f) val))
          (finMemFunC-to (suc (M0f p ps a f)) ps a f (bTlF p ps a f) tl)

------------------------------------------------------------------------
-- finMemAllU cons/nil
--   finMemAllUC (cons p ps) a = MB.finMemAllU (suc N0) (cons p ps) a,
--     N0 = max (RANKFun (cons p ps)) (RANK a)
--   = Pair (Pair (MB.finMem N0 (fst p) a) (MB.finMem N0 (snd p) UCode))
--          (MB.finMemAllU (suc N0) ps a)
------------------------------------------------------------------------

private
  N0a : (p : Pair FinEl FinEl) (ps : FinFun) (a : FinEl) -> Nat
  N0a p ps a = max (RANKFun (cons p ps)) (RANK a)

  bKeyA : (p : Pair FinEl FinEl) (ps : FinFun) (a : FinEl) ->
    Le (RANK (fst p)) (N0a p ps a)
  bKeyA p ps a =
    Le-trans (RANK (fst p)) (RANKFun (cons p ps)) (N0a p ps a)
      (Le-max-l (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps)))
      (Le-max-l (RANKFun (cons p ps)) (RANK a))

  bValA : (p : Pair FinEl FinEl) (ps : FinFun) (a : FinEl) ->
    Le (RANK (snd p)) (N0a p ps a)
  bValA p ps a =
    Le-trans (RANK (snd p)) (RANKFun (cons p ps)) (N0a p ps a)
      (Le-trans (RANK (snd p)) (max (RANK (snd p)) (RANKFun ps)) (RANKFun (cons p ps))
        (Le-max-l (RANK (snd p)) (RANKFun ps))
        (Le-max-r (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps))))
      (Le-max-l (RANKFun (cons p ps)) (RANK a))

  bArgA : (p : Pair FinEl FinEl) (ps : FinFun) (a : FinEl) ->
    Le (RANK a) (N0a p ps a)
  bArgA p ps a = Le-max-r (RANKFun (cons p ps)) (RANK a)

  bTlA : (p : Pair FinEl FinEl) (ps : FinFun) (a : FinEl) ->
    Le (suc (max (RANKFun ps) (RANK a))) (suc (N0a p ps a))
  bTlA p ps a =
    Le-max-lub (RANKFun ps) (RANK a) (N0a p ps a)
      (Le-trans (RANKFun ps) (RANKFun (cons p ps)) (N0a p ps a)
        (Le-trans (RANKFun ps) (max (RANK (snd p)) (RANKFun ps)) (RANKFun (cons p ps))
          (Le-max-r (RANK (snd p)) (RANKFun ps))
          (Le-max-r (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps))))
        (Le-max-l (RANKFun (cons p ps)) (RANK a)))
      (Le-max-r (RANKFun (cons p ps)) (RANK a))

finMemAllUC-nil : (a : FinEl) -> finMemAllUC nil a
finMemAllUC-nil a = tt

finMemAllUC-hd-key : (p : Pair FinEl FinEl) (ps : FinFun) (a : FinEl) ->
  finMemAllUC (cons p ps) a -> finMemC (fst p) a
finMemAllUC-hd-key p ps a mem =
  finMemC-from (N0a p ps a) (fst p) a (bKeyA p ps a) (bArgA p ps a) (fst (fst mem))

finMemAllUC-hd-val : (p : Pair FinEl FinEl) (ps : FinFun) (a : FinEl) ->
  finMemAllUC (cons p ps) a -> finMemC (snd p) UCode
finMemAllUC-hd-val p ps a mem =
  finMemC-from (N0a p ps a) (snd p) UCode (bValA p ps a) (Le0 (N0a p ps a)) (snd (fst mem))

finMemAllUC-tl : (p : Pair FinEl FinEl) (ps : FinFun) (a : FinEl) ->
  finMemAllUC (cons p ps) a -> finMemAllUC ps a
finMemAllUC-tl p ps a mem =
  finMemAllUC-from (suc (N0a p ps a)) ps a (bTlA p ps a) (snd mem)

finMemAllUC-mk : (p : Pair FinEl FinEl) (ps : FinFun) (a : FinEl) ->
  finMemC (fst p) a -> finMemC (snd p) UCode -> finMemAllUC ps a ->
  finMemAllUC (cons p ps) a
finMemAllUC-mk p ps a key val tl =
  mkSigma (mkSigma (finMemC-to (N0a p ps a) (fst p) a (bKeyA p ps a) (bArgA p ps a) key)
                   (finMemC-to (N0a p ps a) (snd p) UCode (bValA p ps a) (Le0 (N0a p ps a)) val))
          (finMemAllUC-to (suc (N0a p ps a)) ps a (bTlA p ps a) tl)

------------------------------------------------------------------------
-- Projections  (structural recursion on the type / element FinEl)
------------------------------------------------------------------------

FinMem-coh-u : (u a : FinEl) -> finMemC u a -> Coherent u
FinMem-coh-u Bot          a            mem = tt
FinMem-coh-u UCode        UCode        mem = tt
FinMem-coh-u UCode        Bot          ()
FinMem-coh-u UCode        (FunEl g)    ()
FinMem-coh-u UCode        (PiCode a f) ()
FinMem-coh-u (FunEl g)    (PiCode a f) mem = finMemC-funel-coh g a f mem
FinMem-coh-u (FunEl g)    Bot          ()
FinMem-coh-u (FunEl g)    UCode        ()
FinMem-coh-u (FunEl g)    (FunEl h)    ()
FinMem-coh-u (PiCode a f) UCode        mem =
  mkSigma (FinMem-coh-u a UCode (finMemC-piU-dom a f mem)) (finMemC-piU-cft a f mem)
FinMem-coh-u (PiCode a f) Bot          ()
FinMem-coh-u (PiCode a f) (FunEl g)    ()
FinMem-coh-u (PiCode a f) (PiCode b g) ()

FinMem-a-in-U : (u a : FinEl) -> finMemC u a -> finMemC a UCode
FinMem-a-in-U Bot          a            mem = finMemC-bot-to a mem
FinMem-a-in-U UCode        UCode        mem = mem
FinMem-a-in-U UCode        Bot          ()
FinMem-a-in-U UCode        (FunEl g)    ()
FinMem-a-in-U UCode        (PiCode a f) ()
FinMem-a-in-U (FunEl g)    (PiCode a f) mem = finMemC-funel-wf g a f mem
FinMem-a-in-U (FunEl g)    Bot          ()
FinMem-a-in-U (FunEl g)    UCode        ()
FinMem-a-in-U (FunEl g)    (FunEl h)    ()
FinMem-a-in-U (PiCode a f) UCode        mem = tt
FinMem-a-in-U (PiCode a f) Bot          ()
FinMem-a-in-U (PiCode a f) (FunEl g)    ()
FinMem-a-in-U (PiCode a f) (PiCode b g) ()

coh-from-aU : (a : FinEl) -> finMemC a UCode -> Coherent a
coh-from-aU a mem = FinMem-coh-u a UCode mem

FinMem-coh-a : (u a : FinEl) -> finMemC u a -> Coherent a
FinMem-coh-a u a mem = coh-from-aU a (FinMem-a-in-U u a mem)
