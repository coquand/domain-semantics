{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- FinMemStageShift.agda  (MIN/ — Pi + U fragment)
--
-- Stage-shift for the membership predicate: above the canonical RANK
-- level the stage is irrelevant.  Mirrors LeqStageStable's
-- leq-lift/leq-lower/leq-shift, iterating goodMemStab's one-step
-- transports.  Then the unfolding isos for the public collapsed
-- finMemC / finMemAllUC / finMemFunC (the "expected computation rules"
-- of FinMem, now as propositional iso pairs), and the projections.
--
-- NO TERMINATING, NO postulates.
------------------------------------------------------------------------

module MIN.FinMemStageShift where

open import MIN.Basic
  using ( Top ; tt ; Empty
        ; Nat ; zero ; suc ; max
        ; Le ; Le-refl ; Le-suc ; Le-trans ; Le-max-l ; Le-max-r
        ; Pair ; mkSigma ; fst ; snd ; Sigma
        ; Eq ; refl ; Eq-sym ; Eq-transport ; Eq-cong
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; nil ; cons )
open import MIN.PaperOrder
  using ( RANK ; RANKFun ; EvalFun ; CoherentFunTail ; Le-max-lub )
open import MIN.FinMemStage
open import MIN.FinMemStageStable

private
  plus : Nat -> Nat -> Nat
  plus zero    a = a
  plus (suc g) a = suc (plus g a)

  plus-0 : (g : Nat) -> Eq (plus g zero) g
  plus-0 zero    = refl
  plus-0 (suc g) = Eq-cong suc (plus-0 g)

  plus-suc : (g a : Nat) -> Eq (plus g (suc a)) (suc (plus g a))
  plus-suc zero    a = refl
  plus-suc (suc g) a = Eq-cong suc (plus-suc g a)

  Le-plus : (g a : Nat) -> Le a (plus g a)
  Le-plus zero    a = Le-refl a
  Le-plus (suc g) a = Le-suc a (plus g a) (Le-plus g a)

  Le-gap : (a b : Nat) -> Le a b -> Sigma Nat (\ g -> Eq b (plus g a))
  Le-gap zero    b       lab = mkSigma b (Eq-sym (plus-0 b))
  Le-gap (suc a) zero    ()
  Le-gap (suc a) (suc b) lab =
    let r = Le-gap a b lab
    in mkSigma (fst r)
         (Eq-transport (\ x -> Eq (suc b) x) (Eq-sym (plus-suc (fst r) a))
           (Eq-cong suc (snd r)))

------------------------------------------------------------------------
-- finMem shift
------------------------------------------------------------------------

finMem-lift : (g j : Nat) (u a : FinEl) -> Le (RANK u) j -> Le (RANK a) j ->
  MB.finMem j u a -> MB.finMem (plus g j) u a
finMem-lift zero    j u a bu ba mem = mem
finMem-lift (suc g) j u a bu ba mem =
  MemStabPack.fm-fwd (goodMemStab (plus g j)) u a
    (Le-trans (RANK u) j (plus g j) bu (Le-plus g j))
    (Le-trans (RANK a) j (plus g j) ba (Le-plus g j))
    (finMem-lift g j u a bu ba mem)

finMem-lower : (g j : Nat) (u a : FinEl) -> Le (RANK u) j -> Le (RANK a) j ->
  MB.finMem (plus g j) u a -> MB.finMem j u a
finMem-lower zero    j u a bu ba mem = mem
finMem-lower (suc g) j u a bu ba mem =
  finMem-lower g j u a bu ba
    (MemStabPack.fm-bwd (goodMemStab (plus g j)) u a
      (Le-trans (RANK u) j (plus g j) bu (Le-plus g j))
      (Le-trans (RANK a) j (plus g j) ba (Le-plus g j))
      mem)

finMem-shift : (j k : Nat) (u a : FinEl) ->
  Le (RANK u) j -> Le (RANK a) j -> Le (RANK u) k -> Le (RANK a) k ->
  MB.finMem j u a -> MB.finMem k u a
finMem-shift j k u a bju bja bku bka mem =
  let M   = max (RANK u) (RANK a)
      bMu = Le-max-l (RANK u) (RANK a)
      bMa = Le-max-r (RANK u) (RANK a)
      bjM = Le-max-lub (RANK u) (RANK a) j bju bja
      bkM = Le-max-lub (RANK u) (RANK a) k bku bka
      gj  = Le-gap M j bjM
      gk  = Le-gap M k bkM
      mM  = finMem-lower (fst gj) M u a bMu bMa
              (Eq-transport (\ x -> MB.finMem x u a) (snd gj) mem)
      mk  = finMem-lift (fst gk) M u a bMu bMa mM
  in Eq-transport (\ x -> MB.finMem x u a) (Eq-sym (snd gk)) mk

------------------------------------------------------------------------
-- finMemAllU shift  (floor = suc (max (RANKFun f) (RANK a)))
------------------------------------------------------------------------

finMemAllU-lift : (g j : Nat) (f : FinFun) (a : FinEl) ->
  Le (suc (max (RANKFun f) (RANK a))) j ->
  MB.finMemAllU j f a -> MB.finMemAllU (plus g j) f a
finMemAllU-lift zero    j f a bnd mem = mem
finMemAllU-lift (suc g) j f a bnd mem =
  MemStabPack.fa-fwd (goodMemStab (plus g j)) f a
    (Le-trans (suc (max (RANKFun f) (RANK a))) j (plus g j) bnd (Le-plus g j))
    (finMemAllU-lift g j f a bnd mem)

finMemAllU-lower : (g j : Nat) (f : FinFun) (a : FinEl) ->
  Le (suc (max (RANKFun f) (RANK a))) j ->
  MB.finMemAllU (plus g j) f a -> MB.finMemAllU j f a
finMemAllU-lower zero    j f a bnd mem = mem
finMemAllU-lower (suc g) j f a bnd mem =
  finMemAllU-lower g j f a bnd
    (MemStabPack.fa-bwd (goodMemStab (plus g j)) f a
      (Le-trans (suc (max (RANKFun f) (RANK a))) j (plus g j) bnd (Le-plus g j))
      mem)

finMemAllU-shift : (j k : Nat) (f : FinFun) (a : FinEl) ->
  Le (suc (max (RANKFun f) (RANK a))) j -> Le (suc (max (RANKFun f) (RANK a))) k ->
  MB.finMemAllU j f a -> MB.finMemAllU k f a
finMemAllU-shift j k f a bj bk mem =
  let N  = suc (max (RANKFun f) (RANK a))
      gj = Le-gap N j bj
      gk = Le-gap N k bk
      mN = finMemAllU-lower (fst gj) N f a (Le-refl N)
             (Eq-transport (\ x -> MB.finMemAllU x f a) (snd gj) mem)
      mk = finMemAllU-lift (fst gk) N f a (Le-refl N) mN
  in Eq-transport (\ x -> MB.finMemAllU x f a) (Eq-sym (snd gk)) mk

------------------------------------------------------------------------
-- finMemFun shift  (floor = suc (max (RANKFun g) (max (RANK a) (RANKFun f))))
------------------------------------------------------------------------

finMemFun-lift : (k j : Nat) (g : FinFun) (a : FinEl) (f : FinFun) ->
  Le (suc (max (RANKFun g) (max (RANK a) (RANKFun f)))) j ->
  MB.finMemFun j g a f -> MB.finMemFun (plus k j) g a f
finMemFun-lift zero    j g a f bnd mem = mem
finMemFun-lift (suc k) j g a f bnd mem =
  MemStabPack.ff-fwd (goodMemStab (plus k j)) g a f
    (Le-trans (suc (max (RANKFun g) (max (RANK a) (RANKFun f)))) j (plus k j)
      bnd (Le-plus k j))
    (finMemFun-lift k j g a f bnd mem)

finMemFun-lower : (k j : Nat) (g : FinFun) (a : FinEl) (f : FinFun) ->
  Le (suc (max (RANKFun g) (max (RANK a) (RANKFun f)))) j ->
  MB.finMemFun (plus k j) g a f -> MB.finMemFun j g a f
finMemFun-lower zero    j g a f bnd mem = mem
finMemFun-lower (suc k) j g a f bnd mem =
  finMemFun-lower k j g a f bnd
    (MemStabPack.ff-bwd (goodMemStab (plus k j)) g a f
      (Le-trans (suc (max (RANKFun g) (max (RANK a) (RANKFun f)))) j (plus k j)
        bnd (Le-plus k j))
      mem)

finMemFun-shift : (j k : Nat) (g : FinFun) (a : FinEl) (f : FinFun) ->
  Le (suc (max (RANKFun g) (max (RANK a) (RANKFun f)))) j ->
  Le (suc (max (RANKFun g) (max (RANK a) (RANKFun f)))) k ->
  MB.finMemFun j g a f -> MB.finMemFun k g a f
finMemFun-shift j k g a f bj bk mem =
  let N  = suc (max (RANKFun g) (max (RANK a) (RANKFun f)))
      gj = Le-gap N j bj
      gk = Le-gap N k bk
      mN = finMemFun-lower (fst gj) N g a f (Le-refl N)
             (Eq-transport (\ x -> MB.finMemFun x g a f) (snd gj) mem)
      mk = finMemFun-lift (fst gk) N g a f (Le-refl N) mN
  in Eq-transport (\ x -> MB.finMemFun x g a f) (Eq-sym (snd gk)) mk
