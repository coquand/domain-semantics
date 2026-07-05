{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- LeqStageInterface.agda  (MIN/ — Pi + U fragment)
--
-- The public order properties on the STRUCTURAL LeCode / LeFunCode /
-- EvalFun (LeqStageBridge), derived by composing the bridges with the
-- stage-indexed pack (LeqStageProps2) and its LeqC collapse
-- (LeqStageOrder).  These have exactly the signatures PaperOrder
-- exports, so the re-founded PaperOrder is a thin re-export of this
-- file + LeqStageComp.
--
-- Pattern:
--   * pure order facts: LeqC-to-LeCode ∘ <LeqC fact> ∘ LeCode-to-LeqC.
--   * EvalFun facts: toLeqf/toLeq the hypotheses up to a canonical stage
--     m, apply the `*-n` lemma at m, ev-bridge the OB.ev-results back to
--     EvalFun, fromLeq the conclusion back to LeCode.
--
-- NO postulates.
------------------------------------------------------------------------

module ID.Domain.OrderInterface where

open import ID.Domain.Basic
  using ( Top ; tt ; Empty
        ; Nat ; zero ; suc ; max
        ; Le ; Le-refl ; Le-trans ; Le-max-l ; Le-max-r
        ; Pair ; mkSigma ; fst ; snd
        ; Eq ; refl ; Eq-sym ; Eq-transport
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; nil ; cons )
open import ID.Domain.OrderStage
open import ID.Domain.OrderComp
open import ID.Domain.OrderProps  using ( leq-Sup-lub )
open import ID.Domain.OrderProps2
open import ID.Domain.OrderStable
open import ID.Domain.OrderLaws
open import ID.Domain.OrderBridge

private
  -- canonical-stage bounds
  b2l : (a b : Nat) -> Le a (max a b)
  b2l = Le-max-l
  b2r : (a b : Nat) -> Le b (max a b)
  b2r = Le-max-r
  b3x : (x y z : Nat) -> Le x (max x (max y z))
  b3x x y z = Le-max-l x (max y z)
  b3y : (x y z : Nat) -> Le y (max x (max y z))
  b3y x y z = Le-trans y (max y z) (max x (max y z)) (Le-max-l y z) (Le-max-r x (max y z))
  b3z : (x y z : Nat) -> Le z (max x (max y z))
  b3z x y z = Le-trans z (max y z) (max x (max y z)) (Le-max-r y z) (Le-max-r x (max y z))

  -- structural-EvalFun rank bound via ev-bridge + RANK-ev
  ev-rank-pub : (m : Nat) (h : FinFun) (u : FinEl) ->
    Le (max (RANKFun h) (RANK u)) m -> Le (RANK (EvalFun h u)) (RANKFun h)
  ev-rank-pub m h u bnd =
    Eq-transport (\ x -> Le (RANK x) (RANKFun h)) (Eq-sym (ev-bridge m h u bnd))
      (RANK-ev (suc m) h u)

  evrk : (m : Nat) (h : FinFun) (u : FinEl) ->
    Le (RANKFun h) m -> Le (RANK u) m -> Le (RANK (EvalFun h u)) m
  evrk m h u bh bu =
    Le-trans (RANK (EvalFun h u)) (RANKFun h) m
      (ev-rank-pub m h u (Le-max-lub (RANKFun h) (RANK u) m bh bu)) bh

------------------------------------------------------------------------
-- pure order facts (one-liners through the LeCode <-> LeqC bridge)
------------------------------------------------------------------------

LeCode-Bot : (v : FinEl) -> LeCode Bot v
LeCode-Bot v = tt

LeCode-refl : (a : FinEl) -> Coherent a -> LeCode a a
LeCode-refl a ca = LeqC-to-LeCode a a (LeqC-refl a ca)

LeCode-trans : (x y z : FinEl) ->
  Coherent x -> Coherent y -> Coherent z ->
  LeCode x y -> LeCode y z -> LeCode x z
LeCode-trans x y z cx cy cz xy yz =
  LeqC-to-LeCode x z
    (LeqC-trans x y z cx cy cz (LeCode-to-LeqC x y xy) (LeCode-to-LeqC y z yz))

LeCode-Sup-left : (a b : FinEl) -> Comp a b -> Coherent a -> Coherent b ->
  LeCode a (Sup a b)
LeCode-Sup-left a b comp ca cb =
  LeqC-to-LeCode a (Sup a b) (LeqC-Sup-left a b comp ca cb)

LeCode-Sup-right : (a b : FinEl) -> Comp a b -> Coherent a -> Coherent b ->
  LeCode b (Sup a b)
LeCode-Sup-right a b comp ca cb =
  LeqC-to-LeCode b (Sup a b) (LeqC-Sup-right a b comp ca cb)

LeCode-Sup-lub : (a b c : FinEl) -> LeCode a c -> LeCode b c -> LeCode (Sup a b) c
LeCode-Sup-lub a b c ac bc =
  LeqC-to-LeCode (Sup a b) c
    (LeqC-Sup-lub a b c (LeCode-to-LeqC a c ac) (LeCode-to-LeqC b c bc))

Comp-down : (u u' v : FinEl) -> LeCode u u' -> Comp u' v -> Comp u v
Comp-down u u' v le c = LeqC-Comp-down u u' v (LeCode-to-LeqC u u' le) c

LeCode-Comp : (u v w : FinEl) -> Coherent w -> LeCode u w -> LeCode v w -> Comp u v
LeCode-Comp u v w coh lu lv =
  LeqC-Comp u v w coh (LeCode-to-LeqC u w lu) (LeCode-to-LeqC v w lv)

------------------------------------------------------------------------
-- LeFunCode facts (through the LeFunCode <-> OB.leqf bridge)
------------------------------------------------------------------------

LeFunCode-refl : (g : FinFun) -> CoherentFunTail g -> LeFunCode g g
LeFunCode-refl g cohg =
  let bgg = Le-max-lub (RANKFun g) (RANKFun g) (RANKFun g) (Le-refl (RANKFun g)) (Le-refl (RANKFun g))
  in fromLeqf (RANKFun g) g g bgg (LeFunCode-refl-n (RANKFun g) g (Le-refl (RANKFun g)) cohg)

LeFunCode-trans : (g h k : FinFun) ->
  CoherentFunTail g -> CoherentFunTail h -> CoherentFunTail k ->
  LeFunCode g h -> LeFunCode h k -> LeFunCode g k
LeFunCode-trans g h k cohg cohh cohk gh hk =
  let m  = max (RANKFun g) (max (RANKFun h) (RANKFun k))
      bg = b3x (RANKFun g) (RANKFun h) (RANKFun k)
      bh = b3y (RANKFun g) (RANKFun h) (RANKFun k)
      bk = b3z (RANKFun g) (RANKFun h) (RANKFun k)
      ghm = toLeqf m g h (Le-max-lub (RANKFun g) (RANKFun h) m bg bh) gh
      hkm = toLeqf m h k (Le-max-lub (RANKFun h) (RANKFun k) m bh bk) hk
      r   = LeFunCode-trans-n m g h k bg bh bk cohg cohh cohk ghm hkm
  in fromLeqf m g k (Le-max-lub (RANKFun g) (RANKFun k) m bg bk) r

------------------------------------------------------------------------
-- EvalFun facts (bridge OB.ev <-> EvalFun on both sides)
------------------------------------------------------------------------

Coherent-EvalFun : (k : FinFun) (u : FinEl) ->
  CoherentFunTail k -> Coherent u -> Coherent (EvalFun k u)
Coherent-EvalFun k u cohk cu =
  let m  = max (RANKFun k) (RANK u)
      bk = b2l (RANKFun k) (RANK u)
      bu = b2r (RANKFun k) (RANK u)
  in Eq-transport Coherent (Eq-sym (ev-bridge m k u (Le-refl m)))
       (Coherent-EvalFun-n m k u bk bu cohk cu)

Comp-value-EvalFun : (q : Pair FinEl FinEl) (rest : FinFun) (xi : FinEl) ->
  LeCode (fst q) xi -> Coherent xi -> Coherent (snd q) ->
  CoherentWith q rest -> CompStepFun q rest ->
  Comp (snd q) (EvalFun rest xi)
Comp-value-EvalFun q rest xi le cxi cohv cw csf =
  let m   = max (RANK (fst q)) (max (RANK xi) (RANKFun rest))
      bkq = b3x (RANK (fst q)) (RANK xi) (RANKFun rest)
      bxi = b3y (RANK (fst q)) (RANK xi) (RANKFun rest)
      brt = b3z (RANK (fst q)) (RANK xi) (RANKFun rest)
      lem = toLeq m (fst q) xi (Le-max-lub (RANK (fst q)) (RANK xi) m bkq bxi) le
      r   = Comp-value-EvalFun-n m q rest xi bkq bxi brt lem cxi cohv cw csf
  in Eq-transport (\ x -> Comp (snd q) x) (Eq-sym (ev-bridge m rest xi
       (Le-max-lub (RANKFun rest) (RANK xi) m brt bxi))) r

EvalFun-mon : (h k : FinFun) (u : FinEl) ->
  CoherentFunTail h -> CoherentFunTail k -> Coherent u ->
  LeFunCode h k -> LeCode (EvalFun h u) (EvalFun k u)
EvalFun-mon h k u cohh cohk cu hk =
  let m  = max (RANKFun h) (max (RANKFun k) (RANK u))
      bh = b3x (RANKFun h) (RANKFun k) (RANK u)
      bk = b3y (RANKFun h) (RANKFun k) (RANK u)
      bu = b3z (RANKFun h) (RANKFun k) (RANK u)
      hkm = toLeqf m h k (Le-max-lub (RANKFun h) (RANKFun k) m bh bk) hk
      r   = EvalFun-mon-n m h k u bh bk bu cohh cohk cu hkm
      -- r : OB.leq m (OB.ev (suc m) h u) (OB.ev (suc m) k u)
      r1 : OB.leq m (EvalFun h u) (OB.ev (suc m) k u)
      r1 = Eq-transport (\ x -> OB.leq m x (OB.ev (suc m) k u))
             (Eq-sym (ev-bridge m h u (Le-max-lub (RANKFun h) (RANK u) m bh bu))) r
      r2 : OB.leq m (EvalFun h u) (EvalFun k u)
      r2 = Eq-transport (\ x -> OB.leq m (EvalFun h u) x)
             (Eq-sym (ev-bridge m k u (Le-max-lub (RANKFun k) (RANK u) m bk bu))) r1
  in fromLeq m (EvalFun h u) (EvalFun k u)
       (Le-max-lub (RANK (EvalFun h u)) (RANK (EvalFun k u)) m
         (evrk m h u bh bu) (evrk m k u bk bu))
       r2

EvalFun-mon-arg : (k : FinFun) (u v : FinEl) ->
  LeCode u v -> CoherentFunTail k -> Coherent u -> Coherent v ->
  LeCode (EvalFun k u) (EvalFun k v)
EvalFun-mon-arg k u v le cohk cu cv =
  let m  = max (RANKFun k) (max (RANK u) (RANK v))
      bk = b3x (RANKFun k) (RANK u) (RANK v)
      bu = b3y (RANKFun k) (RANK u) (RANK v)
      bv = b3z (RANKFun k) (RANK u) (RANK v)
      lem = toLeq m u v (Le-max-lub (RANK u) (RANK v) m bu bv) le
      r   = EvalFun-mon-arg-n m k u v bk bu bv lem cohk cu cv
      r1 : OB.leq m (EvalFun k u) (OB.ev (suc m) k v)
      r1 = Eq-transport (\ x -> OB.leq m x (OB.ev (suc m) k v))
             (Eq-sym (ev-bridge m k u (Le-max-lub (RANKFun k) (RANK u) m bk bu))) r
      r2 : OB.leq m (EvalFun k u) (EvalFun k v)
      r2 = Eq-transport (\ x -> OB.leq m (EvalFun k u) x)
             (Eq-sym (ev-bridge m k v (Le-max-lub (RANKFun k) (RANK v) m bk bv))) r1
  in fromLeq m (EvalFun k u) (EvalFun k v)
       (Le-max-lub (RANK (EvalFun k u)) (RANK (EvalFun k v)) m
         (evrk m k u bk bu) (evrk m k v bk bv))
       r2
