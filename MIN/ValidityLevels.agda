{-# OPTIONS --without-K #-}
------------------------------------------------------------------------
-- ValidityLevels.agda  (MIN/ — Pi + U fragment)
--
-- Step 3 foundation: level-independence of the stratified relations above
-- a code's rank, derived from ValidityStability by iterating the
-- single-step transports.  This is THE consumer of stability.
--
--   shiftVTy / shiftEVTy : valty/eqvalty at any two levels >= suc (RANK a)
--                          agree (transport between them).
--
-- Demonstration that the public canonical-level relations get the property
-- package: downValTy2-pub / downEqValTy2-pub on ValidityStratified.ValTy2.
--
-- No NO_POSITIVITY_CHECK, no postulates.
------------------------------------------------------------------------

module MIN.ValidityLevels where

open import MIN.Basic
  using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ; Sigma ;
         Eq ; refl ; Eq-transport ; Eq-sym ; Eq-cong ;
         Le ; Le-refl ; Le-trans ; Le-suc ; max ; Le-max-l ; Le-max-r ;
         FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun)
open import MIN.RawSyntax using (Expr)
open import MIN.TypingRules using (Ctx ; HasType ; ConvTm)
open import MIN.PaperSemantics using (Coherent ; FinMem ; LeCode ; Comp ; Sup)
open import MIN.Rank using (RANK ; Le-max-lub ; RANK-Sup)
open import MIN.ValidityStratified
open import MIN.ValidityStability using (vtyU ; vtyD ; evtyU ; evtyD ; vlU ; vlD ; evlU ; evlD)
open import MIN.ValidityMono using (MonoPack ; goodStage)
open import MIN.ValidityProps using (FwdPack ; goodStageFwd ; SymTransPack ; goodStageSymTrans ; SupPack ; goodStageSup ; ReflPack ; goodStageRefl ; TransportPack ; goodStageTransport ; BetaPack ; goodStageBeta)
open import MIN.Reduction using (HeadRed)

------------------------------------------------------------------------
-- Gap arithmetic
------------------------------------------------------------------------

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

-- Le a b  =>  b = some gap + a
Le-gap : (a b : Nat) -> Le a b -> Sigma Nat (\ g -> Eq b (plus g a))
Le-gap zero    b       lab = mkSigma b (Eq-sym (plus-0 b))
Le-gap (suc a) zero    ()
Le-gap (suc a) (suc b) lab =
  let r = Le-gap a b lab
  in mkSigma (fst r)
       (Eq-transport (\ x -> Eq (suc b) x) (Eq-sym (plus-suc (fst r) a))
         (Eq-cong suc (snd r)))

------------------------------------------------------------------------
-- valty: lift / lower by a gap, then shift between arbitrary levels
------------------------------------------------------------------------

liftVTy : (g j : Nat) {m : Nat} (G : Ctx m) (M : Expr m) (a : FinEl) ->
  Le (suc (RANK a)) j ->
  Bundle.valty (Stage j) G M a -> Bundle.valty (Stage (plus g j)) G M a
liftVTy zero    j G M a bnd vt = vt
liftVTy (suc g) j G M a bnd vt =
  vtyU (plus g j) G M a (Le-trans (suc (RANK a)) j (plus g j) bnd (Le-plus g j))
    (liftVTy g j G M a bnd vt)

lowerVTy : (g j : Nat) {m : Nat} (G : Ctx m) (M : Expr m) (a : FinEl) ->
  Le (suc (RANK a)) j ->
  Bundle.valty (Stage (plus g j)) G M a -> Bundle.valty (Stage j) G M a
lowerVTy zero    j G M a bnd vt = vt
lowerVTy (suc g) j G M a bnd vt =
  lowerVTy g j G M a bnd
    (vtyD (plus g j) G M a (Le-trans (suc (RANK a)) j (plus g j) bnd (Le-plus g j)) vt)

shiftVTy : (j k : Nat) {m : Nat} (G : Ctx m) (M : Expr m) (a : FinEl) ->
  Le (suc (RANK a)) j -> Le (suc (RANK a)) k ->
  Bundle.valty (Stage j) G M a -> Bundle.valty (Stage k) G M a
shiftVTy j k G M a bj bk vt =
  let gj-r = Le-gap (suc (RANK a)) j bj
      gk-r = Le-gap (suc (RANK a)) k bk
      vt-pj = Eq-transport (\ x -> Bundle.valty (Stage x) G M a) (snd gj-r) vt
      vt-c  = lowerVTy (fst gj-r) (suc (RANK a)) G M a (Le-refl (suc (RANK a))) vt-pj
      vt-pk = liftVTy (fst gk-r) (suc (RANK a)) G M a (Le-refl (suc (RANK a))) vt-c
  in Eq-transport (\ x -> Bundle.valty (Stage x) G M a) (Eq-sym (snd gk-r)) vt-pk

------------------------------------------------------------------------
-- eqvalty: same machinery
------------------------------------------------------------------------

liftEVTy : (g j : Nat) {m : Nat} (G : Ctx m) (M N : Expr m) (a : FinEl) ->
  Le (suc (RANK a)) j ->
  Bundle.eqvalty (Stage j) G M N a -> Bundle.eqvalty (Stage (plus g j)) G M N a
liftEVTy zero    j G M N a bnd vt = vt
liftEVTy (suc g) j G M N a bnd vt =
  evtyU (plus g j) G M N a (Le-trans (suc (RANK a)) j (plus g j) bnd (Le-plus g j))
    (liftEVTy g j G M N a bnd vt)

lowerEVTy : (g j : Nat) {m : Nat} (G : Ctx m) (M N : Expr m) (a : FinEl) ->
  Le (suc (RANK a)) j ->
  Bundle.eqvalty (Stage (plus g j)) G M N a -> Bundle.eqvalty (Stage j) G M N a
lowerEVTy zero    j G M N a bnd vt = vt
lowerEVTy (suc g) j G M N a bnd vt =
  lowerEVTy g j G M N a bnd
    (evtyD (plus g j) G M N a (Le-trans (suc (RANK a)) j (plus g j) bnd (Le-plus g j)) vt)

shiftEVTy : (j k : Nat) {m : Nat} (G : Ctx m) (M N : Expr m) (a : FinEl) ->
  Le (suc (RANK a)) j -> Le (suc (RANK a)) k ->
  Bundle.eqvalty (Stage j) G M N a -> Bundle.eqvalty (Stage k) G M N a
shiftEVTy j k G M N a bj bk vt =
  let gj-r = Le-gap (suc (RANK a)) j bj
      gk-r = Le-gap (suc (RANK a)) k bk
      vt-pj = Eq-transport (\ x -> Bundle.eqvalty (Stage x) G M N a) (snd gj-r) vt
      vt-c  = lowerEVTy (fst gj-r) (suc (RANK a)) G M N a (Le-refl (suc (RANK a))) vt-pj
      vt-pk = liftEVTy (fst gk-r) (suc (RANK a)) G M N a (Le-refl (suc (RANK a))) vt-c
  in Eq-transport (\ x -> Bundle.eqvalty (Stage x) G M N a) (Eq-sym (snd gk-r)) vt-pk

------------------------------------------------------------------------
-- Demonstration: the property package on the PUBLIC canonical-level
-- relations (ValidityStratified.ValTy2 / EqValTy2).
--
--   ValTy2 G M a = valty (Stage (suc (RANK a))) G M a
--
-- downValTy2 takes ValTy2 at u1 (level suc (RANK u1)) to ValTy2 at u0
-- (level suc (RANK u0)) via a common level K = suc (max (RANK u0) (RANK u1)),
-- bridging with shiftVTy and applying goodStage at K.
------------------------------------------------------------------------

downValTy2-pub : {m : Nat} (G : Ctx m) (M : Expr m) (u0 u1 : FinEl) ->
  LeCode u0 u1 -> FinMem u0 UCode -> FinMem u1 UCode ->
  ValTy2 G M u1 -> ValTy2 G M u0
downValTy2-pub G M u0 u1 le fm0 fm1 vt1 =
  let vt1-K = shiftVTy (suc (RANK u1)) (suc (max (RANK u0) (RANK u1))) G M u1
                (Le-refl (suc (RANK u1))) (Le-max-r (RANK u0) (RANK u1)) vt1
      vt0-K = MonoPack.downValTy2 (goodStage (suc (max (RANK u0) (RANK u1)))) G M u0 u1 le fm0 fm1 vt1-K
  in shiftVTy (suc (max (RANK u0) (RANK u1))) (suc (RANK u0)) G M u0
       (Le-max-l (RANK u0) (RANK u1)) (Le-refl (suc (RANK u0))) vt0-K

downEqValTy2-pub : {m : Nat} (G : Ctx m) (M N : Expr m) (u0 u1 : FinEl) ->
  LeCode u0 u1 -> FinMem u0 UCode -> FinMem u1 UCode ->
  EqValTy2 G M N u1 -> EqValTy2 G M N u0
downEqValTy2-pub G M N u0 u1 le fm0 fm1 eq1 =
  let eq1-K = shiftEVTy (suc (RANK u1)) (suc (max (RANK u0) (RANK u1))) G M N u1
                (Le-refl (suc (RANK u1))) (Le-max-r (RANK u0) (RANK u1)) eq1
      eq0-K = MonoPack.downEqValTy2 (goodStage (suc (max (RANK u0) (RANK u1)))) G M N u0 u1 le fm0 fm1 eq1-K
  in shiftEVTy (suc (max (RANK u0) (RANK u1))) (suc (RANK u0)) G M N u0
       (Le-max-l (RANK u0) (RANK u1)) (Le-refl (suc (RANK u0))) eq0-K

------------------------------------------------------------------------
-- val: lift / lower by a gap, then shift between arbitrary levels.
-- Floor c = suc (max (RANK u) (RANK a)); needs BOTH bounds.
------------------------------------------------------------------------

liftVl : (g j : Nat) {m : Nat} (G : Ctx m) (M A : Expr m) (u a : FinEl) ->
  Le (suc (RANK u)) j -> Le (suc (RANK a)) j ->
  Bundle.val (Stage j) G M A u a -> Bundle.val (Stage (plus g j)) G M A u a
liftVl zero    j G M A u a bu ba vt = vt
liftVl (suc g) j G M A u a bu ba vt =
  vlU (plus g j) G M A u a
    (Le-trans (suc (RANK u)) j (plus g j) bu (Le-plus g j))
    (Le-trans (suc (RANK a)) j (plus g j) ba (Le-plus g j))
    (liftVl g j G M A u a bu ba vt)

lowerVl : (g j : Nat) {m : Nat} (G : Ctx m) (M A : Expr m) (u a : FinEl) ->
  Le (suc (RANK u)) j -> Le (suc (RANK a)) j ->
  Bundle.val (Stage (plus g j)) G M A u a -> Bundle.val (Stage j) G M A u a
lowerVl zero    j G M A u a bu ba vt = vt
lowerVl (suc g) j G M A u a bu ba vt =
  lowerVl g j G M A u a bu ba
    (vlD (plus g j) G M A u a
      (Le-trans (suc (RANK u)) j (plus g j) bu (Le-plus g j))
      (Le-trans (suc (RANK a)) j (plus g j) ba (Le-plus g j)) vt)

shiftVl : (j k : Nat) {m : Nat} (G : Ctx m) (M A : Expr m) (u a : FinEl) ->
  Le (suc (RANK u)) j -> Le (suc (RANK a)) j ->
  Le (suc (RANK u)) k -> Le (suc (RANK a)) k ->
  Bundle.val (Stage j) G M A u a -> Bundle.val (Stage k) G M A u a
shiftVl j k G M A u a buj baj buk bak vt =
  let lecj = Le-max-lub (suc (RANK u)) (suc (RANK a)) j buj baj
      leck = Le-max-lub (suc (RANK u)) (suc (RANK a)) k buk bak
      gj-r = Le-gap (suc (max (RANK u) (RANK a))) j lecj
      gk-r = Le-gap (suc (max (RANK u) (RANK a))) k leck
      cu   = Le-max-l (RANK u) (RANK a)
      ca   = Le-max-r (RANK u) (RANK a)
      vt-pj = Eq-transport (\ x -> Bundle.val (Stage x) G M A u a) (snd gj-r) vt
      vt-c  = lowerVl (fst gj-r) (suc (max (RANK u) (RANK a))) G M A u a cu ca vt-pj
      vt-pk = liftVl (fst gk-r) (suc (max (RANK u) (RANK a))) G M A u a cu ca vt-c
  in Eq-transport (\ x -> Bundle.val (Stage x) G M A u a) (Eq-sym (snd gk-r)) vt-pk

------------------------------------------------------------------------
-- eqval: same machinery
------------------------------------------------------------------------

liftEVl : (g j : Nat) {m : Nat} (G : Ctx m) (M N A : Expr m) (u a : FinEl) ->
  Le (suc (RANK u)) j -> Le (suc (RANK a)) j ->
  Bundle.eqval (Stage j) G M N A u a -> Bundle.eqval (Stage (plus g j)) G M N A u a
liftEVl zero    j G M N A u a bu ba vt = vt
liftEVl (suc g) j G M N A u a bu ba vt =
  evlU (plus g j) G M N A u a
    (Le-trans (suc (RANK u)) j (plus g j) bu (Le-plus g j))
    (Le-trans (suc (RANK a)) j (plus g j) ba (Le-plus g j))
    (liftEVl g j G M N A u a bu ba vt)

lowerEVl : (g j : Nat) {m : Nat} (G : Ctx m) (M N A : Expr m) (u a : FinEl) ->
  Le (suc (RANK u)) j -> Le (suc (RANK a)) j ->
  Bundle.eqval (Stage (plus g j)) G M N A u a -> Bundle.eqval (Stage j) G M N A u a
lowerEVl zero    j G M N A u a bu ba vt = vt
lowerEVl (suc g) j G M N A u a bu ba vt =
  lowerEVl g j G M N A u a bu ba
    (evlD (plus g j) G M N A u a
      (Le-trans (suc (RANK u)) j (plus g j) bu (Le-plus g j))
      (Le-trans (suc (RANK a)) j (plus g j) ba (Le-plus g j)) vt)

shiftEVl : (j k : Nat) {m : Nat} (G : Ctx m) (M N A : Expr m) (u a : FinEl) ->
  Le (suc (RANK u)) j -> Le (suc (RANK a)) j ->
  Le (suc (RANK u)) k -> Le (suc (RANK a)) k ->
  Bundle.eqval (Stage j) G M N A u a -> Bundle.eqval (Stage k) G M N A u a
shiftEVl j k G M N A u a buj baj buk bak vt =
  let lecj = Le-max-lub (suc (RANK u)) (suc (RANK a)) j buj baj
      leck = Le-max-lub (suc (RANK u)) (suc (RANK a)) k buk bak
      gj-r = Le-gap (suc (max (RANK u) (RANK a))) j lecj
      gk-r = Le-gap (suc (max (RANK u) (RANK a))) k leck
      cu   = Le-max-l (RANK u) (RANK a)
      ca   = Le-max-r (RANK u) (RANK a)
      vt-pj = Eq-transport (\ x -> Bundle.eqval (Stage x) G M N A u a) (snd gj-r) vt
      vt-c  = lowerEVl (fst gj-r) (suc (max (RANK u) (RANK a))) G M N A u a cu ca vt-pj
      vt-pk = liftEVl (fst gk-r) (suc (max (RANK u) (RANK a))) G M N A u a cu ca vt-c
  in Eq-transport (\ x -> Bundle.eqval (Stage x) G M N A u a) (Eq-sym (snd gk-r)) vt-pk

------------------------------------------------------------------------
-- Rank-bound helpers for the common levels (2-way and 3-way max)
------------------------------------------------------------------------

private
  b2-l : (x y : FinEl) -> Le (suc (RANK x)) (suc (max (RANK x) (RANK y)))
  b2-l x y = Le-max-l (RANK x) (RANK y)
  b2-r : (x y : FinEl) -> Le (suc (RANK y)) (suc (max (RANK x) (RANK y)))
  b2-r x y = Le-max-r (RANK x) (RANK y)
  b3-l : (x y z : FinEl) -> Le (suc (RANK x)) (suc (max (RANK x) (max (RANK y) (RANK z))))
  b3-l x y z = Le-max-l (RANK x) (max (RANK y) (RANK z))
  b3-m : (x y z : FinEl) -> Le (suc (RANK y)) (suc (max (RANK x) (max (RANK y) (RANK z))))
  b3-m x y z = Le-trans (RANK y) (max (RANK y) (RANK z)) (max (RANK x) (max (RANK y) (RANK z)))
                 (Le-max-l (RANK y) (RANK z)) (Le-max-r (RANK x) (max (RANK y) (RANK z)))
  b3-r : (x y z : FinEl) -> Le (suc (RANK z)) (suc (max (RANK x) (max (RANK y) (RANK z))))
  b3-r x y z = Le-trans (RANK z) (max (RANK y) (RANK z)) (max (RANK x) (max (RANK y) (RANK z)))
                 (Le-max-r (RANK y) (RANK z)) (Le-max-r (RANK x) (max (RANK y) (RANK z)))

------------------------------------------------------------------------
-- The index-free monotonicity package on the public relations
-- (down / up / restrict, for Val2 and EqVal2).  Bridge through the
-- 3-way-max level K and apply goodStage there.
------------------------------------------------------------------------

downVal2-pub : {m : Nat} (G : Ctx m) (M T : Expr m) (u a0 a1 : FinEl) ->
  LeCode a0 a1 -> FinMem u a0 -> Coherent a0 -> FinMem a1 UCode ->
  Val2 G M T u a1 -> Val2 G M T u a0
downVal2-pub G M T u a0 a1 le mem ca0 ca1 v1 =
  let v1-K = shiftVl (suc (max (RANK u) (RANK a1))) (suc (max (RANK u) (max (RANK a0) (RANK a1)))) G M T u a1
               (b2-l u a1) (b2-r u a1) (b3-l u a0 a1) (b3-r u a0 a1) v1
      v0-K = MonoPack.downVal2 (goodStage (suc (max (RANK u) (max (RANK a0) (RANK a1))))) G M T u a0 a1 le mem ca0 ca1 v1-K
  in shiftVl (suc (max (RANK u) (max (RANK a0) (RANK a1)))) (suc (max (RANK u) (RANK a0))) G M T u a0
       (b3-l u a0 a1) (b3-m u a0 a1) (b2-l u a0) (b2-r u a0) v0-K

downEqVal2-pub : {m : Nat} (G : Ctx m) (M N T : Expr m) (u a0 a1 : FinEl) ->
  LeCode a0 a1 -> FinMem u a0 -> Coherent a0 -> FinMem a1 UCode ->
  EqVal2 G M N T u a1 -> EqVal2 G M N T u a0
downEqVal2-pub G M N T u a0 a1 le mem ca0 ca1 e1 =
  let e1-K = shiftEVl (suc (max (RANK u) (RANK a1))) (suc (max (RANK u) (max (RANK a0) (RANK a1)))) G M N T u a1
               (b2-l u a1) (b2-r u a1) (b3-l u a0 a1) (b3-r u a0 a1) e1
      e0-K = MonoPack.downEqVal2 (goodStage (suc (max (RANK u) (max (RANK a0) (RANK a1))))) G M N T u a0 a1 le mem ca0 ca1 e1-K
  in shiftEVl (suc (max (RANK u) (max (RANK a0) (RANK a1)))) (suc (max (RANK u) (RANK a0))) G M N T u a0
       (b3-l u a0 a1) (b3-m u a0 a1) (b2-l u a0) (b2-r u a0) e0-K

upVal2-pub : {m : Nat} (G : Ctx m) (M T : Expr m) (u a0 a1 : FinEl) ->
  LeCode a0 a1 -> FinMem u a0 -> FinMem u a1 -> Coherent a0 -> Coherent a1 ->
  Val2 G M T u a0 -> ValTy2 G T a1 -> Val2 G M T u a1
upVal2-pub G M T u a0 a1 le m0 m1 c0 c1 v0 vt1 =
  let v0-K  = shiftVl (suc (max (RANK u) (RANK a0))) (suc (max (RANK u) (max (RANK a0) (RANK a1)))) G M T u a0
                (b2-l u a0) (b2-r u a0) (b3-l u a0 a1) (b3-m u a0 a1) v0
      vt1-K = shiftVTy (suc (RANK a1)) (suc (max (RANK u) (max (RANK a0) (RANK a1)))) G T a1
                (Le-refl (suc (RANK a1))) (b3-r u a0 a1) vt1
      v1-K  = MonoPack.upVal2 (goodStage (suc (max (RANK u) (max (RANK a0) (RANK a1))))) G M T u a0 a1 le m0 m1 c0 c1 v0-K vt1-K
  in shiftVl (suc (max (RANK u) (max (RANK a0) (RANK a1)))) (suc (max (RANK u) (RANK a1))) G M T u a1
       (b3-l u a0 a1) (b3-r u a0 a1) (b2-l u a1) (b2-r u a1) v1-K

upEqVal2-pub : {m : Nat} (G : Ctx m) (M N T : Expr m) (u a0 a1 : FinEl) ->
  LeCode a0 a1 -> FinMem u a0 -> FinMem u a1 -> Coherent a0 -> Coherent a1 ->
  EqVal2 G M N T u a0 -> ValTy2 G T a1 -> EqVal2 G M N T u a1
upEqVal2-pub G M N T u a0 a1 le m0 m1 c0 c1 e0 vt1 =
  let e0-K  = shiftEVl (suc (max (RANK u) (RANK a0))) (suc (max (RANK u) (max (RANK a0) (RANK a1)))) G M N T u a0
                (b2-l u a0) (b2-r u a0) (b3-l u a0 a1) (b3-m u a0 a1) e0
      vt1-K = shiftVTy (suc (RANK a1)) (suc (max (RANK u) (max (RANK a0) (RANK a1)))) G T a1
                (Le-refl (suc (RANK a1))) (b3-r u a0 a1) vt1
      e1-K  = MonoPack.upEqVal2 (goodStage (suc (max (RANK u) (max (RANK a0) (RANK a1))))) G M N T u a0 a1 le m0 m1 c0 c1 e0-K vt1-K
  in shiftEVl (suc (max (RANK u) (max (RANK a0) (RANK a1)))) (suc (max (RANK u) (RANK a1))) G M N T u a1
       (b3-l u a0 a1) (b3-r u a0 a1) (b2-l u a1) (b2-r u a1) e1-K

restrictVal2-pub : {m : Nat} (G : Ctx m) (M T : Expr m) (u u' a : FinEl) ->
  LeCode u' u -> FinMem u' a -> FinMem u a ->
  Val2 G M T u a -> Val2 G M T u' a
restrictVal2-pub G M T u u' a le mem fmu v =
  let v-K  = shiftVl (suc (max (RANK u) (RANK a))) (suc (max (RANK u) (max (RANK u') (RANK a)))) G M T u a
               (b2-l u a) (b2-r u a) (b3-l u u' a) (b3-r u u' a) v
      v'-K = MonoPack.restrictVal2 (goodStage (suc (max (RANK u) (max (RANK u') (RANK a))))) G M T u u' a le mem fmu v-K
  in shiftVl (suc (max (RANK u) (max (RANK u') (RANK a)))) (suc (max (RANK u') (RANK a))) G M T u' a
       (b3-m u u' a) (b3-r u u' a) (b2-l u' a) (b2-r u' a) v'-K

restrictEqVal2-pub : {m : Nat} (G : Ctx m) (M N T : Expr m) (u u' a : FinEl) ->
  LeCode u' u -> FinMem u' a -> FinMem u a ->
  EqVal2 G M N T u a -> EqVal2 G M N T u' a
restrictEqVal2-pub G M N T u u' a le mem fmu e =
  let e-K  = shiftEVl (suc (max (RANK u) (RANK a))) (suc (max (RANK u) (max (RANK u') (RANK a)))) G M N T u a
               (b2-l u a) (b2-r u a) (b3-l u u' a) (b3-r u u' a) e
      e'-K = MonoPack.restrictEqVal2 (goodStage (suc (max (RANK u) (max (RANK u') (RANK a))))) G M N T u u' a le mem fmu e-K
  in shiftEVl (suc (max (RANK u) (max (RANK u') (RANK a)))) (suc (max (RANK u') (RANK a))) G M N T u' a
       (b3-m u u' a) (b3-r u u' a) (b2-l u' a) (b2-r u' a) e'-K

------------------------------------------------------------------------
-- Type-conversion transport + equivalence on the public relations.
-- EqValTy2-sym/trans, EqVal2-sym/trans keep the codes fixed, so no shift.
-- The fwd lemmas raise the EqValTy2 hypothesis from suc (RANK b) to the
-- Val/EqVal level suc (max (RANK u) (RANK b)).
------------------------------------------------------------------------

EqValTy2-sym-pub : {m : Nat} {G : Ctx m} {M N : Expr m}
  (a : FinEl) -> Coherent a -> EqValTy2 G M N a -> EqValTy2 G N M a
EqValTy2-sym-pub a ca eq = FwdPack.EqValTy2-sym (goodStageFwd (suc (RANK a))) a ca eq

EqValTy2-trans-pub : {m : Nat} {G : Ctx m} {A B C : Expr m}
  (u : FinEl) -> Coherent u -> EqValTy2 G A B u -> EqValTy2 G B C u -> EqValTy2 G A C u
EqValTy2-trans-pub u cu eqAB eqBC =
  SymTransPack.EqValTy2-trans (goodStageSymTrans (suc (RANK u))) u cu eqAB eqBC

Val2-EqValTy2-fwd-pub : {m : Nat} (G : Ctx m) (M C C' : Expr m) (u b : FinEl) ->
  Coherent b -> EqValTy2 G C C' b -> Val2 G M C u b -> Val2 G M C' u b
Val2-EqValTy2-fwd-pub G M C C' u b cb eqv val =
  FwdPack.Val2-EqValTy2-fwd (goodStageFwd (suc (max (RANK u) (RANK b)))) u b cb
    (shiftEVTy (suc (RANK b)) (suc (max (RANK u) (RANK b))) G C C' b
      (Le-refl (suc (RANK b))) (b2-r u b) eqv)
    val

EqVal2-EqValTy2-fwd-pub : {m : Nat} (G : Ctx m) (M N C C' : Expr m) (u b : FinEl) ->
  Coherent b -> EqValTy2 G C C' b -> EqVal2 G M N C u b -> EqVal2 G M N C' u b
EqVal2-EqValTy2-fwd-pub G M N C C' u b cb eqv ev =
  FwdPack.EqVal2-EqValTy2-fwd (goodStageFwd (suc (max (RANK u) (RANK b)))) u b cb
    (shiftEVTy (suc (RANK b)) (suc (max (RANK u) (RANK b))) G C C' b
      (Le-refl (suc (RANK b))) (b2-r u b) eqv)
    ev

EqVal2-sym-pub : {m : Nat} {G : Ctx m} {M N A : Expr m}
  (u a : FinEl) -> Coherent u -> Coherent a -> EqVal2 G M N A u a -> EqVal2 G N M A u a
EqVal2-sym-pub u a cu ca ev =
  SymTransPack.EqVal2-sym (goodStageSymTrans (suc (max (RANK u) (RANK a)))) u a cu ca ev

EqVal2-trans-pub : {m : Nat} {G : Ctx m} {M1 M2 M3 A : Expr m}
  (u a : FinEl) -> Coherent u -> Coherent a ->
  EqVal2 G M1 M2 A u a -> EqVal2 G M2 M3 A u a -> EqVal2 G M1 M3 A u a
EqVal2-trans-pub u a cu ca ev1 ev2 =
  SymTransPack.EqVal2-trans (goodStageSymTrans (suc (max (RANK u) (RANK a)))) u a cu ca ev1 ev2

------------------------------------------------------------------------
-- Conditional sup-semilattice closure on the public relations.
-- Output code (Sup a1 a2) has rank <= max (RANK a1) (RANK a2) (RANK-Sup),
-- so the result is shifted down from K = suc (max (RANK a1) (RANK a2)) to
-- its canonical level suc (RANK (Sup a1 a2)).
------------------------------------------------------------------------

ValTy2-Sup-pub : {m : Nat} (G : Ctx m) (T : Expr m) (a1 a2 : FinEl) ->
  Comp a1 a2 -> FinMem a1 UCode -> FinMem a2 UCode ->
  ValTy2 G T a1 -> ValTy2 G T a2 -> ValTy2 G T (Sup a1 a2)
ValTy2-Sup-pub G T a1 a2 comp fm1 fm2 vt1 vt2 =
  let vt1-K = shiftVTy (suc (RANK a1)) (suc (max (RANK a1) (RANK a2))) G T a1
                (Le-refl (suc (RANK a1))) (Le-max-l (RANK a1) (RANK a2)) vt1
      vt2-K = shiftVTy (suc (RANK a2)) (suc (max (RANK a1) (RANK a2))) G T a2
                (Le-refl (suc (RANK a2))) (Le-max-r (RANK a1) (RANK a2)) vt2
      sup-K = SupPack.ValTy2-Sup (goodStageSup (suc (max (RANK a1) (RANK a2)))) G T a1 a2 comp fm1 fm2 vt1-K vt2-K
  in shiftVTy (suc (max (RANK a1) (RANK a2))) (suc (RANK (Sup a1 a2))) G T (Sup a1 a2)
       (RANK-Sup a1 a2) (Le-refl (suc (RANK (Sup a1 a2)))) sup-K

EqValTy2-Sup-pub : {m : Nat} (G : Ctx m) (M N : Expr m) (u1 u2 : FinEl) ->
  Comp u1 u2 -> FinMem u1 UCode -> FinMem u2 UCode ->
  EqValTy2 G M N u1 -> EqValTy2 G M N u2 -> EqValTy2 G M N (Sup u1 u2)
EqValTy2-Sup-pub G M N u1 u2 comp fm1 fm2 eq1 eq2 =
  let eq1-K = shiftEVTy (suc (RANK u1)) (suc (max (RANK u1) (RANK u2))) G M N u1
                (Le-refl (suc (RANK u1))) (Le-max-l (RANK u1) (RANK u2)) eq1
      eq2-K = shiftEVTy (suc (RANK u2)) (suc (max (RANK u1) (RANK u2))) G M N u2
                (Le-refl (suc (RANK u2))) (Le-max-r (RANK u1) (RANK u2)) eq2
      sup-K = SupPack.EqValTy2-Sup (goodStageSup (suc (max (RANK u1) (RANK u2)))) G M N u1 u2 comp fm1 fm2 eq1-K eq2-K
  in shiftEVTy (suc (max (RANK u1) (RANK u2))) (suc (RANK (Sup u1 u2))) G M N (Sup u1 u2)
       (RANK-Sup u1 u2) (Le-refl (suc (RANK (Sup u1 u2)))) sup-K

------------------------------------------------------------------------
-- Reflexivity on the public relations (codes fixed, so no shift).
------------------------------------------------------------------------

Val2-Bot-pub : {m : Nat} {G : Ctx m} {M A : Expr m}
  (a : FinEl) -> Val2 G M A Bot a
Val2-Bot-pub a = ReflPack.Val2-Bot (goodStageRefl (suc (max (RANK Bot) (RANK a)))) a

EqVal2-Bot-pub : {m : Nat} {G : Ctx m} {M N A : Expr m}
  (a : FinEl) -> EqVal2 G M N A Bot a
EqVal2-Bot-pub a = ReflPack.EqVal2-Bot (goodStageRefl (suc (max (RANK Bot) (RANK a)))) a

Val2-to-EqVal2-pub : {m : Nat} {G : Ctx m} {M A : Expr m}
  (u a : FinEl) -> Val2 G M A u a -> EqVal2 G M M A u a
Val2-to-EqVal2-pub u a v =
  ReflPack.Val2-to-EqVal2 (goodStageRefl (suc (max (RANK u) (RANK a)))) u a v

ValTy2-to-EqValTy2-pub : {m : Nat} {G : Ctx m} {M : Expr m}
  (a : FinEl) -> ValTy2 G M a -> EqValTy2 G M M a
ValTy2-to-EqValTy2-pub a vt =
  ReflPack.ValTy2-to-EqValTy2 (goodStageRefl (suc (RANK a))) a vt

------------------------------------------------------------------------
-- Head-expansion / type-transport on the public relations.
-- type-transport: raise the EqValTy2 hyp to the Val/EqVal level (no
-- Coherent needed).  beta-expand: codes fixed, so no shift.
------------------------------------------------------------------------

Val2-type-transport-pub : {m : Nat} (G : Ctx m) (C C' N : Expr m) (u a : FinEl) ->
  EqValTy2 G C C' a -> Val2 G N C u a -> Val2 G N C' u a
Val2-type-transport-pub G C C' N u a eqvt val =
  TransportPack.Val2-type-transport (goodStageTransport (suc (max (RANK u) (RANK a)))) u a
    (shiftEVTy (suc (RANK a)) (suc (max (RANK u) (RANK a))) G C C' a
      (Le-refl (suc (RANK a))) (b2-r u a) eqvt)
    val

EqVal2-type-transport-pub : {m : Nat} (G : Ctx m) (C C' M N : Expr m) (u a : FinEl) ->
  EqValTy2 G C C' a -> EqVal2 G M N C u a -> EqVal2 G M N C' u a
EqVal2-type-transport-pub G C C' M N u a eqvt ev =
  TransportPack.EqVal2-type-transport (goodStageTransport (suc (max (RANK u) (RANK a)))) u a
    (shiftEVTy (suc (RANK a)) (suc (max (RANK u) (RANK a))) G C C' a
      (Le-refl (suc (RANK a))) (b2-r u a) eqvt)
    ev

Val2-beta-expand-pub : {m : Nat} {G : Ctx m} {M M' T : Expr m}
  (u a : FinEl) -> HeadRed M M' -> ConvTm G M M' T ->
  Val2 G M' T u a -> EqVal2 G M' M T u a
Val2-beta-expand-pub u a hr ct val =
  BetaPack.Val2-beta-expand (goodStageBeta (suc (max (RANK u) (RANK a)))) u a hr ct val
