{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- CAST.AdequacyCastDriver.agda
--
-- Public canonical-level wrappers for the cast-coercion validity lemma
-- (CAST.AdequacyCast.goodStageCast).  The stage-level castVal / castEqVal
-- live at a FIXED stage k; the public Val2 / EqVal2 strip to the canonical
-- level suc (max (RANK u) (RANK a)) of THEIR codes, which differ from the
-- inner term's codes (v, c).  So we shift every argument up to a common
-- stage K (above all the codes), run goodStageCast at K, and shift the
-- result back down -- exactly the downValTy2-pub pattern in ValidityLevels.
--
-- 0 postulates.
------------------------------------------------------------------------

module CAST.AdequacyCastDriver where

open import CAST.Basic using (Nat ; suc ; max ; Le ; Le-refl ; Le-trans ; Le-max-l ; Le-max-r ; FinEl)
open import CAST.Rank using (RANK)
open import CAST.RawSyntax using (Expr ; U ; Id ; cast)
open import CAST.TypingRules using (Ctx ; HasType ; ConvTm)
open import CAST.PaperSemantics using (LeCode ; FinMem ; Coherent)
open import CAST.ValidityStratified using (Val2 ; EqVal2 ; ValTy2 ; EqValTy2)
open import CAST.ValidityLevels using (shiftVl ; shiftEVl ; shiftVTy ; shiftEVTy)
open import CAST.AdequacyCast using (CastPack ; goodStageCast)
open import CAST.AdequacyCastRefl using (CastReflPack ; goodStageCastRefl)

------------------------------------------------------------------------
-- castVal-pub : public Val2 of a cast from public ValTy2 / Val2 of the parts.
------------------------------------------------------------------------

castVal-pub : {m : Nat} {G : Ctx m} (T1 T2 q P : Expr m) (u v c a : FinEl) ->
  LeCode u v -> FinMem u a -> FinMem v c -> Coherent v ->
  HasType G T1 U -> HasType G T2 U -> HasType G q (Id T1 T2) -> HasType G P T1 ->
  ValTy2 G T1 c -> ValTy2 G T2 a -> Val2 G P T1 v c ->
  Val2 G (cast T1 T2 q P) T2 u a
castVal-pub {m} {G} T1 T2 q P u v c a le fmua fmvc cohv dT1 dT2 dq dP vtT1 vtT2 vlP =
  shiftVl K (suc (max (RANK u) (RANK a))) G (cast T1 T2 q P) T2 u a
    bu ba (Le-max-l (RANK u) (RANK a)) (Le-max-r (RANK u) (RANK a)) res-K
  where
    X = max (RANK u) (RANK v)
    Y = max (RANK c) (RANK a)
    K = suc (max X Y)
    bu = Le-trans (RANK u) X (max X Y) (Le-max-l (RANK u) (RANK v)) (Le-max-l X Y)
    bv = Le-trans (RANK v) X (max X Y) (Le-max-r (RANK u) (RANK v)) (Le-max-l X Y)
    bc = Le-trans (RANK c) Y (max X Y) (Le-max-l (RANK c) (RANK a)) (Le-max-r X Y)
    ba = Le-trans (RANK a) Y (max X Y) (Le-max-r (RANK c) (RANK a)) (Le-max-r X Y)
    vlP-K  = shiftVl (suc (max (RANK v) (RANK c))) K G P T1 v c
               (Le-max-l (RANK v) (RANK c)) (Le-max-r (RANK v) (RANK c)) bv bc vlP
    vtT1-K = shiftVTy (suc (RANK c)) K G T1 c (Le-refl (suc (RANK c))) bc vtT1
    vtT2-K = shiftVTy (suc (RANK a)) K G T2 a (Le-refl (suc (RANK a))) ba vtT2
    res-K  = CastPack.castVal (goodStageCast K) T1 T2 q P u v c a le fmua fmvc cohv
               dT1 dT2 dq dP vtT1-K vtT2-K vlP-K

------------------------------------------------------------------------
-- castEqVal-pub : public EqVal2 of two casts from public EqValTy2 / EqVal2.
------------------------------------------------------------------------

castEqVal-pub : {m : Nat} {G : Ctx m}
  (T1 T2 q P T1' T2' q' P' : Expr m) (u v c a : FinEl) ->
  LeCode u v -> FinMem u a -> FinMem v c -> Coherent v ->
  HasType G T1 U -> HasType G T2 U -> HasType G q (Id T1 T2) -> HasType G P T1 ->
  HasType G T1' U -> HasType G T2' U -> HasType G q' (Id T1' T2') -> HasType G P' T1' ->
  EqValTy2 G T1 T1' c -> EqValTy2 G T2 T2' a ->
  EqVal2 G P P' T1 v c ->
  EqVal2 G (cast T1 T2 q P) (cast T1' T2' q' P') T2 u a
castEqVal-pub {m} {G} T1 T2 q P T1' T2' q' P' u v c a le fmua fmvc cohv
  dT1 dT2 dq dP dT1' dT2' dq' dP' eqT1 eqT2 eqP =
  shiftEVl K (suc (max (RANK u) (RANK a))) G (cast T1 T2 q P) (cast T1' T2' q' P') T2 u a
    bu ba (Le-max-l (RANK u) (RANK a)) (Le-max-r (RANK u) (RANK a)) res-K
  where
    X = max (RANK u) (RANK v)
    Y = max (RANK c) (RANK a)
    K = suc (max X Y)
    bu = Le-trans (RANK u) X (max X Y) (Le-max-l (RANK u) (RANK v)) (Le-max-l X Y)
    bv = Le-trans (RANK v) X (max X Y) (Le-max-r (RANK u) (RANK v)) (Le-max-l X Y)
    bc = Le-trans (RANK c) Y (max X Y) (Le-max-l (RANK c) (RANK a)) (Le-max-r X Y)
    ba = Le-trans (RANK a) Y (max X Y) (Le-max-r (RANK c) (RANK a)) (Le-max-r X Y)
    eqP-K  = shiftEVl (suc (max (RANK v) (RANK c))) K G P P' T1 v c
               (Le-max-l (RANK v) (RANK c)) (Le-max-r (RANK v) (RANK c)) bv bc eqP
    eqT1-K = shiftEVTy (suc (RANK c)) K G T1 T1' c (Le-refl (suc (RANK c))) bc eqT1
    eqT2-K = shiftEVTy (suc (RANK a)) K G T2 T2' a (Le-refl (suc (RANK a))) ba eqT2
    res-K  = CastPack.castEqVal (goodStageCast K) T1 T2 q P T1' T2' q' P' u v c a le fmua fmvc cohv
               dT1 dT2 dq dP dT1' dT2' dq' dP' eqT1-K eqT2-K eqP-K

------------------------------------------------------------------------
-- castRefl-pub : public EqVal2 witnessing  cast A B q M ~ M : B  when
-- A and B are validity-equal types (EqValTy2 A B).  Mirror of castEqVal-pub.
------------------------------------------------------------------------

castRefl-pub : {m : Nat} {G : Ctx m} (A B q M : Expr m) (u v c a : FinEl) ->
  LeCode u v -> LeCode c a -> FinMem u a -> FinMem v c -> Coherent v ->
  HasType G A U -> HasType G B U -> HasType G q (Id A B) -> HasType G M A ->
  EqValTy2 G A B c -> ValTy2 G B a -> Val2 G M A v c ->
  EqVal2 G (cast A B q M) M B u a
castRefl-pub {m} {G} A B q M u v c a le lec fmua fmvc cohv
  dA dB dq dM eqAB vtB vlM =
  shiftEVl K (suc (max (RANK u) (RANK a))) G (cast A B q M) M B u a
    bu ba (Le-max-l (RANK u) (RANK a)) (Le-max-r (RANK u) (RANK a)) res-K
  where
    X = max (RANK u) (RANK v)
    Y = max (RANK c) (RANK a)
    K = suc (max X Y)
    bu = Le-trans (RANK u) X (max X Y) (Le-max-l (RANK u) (RANK v)) (Le-max-l X Y)
    bv = Le-trans (RANK v) X (max X Y) (Le-max-r (RANK u) (RANK v)) (Le-max-l X Y)
    bc = Le-trans (RANK c) Y (max X Y) (Le-max-l (RANK c) (RANK a)) (Le-max-r X Y)
    ba = Le-trans (RANK a) Y (max X Y) (Le-max-r (RANK c) (RANK a)) (Le-max-r X Y)
    vlM-K  = shiftVl (suc (max (RANK v) (RANK c))) K G M A v c
               (Le-max-l (RANK v) (RANK c)) (Le-max-r (RANK v) (RANK c)) bv bc vlM
    eqAB-K = shiftEVTy (suc (RANK c)) K G A B c (Le-refl (suc (RANK c))) bc eqAB
    vtB-K  = shiftVTy (suc (RANK a)) K G B a (Le-refl (suc (RANK a))) ba vtB
    res-K  = CastReflPack.castId (goodStageCastRefl K) A B q M u v c a le lec fmua fmvc cohv
               dA dB dq dM eqAB-K vtB-K vlM-K
