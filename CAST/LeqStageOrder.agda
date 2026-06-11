{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- LeqStageOrder.agda  (MIN/ — Pi + U fragment)
--
-- COLLAPSE of the stage-indexed order pack (LeqStageProps2) to the
-- public, level-free order LeqC.  Each public lemma shifts all of its
-- LeqC inputs down to a common stage K (the max of the relevant RANKs)
-- via leqC-to, applies the stage-indexed `*-n` lemma at K (whose
-- `Le (RANK ·) K` side-conditions all hold at the max), and shifts the
-- result back up to LeqC via leqC-from.  Mirrors ValidityLevels'
-- downValTy2-pub collapse, one level down.
--
-- These are the pure-order facts (no EvalFun): refl, trans, Sup-left,
-- Sup-right, Sup-lub, Comp-down, LeCode-Comp.  The EvalFun-facts
-- (Coherent-EvalFun, Comp-value-EvalFun, EvalFun-mon, EvalFun-mon-arg)
-- are derived in PaperOrder, where the structural EvalFun and its bridge
-- to OB.ev are in scope.
--
-- NO postulates.
------------------------------------------------------------------------

module CAST.LeqStageOrder where

open import CAST.Basic
  using ( Top ; tt ; Empty
        ; Nat ; zero ; suc ; max
        ; Le ; Le-refl ; Le-trans ; Le-max-l ; Le-max-r
        ; Pair ; mkSigma ; fst ; snd
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; nil ; cons )
open import CAST.LeqStage
open import CAST.LeqStageProps   using ( leq-Sup-lub )
open import CAST.LeqStageProps2
open import CAST.LeqStageStable

private
  -- common-stage bounds
  b3-x : (x y z : Nat) -> Le x (max x (max y z))
  b3-x x y z = Le-max-l x (max y z)

  b3-y : (x y z : Nat) -> Le y (max x (max y z))
  b3-y x y z =
    Le-trans y (max y z) (max x (max y z)) (Le-max-l y z) (Le-max-r x (max y z))

  b3-z : (x y z : Nat) -> Le z (max x (max y z))
  b3-z x y z =
    Le-trans z (max y z) (max x (max y z)) (Le-max-r y z) (Le-max-r x (max y z))

------------------------------------------------------------------------
-- reflexivity
------------------------------------------------------------------------

LeqC-refl : (a : FinEl) -> Coherent a -> LeqC a a
LeqC-refl a ca =
  leqC-from (RANK a) a a
    (Le-max-lub (RANK a) (RANK a) (RANK a) (Le-refl (RANK a)) (Le-refl (RANK a)))
    (LeCode-refl-n (RANK a) a (Le-refl (RANK a)) ca)

------------------------------------------------------------------------
-- transitivity
------------------------------------------------------------------------

LeqC-trans : (x y z : FinEl) ->
  Coherent x -> Coherent y -> Coherent z ->
  LeqC x y -> LeqC y z -> LeqC x z
LeqC-trans x y z cx cy cz xy yz =
  let bx = b3-x (RANK x) (RANK y) (RANK z)
      by = b3-y (RANK x) (RANK y) (RANK z)
      bz = b3-z (RANK x) (RANK y) (RANK z)
      K  = max (RANK x) (max (RANK y) (RANK z))
      xyK = leqC-to K x y (Le-max-lub (RANK x) (RANK y) K bx by) xy
      yzK = leqC-to K y z (Le-max-lub (RANK y) (RANK z) K by bz) yz
      xzK = LeCode-trans-n K x y z bx by bz cx cy cz xyK yzK
  in leqC-from K x z (Le-max-lub (RANK x) (RANK z) K bx bz) xzK

------------------------------------------------------------------------
-- Sup-left / Sup-right
------------------------------------------------------------------------

LeqC-Sup-left : (a b : FinEl) -> Comp a b -> Coherent a -> Coherent b ->
  LeqC a (Sup a b)
LeqC-Sup-left a b comp ca cb =
  let K   = max (RANK a) (RANK b)
      ba  = Le-max-l (RANK a) (RANK b)
      bb  = Le-max-r (RANK a) (RANK b)
      bsup : Le (RANK (Sup a b)) K
      bsup = Le-trans (RANK (Sup a b)) (max (RANK a) (RANK b)) K (RANK-Sup a b) (Le-refl K)
      r   = LeCode-Sup-left-n K a b ba bb comp ca cb
  in leqC-from K a (Sup a b) (Le-max-lub (RANK a) (RANK (Sup a b)) K ba bsup) r

LeqC-Sup-right : (a b : FinEl) -> Comp a b -> Coherent a -> Coherent b ->
  LeqC b (Sup a b)
LeqC-Sup-right a b comp ca cb =
  let K   = max (RANK a) (RANK b)
      ba  = Le-max-l (RANK a) (RANK b)
      bb  = Le-max-r (RANK a) (RANK b)
      bsup : Le (RANK (Sup a b)) K
      bsup = Le-trans (RANK (Sup a b)) (max (RANK a) (RANK b)) K (RANK-Sup a b) (Le-refl K)
      r   = LeCode-Sup-right-n K a b ba bb comp ca cb
  in leqC-from K b (Sup a b) (Le-max-lub (RANK b) (RANK (Sup a b)) K bb bsup) r

------------------------------------------------------------------------
-- Sup-lub  (stage-uniform; leq-Sup-lub needs no Coherent)
------------------------------------------------------------------------

LeqC-Sup-lub : (a b c : FinEl) -> LeqC a c -> LeqC b c -> LeqC (Sup a b) c
LeqC-Sup-lub a b c ac bc =
  let ba = b3-x (RANK a) (RANK b) (RANK c)
      bb = b3-y (RANK a) (RANK b) (RANK c)
      bc' = b3-z (RANK a) (RANK b) (RANK c)
      K  = max (RANK a) (max (RANK b) (RANK c))
      bsup : Le (RANK (Sup a b)) K
      bsup = Le-trans (RANK (Sup a b)) (max (RANK a) (RANK b)) K (RANK-Sup a b)
               (Le-max-lub (RANK a) (RANK b) K ba bb)
      acK = leqC-to K a c (Le-max-lub (RANK a) (RANK c) K ba bc') ac
      bcK = leqC-to K b c (Le-max-lub (RANK b) (RANK c) K bb bc') bc
      r   = leq-Sup-lub K a b c acK bcK
  in leqC-from K (Sup a b) c (Le-max-lub (RANK (Sup a b)) (RANK c) K bsup bc') r

------------------------------------------------------------------------
-- Comp-down  (result is Comp, stage-free; only the LeqC input is shifted)
------------------------------------------------------------------------

LeqC-Comp-down : (u u' v : FinEl) -> LeqC u u' -> Comp u' v -> Comp u v
LeqC-Comp-down u u' v le c =
  let K   = max (RANK u) (RANK u')
      bu  = Le-max-l (RANK u) (RANK u')
      bu' = Le-max-r (RANK u) (RANK u')
      leK = leqC-to K u u' (Le-max-lub (RANK u) (RANK u') K bu bu') le
  in Comp-down-n K u u' v bu bu' leK c

------------------------------------------------------------------------
-- LeCode-Comp
------------------------------------------------------------------------

LeqC-Comp : (u v w : FinEl) -> Coherent w -> LeqC u w -> LeqC v w -> Comp u v
LeqC-Comp u v w coh lu lv =
  let bu = b3-x (RANK u) (RANK v) (RANK w)
      bv = b3-y (RANK u) (RANK v) (RANK w)
      bw = b3-z (RANK u) (RANK v) (RANK w)
      K  = max (RANK u) (max (RANK v) (RANK w))
      luK = leqC-to K u w (Le-max-lub (RANK u) (RANK w) K bu bw) lu
      lvK = leqC-to K v w (Le-max-lub (RANK v) (RANK w) K bv bw) lv
  in LeCode-Comp-n K u v w bu bv bw coh luK lvK
