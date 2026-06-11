{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- FinMemStage.agda  (MIN/ — Pi + U fragment)
--
-- Stage-stratified MEMBERSHIP predicate FinMem (= the typing ":" of the
-- iterative domain), built by structural recursion on a stage index `n`
-- (the same GoodStage / LeqStage `Bundle` template, one level up from the
-- order).  This is the replacement for PaperTyping's literal
-- `FinMem`/`FinMemFun`/`FinMemAllU` mutual block, whose only obstruction
-- to Agda's foetus checker is the swap (`FinMem Bot a = FinMem a UCode`)
-- and the promote (`FinMem (FunEl g)(PiCode a f) -> FinMem (PiCode a f) UCode`)
-- -- both move a finite element of unrelated structure into the
-- termination argument, which only full size-change (not foetus) handles.
--
-- DESIGN (mirrors LeqStage.buildOrderStage):
--   * EXPAND the swap into its 4 type-cases and INLINE the promote, so
--     every FinEl-membership recursion descends into a STRICTLY
--     SMALLER-RANK component (the domain `a` / codomain function `f` of a
--     `PiCode a f`, RANK < its suc; or a key/value of a `cons`).  Each
--     such recursion DROPS one stage -> goes to the predecessor bundle
--     `B.finMem` (= `fmP`).  This pays for the drop with the constructor's
--     `suc`, so the bound is the clean `Le (max (RANK u)(RANK a)) n`
--     (no off-by-one), exactly as in the order.
--   * `finMem'` is therefore NON-recursive at the current stage (all its
--     FinEl recursions go to `fmP`); only `finMemFun'`/`finMemAllU'`
--     recurse, structurally on their FinFun list.  So `buildMemStage` is
--     foetus-trivial.
--   * EvalFun is the FINISHED structural function from the order
--     (CAST.PaperOrder / LeqStageBridge); it is NOT stage-indexed here.
--
-- The public membership is the stage-collapsed `finMemC`/`finMemFunC`/
-- `finMemAllUC` at the canonical level (cf. LeqC); its expected unfolding,
-- projection and closure properties are proved (via stability) in the
-- downstream FinMemStage* files and re-exported by PaperTyping.
--
-- NO postulates.
------------------------------------------------------------------------

module CAST.FinMemStage where

open import CAST.Basic
  using ( Top ; tt ; Empty
        ; Nat ; zero ; suc ; max
        ; Le ; Le-refl ; Le-suc ; Le-trans ; Le-max-l ; Le-max-r
        ; Pair ; mkSigma ; fst ; snd ; Sigma
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; IdCode ; FinFun ; nil ; cons )
open import CAST.PaperOrder
  using ( RANK ; RANKFun ; Sup ; append ; EvalFun
        ; Coherent ; CoherentFun ; CoherentFunTail ; CFTcons ; cft-from-cf
        ; Comp ; Le-max-lub )

------------------------------------------------------------------------
-- One stage of the membership predicate.
------------------------------------------------------------------------

record MemBundle : Set1 where
  field
    finMem     : FinEl  -> FinEl -> Set
    finMemFun  : FinFun -> FinEl -> FinFun -> Set
    finMemAllU : FinFun -> FinEl -> Set

-- Minimal base (Stage 0): correct on atoms (RANK 0), Empty/Top on
-- compounds (which have RANK >= 1 and never land on Stage 0 in-bounds).
trivMem : MemBundle
trivMem = record { finMem = fm0 ; finMemFun = ff0 ; finMemAllU = fa0 }
  where
    fm0 : FinEl -> FinEl -> Set
    fm0 Bot          Bot          = Top
    fm0 Bot          UCode        = Top
    fm0 Bot          (FunEl _)    = Empty
    fm0 Bot          (PiCode _ _) = Empty
    fm0 Bot          (IdCode _ _) = Empty
    fm0 UCode        Bot          = Empty
    fm0 UCode        UCode        = Top
    fm0 UCode        (FunEl _)    = Empty
    fm0 UCode        (PiCode _ _) = Empty
    fm0 UCode        (IdCode _ _) = Empty
    fm0 (FunEl _)    Bot          = Empty
    fm0 (FunEl _)    UCode        = Empty
    fm0 (FunEl _)    (FunEl _)    = Empty
    fm0 (FunEl _)    (PiCode _ _) = Empty
    fm0 (FunEl _)    (IdCode _ _) = Empty
    fm0 (PiCode _ _) Bot          = Empty
    fm0 (PiCode _ _) UCode        = Empty
    fm0 (PiCode _ _) (FunEl _)    = Empty
    fm0 (PiCode _ _) (PiCode _ _) = Empty
    fm0 (PiCode _ _) (IdCode _ _) = Empty
    fm0 (IdCode _ _) Bot          = Empty
    fm0 (IdCode _ _) UCode        = Empty
    fm0 (IdCode _ _) (FunEl _)    = Empty
    fm0 (IdCode _ _) (PiCode _ _) = Empty
    fm0 (IdCode _ _) (IdCode _ _) = Empty

    ff0 : FinFun -> FinEl -> FinFun -> Set
    ff0 nil        _ _ = Top
    ff0 (cons _ _) _ _ = Empty

    fa0 : FinFun -> FinEl -> Set
    fa0 nil        _ = Top
    fa0 (cons _ _) _ = Empty

------------------------------------------------------------------------
-- buildMemStage : level-(suc n) membership from the level-n bundle B.
------------------------------------------------------------------------

buildMemStage : MemBundle -> MemBundle
buildMemStage B = record { finMem = fm' ; finMemFun = ff' ; finMemAllU = fa' }
  where
    open MemBundle B renaming (finMem to fmP)

    -- finMemFun' / finMemAllU': structural on the FinFun list; each
    -- FinEl-membership drops to the predecessor fmP (the EvalFun-result /
    -- key / value all have RANK < the list's RANK).  They never call fm'.
    fa' : FinFun -> FinEl -> Set
    fa' nil         a = Top
    fa' (cons p ps) a =
      Pair (Pair (fmP (fst p) a) (fmP (snd p) UCode)) (fa' ps a)

    ff' : FinFun -> FinEl -> FinFun -> Set
    ff' nil         a f = Top
    ff' (cons p ps) a f =
      Pair (Pair (fmP (fst p) a) (fmP (snd p) (EvalFun f (fst p)))) (ff' ps a f)

    -- finMem': NON-recursive at the current stage.  Swap is expanded into
    -- the four (Bot, type) cases; the promote is inlined.  Every FinEl
    -- membership goes to fmP (predecessor) on a strictly-smaller-RANK arg;
    -- only the FinFun-facts use the current ff'/fa'.
    fm' : FinEl -> FinEl -> Set
    -- Bot element (expanded swap = "the type a is well-formed")
    fm' Bot          Bot          = Top
    fm' Bot          UCode        = Top
    fm' Bot          (FunEl g)    = Empty
    fm' Bot          (PiCode a f) =
      Pair (fmP a UCode) (Pair (fa' f a) (CoherentFunTail f))
    -- Bot element of an Id-type: "Id a b is well-formed" (a, b : U)
    fm' Bot          (IdCode a b) = Pair (fmP a UCode) (fmP b UCode)
    -- UCode element
    fm' UCode        UCode        = Top
    fm' UCode        Bot          = Empty
    fm' UCode        (FunEl g)    = Empty
    fm' UCode        (PiCode a f) = Empty
    fm' UCode        (IdCode a b) = Empty
    -- FunEl element (inlined promote: the Pi-type-wf triple in line 3)
    fm' (FunEl g)    (PiCode a f) =
      Pair (ff' g a f)
           (Pair (CoherentFun g)
                 (Pair (fmP a UCode) (Pair (fa' f a) (CoherentFunTail f))))
    fm' (FunEl g)    Bot          = Empty
    fm' (FunEl g)    UCode        = Empty
    fm' (FunEl g)    (FunEl h)    = Empty
    fm' (FunEl g)    (IdCode a b) = Empty
    -- PiCode element
    fm' (PiCode a f) UCode        =
      Pair (fmP a UCode) (Pair (fa' f a) (CoherentFunTail f))
    fm' (PiCode a f) Bot          = Empty
    fm' (PiCode a f) (FunEl g)    = Empty
    fm' (PiCode a f) (PiCode b g) = Empty
    fm' (PiCode a f) (IdCode b d) = Empty
    -- IdCode element: a member of UCode (Id a b : U) iff a, b : U;
    -- proof-irrelevant, so IdCode is never a member of any other type.
    fm' (IdCode a b) UCode        = Pair (fmP a UCode) (fmP b UCode)
    fm' (IdCode a b) Bot          = Empty
    fm' (IdCode a b) (FunEl g)    = Empty
    fm' (IdCode a b) (PiCode c g) = Empty
    fm' (IdCode a b) (IdCode c d) = Empty

------------------------------------------------------------------------
-- The stratified family, by structural recursion on the stage index.
------------------------------------------------------------------------

Stage : Nat -> MemBundle
Stage zero    = trivMem
Stage (suc n) = buildMemStage (Stage n)

-- MB n : the bundle operations at stage n.
module MB (n : Nat) = MemBundle (Stage n)

------------------------------------------------------------------------
-- Public membership at the canonical level  suc (max (RANK u)(RANK a)).
------------------------------------------------------------------------

finMemC : FinEl -> FinEl -> Set
finMemC u a = MemBundle.finMem (Stage (suc (max (RANK u) (RANK a)))) u a

finMemAllUC : FinFun -> FinEl -> Set
finMemAllUC f a = MemBundle.finMemAllU (Stage (suc (max (RANKFun f) (RANK a)))) f a

finMemFunC : FinFun -> FinEl -> FinFun -> Set
finMemFunC g a f =
  MemBundle.finMemFun
    (Stage (suc (max (RANKFun g) (max (RANK a) (RANKFun f))))) g a f
