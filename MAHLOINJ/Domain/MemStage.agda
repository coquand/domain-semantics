{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- FinMemStage.agda  (NAT/ — Pi + U fragment)
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
--     (MAHLOINJ.Domain.Order / LeqStageBridge); it is NOT stage-indexed here.
--
-- The public membership is the stage-collapsed `finMemC`/`finMemFunC`/
-- `finMemAllUC` at the canonical level (cf. LeqC); its expected unfolding,
-- projection and closure properties are proved (via stability) in the
-- downstream FinMemStage* files and re-exported by PaperTyping.
--
-- NO postulates.
------------------------------------------------------------------------

module MAHLOINJ.Domain.MemStage where

open import MAHLOINJ.Domain.Basic
  using ( Top ; tt ; Empty
        ; Nat ; zero ; suc ; max
        ; Le ; Le-refl ; Le-suc ; Le-trans ; Le-max-l ; Le-max-r
        ; Pair ; mkSigma ; fst ; snd ; Sigma
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; PairEl ; SigmaCode ; FinFun ; nil ; cons )
open import MAHLOINJ.Domain.Order
  using ( RANK ; RANKFun ; Sup ; append ; EvalFun
        ; Coherent ; CoherentFun ; CoherentFunTail ; CFTcons ; cft-from-cf
        ; Comp ; Le-max-lub ; PairNB )

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
    fm0 Bot             Bot             = Top
    fm0 Bot             UCode           = Top
    fm0 Bot             (FunEl _)       = Empty
    fm0 Bot             (PiCode _ _)    = Empty
    fm0 Bot             NatCode         = Top
    fm0 Bot             ZeroEl          = Empty
    fm0 Bot             (SucEl _)       = Empty
    fm0 Bot             (PairEl _ _)    = Empty
    fm0 Bot             (SigmaCode _ _) = Empty
    fm0 UCode           Bot             = Empty
    fm0 UCode           UCode           = Top
    fm0 UCode           (FunEl _)       = Empty
    fm0 UCode           (PiCode _ _)    = Empty
    fm0 UCode           NatCode         = Empty
    fm0 UCode           ZeroEl          = Empty
    fm0 UCode           (SucEl _)       = Empty
    fm0 UCode           (PairEl _ _)    = Empty
    fm0 UCode           (SigmaCode _ _) = Empty
    fm0 (FunEl _)       Bot             = Empty
    fm0 (FunEl _)       UCode           = Empty
    fm0 (FunEl _)       (FunEl _)       = Empty
    fm0 (FunEl _)       (PiCode _ _)    = Empty
    fm0 (FunEl _)       NatCode         = Empty
    fm0 (FunEl _)       ZeroEl          = Empty
    fm0 (FunEl _)       (SucEl _)       = Empty
    fm0 (FunEl _)       (PairEl _ _)    = Empty
    fm0 (FunEl _)       (SigmaCode _ _) = Empty
    fm0 (PiCode _ _)    Bot             = Empty
    fm0 (PiCode _ _)    UCode           = Empty
    fm0 (PiCode _ _)    (FunEl _)       = Empty
    fm0 (PiCode _ _)    (PiCode _ _)    = Empty
    fm0 (PiCode _ _)    NatCode         = Empty
    fm0 (PiCode _ _)    ZeroEl          = Empty
    fm0 (PiCode _ _)    (SucEl _)       = Empty
    fm0 (PiCode _ _)    (PairEl _ _)    = Empty
    fm0 (PiCode _ _)    (SigmaCode _ _) = Empty
    fm0 NatCode         Bot             = Empty
    fm0 NatCode         UCode           = Top
    fm0 NatCode         (FunEl _)       = Empty
    fm0 NatCode         (PiCode _ _)    = Empty
    fm0 NatCode         NatCode         = Empty
    fm0 NatCode         ZeroEl          = Empty
    fm0 NatCode         (SucEl _)       = Empty
    fm0 NatCode         (PairEl _ _)    = Empty
    fm0 NatCode         (SigmaCode _ _) = Empty
    fm0 ZeroEl          Bot             = Empty
    fm0 ZeroEl          UCode           = Empty
    fm0 ZeroEl          (FunEl _)       = Empty
    fm0 ZeroEl          (PiCode _ _)    = Empty
    fm0 ZeroEl          NatCode         = Top
    fm0 ZeroEl          ZeroEl          = Empty
    fm0 ZeroEl          (SucEl _)       = Empty
    fm0 ZeroEl          (PairEl _ _)    = Empty
    fm0 ZeroEl          (SigmaCode _ _) = Empty
    fm0 (SucEl _)       Bot             = Empty
    fm0 (SucEl _)       UCode           = Empty
    fm0 (SucEl _)       (FunEl _)       = Empty
    fm0 (SucEl _)       (PiCode _ _)    = Empty
    fm0 (SucEl _)       NatCode         = Empty
    fm0 (SucEl _)       ZeroEl          = Empty
    fm0 (SucEl _)       (SucEl _)       = Empty
    fm0 (SucEl _)       (PairEl _ _)    = Empty
    fm0 (SucEl _)       (SigmaCode _ _) = Empty
    fm0 (PairEl _ _)    Bot             = Empty
    fm0 (PairEl _ _)    UCode           = Empty
    fm0 (PairEl _ _)    (FunEl _)       = Empty
    fm0 (PairEl _ _)    (PiCode _ _)    = Empty
    fm0 (PairEl _ _)    NatCode         = Empty
    fm0 (PairEl _ _)    ZeroEl          = Empty
    fm0 (PairEl _ _)    (SucEl _)       = Empty
    fm0 (PairEl _ _)    (PairEl _ _)    = Empty
    fm0 (PairEl _ _)    (SigmaCode _ _) = Empty
    fm0 (SigmaCode _ _) Bot             = Empty
    fm0 (SigmaCode _ _) UCode           = Empty
    fm0 (SigmaCode _ _) (FunEl _)       = Empty
    fm0 (SigmaCode _ _) (PiCode _ _)    = Empty
    fm0 (SigmaCode _ _) NatCode         = Empty
    fm0 (SigmaCode _ _) ZeroEl          = Empty
    fm0 (SigmaCode _ _) (SucEl _)       = Empty
    fm0 (SigmaCode _ _) (PairEl _ _)    = Empty
    fm0 (SigmaCode _ _) (SigmaCode _ _) = Empty

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
    fm' Bot             Bot             = Top
    fm' Bot             UCode           = Top
    fm' Bot             (FunEl _)       = Empty
    fm' Bot             (PiCode b g)    = Pair (fmP b UCode) (Pair (fa' g b) (CoherentFunTail g))
    fm' Bot             NatCode         = Top
    fm' Bot             ZeroEl          = Empty
    fm' Bot             (SucEl _)       = Empty
    fm' Bot             (PairEl _ _)    = Empty
    fm' Bot             (SigmaCode b g) = Pair (fmP b UCode) (Pair (fa' g b) (CoherentFunTail g))
    fm' UCode           Bot             = Empty
    fm' UCode           UCode           = Top
    fm' UCode           (FunEl _)       = Empty
    fm' UCode           (PiCode _ _)    = Empty
    fm' UCode           NatCode         = Empty
    fm' UCode           ZeroEl          = Empty
    fm' UCode           (SucEl _)       = Empty
    fm' UCode           (PairEl _ _)    = Empty
    fm' UCode           (SigmaCode _ _) = Empty
    fm' (FunEl _)       Bot             = Empty
    fm' (FunEl _)       UCode           = Empty
    fm' (FunEl _)       (FunEl _)       = Empty
    fm' (FunEl g)       (PiCode b g')    = Pair (ff' g b g')
           (Pair (CoherentFun g)
                 (Pair (fmP b UCode) (Pair (fa' g' b) (CoherentFunTail g'))))
    fm' (FunEl _)       NatCode         = Empty
    fm' (FunEl _)       ZeroEl          = Empty
    fm' (FunEl _)       (SucEl _)       = Empty
    fm' (FunEl _)       (PairEl _ _)    = Empty
    fm' (FunEl _)       (SigmaCode _ _) = Empty
    fm' (PiCode _ _)    Bot             = Empty
    fm' (PiCode a f)    UCode           = Pair (fmP a UCode) (Pair (fa' f a) (CoherentFunTail f))
    fm' (PiCode _ _)    (FunEl _)       = Empty
    fm' (PiCode _ _)    (PiCode _ _)    = Empty
    fm' (PiCode _ _)    NatCode         = Empty
    fm' (PiCode _ _)    ZeroEl          = Empty
    fm' (PiCode _ _)    (SucEl _)       = Empty
    fm' (PiCode _ _)    (PairEl _ _)    = Empty
    fm' (PiCode _ _)    (SigmaCode _ _) = Empty
    fm' NatCode         Bot             = Empty
    fm' NatCode         UCode           = Top
    fm' NatCode         (FunEl _)       = Empty
    fm' NatCode         (PiCode _ _)    = Empty
    fm' NatCode         NatCode         = Empty
    fm' NatCode         ZeroEl          = Empty
    fm' NatCode         (SucEl _)       = Empty
    fm' NatCode         (PairEl _ _)    = Empty
    fm' NatCode         (SigmaCode _ _) = Empty
    fm' ZeroEl          Bot             = Empty
    fm' ZeroEl          UCode           = Empty
    fm' ZeroEl          (FunEl _)       = Empty
    fm' ZeroEl          (PiCode _ _)    = Empty
    fm' ZeroEl          NatCode         = Top
    fm' ZeroEl          ZeroEl          = Empty
    fm' ZeroEl          (SucEl _)       = Empty
    fm' ZeroEl          (PairEl _ _)    = Empty
    fm' ZeroEl          (SigmaCode _ _) = Empty
    fm' (SucEl _)       Bot             = Empty
    fm' (SucEl _)       UCode           = Empty
    fm' (SucEl _)       (FunEl _)       = Empty
    fm' (SucEl _)       (PiCode _ _)    = Empty
    fm' (SucEl a)       NatCode         = fmP a NatCode
    fm' (SucEl _)       ZeroEl          = Empty
    fm' (SucEl _)       (SucEl _)       = Empty
    fm' (SucEl _)       (PairEl _ _)    = Empty
    fm' (SucEl _)       (SigmaCode _ _) = Empty
    fm' (PairEl _ _)    Bot             = Empty
    fm' (PairEl _ _)    UCode           = Empty
    fm' (PairEl _ _)    (FunEl _)       = Empty
    fm' (PairEl _ _)    (PiCode _ _)    = Empty
    fm' (PairEl _ _)    NatCode         = Empty
    fm' (PairEl _ _)    ZeroEl          = Empty
    fm' (PairEl _ _)    (SucEl _)       = Empty
    fm' (PairEl _ _)    (PairEl _ _)    = Empty
    fm' (PairEl a1 a2)  (SigmaCode b g) = Pair (fmP a1 b) (Pair (fmP a2 (EvalFun g a1)) (Pair (PairNB a1 a2)
                 (Pair (fmP b UCode) (Pair (fa' g b) (CoherentFunTail g)))))
    fm' (SigmaCode _ _) Bot             = Empty
    fm' (SigmaCode a f) UCode           = Pair (fmP a UCode) (Pair (fa' f a) (CoherentFunTail f))
    fm' (SigmaCode _ _) (FunEl _)       = Empty
    fm' (SigmaCode _ _) (PiCode _ _)    = Empty
    fm' (SigmaCode _ _) NatCode         = Empty
    fm' (SigmaCode _ _) ZeroEl          = Empty
    fm' (SigmaCode _ _) (SucEl _)       = Empty
    fm' (SigmaCode _ _) (PairEl _ _)    = Empty
    fm' (SigmaCode _ _) (SigmaCode _ _) = Empty

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
