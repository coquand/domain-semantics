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
--     (ID.Domain.Order / LeqStageBridge); it is NOT stage-indexed here.
--
-- The public membership is the stage-collapsed `finMemC`/`finMemFunC`/
-- `finMemAllUC` at the canonical level (cf. LeqC); its expected unfolding,
-- projection and closure properties are proved (via stability) in the
-- downstream FinMemStage* files and re-exported by PaperTyping.
--
-- NO postulates.
------------------------------------------------------------------------

module ID.Domain.MemStage where

open import ID.Domain.Basic
  using ( Top ; tt ; Empty
        ; Nat ; zero ; suc ; max
        ; Le ; Le-refl ; Le-suc ; Le-trans ; Le-max-l ; Le-max-r
        ; Pair ; mkSigma ; fst ; snd ; Sigma
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; IdCode ; RefEl ; FinFun ; nil ; cons )
open import ID.Domain.Order
  using ( RANK ; RANKFun ; Sup ; append ; EvalFun ; LeCode
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
    fm0 UCode        Bot          = Empty
    fm0 UCode        UCode        = Top
    fm0 UCode        (FunEl _)    = Empty
    fm0 UCode        (PiCode _ _) = Empty
    fm0 (FunEl _)    Bot          = Empty
    fm0 (FunEl _)    UCode        = Empty
    fm0 (FunEl _)    (FunEl _)    = Empty
    fm0 (FunEl _)    (PiCode _ _) = Empty
    fm0 (PiCode _ _) Bot          = Empty
    fm0 (PiCode _ _) UCode        = Empty
    fm0 (PiCode _ _) (FunEl _)    = Empty
    fm0 (PiCode _ _) (PiCode _ _) = Empty
    fm0 Bot          (IdCode _ _ _) = Empty
    fm0 Bot          (RefEl _)      = Empty
    fm0 UCode        (IdCode _ _ _) = Empty
    fm0 UCode        (RefEl _)      = Empty
    fm0 (FunEl _)    (IdCode _ _ _) = Empty
    fm0 (FunEl _)    (RefEl _)      = Empty
    fm0 (PiCode _ _) (IdCode _ _ _) = Empty
    fm0 (PiCode _ _) (RefEl _)      = Empty
    fm0 (IdCode _ _ _) Bot          = Empty
    fm0 (IdCode _ _ _) UCode        = Empty
    fm0 (IdCode _ _ _) (FunEl _)    = Empty
    fm0 (IdCode _ _ _) (PiCode _ _) = Empty
    fm0 (IdCode _ _ _) (IdCode _ _ _) = Empty
    fm0 (IdCode _ _ _) (RefEl _)    = Empty
    fm0 (RefEl _)    Bot          = Empty
    fm0 (RefEl _)    UCode        = Empty
    fm0 (RefEl _)    (FunEl _)    = Empty
    fm0 (RefEl _)    (PiCode _ _) = Empty
    fm0 (RefEl _)    (IdCode _ _ _) = Empty
    fm0 (RefEl _)    (RefEl _)    = Empty

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
    -- UCode element
    fm' UCode        UCode        = Top
    fm' UCode        Bot          = Empty
    fm' UCode        (FunEl g)    = Empty
    fm' UCode        (PiCode a f) = Empty
    -- FunEl element (inlined promote: the Pi-type-wf triple in line 3)
    fm' (FunEl g)    (PiCode a f) =
      Pair (ff' g a f)
           (Pair (CoherentFun g)
                 (Pair (fmP a UCode) (Pair (fa' f a) (CoherentFunTail f))))
    fm' (FunEl g)    Bot          = Empty
    fm' (FunEl g)    UCode        = Empty
    fm' (FunEl g)    (FunEl h)    = Empty
    -- PiCode element
    fm' (PiCode a f) UCode        =
      Pair (fmP a UCode) (Pair (fa' f a) (CoherentFunTail f))
    fm' (PiCode a f) Bot          = Empty
    fm' (PiCode a f) (FunEl g)    = Empty
    fm' (PiCode a f) (PiCode b g) = Empty
    -- Id fragment.  IdCode is a type-code (member of UCode; Bot inhabits a
    -- well-formed IdCode).  RefEl w is a PROOF, member of IdCode t u v iff
    -- w <= u and w <= v  (Coquand's rule).
    fm' Bot          (IdCode t u v) = Pair (fmP t UCode) (Pair (fmP u t) (fmP v t))
    fm' Bot          (RefEl _)      = Empty
    fm' UCode        (IdCode _ _ _) = Empty
    fm' UCode        (RefEl _)      = Empty
    fm' (FunEl g)    (IdCode _ _ _) = Empty
    fm' (FunEl g)    (RefEl _)      = Empty
    fm' (PiCode a f) (IdCode _ _ _) = Empty
    fm' (PiCode a f) (RefEl _)      = Empty
    fm' (IdCode t u v) UCode        = Pair (fmP t UCode) (Pair (fmP u t) (fmP v t))
    fm' (IdCode t u v) Bot          = Empty
    fm' (IdCode t u v) (FunEl _)    = Empty
    fm' (IdCode t u v) (PiCode _ _) = Empty
    fm' (IdCode t u v) (IdCode _ _ _) = Empty
    fm' (IdCode t u v) (RefEl _)    = Empty
    -- Ref w : Id t u v  requires  (Coherent w) and (w : t), together with
    -- w <= u, w <= v, and the Id-type-wellformedness witness (t:U, u:t, v:t)
    -- so the type projections (FinMem-coh-u / FinMem-a-in-U) go through.
    fm' (RefEl w)    (IdCode t u v) =
      Pair (Pair (Coherent w) (fmP w t))
           (Pair (Pair (LeCode w u) (LeCode w v))
                 (Pair (fmP t UCode) (Pair (fmP u t) (fmP v t))))
    fm' (RefEl w)    Bot          = Empty
    fm' (RefEl w)    UCode        = Empty
    fm' (RefEl w)    (FunEl _)    = Empty
    fm' (RefEl w)    (PiCode _ _) = Empty
    fm' (RefEl w)    (RefEl _)    = Empty

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
