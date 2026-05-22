{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- PaperTyping.agda  (MIN/ — Pi + U fragment)
--
-- RE-FOUNDED, TERMINATING-FREE.  Formerly an ~550-line block with 3
-- termination-pragmas (the FinMem swap/promote that Agda's foetus checker
-- cannot certify).  The membership ":" (FinMem) is now built by structural
-- recursion on a stage index in the MIN/FinMemStage* family and collapsed
-- by stability; PaperTyping PRESENTS its properties.
--
-- FinMem (the element membership) is the stage-collapse `finMemC` and has
-- NO definitional computation rule; its "expected unfoldings" are the
-- propositional iso pairs below (the swap, the Pi-type-wf triple, and the
-- FunEl characterisation  "Fun f : Pi a g").  FinMemFun / FinMemAllU, by
-- contrast, are STRUCTURAL over FinMem (they only recurse down the FinFun
-- list -- no swap/promote), so they keep their definitional unfolding and
-- the cone destructures them with fst/snd directly.
--
-- Closure / monotonicity (compatible sup  u1:a, u2:a, u1<>u2 -> u1\/u2:a ;
-- monotonicity  u:a, a<=b, b:U -> u:b) come from MIN.FinMemStageProps,
-- bridged where they mention FinMemFun / FinMemAllU.
--
-- 0 TERMINATING, 0 postulates, 0 holes -- across the whole family.
------------------------------------------------------------------------

module MIN.PaperTyping where

open import MIN.Basic
  using ( Top ; tt ; Pair ; mkSigma ; fst ; snd
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; nil ; cons )
open import MIN.PaperOrder public
open import MIN.FinMemStage using ( finMemC ; finMemAllUC ; finMemFunC )
open import MIN.FinMemStageUnfold
  using ( finMemC-piU-dom ; finMemC-piU-allU ; finMemC-piU-cft ; finMemC-piU-mk
        ; finMemC-funel-fun ; finMemC-funel-coh ; finMemC-funel-wf ; finMemC-funel-mk
        ; finMemFunC-nil ; finMemFunC-hd-key ; finMemFunC-hd-val ; finMemFunC-tl ; finMemFunC-mk
        ; finMemAllUC-nil ; finMemAllUC-hd-key ; finMemAllUC-hd-val ; finMemAllUC-tl ; finMemAllUC-mk )
import MIN.FinMemStageProps as P

------------------------------------------------------------------------
-- Public membership ":" (the stage-collapse) + structural FinMemFun/AllU.
------------------------------------------------------------------------

FinMem : FinEl -> FinEl -> Set
FinMem = finMemC

FinMemFun : FinFun -> FinEl -> FinFun -> Set
FinMemFun nil         a f = Top
FinMemFun (cons p ps) a f =
  Pair (Pair (FinMem (fst p) a) (FinMem (snd p) (EvalFun f (fst p)))) (FinMemFun ps a f)

FinMemAllU : FinFun -> FinEl -> Set
FinMemAllU nil         a = Top
FinMemAllU (cons p ps) a =
  Pair (Pair (FinMem (fst p) a) (FinMem (snd p) UCode)) (FinMemAllU ps a)

------------------------------------------------------------------------
-- Bridges  FinMemAllU <-> finMemAllUC  and  FinMemFun <-> finMemFunC.
------------------------------------------------------------------------

allU-to : (f : FinFun) (a : FinEl) -> FinMemAllU f a -> finMemAllUC f a
allU-to nil         a m = finMemAllUC-nil a
allU-to (cons p ps) a m =
  finMemAllUC-mk p ps a (fst (fst m)) (snd (fst m)) (allU-to ps a (snd m))

allU-from : (f : FinFun) (a : FinEl) -> finMemAllUC f a -> FinMemAllU f a
allU-from nil         a m = tt
allU-from (cons p ps) a m =
  mkSigma (mkSigma (finMemAllUC-hd-key p ps a m) (finMemAllUC-hd-val p ps a m))
          (allU-from ps a (finMemAllUC-tl p ps a m))

fun-to : (g : FinFun) (a : FinEl) (f : FinFun) -> FinMemFun g a f -> finMemFunC g a f
fun-to nil         a f m = finMemFunC-nil a f
fun-to (cons p ps) a f m =
  finMemFunC-mk p ps a f (fst (fst m)) (snd (fst m)) (fun-to ps a f (snd m))

fun-from : (g : FinFun) (a : FinEl) (f : FinFun) -> finMemFunC g a f -> FinMemFun g a f
fun-from nil         a f m = tt
fun-from (cons p ps) a f m =
  mkSigma (mkSigma (finMemFunC-hd-key p ps a f m) (finMemFunC-hd-val p ps a f m))
          (fun-from ps a f (finMemFunC-tl p ps a f m))

------------------------------------------------------------------------
-- The expected computation rules of FinMem as iso accessors:
--   swap        FinMem Bot a  <->  FinMem a UCode
--   Pi-type-wf  FinMem (PiCode a f) UCode  <->  (FinMem a UCode, FinMemAllU f a, CoherentFunTail f)
--   FunEl       "Fun g : Pi a f"  FinMem (FunEl g) (PiCode a f)
--               <->  (FinMemFun g a f, CoherentFun g, FinMem (PiCode a f) UCode)
------------------------------------------------------------------------

open MIN.FinMemStageUnfold using ( finMemC-bot-to ; finMemC-bot-from )

finMem-bot-to : (a : FinEl) -> FinMem Bot a -> FinMem a UCode
finMem-bot-to = finMemC-bot-to
finMem-bot-from : (a : FinEl) -> FinMem a UCode -> FinMem Bot a
finMem-bot-from = finMemC-bot-from

finMem-piU-dom : (a : FinEl) (f : FinFun) -> FinMem (PiCode a f) UCode -> FinMem a UCode
finMem-piU-dom = finMemC-piU-dom

finMem-piU-allU : (a : FinEl) (f : FinFun) -> FinMem (PiCode a f) UCode -> FinMemAllU f a
finMem-piU-allU a f mem = allU-from f a (finMemC-piU-allU a f mem)

finMem-piU-cft : (a : FinEl) (f : FinFun) -> FinMem (PiCode a f) UCode -> CoherentFunTail f
finMem-piU-cft = finMemC-piU-cft

finMem-piU-mk : (a : FinEl) (f : FinFun) ->
  FinMem a UCode -> FinMemAllU f a -> CoherentFunTail f -> FinMem (PiCode a f) UCode
finMem-piU-mk a f dom allU cft = finMemC-piU-mk a f dom (allU-to f a allU) cft

finMem-funel-fun : (g : FinFun) (a : FinEl) (f : FinFun) ->
  FinMem (FunEl g) (PiCode a f) -> FinMemFun g a f
finMem-funel-fun g a f mem = fun-from g a f (finMemC-funel-fun g a f mem)

finMem-funel-coh : (g : FinFun) (a : FinEl) (f : FinFun) ->
  FinMem (FunEl g) (PiCode a f) -> CoherentFun g
finMem-funel-coh = finMemC-funel-coh

finMem-funel-wf : (g : FinFun) (a : FinEl) (f : FinFun) ->
  FinMem (FunEl g) (PiCode a f) -> FinMem (PiCode a f) UCode
finMem-funel-wf = finMemC-funel-wf

finMem-funel-mk : (g : FinFun) (a : FinEl) (f : FinFun) ->
  FinMemFun g a f -> CoherentFun g -> FinMem (PiCode a f) UCode -> FinMem (FunEl g) (PiCode a f)
finMem-funel-mk g a f fun coh wf = finMemC-funel-mk g a f (fun-to g a f fun) coh wf

------------------------------------------------------------------------
-- Projections (re-exported; FinMem-only signatures).
------------------------------------------------------------------------

open MIN.FinMemStageUnfold public using ( FinMem-coh-u ; FinMem-a-in-U ; FinMem-coh-a ; coh-from-aU )

------------------------------------------------------------------------
-- Closure / monotonicity.  FinMem-only signatures re-exported directly;
-- the FinMemFun/FinMemAllU ones are bridged.
------------------------------------------------------------------------

open P public
  using ( finMemUCode-Sup ; finMem-Sup-right ; finMem-Sup-left
        ; FinMem-Sup-element ; finMem-Sup-both ; finMem-upward )

-- compatible sup at U:  d:U, c:U (+ allU evidence), d<>c  ->  append/Sup : U
FinMemAllU-append-Sup : (d c : FinEl) (f h : FinFun) ->
  Comp d c -> Coherent d -> Coherent c -> FinMem d UCode -> FinMem c UCode ->
  CoherentFunTail f -> CoherentFunTail h -> FinMemAllU f d -> FinMemAllU h c ->
  FinMemAllU (append f h) (Sup d c)
FinMemAllU-append-Sup d c f h comp cohd cohc dU cU cohf cohh memf memh =
  allU-from (append f h) (Sup d c)
    (P.FinMemAllU-append-Sup d c f h comp cohd cohc dU cU cohf cohh (allU-to f d memf) (allU-to h c memh))

EvalFun-in-UCode : (f : FinFun) (x d : FinEl) ->
  CoherentFunTail f -> Coherent x -> FinMemAllU f d -> FinMem (EvalFun f x) UCode
EvalFun-in-UCode f x d cohf cx allU = P.EvalFun-in-UCode f x d cohf cx (allU-to f d allU)

finMemFun-upward : (g : FinFun) (a b : FinEl) (f h : FinFun) ->
  LeCode a b -> Coherent a -> Coherent b ->
  CoherentFunTail f -> CoherentFunTail h -> LeFunCode f h ->
  FinMemFun g a f -> FinMem b UCode -> FinMemAllU h b -> FinMemFun g b h
finMemFun-upward g a b f h le ca cb cf ch lfh mem bU allUh =
  fun-from g b h
    (P.finMemFun-upward g a b f h le ca cb cf ch lfh (fun-to g a f mem) bU (allU-to h b allUh))

-- FinMemFun-append: structural on g (definitional unfolding of FinMemFun).
FinMemFun-append : (g h : FinFun) (b : FinEl) (f : FinFun) ->
  FinMemFun g b f -> FinMemFun h b f -> FinMemFun (append g h) b f
FinMemFun-append nil         h b f mg mh = mh
FinMemFun-append (cons p ps) h b f mg mh = mkSigma (fst mg) (FinMemFun-append ps h b f (snd mg) mh)
