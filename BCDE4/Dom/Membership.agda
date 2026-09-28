{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- PaperTyping.agda  (MIN/ — Pi + U fragment)
--
-- RE-FOUNDED.  Formerly an ~550-line block with 3
-- non-structural recursions (the FinMem swap/promote that Agda's foetus checker
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
-- monotonicity  u:a, a<=b, b:U -> u:b) come from BCDE4.Dom.MemProps,
-- bridged where they mention FinMemFun / FinMemAllU.
--
-- 0 postulates, 0 holes -- across the whole family.
------------------------------------------------------------------------

module BCDE4.Dom.Membership where

open import BCDE4.Dom.Basic using (U0 ; EqL ; eqL ; EqL-refl ; EqL-sym ; EqL-trans ; EqL-Eq ; eqL-EqL ; EqL-eqL ; eqL-refl)

open import BCDE4.Dom.Basic
  using ( Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ; Sigma ; Eq ; refl
        ; FinEl ; Bot ; UCode ; LevTy ; LevEl ; FunEl ; PiCode ; LPiCode ; FinFun ; nil ; cons ; Nat )
open import BCDE4.Dom.Order public
open import BCDE4.Dom.MemStage using ( finMemC ; finMemAllUC ; finMemFunC )
open import BCDE4.Dom.MemUnfold
  using ( finMemC-piU-dom ; finMemC-piU-allU ; finMemC-piU-cft ; finMemC-piU-mk
        ; finMemC-LpiU-allU ; finMemC-LpiU-cft ; finMemC-LpiU-mk
        ; finMemC-Lfunel-fun ; finMemC-Lfunel-coh ; finMemC-Lfunel-wf ; finMemC-Lfunel-mk
        ; finMemC-funel-fun ; finMemC-funel-coh ; finMemC-funel-wf ; finMemC-funel-mk
        ; finMemFunC-nil ; finMemFunC-hd-key ; finMemFunC-hd-val ; finMemFunC-tl ; finMemFunC-mk
        ; finMemAllUC-nil ; finMemAllUC-hd-key ; finMemAllUC-hd-val ; finMemAllUC-tl ; finMemAllUC-mk )
import BCDE4.Dom.MemProps as P
open import BCDE4.Basic using ( Either ; inl ; inr )

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
  Pair (Pair (FinMem (fst p) a) (FinMem (snd p) U0)) (FinMemAllU ps a)

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

open BCDE4.Dom.MemUnfold using ( finMemC-bot-to ; finMemC-bot-from )

finMem-bot-to : (a : FinEl) -> FinMem Bot a -> FinMem a U0
finMem-bot-to = finMemC-bot-to
finMem-bot-from : (a : FinEl) -> FinMem a U0 -> FinMem Bot a
finMem-bot-from = finMemC-bot-from

finMem-piU-dom : (a : FinEl) (f : FinFun) -> FinMem (PiCode a f) U0 -> FinMem a U0
finMem-piU-dom = finMemC-piU-dom

finMem-piU-allU : (a : FinEl) (f : FinFun) -> FinMem (PiCode a f) U0 -> FinMemAllU f a
finMem-piU-allU a f mem = allU-from f a (finMemC-piU-allU a f mem)

finMem-piU-cft : (a : FinEl) (f : FinFun) -> FinMem (PiCode a f) U0 -> CoherentFunTail f
finMem-piU-cft = finMemC-piU-cft

finMem-piU-mk : (a : FinEl) (f : FinFun) ->
  FinMem a U0 -> FinMemAllU f a -> CoherentFunTail f -> FinMem (PiCode a f) U0
finMem-piU-mk a f dom allU cft = finMemC-piU-mk a f dom (allU-to f a allU) cft

finMem-funel-fun : (g : FinFun) (a : FinEl) (f : FinFun) ->
  FinMem (FunEl g) (PiCode a f) -> FinMemFun g a f
finMem-funel-fun g a f mem = fun-from g a f (finMemC-funel-fun g a f mem)

finMem-funel-coh : (g : FinFun) (a : FinEl) (f : FinFun) ->
  FinMem (FunEl g) (PiCode a f) -> CoherentFun g
finMem-funel-coh = finMemC-funel-coh

finMem-funel-wf : (g : FinFun) (a : FinEl) (f : FinFun) ->
  FinMem (FunEl g) (PiCode a f) -> FinMem (PiCode a f) U0
finMem-funel-wf = finMemC-funel-wf

finMem-funel-mk : (g : FinFun) (a : FinEl) (f : FinFun) ->
  FinMemFun g a f -> CoherentFun g -> FinMem (PiCode a f) U0 -> FinMem (FunEl g) (PiCode a f)
finMem-funel-mk g a f fun coh wf = finMemC-funel-mk g a f (fun-to g a f fun) coh wf

------------------------------------------------------------------------
-- Projections (re-exported; FinMem-only signatures).
------------------------------------------------------------------------

open BCDE4.Dom.MemUnfold public using ( FinMem-coh-u ; FinMem-a-in-U ; FinMem-coh-a ; coh-from-aU )

------------------------------------------------------------------------
-- Closure / monotonicity.  FinMem-only signatures re-exported directly;
-- the FinMemFun/FinMemAllU ones are bridged.
------------------------------------------------------------------------

open P public
  using ( finMemUCode-Sup ; finMem-Sup-right ; finMem-Sup-left
        ; FinMem-Sup-element ; finMem-Sup-both ; finMem-upward )

-- compatible sup at U:  d:U, c:U (+ allU evidence), d<>c  ->  append/Sup : U
FinMemAllU-append-Sup : (d c : FinEl) (f h : FinFun) ->
  Comp d c -> Coherent d -> Coherent c -> FinMem d U0 -> FinMem c U0 ->
  CoherentFunTail f -> CoherentFunTail h -> FinMemAllU f d -> FinMemAllU h c ->
  FinMemAllU (append f h) (Sup d c)
FinMemAllU-append-Sup d c f h comp cohd cohc dU cU cohf cohh memf memh =
  allU-from (append f h) (Sup d c)
    (P.FinMemAllU-append-Sup d c f h comp cohd cohc dU cU cohf cohh (allU-to f d memf) (allU-to h c memh))

EvalFun-in-UCode : (f : FinFun) (x d : FinEl) ->
  CoherentFunTail f -> Coherent x -> FinMemAllU f d -> FinMem (EvalFun f x) U0
EvalFun-in-UCode f x d cohf cx allU = P.EvalFun-in-UCode f x d cohf cx (allU-to f d allU)

finMemFun-upward : (g : FinFun) (a b : FinEl) (f h : FinFun) ->
  LeCode a b -> Coherent a -> Coherent b ->
  CoherentFunTail f -> CoherentFunTail h -> LeFunCode f h ->
  FinMemFun g a f -> FinMem b U0 -> FinMemAllU h b -> FinMemFun g b h
finMemFun-upward g a b f h le ca cb cf ch lfh mem bU allUh =
  fun-from g b h
    (P.finMemFun-upward g a b f h le ca cb cf ch lfh (fun-to g a f mem) bU (allU-to h b allUh))

-- FinMemFun-append: structural on g (definitional unfolding of FinMemFun).
FinMemFun-append : (g h : FinFun) (b : FinEl) (f : FinFun) ->
  FinMemFun g b f -> FinMemFun h b f -> FinMemFun (append g h) b f
FinMemFun-append nil         h b f mg mh = mh
FinMemFun-append (cons p ps) h b f mg mh = mkSigma (fst mg) (FinMemFun-append ps h b f (snd mg) mh)

------------------------------------------------------------------------
-- Membership in a universe does not depend on its level.
------------------------------------------------------------------------

finMem-U-lvl : (y : FinEl) (k m : Nat) -> FinMem y (UCode k) -> FinMem y (UCode m)
finMem-U-lvl Bot          k m x = x
finMem-U-lvl (UCode _)    k m x = x
finMem-U-lvl LevTy        k m x = x
finMem-U-lvl (LPiCode _)  k m x = x
finMem-U-lvl (LevEl _)    k m ()
finMem-U-lvl (FunEl _)    k m x = x
finMem-U-lvl (PiCode _ _) k m x = x

------------------------------------------------------------------------
-- Universe levels as a type: LevTy (a type code) and its tokens LevEl k.
--   LevTy : U_k for every k;  LevEl k : LevTy;  Bot : LevTy (swap);
--   the members of LevTy are exactly Bot and the LevEl k;
--   LevEl k is not a type (it has no members, it is in no universe);
--   LevEl k and LevEl m are compatible / ordered iff k = m.
------------------------------------------------------------------------

finMem-LevTy-U : (k : Nat) -> FinMem LevTy (UCode k)
finMem-LevTy-U k = tt

finMem-LevTy-U0 : FinMem LevTy U0
finMem-LevTy-U0 = tt

finMem-LevEl-LevTy : (k : Nat) -> FinMem (LevEl k) LevTy
finMem-LevEl-LevTy k = tt

finMem-Bot-LevTy : FinMem Bot LevTy
finMem-Bot-LevTy = tt

finMem-LevTy-inv : (u : FinEl) -> FinMem u LevTy ->
  Either (Eq u Bot) (Sigma Nat (\ k -> Eq u (LevEl k)))
finMem-LevTy-inv Bot          m = inl refl
finMem-LevTy-inv (UCode _)    ()
finMem-LevTy-inv LevTy        ()
finMem-LevTy-inv (LevEl k)    m = inr (mkSigma k refl)
finMem-LevTy-inv (FunEl _)    ()
finMem-LevTy-inv (PiCode _ _) ()

finMem-LevEl-notType : (k m : Nat) -> FinMem (LevEl k) (UCode m) -> Empty
finMem-LevEl-notType k m ()

finMem-into-LevEl : (u : FinEl) (k : Nat) -> FinMem u (LevEl k) -> Empty
finMem-into-LevEl Bot          k ()
finMem-into-LevEl (UCode _)    k ()
finMem-into-LevEl LevTy        k ()
finMem-into-LevEl (LevEl _)    k ()
finMem-into-LevEl (FunEl _)    k ()
finMem-into-LevEl (PiCode _ _) k ()

Comp-LevEl-EqL : (k m : Nat) -> Comp (LevEl k) (LevEl m) -> EqL k m
Comp-LevEl-EqL k m c = c

LeCode-LevEl-EqL : (k m : Nat) -> LeCode (LevEl k) (LevEl m) -> EqL k m
LeCode-LevEl-EqL k m le = le

LeCode-LevEl-refl : (k : Nat) -> LeCode (LevEl k) (LevEl k)
LeCode-LevEl-refl k = EqL-refl k

LeCode-LevTy-refl : LeCode LevTy LevTy
LeCode-LevTy-refl = tt

------------------------------------------------------------------------
-- Level-indexed products  LPiCode f  ("[alpha] A").
-- LPiCode f behaves exactly like PiCode LevTy f; its own clauses drop the
-- trivial LevTy components (LevTy : U, LevTy <= LevTy, Comp LevTy LevTy,
-- Coherent LevTy).  First the L-analogues of the Pi accessors, then the
-- bridges  LPiCode f  <->  PiCode LevTy f.
------------------------------------------------------------------------

finMem-LpiU-dom : (f : FinFun) -> FinMem (LPiCode f) U0 -> FinMem LevTy U0
finMem-LpiU-dom f mem = tt

finMem-LpiU-allU : (f : FinFun) -> FinMem (LPiCode f) U0 -> FinMemAllU f LevTy
finMem-LpiU-allU f mem = allU-from f LevTy (finMemC-LpiU-allU f mem)

finMem-LpiU-cft : (f : FinFun) -> FinMem (LPiCode f) U0 -> CoherentFunTail f
finMem-LpiU-cft = finMemC-LpiU-cft

finMem-LpiU-mk : (f : FinFun) ->
  FinMemAllU f LevTy -> CoherentFunTail f -> FinMem (LPiCode f) U0
finMem-LpiU-mk f allU cft = finMemC-LpiU-mk f (allU-to f LevTy allU) cft

finMem-Lfunel-fun : (g : FinFun) (f : FinFun) ->
  FinMem (FunEl g) (LPiCode f) -> FinMemFun g LevTy f
finMem-Lfunel-fun g f mem = fun-from g LevTy f (finMemC-Lfunel-fun g f mem)

finMem-Lfunel-coh : (g : FinFun) (f : FinFun) ->
  FinMem (FunEl g) (LPiCode f) -> CoherentFun g
finMem-Lfunel-coh = finMemC-Lfunel-coh

finMem-Lfunel-wf : (g : FinFun) (f : FinFun) ->
  FinMem (FunEl g) (LPiCode f) -> FinMem (LPiCode f) U0
finMem-Lfunel-wf = finMemC-Lfunel-wf

finMem-Lfunel-mk : (g : FinFun) (f : FinFun) ->
  FinMemFun g LevTy f -> CoherentFun g -> FinMem (LPiCode f) U0 -> FinMem (FunEl g) (LPiCode f)
finMem-Lfunel-mk g f fun coh wf = finMemC-Lfunel-mk g f (fun-to g LevTy f fun) coh wf

-- structural bridges (definitional up to the trivial LevTy components)

RANK-LPi : (f : FinFun) -> Eq (RANK (LPiCode f)) (RANK (PiCode LevTy f))
RANK-LPi f = refl

applyEl-LPi : (f : FinFun) (v : FinEl) -> Eq (applyEl (LPiCode f) v) (applyEl (PiCode LevTy f) v)
applyEl-LPi f v = refl

Sup-LPi : (f g : FinFun) -> Eq (Sup (LPiCode f) (LPiCode g)) (LPiCode (append f g))
Sup-LPi f g = refl

Sup-Pi-LevTy : (f g : FinFun) ->
  Eq (Sup (PiCode LevTy f) (PiCode LevTy g)) (PiCode LevTy (append f g))
Sup-Pi-LevTy f g = refl

LeCode-LPi-to : (f g : FinFun) -> LeCode (LPiCode f) (LPiCode g) -> LeCode (PiCode LevTy f) (PiCode LevTy g)
LeCode-LPi-to f g le = mkSigma tt le

LeCode-LPi-from : (f g : FinFun) -> LeCode (PiCode LevTy f) (PiCode LevTy g) -> LeCode (LPiCode f) (LPiCode g)
LeCode-LPi-from f g le = snd le

Comp-LPi-to : (f g : FinFun) -> Comp (LPiCode f) (LPiCode g) -> Comp (PiCode LevTy f) (PiCode LevTy g)
Comp-LPi-to f g c = mkSigma tt c

Comp-LPi-from : (f g : FinFun) -> Comp (PiCode LevTy f) (PiCode LevTy g) -> Comp (LPiCode f) (LPiCode g)
Comp-LPi-from f g c = snd c

Coherent-LPi-to : (f : FinFun) -> Coherent (LPiCode f) -> Coherent (PiCode LevTy f)
Coherent-LPi-to f c = mkSigma tt c

Coherent-LPi-from : (f : FinFun) -> Coherent (PiCode LevTy f) -> Coherent (LPiCode f)
Coherent-LPi-from f c = snd c

-- membership bridges: LPiCode f as a TYPE-ELEMENT (of a universe)

FinMem-LPi-ty-to : (f : FinFun) (a : FinEl) -> FinMem (LPiCode f) a -> FinMem (PiCode LevTy f) a
FinMem-LPi-ty-to f (UCode k) m =
  let m0 = finMem-U-lvl (LPiCode f) k 0 m
  in finMem-U-lvl (PiCode LevTy f) 0 k
       (finMemC-piU-mk LevTy f tt (finMemC-LpiU-allU f m0) (finMemC-LpiU-cft f m0))
FinMem-LPi-ty-to f Bot ()
FinMem-LPi-ty-to f LevTy ()
FinMem-LPi-ty-to f (LevEl _) ()
FinMem-LPi-ty-to f (FunEl _) ()
FinMem-LPi-ty-to f (PiCode _ _) ()
FinMem-LPi-ty-to f (LPiCode _) ()

FinMem-LPi-ty-from : (f : FinFun) (a : FinEl) -> FinMem (PiCode LevTy f) a -> FinMem (LPiCode f) a
FinMem-LPi-ty-from f (UCode k) m =
  let m0 = finMem-U-lvl (PiCode LevTy f) k 0 m
  in finMem-U-lvl (LPiCode f) 0 k
       (finMemC-LpiU-mk f (finMemC-piU-allU LevTy f m0) (finMemC-piU-cft LevTy f m0))
FinMem-LPi-ty-from f Bot ()
FinMem-LPi-ty-from f LevTy ()
FinMem-LPi-ty-from f (LevEl _) ()
FinMem-LPi-ty-from f (FunEl _) ()
FinMem-LPi-ty-from f (PiCode _ _) ()
FinMem-LPi-ty-from f (LPiCode _) ()

-- membership bridges: elements OF the level-indexed product

FinMem-LPi-el-to : (u : FinEl) (f : FinFun) -> FinMem u (LPiCode f) -> FinMem u (PiCode LevTy f)
FinMem-LPi-el-to Bot f m =
  finMemC-bot-from (PiCode LevTy f) (FinMem-LPi-ty-to f U0 (finMemC-bot-to (LPiCode f) m))
FinMem-LPi-el-to (FunEl g) f m =
  finMemC-funel-mk g LevTy f (finMemC-Lfunel-fun g f m) (finMemC-Lfunel-coh g f m)
    (FinMem-LPi-ty-to f U0 (finMemC-Lfunel-wf g f m))
FinMem-LPi-el-to (UCode _) f ()
FinMem-LPi-el-to LevTy f ()
FinMem-LPi-el-to (LevEl _) f ()
FinMem-LPi-el-to (PiCode _ _) f ()
FinMem-LPi-el-to (LPiCode _) f ()

FinMem-LPi-el-from : (u : FinEl) (f : FinFun) -> FinMem u (PiCode LevTy f) -> FinMem u (LPiCode f)
FinMem-LPi-el-from Bot f m =
  finMemC-bot-from (LPiCode f) (FinMem-LPi-ty-from f U0 (finMemC-bot-to (PiCode LevTy f) m))
FinMem-LPi-el-from (FunEl g) f m =
  finMemC-Lfunel-mk g f (finMemC-funel-fun g LevTy f m) (finMemC-funel-coh g LevTy f m)
    (FinMem-LPi-ty-from f U0 (finMemC-funel-wf g LevTy f m))
FinMem-LPi-el-from (UCode _) f ()
FinMem-LPi-el-from LevTy f ()
FinMem-LPi-el-from (LevEl _) f ()
FinMem-LPi-el-from (PiCode _ _) f ()
FinMem-LPi-el-from (LPiCode _) f ()
