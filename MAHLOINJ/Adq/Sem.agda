{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Adq/Sem.agda
--
-- Small semantic lemmas on Lam approximants used by the fundamental
-- lemma.
------------------------------------------------------------------------

module MAHLOINJ.Adq.Sem where

open import MAHLOINJ.Domain.Basic
  using ( Top ; tt ; Pair ; mkSigma ; fst ; snd ; Sigma ; Eq ; refl ; Eq-transport ; Eq-sym
        ; FinEl ; Bot ; UCode ; FunEl ; FinFun ; nil ; cons )
open import MAHLOINJ.Domain.Kernel
  using (EvalFun ; LeCode ; FinMem ; Coherent ; CoherentFunTail ; LeCode-trans ; FinMem-coh-u)
open import MAHLOINJ.Model.Selection using (Selection ; sel-nil ; selectionBelow ; Coherent-Selection)
open import MAHLOINJ.Model.Comb using (Pred ; Ideal ; BodyOK ; LamS ; LamBody ; FamRel)

-- the value of a Lam approximant at a selection, in the body at the key
lamAt : (PA : Pred) (B : FinEl -> Pred) -> BodyOK B -> (g : FinFun) -> LamS PA B (FunEl g) ->
  {w v : FinEl} -> Selection g w v -> Coherent w -> B w v
lamAt PA B ok g e {w} {v} sel cw =
  let r = snd (snd (snd (snd e))) w v sel
      x = fst r ; le = fst (snd r) ; xm = fst (snd (snd r))
      cx = FinMem-coh-u x (fst e) xm
  in BodyOK.mon ok x w v cx cw le (snd (snd (snd r)))

-- the value of a codomain family at a point
famEval : (PA : Pred) (B : FinEl -> Pred) -> BodyOK B -> (f : FinFun) -> CoherentFunTail f ->
  FamRel (LamS PA B) f -> (w : FinEl) -> Coherent w -> B w (EvalFun f w)
famEval PA B ok nil cf fr w cw = Ideal.bot (BodyOK.ideal ok w cw)
famEval PA B ok (cons p ps) cf fr w cw =
  let sb = selectionBelow (cons p ps) w cf cw
      u0 = fst sb ; v0 = fst (snd sb) ; sel = fst (snd (snd sb))
      le = fst (snd (snd (snd sb))) ; eq = snd (snd (snd (snd sb)))
      r = snd (snd (snd (snd fr))) u0 v0 sel
      x = fst r ; lex = fst (snd r) ; xm = fst (snd (snd r))
      cx = FinMem-coh-u x (fst fr) xm
      cu0 = Coherent-Selection sel cf
      lexw = LeCode-trans x u0 w cx cu0 cw lex le
  in Eq-transport (B w) (Eq-sym eq) (BodyOK.mon ok x w v0 cx cw lexw (snd (snd (snd r))))

-- values of a codomain family at its selections
famAt : (PA : Pred) (B : FinEl -> Pred) -> BodyOK B -> (f : FinFun) -> FamRel (LamS PA B) f ->
  {w c : FinEl} -> Selection f w c -> Coherent w -> B w c
famAt PA B ok nil fr sel-nil cw = Ideal.bot (BodyOK.ideal ok Bot tt)
famAt PA B ok (cons p ps) fr sel cw = lamAt PA B ok (cons p ps) fr sel cw

------------------------------------------------------------------------
-- guards, projections of pairs, singletons below a function
------------------------------------------------------------------------

open import MAHLOINJ.Model.Comb using (Guard ; FstS ; SndS ; sing ; sing-coh ; guard-intro ; bot-or)
open import MAHLOINJ.Model.Selection using (Or ; left ; right ; Selection-le-EvalFun)
open import MAHLOINJ.Domain.Basic using (PairEl ; Empty)
open import MAHLOINJ.Domain.Kernel using (NotBot ; LeCode-refl ; LeCode-Bot ; LeFunCode-refl)

gi : (u : FinEl) {X : Set} -> X -> Guard u X
gi u {X} x = go (bot-or u)
  where
    go : Or (Eq u Bot) (NotBot u) -> Guard u X
    go (left refl) = tt
    go (right nb) = guard-intro u nb x

fstOf : (P : Pred) -> Ideal P -> (x1 x2 : FinEl) -> P (PairEl x1 x2) -> FstS P x1
fstOf P iP x1 x2 e = go (bot-or x1)
  where
    c12 = Ideal.coh iP (PairEl x1 x2) e
    go : Or (Eq x1 Bot) (NotBot x1) -> FstS P x1
    go (left refl) = tt
    go (right nb) = guard-intro x1 nb
      (Ideal.down iP (PairEl x1 x2) (PairEl x1 Bot) e (mkSigma (fst c12) (mkSigma tt (pnb x1 nb)))
         (mkSigma (LeCode-refl x1 (fst c12)) (LeCode-Bot x2)))
      where
        pnb : (a : FinEl) -> NotBot a -> MAHLOINJ.Domain.Kernel.PairNB a Bot
        pnb Bot ()
        pnb MAHLOINJ.Domain.Basic.UCode nb = tt
        pnb (MAHLOINJ.Domain.Basic.FunEl _) nb = tt
        pnb (MAHLOINJ.Domain.Basic.PiCode _ _) nb = tt
        pnb MAHLOINJ.Domain.Basic.NatCode nb = tt
        pnb MAHLOINJ.Domain.Basic.ZeroEl nb = tt
        pnb (MAHLOINJ.Domain.Basic.SucEl _) nb = tt
        pnb (PairEl _ _) nb = tt
        pnb (MAHLOINJ.Domain.Basic.SigmaCode _ _) nb = tt

sndOf : (P : Pred) -> Ideal P -> (x1 x2 : FinEl) -> P (PairEl x1 x2) -> SndS P x2
sndOf P iP x1 x2 e = go (bot-or x2)
  where
    c12 = Ideal.coh iP (PairEl x1 x2) e
    go : Or (Eq x2 Bot) (NotBot x2) -> SndS P x2
    go (left refl) = tt
    go (right nb) = guard-intro x2 nb
      (Ideal.down iP (PairEl x1 x2) (PairEl Bot x2) e (mkSigma tt (mkSigma (fst (snd c12)) nb))
         (mkSigma (LeCode-Bot x1) (LeCode-refl x2 (fst (snd c12)))))

-- a selection of g gives a singleton below g
singBelow : (g : FinFun) {w v : FinEl} -> Selection g w v -> CoherentFunTail g -> Coherent w ->
  LeCode (sing w v) (FunEl g)
singBelow g sel cg cw = mkSigma (Selection-le-EvalFun g sel (LeFunCode-refl g cg) cg cg cw) tt
