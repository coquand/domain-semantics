{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Adq/Cod.agda  (Tarski port of MAHLOINJ/Adq/Cod)
--
-- The codomain of a related Pi / Sigma type at a point: from the type
-- relation of (S A B) at every code, the relation of  B[N] ~ B'[N']  at
-- every code of the family at a point x of N.  Uses the singleton code
-- (a', [(x, c)]).
------------------------------------------------------------------------

module MAHLORT.Adq.Cod where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; PiCode ; SigmaCode ; FinFun ; nil ; cons ; mkSigma)
  renaming (fst to dfst ; snd to dsnd)
open import MAHLOINJ.Domain.Kernel
  using (FinMem ; FinMemAllU ; LeCode ; NotBot ; Coherent ; CoherentFunTail ; CFTcons ; mkCFT ; LeCode-refl ; FinMem-coh-u ; coh-from-aU
        ; finMem-piU-mk ; finMem-sigU-mk ; finMem-bot-from ; Sup ; comp-Bot-r ; Sup-Bot-r)
open import MAHLOINJ.Model.Selection using (Selection ; sel-nil ; sel-skip ; sel-take ; Or ; left ; right)
open import MAHLOINJ.Model.Comb using (Pred ; Ideal ; BodyOK ; PiS ; SigS ; LamS ; FamRel ; LamBody ; bot-or)
open import MAHLORT.Valid.HeadRed
open import MAHLORT.Valid.Stage
open import MAHLORT.Valid.Props using (ShapeOK ; PiOK ; SigOK)
open import MAHLORT.Valid.Public
open import MAHLORT.Adq.View

module CodCore {h : Num} {H : Ctx h} (Al Ar : Expr h) (Bl Br : Expr (suc h))
  (PA : Pred) (Bb : FinEl -> Pred) (iA : Ideal PA) (okb : BodyOK Bb) where

  -- the singleton family (x |-> c)
  private
    f1 : FinEl -> FinEl -> FinFun
    f1 x c = cons (mkSigma x c) nil

    cft1 : (x c : FinEl) -> Coherent x -> Coherent c -> NotBot c -> CoherentFunTail (f1 x c)
    cft1 x c cx cc nb = mkCFT cx cc nb tt tt

    lam1 : (x a' c : FinEl) -> PA a' -> FinMem a' UCode -> FinMem x a' -> Bb x c -> NotBot c -> Coherent c ->
      FamRel (LamS PA Bb) (f1 x c)
    lam1 x a' c ea aU xa ec nb cc =
      mkSigma a' (mkSigma (cft1 x c (FinMem-coh-u x a' xa) cc nb) (mkSigma aU (mkSigma ea body)))
      where
        body : (u v : FinEl) -> Selection (f1 x c) u v ->
               D.Sigma FinEl (\ x' -> D.Pair (LeCode x' u) (D.Pair (FinMem x' a') (Bb x' v)))
        body .Bot .Bot (sel-skip sel-nil) =
          mkSigma Bot (mkSigma tt (mkSigma (finMem-bot-from a' aU) (Ideal.bot (BodyOK.ideal okb Bot tt))))
        body .(Sup x Bot) .(Sup c Bot) (sel-take ck cv sel-nil) =
          let cx = FinMem-coh-u x a' xa
          in mkSigma x (mkSigma (transport (LeCode x) (Eq-sym (Sup-Bot-r x)) (LeCode-refl x cx))
               (mkSigma xa (transport (Bb x) (Eq-sym (Sup-Bot-r c)) ec)))

    selx : (x c : FinEl) -> Selection (f1 x c) (Sup x Bot) (Sup c Bot)
    selx x c = sel-take (comp-Bot-r x) (comp-Bot-r c) sel-nil

  module Shape (S : Shape) (sok : ShapeOK S) (Code : Pred -> Pred -> Pred) (mk : FinEl -> FinFun -> FinEl)
    (toCode : (a : FinEl) (f : FinFun) -> D.Pair (D.Pair (Coherent a) (CoherentFunTail f)) (D.Pair (PA a) (FamRel (LamS PA Bb) f)) ->
              Code PA (LamS PA Bb) (mk a f))
    (mkU : (a : FinEl) (f : FinFun) -> FinMem a UCode -> FinMemAllU f a -> CoherentFunTail f -> FinMem (mk a f) UCode)
    (view : {b : FinEl} {f : FinFun} -> RTy H (S Al Bl) (S Ar Br) (mk b f) -> CodeTy S RTy RTm H (S Al Bl) (S Ar Br) b f)
    (DT : (a : FinEl) -> Code PA (LamS PA Bb) a -> FinMem a UCode -> RTy H (S Al Bl) (S Ar Br) a) where

    cod : (N N' : Expr h) (x a' c : FinEl) -> ConvTm H N N' Al ->
      ((a : FinEl) -> PA a -> FinMem a UCode -> FinMem x a -> RTm H N N' Al x a) ->
      PA a' -> FinMem a' UCode -> FinMem x a' -> Bb x c -> FinMem c UCode -> RTy H (subst1 Bl N) (subst1 Br N') c
    cod N N' x a' c cv RN ea aU xa ec cU = go (bot-or c)
      where
        go : Or (Eq c Bot) (NotBot c) -> RTy H (subst1 Bl N) (subst1 Br N') c
        go (left refl) = tt
        go (right nb) =
          let cx = FinMem-coh-u x a' xa ; cc = coh-from-aU c cU ; ca = coh-from-aU a' aU
              cf = cft1 x c cx cc nb
              code = toCode a' (f1 x c) (mkSigma (mkSigma ca cf) (mkSigma ea (lam1 x a' c ea aU xa ec nb cc)))
              codeU = mkU a' (f1 x c) aU (mkSigma (mkSigma xa cU) tt) cf
              r = view (DT (mk a' (f1 x c)) code codeU)
              rm = transport (\ z -> RTm H N N' Al z a') (Eq-sym (Sup-Bot-r x)) (RN a' ea aU xa)
              res = codeCodN sok r (Sup x Bot) (Sup c Bot) (selx x c) N N' cv rm
          in transport (RTy H (subst1 Bl N) (subst1 Br N')) (Sup-Bot-r c) res

  module PiCod = Shape PiB PiOK PiS PiCode (\ a f e -> e) finMem-piU-mk (\ r -> piTyV r)
  module SigCod = Shape SigmaB SigOK SigS SigmaCode (\ a f e -> e) finMem-sigU-mk (\ r -> sigTyV r)
