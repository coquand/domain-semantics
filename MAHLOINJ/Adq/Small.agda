{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Adq/Small.agda
--
-- Case lemmas: variables, function extensionality, zero, successor.
------------------------------------------------------------------------

module MAHLOINJ.Adq.Small where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Typing
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; PairEl ; SigmaCode
             ; FinFun ; mkSigma) renaming (fst to dfst ; snd to dsnd)
open import MAHLOINJ.Domain.Kernel
  using (EvalFun ; LeCode ; FinMem ; NotBot ; Coherent ; FinMem-a-in-U ; FinMem-coh-u ; LeCode-refl
        ; finMem-funel-coh ; cft-from-cf ; sucNat-to)
open import MAHLOINJ.Model.Selection using (Selection ; Or ; left ; right ; Coherent-Selection-val)
open import MAHLOINJ.Model.Comb using (bot-or ; guard-intro ; sing-coh)
open import MAHLOINJ.Model.Eval
open import MAHLOINJ.Model.EvalSubst using (EvalRel-wk)
open import MAHLOINJ.Model.SoundBase using (bodyOK ; Fits-var)
open import MAHLOINJ.Syntax.Lemmas
open import MAHLOINJ.Syntax.Subst
open import MAHLOINJ.Syntax.Funct
open import MAHLOINJ.Syntax.Wf using (NatTy)
open import MAHLOINJ.Valid.HeadRed
open import MAHLOINJ.Valid.Stage
open import MAHLOINJ.Valid.Props using (CodeU ; piU)
open import MAHLOINJ.Valid.Public
open import MAHLOINJ.Adq.View
open import MAHLOINJ.Adq.Base
open import MAHLOINJ.Adq.Sem
open import MAHLOINJ.Adq.Env

module _ {h g : Num} {H : Ctx h} {G : Ctx g} where

  varR : (i : Fin g) -> TmIH H G (Var i) (Var i) (lookup G i)
  varR i {s} {s'} {rho} E a u ea aU eu ua =
    let fv = Fits-var G rho (Env.fits E) i
        a0 = dfst fv ; m = dfst (dsnd fv) ; ea0 = dsnd (dsnd fv)
        a0U = FinMem-a-in-U (lookupEnv i rho) a0 m
        r0 = SR.tm (Env.sr E) i a0 ea0 a0U m
    in adj (EvalRel (lookup G i) rho) (EvalRel-ideal (lookup G i) rho (Env.crho E))
         (\ c ec cU -> diagL {G = H} {T = substExpr s (lookup G i)} {T' = substExpr s' (lookup G i)} c cU
                         (SR.ty (Env.sr E) i c ec cU))
         (lookupEnv i rho) a0 ea0 a0U m r0 u a ea aU (dsnd eu) ua

  funextR : {A : Expr g} {B : Expr (suc g)} {t t' : Expr g} -> IsType G A -> IsType (extend G A) B ->
    TyIH H G A A -> TmIH H (extend G A) (App (wkExpr t) x0) (App (wkExpr t') x0) B -> TmIH H G t t' (PiB A B)
  funextR {A} {B} {t} {t'} iA iB VA Fb {s} {s'} {rho} E Bot u ec cU eu uc = goB u
    where
      goB : (u : FinEl) -> RTm H (substExpr s t) (substExpr s' t') (substExpr s (PiB A B)) u Bot
      goB Bot = tt
      goB UCode = tt
      goB (FunEl _) = tt
      goB (PiCode _ _) = tt
      goB NatCode = tt
      goB ZeroEl = tt
      goB (SucEl _) = tt
      goB (PairEl _ _) = tt
      goB (SigmaCode _ _) = tt
  funextR {A} {B} {t} {t'} iA iB VA Fb {s} {s'} {rho} E (PiCode b f) Bot ec cU eu uc = tt
  funextR {A} {B} {t} {t'} iA iB VA Fb {s} {s'} {rho} E (PiCode b f) (FunEl g) ec cU eu gm = lamM (record
    { A = substExpr s A ; B = Bs ; rT = hrs-refl ; tT = tyeq-refl (isty-Pi iAl iBl) ; iA = iAl ; iB = iBl
    ; app = \ w v sel N N' cv rm ->
        let wb = selKey gm cU sel
            cw = FinMem-coh-u w b wb
            RN = \ a ea aU wa -> adj (EvalRel A rho) (EvalRel-ideal A rho crho) VAd w b eb bU wb rm w a ea aU (LeCode-refl w cw) wa
            E' = envExt E iA (VA E) cv w b eb wb RN
            ef = EvalFun f w
            eBb = famEval (EvalRel A rho) (\ x -> EvalRel B (extendEnv rho x)) (bodyOK B rho crho) f
                    (CodeU.cft cu) (dsnd (dsnd ec)) w cw
            r = Fb E' ef v eBb (efU b f cu wb) (evApp w v sel cw) (selVal gm cU sel)
        in transport3 (\ X Y Z -> RTm H (App X N) (App Y N') Z v ef)
             (consSub-wk s N t) (consSub-wk s' N' t') (subst-consSub s N B) r })
    where
      crho = Env.crho E ; wH = Env.wH E ; cs = Env.cs E ; w1 = CSub.w1 cs
      iAl = sbTy s w1 wH iA
      iBl = sbTy (liftSub s) (liftWS {A = A} w1 iAl) (wf-extend iAl) iB
      Bs = substExpr (liftSub s) B
      cu = piU b f cU
      bU = CodeU.bU cu
      eb = dfst (dsnd ec)
      ctg = cft-from-cf g (finMem-funel-coh g b f gm)
      VAd = \ c ec' cU' -> diagL {G = H} {T = substExpr s A} {T' = substExpr s' A} c cU' (VA E c ec' cU')
      evApp : (w v : FinEl) -> Selection g w v -> Coherent w -> EvalRel (App (wkExpr t) x0) (extendEnv rho w) v
      evApp w v sel cw = go (bot-or v)
        where
          go : Or (Eq v Bot) (NotBot v) -> EvalRel (App (wkExpr t) x0) (extendEnv rho w) v
          go (left refl) = tt
          go (right nbv) =
            let cv = Coherent-Selection-val sel ctg
                es = EvalRel-down t rho crho (FunEl g) (D.FunEl (D.cons (mkSigma w v) D.nil)) eu
                       (sing-coh w v cw cv nbv) (singBelow g sel ctg cw)
            in guard-intro v nbv (mkSigma w (mkSigma (mkSigma cw (LeCode-refl w cw)) (EvalRel-wk t rho w _ es)))

  zeroR : TmIH H G Zero Zero Nat
  zeroR E a Bot ea aU eu ua = tt
  zeroR E NatCode ZeroEl ea aU eu ua =
    tyeq-refl iN , ((hrs-refl , conv-refl (ty-Zero (Env.wH E))) , (hrs-refl , conv-refl (ty-Zero (Env.wH E))))
    where iN = NatTy (Env.wH E)

  sucR : {t t' : Expr g} -> HasType G t Nat -> HasType G t' Nat -> ConvTm G t t' Nat ->
    TmIH H G t t' Nat -> TmIH H G (Suc t) (Suc t') Nat
  sucR dt dt' ct Ft E a Bot ea aU eu ua = tt
  sucR {t} {t'} dt dt' ct Ft {s} {s'} {rho} E NatCode (SucEl v') ea aU eu ua =
    sucM (tyeq-refl (NatTy wH)) (record
      { P = substExpr s t ; P' = substExpr s' t' ; rM = hrs-refl ; rM' = hrs-refl
      ; cM = conv-refl (ty-Suc (sbTm s w1 wH dt)) ; cM' = conv-refl (ty-Suc (sbTm s' w2 wH dt'))
      ; cP = conv-trans (sbCv s w1 wH ct) (fst (fTm s s' cs wH dt'))
      ; pred = Ft E NatCode v' (mkSigma tt (LeCode-refl NatCode tt)) tt ev' (sucNat-to v' ua) })
    where
      wH = Env.wH E ; cs = Env.cs E ; w1 = CSub.w1 cs ; w2 = CSub.w2 cs
      ev = dfst (dsnd (dsnd eu))
      ev' = EvalRel-down t rho (Env.crho E) (dfst (dsnd eu)) v' ev (dfst eu) (dsnd (dsnd (dsnd eu)))
