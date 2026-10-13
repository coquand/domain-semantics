{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Adq/Small.agda  (Tarski port of MAHLOINJ/Adq/Small)
--
-- Case lemmas: variables, function extensionality, zero, successor.
------------------------------------------------------------------------

module MAHLORT.Adq.Small where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; PairEl ; SigmaCode
             ; FinFun ; mkSigma) renaming (fst to dfst ; snd to dsnd)
open import MAHLOINJ.Domain.Kernel
  using (EvalFun ; LeCode ; FinMem ; NotBot ; Coherent ; FinMem-a-in-U ; FinMem-coh-u ; LeCode-refl
        ; finMem-funel-coh ; cft-from-cf ; sucNat-to)
open import MAHLOINJ.Model.Selection using (Selection ; Or ; left ; right ; Coherent-Selection-val)
open import MAHLOINJ.Model.Comb using (bot-or ; guard-intro ; sing-coh)
open import MAHLORT.Model
open import MAHLORT.Model using (EvalRel-wk)
open import MAHLORT.Model using (bodyOK ; Fits-var)
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Subst
open import MAHLORT.Syntax.Funct
open import MAHLORT.Syntax.Wf using (NatTy)
open import MAHLORT.Syntax.CtxConv using (ccTE)
open import MAHLORT.Syntax.Presup using (pCv)
open import MAHLORT.Syntax.SubstLemmas using (subst-ren-gen ; cong3)
open import MAHLORT.Valid.HeadRed
open import MAHLORT.Valid.Stage
open import MAHLORT.Valid.Props using (CodeU ; piU)
open import MAHLORT.Valid.Public
open import MAHLORT.Adq.View
open import MAHLORT.Adq.Base
open import MAHLOINJ.Adq.Sem
open import MAHLORT.Adq.Env

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
    HasType G t (PiB A B) -> HasType G t' (PiB A B) -> TyIH H G A A -> TyIH H (extend G A) B B -> TmIH H (extend G A) (FunB A B t) (FunB A B t') B -> TmIH H G t t' (PiB A B)
  funextR {A} {B} {t} {t'} iA iB dt dt' VA VB Fb {s} {s'} {rho} E Bot u ec cU eu uc = goB u
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
  funextR {A} {B} {t} {t'} iA iB dt dt' VA VB Fb {s} {s'} {rho} E (PiCode b f) Bot ec cU eu uc = tt
  funextR {A} {B} {t} {t'} iA iB dt dt' VA VB Fb {s} {s'} {rho} E (PiCode b f) (FunEl g) ec cU eu gm = lamM (record
    { A = substExpr s A ; B = Bs ; rT = hrs-refl ; tT = tyeq-refl (isty-Pi iAl iBl) ; iA = iAl ; iB = iBl
    ; app = \ w v sel A0 A1 B0 B1 e0 e1 e2 e3 N N' cv rm ->
        let wb = selKey gm cU sel
            cw = FinMem-coh-u w b wb
            RN = \ a ea aU wa -> adj (EvalRel A rho) (EvalRel-ideal A rho crho) VAd w b eb bU wb rm w a ea aU (LeCode-refl w cw) wa
            E' = envExt E iA (VA E) cv w b eb wb RN
            ef = EvalFun f w
            efm = efU b f cu wb
            vm = selVal gm cU sel
            eBb = famEval (EvalRel A rho) (\ x -> EvalRel B (extendEnv rho x)) (bodyOK B rho crho) f
                    (CodeU.cft cu) (dsnd (dsnd ec)) w cw
            r = Fb E' ef v eBb efm (evApp w v sel cw) vm
            r' : RTm H (appB (substExpr s A) Bs (substExpr s t) N) (appB (substExpr s' A) Bs' (substExpr s' t') N')
                   (subst1 Bs N) v ef
            r' = transport3 (\ X Y Z -> RTm H X Y Z v ef) (fbL s N t) (fbL s' N' t') (subst-consSub s N B) r
            vt = transport2 (\ X Y -> RTy H X Y ef) (subst-consSub s N B) (subst-consSub s N B)
                   (diagL {G = H} {T = substExpr (consSub s N) B} {T' = substExpr (consSub s' N') B} ef efm (VB E' ef eBb efm))
            hN = fst (pCv cv) ; hN' = snd (pCv cv)
        in pExpM v ef vm efm (ar _ (ann-app ann-refl) hrs-refl)
             (conv-sym (conv-App iAl iBl e0 e1 (conv-refl hL) (conv-refl hN)))
             vt
             (pExpM' v ef vm efm (ar _ (ann-app ann-refl) hrs-refl)
                (conv-conv (conv-sym (conv-App iAr iBr (tyeq-trans (tyeq-sym eA) e2) (eBr e3) (conv-refl hR) (conv-refl (ty-conv hN' eA))))
                           (tyeq-sym (qB N N' cv)))
                vt r') })
    where
      crho = Env.crho E ; wH = Env.wH E ; cs = Env.cs E ; w1 = CSub.w1 cs ; w2 = CSub.w2 cs
      iAl = sbTy s w1 wH iA
      iAr = sbTy s' w2 wH iA
      eA = fTy s s' cs wH iA
      cU' = liftC cs iAl eA
      iBl = sbTy (liftSub s) (CSub.w1 cU') (wf-extend iAl) iB
      iBr = sbTy (liftSub s') (liftWS {A = A} w2 iAr) (wf-extend iAr) iB
      Bs = substExpr (liftSub s) B ; Bs' = substExpr (liftSub s') B
      eB : TyEq (extend H (substExpr s A)) Bs Bs'
      eB = fTy (liftSub s) (liftSub s') cU' (wf-extend iAl) iB
      eBr : {B1 : Expr (suc h)} -> TyEq (extend H (substExpr s A)) Bs B1 -> TyEq (extend H (substExpr s' A)) Bs' B1
      eBr e3 = ccTE iAr (tyeq-sym eA) (tyeq-trans (tyeq-sym eB) e3)
      qB : (N N' : Expr h) -> ConvTm H N N' (substExpr s A) -> TyEq H (subst1 Bs N) (subst1 Bs' N')
      qB N N' cv = trTE (subst-consSub s N B) (subst-consSub s' N' B)
                     (fTy (consSub s N) (consSub s' N') (consC cs {A = A} (fst (pCv cv)) (ty-conv (snd (pCv cv)) eA) cv eA) wH iB)
      hL : HasType H (substExpr s t) (PiB (substExpr s A) Bs)
      hL = sbTm s w1 wH dt
      hR : HasType H (substExpr s' t') (PiB (substExpr s' A) Bs')
      hR = sbTm s' w2 wH dt'
      cu = piU b f cU
      bU = CodeU.bU cu
      eb = dfst (dsnd ec)
      ctg = cft-from-cf g (finMem-funel-coh g b f gm)
      VAd = \ c ec' cU' -> diagL {G = H} {T = substExpr s A} {T' = substExpr s' A} c cU' (VA E c ec' cU')
      consSub-lift-wk : {k : Num} (r : Sub h k) (N : Expr h) (X : Expr (suc k)) ->
        Eq (substExpr (liftSub (consSub r N)) (renExpr (liftRen wkRen) X)) (substExpr (liftSub r) X)
      consSub-lift-wk r N X = subst-ren-gen (liftSub (consSub r N)) (liftRen wkRen) (liftSub r) e X
        where
          e : (i : Fin (suc _)) -> Eq (liftSub (consSub r N) (liftRen wkRen i)) (liftSub r i)
          e fzero = refl
          e (fsuc j) = refl
      fbL : (r : Sub h _) (N : Expr h) (u : Expr _) ->
        Eq (substExpr (consSub r N) (FunB A B u)) (appB (substExpr r A) (substExpr (liftSub r) B) (substExpr r u) N)
      fbL r N u = cong3 (\ X Y Z -> appB X Y Z N) (consSub-wk r N A) (consSub-lift-wk r N B) (consSub-wk r N u)
      evApp : (w v : FinEl) -> Selection g w v -> Coherent w -> EvalRel (FunB A B t) (extendEnv rho w) v
      evApp w v sel cw = go (bot-or v)
        where
          go : Or (Eq v Bot) (NotBot v) -> EvalRel (FunB A B t) (extendEnv rho w) v
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
