{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Adeq.Driver
--
-- The fundamental theorem (adequacy of the domain model) for T_R with
-- constraint products AND level products, by case analysis on the
-- derivation and STRUCTURAL induction.  Every statement is proved for
-- every level substitution z of the derivation:
--
--   adqTy  : IsType  G A      -> (z : LSub) -> AdqTy     Gz Az
--   adqTyC : IsType  G A      -> (z : LSub) -> AdqConvTy Gz Az
--   adqTm  : HasType G M A    -> (z : LSub) -> Adq       Gz Mz Az
--   adqTmC : HasType G M A    -> (z : LSub) -> AdqConv   Gz Mz Az
--   adqCTy : ConvTy  G A B    -> (z : LSub) -> AdqETy    Gz Az Bz
--   adqCTm : ConvTm  G M N A  -> (z : LSub) -> AdqE1     Gz Mz Nz Az
--
-- (Gz = lsubCtx z G, Mz = lsubE z M).  The level binders ([α]A, <α>u)
-- use the induction hypothesis at EVERY instance  l·z  of the bound
-- level: this is what the combinators of Adeq.Level consume.  The
-- statements at the identity substitution are  adqTm0  etc. below.
--
-- The semantic cases are the combinators of the Adeq.* modules; the
-- driver only transports along the level-substitution equations of
-- RussellLsub.  No postulates, no pragmas.
------------------------------------------------------------------------

open import BCDE4.Levels using (LDecAll)
module BCDE4.Adeq.Driver (D : LDecAll) where

open import BCDE4.Adeq.HeadRed D
open import BCDE4.Adeq.Stmt D
open import BCDE4.Adeq.Pi D using (AdqTy-Pi)
open import BCDE4.Adeq.PiConv D using (AdqConvTy-Pi ; AdqETy-Pi)
open import BCDE4.Adeq.Lam D using (Adq-Lam)
open import BCDE4.Adeq.LamConv D using (AdqConv-Lam)
open import BCDE4.Adeq.LamCong D using (AdqE1-Lam-body ; AdqE1-Lam-Ty ; Adq-right ; AdqConv-right)
open import BCDE4.Adeq.App D using (Adq-App ; AdqConv-App)
open import BCDE4.Adeq.AppCong D using (AdqE1-App-fun ; AdqE1-App-arg)
open import BCDE4.Adeq.Beta D using (AdqE1-beta)
open import BCDE4.Adeq.Eta D using (AdqE1-eta)
open import BCDE4.Adeq.Guard D
open import BCDE4.Adeq.Level D using (AdqTy-LPi ; AdqConvTy-LPi ; AdqETy-LPi ; Adq-LLam ; AdqConv-LLam ; AdqE1-LLam ;
  LvTy ; LvTm ; EqValTy2-snd')
open import BCDE4.Adeq.LevelApp D using (Adq-LApp ; AdqConv-LApp ; AdqE1-LApp-fun ; AdqE1-LApp-beta ; AdqE1-LApp-eta ;
  AdqE1-LApp-lvl)
open import BCDE4.Adeq.Relevel D using (relAdq ; relConv ; relE1 ; relTy ; relConvTy ; relETy)
open import BCDE4.RussellLeq

import BCDE4.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; mkSigma ; fst ; snd ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode)
open import BCDE4.Basic using (Eq ; refl ; Eq-sym ; Eq-transport ; Eq-cong2 ; Eq-cong3 ; Fin ; fzero)
open import BCDE4.Levels using (LSub ; LExpr ; lvar ; liftL ; lconsS ; lsubL ; lsubC ; lidS ; Constr ;
  ceq ; Valid ; v-sym ; equivC-lsub ; equivC-refl ; loop-lsub ; lsubL-id ; valid-ent ; LDec ; valid-lsub)
open import BCDE4.Dom.Kernel using (FinMem ; FinMem-coh-u ; FinMem-a-in-U)
open import BCDE4.Model.Eval D using (EvalRel-coh)
open import BCDE4.Model.Strip using (strip)
open import BCDE4.RussellSyntax using (Expr ; U ; Pi ; Lam ; App ; Var ; Grd ; GLam ; Emp ;
  LPi ; LLam ; LApp ; lsubE ; lsub1 ; lshiftE ; subst1 ; wkExpr ; renExpr ; liftRen ; wkRen ; lsubE-liftL-shift ;
  lsubE-liftL2-shift ; lsubE-id)
open import BCDE4.RussellTyping
open import BCDE4.RussellMeta using (presup-l-ConvTy ; presup-r-ConvTm ; presup-r-ConvTy ; wtE ; isType-U)
open import BCDE4.RussellLsub

------------------------------------------------------------------------
-- Universes
------------------------------------------------------------------------

AdqTy-U : {g : Nat} {G : Ctx g} (l : LExpr) -> AdqTy G (U l)
AdqTy-U l sigma rho crho vs fits wt wfH Bot          ev aU = tt
AdqTy-U l {H = H} sigma rho crho vs fits wt wfH (UCode k) ev aU = valTyU l wfH (S.EqL-sym k (cU H l) (snd ev))
AdqTy-U l sigma rho crho vs fits wt wfH (FunEl _)    () aU
AdqTy-U l sigma rho crho vs fits wt wfH (PiCode _ _) () aU

AdqConvTy-U : {g : Nat} {G : Ctx g} (l : LExpr) -> AdqConvTy G (U l)
AdqConvTy-U {G = G} l sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH a ev aU =
  ValTy2-to-EqValTy2 a (AdqTy-U {G = G} l sigma rho crho vs fits wt wfH a ev aU)

-- U_l = U_l' for levels equal in Γ: the two codes coincide
AdqETy-U-lvl : {g : Nat} {G : Ctx g} {l l' : LExpr} -> Valid (lctx G) l l' -> AdqETy G (U l) (U l')
AdqETy-U-lvl v sigma rho crho vs fits wt wfH Bot          ev aU = tt
AdqETy-U-lvl {l = l} {l' = l'} v {H = H} sigma rho crho vs fits wt wfH (UCode k) ev aU =
  mkSigma (valTyU l wfH e) (valTyU l' wfH (Eq-transport (\ x -> S.EqL x k) eq e))
  where
    e : S.EqL (cU H l) k
    e = S.EqL-sym k (cU H l) (snd ev)
    vH : Valid (lctx H) (lsubL lidS l) (lsubL lidS l')
    vH = Eq-transport (\ x -> Valid (lctx H) x (lsubL lidS l')) (Eq-sym (lsubL-id l))
           (Eq-transport (Valid (lctx H) l) (Eq-sym (lsubL-id l')) (valid-ent (wtE wt) v))
    eq : Eq (cU H l) (cU H l')
    eq = LDec.lcode-sound (D (lctx H)) vH
AdqETy-U-lvl v sigma rho crho vs fits wt wfH (FunEl _)    () aU
AdqETy-U-lvl v sigma rho crho vs fits wt wfH (PiCode _ _) () aU

------------------------------------------------------------------------
-- Substitution-free semantic cases
------------------------------------------------------------------------

Adq-var : {g : Nat} {G : Ctx g} (i : Fin g) -> Adq G (Var i) (lookup G i)
Adq-var i sigma rho crho vs fits wt wfH u hu a evA fm = vs i u (fst hu) (snd hu) a evA fm

AdqConv-var : {g : Nat} {G : Ctx g} (i : Fin g) -> AdqConv G (Var i) (lookup G i)
AdqConv-var i sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH u hu a evA fm =
  vcs i u (fst hu) (snd hu) a evA fm

Adq-conv : {g : Nat} {G : Ctx g} {M A B : Expr g} ->
  ConvTy G A B -> AdqETy G A B -> Adq G M A -> Adq G M B
Adq-conv {A = A} dAB IHab IH sigma rho crho vs fits wt wfH u hu a evB fm =
  let evA = evBwd-Ty dAB rho fits a evB
      ca  = EvalRel-coh (strip A) rho a evA
  in Val2-EqValTy2-fwd u a ca
       (IHab sigma rho crho vs fits wt wfH a evA (FinMem-a-in-U u a fm))
       (IH sigma rho crho vs fits wt wfH u hu a evA fm)

AdqConv-conv : {g : Nat} {G : Ctx g} {M A B : Expr g} ->
  ConvTy G A B -> AdqETy G A B -> AdqConv G M A -> AdqConv G M B
AdqConv-conv {A = A} dAB IHab IH sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH u hu a evB fm =
  let evA = evBwd-Ty dAB rho fits a evB
      ca  = EvalRel-coh (strip A) rho a evA
  in EqVal2-EqValTy2-fwd u a ca
       (IHab sigma rho crho vs fits wt wfH a evA (FinMem-a-in-U u a fm))
       (IH sigma sigma' rho crho vs vs' vcs fits wt wt' wcs wfH u hu a evA fm)

AdqETy-refl : {g : Nat} {G : Ctx g} {A : Expr g} -> AdqTy G A -> AdqETy G A A
AdqETy-refl IH sigma rho crho vs fits wt wfH a evA aU =
  ValTy2-to-EqValTy2 a (IH sigma rho crho vs fits wt wfH a evA aU)

AdqETy-sym : {g : Nat} {G : Ctx g} {A B : Expr g} -> ConvTy G A B -> AdqETy G A B -> AdqETy G B A
AdqETy-sym {A = A} d IH sigma rho crho vs fits wt wfH a evB aU =
  let evA = evBwd-Ty d rho fits a evB
  in EqValTy2-sym a (EvalRel-coh (strip A) rho a evA)
       (IH sigma rho crho vs fits wt wfH a evA aU)

AdqETy-trans : {g : Nat} {G : Ctx g} {A B C : Expr g} ->
  ConvTy G A B -> AdqETy G A B -> AdqETy G B C -> AdqETy G A C
AdqETy-trans {A = A} d1 IH1 IH2 sigma rho crho vs fits wt wfH a evA aU =
  EqValTy2-trans a (EvalRel-coh (strip A) rho a evA)
    (IH1 sigma rho crho vs fits wt wfH a evA aU)
    (IH2 sigma rho crho vs fits wt wfH a (evFwd-Ty d1 rho fits a evA) aU)

AdqE1-refl : {g : Nat} {G : Ctx g} {M A : Expr g} -> Adq G M A -> AdqE1 G M M A
AdqE1-refl IH sigma rho crho vs fits wt wfH u hu a evA fm =
  Val2-to-EqVal2 u a (IH sigma rho crho vs fits wt wfH u hu a evA fm)

AdqE1-sym : {g : Nat} {G : Ctx g} {M N A : Expr g} -> ConvTm G M N A -> AdqE1 G M N A -> AdqE1 G N M A
AdqE1-sym {A = A} d IH sigma rho crho vs fits wt wfH u hu a evA fm =
  let huM = evBwd-Tm d rho fits u hu
  in EqVal2-sym u a (FinMem-coh-u u a fm) (EvalRel-coh (strip A) rho a evA)
       (IH sigma rho crho vs fits wt wfH u huM a evA fm)

AdqE1-trans : {g : Nat} {G : Ctx g} {M N P A : Expr g} ->
  ConvTm G M N A -> AdqE1 G M N A -> AdqE1 G N P A -> AdqE1 G M P A
AdqE1-trans {A = A} d1 IH1 IH2 sigma rho crho vs fits wt wfH u hu a evA fm =
  EqVal2-trans u a (FinMem-coh-u u a fm) (EvalRel-coh (strip A) rho a evA)
    (IH1 sigma rho crho vs fits wt wfH u hu a evA fm)
    (IH2 sigma rho crho vs fits wt wfH u (evFwd-Tm d1 rho fits u hu) a evA fm)

AdqE1-conv : {g : Nat} {G : Ctx g} {M N A B : Expr g} ->
  ConvTy G A B -> AdqETy G A B -> AdqE1 G M N A -> AdqE1 G M N B
AdqE1-conv {A = A} dAB IHab IH sigma rho crho vs fits wt wfH u hu a evB fm =
  let evA = evBwd-Ty dAB rho fits a evB
      ca  = EvalRel-coh (strip A) rho a evA
  in EqVal2-EqValTy2-fwd u a ca
       (IHab sigma rho crho vs fits wt wfH a evA (FinMem-a-in-U u a fm))
       (IH sigma rho crho vs fits wt wfH u hu a evA fm)

------------------------------------------------------------------------
-- Transport along the level-substitution equations
------------------------------------------------------------------------

module _ {n : Nat} where

  sT : (z : LSub) {G : Ctx n} {M A : Expr n} -> HasType G M A -> HasType (lsubCtx z G) (lsubE z M) (lsubE z A)
  sT z {G} = lsubD-HasType z G
  sI : (z : LSub) {G : Ctx n} {A : Expr n} -> IsType G A -> IsType (lsubCtx z G) (lsubE z A)
  sI z {G} = lsubD-IsType z G
  sCy : (z : LSub) {G : Ctx n} {A B : Expr n} -> ConvTy G A B -> ConvTy (lsubCtx z G) (lsubE z A) (lsubE z B)
  sCy z {G} = lsubD-ConvTy z G
  sCm : (z : LSub) {G : Ctx n} {M N A : Expr n} -> ConvTm G M N A ->
    ConvTm (lsubCtx z G) (lsubE z M) (lsubE z N) (lsubE z A)
  sCm z {G} = lsubD-ConvTm z G
  sW : (z : LSub) {G : Ctx n} -> WfCtx G -> WfCtx (lsubCtx z G)
  sW z {G} = lsubD-WfCtx z G

  -- under a constraint
  ctxC : (P : Ctx n -> Set) (z : LSub) (G : Ctx n) (c : Constr) ->
    P (lsubCtx z (addC G c)) -> P (addC (lsubCtx z G) (lsubC z c))
  ctxC P z G c = Eq-transport P (lsubCtx-addC z G c)

  -- under a level binder
  ctxL : (P : Ctx n -> Set) (z : LSub) (G : Ctx n) ->
    P (lsubCtx (liftL z) (addL G)) -> P (addL (lsubCtx z G))
  ctxL P z G = Eq-transport P (lsubCtx-addL z G)

  sIL : (z : LSub) (G : Ctx n) {A : Expr n} -> IsType (addL G) A -> IsType (addL (lsubCtx z G)) (lsubE (liftL z) A)
  sIL z G {A} d = ctxL (\ X -> IsType X (lsubE (liftL z) A)) z G (sI (liftL z) d)
  sTL : (z : LSub) (G : Ctx n) {M A : Expr n} -> HasType (addL G) M A ->
    HasType (addL (lsubCtx z G)) (lsubE (liftL z) M) (lsubE (liftL z) A)
  sTL z G {M} {A} d = ctxL (\ X -> HasType X (lsubE (liftL z) M) (lsubE (liftL z) A)) z G (sT (liftL z) d)
  sCyL : (z : LSub) (G : Ctx n) {A B : Expr n} -> ConvTy (addL G) A B ->
    ConvTy (addL (lsubCtx z G)) (lsubE (liftL z) A) (lsubE (liftL z) B)
  sCyL z G {A} {B} d = ctxL (\ X -> ConvTy X (lsubE (liftL z) A) (lsubE (liftL z) B)) z G (sCy (liftL z) d)
  sCmL : (z : LSub) (G : Ctx n) {M N A : Expr n} -> ConvTm (addL G) M N A ->
    ConvTm (addL (lsubCtx z G)) (lsubE (liftL z) M) (lsubE (liftL z) N) (lsubE (liftL z) A)
  sCmL z G {M} {N} {A} d =
    ctxL (\ X -> ConvTm X (lsubE (liftL z) M) (lsubE (liftL z) N) (lsubE (liftL z) A)) z G (sCm (liftL z) d)

  sIC : (z : LSub) (G : Ctx n) (c : Constr) {A : Expr n} -> IsType (addC G c) A ->
    IsType (addC (lsubCtx z G) (lsubC z c)) (lsubE z A)
  sIC z G c {A} d = ctxC (\ X -> IsType X (lsubE z A)) z G c (sI z d)
  sTC : (z : LSub) (G : Ctx n) (c : Constr) {M A : Expr n} -> HasType (addC G c) M A ->
    HasType (addC (lsubCtx z G) (lsubC z c)) (lsubE z M) (lsubE z A)
  sTC z G c {M} {A} d = ctxC (\ X -> HasType X (lsubE z M) (lsubE z A)) z G c (sT z d)
  sCyC : (z : LSub) (G : Ctx n) (c : Constr) {A B : Expr n} -> ConvTy (addC G c) A B ->
    ConvTy (addC (lsubCtx z G) (lsubC z c)) (lsubE z A) (lsubE z B)
  sCyC z G c {A} {B} d = ctxC (\ X -> ConvTy X (lsubE z A) (lsubE z B)) z G c (sCy z d)
  sCmC : (z : LSub) (G : Ctx n) (c : Constr) {M N A : Expr n} -> ConvTm (addC G c) M N A ->
    ConvTm (addC (lsubCtx z G) (lsubC z c)) (lsubE z M) (lsubE z N) (lsubE z A)
  sCmC z G c {M} {N} {A} d = ctxC (\ X -> ConvTm X (lsubE z M) (lsubE z N) (lsubE z A)) z G c (sCm z d)

  -- the instance l of a level body, from the IH at l·z
  inst1 : (P : Ctx n -> Expr n -> Set) (z : LSub) (G : Ctx n) (A : Expr n) (l : LExpr) ->
    P (lsubCtx (lconsS l z) (addL G)) (lsubE (lconsS l z) A) ->
    P (lsubCtx z G) (lsub1 (lsubE (liftL z) A) l)
  inst1 P z G A l h =
    Eq-transport (P (lsubCtx z G)) (Eq-sym (lsub1-liftL z A l))
      (Eq-transport (\ Y -> P Y (lsubE (lconsS l z) A)) (lsubCtx-inst l z G) h)

  inst2 : (P : Ctx n -> Expr n -> Expr n -> Set) (z : LSub) (G : Ctx n) (A B : Expr n) (l : LExpr) ->
    P (lsubCtx (lconsS l z) (addL G)) (lsubE (lconsS l z) A) (lsubE (lconsS l z) B) ->
    P (lsubCtx z G) (lsub1 (lsubE (liftL z) A) l) (lsub1 (lsubE (liftL z) B) l)
  inst2 P z G A B l h =
    inst1 (\ X Y -> P X Y (lsub1 (lsubE (liftL z) B) l)) z G A l
      (Eq-transport (P (lsubCtx (lconsS l z) (addL G)) (lsubE (lconsS l z) A))
        (Eq-sym (lsub1-liftL z B l)) h)

  inst3 : (P : Ctx n -> Expr n -> Expr n -> Expr n -> Set) (z : LSub) (G : Ctx n) (A B C : Expr n) (l : LExpr) ->
    P (lsubCtx (lconsS l z) (addL G)) (lsubE (lconsS l z) A) (lsubE (lconsS l z) B) (lsubE (lconsS l z) C) ->
    P (lsubCtx z G) (lsub1 (lsubE (liftL z) A) l) (lsub1 (lsubE (liftL z) B) l) (lsub1 (lsubE (liftL z) C) l)
  inst3 P z G A B C l h =
    inst2 (\ X Y W -> P X Y W (lsub1 (lsubE (liftL z) C) l)) z G A B l
      (Eq-transport (P (lsubCtx (lconsS l z) (addL G)) (lsubE (lconsS l z) A) (lsubE (lconsS l z) B))
        (Eq-sym (lsub1-liftL z C l)) h)

-- the eta-expansion commutes with level substitution
eta-lsub : {n : Nat} (z : LSub) (A : Expr n) (B : Expr (suc n)) (c : Expr n) ->
  Eq (App (lsubE z (wkExpr A)) (lsubE z (renExpr (liftRen wkRen) B)) (lsubE z (wkExpr c)) (Var fzero))
     (App (wkExpr (lsubE z A)) (renExpr (liftRen wkRen) (lsubE z B)) (wkExpr (lsubE z c)) (Var fzero))
eta-lsub z A B c =
  Eq-cong3 (\ X Y W -> App X Y W (Var fzero)) (lsubE-wkExpr z A) (lsubE-liftRen-wk z B) (lsubE-wkExpr z c)

------------------------------------------------------------------------
-- Level variation: helpers
------------------------------------------------------------------------

-- the right end of a type conversion is a valid type
AdqTy-right : {g : Nat} {G : Ctx g} {A B : Expr g} -> ConvTy G A B -> AdqETy G A B -> AdqTy G B
AdqTy-right d IH sigma rho crho vs fits wt wfH a evB aU =
  EqValTy2-snd' a (IH sigma rho crho vs fits wt wfH a (evBwd-Ty d rho fits a evB) aU)

tr2ETy : {g : Nat} {G : Ctx g} {A A' B B' : Expr g} -> Eq A A' -> Eq B B' -> AdqETy G A B -> AdqETy G A' B'
tr2ETy refl refl IH = IH

tr3E1 : {g : Nat} {G : Ctx g} {M M' N N' A A' : Expr g} -> Eq M M' -> Eq N N' -> Eq A A' ->
  AdqE1 G M N A -> AdqE1 G M' N' A'
tr3E1 refl refl refl IH = IH

-- statements at Γz, moved to a target related to Γ by z
module RL {g : Nat} {G K : Ctx g} {z : LSub} (s : LSk z G K) (ok : LOK z G K) where
  rA : (M A : Expr g) -> Adq (lsubCtx z G) M A -> Adq K M A
  rA M A = relAdq (lsk-skel s) (lok-cent G K ok) {M = M} {A = A}
  rC : (M A : Expr g) -> AdqConv (lsubCtx z G) M A -> AdqConv K M A
  rC M A = relConv (lsk-skel s) (lok-cent G K ok) {M = M} {A = A}
  rT : (A : Expr g) -> AdqTy (lsubCtx z G) A -> AdqTy K A
  rT A = relTy (lsk-skel s) (lok-cent G K ok) {A = A}
  rCT : (A : Expr g) -> AdqConvTy (lsubCtx z G) A -> AdqConvTy K A
  rCT A = relConvTy (lsk-skel s) (lok-cent G K ok) {A = A}
  rET : (A B : Expr g) -> AdqETy (lsubCtx z G) A B -> AdqETy K A B
  rET A B = relETy (lsk-skel s) (lok-cent G K ok) {A = A} {B = B}

------------------------------------------------------------------------
-- The driver
------------------------------------------------------------------------

mutual

  adqTy : {g : Nat} {G : Ctx g} {A : Expr g} -> IsType G A -> (z : LSub) -> AdqTy (lsubCtx z G) (lsubE z A)
  adqTy (is-Ty-from-U {A = A} {l = l} d) z = Adq-U-to-AdqTy {A = lsubE z A} {l = lsubL z l} (adqTm d z)
  adqTy (is-Pi dA dB) z =
    AdqTy-Pi (sI z dA) (sI z dB) (adqTy dA z) (adqTy dB z) (adqTyC dB z)
  adqTy (is-Grd {G = G} {c = c} {A = A} dG dA) z =
    AdqTy-Grd (sIC z G c dA) (ctxC (\ X -> AdqTy X (lsubE z A)) z G c (adqTy dA z))
  adqTy (is-LPi {G = G} {A = A} dG dA) z =
    AdqTy-LPi (sW z dG) (sIL z G dA)
      (\ l -> inst1 AdqTy z G A l (adqTy dA (lconsS l z)))
      (lvTy dA z (lsk-lsubCtx z G) (lok-lsubCtx z G))

  adqTyC : {g : Nat} {G : Ctx g} {A : Expr g} -> IsType G A -> (z : LSub) -> AdqConvTy (lsubCtx z G) (lsubE z A)
  adqTyC (is-Ty-from-U {A = A} {l = l} d) z = AdqConv-U-to-AdqConvTy {A = lsubE z A} {l = lsubL z l} (adqTmC d z)
  adqTyC (is-Pi dA dB) z = AdqConvTy-Pi (sI z dA) (sI z dB) (adqTyC dA z) (adqTyC dB z)
  adqTyC (is-Grd {G = G} {c = c} {A = A} dG dA) z =
    AdqConvTy-Grd (sIC z G c dA) (ctxC (\ X -> AdqConvTy X (lsubE z A)) z G c (adqTyC dA z))
  adqTyC (is-LPi {G = G} {A = A} dG dA) z =
    AdqConvTy-LPi (sW z dG) (sIL z G dA)
      (\ l -> inst1 AdqConvTy z G A l (adqTyC dA (lconsS l z)))
      (lvTy dA z (lsk-lsubCtx z G) (lok-lsubCtx z G))

  adqTm : {g : Nat} {G : Ctx g} {M A : Expr g} -> HasType G M A -> (z : LSub) ->
    Adq (lsubCtx z G) (lsubE z M) (lsubE z A)
  adqTm (ty-var {G = G} {i = i} _) z =
    Eq-transport (Adq (lsubCtx z G) (Var i)) (lsk-lookup (lsk-lsubCtx z G) i) (Adq-var i)
  adqTm (ty-conv {G = G} {M = M} {A = A} {B = B} d dAB) z =
    Adq-conv {G = lsubCtx z G} {M = lsubE z M} {A = lsubE z A} {B = lsubE z B} (sCy z dAB) (adqCTy dAB z) (adqTm d z)
  adqTm (ty-U {l = l} {m = m} _ _) z = AdqTy-to-Adq-U {T = U (lsubL z l)} {l = lsubL z m} (AdqTy-U (lsubL z l))
  adqTm (ty-cum {A = A} {l = l} {m = m} d _) z =
    AdqTy-to-Adq-U {T = lsubE z A} {l = lsubL z m} (Adq-U-to-AdqTy {A = lsubE z A} {l = lsubL z l} (adqTm d z))
  adqTm (ty-GLam {G = G} {c = c} {A = A} {t = t} dG dA dt) z =
    Adq-GLam (sIC z G c dA) (sTC z G c dt)
      (ctxC (\ X -> AdqTy X (lsubE z A)) z G c (adqTy dA z))
      (ctxC (\ X -> Adq X (lsubE z t) (lsubE z A)) z G c (adqTm dt z))
  adqTm (ty-Emp {l = l} dG) z = AdqTy-to-Adq-U {T = Emp} {l = lsubL z l} AdqTy-Emp
  adqTm (ty-collapse {G = G} {A = A} lp dA) z =
    Adq-collapse {G = lsubCtx z G} {M = Emp} {A = lsubE z A} (lsubCtx-loop z G lp)
  adqTm (ty-Pi {A = A} {B = B} {l = l} dA dB) z =
    AdqTy-to-Adq-U {T = Pi (lsubE z A) (lsubE z B)} {l = lsubL z l}
      (AdqTy-Pi (is-Ty-from-U (sT z dA)) (is-Ty-from-U (sT z dB))
        (Adq-U-to-AdqTy {A = lsubE z A} {l = lsubL z l} (adqTm dA z))
        (Adq-U-to-AdqTy {A = lsubE z B} {l = lsubL z l} (adqTm dB z))
        (AdqConv-U-to-AdqConvTy {A = lsubE z B} {l = lsubL z l} (adqTmC dB z)))
  adqTm (ty-Lam dA dB db) z =
    Adq-Lam (sI z dA) (sI z dB) (sT z db) (conv-Ty-refl (sI z dA)) (conv-Ty-refl (sI z dB)) (adqTy dA z)
      (AdqTy-Pi (sI z dA) (sI z dB) (adqTy dA z) (adqTy dB z) (adqTyC dB z)) (adqTm db z) (adqTmC db z)
  adqTm (ty-App {G = G} {A = A} {B = B} {c = c} {a = a} dA dB dc da) z =
    Eq-transport (Adq (lsubCtx z G) (lsubE z (App A B c a))) (Eq-sym (lsubE-subst1 z B a))
      (Adq-App (sI z dA) (sI z dB) (sT z dc) (sT z da) (adqTm dc z) (adqTm da z) (adqTy dB z))
  adqTm (ty-LLam {G = G} {A = A} {u = u} dG dA du) z =
    Adq-LLam (sW z dG) (sIL z G dA) (sTL z G du)
      (\ l -> inst1 AdqTy z G A l (adqTy dA (lconsS l z)))
      (\ l -> inst2 Adq z G u A l (adqTm du (lconsS l z)))
      (lvTy dA z (lsk-lsubCtx z G) (lok-lsubCtx z G)) (lvTm du z (lsk-lsubCtx z G) (lok-lsubCtx z G))
  adqTm (ty-LApp {G = G} {A = A} {t = t} {l = l} dA dt) z =
    Eq-transport (Adq (lsubCtx z G) (LApp (lsubE (liftL z) A) (lsubE z t) (lsubL z l))) (Eq-sym (lsubE-lsub1 z A l))
      (Adq-LApp (sIL z G dA) (sT z dt) (adqTm dt z)
        (\ l' -> inst1 AdqTy z G A l' (adqTy dA (lconsS l' z))) (lsubL z l))

  adqTmC : {g : Nat} {G : Ctx g} {M A : Expr g} -> HasType G M A -> (z : LSub) ->
    AdqConv (lsubCtx z G) (lsubE z M) (lsubE z A)
  adqTmC (ty-var {G = G} {i = i} _) z =
    Eq-transport (AdqConv (lsubCtx z G) (Var i)) (lsk-lookup (lsk-lsubCtx z G) i) (AdqConv-var i)
  adqTmC (ty-conv {G = G} {M = M} {A = A} {B = B} d dAB) z =
    AdqConv-conv {G = lsubCtx z G} {M = lsubE z M} {A = lsubE z A} {B = lsubE z B} (sCy z dAB) (adqCTy dAB z) (adqTmC d z)
  adqTmC (ty-U {l = l} {m = m} _ _) z =
    AdqConvTy-to-AdqConv-U {T = U (lsubL z l)} {l = lsubL z m} (AdqConvTy-U (lsubL z l))
  adqTmC (ty-cum {A = A} {l = l} {m = m} d _) z =
    AdqConvTy-to-AdqConv-U {T = lsubE z A} {l = lsubL z m}
      (AdqConv-U-to-AdqConvTy {A = lsubE z A} {l = lsubL z l} (adqTmC d z))
  adqTmC (ty-GLam {G = G} {c = c} {A = A} {t = t} dG dA dt) z =
    AdqConv-GLam (sIC z G c dA) (sTC z G c dt)
      (ctxC (\ X -> AdqTy X (lsubE z A)) z G c (adqTy dA z))
      (ctxC (\ X -> AdqConv X (lsubE z t) (lsubE z A)) z G c (adqTmC dt z))
  adqTmC (ty-Emp {l = l} dG) z = AdqConvTy-to-AdqConv-U {T = Emp} {l = lsubL z l} AdqConvTy-Emp
  adqTmC (ty-collapse {G = G} {A = A} lp dA) z =
    AdqConv-collapse {G = lsubCtx z G} {M = Emp} {A = lsubE z A} (lsubCtx-loop z G lp)
  adqTmC (ty-Pi {A = A} {B = B} {l = l} dA dB) z =
    AdqConvTy-to-AdqConv-U {T = Pi (lsubE z A) (lsubE z B)} {l = lsubL z l}
      (AdqConvTy-Pi (is-Ty-from-U (sT z dA)) (is-Ty-from-U (sT z dB))
        (AdqConv-U-to-AdqConvTy {A = lsubE z A} {l = lsubL z l} (adqTmC dA z))
        (AdqConv-U-to-AdqConvTy {A = lsubE z B} {l = lsubL z l} (adqTmC dB z)))
  adqTmC (ty-Lam dA dB db) z =
    AdqConv-Lam (sI z dA) (sI z dB) (sT z db) (adqTy dA z) (adqTyC dA z)
      (AdqTy-Pi (sI z dA) (sI z dB) (adqTy dA z) (adqTy dB z) (adqTyC dB z))
      (AdqConvTy-Pi (sI z dA) (sI z dB) (adqTyC dA z) (adqTyC dB z))
      (adqTm db z) (adqTmC db z)
  adqTmC (ty-App {G = G} {A = A} {B = B} {c = c} {a = a} dA dB dc da) z =
    Eq-transport (AdqConv (lsubCtx z G) (lsubE z (App A B c a))) (Eq-sym (lsubE-subst1 z B a))
      (AdqConv-App (sI z dA) (sI z dB) (sT z dc) (sT z da) (adqTm da z) (adqTy dB z) (adqTmC dc z) (adqTmC da z))
  adqTmC (ty-LLam {G = G} {A = A} {u = u} dG dA du) z =
    AdqConv-LLam (sW z dG) (sIL z G dA) (sTL z G du)
      (\ l -> inst1 AdqConvTy z G A l (adqTyC dA (lconsS l z)))
      (\ l -> inst2 AdqConv z G u A l (adqTmC du (lconsS l z)))
      (lvTy dA z (lsk-lsubCtx z G) (lok-lsubCtx z G)) (lvTm du z (lsk-lsubCtx z G) (lok-lsubCtx z G))
  adqTmC (ty-LApp {G = G} {A = A} {t = t} {l = l} dA dt) z =
    Eq-transport (AdqConv (lsubCtx z G) (LApp (lsubE (liftL z) A) (lsubE z t) (lsubL z l))) (Eq-sym (lsubE-lsub1 z A l))
      (AdqConv-LApp (sIL z G dA) (sT z dt) (adqTmC dt z)
        (\ l' -> inst1 AdqTy z G A l' (adqTy dA (lconsS l' z))) (lsubL z l))

  adqCTy : {g : Nat} {G : Ctx g} {A B : Expr g} -> ConvTy G A B -> (z : LSub) ->
    AdqETy (lsubCtx z G) (lsubE z A) (lsubE z B)
  adqCTy (conv-Ty-refl {G = G} {A = A} dA) z = AdqETy-refl {G = lsubCtx z G} {A = lsubE z A} (adqTy dA z)
  adqCTy (conv-Ty-sym {G = G} {A = A} {B = B} d) z = AdqETy-sym {G = lsubCtx z G} {A = lsubE z A} {B = lsubE z B} (sCy z d) (adqCTy d z)
  adqCTy (conv-Ty-trans {G = G} {A = A} {B = B} {C = C} d1 d2) z =
    AdqETy-trans {G = lsubCtx z G} {A = lsubE z A} {B = lsubE z B} {C = lsubE z C} (sCy z d1) (adqCTy d1 z) (adqCTy d2 z)
  adqCTy (conv-Ty-Pi dA dB cA cB) z =
    AdqETy-Pi (sI z dA) (sI z dB) (sCy z cA) (sCy z cB)
      (adqTyC dA z) (adqTyC dB z) (adqCTy cA z) (adqCTy cB z)
  adqCTy (conv-Ty-from-U {A = A} {B = B} {l = l} d) z =
    AdqE1-U-to-AdqETy {A = lsubE z A} {B = lsubE z B} {l = lsubL z l} (adqCTm d z)
  adqCTy (conv-Ty-Grd {G = G} {c = c} {A = A} {B = B} dG dA dAB) z =
    AdqETy-Grd (sIC z G c dA) (sCyC z G c dAB)
      (ctxC (\ X -> AdqETy X (lsubE z A) (lsubE z B)) z G c (adqCTy dAB z))
  adqCTy (conv-Ty-Grd-beta {G = G} {c = c} {A = A} v dA) z =
    AdqETy-Grd-beta (lsubCtx-valid z G c v) (sI z dA) (adqTy dA z)
  adqCTy (conv-Ty-Grd-equiv {G = G} {c = c} {c' = c'} {A = A} dG q dA) z =
    AdqETy-Grd-equiv (equivC-lsub z (lok-lsubCtx z G) q) (sIC z G c dA)
      (ctxC (\ X -> AdqTy X (lsubE z A)) z G c (adqTy dA z))
  adqCTy (conv-Ty-LPi {G = G} {A = A} {B = B} dG dA dAB) z =
    AdqETy-LPi (sW z dG) (sIL z G dA) (sCyL z G dAB)
      (\ l -> inst2 AdqETy z G A B l (adqCTy dAB (lconsS l z)))
      (lvTy dA z (lsk-lsubCtx z G) (lok-lsubCtx z G))
  adqCTy (conv-Ty-collapse {G = G} {A = A} lp dA) z =
    AdqETy-collapse {G = lsubCtx z G} {A = lsubE z A} {B = Emp} (lsubCtx-loop z G lp)

  adqCTm : {g : Nat} {G : Ctx g} {M N A : Expr g} -> ConvTm G M N A -> (z : LSub) ->
    AdqE1 (lsubCtx z G) (lsubE z M) (lsubE z N) (lsubE z A)
  adqCTm (conv-refl {G = G} {M = M} {A = A} d) z = AdqE1-refl {G = lsubCtx z G} {M = lsubE z M} {A = lsubE z A} (adqTm d z)
  adqCTm (conv-sym {G = G} {M = M} {N = N} {A = A} d) z =
    AdqE1-sym {G = lsubCtx z G} {M = lsubE z M} {N = lsubE z N} {A = lsubE z A} (sCm z d) (adqCTm d z)
  adqCTm (conv-trans {G = G} {M = M} {N = N} {P = P} {A = A} d1 d2) z =
    AdqE1-trans {G = lsubCtx z G} {M = lsubE z M} {N = lsubE z N} {P = lsubE z P} {A = lsubE z A} (sCm z d1) (adqCTm d1 z) (adqCTm d2 z)
  adqCTm (conv-conv {G = G} {M = M} {N = N} {A = A} {B = B} d dAB) z =
    AdqE1-conv {G = lsubCtx z G} {M = lsubE z M} {N = lsubE z N} {A = lsubE z A} {B = lsubE z B} (sCy z dAB) (adqCTy dAB z) (adqCTm d z)
  adqCTm (conv-cong-Pi {A = A} {A' = A'} {B = B} {B' = B'} {l = l} dA dB cA cB) z =
    AdqETy-to-AdqE1-U {T = Pi (lsubE z A) (lsubE z B)} {T' = Pi (lsubE z A') (lsubE z B')} {l = lsubL z l}
      (AdqETy-Pi (is-Ty-from-U (sT z dA)) (is-Ty-from-U (sT z dB))
        (conv-Ty-from-U (sCm z cA)) (conv-Ty-from-U (sCm z cB))
        (AdqConv-U-to-AdqConvTy {A = lsubE z A} {l = lsubL z l} (adqTmC dA z))
        (AdqConv-U-to-AdqConvTy {A = lsubE z B} {l = lsubL z l} (adqTmC dB z))
        (AdqE1-U-to-AdqETy {A = lsubE z A} {B = lsubE z A'} {l = lsubL z l} (adqCTm cA z))
        (AdqE1-U-to-AdqETy {A = lsubE z B} {B = lsubE z B'} {l = lsubL z l} (adqCTm cB z)))
  adqCTm (conv-cum {A = A} {B = B} {l = l} {m = m} d _) z =
    AdqETy-to-AdqE1-U {T = lsubE z A} {T' = lsubE z B} {l = lsubL z m}
      (AdqE1-U-to-AdqETy {A = lsubE z A} {B = lsubE z B} {l = lsubL z l} (adqCTm d z))
  adqCTm (conv-U-lvl {G = G} {l = l} {l' = l'} {m = m} dG v _) z =
    AdqETy-to-AdqE1-U {T = U (lsubL z l)} {T' = U (lsubL z l')} {l = lsubL z m}
      (AdqETy-U-lvl (lsubCtx-valid z G (ceq l l') v))
  adqCTm (conv-cong-Lam-body dA dB db0 db) z =
    AdqE1-Lam-body (sI z dA) (sI z dB) (sT z db0) (sCm z db) (adqTy dA z)
      (AdqTy-Pi (sI z dA) (sI z dB) (adqTy dA z) (adqTy dB z) (adqTyC dB z)) (adqTyC dB z)
      (adqTm db0 z) (adqTmC db0 z) (adqCTm db z)
  adqCTm (conv-cong-Lam-Ty dA dB cA cB db) z =
    AdqE1-Lam-Ty (sI z dA) (sI z dB) (sCy z cA) (sCy z cB) (sT z db) (adqTy dA z)
      (AdqTy-Pi (sI z dA) (sI z dB) (adqTy dA z) (adqTy dB z) (adqTyC dB z)) (adqTm db z) (adqTmC db z)
  adqCTm (conv-cong-App-fun {G = G} {A = A} {B = B} {c = c} {c' = c'} {a = a} dA dB dc da) z =
    Eq-transport (AdqE1 (lsubCtx z G) (lsubE z (App A B c a)) (lsubE z (App A B c' a)))
      (Eq-sym (lsubE-subst1 z B a))
      (AdqE1-App-fun (sI z dA) (sI z dB) (sCm z dc) (sT z da) (adqCTm dc z) (adqTm da z) (adqTy dB z))
  adqCTm (conv-cong-App-arg {G = G} {A = A} {B = B} {c = c} {a = a} {a' = a'} dA dB dc da _) z =
    Eq-transport (AdqE1 (lsubCtx z G) (lsubE z (App A B c a)) (lsubE z (App A B c a')))
      (Eq-sym (lsubE-subst1 z B a))
      (AdqE1-App-arg (sI z dA) (sI z dB) (sT z dc) (sCm z da)
        (Ann-refl (sI z dA) (sI z dB)) (Ann-refl (sI z dA) (sI z dB))
        (adqTm dc z) (adqTy dB z) (adqCTm da z))
  adqCTm (conv-cong-App-Ty {G = G} {A = A} {A' = A'} {B = B} {B' = B'} {c = c} {a = a} dA dB cA cB dc da) z =
    Eq-transport (AdqE1 (lsubCtx z G) (lsubE z (App A B c a)) (lsubE z (App A' B' c a)))
      (Eq-sym (lsubE-subst1 z B a))
      (AdqE1-App-arg (sI z dA) (sI z dB) (sT z dc) (conv-refl (sT z da))
        (Ann-refl (sI z dA) (sI z dB)) (mkAnn (conv-Ty-sym (sCy z cA)) (conv-Ty-sym (sCy z cB)))
        (adqTm dc z) (AdqETy-to-AdqTy {A = lsubE z B} {B = lsubE z B'} (adqCTy cB z))
        (AdqE1-refl {G = lsubCtx z G} {M = lsubE z a} {A = lsubE z A} (adqTm da z)))
  adqCTm (conv-beta {G = G} {A = A} {B = B} {b = b} {a = a} dA dB db da) z =
    Eq-transport (\ X -> AdqE1 (lsubCtx z G) (lsubE z (App A B (Lam A B b) a)) X (lsubE z (subst1 B a)))
      (Eq-sym (lsubE-subst1 z b a))
      (Eq-transport (AdqE1 (lsubCtx z G) (lsubE z (App A B (Lam A B b) a)) (subst1 (lsubE z b) (lsubE z a)))
        (Eq-sym (lsubE-subst1 z B a))
        (AdqE1-beta (sI z dA) (sI z dB) (sT z db) (sT z da) (adqTm db z) (adqTm da z)))
  adqCTm (conv-eta {G = G} {A = A} {B = B} {c = c} dA dB dc) z =
    Eq-transport (\ X -> AdqE1 (lsubCtx z G) (lsubE z c) (Lam (lsubE z A) (lsubE z B) X) (lsubE z (Pi A B)))
      (Eq-sym (eta-lsub z A B c))
      (AdqE1-eta (sI z dA) (sI z dB) (sT z dc) (adqTm dc z))
  adqCTm (conv-cong-GLam {G = G} {c = c} {A = A} {t = t} {t' = t'} dG dA dt dtt) z =
    AdqE1-GLam (sIC z G c dA) (sTC z G c dt) (sCmC z G c dtt)
      (ctxC (\ X -> AdqTy X (lsubE z A)) z G c (adqTy dA z))
      (ctxC (\ X -> AdqE1 X (lsubE z t) (lsubE z t') (lsubE z A)) z G c (adqCTm dtt z))
  adqCTm (conv-GLam-eta {G = G} {c = c} {A = A} {t = t} dG dA dt dt') z =
    AdqE1-GLam-eta (sIC z G c dA) (sTC z G c dt')
      (ctxC (\ X -> AdqTy X (lsubE z A)) z G c (adqTy dA z))
      (adqTm dt z)
  adqCTm (conv-GLam-beta {G = G} {c = c} v dA dt) z =
    AdqE1-GLam-beta (lsubCtx-valid z G c v) (sI z dA) (sT z dt) (adqTm dt z)
  adqCTm (conv-cong-GLam-Ty {G = G} {c = c} {A = A} {A' = A'} {t = t} dG dA cAA' dt) z =
    AdqE1-GLam-equiv (equivC-refl (lsubC z c)) (sIC z G c dA) (sCyC z G c cAA') (sTC z G c dt)
      (ctxC (\ X -> AdqTy X (lsubE z A)) z G c (adqTy dA z))
      (ctxC (\ X -> Adq X (lsubE z t) (lsubE z A)) z G c (adqTm dt z))
  adqCTm (conv-cong-LLam-Ty {G = G} {A = A} {A' = A'} {u = u} dG dA cAA' du) z =
    AdqE1-LLam (sW z dG) (sIL z G dA) (sCyL z G cAA') (sTL z G du) (conv-refl (sTL z G du))
      (\ l -> inst1 AdqTy z G A l (adqTy dA (lconsS l z)))
      (\ l -> AdqE1-refl {G = lsubCtx z G} {M = lsub1 (lsubE (liftL z) u) l} {A = lsub1 (lsubE (liftL z) A) l}
                 (inst2 Adq z G u A l (adqTm du (lconsS l z))))
      (lvTy dA z (lsk-lsubCtx z G) (lok-lsubCtx z G)) (lvTm du z (lsk-lsubCtx z G) (lok-lsubCtx z G))
  adqCTm (conv-cong-LApp-Ty {G = G} {A = A} {A' = A'} {t = t} {l = l} dA cAA' dt) z =
    Eq-transport (AdqE1 (lsubCtx z G) (LApp (lsubE (liftL z) A) (lsubE z t) (lsubL z l))
                    (LApp (lsubE (liftL z) A') (lsubE z t) (lsubL z l)))
      (Eq-sym (lsubE-lsub1 z A l))
      (AdqE1-LApp-fun (sIL z G dA) (sCyL z G cAA') (conv-refl (sT z dt))
        (AdqE1-refl {G = lsubCtx z G} {M = lsubE z t} {A = lsubE z (LPi A)} (adqTm dt z))
        (\ l' -> inst1 AdqTy z G A l' (adqTy dA (lconsS l' z))) (lsubL z l))
  adqCTm (conv-cong-LLam {G = G} {A = A} {u = u} {u' = u'} dG dA du duu) z =
    AdqE1-LLam (sW z dG) (sIL z G dA) (conv-Ty-refl (sIL z G dA)) (sTL z G du) (sCmL z G duu)
      (\ l -> inst1 AdqTy z G A l (adqTy dA (lconsS l z)))
      (\ l -> inst3 AdqE1 z G u u' A l (adqCTm duu (lconsS l z)))
      (lvTy dA z (lsk-lsubCtx z G) (lok-lsubCtx z G)) (lvTm du z (lsk-lsubCtx z G) (lok-lsubCtx z G))
  adqCTm (conv-cong-LApp-fun {G = G} {A = A} {t = t} {t' = t'} {l = l} dA dtt) z =
    Eq-transport (AdqE1 (lsubCtx z G) (LApp (lsubE (liftL z) A) (lsubE z t) (lsubL z l))
                    (LApp (lsubE (liftL z) A) (lsubE z t') (lsubL z l)))
      (Eq-sym (lsubE-lsub1 z A l))
      (AdqE1-LApp-fun (sIL z G dA) (conv-Ty-refl (sIL z G dA)) (sCm z dtt) (adqCTm dtt z)
        (\ l' -> inst1 AdqTy z G A l' (adqTy dA (lconsS l' z))) (lsubL z l))
  adqCTm (conv-LApp-beta {G = G} {A = A} {u = u} {l = l} dA du) z =
    Eq-transport (\ X -> AdqE1 (lsubCtx z G) (lsubE z (LApp A (LLam A u) l)) X (lsubE z (lsub1 A l)))
      (Eq-sym (lsubE-lsub1 z u l))
      (Eq-transport (AdqE1 (lsubCtx z G) (lsubE z (LApp A (LLam A u) l)) (lsub1 (lsubE (liftL z) u) (lsubL z l)))
        (Eq-sym (lsubE-lsub1 z A l))
        (AdqE1-LApp-beta (sIL z G dA) (sTL z G du) (lsubL z l)
          (inst2 Adq z G u A (lsubL z l) (adqTm du (lconsS (lsubL z l) z)))))
  adqCTm (conv-LApp-eta {G = G} {A = A} {t = t} dA dt) z =
    Eq-transport (\ X -> AdqE1 (lsubCtx z G) (lsubE z t) X (lsubE z (LPi A)))
      (Eq-cong2 (\ Y X -> LLam (lsubE (liftL z) A) (LApp Y X (lvar zero)))
         (Eq-sym (lsubE-liftL2-shift z A)) (Eq-sym (lsubE-liftL-shift z t)))
      (AdqE1-LApp-eta (sIL z G dA) (sT z dt) (adqTm dt z))
  adqCTm (conv-cong-LApp-lvl {G = G} {A = A} {t = t} {l = l} {l' = l'} dA dt v _) z =
    Eq-transport (AdqE1 (lsubCtx z G) (LApp (lsubE (liftL z) A) (lsubE z t) (lsubL z l))
                    (LApp (lsubE (liftL z) A) (lsubE z t) (lsubL z l')))
      (Eq-sym (lsubE-lsub1 z A l))
      (AdqE1-LApp-lvl (sIL z G dA) (sT z dt) (lsubCtx-valid z G (ceq l l') v) (adqTm dt z)
        (\ l'' -> inst1 AdqTy z G A l'' (adqTy dA (lconsS l'' z))))
  adqCTm (conv-GLam-equiv {G = G} {c = c} {c' = c'} {A = A} {t = t} dG q dA dt) z =
    AdqE1-GLam-equiv (equivC-lsub z (lok-lsubCtx z G) q) (sIC z G c dA) (conv-Ty-refl (sIC z G c dA)) (sTC z G c dt)
      (ctxC (\ X -> AdqTy X (lsubE z A)) z G c (adqTy dA z))
      (ctxC (\ X -> Adq X (lsubE z t) (lsubE z A)) z G c (adqTm dt z))
  adqCTm (conv-collapse {G = G} {t = t} {A = A} lp dA dt) z =
    AdqE1-collapse {G = lsubCtx z G} {M = lsubE z t} {N = Emp} {A = lsubE z A} (lsubCtx-loop z G lp)

  ----------------------------------------------------------------------
  -- Level variation: z, z' pointwise equal in the target K related to Γ
  -- by z give related instances (the semantic side of BCDE4.RussellLeq)
  ----------------------------------------------------------------------

  -- the level-variation hypotheses of a level body
  lvTy : {g : Nat} {G : Ctx g} {A : Expr g} -> IsType (addL G) A -> (z : LSub) {K : Ctx g} ->
    LSk z G K -> LOK z G K -> LvTy K (lsubE (liftL z) A)
  lvTy {G = G} {A = A} dA z {K} s ok l l' =
    tr2ETy (Eq-sym (lsub1-liftL z A l)) (Eq-sym (lsub1-liftL z A l'))
      (adqLvTy dA (lconsS l z) (lconsS l' z) (lsk-addCr (ceq l l') (lsk-cons l s))
         (lok-addCr (addL G) K (ceq l l') (lok-cons G K l ok)) (leqS-hyp K l l'))

  -- the same, at the same instance l under z and z'
  lvSameTy : {g : Nat} {G : Ctx g} {A : Expr g} -> IsType (addL G) A -> (z z' : LSub) {K : Ctx g} ->
    LSk z G K -> LOK z G K -> LEqS (lctx K) z z' -> (l : LExpr) ->
    AdqETy K (lsub1 (lsubE (liftL z) A) l) (lsub1 (lsubE (liftL z') A) l)
  lvSameTy {G = G} {A = A} dA z z' {K} s ok q l =
    tr2ETy (Eq-sym (lsub1-liftL z A l)) (Eq-sym (lsub1-liftL z' A l))
      (adqLvTy dA (lconsS l z) (lconsS l z') (lsk-cons l s) (lok-cons G K l ok) (leqS-same l q))

  lvTm : {g : Nat} {G : Ctx g} {A u : Expr g} -> HasType (addL G) u A -> (z : LSub) {K : Ctx g} ->
    LSk z G K -> LOK z G K -> LvTm K (lsubE (liftL z) u) (lsubE (liftL z) A)
  lvTm {G = G} {A = A} {u = u} du z {K} s ok l l' =
    tr3E1 (Eq-sym (lsub1-liftL z u l)) (Eq-sym (lsub1-liftL z u l')) (Eq-sym (lsub1-liftL z A l))
      (adqLv du (lconsS l z) (lconsS l' z) (lsk-addCr (ceq l l') (lsk-cons l s))
         (lok-addCr (addL G) K (ceq l l') (lok-cons G K l ok)) (leqS-hyp K l l'))

  -- the IH at the same instance l of a level body under z and z'
  lvSame : {g : Nat} {G : Ctx g} {A u : Expr g} -> HasType (addL G) u A -> (z z' : LSub) {K : Ctx g} ->
    LSk z G K -> LOK z G K -> LEqS (lctx K) z z' -> (l : LExpr) ->
    AdqE1 K (lsub1 (lsubE (liftL z) u) l) (lsub1 (lsubE (liftL z') u) l) (lsub1 (lsubE (liftL z) A) l)
  lvSame {G = G} {A = A} {u = u} du z z' {K} s ok q l =
    tr3E1 (Eq-sym (lsub1-liftL z u l)) (Eq-sym (lsub1-liftL z' u l)) (Eq-sym (lsub1-liftL z A l))
      (adqLv du (lconsS l z) (lconsS l z') (lsk-cons l s) (lok-cons G K l ok) (leqS-same l q))

  adqLvTy : {g : Nat} {G : Ctx g} {A : Expr g} -> IsType G A -> (z z' : LSub) {K : Ctx g} ->
    LSk z G K -> LOK z G K -> LEqS (lctx K) z z' -> AdqETy K (lsubE z A) (lsubE z' A)
  adqLvTy (is-Ty-from-U {A = A} {l = l} d) z z' s ok q =
    AdqE1-U-to-AdqETy {A = lsubE z A} {B = lsubE z' A} {l = lsubL z l} (adqLv d z z' s ok q)
  adqLvTy (is-Pi {A = A} {B = B} dA dB) z z' {K} s ok q =
    let s' = lsk-extend s refl
    in AdqETy-Pi (lsub-IsType s ok dA) (lsub-IsType s' ok dB) (leq-IsType s ok q dA) (leq-IsType s' ok q dB)
         (RL.rCT s ok (lsubE z A) (adqTyC dA z)) (RL.rCT s' ok (lsubE z B) (adqTyC dB z))
         (adqLvTy dA z z' s ok q) (adqLvTy dB z z' s' ok q)
  adqLvTy (is-Grd {G = G} {c = c} {A = A} dG dA) z z' {K} s ok q =
    let s'  = lsk-addC c s
        ok' = lok-addC G K c ok
        q'  = leqS-addC {T = lctx K} K (lsubC z c) q
        sA  = lsub-IsType s' ok' dA
        cA  = leq-IsType s' ok' q' dA
        EA  = adqLvTy dA z z' s' ok' q'
        e1  = AdqETy-Grd sA cA EA
        e2  = AdqETy-Grd-equiv (equivC-leq q c) (presup-r-ConvTy cA) (AdqTy-right cA EA)
    in AdqETy-trans {G = K} {A = Grd (lsubC z c) (lsubE z A)} {B = Grd (lsubC z c) (lsubE z' A)}
         {C = Grd (lsubC z' c) (lsubE z' A)}
         (conv-Ty-Grd (lsub-WfCtx s ok dG) sA cA) e1 e2
  adqLvTy (is-LPi {G = G} {A = A} dG dA) z z' {K} s ok q =
    let sL  = lsk-addL s
        okL = lok-addL G K ok
        qL  = leqS-addL K q
    in AdqETy-LPi (lsub-WfCtx s ok dG) (lsub-IsType sL okL dA) (leq-IsType sL okL qL dA)
         (lvSameTy dA z z' s ok q) (lvTy dA z s ok)

  adqLv : {g : Nat} {G : Ctx g} {M A : Expr g} -> HasType G M A -> (z z' : LSub) {K : Ctx g} ->
    LSk z G K -> LOK z G K -> LEqS (lctx K) z z' -> AdqE1 K (lsubE z M) (lsubE z' M) (lsubE z A)
  adqLv d@(ty-var {G = G} {i = i} _) z z' {K} s ok q =
    AdqE1-refl {G = K} {M = Var i} {A = lsubE z (lookup G i)} (RL.rA s ok (Var i) (lsubE z (lookup G i)) (adqTm d z))
  adqLv (ty-conv {M = M} {A = A} {B = B} dM dAB) z z' {K} s ok q =
    AdqE1-conv {G = K} {M = lsubE z M} {N = lsubE z' M} {A = lsubE z A} {B = lsubE z B}
      (lsub-ConvTy s ok dAB) (RL.rET s ok (lsubE z A) (lsubE z B) (adqCTy dAB z)) (adqLv dM z z' s ok q)
  adqLv (ty-U {l = l} {m = m} _ _) z z' {K} s ok q =
    AdqETy-to-AdqE1-U {T = U (lsubL z l)} {T' = U (lsubL z' l)} {l = lsubL z m} (AdqETy-U-lvl (leqL q l))
  adqLv (ty-cum {A = A} {l = l} {m = m} d _) z z' {K} s ok q =
    AdqETy-to-AdqE1-U {T = lsubE z A} {T' = lsubE z' A} {l = lsubL z m}
      (AdqE1-U-to-AdqETy {A = lsubE z A} {B = lsubE z' A} {l = lsubL z l} (adqLv d z z' s ok q))
  adqLv d@(ty-Emp {l = l} _) z z' {K} s ok q =
    AdqE1-refl {G = K} {M = Emp} {A = U (lsubL z l)} (RL.rA s ok Emp (U (lsubL z l)) (adqTm d z))
  adqLv (ty-collapse {A = A} lp dA) z z' {K} s ok q =
    AdqE1-collapse {G = K} {M = Emp} {N = Emp} {A = lsubE z A} (loop-lsub z ok lp)
  adqLv (ty-Pi {A = A} {B = B} {l = l} dA dB) z z' {K} s ok q =
    let s'  = lsk-extend s refl
        sA  = lsub-HasType s ok dA
        sB  = lsub-HasType s' ok dB
        cA  = leq-HasType s ok q dA
        cB  = leq-HasType s' ok q dB
        lz  = lsubL z l
    in AdqETy-to-AdqE1-U {T = Pi (lsubE z A) (lsubE z B)} {T' = Pi (lsubE z' A) (lsubE z' B)} {l = lz}
         (AdqETy-Pi (is-Ty-from-U sA) (is-Ty-from-U sB) (conv-Ty-from-U cA) (conv-Ty-from-U cB)
           (RL.rCT s ok (lsubE z A) (AdqConv-U-to-AdqConvTy {A = lsubE z A} {l = lz} (adqTmC dA z)))
           (RL.rCT s' ok (lsubE z B) (AdqConv-U-to-AdqConvTy {A = lsubE z B} {l = lz} (adqTmC dB z)))
           (AdqE1-U-to-AdqETy {A = lsubE z A} {B = lsubE z' A} {l = lz} (adqLv dA z z' s ok q))
           (AdqE1-U-to-AdqETy {A = lsubE z B} {B = lsubE z' B} {l = lz} (adqLv dB z z' s' ok q)))
  adqLv (ty-Lam {A = A} {B = B} {b = b} dA dB db) z z' {K} s ok q =
    let s'   = lsk-extend s refl
        sA   = lsub-IsType s ok dA
        sB   = lsub-IsType s' ok dB
        sb   = lsub-HasType s' ok db
        cb   = leq-HasType s' ok q db
        cA   = leq-IsType s ok q dA
        cB   = leq-IsType s' ok q dB
        IHA  = RL.rT s ok (lsubE z A) (adqTy dA z)
        IHcB = RL.rCT s' ok (lsubE z B) (adqTyC dB z)
        IHPi = AdqTy-Pi sA sB IHA (RL.rT s' ok (lsubE z B) (adqTy dB z)) IHcB
        IHcb = RL.rC s' ok (lsubE z b) (lsubE z B) (adqTmC db z)
        Eb   = adqLv db z z' s' ok q
        st1  = AdqE1-Lam-body sA sB sb cb IHA IHPi IHcB (RL.rA s' ok (lsubE z b) (lsubE z B) (adqTm db z)) IHcb Eb
        st2  = AdqE1-Lam-Ty sA sB cA cB (presup-r-ConvTm cb) IHA IHPi
                 (Adq-right cb Eb) (AdqConv-right cb Eb IHcb IHcB)
    in AdqE1-trans {G = K} {M = Lam (lsubE z A) (lsubE z B) (lsubE z b)}
         {N = Lam (lsubE z A) (lsubE z B) (lsubE z' b)} {P = Lam (lsubE z' A) (lsubE z' B) (lsubE z' b)}
         {A = Pi (lsubE z A) (lsubE z B)}
         (conv-cong-Lam-body sA sB sb cb) st1 st2
  adqLv (ty-App {A = A} {B = B} {c = c} {a = a} dA dB dc da) z z' {K} s ok q =
    let s'  = lsk-extend s refl
        sA  = lsub-IsType s ok dA
        sB  = lsub-IsType s' ok dB
        sa  = lsub-HasType s ok da
        cc  = leq-HasType s ok q dc
        ca  = leq-HasType s ok q da
        cA  = leq-IsType s ok q dA
        cB  = leq-IsType s' ok q dB
        Ec  = adqLv dc z z' s ok q
        IHB = RL.rT s' ok (lsubE z B) (adqTy dB z)
        st1 = AdqE1-App-fun sA sB cc sa Ec (RL.rA s ok (lsubE z a) (lsubE z A) (adqTm da z)) IHB
        st2 = AdqE1-App-arg sA sB (presup-r-ConvTm cc) ca (Ann-refl sA sB)
                (mkAnn (conv-Ty-sym cA) (conv-Ty-sym cB)) (Adq-right cc Ec) IHB (adqLv da z z' s ok q)
    in Eq-transport (AdqE1 K (lsubE z (App A B c a)) (lsubE z' (App A B c a))) (Eq-sym (lsubE-subst1 z B a))
         (AdqE1-trans {G = K} {M = App (lsubE z A) (lsubE z B) (lsubE z c) (lsubE z a)}
            {N = App (lsubE z A) (lsubE z B) (lsubE z' c) (lsubE z a)}
            {P = App (lsubE z' A) (lsubE z' B) (lsubE z' c) (lsubE z' a)}
            {A = subst1 (lsubE z B) (lsubE z a)}
            (conv-cong-App-fun sA sB cc sa) st1 st2)
  adqLv (ty-GLam {G = G} {c = c} {A = A} {t = t} dG dA dt) z z' {K} s ok q =
    let s'  = lsk-addC c s
        ok' = lok-addC G K c ok
        q'  = leqS-addC {T = lctx K} K (lsubC z c) q
        sA  = lsub-IsType s' ok' dA
        st  = lsub-HasType s' ok' dt
        ct  = leq-HasType s' ok' q' dt
        IHA = RL.rT s' ok' (lsubE z A) (adqTy dA z)
        Et  = adqLv dt z z' s' ok' q'
        e1  = AdqE1-GLam sA st ct IHA Et
        cA  = leq-IsType s' ok' q' dA
        e2  = AdqE1-GLam-equiv (equivC-leq q c) sA cA (presup-r-ConvTm ct) IHA (Adq-right ct Et)
        wfK = lsub-WfCtx s ok dG
    in AdqE1-trans {G = K} {M = GLam (lsubC z c) (lsubE z A) (lsubE z t)} {N = GLam (lsubC z c) (lsubE z A) (lsubE z' t)}
         {P = GLam (lsubC z' c) (lsubE z' A) (lsubE z' t)} {A = Grd (lsubC z c) (lsubE z A)}
         (conv-cong-GLam wfK sA st ct) e1 e2
  adqLv (ty-LLam {G = G} {A = A} {u = u} dG dA du) z z' {K} s ok q =
    let sL  = lsk-addL s
        okL = lok-addL G K ok
        qL  = leqS-addL K q
    in AdqE1-LLam (lsub-WfCtx s ok dG) (lsub-IsType sL okL dA) (leq-IsType sL okL qL dA) (lsub-HasType sL okL du)
         (leq-HasType sL okL qL du)
         (\ l -> RL.rT s ok (lsub1 (lsubE (liftL z) A) l) (inst1 AdqTy z G A l (adqTy dA (lconsS l z))))
         (lvSame du z z' s ok q) (lvTy dA z s ok) (lvTm du z s ok)
  adqLv (ty-LApp {G = G} {A = A} {t = t} {l = l} dA dt) z z' {K} s ok q =
    let sAL = lsub-IsType (lsk-addL s) (lok-addL G K ok) dA
        st  = lsub-HasType s ok dt
        ct  = leq-HasType s ok q dt
        lz  = lsubL z l
        lz' = lsubL z' l
        vzz = leqL q l
        Az  = lsubE (liftL z) A
        IHA : (l'' : LExpr) -> AdqTy K (lsub1 Az l'')
        IHA l'' = RL.rT s ok (lsub1 Az l'') (inst1 AdqTy z G A l'' (adqTy dA (lconsS l'' z)))
        cAl : ConvTy K (lsub1 Az lz) (lsub1 Az lz')
        cAl = Eq-transport (\ X -> ConvTy K X (lsub1 Az lz')) (Eq-sym (lsub1-liftL z A lz))
                (Eq-transport (ConvTy K (lsubE (lconsS lz z) A)) (Eq-sym (lsub1-liftL z A lz'))
                  (leq-IsType (lsk-cons lz s) (lok-cons G K lz ok) (leqS-inst {z = z} vzz) dA))
        Ety : AdqETy K (lsub1 Az lz') (lsub1 Az lz)
        Ety = tr2ETy (Eq-sym (lsub1-liftL z A lz')) (Eq-sym (lsub1-liftL z A lz))
                (adqLvTy dA (lconsS lz' z) (lconsS lz z) (lsk-cons lz' s) (lok-cons G K lz' ok)
                   (leqS-inst {z = z} (v-sym vzz)))
        Az' = lsubE (liftL z') A
        cAz = leq-IsType (lsk-addL s) (lok-addL G K ok) (leqS-addL K q) dA
        st1 = AdqE1-LApp-lvl sAL st vzz (RL.rA s ok (lsubE z t) (LPi Az) (adqTm dt z)) IHA
        st2 = AdqE1-conv {G = K} {M = LApp Az (lsubE z t) lz'} {N = LApp Az' (lsubE z' t) lz'}
                {A = lsub1 Az lz'} {B = lsub1 Az lz} (conv-Ty-sym cAl) Ety
                (AdqE1-LApp-fun sAL cAz ct (adqLv dt z z' s ok q) IHA lz')
    in Eq-transport (AdqE1 K (LApp Az (lsubE z t) lz) (LApp Az' (lsubE z' t) lz')) (Eq-sym (lsubE-lsub1 z A l))
         (AdqE1-trans {G = K} {M = LApp Az (lsubE z t) lz} {N = LApp Az (lsubE z t) lz'} {P = LApp Az' (lsubE z' t) lz'}
            {A = lsub1 Az lz} (conv-cong-LApp-lvl sAL st vzz cAl) st1 st2)

------------------------------------------------------------------------
-- At the identity level substitution
------------------------------------------------------------------------

private
  atId : {g : Nat} (P : Ctx g -> Set) (G : Ctx g) -> P (lsubCtx lidS G) -> P G
  atId P G = Eq-transport P (lsubCtx-id G)

adqTm0 : {g : Nat} {G : Ctx g} {M A : Expr g} -> HasType G M A -> Adq G M A
adqTm0 {G = G} {M} {A} d =
  atId (\ X -> Adq X M A) G
    (Eq-transport (\ Y -> Adq (lsubCtx lidS G) Y A) (lsubE-id M)
      (Eq-transport (Adq (lsubCtx lidS G) (lsubE lidS M)) (lsubE-id A) (adqTm d lidS)))

adqTy0 : {g : Nat} {G : Ctx g} {A : Expr g} -> IsType G A -> AdqTy G A
adqTy0 {G = G} {A} d =
  atId (\ X -> AdqTy X A) G (Eq-transport (AdqTy (lsubCtx lidS G)) (lsubE-id A) (adqTy d lidS))

adqCTy0 : {g : Nat} {G : Ctx g} {A B : Expr g} -> ConvTy G A B -> AdqETy G A B
adqCTy0 {G = G} {A} {B} d =
  atId (\ X -> AdqETy X A B) G
    (Eq-transport (\ Y -> AdqETy (lsubCtx lidS G) Y B) (lsubE-id A)
      (Eq-transport (AdqETy (lsubCtx lidS G) (lsubE lidS A)) (lsubE-id B) (adqCTy d lidS)))

adqCTm0 : {g : Nat} {G : Ctx g} {M N A : Expr g} -> ConvTm G M N A -> AdqE1 G M N A
adqCTm0 {G = G} {M} {N} {A} d =
  atId (\ X -> AdqE1 X M N A) G
    (Eq-transport (\ Y -> AdqE1 (lsubCtx lidS G) Y N A) (lsubE-id M)
      (Eq-transport (\ Y -> AdqE1 (lsubCtx lidS G) (lsubE lidS M) Y A) (lsubE-id N)
        (Eq-transport (AdqE1 (lsubCtx lidS G) (lsubE lidS M) (lsubE lidS N)) (lsubE-id A) (adqCTm d lidS))))
