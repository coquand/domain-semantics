{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- UnitType.agda
--
-- Church-encoded unit type:  Unit = Π(X:Prop). X → X
-- Unit : Prop  (proof-irrelevant)
-- tt = λ(X:Prop). λ(x:X). x
--
-- Dependent elimination:
--   G ⊢ C : U  (in context G, u:Unit)
--   G ⊢ a : C[tt]
--   ⇒  G ⊢ elim a : Π(u:Unit). C
--
-- Key: Unit : Prop gives  u = tt  for free (conv-Prop),
-- which yields  C[u] = C[tt] : U  via β + conv-App-arg.
------------------------------------------------------------------------

module UnitType where

open import Basic using (Nat ; zero ; suc ; Eq ; refl ; Eq-cong ;
  Eq-transport ; Eq-sym ; Pair ; mkSigma ; fst ; snd)
open import RawSyntax using (Fin ; fzero ; fsuc ;
  Expr ; Var ; U ; Prop ; Pi ; Lam ; App ; wkExpr ; subst1 ;
  renExpr ; liftRen ; wkRen ; Eq-trans)
open import TypingRules using (Ctx ; empty ; extend ;
  WfCtx ; wf-empty ; wf-extend ;
  HasType ; ty-var ; ty-conv ; ty-U ; ty-Prop ; ty-Prop-U ;
  ty-Pi ; ty-Pi-Prop ; ty-Lam ; ty-App ;
  ConvTm ; conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-beta ; conv-Prop ; conv-Prop-U ; conv-Pi ;
  conv-App-fun ; conv-App-arg)
open import SubstitutionLemma using (
  wk-HasType ; wk-ConvTm ;
  ren-HasType ; liftRen-RenTypes ; wkRen-RenTypes ;
  subst1-wk ; subst1-liftWk-cancel ; ren-subst1 ;
  subst-HasType ; subst1-WtSub ;
  typing-ConvTm ; typing-WfCtx ;
  subst1-cong-ConvTm)

------------------------------------------------------------------------
-- Unit = Π(X:Prop). X → X
------------------------------------------------------------------------

UnitTy : {n : Nat} -> Expr n
UnitTy = Pi Prop (Pi (Var fzero) (Var (fsuc fzero)))

ttTm : {n : Nat} -> Expr n
ttTm = Lam Prop (Lam (Var fzero) (Var fzero))

------------------------------------------------------------------------
-- Typing: Unit : Prop, Unit : U, tt : Unit
------------------------------------------------------------------------

-- G, X:Prop ⊢ X : Prop
private
  htX-Prop : {n : Nat} {G : Ctx n} -> WfCtx G ->
    HasType (extend G Prop) (Var fzero) Prop
  htX-Prop wfG = ty-var (wf-extend (ty-Prop wfG))

-- G, X:Prop ⊢ X → X : Prop
inner-Prop : {n : Nat} {G : Ctx n} -> WfCtx G ->
  HasType (extend G Prop) (Pi (Var fzero) (Var (fsuc fzero))) Prop
inner-Prop wfG =
  ty-Pi-Prop (ty-Prop-U (htX-Prop wfG))
             (ty-var (wf-extend (ty-Prop-U (htX-Prop wfG))))

-- G ⊢ Unit : Prop
UnitTy-Prop : {n : Nat} {G : Ctx n} -> WfCtx G -> HasType G UnitTy Prop
UnitTy-Prop wfG = ty-Pi-Prop (ty-Prop wfG) (inner-Prop wfG)

-- G ⊢ Unit : U
UnitTy-U : {n : Nat} {G : Ctx n} -> WfCtx G -> HasType G UnitTy U
UnitTy-U wfG = ty-Prop-U (UnitTy-Prop wfG)

-- G, X:Prop ⊢ X → X : U
inner-U : {n : Nat} {G : Ctx n} -> WfCtx G ->
  HasType (extend G Prop) (Pi (Var fzero) (Var (fsuc fzero))) U
inner-U wfG = ty-Prop-U (inner-Prop wfG)

-- G ⊢ tt : Unit
ttTm-hastype : {n : Nat} {G : Ctx n} -> WfCtx G -> HasType G ttTm UnitTy
ttTm-hastype wfG =
  ty-Lam (ty-Prop wfG) (inner-U wfG)
    (ty-Lam htXU htX1U (ty-var (wf-extend htXU)))
  where
    htXU  = ty-Prop-U (htX-Prop wfG)
    htX1U = ty-Prop-U (ty-var (wf-extend htXU))

------------------------------------------------------------------------
-- Dependent elimination
--
-- Given:
--   htC  : HasType (extend G UnitTy) C U     (C is a type family over Unit)
--   hta  : HasType G a (subst1 C ttTm)        (a inhabits C[tt])
-- Produce:
--   HasType G (Lam UnitTy (wkExpr a)) (Pi UnitTy C)
--
-- Proof idea:
--   1. wkExpr a  has type  wkExpr(C[tt])  in context  G, u:Unit
--   2. By proof irrelevance (Unit : Prop):  u = tt : Unit
--   3. Therefore  C[u] = C[tt] : U,  i.e.  C = wkExpr(C[tt]) : U
--      (via the chain:  C ←β F u = F (wk tt) β→ wkExpr(C[tt])
--       where F = wkExpr(Lam Unit C))
--   4. Convert the lambda's type from  Pi Unit (wkExpr(C[tt]))  to  Pi Unit C
------------------------------------------------------------------------

dep-elim : {n : Nat} {G : Ctx n} {C : Expr (suc n)} {a : Expr n} ->
  HasType (extend G UnitTy) C U ->
  HasType G a (subst1 C ttTm) ->
  HasType G (Lam UnitTy (wkExpr a)) (Pi UnitTy C)
dep-elim {n} {G} {C} {a} htC hta =
  let
      wfG : WfCtx G
      wfG = typing-WfCtx hta

      htUnit : HasType G UnitTy U
      htUnit = UnitTy-U wfG

      htUnitP : HasType G UnitTy Prop
      htUnitP = UnitTy-Prop wfG

      wfGU : WfCtx (extend G UnitTy)
      wfGU = wf-extend htUnit

      -- G ⊢ subst1 C ttTm : U   (by substitution lemma)
      htCtt : HasType G (subst1 C ttTm) U
      htCtt = subst-HasType (subst1-WtSub htUnit (ttTm-hastype wfG)) wfG htC

      -- G, u:Unit ⊢ wkExpr(C[tt]) : U
      htWkCtt : HasType (extend G UnitTy) (wkExpr (subst1 C ttTm)) U
      htWkCtt = wk-HasType htUnit htCtt

      -- G, u:Unit ⊢ wkExpr a : wkExpr(C[tt])
      htWka : HasType (extend G UnitTy) (wkExpr a) (wkExpr (subst1 C ttTm))
      htWka = wk-HasType htUnit hta

      -- F = Lam UnitTy C : Pi UnitTy U   in context G
      -- (F is the "type family" as a lambda)
      htF : HasType G (Lam UnitTy C) (Pi UnitTy U)
      htF = ty-Lam htUnit (ty-U wfGU) htC

      -- G, u:Unit ⊢ wkExpr F : Pi UnitTy U
      htWkF : HasType (extend G UnitTy) (wkExpr (Lam UnitTy C)) (Pi UnitTy U)
      htWkF = wk-HasType htUnit htF

      -- G, u:Unit ⊢ Prop : U   (for ty-App domain)
      htP : HasType (extend G UnitTy) Prop U
      htP = ty-Prop wfGU

      -- G, u:Unit, X:Prop ⊢ U : U   (codomain of UnitTy)
      htUU : HasType (extend (extend G UnitTy) Prop) U U
      htUU = ty-U (wf-extend htP)

      -- G, u:Unit ⊢ Unit : U
      htUnit' : HasType (extend G UnitTy) UnitTy U
      htUnit' = UnitTy-U wfGU

      -- G, u:Unit, u':Unit ⊢ U : U
      htUU2 : HasType (extend (extend G UnitTy) UnitTy) U U
      htUU2 = ty-U (wf-extend htUnit')

      -- G, u:Unit ⊢ Var 0 : Unit
      htVar0 : HasType (extend G UnitTy) (Var fzero) UnitTy
      htVar0 = ty-var wfGU

      -- G, u:Unit ⊢ wkExpr tt : Unit
      htWkTt : HasType (extend G UnitTy) (wkExpr ttTm) UnitTy
      htWkTt = wk-HasType htUnit (ttTm-hastype wfG)

      -- G, u:Unit ⊢ Unit : Prop
      htUnitP' : HasType (extend G UnitTy) UnitTy Prop
      htUnitP' = UnitTy-Prop wfGU

      ------------------------------------------------------------------
      -- Proof irrelevance:  Var 0 = wkExpr tt : Unit
      ------------------------------------------------------------------
      proof-irrel : ConvTm (extend G UnitTy) (Var fzero) (wkExpr ttTm) UnitTy
      proof-irrel = conv-Prop htUnitP' htVar0 htWkTt

      ------------------------------------------------------------------
      -- Step 1: conv-beta at Var 0
      --   App (wkExpr F) (Var 0) ≡ subst1 (liftWk C) (Var 0) : subst1 U (Var 0) = U
      -- and subst1 (liftWk C) (Var 0) = C  by subst1-liftWk-cancel
      ------------------------------------------------------------------

      -- App (wkExpr F) (Var 0)
      htApp1 : HasType (extend G UnitTy) (App (wkExpr (Lam UnitTy C)) (Var fzero)) U
      htApp1 = ty-App htUnit' htUU2 htWkF htVar0

      -- conv-beta for  (wkExpr(Lam UnitTy C)) (Var 0) ≡ subst1 (liftWk C) (Var 0)
      -- wkExpr (Lam UnitTy C) = Lam UnitTy (renExpr (liftRen wkRen) C)
      -- so the beta gives: ConvTm at (subst1 (renExpr (liftRen wkRen) C) (Var fzero))
      -- G, u:Unit, u':Unit ⊢ renExpr (liftRen wkRen) C : U
      -- (renaming C from (G,Unit) to (G,Unit,Unit) via liftRen wkRen)
      htLiftC : HasType (extend (extend G UnitTy) UnitTy) (renExpr (liftRen wkRen) C) U
      htLiftC = ren-HasType (liftRen-RenTypes {G = G} {A = UnitTy} (wkRen-RenTypes {G = G} {C = UnitTy})) (wf-extend htUnit') htC

      beta1-raw : ConvTm (extend G UnitTy)
                    (App (wkExpr (Lam UnitTy C)) (Var fzero))
                    (subst1 (renExpr (liftRen wkRen) C) (Var fzero))
                    (subst1 U (Var fzero))
      beta1-raw = conv-beta htUnit' (ty-U (wf-extend htUnit'))
                    htLiftC htVar0

      -- subst1 (renExpr (liftRen wkRen) C) (Var fzero) = C
      cancel1 : Eq (subst1 (renExpr (liftRen wkRen) C) (Var fzero)) C
      cancel1 = subst1-liftWk-cancel C

      -- subst1 U (Var fzero) = U  (definitional, but let's be safe)
      -- Actually this is definitional: substExpr (subst1Sub (Var fzero)) U = U

      -- So:  App (wkExpr F) (Var 0) ≡ C : U
      beta1 : ConvTm (extend G UnitTy)
                (App (wkExpr (Lam UnitTy C)) (Var fzero)) C U
      beta1 = Eq-transport
                (\ T -> ConvTm (extend G UnitTy)
                  (App (wkExpr (Lam UnitTy C)) (Var fzero)) T U)
                cancel1 beta1-raw

      ------------------------------------------------------------------
      -- Step 2: conv-beta at wkExpr tt
      --   App (wkExpr F) (wkExpr tt) ≡ subst1 (liftWk C) (wkExpr tt) : U
      -- and subst1 (liftWk C) (wkExpr tt) = wkExpr(C[tt])  by ren-subst1
      ------------------------------------------------------------------

      beta2-raw : ConvTm (extend G UnitTy)
                    (App (wkExpr (Lam UnitTy C)) (wkExpr ttTm))
                    (subst1 (renExpr (liftRen wkRen) C) (wkExpr ttTm))
                    (subst1 U (wkExpr ttTm))
      beta2-raw = conv-beta htUnit' (ty-U (wf-extend htUnit'))
                    htLiftC htWkTt

      -- subst1 (renExpr (liftRen wkRen) C) (wkExpr tt) = wkExpr (subst1 C tt)
      -- From ren-subst1: renExpr r (subst1 B a) = subst1 (renExpr (liftRen r) B) (renExpr r a)
      -- Setting r = wkRen, B = C, a = tt:
      --   wkExpr (subst1 C tt) = subst1 (renExpr (liftRen wkRen) C) (wkExpr tt)
      cancel2 : Eq (subst1 (renExpr (liftRen wkRen) C) (wkExpr ttTm))
                   (wkExpr (subst1 C ttTm))
      cancel2 = Eq-sym (ren-subst1 wkRen C ttTm)

      -- So:  App (wkExpr F) (wkExpr tt) ≡ wkExpr(C[tt]) : U
      beta2 : ConvTm (extend G UnitTy)
                (App (wkExpr (Lam UnitTy C)) (wkExpr ttTm))
                (wkExpr (subst1 C ttTm)) U
      beta2 = Eq-transport
                (\ T -> ConvTm (extend G UnitTy)
                  (App (wkExpr (Lam UnitTy C)) (wkExpr ttTm)) T U)
                cancel2 beta2-raw

      ------------------------------------------------------------------
      -- Step 3: conv-App-arg with proof irrelevance
      --   App (wkExpr F) (Var 0) ≡ App (wkExpr F) (wkExpr tt) : U
      ------------------------------------------------------------------
      app-conv : ConvTm (extend G UnitTy)
                   (App (wkExpr (Lam UnitTy C)) (Var fzero))
                   (App (wkExpr (Lam UnitTy C)) (wkExpr ttTm))
                   (subst1 U (Var fzero))
      app-conv = conv-App-arg htUnit' htUU2 htWkF proof-irrel

      -- subst1 U (Var fzero) = U  (definitional)
      -- So this is: App (wkExpr F) (Var 0) ≡ App (wkExpr F) (wkExpr tt) : U

      ------------------------------------------------------------------
      -- Chain:  wkExpr(C[tt]) ≡ C : U
      --   wkExpr(C[tt])  ←  App F (wk tt)  ←  App F (Var 0)  →  C
      ------------------------------------------------------------------
      codomain-conv : ConvTm (extend G UnitTy) (wkExpr (subst1 C ttTm)) C U
      codomain-conv =
        conv-trans (conv-sym beta2)
          (conv-trans (conv-sym app-conv) beta1)

      ------------------------------------------------------------------
      -- Build the lambda and convert its type
      ------------------------------------------------------------------

      -- G ⊢ Lam UnitTy (wkExpr a) : Pi UnitTy (wkExpr(C[tt]))
      htLam : HasType G (Lam UnitTy (wkExpr a)) (Pi UnitTy (wkExpr (subst1 C ttTm)))
      htLam = ty-Lam htUnit htWkCtt htWka

      -- ConvTm G (Pi UnitTy (wkExpr(C[tt]))) (Pi UnitTy C) U
      piConv : ConvTm G (Pi UnitTy (wkExpr (subst1 C ttTm))) (Pi UnitTy C) U
      piConv = conv-Pi (conv-refl (UnitTy-U wfG)) codomain-conv

      htTarget : HasType G (Pi UnitTy C) U
      htTarget = ty-Pi htUnit htC

  in ty-conv htLam piConv htTarget
