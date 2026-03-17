{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- EtaConversion.agda
--
-- Eta-conversion:
--   G |- A : U   G.A |- B : U   G |- f : Pi A B
--   ─────────────────────────────────────────────
--   G |- f = \(x:A). f x : Pi A B
--
-- Uses conv-funext + conv-beta.  0 postulates.
------------------------------------------------------------------------

module EtaConversion where

open import Basic using (Nat ; suc ; Pair ; mkSigma ; fst ; snd ;
  Eq ; refl ; Eq-transport)
open import RawSyntax using (Expr ; Var ; U ; Pi ; Lam ; App ;
  Fin ; fzero ; fsuc ; wkExpr ; subst1 ;
  Ren ; liftRen ; renExpr ; wkRen ;
  Sub ; subst1Sub ;
  subst-ren ; substExpr-ext ; Eq-trans)
open import TypingRules using (Ctx ; extend ;
  HasType ; ConvTm ; WfCtx ;
  ty-var ; ty-Pi ; ty-Lam ; ty-App ;
  conv-sym ; conv-beta ; conv-funext ;
  wf-extend)
open import Reduction using (idSub ; substExpr-id)
open import SubstitutionLemma using (
  wk-HasType ; ren-HasType ;
  wkRen-RenTypes ; liftRen-RenTypes ;
  typing-WfCtx)

------------------------------------------------------------------------
-- Key identity: subst1 (renExpr (liftRen wkRen) M) (Var fzero) = M
--
-- Weakening a term in (suc n) by liftRen wkRen shifts free
-- variables while keeping var 0 fixed.  Substituting Var fzero
-- for var 0 undoes this, recovering M.
------------------------------------------------------------------------

subst1-liftWk : {n : Nat} (M : Expr (suc n)) ->
  Eq (subst1 (renExpr (liftRen wkRen) M) (Var fzero)) M
subst1-liftWk M =
  Eq-trans (subst-ren (subst1Sub (Var fzero)) (liftRen wkRen) M)
    (Eq-trans (substExpr-ext _ idSub
                (\ { fzero -> refl ; (fsuc j) -> refl }) M)
              (substExpr-id M))

------------------------------------------------------------------------
-- Inversion for Pi typing
------------------------------------------------------------------------

ty-Pi-invert : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
  {T : Expr n} ->
  HasType G (Pi A B) T -> Pair (HasType G A U) (HasType (extend G A) B U)
ty-Pi-invert (ty-Pi dA dB) = mkSigma dA dB
ty-Pi-invert (TypingRules.ty-conv d _ _) = ty-Pi-invert d

------------------------------------------------------------------------
-- Eta-conversion
------------------------------------------------------------------------

eta-conv : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
  {f : Expr n} ->
  HasType G A U -> HasType (extend G A) B U -> HasType G f (Pi A B) ->
  ConvTm G f (Lam A (App (wkExpr f) (Var fzero))) (Pi A B)
eta-conv {n} {G} {A} {B} {f} dA dB df =
  let -- Weakened types
      wkA  : HasType (extend G A) (wkExpr A) U
      wkA  = wk-HasType dA dA

      wfGA : WfCtx (extend G A)
      wfGA = wf-extend dA

      -- wkExpr (Pi A B) = Pi (wkExpr A) (renExpr (liftRen wkRen) B)
      -- so weakening df gives the right type
      wkf : HasType (extend G A) (wkExpr f) (Pi (wkExpr A) (renExpr (liftRen wkRen) B))
      wkf = wk-HasType dA df

      -- Codomain in doubly-extended context, via Pi inversion on weakened Pi
      wkPiAB : HasType (extend G A) (Pi (wkExpr A) (renExpr (liftRen wkRen) B)) U
      wkPiAB = wk-HasType dA (ty-Pi dA dB)

      wkB : HasType (extend (extend G A) (wkExpr A)) (renExpr (liftRen wkRen) B) U
      wkB = snd (ty-Pi-invert wkPiAB)

      -- Variable 0 in extended context
      var0 : HasType (extend G A) (Var fzero) (wkExpr A)
      var0 = ty-var wfGA

      -- Application: f x in extended context
      dApp0 : HasType (extend G A) (App (wkExpr f) (Var fzero))
                (subst1 (renExpr (liftRen wkRen) B) (Var fzero))
      dApp0 = ty-App wkA wkB wkf var0

      -- Transport to type B
      dApp : HasType (extend G A) (App (wkExpr f) (Var fzero)) B
      dApp = Eq-transport (HasType (extend G A) (App (wkExpr f) (Var fzero)))
               (subst1-liftWk B) dApp0

      -- Lambda: G |- \(x:A). f x : Pi A B
      dLam : HasType G (Lam A (App (wkExpr f) (Var fzero))) (Pi A B)
      dLam = ty-Lam dA dB dApp

      -- Body of weakened lambda in doubly-extended context
      -- renExpr (liftRen wkRen) preserves typing via ren-HasType
      wfGAA : WfCtx (extend (extend G A) (wkExpr A))
      wfGAA = wf-extend wkA

      rt = liftRen-RenTypes (wkRen-RenTypes {G = G} {C = A})

      dBody : HasType (extend (extend G A) (wkExpr A))
                (renExpr (liftRen wkRen) (App (wkExpr f) (Var fzero)))
                (renExpr (liftRen wkRen) B)
      dBody = ren-HasType rt wfGAA dApp

      -- Beta reduction in extended context:
      -- wkExpr (Lam A M) = Lam (wkExpr A) (renExpr (liftRen wkRen) M)  (definitional)
      -- so App (wkExpr (Lam A M)) (Var 0)  beta-reduces to  subst1 (renExpr (liftRen wkRen) M) (Var 0) = M
      beta0 : ConvTm (extend G A)
                (App (wkExpr (Lam A (App (wkExpr f) (Var fzero)))) (Var fzero))
                (subst1 (renExpr (liftRen wkRen) (App (wkExpr f) (Var fzero))) (Var fzero))
                (subst1 (renExpr (liftRen wkRen) B) (Var fzero))
      beta0 = conv-beta wkA wkB dBody var0

      -- Transport: result = App (wkExpr f) (Var fzero), type = B
      beta1 : ConvTm (extend G A)
                (App (wkExpr (Lam A (App (wkExpr f) (Var fzero)))) (Var fzero))
                (App (wkExpr f) (Var fzero))
                (subst1 (renExpr (liftRen wkRen) B) (Var fzero))
      beta1 = Eq-transport
                (\ X -> ConvTm (extend G A)
                  (App (wkExpr (Lam A (App (wkExpr f) (Var fzero)))) (Var fzero))
                  X (subst1 (renExpr (liftRen wkRen) B) (Var fzero)))
                (subst1-liftWk (App (wkExpr f) (Var fzero))) beta0

      beta : ConvTm (extend G A)
               (App (wkExpr (Lam A (App (wkExpr f) (Var fzero)))) (Var fzero))
               (App (wkExpr f) (Var fzero))
               B
      beta = Eq-transport
               (ConvTm (extend G A)
                 (App (wkExpr (Lam A (App (wkExpr f) (Var fzero)))) (Var fzero))
                 (App (wkExpr f) (Var fzero)))
               (subst1-liftWk B) beta1

      -- Symmetric: App (wkExpr f) (Var 0) = App (wkExpr g) (Var 0) : B
      body-conv : ConvTm (extend G A)
                    (App (wkExpr f) (Var fzero))
                    (App (wkExpr (Lam A (App (wkExpr f) (Var fzero)))) (Var fzero))
                    B
      body-conv = conv-sym beta

  in conv-funext dA body-conv df dLam
