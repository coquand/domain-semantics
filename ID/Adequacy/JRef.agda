{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ID.Adequacy.JRef.agda
--
-- The RefEl-case machinery for the based-J value driver.  Builds the
-- endpoint EqValTy2  App³ sC wit0 wit0 (Ref wit0) ~ App³ sC sa sb sp  by
-- instantiating JEndpoint.adqEq-motiveApp3 (the cross App³-motive adequacy)
-- ANCHORED AT THE REAL G via a 3-slot extension of the actual sigma/rho.
--
-- Bottom layer (this commit): the endpoint value/equality transporters --
-- app-transport wrappers that move a record-level endpoint  (fixed at value
-- w, type-code tA)  down to an arbitrary  (u' <= w, a')  as the slot
-- providers of the 3-slot ValidSub2 / ValidConvSub2 require.  The type-value
-- change  tA -> a'  is exactly what app-transport-{Val2,EqVal2} does (both
-- are type-values of the same domain sA in the same env, hence Comp).
--
-- No postulates.
------------------------------------------------------------------------

module ID.Adequacy.JRef where

open import ID.Adequacy.HeadRed
open import ID.Adequacy.App using (app-transport-Val2 ; app-transport-EqVal2)
open import ID.Adequacy.Pi using (Adq ; AdqConv ; EqVal2-U-to-EqValTy2)
open import ID.Adequacy.AdqWk using (adq-wk ; adqConv-wk ; adqVar ; adqConvVar)
open import ID.Adequacy.JEndpoint using (adqEq-motiveApp3 ; adqConv-transport-type)

import ID.Domain.Basic as S
open S using (Nat ; suc ; tt ; mkSigma ; fst ; snd ; FinEl ; UCode ;
  Eq ; refl ; Eq-transport ; Eq-sym)
open import ID.Domain.Kernel using (LeCode ; LeCode-refl ; Coherent ; Comp ; FinMem)
open import ID.Syntax.Raw using (Expr ; Var ; U ; App ; Id ; Ref ; wkExpr ; wkRen ; renExpr ;
  fzero ; fsuc ; motiveTy ; ren-motiveTy ; Sub ; substExpr)
open import ID.Syntax.Typing using (Ctx ; extend ; lookup ; HasType ; WfCtx ;
  ty-var ; ty-U ; ty-Id ; wf-extend)
open import ID.Syntax.Substitution using (wk-HasType ; WtSub ; WtConvSub)
open import ID.Model.Eval using (EnvApprox ; extendEnv ; EvalRel ; CoherentEnv)
open import ID.Model.SoundnessLemmas using (Fits)

------------------------------------------------------------------------
-- epTransportVal2 : move a record endpoint VALUE (Val2 M A0 w tA) down to
-- (u' <= w, a'), for the ValidSub2 slot providers.
------------------------------------------------------------------------

epTransportVal2 : {h : Nat} {H : Ctx h} {M A0 : Expr h}
  (w tA : FinEl) -> Val2 H M A0 w tA -> FinMem w tA -> FinMem tA UCode ->
  (u' a' : FinEl) -> LeCode u' w -> Comp a' tA -> FinMem a' UCode ->
  ValTy2 H A0 a' -> ValTy2 H A0 tA -> FinMem u' a' ->
  Val2 H M A0 u' a'
epTransportVal2 w tA val fm_w_tA fm_tA_U u' a' le comp fm_a'_U vt_a' vt_tA fm_u'_a' =
  app-transport-Val2 a' tA comp fm_a'_U fm_tA_U w u' fm_w_tA fm_u'_a' le vt_a' vt_tA val

------------------------------------------------------------------------
-- epTransportEqVal2 : move a record endpoint EQUALITY (EqVal2 M N A0 w tA)
-- down to (u' <= w, a'), for the ValidConvSub2 slot providers.
------------------------------------------------------------------------

epTransportEqVal2 : {h : Nat} {H : Ctx h} {M N A0 : Expr h}
  (w tA : FinEl) -> EqVal2 H M N A0 w tA -> FinMem w tA -> FinMem tA UCode ->
  (u' a' : FinEl) -> LeCode u' w -> Comp a' tA -> FinMem a' UCode ->
  ValTy2 H A0 a' -> ValTy2 H A0 tA -> FinMem u' a' ->
  EqVal2 H M N A0 u' a'
epTransportEqVal2 w tA eq fm_w_tA fm_tA_U u' a' le comp fm_a'_U vt_a' vt_tA fm_u'_a' =
  app-transport-EqVal2 a' tA comp fm_a'_U fm_tA_U w u' fm_w_tA fm_u'_a' le vt_a' vt_tA eq

------------------------------------------------------------------------
-- jEnd-adqEq : the App³-motive CROSS adequacy at the identity-system
-- context  G'' = extend³ G (A, A↑, Id A↑↑ (Var 1)(Var 0)),  with C weakened
-- and the three arguments taken as the three fresh variables Var2/Var1/Var0.
-- This is JEndpoint.adqEq-motiveApp3 instantiated at that context; the only
-- non-trivial arguments are the weakenings of A and C (variables handle the
-- three slots) -- the wk³C : motiveTy(wk³A) obligation is discharged with
-- three ren-motiveTy transports, exactly as adq-baseBody does for the single
-- extension.
------------------------------------------------------------------------

jEnd-adqEq : {g : Nat} {G : Ctx g} {A C : Expr g} ->
  HasType G A U -> HasType G C (motiveTy A) ->
  Adq G A U -> AdqConv G A U -> AdqConv G C (motiveTy A) ->
  AdqConv (extend (extend (extend G A) (wkExpr A))
                  (Id (wkExpr (wkExpr A)) (Var (fsuc fzero)) (Var fzero)))
          (App (App (App (wkExpr (wkExpr (wkExpr C)))
                         (Var (fsuc (fsuc fzero))))
                    (Var (fsuc fzero)))
               (Var fzero)) U
jEnd-adqEq {g} {G} {A} {C} dA dC IHA IHcA IHcC =
  adqEq-motiveApp3 dA'' dC'' da'' db'' dp''
    IHA'' IHcA'' IHcC'' (adqVar (fsuc (fsuc fzero))) (adqConvVar (fsuc (fsuc fzero)))
    (adqVar (fsuc fzero)) (adqConvVar (fsuc fzero)) (adqVar fzero) (adqConvVar fzero)
  where
    IdSlot : Expr (suc (suc g))
    IdSlot = Id (wkExpr (wkExpr A)) (Var (fsuc fzero)) (Var fzero)
    -- weakened A typings
    dwkA1 = wk-HasType dA dA                    -- HasType G2 (wkA) U
    dwkA2 = wk-HasType dwkA1 dwkA1              -- HasType G3 (wk2A) U
    dv1   = ty-var {i = fsuc fzero} (wf-extend dwkA1)   -- HasType G3 (Var1) (wk2A)
    dv0   = ty-var {i = fzero} (wf-extend dwkA1)        -- HasType G3 (Var0) (wk2A)
    dIdSlot = ty-Id dwkA2 dv1 dv0              -- HasType G3 IdSlot U
    dA'' = wk-HasType dIdSlot dwkA2            -- HasType G'' (wk3A) U
    da'' = ty-var {i = fsuc (fsuc fzero)} (wf-extend dIdSlot)
    db'' = ty-var {i = fsuc fzero} (wf-extend dIdSlot)
    dp'' = ty-var {i = fzero} (wf-extend dIdSlot)
    -- weakened C typings, transported to motiveTy at each level
    dwkC1 = Eq-transport (\ T -> HasType (extend G A) (wkExpr C) T)
              (ren-motiveTy wkRen A) (wk-HasType dA dC)
    dwkC2 = Eq-transport (\ T -> HasType (extend (extend G A) (wkExpr A)) (wkExpr (wkExpr C)) T)
              (ren-motiveTy wkRen (wkExpr A)) (wk-HasType dwkA1 dwkC1)
    dC'' = Eq-transport (\ T -> HasType (extend (extend (extend G A) (wkExpr A)) IdSlot)
                                        (wkExpr (wkExpr (wkExpr C))) T)
              (ren-motiveTy wkRen (wkExpr (wkExpr A))) (wk-HasType dIdSlot dwkC2)
    -- weakened A IHs
    IHA'' = adq-wk IdSlot (wkExpr (wkExpr A)) U
              (adq-wk (wkExpr A) (wkExpr A) U (adq-wk A A U IHA))
    IHcA'' = adqConv-wk IdSlot (wkExpr (wkExpr A)) U
              (adqConv-wk (wkExpr A) (wkExpr A) U (adqConv-wk A A U IHcA))
    -- weakened C IH, transported to motiveTy at each level
    IHcC1 = adqConv-transport-type (wkExpr C) (ren-motiveTy wkRen A)
              (adqConv-wk A C (motiveTy A) IHcC)
    IHcC2 = adqConv-transport-type (wkExpr (wkExpr C)) (ren-motiveTy wkRen (wkExpr A))
              (adqConv-wk (wkExpr A) (wkExpr C) (motiveTy (wkExpr A)) IHcC1)
    IHcC'' = adqConv-transport-type (wkExpr (wkExpr (wkExpr C))) (ren-motiveTy wkRen (wkExpr (wkExpr A)))
              (adqConv-wk IdSlot (wkExpr (wkExpr C)) (motiveTy (wkExpr (wkExpr A))) IHcC2)

------------------------------------------------------------------------
-- jEnd-instantiate : apply jEnd-adqEq at the two 3-slot extended
-- substitutions (both sharing the outer sigma, differing only in the three
-- injected argument slots t0/t1/t2 vs s0/s1/s2) and the 3-slot extended
-- environment, then bridge the App³ head (substExpr σ'' (wk³C) = sC, the
-- three Var slots reduce definitionally to the injected terms) and convert
-- the U-level equality to an EqValTy2.  The caller (refCore) assembles the
-- ValidSub2 / ValidConvSub2 / WtSub / Fits / CoherentEnv objects and the
-- App³ evaluation ac in the extended environment.
------------------------------------------------------------------------

private
  App3 : {n : Nat} -> Expr n -> Expr n -> Expr n -> Expr n -> Expr n
  App3 C a b p = App (App (App C a) b) p

jEnd-instantiate : {h g : Nat} {H : Ctx h} {G : Ctx g} {A C : Expr g} ->
  HasType G A U -> HasType G C (motiveTy A) ->
  Adq G A U -> AdqConv G A U -> AdqConv G C (motiveTy A) ->
  (sigma : Sub h g) (t0 t1 t2 s0 s1 s2 : Expr h) (rho : EnvApprox g) (w0 w1 w2 : FinEl) ->
  let G'' = extend (extend (extend G A) (wkExpr A))
                   (Id (wkExpr (wkExpr A)) (Var (fsuc fzero)) (Var fzero))
      s2sub = extSub (extSub (extSub sigma t0) t1) t2
      s3sub = extSub (extSub (extSub sigma s0) s1) s2
      rho'' = extendEnv (extendEnv (extendEnv rho w0) w1) w2
  in CoherentEnv rho'' ->
     ValidSub2 H G'' s2sub rho'' -> ValidSub2 H G'' s3sub rho'' ->
     ValidConvSub2 H G'' s2sub s3sub rho'' -> Fits G'' rho'' ->
     WtSub H G'' s2sub -> WtSub H G'' s3sub -> WtConvSub H G'' s2sub s3sub -> WfCtx H ->
     (ac : FinEl) ->
     EvalRel (App3 (wkExpr (wkExpr (wkExpr C))) (Var (fsuc (fsuc fzero))) (Var (fsuc fzero)) (Var fzero))
             rho'' ac ->
     FinMem ac UCode ->
     EqValTy2 H (App3 (substExpr sigma C) t0 t1 t2) (App3 (substExpr sigma C) s0 s1 s2) ac
jEnd-instantiate {H = H} {G = G} {A = A} {C = C} dA dC IHA IHcA IHcC
  sigma t0 t1 t2 s0 s1 s2 rho w0 w1 w2
  crho'' vs'' vs''' vcs'' fits'' wt'' wt''' wcs'' wfH ac evApp3 acU =
  EqVal2-U-to-EqValTy2 ac acU eqvBridged
  where
    sC = substExpr sigma C
    s2sub = extSub (extSub (extSub sigma t0) t1) t2
    s3sub = extSub (extSub (extSub sigma s0) s1) s2
    evU = mkSigma tt (LeCode-refl UCode tt)
    -- App³ head bridge: substExpr σ'' (wk³C) = sC (peel three weakenings)
    headEqL : Eq (substExpr s2sub (wkExpr (wkExpr (wkExpr C)))) sC
    headEqL = Eq-trans (substExpr-wk (extSub (extSub sigma t0) t1) (wkExpr (wkExpr C)) t2)
                (Eq-trans (substExpr-wk (extSub sigma t0) (wkExpr C) t1)
                            (substExpr-wk sigma C t0))
    headEqR : Eq (substExpr s3sub (wkExpr (wkExpr (wkExpr C)))) sC
    headEqR = Eq-trans (substExpr-wk (extSub (extSub sigma s0) s1) (wkExpr (wkExpr C)) s2)
                (Eq-trans (substExpr-wk (extSub sigma s0) (wkExpr C) s1)
                            (substExpr-wk sigma C s0))
    raw = jEnd-adqEq dA dC IHA IHcA IHcC s2sub s3sub _
            crho'' vs'' vs''' vcs'' fits'' wt'' wt''' wcs'' wfH
            ac evApp3 UCode evU acU
    -- raw : EqVal2 H (App3 (substExpr s2sub (wk³C)) t0 t1 t2)
    --                (App3 (substExpr s3sub (wk³C)) s0 s1 s2) U ac UCode
    eqvL = Eq-transport
             (\ X -> EqVal2 H (App3 X t0 t1 t2) (App3 (substExpr s3sub (wkExpr (wkExpr (wkExpr C)))) s0 s1 s2) U ac UCode)
             headEqL raw
    eqvBridged = Eq-transport
             (\ X -> EqVal2 H (App3 sC t0 t1 t2) (App3 X s0 s1 s2) U ac UCode)
             headEqR eqvL
