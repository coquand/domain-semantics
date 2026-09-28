{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Model.RussellSound
--
-- Soundness of the finite-element model (Coquand-Huber, as formalised
-- in MIN/Model, with universe levels added) for the Russell system T_R:
-- every judgement is interpreted through `strip`, and
--
--   IsType  G A      ->  A : U_0         (InvTyp)
--   HasType G M A    ->  M : A           (InvTyp)
--   ConvTy  G A B    ->  A = B : U_0     (InvConv)
--   ConvTm  G M N A  ->  M = N : A       (InvConv)
--
-- in every environment that fits the context.  By structural induction
-- on the derivation.
--
-- 0 postulates.
------------------------------------------------------------------------

open import BCDE4.Levels using (LDecAll)

module BCDE4.Model.RussellSound (D : LDecAll) where

open import BCDE4.Dom.Basic using (EqL-refl)
import BCDE4.Dom.Basic as S
open S using (Empty ; Nat ; zero ; suc ; Top ; tt ; Sigma ; mkSigma ; fst ; snd ; Pair ;
              Eq ; refl ; Eq-transport ; Eq-sym ; Eq-cong ;
              FinEl ; Bot ; UCode ; LevTy ; LevEl ; FunEl ; PiCode ; LPiCode)
open import BCDE4.Dom.Kernel using (FinMem ; Coherent ; LeCode ; NotBot)
import BCDE4.RussellSyntax as R
open import BCDE4.RussellTyping
import BCDE4.Model.Core as C
open import BCDE4.Model.Eval D using (EnvApprox ; extendEnv ; EvalRel ; extL ; ldecT ; lcodeT)
open import BCDE4.Model.SoundnessLemmas D using (Fits ; InvTyp ; InvConv ;
  InvTyp-Lam ; InvTyp-App ; InvTyp-Pi ; InvConv-beta ; InvConv-App-fun ; InvConv-App-arg)
open import BCDE4.Model.SoundnessExtra D
open import BCDE4.Model.SoundnessLevel D
open import BCDE4.Model.EvalLevel D using (EvalRel-lshift-bwd)
open import BCDE4.Model.Strip

open import BCDE4.Levels using (LCtx ; Constr ; ValidC ; Valid ; Loop ; LoopFree ; LSub ; LSubOK ; LExpr ;
  LMem ; lhere ; lthere ; lcons ; lsubC ; lsubL ; lsubTh ; lconsS ; lwkS ; lsub1S ; lvar ;
  lsubC-comp ; lmem-unmap ; validC-lsub ; valid-lsub ; loop-lsub ;
  EquivC ; equivC-sym ; equivC-valid ; equivC-lsub ; LDec)
open import BCDE4.Model.Eval D using (emptyEnv ; EvalRel-Bot)
open import BCDE4.Model.Guard
open import BCDE4.Dom.Membership using (finMem-bot-from)
open import BCDE4.Basic using (Either ; inl ; inr ; absurd)
open import BCDE4.Model.SoundnessLemmas D using (Typed)
private variable
  TL : LCtx
  θ : LSub

------------------------------------------------------------------------
-- The level part of a fitting environment
------------------------------------------------------------------------

fits-info : {n : Nat} {G : Ctx n} {rho : EnvApprox TL θ n} ->
  Fits (stripCtx G) rho -> Pair (LoopFree TL) (LSubOK TL (lctx G) θ)
fits-info {G = empty Th} {rho = emptyEnv} f = f
fits-info {G = extend G A} {rho = extendEnv rho x} f = fits-info {G = G} (fst f)

lsubOK-cons : {Th : LCtx} (c : Constr) -> ValidC TL (lsubC θ c) -> LSubOK TL Th θ -> LSubOK TL (lcons c Th) θ
lsubOK-cons c v ok lhere      = v
lsubOK-cons c v ok (lthere h) = ok h

fits-addC : {n : Nat} {G : Ctx n} {rho : EnvApprox TL θ n} (c : Constr) ->
  Fits (stripCtx G) rho -> ValidC TL (lsubC θ c) -> Fits (stripCtx (addC G c)) rho
fits-addC {G = empty Th} {rho = emptyEnv} c f v = mkSigma (fst f) (lsubOK-cons c v (snd f))
fits-addC {G = extend G A} {rho = extendEnv rho x} c f v =
  mkSigma (fits-addC {G = G} c (fst f) v) (snd f)

fits-valid : {n : Nat} {G : Ctx n} {rho : EnvApprox TL θ n} (c : Constr) ->
  Fits (stripCtx G) rho -> ValidC (lctx G) c -> ValidC TL (lsubC θ c)
fits-valid {θ = θ} {G = G} c f v = validC-lsub θ c (snd (fits-info {G = G} f)) v

fits-equiv : {n : Nat} {G : Ctx n} {rho : EnvApprox TL θ n} {c c' : Constr} ->
  Fits (stripCtx G) rho -> EquivC (lctx G) c c' -> ValidC TL (lsubC θ c) -> ValidC TL (lsubC θ c')
fits-equiv {θ = θ} {G = G} f q = equivC-valid (equivC-lsub θ (snd (fits-info {G = G} f)) q)

fits-level : {n : Nat} {G : Ctx n} {rho : EnvApprox TL θ n} (l m : LExpr) ->
  Fits (stripCtx G) rho -> Valid (lctx G) l m -> Valid TL (lsubL θ l) (lsubL θ m)
fits-level {θ = θ} {G = G} l m f v = valid-lsub θ (snd (fits-info {G = G} f)) v

-- no environment fits a context with a loop
fits-loop : {n : Nat} {G : Ctx n} {rho : EnvApprox TL θ n} {X : Set} ->
  Fits (stripCtx G) rho -> Loop (lctx G) -> X
fits-loop {θ = θ} {G = G} f lp =
  absurd (fst (fits-info {G = G} f) (loop-lsub θ (snd (fits-info {G = G} f)) lp))

-- entering a level binder: level 0 := l
lsubOK-addL : {Th : LCtx} (l : LExpr) -> LSubOK TL Th θ -> LSubOK TL (lsubTh lwkS Th) (lconsS l θ)
lsubOK-addL {TL = TL} {θ = θ} {Th = Th} l ok {d} h =
  let r  = lmem-unmap lwkS Th h
      c  = fst r
  in Eq-transport (\ e -> ValidC TL (lsubC (lconsS l θ) e)) (Eq-sym (snd (snd r)))
       (Eq-transport (ValidC TL) (Eq-sym (lsubC-comp (lconsS l θ) lwkS c)) (ok (fst (snd r))))

fits-addL : {n : Nat} {G : Ctx n} {rho : EnvApprox TL θ n} (l : LExpr) ->
  Fits (stripCtx G) rho -> Fits (stripCtx (addL G)) (extL rho l)
fits-addL {G = empty Th} {rho = emptyEnv} l f = mkSigma (fst f) (lsubOK-addL l (snd f))
fits-addL {G = extend G A} {rho = extendEnv rho x} l f =
  mkSigma (fits-addL {G = G} l (fst f))
    (mkSigma (fst (snd f)) (mkSigma (fst (snd (snd f)))
      (Eq-transport (\ X -> EvalRel X (extL rho l) (fst (snd f))) (Eq-sym (strip-lsubE lwkS A))
        (EvalRel-lshift-bwd (strip A) rho l (fst (snd f)) (snd (snd (snd f)))))))

------------------------------------------------------------------------
-- Guarded terms and types
------------------------------------------------------------------------

memBotU : {k : Nat} -> FinMem Bot (UCode k)
memBotU {k} = finMem-bot-from (UCode k) tt

-- the universe used to state the soundness of the type judgements (any
-- universe would do: membership in the model ignores the level)
L0 : LExpr
L0 = lvar zero

-- U_l : U_m holds in the model for all l, m
InvTyp-UU : {n : Nat} {G : C.Ctx n} {rho : EnvApprox TL θ n} (l m : LExpr) ->
  InvTyp G (C.U l) (C.U m) rho
InvTyp-UU {TL = TL} {θ = θ} l m u ev =
  mkSigma (UCode (lcodeT TL (lsubL θ l))) (mkSigma (UCode (lcodeT TL (lsubL θ m)))
    (mkSigma (snd ev) (mkSigma (mkSigma tt (EqL-refl (lcodeT TL (lsubL θ l))))
      (mkSigma tt (mkSigma tt (EqL-refl (lcodeT TL (lsubL θ m))))))))

-- a conversion at one universe is one at any other
InvConv-U-lvl : {n : Nat} {G : C.Ctx n} {M N : C.Expr n} {rho : EnvApprox TL θ n} (l m : LExpr) ->
  InvConv G M N (C.U l) rho -> InvConv G M N (C.U m) rho
InvConv-U-lvl {G = G} {M = M} {N = N} {rho = rho} l m h =
  mkSigma (InvTyp-U-lvl {G = G} {M = M} {rho = rho} l m (fst h))
    (mkSigma (InvTyp-U-lvl {G = G} {M = N} {rho = rho} l m (fst (snd h))) (snd (snd h)))

memBotBot : FinMem Bot Bot
memBotBot = finMem-bot-from Bot (memBotU {zero})

InvTyp-GrdU : {n : Nat} {G : C.Ctx n} {c : Constr} {X : C.Expr n} {rho : EnvApprox TL θ n} {L : LExpr} ->
  (ValidC TL (lsubC θ c) -> InvTyp G X (C.U L) rho) -> InvTyp G (C.Grd c X) (C.U L) rho
InvTyp-GrdU {TL = TL} {θ = θ} {c = c} {X = X} {rho = rho} {L = L} ih u ev = cases u (guard-out u ev)
  where
    cases : (u : FinEl) -> Either (Eq u Bot) (Pair (ValidC TL (lsubC θ c)) (EvalRel X rho u)) ->
      Typed (C.Grd c X) (C.U L) rho u
    cases .Bot (inl refl) =
      mkSigma Bot (mkSigma (UCode (lcodeT TL (lsubL θ L)))
        (mkSigma tt (mkSigma tt (mkSigma (memBotU {lcodeT TL (lsubL θ L)}) (mkSigma tt (EqL-refl (lcodeT TL (lsubL θ L))))))))
    cases u (inr ve) =
      let t = ih (fst ve) u (snd ve)
      in mkSigma (fst t) (mkSigma (fst (snd t)) (mkSigma (fst (snd (snd t)))
           (mkSigma (guard-in (fst t) (fst ve) (fst (snd (snd (snd t))))) (snd (snd (snd (snd t)))))))

InvTyp-GLam : {n : Nat} {G : C.Ctx n} {c : Constr} {X Y : C.Expr n} {rho : EnvApprox TL θ n} ->
  (ValidC TL (lsubC θ c) -> InvTyp G X Y rho) -> InvTyp G (C.GLam c X) (C.Grd c Y) rho
InvTyp-GLam {TL = TL} {θ = θ} {c = c} {X = X} {Y = Y} {rho = rho} ih u ev = cases u (guard-out u ev)
  where
    cases : (u : FinEl) -> Either (Eq u Bot) (Pair (ValidC TL (lsubC θ c)) (EvalRel X rho u)) ->
      Typed (C.GLam c X) (C.Grd c Y) rho u
    cases .Bot (inl refl) =
      mkSigma Bot (mkSigma Bot (mkSigma tt (mkSigma tt (mkSigma memBotBot tt))))
    cases u (inr ve) =
      let t = ih (fst ve) u (snd ve)
          a' = fst (snd t)
      in mkSigma (fst t) (mkSigma a' (mkSigma (fst (snd (snd t)))
           (mkSigma (guard-in (fst t) (fst ve) (fst (snd (snd (snd t)))))
             (mkSigma (fst (snd (snd (snd (snd t)))))
                      (guard-in a' (fst ve) (snd (snd (snd (snd (snd t))))))))))

InvConv-GrdU : {n : Nat} {G : C.Ctx n} {c : Constr} {X X' : C.Expr n} {rho : EnvApprox TL θ n} {L : LExpr} ->
  (ValidC TL (lsubC θ c) -> InvConv G X X' (C.U L) rho) -> InvConv G (C.Grd c X) (C.Grd c X') (C.U L) rho
InvConv-GrdU {G = G} {c = c} {X = X} {X' = X'} {rho = rho} {L = L} h =
  mkSigma (InvTyp-GrdU {G = G} {c = c} {X = X} {rho = rho} {L = L} (\ v -> fst (h v))) (mkSigma (InvTyp-GrdU {G = G} {c = c} {X = X'} {rho = rho} {L = L} (\ v -> fst (snd (h v))))
    (mkSigma (\ u ev -> guard-mapV {P = EvalRel X rho} {Q = EvalRel X' rho} (\ v -> v) (\ b v e -> fst (snd (snd (h v))) b e) u ev)
             (\ u ev -> guard-mapV {P = EvalRel X' rho} {Q = EvalRel X rho} (\ v -> v) (\ b v e -> snd (snd (snd (h v))) b e) u ev)))

InvConv-GLam : {n : Nat} {G : C.Ctx n} {c : Constr} {X X' Y : C.Expr n} {rho : EnvApprox TL θ n} ->
  (ValidC TL (lsubC θ c) -> InvConv G X X' Y rho) -> InvConv G (C.GLam c X) (C.GLam c X') (C.Grd c Y) rho
InvConv-GLam {G = G} {c = c} {X = X} {X' = X'} {Y = Y} {rho = rho} h =
  mkSigma (InvTyp-GLam {G = G} {c = c} {X = X} {Y = Y} {rho = rho} (\ v -> fst (h v))) (mkSigma (InvTyp-GLam {G = G} {c = c} {X = X'} {Y = Y} {rho = rho} (\ v -> fst (snd (h v))))
    (mkSigma (\ u ev -> guard-mapV {P = EvalRel X rho} {Q = EvalRel X' rho} (\ v -> v) (\ b v e -> fst (snd (snd (h v))) b e) u ev)
             (\ u ev -> guard-mapV {P = EvalRel X' rho} {Q = EvalRel X rho} (\ v -> v) (\ b v e -> snd (snd (snd (h v))) b e) u ev)))

-- a guard can be replaced by an equivalent one
InvConv-GrdEquiv : {n : Nat} {G : C.Ctx n} {c c' : Constr} {X : C.Expr n} {rho : EnvApprox TL θ n} {L : LExpr} ->
  (ValidC TL (lsubC θ c) -> ValidC TL (lsubC θ c')) -> (ValidC TL (lsubC θ c') -> ValidC TL (lsubC θ c)) ->
  (ValidC TL (lsubC θ c) -> InvTyp G X (C.U L) rho) -> InvConv G (C.Grd c X) (C.Grd c' X) (C.U L) rho
InvConv-GrdEquiv {G = G} {c = c} {c' = c'} {X = X} {rho = rho} {L = L} to from ih =
  mkSigma invL
    (mkSigma (InvTyp-equiv {G = G} {M = C.Grd c X} {N = C.Grd c' X} {T = C.U L} {rho = rho} invL bwd fwd)
      (mkSigma fwd bwd))
  where
    invL = InvTyp-GrdU {G = G} {c = c} {X = X} {rho = rho} {L = L} ih
    fwd : (u : FinEl) -> EvalRel (C.Grd c X) rho u -> EvalRel (C.Grd c' X) rho u
    fwd u ev = guard-mapV {P = EvalRel X rho} {Q = EvalRel X rho} to (\ b v e -> e) u ev
    bwd : (u : FinEl) -> EvalRel (C.Grd c' X) rho u -> EvalRel (C.Grd c X) rho u
    bwd u ev = guard-mapV {P = EvalRel X rho} {Q = EvalRel X rho} from (\ b v e -> e) u ev

InvConv-GLamEquiv : {n : Nat} {G : C.Ctx n} {c c' : Constr} {X Y : C.Expr n} {rho : EnvApprox TL θ n} ->
  (ValidC TL (lsubC θ c) -> ValidC TL (lsubC θ c')) -> (ValidC TL (lsubC θ c') -> ValidC TL (lsubC θ c)) ->
  (ValidC TL (lsubC θ c) -> InvTyp G X Y rho) -> InvConv G (C.GLam c X) (C.GLam c' X) (C.Grd c Y) rho
InvConv-GLamEquiv {G = G} {c = c} {c' = c'} {X = X} {Y = Y} {rho = rho} to from ih =
  mkSigma invL
    (mkSigma (InvTyp-equiv {G = G} {M = C.GLam c X} {N = C.GLam c' X} {T = C.Grd c Y} {rho = rho} invL bwd fwd)
      (mkSigma fwd bwd))
  where
    invL = InvTyp-GLam {G = G} {c = c} {X = X} {Y = Y} {rho = rho} ih
    fwd : (u : FinEl) -> EvalRel (C.GLam c X) rho u -> EvalRel (C.GLam c' X) rho u
    fwd u ev = guard-mapV {P = EvalRel X rho} {Q = EvalRel X rho} to (\ b v e -> e) u ev
    bwd : (u : FinEl) -> EvalRel (C.GLam c' X) rho u -> EvalRel (C.GLam c X) rho u
    bwd u ev = guard-mapV {P = EvalRel X rho} {Q = EvalRel X rho} from (\ b v e -> e) u ev

-- a valid guard can be dropped
guard-drop : {V : Set} {P : FinEl -> Set} -> P Bot -> (u : FinEl) ->
  Either (Eq u Bot) (Pair V (P u)) -> P u
guard-drop pb .Bot (inl refl) = pb
guard-drop pb u (inr ve) = snd ve

InvConv-dropGrd : {n : Nat} {G : C.Ctx n} {c : Constr} {X Y : C.Expr n} {rho : EnvApprox TL θ n} ->
  ValidC TL (lsubC θ c) -> InvTyp G X Y rho -> InvConv G (C.Grd c X) X Y rho
InvConv-dropGrd {G = G} {c = c} {X = X} {Y = Y} {rho = rho} v inv =
  mkSigma (InvTyp-equiv {G = G} {M = X} {N = C.Grd c X} {T = Y} {rho = rho} inv fwd bwd)
    (mkSigma inv (mkSigma fwd bwd))
  where
    fwd : (u : FinEl) -> EvalRel (C.Grd c X) rho u -> EvalRel X rho u
    fwd u ev = guard-drop {P = EvalRel X rho} (EvalRel-Bot X rho) u (guard-out u ev)
    bwd : (u : FinEl) -> EvalRel X rho u -> EvalRel (C.Grd c X) rho u
    bwd u e = guard-in u v e

InvConv-dropGLam : {n : Nat} {G : C.Ctx n} {c : Constr} {X Y : C.Expr n} {rho : EnvApprox TL θ n} ->
  ValidC TL (lsubC θ c) -> InvTyp G X Y rho -> InvConv G (C.GLam c X) X Y rho
InvConv-dropGLam {G = G} {c = c} {X = X} {Y = Y} {rho = rho} v inv =
  mkSigma (InvTyp-equiv {G = G} {M = X} {N = C.GLam c X} {T = Y} {rho = rho} inv fwd bwd)
    (mkSigma inv (mkSigma fwd bwd))
  where
    fwd : (u : FinEl) -> EvalRel (C.GLam c X) rho u -> EvalRel X rho u
    fwd u ev = guard-drop {P = EvalRel X rho} (EvalRel-Bot X rho) u (guard-out u ev)
    bwd : (u : FinEl) -> EvalRel X rho u -> EvalRel (C.GLam c X) rho u
    bwd u e = guard-in u v e


------------------------------------------------------------------------
-- Transport along syntactic equalities
------------------------------------------------------------------------

-- guard η: a term of type [ψ]Y denotes ⊥ where ψ fails
private
  nb-le : (u u' : FinEl) -> NotBot u -> LeCode u u' -> NotBot u'
  nb-le u Bot          nb le = absurd (nb-eq u nb (leBot-eq u le))
    where
      nb-eq : (u : FinEl) -> NotBot u -> Eq u Bot -> Empty
      nb-eq .Bot () refl
  nb-le u (UCode _)    nb le = tt
  nb-le u LevTy        nb le = tt
  nb-le u (LevEl _)    nb le = tt
  nb-le u (FunEl _)    nb le = tt
  nb-le u (PiCode _ _) nb le = tt
  nb-le u (LPiCode _)  nb le = tt

  grd-V : {V : Set} {P : FinEl -> Set} (u a : FinEl) -> NotBot u -> FinMem u a -> Guard V P a -> V
  grd-V u Bot          nb fm g = absurd (mem-bot u nb fm)
    where
      mem-bot : (u : FinEl) -> NotBot u -> FinMem u Bot -> Empty
      mem-bot (UCode _)    nb ()
      mem-bot LevTy        nb ()
      mem-bot (LevEl _)    nb ()
      mem-bot (FunEl _)    nb ()
      mem-bot (PiCode _ _) nb ()
      mem-bot (LPiCode _)  nb ()
  grd-V u (UCode _)    nb fm g = fst g
  grd-V u LevTy        nb fm g = fst g
  grd-V u (LevEl _)    nb fm g = fst g
  grd-V u (FunEl _)    nb fm g = fst g
  grd-V u (PiCode _ _) nb fm g = fst g
  grd-V u (LPiCode _)  nb fm g = fst g

InvConv-GLamEta : {n : Nat} {G : C.Ctx n} {c : Constr} {X Y : C.Expr n} {rho : EnvApprox TL θ n} ->
  InvTyp G X (C.Grd c Y) rho -> InvConv G X (C.GLam c X) (C.Grd c Y) rho
InvConv-GLamEta {TL = TL} {θ = θ} {G = G} {c = c} {X = X} {Y = Y} {rho = rho} inv =
  mkSigma inv
    (mkSigma (InvTyp-equiv {G = G} {M = X} {N = C.GLam c X} {T = C.Grd c Y} {rho = rho} inv bwd fwd)
      (mkSigma fwd bwd))
  where
    fwd : (u : FinEl) -> EvalRel X rho u -> EvalRel (C.GLam c X) rho u
    fwd = nb-elim (\ u -> EvalRel X rho u -> EvalRel (C.GLam c X) rho u) (\ _ -> tt)
      (\ u nb ev ->
        let mkSigma u' (mkSigma a' (mkSigma le (mkSigma _ (mkSigma fm evT)))) = inv u ev
        in guard-in u (grd-V {P = EvalRel Y rho} u' a' (nb-le u u' nb le) fm evT) ev)
    bwd : (u : FinEl) -> EvalRel (C.GLam c X) rho u -> EvalRel X rho u
    bwd u ev = guard-drop {P = EvalRel X rho} (EvalRel-Bot X rho) u (guard-out u ev)

InvTyp-cong : {n : Nat} {G : C.Ctx n} {M M' T T' : C.Expr n} {rho : EnvApprox TL θ n}
  -> Eq M M' -> Eq T T' -> InvTyp G M T rho -> InvTyp G M' T' rho
InvTyp-cong refl refl inv = inv

InvConv-cong : {n : Nat} {G : C.Ctx n} {M M' N N' T T' : C.Expr n} {rho : EnvApprox TL θ n}
  -> Eq M M' -> Eq N N' -> Eq T T' -> InvConv G M N T rho -> InvConv G M' N' T' rho
InvConv-cong refl refl refl inv = inv

------------------------------------------------------------------------
-- Evaluation of products respects conversion of the components
------------------------------------------------------------------------

Pi-fwd : {n : Nat} (A A' : C.Expr n) (B B' : C.Expr (suc n))
  (rho : EnvApprox TL θ n) -> (u : FinEl) ->
  ((w : FinEl) -> EvalRel A rho w -> EvalRel A' rho w) ->
  ((x a : FinEl) -> FinMem x a -> EvalRel A rho a ->
    (w : FinEl) -> EvalRel B (extendEnv rho x) w -> EvalRel B' (extendEnv rho x) w) ->
  EvalRel (C.Pi A B) rho u -> EvalRel (C.Pi A' B') rho u
Pi-fwd A A' B B' rho Bot eqA eqB ev = tt
Pi-fwd A A' B B' rho (PiCode b f) eqA eqB
  (mkSigma coh (mkSigma evA-b (mkSigma a' (mkSigma evA' body)))) =
  mkSigma coh (mkSigma (eqA b evA-b)
    (mkSigma a' (mkSigma (eqA a' evA')
      (\ u v sel ->
        let mkSigma x (mkSigma le (mkSigma mem evB)) = body u v sel
        in mkSigma x (mkSigma le (mkSigma mem (eqB x a' mem evA' v evB)))))))
Pi-fwd A A' B B' rho (UCode _) eqA eqB ()
Pi-fwd A A' B B' rho (FunEl g) eqA eqB ()
Pi-fwd A A' B B' rho LevTy eqA eqB ()
Pi-fwd A A' B B' rho (LevEl _) eqA eqB ()
Pi-fwd A A' B B' rho (LPiCode _) eqA eqB ()

-- Congruence for products, at any level, from the component invariants.
InvConv-Pi : {n : Nat} {G : C.Ctx n} {L : LExpr} (A A' : C.Expr n) (B B' : C.Expr (suc n))
  (rho : EnvApprox TL θ n) -> Fits G rho
  -> InvConv G A A' (C.U L) rho
  -> ((rho' : EnvApprox TL θ n) (x a : FinEl) -> Fits G rho' -> FinMem x a ->
        EvalRel A rho' a -> InvConv (C.extend G A) B B' (C.U L) (extendEnv rho' x))
  -> InvConv G (C.Pi A B) (C.Pi A' B') (C.U L) rho
InvConv-Pi {L = L} A A' B B' rho fits cA cB =
  let mkSigma invA (mkSigma invA' (mkSigma fwdA bwdA)) = cA
      fwd = \ u ev -> Pi-fwd A A' B B' rho u fwdA
              (\ x a0 fm evA w -> fst (snd (snd (cB rho x a0 fits fm evA))) w) ev
      bwd = \ u ev -> Pi-fwd A' A B' B rho u bwdA
              (\ x a0 fm evA' w ->
                 snd (snd (snd (cB rho x a0 fits fm (bwdA a0 evA')))) w) ev
      invL = InvTyp-Pi {l = L} A B rho fits invA
               (\ x a0 fm evA -> fst (cB rho x a0 fits fm evA))
      invR = InvTyp-Pi {l = L} A' B' rho fits invA'
               (\ x a0 fm evA' -> fst (snd (cB rho x a0 fits fm (bwdA a0 evA'))))
  in mkSigma invL (mkSigma invR (mkSigma fwd bwd))

------------------------------------------------------------------------
-- The soundness theorem
------------------------------------------------------------------------

-- Fits for an extended context.
fitsE : {n : Nat} {G : Ctx n} {A : R.Expr n} {rho : EnvApprox TL θ n} {x a : FinEl}
  -> Fits (stripCtx G) rho -> FinMem x a -> EvalRel (strip A) rho a
  -> Fits (stripCtx (extend G A)) (extendEnv rho x)
fitsE {a = a} fits fm evA = mkSigma fits (mkSigma a (mkSigma fm evA))

mutual

  sound-Ty : {n : Nat} {G : Ctx n} {A : R.Expr n}
    -> IsType G A -> (rho : EnvApprox TL θ n) -> Fits (stripCtx G) rho
    -> InvTyp (stripCtx G) (strip A) (C.U L0) rho
  sound-Ty {G = G} (is-Ty-from-U {A = A} {l = l} d) rho fits =
    InvTyp-U-lvl {G = stripCtx G} {M = strip A} {rho = rho} l L0 (sound-Tm d rho fits)
  sound-Ty {G = G} (is-Pi {A = A} {B = B} dA dB) rho fits =
    InvTyp-Pi (strip A) (strip B) rho fits (sound-Ty dA rho fits)
      (\ x a fm evA -> sound-Ty dB (extendEnv rho x) (fitsE {G = G} {A = A} fits fm evA))
  sound-Ty {G = G} (is-Grd {c = c} {A = A} dG dA) rho fits =
    InvTyp-GrdU {G = stripCtx G} {c = c} {X = strip A} {rho = rho} {L = L0}
      (\ v -> sound-Ty dA rho (fits-addC {G = G} c fits v))
  sound-Ty {TL = TL} {G = G} (is-LPi {A = A} dG dA) rho fits =
    InvTyp-LPi {l = L0} (strip A) rho fits
      (\ k -> sound-Ty dA (extL rho (ldecT TL k)) (fits-addL {G = G} (ldecT TL k) fits))

  sound-Tm : {n : Nat} {G : Ctx n} {M A : R.Expr n}
    -> HasType G M A -> (rho : EnvApprox TL θ n) -> Fits (stripCtx G) rho
    -> InvTyp (stripCtx G) (strip M) (strip A) rho
  sound-Tm {G = G} (ty-var {i = i} wf) rho fits =
    InvTyp-cong {G = stripCtx G} {M = C.Var i} {M' = C.Var i} refl (Eq-sym (strip-lookup G i))
      (InvTyp-var rho fits i)
  sound-Tm {G = G} (ty-GLam {c = c} {A = A} {t = t} dG dA dt) rho fits =
    InvTyp-GLam {G = stripCtx G} {c = c} {X = strip t} {Y = strip A} {rho = rho} (\ v -> sound-Tm dt rho (fits-addC {G = G} c fits v))
  sound-Tm {TL = TL} {θ = θ} (ty-Emp {l = l} dG) rho fits u ev =
    mkSigma Bot (mkSigma (UCode (lcodeT TL (lsubL θ l))) (mkSigma (snd ev) (mkSigma (mkSigma tt tt)
      (mkSigma (memBotU {lcodeT TL (lsubL θ l)}) (mkSigma tt (EqL-refl (lcodeT TL (lsubL θ l))))))))
  sound-Tm {G = G} (ty-collapse lp dA) rho fits = fits-loop {G = G} fits lp
  sound-Tm {TL = TL} {G = G} (ty-LLam {A = A} {u = u} dG dA du) rho fits =
    InvTyp-LLam (strip A) (strip u) rho fits
      (\ k -> sound-Tm du (extL rho (ldecT TL k)) (fits-addL {G = G} (ldecT TL k) fits))
  sound-Tm {G = G} (ty-LApp {A = A} {t = t} {l = l} dA dt) rho fits =
    InvTyp-cong {G = stripCtx G} {M = C.LApp (strip t) l} refl (Eq-sym (strip-lsubE (lsub1S l) A))
      (InvTyp-LApp (strip A) (strip t) l rho fits (sound-Tm dt rho fits))
  sound-Tm (ty-conv dM dAB) rho fits u ev =
    let mkSigma u' (mkSigma a' (mkSigma le (mkSigma evM (mkSigma fm evA)))) =
          sound-Tm dM rho fits u ev
        fwdAB = fst (snd (snd (sound-CTy dAB rho fits)))
    in mkSigma u' (mkSigma a' (mkSigma le (mkSigma evM (mkSigma fm (fwdAB a' evA)))))
  sound-Tm {G = G} (ty-U {l = l} {m = m} wf _) rho fits = InvTyp-UU {G = stripCtx G} {rho = rho} l m
  sound-Tm {G = G} (ty-cum {A = A} {l = l} {m = m} d _) rho fits =
    InvTyp-U-lvl {G = stripCtx G} {M = strip A} {rho = rho} l m (sound-Tm d rho fits)
  sound-Tm {G = G} (ty-Pi {A = A} {B = B} {l = l} dA dB) rho fits =
    InvTyp-Pi {l = l} (strip A) (strip B) rho fits (sound-Tm dA rho fits)
      (\ x a fm evA -> sound-Tm dB (extendEnv rho x) (fitsE {G = G} {A = A} fits fm evA))
  sound-Tm {G = G} (ty-Lam {A = A} {B = B} {b = b} dA dB db) rho fits =
    InvTyp-Lam (strip A) (strip B) (strip b)
      (\ rho' x a fits' fm evA -> sound-Tm db (extendEnv rho' x) (fitsE {G = G} {A = A} fits' fm evA))
      rho fits
  sound-Tm {G = G} (ty-App {A = A} {B = B} {c = c} {a = a} dA dB dc da) rho fits =
    InvTyp-cong {G = stripCtx G} {M = C.App (strip c) (strip a)} {M' = C.App (strip c) (strip a)}
      refl (Eq-sym (strip-subst1 B a))
      (InvTyp-App (strip A) (strip B) (strip c) (strip a) rho fits
        (sound-Tm dc rho fits) (sound-Tm da rho fits))

  sound-CTy : {n : Nat} {G : Ctx n} {A B : R.Expr n}
    -> ConvTy G A B -> (rho : EnvApprox TL θ n) -> Fits (stripCtx G) rho
    -> InvConv (stripCtx G) (strip A) (strip B) (C.U L0) rho
  sound-CTy (conv-Ty-refl dA) rho fits =
    let inv = sound-Ty dA rho fits
    in mkSigma inv (mkSigma inv (mkSigma (\ u ev -> ev) (\ u ev -> ev)))
  sound-CTy (conv-Ty-sym d) rho fits =
    let mkSigma iA (mkSigma iB (mkSigma f b)) = sound-CTy d rho fits
    in mkSigma iB (mkSigma iA (mkSigma b f))
  sound-CTy (conv-Ty-trans d1 d2) rho fits =
    let mkSigma iA (mkSigma _  (mkSigma f1 b1)) = sound-CTy d1 rho fits
        mkSigma _  (mkSigma iC (mkSigma f2 b2)) = sound-CTy d2 rho fits
    in mkSigma iA (mkSigma iC
         (mkSigma (\ u ev -> f2 u (f1 u ev)) (\ u ev -> b1 u (b2 u ev))))
  sound-CTy {G = G} (conv-Ty-Pi {A = A} {A' = A'} {B = B} {B' = B'} _ _ dA dB) rho fits =
    InvConv-Pi {L = L0} (strip A) (strip A') (strip B) (strip B') rho fits
      (sound-CTy dA rho fits)
      (\ rho' x a fits' fm evA -> sound-CTy dB (extendEnv rho' x) (fitsE {G = G} {A = A} fits' fm evA))
  sound-CTy {G = G} (conv-Ty-from-U {A = A} {B = B} {l = l} d) rho fits =
    InvConv-U-lvl {G = stripCtx G} {M = strip A} {N = strip B} {rho = rho} l L0 (sound-CTm d rho fits)
  sound-CTy {G = G} (conv-Ty-Grd-beta {c = c} {A = A} v dA) rho fits =
    InvConv-dropGrd {G = stripCtx G} {c = c} {X = strip A} {Y = C.U L0} {rho = rho}
      (fits-valid {G = G} c fits v) (sound-Ty dA rho fits)
  sound-CTy {G = G} (conv-Ty-Grd-equiv {c = c} {c' = c'} {A = A} dG q dA) rho fits =
    InvConv-GrdEquiv {G = stripCtx G} {c = c} {c' = c'} {X = strip A} {rho = rho} {L = L0}
      (fits-equiv {G = G} fits q) (fits-equiv {G = G} fits (equivC-sym q))
      (\ v -> sound-Ty dA rho (fits-addC {G = G} c fits v))
  sound-CTy {G = G} (conv-Ty-Grd {c = c} {A = A} {B = B} dG dA dAB) rho fits =
    InvConv-GrdU {G = stripCtx G} {c = c} {X = strip A} {X' = strip B} {rho = rho} {L = L0} (\ v -> sound-CTy dAB rho (fits-addC {G = G} c fits v))
  sound-CTy {G = G} (conv-Ty-collapse lp dA) rho fits = fits-loop {G = G} fits lp
  sound-CTy {TL = TL} {G = G} (conv-Ty-LPi {A = A} {B = B} dG dA dAB) rho fits =
    InvConv-LPi {l = L0} (strip A) (strip B) rho fits
      (\ k -> sound-CTy dAB (extL rho (ldecT TL k)) (fits-addL {G = G} (ldecT TL k) fits))

  sound-CTm : {n : Nat} {G : Ctx n} {M N A : R.Expr n}
    -> ConvTm G M N A -> (rho : EnvApprox TL θ n) -> Fits (stripCtx G) rho
    -> InvConv (stripCtx G) (strip M) (strip N) (strip A) rho
  sound-CTm {G = G} (conv-cum {A = A} {B = B} {l = l} {m = m} d _) rho fits =
    InvConv-U-lvl {G = stripCtx G} {M = strip A} {N = strip B} {rho = rho} l m (sound-CTm d rho fits)
  sound-CTm {TL = TL} {θ = θ} {G = G} (conv-U-lvl {l = l} {l' = l'} {m = m} dG v w) rho fits =
    mkSigma (InvTyp-UU {G = stripCtx G} {rho = rho} l m) (mkSigma (InvTyp-UU {G = stripCtx G} {rho = rho} l' m)
      (mkSigma (tr eq) (tr (Eq-sym eq))))
    where
      eq : Eq (lcodeT TL (lsubL θ l)) (lcodeT TL (lsubL θ l'))
      eq = LDec.lcode-sound (D TL) (fits-level {G = G} l l' fits v)
      tr : {a b : Nat} -> Eq a b -> (u : FinEl) -> Pair (Coherent u) (LeCode u (UCode a)) ->
        Pair (Coherent u) (LeCode u (UCode b))
      tr refl u e = e
  sound-CTm (conv-refl dM) rho fits =
    let inv = sound-Tm dM rho fits
    in mkSigma inv (mkSigma inv (mkSigma (\ u ev -> ev) (\ u ev -> ev)))
  sound-CTm {G = G} (conv-cong-GLam {c = c} {A = A} {t = t} {t' = t'} dG dA dt dtt) rho fits =
    InvConv-GLam {G = stripCtx G} {c = c} {X = strip t} {X' = strip t'} {Y = strip A} {rho = rho} (\ v -> sound-CTm dtt rho (fits-addC {G = G} c fits v))
  sound-CTm {G = G} (conv-GLam-beta {c = c} {A = A} {t = t} v dA dt) rho fits =
    InvConv-dropGLam {G = stripCtx G} {c = c} {X = strip t} {Y = strip A} {rho = rho} (fits-valid {G = G} c fits v) (sound-Tm dt rho fits)
  sound-CTm {G = G} (conv-GLam-eta {c = c} {A = A} {t = t} dG dA dt dt') rho fits =
    InvConv-GLamEta {G = stripCtx G} {c = c} {X = strip t} {Y = strip A} {rho = rho} (sound-Tm dt rho fits)
  sound-CTm {G = G} (conv-collapse lp dA dt) rho fits = fits-loop {G = G} fits lp
  sound-CTm {TL = TL} {G = G} (conv-cong-LLam {A = A} {u = u} {u' = u'} dG dA du duu) rho fits =
    InvConv-LLam (strip A) (strip u) (strip u') rho fits
      (\ k -> sound-CTm duu (extL rho (ldecT TL k)) (fits-addL {G = G} (ldecT TL k) fits))
  sound-CTm {G = G} (conv-cong-LApp-fun {A = A} {t = t} {t' = t'} {l = l} dA dtt) rho fits =
    InvConv-cong {G = stripCtx G} {M = C.LApp (strip t) l} {N = C.LApp (strip t') l}
      refl refl (Eq-sym (strip-lsubE (lsub1S l) A))
      (InvConv-LApp-fun (strip A) (strip t) (strip t') l rho fits (sound-CTm dtt rho fits))
  sound-CTm {G = G} (conv-cong-LApp-lvl {A = A} {t = t} {l = l} {l' = l'} dA dt v _) rho fits =
    InvConv-cong {G = stripCtx G} {M = C.LApp (strip t) l} {N = C.LApp (strip t) l'}
      refl refl (Eq-sym (strip-lsubE (lsub1S l) A))
      (InvConv-LApp-lvl (strip A) (strip t) l l' rho fits (sound-Tm dt rho fits) (fits-level {G = G} l l' fits v))
  sound-CTm {G = G} (conv-GLam-equiv {c = c} {c' = c'} {A = A} {t = t} dG q dA dt) rho fits =
    InvConv-GLamEquiv {G = stripCtx G} {c = c} {c' = c'} {X = strip t} {Y = strip A} {rho = rho}
      (fits-equiv {G = G} fits q) (fits-equiv {G = G} fits (equivC-sym q))
      (\ v -> sound-Tm dt rho (fits-addC {G = G} c fits v))
  sound-CTm {TL = TL} {G = G} (conv-LApp-beta {A = A} {u = u} {l = l} dA du) rho fits =
    InvConv-cong {G = stripCtx G} {M = C.LApp (C.LLam (strip u)) l}
      refl (Eq-sym (strip-lsubE (lsub1S l) u)) (Eq-sym (strip-lsubE (lsub1S l) A))
      (InvConv-LApp-beta (strip A) (strip u) l rho fits
        (\ k -> sound-Tm du (extL rho (ldecT TL k)) (fits-addL {G = G} (ldecT TL k) fits)))
  sound-CTm {G = G} (conv-LApp-eta {A = A} {t = t} dA dt) rho fits =
    InvConv-cong {G = stripCtx G} {M = strip t} {T = C.LPi (strip A)} refl
      (Eq-cong (\ X -> C.LLam (C.LApp X (lvar zero))) (Eq-sym (strip-lsubE lwkS t)))
      refl
      (InvConv-LApp-eta (strip A) (strip t) rho fits (sound-Tm dt rho fits))
  sound-CTm (conv-cong-GLam-Ty dG dA _ dt) rho fits =
    let inv = sound-Tm (ty-GLam dG dA dt) rho fits
    in mkSigma inv (mkSigma inv (mkSigma (\ u ev -> ev) (\ u ev -> ev)))
  sound-CTm (conv-cong-LLam-Ty dG dA _ du) rho fits =
    let inv = sound-Tm (ty-LLam dG dA du) rho fits
    in mkSigma inv (mkSigma inv (mkSigma (\ u ev -> ev) (\ u ev -> ev)))
  sound-CTm (conv-cong-LApp-Ty {l = l} dA _ dt) rho fits =
    let inv = sound-Tm (ty-LApp {l = l} dA dt) rho fits
    in mkSigma inv (mkSigma inv (mkSigma (\ u ev -> ev) (\ u ev -> ev)))
  sound-CTm (conv-sym d) rho fits =
    let mkSigma iM (mkSigma iN (mkSigma f b)) = sound-CTm d rho fits
    in mkSigma iN (mkSigma iM (mkSigma b f))
  sound-CTm (conv-trans d1 d2) rho fits =
    let mkSigma iM (mkSigma _  (mkSigma f1 b1)) = sound-CTm d1 rho fits
        mkSigma _  (mkSigma iP (mkSigma f2 b2)) = sound-CTm d2 rho fits
    in mkSigma iM (mkSigma iP
         (mkSigma (\ u ev -> f2 u (f1 u ev)) (\ u ev -> b1 u (b2 u ev))))
  sound-CTm {G = G} {M = M} {N = N} {A = B} (conv-conv {A = A} d dAB) rho fits =
    let mkSigma iM (mkSigma iN (mkSigma f b)) = sound-CTm d rho fits
        fwdAB = fst (snd (snd (sound-CTy dAB rho fits)))
        tr : {X : C.Expr _} -> InvTyp (stripCtx G) X (strip A) rho
                            -> InvTyp (stripCtx G) X (strip B) rho
        tr inv u ev =
          let mkSigma u' (mkSigma a' (mkSigma le (mkSigma evX (mkSigma fm evA)))) = inv u ev
          in mkSigma u' (mkSigma a' (mkSigma le (mkSigma evX (mkSigma fm (fwdAB a' evA)))))
    in mkSigma (tr {X = strip M} iM) (mkSigma (tr {X = strip N} iN) (mkSigma f b))
  sound-CTm {G = G} (conv-cong-Pi {A = A} {A' = A'} {B = B} {B' = B'} {l = l} _ _ dA dB) rho fits =
    InvConv-Pi {L = l} (strip A) (strip A') (strip B) (strip B') rho fits
      (sound-CTm dA rho fits)
      (\ rho' x a fits' fm evA -> sound-CTm dB (extendEnv rho' x) (fitsE {G = G} {A = A} fits' fm evA))
  sound-CTm {G = G} (conv-cong-Lam-body {A = A} {B = B} {b = b} {b' = b'} dA dB _ db) rho fits =
    let bih = \ rho' x a fits' fm evA -> sound-CTm db (extendEnv rho' x) (fitsE {G = G} {A = A} fits' fm evA)
    in InvConv-Lam-body (strip A) (strip B) (strip b) (strip b') rho fits bih
         (InvTyp-Lam (strip A) (strip B) (strip b)
           (\ rho' x a fits' fm evA -> fst (bih rho' x a fits' fm evA)) rho fits)
         (InvTyp-Lam (strip A) (strip B) (strip b')
           (\ rho' x a fits' fm evA -> fst (snd (bih rho' x a fits' fm evA))) rho fits)
  sound-CTm {G = G} (conv-cong-Lam-Ty {A = A} {A' = A'} {B = B} {b = b} _ _ dA dB db) rho fits =
    let mkSigma _ (mkSigma _ (mkSigma fA bA)) = sound-CTy dA rho fits
    in InvConv-Lam-dom {G = stripCtx G} (strip A) (strip A') (strip b) (C.Pi (strip A) (strip B)) rho
         (InvTyp-Lam (strip A) (strip B) (strip b)
           (\ rho' x a fits' fm evA -> sound-Tm db (extendEnv rho' x) (fitsE {G = G} {A = A} fits' fm evA))
           rho fits)
         fA bA
  sound-CTm {G = G} (conv-cong-App-fun {A = A} {B = B} {c = c} {c' = c'} {a = a} dA dB dc da)
    rho fits =
    InvConv-cong {G = stripCtx G} {M = C.App (strip c) (strip a)} {N = C.App (strip c') (strip a)}
      refl refl (Eq-sym (strip-subst1 B a))
      (InvConv-App-fun (strip A) (strip B) (strip c) (strip c') (strip a) rho fits
        (sound-CTm dc rho fits) (sound-Tm da rho fits))
  sound-CTm {G = G} (conv-cong-App-arg {A = A} {B = B} {c = c} {a = a} {a' = a'} dA dB dc da _)
    rho fits =
    InvConv-cong {G = stripCtx G} {M = C.App (strip c) (strip a)} {N = C.App (strip c) (strip a')}
      refl refl (Eq-sym (strip-subst1 B a))
      (InvConv-App-arg (strip A) (strip B) (strip c) (strip a) (strip a') rho fits
        (sound-Tm dc rho fits) (sound-CTm da rho fits))
  sound-CTm {G = G} (conv-cong-App-Ty {A = A} {B = B} {c = c} {a = a} _ _ dA dB dc da) rho fits =
    let inv = InvTyp-cong {G = stripCtx G} {M = C.App (strip c) (strip a)} refl (Eq-sym (strip-subst1 B a))
                (InvTyp-App (strip A) (strip B) (strip c) (strip a) rho fits
                  (sound-Tm dc rho fits) (sound-Tm da rho fits))
    in mkSigma inv (mkSigma inv (mkSigma (\ u ev -> ev) (\ u ev -> ev)))
  sound-CTm {G = G} (conv-beta {A = A} {B = B} {b = b} {a = a} dA dB db da) rho fits =
    InvConv-cong {G = stripCtx G} {M = C.App (C.Lam (strip A) (strip b)) (strip a)} refl (Eq-sym (strip-subst1 b a)) (Eq-sym (strip-subst1 B a))
      (InvConv-beta (strip A) (strip B) (strip b) (strip a) rho fits
        (sound-Tm da rho fits)
        (\ rho' x a0 fits' fm evA -> sound-Tm db (extendEnv rho' x) (fitsE {G = G} {A = A} fits' fm evA)))
  sound-CTm {G = G} (conv-eta {A = A} {B = B} {c = c} dA dB dc) rho fits =
    InvConv-cong {G = stripCtx G} {M = strip c} {T = C.Pi (strip A) (strip B)} refl
      (Eq-cong (\ X -> C.Lam (strip A) (C.App X (C.Var fzero'))) (Eq-sym (strip-wk c)))
      refl
      (InvConv-eta (strip A) (strip B) (strip c) rho fits (sound-Tm dc rho fits) invL)
    where
      fzero' = C.fzero
      invL : InvTyp (stripCtx G)
               (C.Lam (strip A) (C.App (C.wkExpr (strip c)) (C.Var C.fzero)))
               (C.Pi (strip A) (strip B)) rho
      invL = InvTyp-Lam (strip A) (strip B) (C.App (C.wkExpr (strip c)) (C.Var C.fzero))
        (\ rho' x a fits' fm evA ->
           let fx = fitsE {G = G} {A = A} fits' fm evA
           in InvTyp-cong {G = C.extend (stripCtx G) (strip A)}
                {M = C.App (C.wkExpr (strip c)) (C.Var C.fzero)}
                refl (subst1-liftWk-cancel (strip B))
                (InvTyp-App {G = C.extend (stripCtx G) (strip A)} (C.wkExpr (strip A)) (C.renExpr (C.liftRen C.wkRen) (strip B))
                  (C.wkExpr (strip c)) (C.Var C.fzero) (extendEnv rho' x) fx
                  (InvTyp-wk {G = stripCtx G} {C = strip A} {M = strip c}
                     {T = C.Pi (strip A) (strip B)} {rho = rho'} {x = x} (sound-Tm dc rho' fits'))
                  (InvTyp-var {G = C.extend (stripCtx G) (strip A)} (extendEnv rho' x) fx C.fzero)))
        rho fits
