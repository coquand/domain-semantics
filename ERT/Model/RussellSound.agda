{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.Model.RussellSound
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

module ERT.Model.RussellSound where

open import ERT.Dom.Basic using (EqL-refl)
import ERT.Dom.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Sigma ; mkSigma ; fst ; snd ; Pair ;
              Eq ; refl ; Eq-transport ; Eq-sym ; Eq-cong ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode)
open import ERT.Dom.Kernel using (FinMem)
import ERT.RussellSyntax as R
open import ERT.RussellTyping
import ERT.Model.Core as C
open import ERT.Model.Eval using (EnvApprox ; extendEnv ; EvalRel)
open import ERT.Model.SoundnessLemmas using (Fits ; InvTyp ; InvConv ;
  InvTyp-Lam ; InvTyp-App ; InvTyp-Pi ; InvConv-beta ; InvConv-App-fun ; InvConv-App-arg)
open import ERT.Model.SoundnessExtra
open import ERT.Model.Strip

------------------------------------------------------------------------
-- Transport along syntactic equalities
------------------------------------------------------------------------

InvTyp-cong : {n : Nat} {G : C.Ctx n} {M M' T T' : C.Expr n} {rho : EnvApprox n}
  -> Eq M M' -> Eq T T' -> InvTyp G M T rho -> InvTyp G M' T' rho
InvTyp-cong refl refl inv = inv

InvConv-cong : {n : Nat} {G : C.Ctx n} {M M' N N' T T' : C.Expr n} {rho : EnvApprox n}
  -> Eq M M' -> Eq N N' -> Eq T T' -> InvConv G M N T rho -> InvConv G M' N' T' rho
InvConv-cong refl refl refl inv = inv

------------------------------------------------------------------------
-- Evaluation of products respects conversion of the components
------------------------------------------------------------------------

Pi-fwd : {n : Nat} (A A' : C.Expr n) (B B' : C.Expr (suc n))
  (rho : EnvApprox n) -> (u : FinEl) ->
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

-- Congruence for products, at any level, from the component invariants.
InvConv-Pi : {n : Nat} {G : C.Ctx n} {l : Nat} (A A' : C.Expr n) (B B' : C.Expr (suc n))
  (rho : EnvApprox n) -> Fits G rho
  -> InvConv G A A' (C.U l) rho
  -> ((rho' : EnvApprox n) (x a : FinEl) -> Fits G rho' -> FinMem x a ->
        EvalRel A rho' a -> InvConv (C.extend G A) B B' (C.U l) (extendEnv rho' x))
  -> InvConv G (C.Pi A B) (C.Pi A' B') (C.U l) rho
InvConv-Pi A A' B B' rho fits cA cB =
  let mkSigma invA (mkSigma invA' (mkSigma fwdA bwdA)) = cA
      fwd = \ u ev -> Pi-fwd A A' B B' rho u fwdA
              (\ x a0 fm evA w -> fst (snd (snd (cB rho x a0 fits fm evA))) w) ev
      bwd = \ u ev -> Pi-fwd A' A B' B rho u bwdA
              (\ x a0 fm evA' w ->
                 snd (snd (snd (cB rho x a0 fits fm (bwdA a0 evA')))) w) ev
      invL = InvTyp-Pi A B rho fits invA
               (\ x a0 fm evA -> fst (cB rho x a0 fits fm evA))
      invR = InvTyp-Pi A' B' rho fits invA'
               (\ x a0 fm evA' -> fst (snd (cB rho x a0 fits fm (bwdA a0 evA'))))
  in mkSigma invL (mkSigma invR (mkSigma fwd bwd))

------------------------------------------------------------------------
-- The soundness theorem
------------------------------------------------------------------------

-- Fits for an extended context.
fitsE : {n : Nat} {G : Ctx n} {A : R.Expr n} {rho : EnvApprox n} {x a : FinEl}
  -> Fits (stripCtx G) rho -> FinMem x a -> EvalRel (strip A) rho a
  -> Fits (stripCtx (extend G A)) (extendEnv rho x)
fitsE {a = a} fits fm evA = mkSigma fits (mkSigma a (mkSigma fm evA))

mutual

  sound-Ty : {n : Nat} {G : Ctx n} {A : R.Expr n}
    -> IsType G A -> (rho : EnvApprox n) -> Fits (stripCtx G) rho
    -> InvTyp (stripCtx G) (strip A) (C.U 0) rho
  sound-Ty {G = G} {A = A} (is-Ty-from-U {l = l} d) rho fits =
    InvTyp-U-lvl {G = stripCtx G} {M = strip A} l 0 (sound-Tm d rho fits)

  sound-Tm : {n : Nat} {G : Ctx n} {M A : R.Expr n}
    -> HasType G M A -> (rho : EnvApprox n) -> Fits (stripCtx G) rho
    -> InvTyp (stripCtx G) (strip M) (strip A) rho
  sound-Tm {G = G} (ty-var {i = i} wf) rho fits =
    InvTyp-cong {G = stripCtx G} {M = C.Var i} {M' = C.Var i} refl (Eq-sym (strip-lookup G i))
      (InvTyp-var rho fits i)
  sound-Tm (ty-conv dM dAB) rho fits u ev =
    let mkSigma u' (mkSigma a' (mkSigma le (mkSigma evM (mkSigma fm evA)))) =
          sound-Tm dM rho fits u ev
        fwdAB = fst (snd (snd (sound-CTy dAB rho fits)))
    in mkSigma u' (mkSigma a' (mkSigma le (mkSigma evM (mkSigma fm (fwdAB a' evA)))))
  sound-Tm (ty-U {l = l} wf) rho fits u ev =
    mkSigma (UCode l) (mkSigma (UCode (suc l))
      (mkSigma (snd ev) (mkSigma (mkSigma tt (EqL-refl l))
        (mkSigma tt (mkSigma tt (EqL-refl (suc l)))))))
  sound-Tm {G = G} {M = M} (ty-cum {l = l} d) rho fits =
    InvTyp-U-lvl {G = stripCtx G} {M = strip M} l (suc l) (sound-Tm d rho fits)
  sound-Tm (ty-Pi {A = A} {B = B} dA dB) rho fits =
    InvTyp-Pi (strip A) (strip B) rho fits (sound-Tm dA rho fits)
      (\ x a fm evA -> sound-Tm dB (extendEnv rho x) (fitsE fits fm evA))
  sound-Tm (ty-Lam {A = A} {B = B} {b = b} dA dB db) rho fits =
    InvTyp-Lam (strip A) (strip B) (strip b)
      (\ rho' x a fits' fm evA -> sound-Tm db (extendEnv rho' x) (fitsE fits' fm evA))
      rho fits
  sound-Tm {G = G} (ty-App {A = A} {B = B} {c = c} {a = a} dA dB dc da) rho fits =
    InvTyp-cong {G = stripCtx G} {M = C.App (strip c) (strip a)} {M' = C.App (strip c) (strip a)}
      refl (Eq-sym (strip-subst1 B a))
      (InvTyp-App (strip A) (strip B) (strip c) (strip a) rho fits
        (sound-Tm dc rho fits) (sound-Tm da rho fits))

  sound-CTy : {n : Nat} {G : Ctx n} {A B : R.Expr n}
    -> ConvTy G A B -> (rho : EnvApprox n) -> Fits (stripCtx G) rho
    -> InvConv (stripCtx G) (strip A) (strip B) (C.U 0) rho
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
  sound-CTy (conv-Ty-Pi {A = A} {A' = A'} {B = B} {B' = B'} _ _ dA dB) rho fits =
    InvConv-Pi (strip A) (strip A') (strip B) (strip B') rho fits
      (sound-CTy dA rho fits)
      (\ rho' x a fits' fm evA -> sound-CTy dB (extendEnv rho' x) (fitsE fits' fm evA))
  sound-CTy {G = G} {A = A} {B = B} (conv-Ty-from-U {l = l} d) rho fits =
    let mkSigma iA (mkSigma iB (mkSigma f b)) = sound-CTm d rho fits
    in mkSigma (InvTyp-U-lvl {G = stripCtx G} {M = strip A} l 0 iA)
         (mkSigma (InvTyp-U-lvl {G = stripCtx G} {M = strip B} l 0 iB) (mkSigma f b))

  sound-CTm : {n : Nat} {G : Ctx n} {M N A : R.Expr n}
    -> ConvTm G M N A -> (rho : EnvApprox n) -> Fits (stripCtx G) rho
    -> InvConv (stripCtx G) (strip M) (strip N) (strip A) rho
  sound-CTm (conv-refl dM) rho fits =
    let inv = sound-Tm dM rho fits
    in mkSigma inv (mkSigma inv (mkSigma (\ u ev -> ev) (\ u ev -> ev)))
  sound-CTm (conv-sym d) rho fits =
    let mkSigma iM (mkSigma iN (mkSigma f b)) = sound-CTm d rho fits
    in mkSigma iN (mkSigma iM (mkSigma b f))
  sound-CTm (conv-trans d1 d2) rho fits =
    let mkSigma iM (mkSigma _  (mkSigma f1 b1)) = sound-CTm d1 rho fits
        mkSigma _  (mkSigma iP (mkSigma f2 b2)) = sound-CTm d2 rho fits
    in mkSigma iM (mkSigma iP
         (mkSigma (\ u ev -> f2 u (f1 u ev)) (\ u ev -> b1 u (b2 u ev))))
  sound-CTm {G = G} {A = B} (conv-conv {A = A} d dAB) rho fits =
    let mkSigma iM (mkSigma iN (mkSigma f b)) = sound-CTm d rho fits
        fwdAB = fst (snd (snd (sound-CTy dAB rho fits)))
        tr : {X : C.Expr _} -> InvTyp (stripCtx G) X (strip A) rho
                            -> InvTyp (stripCtx G) X (strip B) rho
        tr inv u ev =
          let mkSigma u' (mkSigma a' (mkSigma le (mkSigma evX (mkSigma fm evA)))) = inv u ev
          in mkSigma u' (mkSigma a' (mkSigma le (mkSigma evX (mkSigma fm (fwdAB a' evA)))))
    in mkSigma (tr iM) (mkSigma (tr iN) (mkSigma f b))
  sound-CTm {G = G} {M = M} {N = N} (conv-cum {l = l} d) rho fits =
    let mkSigma iM (mkSigma iN (mkSigma f b)) = sound-CTm d rho fits
    in mkSigma (InvTyp-U-lvl {G = stripCtx G} {M = strip M} l (suc l) iM)
         (mkSigma (InvTyp-U-lvl {G = stripCtx G} {M = strip N} l (suc l) iN) (mkSigma f b))
  sound-CTm (conv-cong-Pi {A = A} {A' = A'} {B = B} {B' = B'} _ _ dA dB) rho fits =
    InvConv-Pi (strip A) (strip A') (strip B) (strip B') rho fits
      (sound-CTm dA rho fits)
      (\ rho' x a fits' fm evA -> sound-CTm dB (extendEnv rho' x) (fitsE fits' fm evA))
  sound-CTm (conv-cong-Lam-body {A = A} {B = B} {b = b} {b' = b'} dA dB _ db) rho fits =
    let bih = \ rho' x a fits' fm evA -> sound-CTm db (extendEnv rho' x) (fitsE fits' fm evA)
    in InvConv-Lam-body (strip A) (strip B) (strip b) (strip b') rho fits bih
         (InvTyp-Lam (strip A) (strip B) (strip b)
           (\ rho' x a fits' fm evA -> fst (bih rho' x a fits' fm evA)) rho fits)
         (InvTyp-Lam (strip A) (strip B) (strip b')
           (\ rho' x a fits' fm evA -> fst (snd (bih rho' x a fits' fm evA))) rho fits)
  sound-CTm {G = G} (conv-cong-Lam-Ty {A = A} {A' = A'} {B = B} {b = b} _ _ dA dB db) rho fits =
    let mkSigma _ (mkSigma _ (mkSigma fA bA)) = sound-CTy dA rho fits
    in InvConv-Lam-dom {G = stripCtx G} (strip A) (strip A') (strip b) (C.Pi (strip A) (strip B)) rho
         (InvTyp-Lam (strip A) (strip B) (strip b)
           (\ rho' x a fits' fm evA -> sound-Tm db (extendEnv rho' x) (fitsE fits' fm evA))
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
        (\ rho' x a0 fits' fm evA -> sound-Tm db (extendEnv rho' x) (fitsE fits' fm evA)))
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
           let fx = fitsE {A = A} fits' fm evA
           in InvTyp-cong {G = C.extend (stripCtx G) (strip A)}
                {M = C.App (C.wkExpr (strip c)) (C.Var C.fzero)}
                refl (subst1-liftWk-cancel (strip B))
                (InvTyp-App (C.wkExpr (strip A)) (C.renExpr (C.liftRen C.wkRen) (strip B))
                  (C.wkExpr (strip c)) (C.Var C.fzero) (extendEnv rho' x) fx
                  (InvTyp-wk {G = stripCtx G} {C = strip A} {M = strip c}
                     {T = C.Pi (strip A) (strip B)} (sound-Tm dc rho' fits'))
                  (InvTyp-var (extendEnv rho' x) fx C.fzero)))
        rho fits
