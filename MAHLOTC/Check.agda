{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOTC/Check.agda
--
-- Decidable type checking (second half of (T3)), relative to TCHyp
-- (decidable type equality and type head views, from decidable
-- conversion) and InjHyp:
--
--   decHasType : WfCtx G -> Chk t -> IsType G C -> Dec (HasType G t C)
--   decIsType  : WfCtx G -> ChkTy A -> Dec (IsType G A)
--   decWfCtx   : ChkCtx G -> Dec (WfCtx G)
--
-- for the bidirectional fragment (MAHLOTC/Frag.agda), which contains
-- every beta-normal term.  infer / check / isType are defined by
-- structural recursion on terms; each case is a rule of MAHLOTC/Rules.
------------------------------------------------------------------------

open import MAHLOTC.Base

module MAHLOTC.Check (H : TCHyp) where

open import MAHLO.Syntax
open import MAHLO.Typing
open TCHyp H
open import MAHLOINJ.Inversion.Inv inj
open import MAHLOINJ.Syntax.Wf using (wfTy ; NatTy)
open import MAHLOINJ.Syntax.Presup using (pTm)
open import MAHLOTC.Frag
open import MAHLOTC.Lemmas inj
open import MAHLOTC.Res H
open import MAHLOTC.Rules H

------------------------------------------------------------------------
-- Is a family argument of the form  \x:A.B ?
------------------------------------------------------------------------

data FamV {n : Num} (F : Expr n) : Set where
  famLam : (A : Expr n) (B : Expr (suc n)) -> Eq F (Lam A B) -> FamV F
  famNo  : ((A : Expr n) (B : Expr (suc n)) -> Eq F (Lam A B) -> Empty) -> FamV F

famV : {n : Num} (F : Expr n) -> FamV F
famV (Var y0) = famNo (\ A B ())
famV (Lam A B) = famLam A B refl
famV (App y0 y1) = famNo (\ A B ())
famV (Pi y0 y1) = famNo (\ A B ())
famV (Sigma y0 y1) = famNo (\ A B ())
famV (Pair y0 y1) = famNo (\ A B ())
famV (Fst y0) = famNo (\ A B ())
famV (Snd y0) = famNo (\ A B ())
famV Nat = famNo (\ A B ())
famV Zero = famNo (\ A B ())
famV (Suc y0) = famNo (\ A B ())
famV (Rec y0 y1 y2 y3) = famNo (\ A B ())
famV V = famNo (\ A B ())
famV (Ucode y0 y1) = famNo (\ A B ())
famV (Fhat y0 y1 y2 y3) = famNo (\ A B ())
famV (Ghat y0 y1 y2 y3 y4) = famNo (\ A B ())

private
  -- the components of a checkable Pi/Sigma type
  piParts : {n : Num} {A A' : Expr n} {B : Expr (suc n)} ->
            ChkTy (Pi A (Lam A' B)) -> ChkTy A * ChkTy B
  piParts (inl (inl (iA , cB))) = inl (inl iA) , inl cB
  piParts (inl (inr (cA , cB))) = inl cA , inl cB
  piParts (inr (tA , tB)) = tA , tB

  sigParts : {n : Num} {A A' : Expr n} {B : Expr (suc n)} ->
             ChkTy (Sigma A (Lam A' B)) -> ChkTy A * ChkTy B
  sigParts (inl (inl (iA , cB))) = inl (inl iA) , inl cB
  sigParts (inl (inr (cA , cB))) = inl cA , inl cB
  sigParts (inr (tA , tB)) = tA , tB

------------------------------------------------------------------------
-- The checker
------------------------------------------------------------------------

mutual
  infer : {n : Num} (G : Ctx n) -> WfCtx G -> (t : Expr n) -> Inf t -> Res G t
  infer G w (Var i) _ = varRes w i
  infer G w (Lam A b) (cA , ib) =
    lamRes w (isType G w A cA) (\ hA -> infer (extend G A) (wf-extend hA) b ib)
  infer G w (App t a) (it , ca) = appRes w (infer G w t it) (check G w a ca)
  infer G w (Pi A F) (iA , fF) = h (famV F) fF
    where
      h : FamV F -> FamF F -> Res G (Pi A F)
      h (famNo k) _ = nilRes (\ C x -> k _ _ (PiInv.eF (invPi x)))
      h (famLam A' B refl) cB = h2 (decExpr A' A)
        where
          h2 : Dec (Eq A' A) -> Res G (Pi A (Lam A' B))
          h2 (yes refl) = piRes w (infer G w A iA) (\ hA -> check (extend G A) (wf-extend hA) B cB)
          h2 (no k) = nilRes (\ C x -> k (fst (lam-inj (PiInv.eF (invPi x)))))
  infer G w (Sigma A F) (iA , fF) = h (famV F) fF
    where
      h : FamV F -> FamF F -> Res G (Sigma A F)
      h (famNo k) _ = nilRes (\ C x -> k _ _ (PiInv.eF (invSigma x)))
      h (famLam A' B refl) cB = h2 (decExpr A' A)
        where
          h2 : Dec (Eq A' A) -> Res G (Sigma A (Lam A' B))
          h2 (yes refl) = sigRes w (infer G w A iA) (\ hA -> check (extend G A) (wf-extend hA) B cB)
          h2 (no k) = nilRes (\ C x -> k (fst (lam-inj (PiInv.eF (invSigma x)))))
  infer G w (Pair a b) ()
  infer G w (Fst t) it = fstRes w (infer G w t it)
  infer G w (Snd t) it = sndRes w (infer G w t it)
  infer G w Nat ()
  infer G w Zero _ = zeroRes w
  infer G w (Suc t) ct = sucRes w (check G w t ct)
  infer G w (Rec F z s k) (mF , (cz , (cs , ck))) = h (famV F) mF
    where
      h : FamV F -> MotF F -> Res G (Rec F z s k)
      h (famNo kF) _ = nilRes (\ C x -> kF _ _ (RecInv.eF (invRec x)))
      h (famLam A' C0 refl) mC = h2 (decExpr A' Nat)
        where
          h2 : Dec (Eq A' Nat) -> Res G (Rec (Lam A' C0) z s k)
          h2 (yes refl) =
            recRes w (isType (extend G Nat) (wf-extend (NatTy w)) C0 mC)
                   (check G w z cz) (check G w s cs) (check G w k ck)
          h2 (no kA) = nilRes (\ C x -> kA (fst (lam-inj (RecInv.eF (invRec x)))))
  infer G w V _ = vRes w
  infer G w (Ucode f g) (cf , cg) = ucodeRes w (check G w f cf) (check G w g cg)
  infer G w (Fhat f g A F) (cf , (cg , (cA , fF))) = h (famV F) fF
    where
      h : FamV F -> FamF F -> Res G (Fhat f g A F)
      h (famNo k) _ = nilRes (\ C x -> k _ _ (FhatInv.eF (invFhat x)))
      h (famLam A' B refl) cB = h2 (decExpr A' A)
        where
          h2 : Dec (Eq A' A) -> Res G (Fhat f g A (Lam A' B))
          h2 (yes refl) = fhatRes w (check G w f cf) (check G w g cg) (check G w A cA)
                                  (\ hA -> check (extend G A) (wf-extend hA) B cB)
          h2 (no k) = nilRes (\ C x -> k (fst (lam-inj (FhatInv.eF (invFhat x)))))
  infer G w (Ghat f g A F c) (cf , (cg , (cA , (fF , cc)))) = h (famV F) fF
    where
      h : FamV F -> FamF F -> Res G (Ghat f g A F c)
      h (famNo k) _ = nilRes (\ C x -> k _ _ (GhatInv.eF (invGhat x)))
      h (famLam A' B refl) cB = h2 (decExpr A' A)
        where
          h2 : Dec (Eq A' A) -> Res G (Ghat f g A (Lam A' B) c)
          h2 (yes refl) = ghatRes w (check G w f cf) (check G w g cg) (check G w A cA)
                                  (\ hA -> check (extend G A) (wf-extend hA) B cB) (check G w c cc)
          h2 (no k) = nilRes (\ C x -> k (fst (lam-inj (GhatInv.eF (invGhat x)))))

  check : {n : Num} (G : Ctx n) -> WfCtx G -> (t : Expr n) -> Chk t -> Chkr G t
  check G w t (inl it) C hC = checkRes hC (infer G w t it)
  check G w t (inr co) C hC = chkOnly G w t co C hC

  chkOnly : {n : Num} (G : Ctx n) -> WfCtx G -> (t : Expr n) -> ChkOnly t -> Chkr G t
  chkOnly G w (Lam A b) (cA , cb) C hC =
    lamChk w (isType G w A cA) (\ hA -> check (extend G A) (wf-extend hA) b cb) C hC
  chkOnly G w (Pair a b) (ca , cb) C hC = pairChk w (check G w a ca) (check G w b cb) C hC
  chkOnly G w Nat _ C hC = natChk w C hC
  chkOnly G w (Pi A F) (cA , fF) C hC = h (famV F) fF
    where
      h : FamV F -> FamF F -> Dec (HasType G (Pi A F) C)
      h (famNo k) _ = no (\ x -> k _ _ (PiInv.eF (invPi x)))
      h (famLam A' B refl) cB = h2 (decExpr A' A)
        where
          h2 : Dec (Eq A' A) -> Dec (HasType G (Pi A (Lam A' B)) C)
          h2 (yes refl) = piChk w (check G w A cA) (\ hA -> check (extend G A) (wf-extend hA) B cB) C hC
          h2 (no k) = no (\ x -> k (fst (lam-inj (PiInv.eF (invPi x)))))
  chkOnly G w (Sigma A F) (cA , fF) C hC = h (famV F) fF
    where
      h : FamV F -> FamF F -> Dec (HasType G (Sigma A F) C)
      h (famNo k) _ = no (\ x -> k _ _ (PiInv.eF (invSigma x)))
      h (famLam A' B refl) cB = h2 (decExpr A' A)
        where
          h2 : Dec (Eq A' A) -> Dec (HasType G (Sigma A (Lam A' B)) C)
          h2 (yes refl) = sigChk w (check G w A cA) (\ hA -> check (extend G A) (wf-extend hA) B cB) C hC
          h2 (no k) = no (\ x -> k (fst (lam-inj (PiInv.eF (invSigma x)))))
  chkOnly G w (Var y0) () C hC
  chkOnly G w (App y0 y1) () C hC
  chkOnly G w (Fst y0) () C hC
  chkOnly G w (Snd y0) () C hC
  chkOnly G w Zero () C hC
  chkOnly G w (Suc y0) () C hC
  chkOnly G w (Rec y0 y1 y2 y3) () C hC
  chkOnly G w V () C hC
  chkOnly G w (Ucode y0 y1) () C hC
  chkOnly G w (Fhat y0 y1 y2 y3) () C hC
  chkOnly G w (Ghat y0 y1 y2 y3 y4) () C hC

  isType : {n : Num} (G : Ctx n) -> WfCtx G -> (A : Expr n) -> ChkTy A -> Dec (IsType G A)
  isType G w V _ = yes (isty-V w)
  isType G w (Pi A1 F) cA = h (famV F) cA
    where
      h : FamV F -> ChkTy (Pi A1 F) -> Dec (IsType G (Pi A1 F))
      h (famNo k) _ = no (\ x -> k _ _ (snd (piShape x refl)))
      h (famLam A' B refl) c = h2 (decExpr A' A1)
        where
          ps = piParts {A = A1} {A' = A'} {B = B} c
          h2 : Dec (Eq A' A1) -> Dec (IsType G (Pi A1 (Lam A' B)))
          h2 (no k) = no (\ x -> k (fst (lam-inj (snd (piShape x refl)))))
          h2 (yes refl) = h3 (isType G w A1 (fst ps))
            where
              h3 : Dec (IsType G A1) -> Dec (IsType G (PiB A1 B))
              h3 (no k) = no (\ x -> k (fst (piTyInv x)))
              h3 (yes hA) = h4 (isType (extend G A1) (wf-extend hA) B (snd ps))
                where
                  h4 : Dec (IsType (extend G A1) B) -> Dec (IsType G (PiB A1 B))
                  h4 (no k) = no (\ x -> k (snd (piTyInv x)))
                  h4 (yes hB) = yes (isty-Pi hA hB)
  isType G w (Sigma A1 F) cA = h (famV F) cA
    where
      h : FamV F -> ChkTy (Sigma A1 F) -> Dec (IsType G (Sigma A1 F))
      h (famNo k) _ = no (\ x -> k _ _ (snd (sigShape x refl)))
      h (famLam A' B refl) c = h2 (decExpr A' A1)
        where
          ps = sigParts {A = A1} {A' = A'} {B = B} c
          h2 : Dec (Eq A' A1) -> Dec (IsType G (Sigma A1 (Lam A' B)))
          h2 (no k) = no (\ x -> k (fst (lam-inj (snd (sigShape x refl)))))
          h2 (yes refl) = h3 (isType G w A1 (fst ps))
            where
              h3 : Dec (IsType G A1) -> Dec (IsType G (SigmaB A1 B))
              h3 (no k) = no (\ x -> k (fst (sigTyInv x)))
              h3 (yes hA) = h4 (isType (extend G A1) (wf-extend hA) B (snd ps))
                where
                  h4 : Dec (IsType (extend G A1) B) -> Dec (IsType G (SigmaB A1 B))
                  h4 (no k) = no (\ x -> k (snd (sigTyInv x)))
                  h4 (yes hB) = yes (isty-Sigma hA hB)
  isType G w (Var y0) (inl c) = elDec (check G w (Var y0) c V (isty-V w))
    where
      elDec : Dec (HasType G (Var y0) V) -> Dec (IsType G (Var y0))
      elDec (yes h) = yes (isty-el h)
      elDec (no k) = no (\ { (isty-el h) -> k h })
  isType G w (Var y0) (inr ())
  isType G w (Lam y0 y1) (inl c) = elDec (check G w (Lam y0 y1) c V (isty-V w))
    where
      elDec : Dec (HasType G (Lam y0 y1) V) -> Dec (IsType G (Lam y0 y1))
      elDec (yes h) = yes (isty-el h)
      elDec (no k) = no (\ { (isty-el h) -> k h })
  isType G w (Lam y0 y1) (inr ())
  isType G w (App y0 y1) (inl c) = elDec (check G w (App y0 y1) c V (isty-V w))
    where
      elDec : Dec (HasType G (App y0 y1) V) -> Dec (IsType G (App y0 y1))
      elDec (yes h) = yes (isty-el h)
      elDec (no k) = no (\ { (isty-el h) -> k h })
  isType G w (App y0 y1) (inr ())
  isType G w (Pair y0 y1) (inl c) = elDec (check G w (Pair y0 y1) c V (isty-V w))
    where
      elDec : Dec (HasType G (Pair y0 y1) V) -> Dec (IsType G (Pair y0 y1))
      elDec (yes h) = yes (isty-el h)
      elDec (no k) = no (\ { (isty-el h) -> k h })
  isType G w (Pair y0 y1) (inr ())
  isType G w (Fst y0) (inl c) = elDec (check G w (Fst y0) c V (isty-V w))
    where
      elDec : Dec (HasType G (Fst y0) V) -> Dec (IsType G (Fst y0))
      elDec (yes h) = yes (isty-el h)
      elDec (no k) = no (\ { (isty-el h) -> k h })
  isType G w (Fst y0) (inr ())
  isType G w (Snd y0) (inl c) = elDec (check G w (Snd y0) c V (isty-V w))
    where
      elDec : Dec (HasType G (Snd y0) V) -> Dec (IsType G (Snd y0))
      elDec (yes h) = yes (isty-el h)
      elDec (no k) = no (\ { (isty-el h) -> k h })
  isType G w (Snd y0) (inr ())
  isType G w Nat (inl c) = elDec (check G w Nat c V (isty-V w))
    where
      elDec : Dec (HasType G Nat V) -> Dec (IsType G Nat)
      elDec (yes h) = yes (isty-el h)
      elDec (no k) = no (\ { (isty-el h) -> k h })
  isType G w Nat (inr ())
  isType G w Zero (inl c) = elDec (check G w Zero c V (isty-V w))
    where
      elDec : Dec (HasType G Zero V) -> Dec (IsType G Zero)
      elDec (yes h) = yes (isty-el h)
      elDec (no k) = no (\ { (isty-el h) -> k h })
  isType G w Zero (inr ())
  isType G w (Suc y0) (inl c) = elDec (check G w (Suc y0) c V (isty-V w))
    where
      elDec : Dec (HasType G (Suc y0) V) -> Dec (IsType G (Suc y0))
      elDec (yes h) = yes (isty-el h)
      elDec (no k) = no (\ { (isty-el h) -> k h })
  isType G w (Suc y0) (inr ())
  isType G w (Rec y0 y1 y2 y3) (inl c) = elDec (check G w (Rec y0 y1 y2 y3) c V (isty-V w))
    where
      elDec : Dec (HasType G (Rec y0 y1 y2 y3) V) -> Dec (IsType G (Rec y0 y1 y2 y3))
      elDec (yes h) = yes (isty-el h)
      elDec (no k) = no (\ { (isty-el h) -> k h })
  isType G w (Rec y0 y1 y2 y3) (inr ())
  isType G w (Ucode y0 y1) (inl c) = elDec (check G w (Ucode y0 y1) c V (isty-V w))
    where
      elDec : Dec (HasType G (Ucode y0 y1) V) -> Dec (IsType G (Ucode y0 y1))
      elDec (yes h) = yes (isty-el h)
      elDec (no k) = no (\ { (isty-el h) -> k h })
  isType G w (Ucode y0 y1) (inr ())
  isType G w (Fhat y0 y1 y2 y3) (inl c) = elDec (check G w (Fhat y0 y1 y2 y3) c V (isty-V w))
    where
      elDec : Dec (HasType G (Fhat y0 y1 y2 y3) V) -> Dec (IsType G (Fhat y0 y1 y2 y3))
      elDec (yes h) = yes (isty-el h)
      elDec (no k) = no (\ { (isty-el h) -> k h })
  isType G w (Fhat y0 y1 y2 y3) (inr ())
  isType G w (Ghat y0 y1 y2 y3 y4) (inl c) = elDec (check G w (Ghat y0 y1 y2 y3 y4) c V (isty-V w))
    where
      elDec : Dec (HasType G (Ghat y0 y1 y2 y3 y4) V) -> Dec (IsType G (Ghat y0 y1 y2 y3 y4))
      elDec (yes h) = yes (isty-el h)
      elDec (no k) = no (\ { (isty-el h) -> k h })
  isType G w (Ghat y0 y1 y2 y3 y4) (inr ())

------------------------------------------------------------------------
-- Well-formed contexts
------------------------------------------------------------------------

decWfCtx : {n : Num} (G : Ctx n) -> ChkCtx G -> Dec (WfCtx G)
decWfCtx empty _ = yes wf-empty
decWfCtx (extend G A) (cG , cA) = h (decWfCtx G cG)
  where
    h : Dec (WfCtx G) -> Dec (WfCtx (extend G A))
    h (no k) = no (\ { (wf-extend hA) -> k (wfTy hA) })
    h (yes w) = h2 (isType G w A cA)
      where
        h2 : Dec (IsType G A) -> Dec (WfCtx (extend G A))
        h2 (yes hA) = yes (wf-extend hA)
        h2 (no k) = no (\ { (wf-extend hA) -> k hA })

------------------------------------------------------------------------
-- The theorems
------------------------------------------------------------------------

-- (T3), type checking, for the bidirectional fragment
decHasType : {n : Num} {G : Ctx n} {t C : Expr n} -> WfCtx G -> Chk t -> IsType G C ->
             Dec (HasType G t C)
decHasType {G = G} {t} {C} w ct hC = check G w t ct C hC

decIsType : {n : Num} {G : Ctx n} {A : Expr n} -> WfCtx G -> ChkTy A -> Dec (IsType G A)
decIsType {G = G} {A} w cA = isType G w A cA

-- without assuming C is a type
decHasType' : {n : Num} {G : Ctx n} {t C : Expr n} -> WfCtx G -> Chk t -> ChkTy C ->
              Dec (HasType G t C)
decHasType' {G = G} {t} {C} w ct cC = h (isType G w C cC)
  where
    h : Dec (IsType G C) -> Dec (HasType G t C)
    h (yes hC) = check G w t ct C hC
    h (no k) = no (\ x -> k (pTm x))
