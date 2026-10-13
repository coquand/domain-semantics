{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/ValPi.agda
--
-- Validity of the rules for Pi and Sigma (as types), lambda,
-- application, pairs and projections, beta, eta (funext) and
-- surjective pairing.  "Verbatim as in Abel--Coquand" (plan Sec. 6.4).
------------------------------------------------------------------------

open import MAHLO.Basic
open import MAHLO.TermModel
import MAHLO.Model
import MAHLO.Fixpoint

module MAHLO.ValPi (TM : TermModel) (M : MAHLO.Model.Model TM)
                   (Fx : MAHLO.Fixpoint.Fixpoint TM) where

open TermModel TM
open MAHLO.Model TM using (Env ; cons)
open MAHLO.Model.Model M
open import MAHLO.Candidate TM
open import MAHLO.Validity TM M Fx
open import MAHLO.Syntax
  renaming (Pi to tPi ; Sigma to tSigma ; Nat to tNat ; V to tV)
open import MAHLO.Typing

private
  lamE : {n : Num} {rho : Env n} (A : Expr n) (B : Expr (suc n)) (v : D) ->
         den B (cons rho v) ~~ app (den (Lam A B) rho) v
  lamE A B v = ~~-sym (den-Lam A B v)

  -- den (subst1 B a) rho  =  app (den (Lam A B) rho) (den a rho)
  s1E : {n : Num} (rho : Env n) (A : Expr n) (B : Expr (suc n)) (a : Expr n) ->
        den (subst1 B a) rho ~~ app (den (Lam A B) rho) (den a rho)
  s1E rho A B a = ~~-trans (den-subst1 rho B a) (lamE A B (den a rho))

  piE : {n : Num} {rho : Env n} (A : Expr n) (B : Expr (suc n)) ->
        den (PiB A B) rho ~~ Pi (den A rho) (den (Lam A B) rho)
  piE A B = den-Pi A (Lam A B)

  sigE : {n : Num} {rho : Env n} (A : Expr n) (B : Expr (suc n)) ->
         den (SigmaB A B) rho ~~ Sig (den A rho) (den (Lam A B) rho)
  sigE A B = den-Sigma A (Lam A B)

module _ {n : Num} {G : Ctx n} where

  ----------------------------------------------------------------------
  -- types
  ----------------------------------------------------------------------

  v-isty-Pi : {A : Expr n} {B : Expr (suc n)} ->
              ValTy G A -> ValTy (extend G A) B -> ValTy G (PiB A B)
  v-isty-Pi {A} {B} hA hB e =
    piTy (piE A B) (piE A B) (TyV.ty (hA e))
      (\ v v' i -> tyvTr (lamE A B v) (lamE A B v') (hB (envCons e (tmv _ (TyV.ty (hA e)) i))))

  v-isty-Sigma : {A : Expr n} {B : Expr (suc n)} ->
                 ValTy G A -> ValTy (extend G A) B -> ValTy G (SigmaB A B)
  v-isty-Sigma {A} {B} hA hB e =
    sigTy (sigE A B) (sigE A B) (TyV.ty (hA e))
      (\ v v' i -> tyvTr (lamE A B v) (lamE A B v') (hB (envCons e (tmv _ (TyV.ty (hA e)) i))))

  v-tyeq-Pi : {A A' : Expr n} {B B' : Expr (suc n)} ->
              ValTy G A -> ValTyEq G A A' -> ValTyEq (extend G A) B B' ->
              ValTyEq G (PiB A B) (PiB A' B')
  v-tyeq-Pi {A} {A'} {B} {B'} hA hAA hB e =
    piTy (piE A B) (piE A' B') (TyV.ty (hAA e))
      (\ v v' i -> tyvTr (lamE A B v) (lamE A' B' v')
         (hB (envCons e (retype (tmv _ (TyV.ty (hAA e)) i) (TyV.ty (hA e))))))

  v-tyeq-Sigma : {A A' : Expr n} {B B' : Expr (suc n)} ->
                 ValTy G A -> ValTyEq G A A' -> ValTyEq (extend G A) B B' ->
                 ValTyEq G (SigmaB A B) (SigmaB A' B')
  v-tyeq-Sigma {A} {A'} {B} {B'} hA hAA hB e =
    sigTy (sigE A B) (sigE A' B') (TyV.ty (hAA e))
      (\ v v' i -> tyvTr (lamE A B v) (lamE A' B' v')
         (hB (envCons e (retype (tmv _ (TyV.ty (hAA e)) i) (TyV.ty (hA e))))))

  ----------------------------------------------------------------------
  -- Pi
  ----------------------------------------------------------------------

  v-ty-Lam : {A : Expr n} {B t : Expr (suc n)} ->
             ValTy G A -> ValTy (extend G A) B -> ValTm (extend G A) t B ->
             ValTm G (Lam A t) (PiB A B)
  v-ty-Lam {A} {B} {t} hA hB ht e =
    tmv _ d (piIntro d (piE A B) (piE A B)
      (\ v v' dY y ->
         tmvTr (lamE A B v) (lamE A B v') (lamE A t v) (lamE A t v')
           (ht (envCons e (tmv _ dY y)))))
    where d = TyV.ty (v-isty-Pi hA hB e)

  v-ty-App : {A t a : Expr n} {B : Expr (suc n)} ->
             ValTm G t (PiB A B) -> ValTm G a A -> ValTm G (App t a) (subst1 B a)
  v-ty-App {A} {t} {a} {B} ht ha {rho} {rho'} e =
    tmvTr (~~-sym (s1E rho A B a)) (~~-sym (s1E rho' A B a))
          (~~-sym (den-App t a)) (~~-sym (den-App t a))
          (piElim (TmV.ty (ht e)) (piE A B) (piE A B) (TmV.el (ht e))
                  (TmV.ty (ha e)) (TmV.el (ha e)))

  v-conv-App : {A t t' a a' : Expr n} {B : Expr (suc n)} ->
               ValTy G A -> ValTy (extend G A) B ->
               ValConv G t t' (PiB A B) -> ValConv G a a' A ->
               ValConv G (App t a) (App t' a') (subst1 B a)
  v-conv-App {A} {t} {t'} {a} {a'} {B} hA hB ht ha {rho} {rho'} e =
    tmvTr (~~-sym (den-subst1 rho B a)) (~~-sym (den-subst1 rho' B a))
          (~~-sym (den-App t a)) (~~-sym (den-App t' a'))
          (retype
            (tmvTr (den-Lam A B (den a rho)) (den-Lam A B (den a' rho')) ~~-refl ~~-refl
              (piElim (TmV.ty (ht e)) (piE A B) (piE A B) (TmV.el (ht e))
                      (TmV.ty (ha e)) (TmV.el (ha e))))
            (TyV.ty (hB (envCons e (vconv-l {G = G} ha e)))))

  v-conv-beta : {A a : Expr n} {B t : Expr (suc n)} ->
                ValTm (extend G A) t B -> ValTm G a A ->
                ValConv G (App (Lam A t) a) (subst1 t a) (subst1 B a)
  v-conv-beta {A} {a} {B} {t} ht ha {rho} {rho'} e =
    tmvTr (~~-sym (den-subst1 rho B a)) (~~-sym (den-subst1 rho' B a))
          (~~-sym (~~-trans (den-App (Lam A t) a) (den-Lam A t (den a rho))))
          (~~-sym (den-subst1 rho' t a))
          (ht (envCons e (ha e)))

  v-conv-funext : {A t t' : Expr n} {B : Expr (suc n)} ->
                  ValTm G t (PiB A B) ->
                  ValConv (extend G A) (App (wkExpr t) x0) (App (wkExpr t') x0) B ->
                  ValConv G t t' (PiB A B)
  v-conv-funext {A} {t} {t'} {B} ht hc {rho} {rho'} e =
    tmv _ d (piIntro d (piE A B) (piE A B)
      (\ v v' dY y ->
         tmvTr (lamE A B v) (lamE A B v') (E t rho v) (E t' rho' v')
           (hc (envCons e (tmv _ dY y)))))
    where
      d = TmV.ty (ht e)
      E : (s : Expr n) (r : Env n) (v : D) ->
          den (App (wkExpr s) x0) (cons r v) ~~ app (den s r) v
      E s r v = ~~-trans (den-App (wkExpr s) x0)
                  (app-cong (den-wk-cons r v s) (den-Var fzero))

  ----------------------------------------------------------------------
  -- Sigma
  ----------------------------------------------------------------------

  private
    pr1E : (t u : Expr n) (r : Env n) -> pr1 (den (Pair t u) r) ~~ den t r
    pr1E t u r = ~~-trans (pr1-cong (den-Pair t u)) pr1-pair
    pr2E : (t u : Expr n) (r : Env n) -> pr2 (den (Pair t u) r) ~~ den u r
    pr2E t u r = ~~-trans (pr2-cong (den-Pair t u)) pr2-pair

  v-ty-Pair : {A t u : Expr n} {B : Expr (suc n)} ->
              ValTy G A -> ValTy (extend G A) B -> ValTm G t A -> ValTm G u (subst1 B t) ->
              ValTm G (Pair t u) (SigmaB A B)
  v-ty-Pair {A} {t} {u} {B} hA hB ht hu {rho} {rho'} e =
    tmv _ d (sigIntro d (sigE A B) (sigE A B)
      (tmvTr ~~-refl ~~-refl (~~-sym (pr1E t u rho)) (~~-sym (pr1E t u rho')) (ht e))
      (tmvTr (~~-trans (s1E rho A B t)
                (app-cong ~~-refl (~~-sym (pr1E t u rho))))
             ~~-refl (~~-sym (pr2E t u rho)) (~~-sym (pr2E t u rho')) (hu e)))
    where d = TyV.ty (v-isty-Sigma hA hB e)

  v-ty-Fst : {A t : Expr n} {B : Expr (suc n)} ->
             ValTm G t (SigmaB A B) -> ValTm G (Fst t) A
  v-ty-Fst {A} {t} {B} ht e =
    tmvTr ~~-refl ~~-refl (~~-sym (den-Fst t)) (~~-sym (den-Fst t))
      (sigElim1 (TmV.ty (ht e)) (sigE A B) (sigE A B) (TmV.el (ht e)))

  v-conv-Fst : {A t t' : Expr n} {B : Expr (suc n)} ->
               ValConv G t t' (SigmaB A B) -> ValConv G (Fst t) (Fst t') A
  v-conv-Fst {A} {t} {t'} {B} ht e =
    tmvTr ~~-refl ~~-refl (~~-sym (den-Fst t)) (~~-sym (den-Fst t'))
      (sigElim1 (TmV.ty (ht e)) (sigE A B) (sigE A B) (TmV.el (ht e)))

  private
    fstE : (r : Env n) (A t : Expr n) (B : Expr (suc n)) ->
           app (den (Lam A B) r) (pr1 (den t r)) ~~ den (subst1 B (Fst t)) r
    fstE r A t B =
      ~~-trans (den-Lam A B _)
        (~~-trans (den-cons r B (~~-sym (den-Fst t)))
                  (~~-sym (den-subst1 r B (Fst t))))

  v-ty-Snd : {A t : Expr n} {B : Expr (suc n)} ->
             ValTm G t (SigmaB A B) -> ValTm G (Snd t) (subst1 B (Fst t))
  v-ty-Snd {A} {t} {B} ht {rho} {rho'} e =
    tmvTr (fstE rho A t B) (fstE rho' A t B) (~~-sym (den-Snd t)) (~~-sym (den-Snd t))
      (sigElim2 (TmV.ty (ht e)) (sigE A B) (sigE A B) (TmV.el (ht e)))

  v-conv-Snd : {A t t' : Expr n} {B : Expr (suc n)} ->
               ValTy (extend G A) B -> ValConv G t t' (SigmaB A B) ->
               ValConv G (Snd t) (Snd t') (subst1 B (Fst t))
  v-conv-Snd {A} {t} {t'} {B} hB ht {rho} {rho'} e =
    tmvTr (~~-trans (den-Fst' rho) (~~-sym (den-subst1 rho B (Fst t))))
          (~~-trans (den-Fst' rho') (~~-sym (den-subst1 rho' B (Fst t))))
          (~~-sym (den-Snd t)) (~~-sym (den-Snd t'))
      (retype
        (tmvTr (den-Lam A B _) (den-Lam A B _) ~~-refl ~~-refl
          (sigElim2 (TmV.ty (ht e)) (sigE A B) (sigE A B) (TmV.el (ht e))))
        (TyV.ty (hB (envCons e (sigElim1 (TmV.ty tl0) (sigE A B) (sigE A B) (TmV.el tl0))))))
    where
      tl0 = vconv-l {G = G} ht e
      den-Fst' : (r : Env n) -> den B (cons r (pr1 (den t r))) ~~ den B (cons r (den (Fst t) r))
      den-Fst' r = den-cons r B (~~-sym (den-Fst t))

  v-conv-fst-beta : {A t u : Expr n} ->
                    ValTm G t A -> ValConv G (Fst (Pair t u)) t A
  v-conv-fst-beta {A} {t} {u} ht {rho} {rho'} e =
    tmvTr ~~-refl ~~-refl (~~-sym (~~-trans (den-Fst (Pair t u)) (pr1E t u rho))) ~~-refl (ht e)

  v-conv-snd-beta : {A t u : Expr n} ->
                    ValTm G u A -> ValConv G (Snd (Pair t u)) u A
  v-conv-snd-beta {A} {t} {u} hu {rho} {rho'} e =
    tmvTr ~~-refl ~~-refl (~~-sym (~~-trans (den-Snd (Pair t u)) (pr2E t u rho))) ~~-refl (hu e)

  v-conv-pairext : {A t t' : Expr n} {B : Expr (suc n)} ->
                   ValTm G t (SigmaB A B) ->
                   ValConv G (Fst t) (Fst t') A ->
                   ValConv G (Snd t) (Snd t') (subst1 B (Fst t)) ->
                   ValConv G t t' (SigmaB A B)
  v-conv-pairext {A} {t} {t'} {B} ht hf hs {rho} {rho'} e =
    tmv _ d (sigIntro d (sigE A B) (sigE A B)
      (tmvTr ~~-refl ~~-refl (den-Fst t) (den-Fst t') (hf e))
      (tmvTr (~~-sym (fstE rho A t B)) ~~-refl (den-Snd t) (den-Snd t') (hs e)))
    where d = TmV.ty (ht e)
