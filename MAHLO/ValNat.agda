{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/ValNat.agda
--
-- Validity of the rules for V as a type, and for Nat, 0, S and rec.
-- Soundness of rec is by induction on NatR (plan Sec. 6.4): on a
-- neutral argument the result is neutral, hence in [C n].
------------------------------------------------------------------------

open import MAHLO.Basic
open import MAHLO.TermModel
import MAHLO.Model
import MAHLO.Fixpoint

module MAHLO.ValNat (TM : TermModel) (M : MAHLO.Model.Model TM)
                    (Fx : MAHLO.Fixpoint.Fixpoint TM) where

open TermModel TM
open MAHLO.Model TM using (Env ; cons)
open MAHLO.Model.Model M
open import MAHLO.Candidate TM
open MAHLO.Fixpoint TM
open Fixpoint Fx
open Cand V
open import MAHLO.Validity TM M Fx
open import MAHLO.Syntax
  renaming (Pi to tPi ; Sigma to tSigma ; Nat to tNat ; V to tV)
open import MAHLO.Typing

private
  module RV = IsPER R-per

-- the type Nat
natTy : TyR Nat Nat (I Nat)
natTy = tySm seed-nat ~-refl

module _ {n : Num} {G : Ctx n} where

  natTm : {rho rho' : Env n} {t t' : D} -> NatR t t' ->
          TmV (den tNat rho) (den tNat rho') t t'
  natTm i = tmvTr (~~-sym den-Nat) (~~-sym den-Nat) ~~-refl ~~-refl (tmv _ natTy (snd nat-int i))

  natEl : {rho rho' : Env n} {t t' : D} ->
          TmV (den tNat rho) (den tNat rho') t t' -> NatR t t'
  natEl p = fst nat-int (elAt (tmvTr den-Nat den-Nat ~~-refl ~~-refl p) natTy)

  v-isty-V : ValTy G tV
  v-isty-V e = tyvTr (~~-sym den-V) (~~-sym den-V) (tyv _ tyVV)

  v-ty-Nat-V : ValTm G tNat tV
  v-ty-Nat-V e =
    tmvTr (~~-sym den-V) (~~-sym den-V) (~~-sym den-Nat) (~~-sym den-Nat)
      (tmv _ tyVV seed-nat)

  v-ty-Zero : ValTm G Zero tNat
  v-ty-Zero e = tmvTr ~~-refl ~~-refl (~~-sym den-Zero) (~~-sym den-Zero) (natTm NatR-zero)

  v-conv-Suc : {t t' : Expr n} -> ValConv G t t' tNat -> ValConv G (Suc t) (Suc t') tNat
  v-conv-Suc {t} {t'} h e =
    tmvTr ~~-refl ~~-refl (~~-sym (den-Suc t)) (~~-sym (den-Suc t')) (natTm (NatR-suc (natEl (h e))))

  ----------------------------------------------------------------------
  -- rec
  ----------------------------------------------------------------------

  module _ {C C' : Expr (suc n)} {z z' s s' : Expr n} {rho rho' : Env n}
           (e : EnvR G rho rho') (hC : ValTy (extend G tNat) C)
           (hS : S (den (Lam tNat C) rho) (den (Lam tNat C') rho'))
           (tz : TmV (den (subst1 C Zero) rho) (den (subst1 C Zero) rho')
                     (den z rho) (den z' rho'))
           (ts : TmV (den (RecStep C) rho) (den (RecStep C) rho')
                     (den s rho) (den s' rho')) where

    private
      Cr  = den (Lam tNat C) rho
      Cr' = den (Lam tNat C') rho'
      rc : D -> D
      rc k = recD Cr (den z rho) (den s rho) k
      rc' : D -> D
      rc' k = recD Cr' (den z' rho') (den s' rho') k

      h : (k k' : D) -> NatR k k' -> TyV (den C (cons rho k)) (den C (cons rho' k'))
      h k k' i = hC (envCons e (natTm i))

      Yf : D -> Rel
      Yf = mkFam NatR (\ w p -> TyV.X (h w w p))

      coh : {k k' : D} (i : NatR k k') -> TyV.X (h k k' i) ~ Yf k
      coh i = famCoh NatR-per h i

      YfCl : {k v v' w w' : D} -> v ~~ w -> v' ~~ w' -> Yf k v v' -> Yf k w w'
      YfCl e e' (p , y) = p , TyR-el2 (TyV.ty (h _ _ p)) e e' y

      P : D -> D -> Set
      P k k' = Yf k (rc k) (rc' k')

      -- P is closed under the equality of D
      clL : {k m k' : D} -> k ~~ m -> P k k' -> P m k'
      clL {k} {m} e (p , y) =
        pm , TyR-el2 d2 (recD-cong ~~-refl ~~-refl ~~-refl e) ~~-refl
               (fst (funL (TyR-cl2 (den-cons rho C e) ~~-refl (TyV.ty (h k k p))) d2) y)
        where
          pm = NatR-resp e (clR-of NatR-per NatR-resp e p)
          d2 = TyV.ty (h m m pm)

      clR : {k k' m' : D} -> k' ~~ m' -> P k k' -> P k m'
      clR {k} e (p , y) = p , TyR-elR (TyV.ty (h k k p)) (recD-cong ~~-refl ~~-refl ~~-refl e) y

      pN : {k k' : D} -> N k k' -> P k k'
      pN nk = fst (coh i) (lo (TyV.ty (h _ _ i))
                (ne-rec hS (hi (TmV.ty tz) (TmV.el tz)) (hi (TmV.ty ts) (TmV.el ts)) nk))
        where i = N-NatR nk

      zE : (r : Env n) -> den (subst1 C Zero) r ~~ den C (cons r zeroD)
      zE r = ~~-trans (den-subst1 r C Zero) (den-cons r C den-Zero)

      pZ : P zeroD zeroD
      pZ = YfCl (~~-sym rec-zero) (~~-sym rec-zero)
             (fst (coh NatR-zero)
               (elAt (tmvTr (zE rho) (zE rho') ~~-refl ~~-refl tz) (TyV.ty (h _ _ NatR-zero))))

      -- the step type at (rho, k):  Pi (C k) (\_. C (S k))
      stepE : (r : Env n) (k : D) ->
              app (den (Lam tNat (Arr C (substExpr sucSub C))) r) k ~~
                 Pi (den C (cons r k)) (den (Lam C (wkExpr (substExpr sucSub C))) (cons r k))
      stepE r k = ~~-trans (den-Lam tNat (Arr C (substExpr sucSub C)) k)
                           (den-Pi C (Lam C (wkExpr (substExpr sucSub C))))

      sucE : (r : Env n) (k w : D) ->
             app (den (Lam C (wkExpr (substExpr sucSub C))) (cons r k)) w ~~
                den C (cons r (sucD k))
      sucE r k w = ~~-trans (den-Lam C (wkExpr (substExpr sucSub C)) w)
                     (~~-trans (den-wk-cons (cons r k) w (substExpr sucSub C))
                               (den-sucSub r k C))

      pS : {k k' : D} -> NatR k k' -> P k k' -> P (sucD k) (sucD k')
      pS {k} {k'} i p =
        YfCl (~~-sym rec-suc) (~~-sym rec-suc)
          (fst (coh (NatR-suc i))
            (elAt (tmvTr (sucE rho k (rc k)) (sucE rho' k' (rc' k')) ~~-refl ~~-refl t2)
                  (TyV.ty (h _ _ (NatR-suc i)))))
        where
          t0 = natTm {rho = rho} {rho'} i
          t1 = piElim (TmV.ty ts) (den-Pi tNat _) (den-Pi tNat _) (TmV.el ts)
                      (TmV.ty t0) (TmV.el t0)
          t2 = piElim (TmV.ty t1) (stepE rho k) (stepE rho' k') (TmV.el t1)
                      (TyV.ty (h k k' i)) (snd (coh i) p)

    recSem : {k k' : D} -> NatR k k' ->
             TmV (den C (cons rho k)) (den C (cons rho' k')) (rc k) (rc' k')
    recSem i = tmv _ (TyV.ty (h _ _ i)) (snd (coh i) (NatR-ind P clL clR pN pZ pS i))

  -- S (den (Lam Nat C) rho) (den (Lam Nat C') rho') from C = C'
  private
    lamS : {C C' : Expr (suc n)} {rho rho' : Env n} -> EnvR G rho rho' ->
           ValTyEq (extend G tNat) C C' ->
           S (den (Lam tNat C) rho) (den (Lam tNat C') rho')
    lamS {C} {C'} {rho} {rho'} e hC =
      k (S-back (den-Lam tNat C x) (den-Lam tNat C' x)
           (safe (TyV.ty (hC (envCons e (natTm (N-NatR nx)))))))
      where
        x  = fst (ext (den (Lam tNat C) rho) (den (Lam tNat C') rho'))
        nx = fst (snd (ext (den (Lam tNat C) rho) (den (Lam tNat C') rho')))
        k  = snd (snd (ext (den (Lam tNat C) rho) (den (Lam tNat C') rho')))

    recE : (r : Env n) (C : Expr (suc n)) (z s k : Expr n) ->
           recD (den (Lam tNat C) r) (den z r) (den s r) (den k r) ~~
              den (Rec (Lam tNat C) z s k) r
    recE r C z s k = ~~-sym (den-Rec (Lam tNat C) z s k)

  v-conv-Rec : {z z' s s' k k' : Expr n} {C C' : Expr (suc n)} ->
               ValTy (extend G tNat) C -> ValTyEq (extend G tNat) C C' ->
               ValConv G z z' (subst1 C Zero) -> ValConv G s s' (RecStep C) ->
               ValConv G k k' tNat ->
               ValConv G (Rec (Lam tNat C) z s k) (Rec (Lam tNat C') z' s' k') (subst1 C k)
  v-conv-Rec {z} {z'} {s} {s'} {k} {k'} {C} {C'} hC hCC hz hs hk {rho} {rho'} e =
    tmvTr (~~-sym (den-subst1 rho C k)) (~~-sym (den-subst1 rho' C k))
          (recE rho C z s k) (recE rho' C' z' s' k')
      (retype (recSem {C = C} {C'} {z} {z'} {s} {s'} e hC (lamS e hCC) (hz e) (hs e)
                      (natEl (hk e)))
              (TyV.ty (hC (envCons e (natTm (natEl (vconv-l {G = G} hk e)))))))

  v-ty-Rec : {z s k : Expr n} {C : Expr (suc n)} ->
             ValTy (extend G tNat) C -> ValTm G z (subst1 C Zero) ->
             ValTm G s (RecStep C) -> ValTm G k tNat ->
             ValTm G (Rec (Lam tNat C) z s k) (subst1 C k)
  v-ty-Rec hC hz hs hk = v-conv-Rec hC hC hz hs hk

  v-conv-rec-zero : {z s : Expr n} {C : Expr (suc n)} ->
                    ValTm G z (subst1 C Zero) ->
                    ValConv G (Rec (Lam tNat C) z s Zero) z (subst1 C Zero)
  v-conv-rec-zero {z} {s} {C} hz {rho} {rho'} e =
    tmvTr ~~-refl ~~-refl
      (~~-sym (~~-trans (den-Rec (Lam tNat C) z s Zero)
                (~~-trans (recD-cong ~~-refl ~~-refl ~~-refl den-Zero) rec-zero)))
      ~~-refl (hz e)

  v-conv-rec-suc : {z s k : Expr n} {C : Expr (suc n)} ->
                   ValTy (extend G tNat) C -> ValTm G z (subst1 C Zero) ->
                   ValTm G s (RecStep C) -> ValTm G k tNat ->
                   ValConv G (Rec (Lam tNat C) z s (Suc k))
                             (App (App s k) (Rec (Lam tNat C) z s k)) (subst1 C (Suc k))
  v-conv-rec-suc {z} {s} {k} {C} hC hz hs hk {rho} {rho'} e =
    tmvTr ~~-refl ~~-refl ~~-refl (E rho') (v-ty-Rec hC hz hs (v-conv-Suc hk) e)
    where
      E : (r : Env n) -> den (Rec (Lam tNat C) z s (Suc k)) r ~~
                            den (App (App s k) (Rec (Lam tNat C) z s k)) r
      E r = ~~-trans (den-Rec (Lam tNat C) z s (Suc k))
              (~~-trans (recD-cong ~~-refl ~~-refl ~~-refl (den-Suc k))
                (~~-trans rec-suc
                  (~~-sym (~~-trans (den-App (App s k) (Rec (Lam tNat C) z s k))
                            (app-cong (den-App s k) (den-Rec (Lam tNat C) z s k))))))
