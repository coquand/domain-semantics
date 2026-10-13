{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/EraseDeriv.agda
--
-- Lemma 4.6 (Tarski -> Russell): erasure preserves all five judgements.
--   T-derivation of J   ==>   R-derivation of |J|.
-- The decoding and T^-commutation equations erase to reflexivity (both
-- sides have the same erasure); T^(f^ ..), T^(g^ ..) erase to
-- conv-delta-f/g; reflection erases to conv-R'; conv-Lam / conv-Pair
-- erase to the derived Russell congruences of MAHLORT/RussellCong.
------------------------------------------------------------------------

module MAHLORT.EraseDeriv where

open import MAHLO.Basic
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
import MAHLO.Syntax as R
import MAHLO.Typing as RT
open import MAHLORT.Erasure
open import MAHLORT.EraseLemmas
open import MAHLORT.RussellCong

------------------------------------------------------------------------
-- Transports along syntactic equalities
------------------------------------------------------------------------

private
  trH : {n : Num} {G : RT.Ctx n} {t t' A A' : R.Expr n} ->
        Eq t t' -> Eq A A' -> RT.HasType G t A -> RT.HasType G t' A'
  trH refl refl d = d

  trA : {n : Num} {G : RT.Ctx n} {t A A' : R.Expr n} ->
        Eq A A' -> RT.HasType G t A -> RT.HasType G t A'
  trA refl d = d

  trC : {n : Num} {G : RT.Ctx n} {t t' u u' A A' : R.Expr n} ->
        Eq t t' -> Eq u u' -> Eq A A' -> RT.ConvTm G t u A -> RT.ConvTm G t' u' A'
  trC refl refl refl d = d

  trCA : {n : Num} {G : RT.Ctx n} {t u A A' : R.Expr n} ->
         Eq A A' -> RT.ConvTm G t u A -> RT.ConvTm G t u A'
  trCA refl d = d

  wkU : {n : Num} (f g : Expr n) -> Eq (er (wkExpr (TyU f g))) (R.wkExpr (R.Ucode (er f) (er g)))
  wkU f g = er-wk (TyU f g)

  uU : {n : Num} (f g : Expr n) -> RT.Univ (R.Ucode (er f) (er g))
  uU f g = RT.univ-U _ _ refl

  uV : {n : Num} -> RT.Univ {n} R.V
  uV = RT.univ-V refl

------------------------------------------------------------------------
-- The five erasures
------------------------------------------------------------------------

erW : {n : Num} {G : Ctx n} -> WfCtx G -> RT.WfCtx (erCtx G)
erI : {n : Num} {G : Ctx n} {A : Expr n} -> IsType G A -> RT.IsType (erCtx G) (er A)
erH : {n : Num} {G : Ctx n} {t A : Expr n} -> HasType G t A -> RT.HasType (erCtx G) (er t) (er A)
erT : {n : Num} {G : Ctx n} {A B : Expr n} -> TyEq G A B -> RT.TyEq (erCtx G) (er A) (er B)
erC : {n : Num} {G : Ctx n} {t u A : Expr n} -> ConvTm G t u A ->
      RT.ConvTm (erCtx G) (er t) (er u) (er A)

-- g : OpG f, erased
erG : {n : Num} {G : Ctx n} {f g : Expr n} -> HasType G g (OpG f) ->
      RT.HasType (erCtx G) (er g) (R.OpG (er f))
erG {f = f} d = trA (er-OpG f) (erH d)

erW wf-empty = RT.wf-empty
erW (wf-extend A) = RT.wf-extend (erI A)

erI (isty-V w) = RT.isty-V (erW w)
erI (isty-ElV a) = RT.isty-el (erH a)
erI (isty-TyU df dg) = RT.isty-el (RT.ty-Ucode (erH df) (erG dg))
erI (isty-ElU a) = RT.isty-el (RT.ty-sub (erH a))
erI (isty-Pi A B) = RT.isty-Pi (erI A) (erI B)
erI (isty-Sigma A B) = RT.isty-Sigma (erI A) (erI B)
erI (isty-Nat w) = RT.isty-el (RT.ty-Nat-V (erW w))

erH (ty-var {G = G} {i = i} w) = trA (Eq-sym (er-lookup G i)) (RT.ty-var (erW w))
erH (ty-conv d e) = RT.ty-conv (erH d) (erT e)
erH (ty-Lam A B t) = RT.ty-Lam (erI A) (erI B) (erH t)
erH (ty-App {a = a} {B = B} A Bd c d) =
  trA (Eq-sym (er-subst1 B a)) (RT.ty-App (erI A) (erI Bd) (erH c) (erH d))
erH (ty-Pair {a = a} {B = B} A Bd d e) =
  RT.ty-Pair (erI A) (erI Bd) (erH d) (trA (er-subst1 B a) (erH e))
erH (ty-Fst A B d) = RT.ty-Fst (erI A) (erI B) (erH d)
erH (ty-Snd {A = A} {t = t} {B = B} Ad Bd d) =
  trA (Eq-sym (er-subst1 B (Fst A (Lam A B) t))) (RT.ty-Snd (erI Ad) (erI Bd) (erH d))
erH (ty-Zero w) = RT.ty-Zero (erW w)
erH (ty-Suc d) = RT.ty-Suc (erH d)
erH (ty-Rec {k = k} {C = C} Cd z s kd) =
  trA (Eq-sym (er-subst1 C k))
    (RT.ty-Rec (erI Cd) (trA (er-subst1 C Zero) (erH z)) (trA (er-RecStep C) (erH s)) (erH kd))
erH (ty-PiV a b) = RT.ty-Pi uV (erH a) (erH b)
erH (ty-SigV a b) = RT.ty-Sigma uV (erH a) (erH b)
erH (ty-NatV w) = RT.ty-Nat-V (erW w)
erH (ty-UV df dg) = RT.ty-Ucode (erH df) (erG dg)
erH (ty-PiU {f = f} {g = g} a b) = RT.ty-Pi (uU f g) (erH a) (trA (wkU f g) (erH b))
erH (ty-SigU {f = f} {g = g} a b) = RT.ty-Sigma (uU f g) (erH a) (trA (wkU f g) (erH b))
erH (ty-NatU (isty-TyU df dg)) = RT.ty-Nat-U (RT.ty-Ucode (erH df) (erG dg))
erH (ty-Fhat {f = f} {g = g} df dg a b) =
  RT.ty-Fhat (erH df) (erG dg) (erH a) (trA (wkU f g) (erH b))
erH (ty-Ghat {f = f} {g = g} df dg a b c) =
  RT.ty-Ghat (erH df) (erG dg) (erH a) (trA (wkU f g) (erH b)) (erH c)
erH (ty-That a) = RT.ty-sub (erH a)

erT (tyeq-refl A) = RT.tyeq-refl (erI A)
erT (tyeq-sym e) = RT.tyeq-sym (erT e)
erT (tyeq-trans e e') = RT.tyeq-trans (erT e) (erT e')
erT (tyeq-ElV c) = RT.tyeq-el (erC c)
erT (tyeq-ElU c) = RT.tyeq-el (RT.conv-sub (erC c))
erT (tyeq-TyU {f = f} df dg cf cg) =
  RT.tyeq-el (RT.conv-Ucode (erH df) (erG dg) (erC cf) (trCA (er-OpG f) (erC cg)))
erT (tyeq-Pi A B B' e e') = RT.tyeq-Pi (erI A) (erI B) (erI B') (erT e) (erT e')
erT (tyeq-Sigma A B B' e e') = RT.tyeq-Sigma (erI A) (erI B) (erI B') (erT e) (erT e')
erT (tyeq-El-PiV a b) = RT.tyeq-refl (RT.isty-el (RT.ty-Pi uV (erH a) (erH b)))
erT (tyeq-El-SigV a b) = RT.tyeq-refl (RT.isty-el (RT.ty-Sigma uV (erH a) (erH b)))
erT (tyeq-El-NatV w) = RT.tyeq-refl (RT.isty-el (RT.ty-Nat-V (erW w)))
erT (tyeq-El-UV df dg) = RT.tyeq-refl (RT.isty-el (RT.ty-Ucode (erH df) (erG dg)))
erT (tyeq-ElU-That a) = RT.tyeq-refl (RT.isty-el (RT.ty-sub (erH a)))

erC (conv-refl d) = RT.conv-refl (erH d)
erC (conv-sym c) = RT.conv-sym (erC c)
erC (conv-trans c c') = RT.conv-trans (erC c) (erC c')
erC (conv-conv c e) = RT.conv-conv (erC c) (erT e)
erC (conv-beta {a = a} {B = B} {t = t} A Bd td ad) =
  trC refl (Eq-sym (er-subst1 t a)) (Eq-sym (er-subst1 B a))
    (RT.conv-beta (erI A) (erI Bd) (erH td) (erH ad))
erC (conv-funext {A = A} {t = t} {t' = t'} Ad Bd d d' c) =
  RT.conv-funext (erI Ad) (erI Bd) (erH d) (erH d')
    (trC (Eq-cong (\ x -> R.App x R.x0) (er-wk t)) (Eq-cong (\ x -> R.App x R.x0) (er-wk t')) refl (erC c))
erC (conv-fst-beta {a = a} {B = B} A Bd d e) =
  RT.conv-fst-beta (erI A) (erI Bd) (erH d) (trA (er-subst1 B a) (erH e))
erC (conv-snd-beta {a = a} {B = B} A Bd d e) =
  trCA (Eq-sym (er-subst1 B a))
    (RT.conv-snd-beta (erI A) (erI Bd) (erH d) (trA (er-subst1 B a) (erH e)))
erC (conv-pairext {A = A} {t = t} {B = B} Ad Bd d d' c c') =
  RT.conv-pairext (erI Ad) (erI Bd) (erH d) (erH d') (erC c)
    (trCA (er-subst1 B (Fst A (Lam A B) t)) (erC c'))
erC (conv-rec-zero {C = C} Cd z s) =
  trCA (Eq-sym (er-subst1 C Zero))
    (RT.conv-rec-zero (erI Cd) (trA (er-subst1 C Zero) (erH z)) (trA (er-RecStep C) (erH s)))
erC (conv-rec-suc {k = k} {C = C} Cd z s kd) =
  trCA (Eq-sym (er-subst1 C (Suc k)))
    (RT.conv-rec-suc (erI Cd) (trA (er-subst1 C Zero) (erH z)) (trA (er-RecStep C) (erH s)) (erH kd))
erC (conv-Lam A B q c) = cvLam (erI A) (erI B) (erT q) (erC c)
erC (conv-App {a = a} {B = B} A Bd _ _ c c') =
  trCA (Eq-sym (er-subst1 B a)) (RT.conv-App (erI A) (erI Bd) (erC c) (erC c'))
erC (conv-Pair {a = a} {B = B} A Bd _ _ ca cb) =
  cvPair (erI A) (erI Bd) (erC ca) (trCA (er-subst1 B a) (erC cb))
erC (conv-Fst A B _ _ c) = RT.conv-Fst (erI A) (erI B) (erC c)
erC (conv-Snd {A = A} {t = t} {B = B} Ad Bd _ _ c) =
  trCA (Eq-sym (er-subst1 B (Fst A (Lam A B) t))) (RT.conv-Snd (erI Ad) (erI Bd) (erC c))
erC (conv-Suc c) = RT.conv-Suc (erC c)
erC (conv-Rec {k = k} {C = C} Cd Cd' e z s kc) =
  trCA (Eq-sym (er-subst1 C k))
    (RT.conv-Rec (erI Cd) (erI Cd') (erT e) (trCA (er-subst1 C Zero) (erC z))
       (trCA (er-RecStep C) (erC s)) (erC kc))
erC (conv-PiV a b b' c c') = RT.conv-Pi uV (erH a) (erH b) (erH b') (erC c) (erC c')
erC (conv-SigV a b b' c c') = RT.conv-Sigma uV (erH a) (erH b) (erH b') (erC c) (erC c')
erC (conv-UV {f = f} df dg cf cg) =
  RT.conv-Ucode (erH df) (erG dg) (erC cf) (trCA (er-OpG f) (erC cg))
erC (conv-PiU {f = f} {g = g} a b b' c c') =
  RT.conv-Pi (uU f g) (erH a) (trA (wkU f g) (erH b)) (trA (wkU f g) (erH b')) (erC c)
    (trCA (wkU f g) (erC c'))
erC (conv-SigU {f = f} {g = g} a b b' c c') =
  RT.conv-Sigma (uU f g) (erH a) (trA (wkU f g) (erH b)) (trA (wkU f g) (erH b')) (erC c)
    (trCA (wkU f g) (erC c'))
erC (conv-Fhat {f = f} {g = g} df dg a b b' c c') =
  RT.conv-Fhat (RT.conv-refl (erH df)) (RT.conv-refl (erG dg)) (erH a)
    (trA (wkU f g) (erH b)) (trA (wkU f g) (erH b')) (erC c) (trCA (wkU f g) (erC c'))
erC (conv-Ghat {f = f} {g = g} df dg a b b' c c' cc) =
  RT.conv-Ghat (RT.conv-refl (erH df)) (RT.conv-refl (erG dg)) (erH a)
    (trA (wkU f g) (erH b)) (trA (wkU f g) (erH b')) (erC c) (trCA (wkU f g) (erC c')) (erC cc)
erC (conv-That c) = RT.conv-sub (erC c)
erC (conv-That-PiU {f = f} {g = g} a b) =
  RT.conv-refl (RT.ty-sub (RT.ty-Pi (uU f g) (erH a) (trA (wkU f g) (erH b))))
erC (conv-That-SigU {f = f} {g = g} a b) =
  RT.conv-refl (RT.ty-sub (RT.ty-Sigma (uU f g) (erH a) (trA (wkU f g) (erH b))))
erC (conv-That-NatU (isty-TyU df dg)) =
  RT.conv-refl (RT.ty-sub (RT.ty-Nat-U (RT.ty-Ucode (erH df) (erG dg))))
erC (conv-That-Fhat {f = f} {g = g} df dg a b) =
  RT.conv-delta-f (erH df) (erG dg) (erH a) (trA (wkU f g) (erH b))
erC (conv-That-Ghat {f = f} {g = g} df dg a b c) =
  RT.conv-delta-g (erH df) (erG dg) (erH a) (trA (wkU f g) (erH b)) (erH c)
erC (conv-reflect a b c) = RT.conv-R' (erH a) (erH b) (erC c)
