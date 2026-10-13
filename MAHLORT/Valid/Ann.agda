{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Valid/Ann.agda
--
-- Conversion of annotated eliminations whose annotations are both
-- convertible to a canonical (A, B):  app, fst, snd at two arbitrary
-- annotation pairs, typed at the canonical type.
------------------------------------------------------------------------

module MAHLORT.Valid.Ann where

open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping

module _ {n : Num} {G : Ctx n} {A A0 A1 : Expr n} {B B0 B1 : Expr (suc n)}
         (iA : IsType G A) (iB : IsType (extend G A) B)
         (e0 : TyEq G A A0) (e1 : TyEq (extend G A) B B0)
         (e2 : TyEq G A A1) (e3 : TyEq (extend G A) B B1) where

  appEq : {c c' a a' : Expr n} -> HasType G c (PiB A B) -> HasType G a A ->
    ConvTm G c c' (PiB A B) -> ConvTm G a a' A ->
    ConvTm G (appB A0 B0 c a) (appB A1 B1 c' a') (subst1 B a)
  appEq hc ha cc ca =
    conv-trans (conv-sym (conv-App iA iB e0 e1 (conv-refl hc) (conv-refl ha))) (conv-App iA iB e2 e3 cc ca)

  fstEq : {t t' : Expr n} -> HasType G t (SigmaB A B) -> ConvTm G t t' (SigmaB A B) ->
    ConvTm G (Fst A0 (Lam A0 B0) t) (Fst A1 (Lam A1 B1) t') A
  fstEq ht c = conv-trans (conv-sym (conv-Fst iA iB e0 e1 (conv-refl ht))) (conv-Fst iA iB e2 e3 c)

  sndEq : {t t' : Expr n} -> HasType G t (SigmaB A B) -> ConvTm G t t' (SigmaB A B) ->
    ConvTm G (Snd A0 (Lam A0 B0) t) (Snd A1 (Lam A1 B1) t') (subst1 B (Fst A (Lam A B) t))
  sndEq ht c = conv-trans (conv-sym (conv-Snd iA iB e0 e1 (conv-refl ht))) (conv-Snd iA iB e2 e3 c)
