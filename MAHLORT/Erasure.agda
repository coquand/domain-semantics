{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Erasure.agda   (DRAFT)
--
-- The erasure  |.| : Tarski -> Russell (MAHLO/Syntax.agda): forget El,
-- T^ and the annotations of app/pair/fst/snd; identify the codes with
-- the type formers:
--   El_V a, El_U a, T^ a          |->  |a|
--   Pi^_V, Pi^_U, Pi              |->  Pi       (Sigma likewise)
--   N^_V, N^_U, N                 |->  Nat
--   U^_{f,g}, U_{f,g}             |->  Ucode |f| |g|
--   f^, g^                        |->  Fhat, Ghat
------------------------------------------------------------------------

module MAHLORT.Erasure where

open import MAHLORT.TarskiSyntax as T
import MAHLO.Syntax as R
import MAHLORT.TarskiTyping as TT
import MAHLO.Typing as RT

er : {n : Num} -> T.Expr n -> R.Expr n
er (Var i) = R.Var i
er (Lam A t) = R.Lam (er A) (er t)
er (App A F c a) = R.App (er c) (er a)
er (Pi A F) = R.Pi (er A) (er F)
er (Sigma A F) = R.Sigma (er A) (er F)
er (Pair A F a b) = R.Pair (er a) (er b)
er (Fst A F t) = R.Fst (er t)
er (Snd A F t) = R.Snd (er t)
er Nat = R.Nat
er Zero = R.Zero
er (Suc t) = R.Suc (er t)
er (Rec C z s k) = R.Rec (er C) (er z) (er s) (er k)
er V = R.V
er (ElV a) = er a
er (TyU f g) = R.Ucode (er f) (er g)
er (ElU f g a) = er a
er (PiV a F) = R.Pi (er a) (er F)
er (SigV a F) = R.Sigma (er a) (er F)
er NatV = R.Nat
er (UV f g) = R.Ucode (er f) (er g)
er (PiU f g a F) = R.Pi (er a) (er F)
er (SigU f g a F) = R.Sigma (er a) (er F)
er (NatU f g) = R.Nat
er (Fhat f g a F) = R.Fhat (er f) (er g) (er a) (er F)
er (Ghat f g a F c) = R.Ghat (er f) (er g) (er a) (er F) (er c)
er (That a) = er a

erCtx : {n : Num} -> TT.Ctx n -> RT.Ctx n
erCtx TT.empty = RT.empty
erCtx (TT.extend G A) = RT.extend (erCtx G) (er A)
