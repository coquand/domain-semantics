{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/TarskiTyping.agda   (FROZEN shared module: edit only via coordinator)
--
-- Typing of the Tarski-style Mahlo universe (setzer1 Def. 3.5 (a):
-- recursive subuniverses with full decoding), plus the REFLECTION rule
-- (mahlo-plan Sec. 1.2, Remark "Tarski and Russell").
--
-- Judgements WfCtx, IsType, HasType, TyEq, ConvTm, as in
-- MAHLO/Typing.agda; grey premises on binder rules (MIN style).
--
-- Universe rules:
--   (V, T_V) closed under Pi, Sigma, N, and U^_{f,g} : V for f, g in
--   IOper(V, T_V);  T_V(U^_{f,g}) = U_{f,g}.
--   (U_{f,g}, T^_{f,g}) recursive subuniverse of V, full decoding
--   T_{U,f,g}(a) = T_V(T^(a)), closed under Pi^_U, Sigma^_U, N^_U with
--   T^ commuting with them, and under f^, g^ reflecting (f, g):
--     T^(f^(a, F)) = f(T^ a, T^ o F),  T^(g^(a, F, c)) = g(T^ a, T^ o F, c).
--   Reflection: a, b : U_{f,g},  T^ a = T^ b : V  ==>  a = b : U_{f,g}.
------------------------------------------------------------------------

module MAHLORT.TarskiTyping where

open import MAHLORT.TarskiSyntax

data Ctx : Num -> Set where
  empty  : Ctx zero
  extend : {n : Num} -> Ctx n -> Expr n -> Ctx (suc n)

lookup : {n : Num} -> Ctx n -> Fin n -> Expr n
lookup (extend G A) fzero    = wkExpr A
lookup (extend G A) (fsuc i) = wkExpr (lookup G i)

data WfCtx   : {n : Num} -> Ctx n -> Set
data IsType  : {n : Num} -> Ctx n -> Expr n -> Set
data HasType : {n : Num} -> Ctx n -> Expr n -> Expr n -> Set
data TyEq    : {n : Num} -> Ctx n -> Expr n -> Expr n -> Set
data ConvTm  : {n : Num} -> Ctx n -> Expr n -> Expr n -> Expr n -> Set

data WfCtx where
  wf-empty  : WfCtx empty
  wf-extend : {n : Num} {G : Ctx n} {A : Expr n} -> IsType G A -> WfCtx (extend G A)

------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------

data IsType where
  isty-V   : {n : Num} {G : Ctx n} -> WfCtx G -> IsType G V
  isty-ElV : {n : Num} {G : Ctx n} {a : Expr n} -> HasType G a V -> IsType G (ElV a)
  isty-TyU : {n : Num} {G : Ctx n} {f g : Expr n} ->
             HasType G f OpF -> HasType G g (OpG f) -> IsType G (TyU f g)
  isty-ElU : {n : Num} {G : Ctx n} {f g a : Expr n} ->
             HasType G a (TyU f g) -> IsType G (ElU f g a)
  isty-Pi  : {n : Num} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} ->
             IsType G A -> IsType (extend G A) B -> IsType G (PiB A B)
  isty-Sigma : {n : Num} {G : Ctx n} {A : Expr n} {B : Expr (suc n)} ->
             IsType G A -> IsType (extend G A) B -> IsType G (SigmaB A B)
  isty-Nat : {n : Num} {G : Ctx n} -> WfCtx G -> IsType G Nat

------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------

data HasType where
  ty-var  : {n : Num} {G : Ctx n} {i : Fin n} -> WfCtx G -> HasType G (Var i) (lookup G i)
  ty-conv : {n : Num} {G : Ctx n} {t A B : Expr n} -> HasType G t A -> TyEq G A B -> HasType G t B

  -- Pi, Sigma (annotated eliminations and pairs)
  ty-Lam  : {n : Num} {G : Ctx n} {A : Expr n} {B t : Expr (suc n)} ->
            IsType G A -> IsType (extend G A) B -> HasType (extend G A) t B ->
            HasType G (Lam A t) (PiB A B)
  ty-App  : {n : Num} {G : Ctx n} {A c a : Expr n} {B : Expr (suc n)} ->
            IsType G A -> IsType (extend G A) B -> HasType G c (PiB A B) -> HasType G a A ->
            HasType G (appB A B c a) (subst1 B a)
  ty-Pair : {n : Num} {G : Ctx n} {A a b : Expr n} {B : Expr (suc n)} ->
            IsType G A -> IsType (extend G A) B -> HasType G a A -> HasType G b (subst1 B a) ->
            HasType G (Pair A (Lam A B) a b) (SigmaB A B)
  ty-Fst  : {n : Num} {G : Ctx n} {A t : Expr n} {B : Expr (suc n)} ->
            IsType G A -> IsType (extend G A) B -> HasType G t (SigmaB A B) ->
            HasType G (Fst A (Lam A B) t) A
  ty-Snd  : {n : Num} {G : Ctx n} {A t : Expr n} {B : Expr (suc n)} ->
            IsType G A -> IsType (extend G A) B -> HasType G t (SigmaB A B) ->
            HasType G (Snd A (Lam A B) t) (subst1 B (Fst A (Lam A B) t))

  -- N
  ty-Zero : {n : Num} {G : Ctx n} -> WfCtx G -> HasType G Zero Nat
  ty-Suc  : {n : Num} {G : Ctx n} {t : Expr n} -> HasType G t Nat -> HasType G (Suc t) Nat
  ty-Rec  : {n : Num} {G : Ctx n} {z s k : Expr n} {C : Expr (suc n)} ->
            IsType (extend G Nat) C -> HasType G z (subst1 C Zero) ->
            HasType G s (RecStep C) -> HasType G k Nat ->
            HasType G (Rec (Lam Nat C) z s k) (subst1 C k)

  -- codes in V
  ty-PiV  : {n : Num} {G : Ctx n} {a : Expr n} {b : Expr (suc n)} ->
            HasType G a V -> HasType (extend G (ElV a)) b V ->
            HasType G (PiV a (Lam (ElV a) b)) V
  ty-SigV : {n : Num} {G : Ctx n} {a : Expr n} {b : Expr (suc n)} ->
            HasType G a V -> HasType (extend G (ElV a)) b V ->
            HasType G (SigV a (Lam (ElV a) b)) V
  ty-NatV : {n : Num} {G : Ctx n} -> WfCtx G -> HasType G NatV V
  ty-UV   : {n : Num} {G : Ctx n} {f g : Expr n} ->
            HasType G f OpF -> HasType G g (OpG f) -> HasType G (UV f g) V

  -- codes in U_{f,g}
  ty-PiU  : {n : Num} {G : Ctx n} {f g a : Expr n} {b : Expr (suc n)} ->
            HasType G a (TyU f g) -> HasType (extend G (ElU f g a)) b (wkExpr (TyU f g)) ->
            HasType G (PiU f g a (Lam (ElU f g a) b)) (TyU f g)
  ty-SigU : {n : Num} {G : Ctx n} {f g a : Expr n} {b : Expr (suc n)} ->
            HasType G a (TyU f g) -> HasType (extend G (ElU f g a)) b (wkExpr (TyU f g)) ->
            HasType G (SigU f g a (Lam (ElU f g a) b)) (TyU f g)
  ty-NatU : {n : Num} {G : Ctx n} {f g : Expr n} ->
            IsType G (TyU f g) -> HasType G (NatU f g) (TyU f g)
  ty-Fhat : {n : Num} {G : Ctx n} {f g a : Expr n} {b : Expr (suc n)} ->
            HasType G f OpF -> HasType G g (OpG f) ->
            HasType G a (TyU f g) -> HasType (extend G (ElU f g a)) b (wkExpr (TyU f g)) ->
            HasType G (Fhat f g a (Lam (ElU f g a) b)) (TyU f g)
  ty-Ghat : {n : Num} {G : Ctx n} {f g a c : Expr n} {b : Expr (suc n)} ->
            HasType G f OpF -> HasType G g (OpG f) ->
            HasType G a (TyU f g) -> HasType (extend G (ElU f g a)) b (wkExpr (TyU f g)) ->
            HasType G c (ElU f g (Fhat f g a (Lam (ElU f g a) b))) ->
            HasType G (Ghat f g a (Lam (ElU f g a) b) c) (TyU f g)

  -- the embedding  T^_{f,g} : U_{f,g} -> V
  ty-That : {n : Num} {G : Ctx n} {f g a : Expr n} ->
            HasType G a (TyU f g) -> HasType G (That a) V

------------------------------------------------------------------------
-- Type equality
------------------------------------------------------------------------

data TyEq where
  tyeq-refl  : {n : Num} {G : Ctx n} {A : Expr n} -> IsType G A -> TyEq G A A
  tyeq-sym   : {n : Num} {G : Ctx n} {A B : Expr n} -> TyEq G A B -> TyEq G B A
  tyeq-trans : {n : Num} {G : Ctx n} {A B C : Expr n} -> TyEq G A B -> TyEq G B C -> TyEq G A C

  -- congruences
  tyeq-ElV : {n : Num} {G : Ctx n} {a a' : Expr n} -> ConvTm G a a' V -> TyEq G (ElV a) (ElV a')
  tyeq-ElU : {n : Num} {G : Ctx n} {f g a a' : Expr n} ->
             ConvTm G a a' (TyU f g) -> TyEq G (ElU f g a) (ElU f g a')
  tyeq-TyU : {n : Num} {G : Ctx n} {f f' g g' : Expr n} ->
             HasType G f OpF -> HasType G g (OpG f) ->
             ConvTm G f f' OpF -> ConvTm G g g' (OpG f) -> TyEq G (TyU f g) (TyU f' g')
  tyeq-Pi  : {n : Num} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)} ->
             IsType G A -> IsType (extend G A) B -> IsType (extend G A) B' ->
             TyEq G A A' -> TyEq (extend G A) B B' -> TyEq G (PiB A B) (PiB A' B')
  tyeq-Sigma : {n : Num} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)} ->
             IsType G A -> IsType (extend G A) B -> IsType (extend G A) B' ->
             TyEq G A A' -> TyEq (extend G A) B B' -> TyEq G (SigmaB A B) (SigmaB A' B')

  -- decoding of the codes in V
  tyeq-El-PiV  : {n : Num} {G : Ctx n} {a : Expr n} {b : Expr (suc n)} ->
                 HasType G a V -> HasType (extend G (ElV a)) b V ->
                 TyEq G (ElV (PiV a (Lam (ElV a) b))) (PiB (ElV a) (ElV b))
  tyeq-El-SigV : {n : Num} {G : Ctx n} {a : Expr n} {b : Expr (suc n)} ->
                 HasType G a V -> HasType (extend G (ElV a)) b V ->
                 TyEq G (ElV (SigV a (Lam (ElV a) b))) (SigmaB (ElV a) (ElV b))
  tyeq-El-NatV : {n : Num} {G : Ctx n} -> WfCtx G -> TyEq G (ElV NatV) Nat
  tyeq-El-UV   : {n : Num} {G : Ctx n} {f g : Expr n} ->
                 HasType G f OpF -> HasType G g (OpG f) -> TyEq G (ElV (UV f g)) (TyU f g)

  -- full decoding of the recursive subuniverse:  T_U(a) = T_V(T^ a)
  tyeq-ElU-That : {n : Num} {G : Ctx n} {f g a : Expr n} ->
                  HasType G a (TyU f g) -> TyEq G (ElU f g a) (ElV (That a))

------------------------------------------------------------------------
-- Term equality
------------------------------------------------------------------------

data ConvTm where
  conv-refl  : {n : Num} {G : Ctx n} {t A : Expr n} -> HasType G t A -> ConvTm G t t A
  conv-sym   : {n : Num} {G : Ctx n} {t u A : Expr n} -> ConvTm G t u A -> ConvTm G u t A
  conv-trans : {n : Num} {G : Ctx n} {t u w A : Expr n} ->
               ConvTm G t u A -> ConvTm G u w A -> ConvTm G t w A
  conv-conv  : {n : Num} {G : Ctx n} {t u A B : Expr n} ->
               ConvTm G t u A -> TyEq G A B -> ConvTm G t u B

  -- Pi: beta, eta
  conv-beta : {n : Num} {G : Ctx n} {A a : Expr n} {B t : Expr (suc n)} ->
              IsType G A -> IsType (extend G A) B -> HasType (extend G A) t B -> HasType G a A ->
              ConvTm G (appB A B (Lam A t) a) (subst1 t a) (subst1 B a)
  conv-funext : {n : Num} {G : Ctx n} {A t t' : Expr n} {B : Expr (suc n)} ->
              IsType G A -> IsType (extend G A) B ->
              HasType G t (PiB A B) -> HasType G t' (PiB A B) ->
              ConvTm (extend G A) (appB (wkExpr A) (renExpr (liftRen wkRen) B) (wkExpr t) x0)
                                  (appB (wkExpr A) (renExpr (liftRen wkRen) B) (wkExpr t') x0) B ->
              ConvTm G t t' (PiB A B)

  -- Sigma: beta, surjective pairing
  conv-fst-beta : {n : Num} {G : Ctx n} {A a b : Expr n} {B : Expr (suc n)} ->
              IsType G A -> IsType (extend G A) B -> HasType G a A -> HasType G b (subst1 B a) ->
              ConvTm G (Fst A (Lam A B) (Pair A (Lam A B) a b)) a A
  conv-snd-beta : {n : Num} {G : Ctx n} {A a b : Expr n} {B : Expr (suc n)} ->
              IsType G A -> IsType (extend G A) B -> HasType G a A -> HasType G b (subst1 B a) ->
              ConvTm G (Snd A (Lam A B) (Pair A (Lam A B) a b)) b (subst1 B a)
  conv-pairext : {n : Num} {G : Ctx n} {A t t' : Expr n} {B : Expr (suc n)} ->
              IsType G A -> IsType (extend G A) B ->
              HasType G t (SigmaB A B) -> HasType G t' (SigmaB A B) ->
              ConvTm G (Fst A (Lam A B) t) (Fst A (Lam A B) t') A ->
              ConvTm G (Snd A (Lam A B) t) (Snd A (Lam A B) t') (subst1 B (Fst A (Lam A B) t)) ->
              ConvTm G t t' (SigmaB A B)

  -- N: iota
  conv-rec-zero : {n : Num} {G : Ctx n} {z s : Expr n} {C : Expr (suc n)} ->
              IsType (extend G Nat) C -> HasType G z (subst1 C Zero) -> HasType G s (RecStep C) ->
              ConvTm G (Rec (Lam Nat C) z s Zero) z (subst1 C Zero)
  conv-rec-suc : {n : Num} {G : Ctx n} {z s k : Expr n} {C : Expr (suc n)} ->
              IsType (extend G Nat) C -> HasType G z (subst1 C Zero) -> HasType G s (RecStep C) ->
              HasType G k Nat ->
              ConvTm G (Rec (Lam Nat C) z s (Suc k))
                       (appB (subst1 C k) (wkExpr (subst1 C (Suc k)))
                          (appB Nat (Arr C (substExpr sucSub C)) s k) (Rec (Lam Nat C) z s k))
                       (subst1 C (Suc k))

  -- congruences of the eliminations and of Suc, Rec
  -- (annotations may change along a type equality: needed for the section,
  --  since Russell derives e.g. Lam A t = Lam A' t from funext + beta)
  conv-Lam : {n : Num} {G : Ctx n} {A A' : Expr n} {B t t' : Expr (suc n)} ->
              IsType G A -> IsType (extend G A) B -> TyEq G A A' ->
              ConvTm (extend G A) t t' B ->
              ConvTm G (Lam A t) (Lam A' t') (PiB A B)
  conv-App : {n : Num} {G : Ctx n} {A A' c c' a a' : Expr n} {B B' : Expr (suc n)} ->
              IsType G A -> IsType (extend G A) B -> TyEq G A A' -> TyEq (extend G A) B B' ->
              ConvTm G c c' (PiB A B) -> ConvTm G a a' A ->
              ConvTm G (appB A B c a) (appB A' B' c' a') (subst1 B a)
  conv-Pair : {n : Num} {G : Ctx n} {A A' a a' b b' : Expr n} {B B' : Expr (suc n)} ->
              IsType G A -> IsType (extend G A) B -> TyEq G A A' -> TyEq (extend G A) B B' ->
              ConvTm G a a' A -> ConvTm G b b' (subst1 B a) ->
              ConvTm G (Pair A (Lam A B) a b) (Pair A' (Lam A' B') a' b') (SigmaB A B)
  conv-Fst : {n : Num} {G : Ctx n} {A A' t t' : Expr n} {B B' : Expr (suc n)} ->
              IsType G A -> IsType (extend G A) B -> TyEq G A A' -> TyEq (extend G A) B B' ->
              ConvTm G t t' (SigmaB A B) ->
              ConvTm G (Fst A (Lam A B) t) (Fst A' (Lam A' B') t') A
  conv-Snd : {n : Num} {G : Ctx n} {A A' t t' : Expr n} {B B' : Expr (suc n)} ->
              IsType G A -> IsType (extend G A) B -> TyEq G A A' -> TyEq (extend G A) B B' ->
              ConvTm G t t' (SigmaB A B) ->
              ConvTm G (Snd A (Lam A B) t) (Snd A' (Lam A' B') t') (subst1 B (Fst A (Lam A B) t))
  conv-Suc : {n : Num} {G : Ctx n} {t t' : Expr n} -> ConvTm G t t' Nat -> ConvTm G (Suc t) (Suc t') Nat
  conv-Rec : {n : Num} {G : Ctx n} {z z' s s' k k' : Expr n} {C C' : Expr (suc n)} ->
              IsType (extend G Nat) C -> IsType (extend G Nat) C' -> TyEq (extend G Nat) C C' ->
              ConvTm G z z' (subst1 C Zero) -> ConvTm G s s' (RecStep C) -> ConvTm G k k' Nat ->
              ConvTm G (Rec (Lam Nat C) z s k) (Rec (Lam Nat C') z' s' k') (subst1 C k)

  -- congruences of the codes in V
  conv-PiV : {n : Num} {G : Ctx n} {a a' : Expr n} {b b' : Expr (suc n)} ->
              HasType G a V -> HasType (extend G (ElV a)) b V -> HasType (extend G (ElV a)) b' V ->
              ConvTm G a a' V -> ConvTm (extend G (ElV a)) b b' V ->
              ConvTm G (PiV a (Lam (ElV a) b)) (PiV a' (Lam (ElV a') b')) V
  conv-SigV : {n : Num} {G : Ctx n} {a a' : Expr n} {b b' : Expr (suc n)} ->
              HasType G a V -> HasType (extend G (ElV a)) b V -> HasType (extend G (ElV a)) b' V ->
              ConvTm G a a' V -> ConvTm (extend G (ElV a)) b b' V ->
              ConvTm G (SigV a (Lam (ElV a) b)) (SigV a' (Lam (ElV a') b')) V
  conv-UV : {n : Num} {G : Ctx n} {f f' g g' : Expr n} ->
              HasType G f OpF -> HasType G g (OpG f) ->
              ConvTm G f f' OpF -> ConvTm G g g' (OpG f) -> ConvTm G (UV f g) (UV f' g') V

  -- congruences of the codes in U_{f,g}
  conv-PiU : {n : Num} {G : Ctx n} {f g a a' : Expr n} {b b' : Expr (suc n)} ->
              HasType G a (TyU f g) -> HasType (extend G (ElU f g a)) b (wkExpr (TyU f g)) ->
              HasType (extend G (ElU f g a)) b' (wkExpr (TyU f g)) ->
              ConvTm G a a' (TyU f g) -> ConvTm (extend G (ElU f g a)) b b' (wkExpr (TyU f g)) ->
              ConvTm G (PiU f g a (Lam (ElU f g a) b)) (PiU f g a' (Lam (ElU f g a') b')) (TyU f g)
  conv-SigU : {n : Num} {G : Ctx n} {f g a a' : Expr n} {b b' : Expr (suc n)} ->
              HasType G a (TyU f g) -> HasType (extend G (ElU f g a)) b (wkExpr (TyU f g)) ->
              HasType (extend G (ElU f g a)) b' (wkExpr (TyU f g)) ->
              ConvTm G a a' (TyU f g) -> ConvTm (extend G (ElU f g a)) b b' (wkExpr (TyU f g)) ->
              ConvTm G (SigU f g a (Lam (ElU f g a) b)) (SigU f g a' (Lam (ElU f g a') b')) (TyU f g)
  conv-Fhat : {n : Num} {G : Ctx n} {f g a a' : Expr n} {b b' : Expr (suc n)} ->
              HasType G f OpF -> HasType G g (OpG f) ->
              HasType G a (TyU f g) -> HasType (extend G (ElU f g a)) b (wkExpr (TyU f g)) ->
              HasType (extend G (ElU f g a)) b' (wkExpr (TyU f g)) ->
              ConvTm G a a' (TyU f g) -> ConvTm (extend G (ElU f g a)) b b' (wkExpr (TyU f g)) ->
              ConvTm G (Fhat f g a (Lam (ElU f g a) b)) (Fhat f g a' (Lam (ElU f g a') b')) (TyU f g)
  conv-Ghat : {n : Num} {G : Ctx n} {f g a a' c c' : Expr n} {b b' : Expr (suc n)} ->
              HasType G f OpF -> HasType G g (OpG f) ->
              HasType G a (TyU f g) -> HasType (extend G (ElU f g a)) b (wkExpr (TyU f g)) ->
              HasType (extend G (ElU f g a)) b' (wkExpr (TyU f g)) ->
              ConvTm G a a' (TyU f g) -> ConvTm (extend G (ElU f g a)) b b' (wkExpr (TyU f g)) ->
              ConvTm G c c' (ElU f g (Fhat f g a (Lam (ElU f g a) b))) ->
              ConvTm G (Ghat f g a (Lam (ElU f g a) b) c) (Ghat f g a' (Lam (ElU f g a') b') c') (TyU f g)
  conv-That : {n : Num} {G : Ctx n} {f g a a' : Expr n} ->
              ConvTm G a a' (TyU f g) -> ConvTm G (That a) (That a') V

  -- T^ commutes with the basic codes (recursive subuniverse)
  conv-That-PiU : {n : Num} {G : Ctx n} {f g a : Expr n} {b : Expr (suc n)} ->
              HasType G a (TyU f g) -> HasType (extend G (ElU f g a)) b (wkExpr (TyU f g)) ->
              ConvTm G (That (PiU f g a (Lam (ElU f g a) b)))
                       (PiV (That a) (Lam (ElV (That a)) (That b))) V
  conv-That-SigU : {n : Num} {G : Ctx n} {f g a : Expr n} {b : Expr (suc n)} ->
              HasType G a (TyU f g) -> HasType (extend G (ElU f g a)) b (wkExpr (TyU f g)) ->
              ConvTm G (That (SigU f g a (Lam (ElU f g a) b)))
                       (SigV (That a) (Lam (ElV (That a)) (That b))) V
  conv-That-NatU : {n : Num} {G : Ctx n} {f g : Expr n} ->
              IsType G (TyU f g) -> ConvTm G (That (NatU f g)) NatV V

  -- f^, g^ reflect (f, g)  (the analogue of the Russell delta-equations)
  conv-That-Fhat : {n : Num} {G : Ctx n} {f g a : Expr n} {b : Expr (suc n)} ->
              HasType G f OpF -> HasType G g (OpG f) ->
              HasType G a (TyU f g) -> HasType (extend G (ElU f g a)) b (wkExpr (TyU f g)) ->
              ConvTm G (That (Fhat f g a (Lam (ElU f g a) b)))
                       (fApp f (That a) (Lam (ElV (That a)) (That b))) V
  conv-That-Ghat : {n : Num} {G : Ctx n} {f g a c : Expr n} {b : Expr (suc n)} ->
              HasType G f OpF -> HasType G g (OpG f) ->
              HasType G a (TyU f g) -> HasType (extend G (ElU f g a)) b (wkExpr (TyU f g)) ->
              HasType G c (ElU f g (Fhat f g a (Lam (ElU f g a) b))) ->
              ConvTm G (That (Ghat f g a (Lam (ElU f g a) b) c))
                       (gApp f g (That a) (Lam (ElV (That a)) (That b)) c) V

  -- REFLECTION: T^ is faithful
  conv-reflect : {n : Num} {G : Ctx n} {f g a b : Expr n} ->
              HasType G a (TyU f g) -> HasType G b (TyU f g) ->
              ConvTm G (That a) (That b) V -> ConvTm G a b (TyU f g)
