{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Valid/HeadRed.agda
--
-- Untyped weak-head reduction of the Tarski syntax, used by the logical
-- relation (the Tarski port of MAHLOINJ/Valid/HeadRed).
--
--   terms : beta, pi (projections of pairs), iota (rec), and the
--           equations of the embedding T^ (That): T^ commutes with the
--           codes of U_{f,g}, and T^ f^ / T^ g^ unfold to f / g;
--   types : the decoding El_V of the codes in V, and the full decoding
--           El_U(a) -> El_V(T^ a);
--   with head congruences (application, projections, rec, That, El_V).
--
-- The reduction ignores the annotations (of App, Fst, Snd, and the
-- domains of the families of the codes).  It is deterministic.
------------------------------------------------------------------------

module MAHLORT.Valid.HeadRed where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLORT.TarskiSyntax

-- the contractum of rec(\x:X.C, z, s, S k)
recSuc : {n : Num} -> Expr n -> Expr (suc n) -> Expr n -> Expr n -> Expr n -> Expr n
recSuc X C z s k =
  appB (subst1 C k) (wkExpr (subst1 C (Suc k)))
       (appB Nat (Arr C (substExpr sucSub C)) s k) (Rec (Lam X C) z s k)

data HR {n : Num} : Expr n -> Expr n -> Set where
  -- terms
  hr-beta     : {A F A' a : Expr n} {t : Expr (suc n)} -> HR (App A F (Lam A' t) a) (subst1 t a)
  hr-app      : {A F c c' a : Expr n} -> HR c c' -> HR (App A F c a) (App A F c' a)
  hr-fst-pair : {A F A' F' a b : Expr n} -> HR (Fst A F (Pair A' F' a b)) a
  hr-snd-pair : {A F A' F' a b : Expr n} -> HR (Snd A F (Pair A' F' a b)) b
  hr-fst      : {A F t t' : Expr n} -> HR t t' -> HR (Fst A F t) (Fst A F t')
  hr-snd      : {A F t t' : Expr n} -> HR t t' -> HR (Snd A F t) (Snd A F t')
  hr-rec-zero : {F z s : Expr n} -> HR (Rec F z s Zero) z
  hr-rec-suc  : {X z s k : Expr n} {C : Expr (suc n)} -> HR (Rec (Lam X C) z s (Suc k)) (recSuc X C z s k)
  hr-rec      : {F z s k k' : Expr n} -> HR k k' -> HR (Rec F z s k) (Rec F z s k')
  -- the embedding T^
  hr-That     : {a a' : Expr n} -> HR a a' -> HR (That a) (That a')
  hr-That-PiU : {f g a X : Expr n} {b : Expr (suc n)} ->
                HR (That (PiU f g a (Lam X b))) (PiV (That a) (Lam (ElV (That a)) (That b)))
  hr-That-SigU : {f g a X : Expr n} {b : Expr (suc n)} ->
                HR (That (SigU f g a (Lam X b))) (SigV (That a) (Lam (ElV (That a)) (That b)))
  hr-That-NatU : {f g : Expr n} -> HR (That (NatU f g)) NatV
  hr-That-Fhat : {f g a X : Expr n} {b : Expr (suc n)} ->
                HR (That (Fhat f g a (Lam X b))) (fApp f (That a) (Lam (ElV (That a)) (That b)))
  hr-That-Ghat : {f g a X c : Expr n} {b : Expr (suc n)} ->
                HR (That (Ghat f g a (Lam X b) c)) (gApp f g (That a) (Lam (ElV (That a)) (That b)) c)
  -- types
  hr-ElV      : {a a' : Expr n} -> HR a a' -> HR (ElV a) (ElV a')
  hr-El-PiV   : {a X : Expr n} {b : Expr (suc n)} -> HR (ElV (PiV a (Lam X b))) (PiB (ElV a) (ElV b))
  hr-El-SigV  : {a X : Expr n} {b : Expr (suc n)} -> HR (ElV (SigV a (Lam X b))) (SigmaB (ElV a) (ElV b))
  hr-El-NatV  : HR (ElV NatV) Nat
  hr-El-UV    : {f g : Expr n} -> HR (ElV (UV f g)) (TyU f g)
  hr-ElU      : {f g a : Expr n} -> HR (ElU f g a) (ElV (That a))

data HRs {n : Num} : Expr n -> Expr n -> Set where
  hrs-refl : {t : Expr n} -> HRs t t
  hrs-step : {t t' t'' : Expr n} -> HR t t' -> HRs t' t'' -> HRs t t''

HRs-trans : {n : Num} {t t' t'' : Expr n} -> HRs t t' -> HRs t' t'' -> HRs t t''
HRs-trans hrs-refl q = q
HRs-trans (hrs-step r p) q = hrs-step r (HRs-trans p q)

HRs-app : {n : Num} {A F t t' a : Expr n} -> HRs t t' -> HRs (App A F t a) (App A F t' a)
HRs-app hrs-refl = hrs-refl
HRs-app (hrs-step r p) = hrs-step (hr-app r) (HRs-app p)

HRs-fst : {n : Num} {A F t t' : Expr n} -> HRs t t' -> HRs (Fst A F t) (Fst A F t')
HRs-fst hrs-refl = hrs-refl
HRs-fst (hrs-step r p) = hrs-step (hr-fst r) (HRs-fst p)

HRs-snd : {n : Num} {A F t t' : Expr n} -> HRs t t' -> HRs (Snd A F t) (Snd A F t')
HRs-snd hrs-refl = hrs-refl
HRs-snd (hrs-step r p) = hrs-step (hr-snd r) (HRs-snd p)

HRs-rec : {n : Num} {F z s k k' : Expr n} -> HRs k k' -> HRs (Rec F z s k) (Rec F z s k')
HRs-rec hrs-refl = hrs-refl
HRs-rec (hrs-step r p) = hrs-step (hr-rec r) (HRs-rec p)

HRs-That : {n : Num} {a a' : Expr n} -> HRs a a' -> HRs (That a) (That a')
HRs-That hrs-refl = hrs-refl
HRs-That (hrs-step r p) = hrs-step (hr-That r) (HRs-That p)

HRs-ElV : {n : Num} {a a' : Expr n} -> HRs a a' -> HRs (ElV a) (ElV a')
HRs-ElV hrs-refl = hrs-refl
HRs-ElV (hrs-step r p) = hrs-step (hr-ElV r) (HRs-ElV p)

------------------------------------------------------------------------
-- Determinism
------------------------------------------------------------------------

NoRed : {n : Num} -> Expr n -> Set
NoRed t = {t' : _} -> HR t t' -> Empty

nored-Lam : {n : Num} {A : Expr n} {t : Expr (suc n)} -> NoRed (Lam A t)
nored-Lam ()
nored-Pair : {n : Num} {A F a b : Expr n} -> NoRed (Pair A F a b)
nored-Pair ()
nored-Zero : {n : Num} -> NoRed (Zero {n})
nored-Zero ()
nored-Suc : {n : Num} {t : Expr n} -> NoRed (Suc t)
nored-Suc ()
nored-Pi : {n : Num} {A F : Expr n} -> NoRed (Pi A F)
nored-Pi ()
nored-Sigma : {n : Num} {A F : Expr n} -> NoRed (Sigma A F)
nored-Sigma ()
nored-Nat : {n : Num} -> NoRed (Nat {n})
nored-Nat ()
nored-V : {n : Num} -> NoRed (V {n})
nored-V ()
nored-TyU : {n : Num} {f g : Expr n} -> NoRed (TyU f g)
nored-TyU ()
nored-PiV : {n : Num} {a F : Expr n} -> NoRed (PiV a F)
nored-PiV ()
nored-SigV : {n : Num} {a F : Expr n} -> NoRed (SigV a F)
nored-SigV ()
nored-NatV : {n : Num} -> NoRed (NatV {n})
nored-NatV ()
nored-UV : {n : Num} {f g : Expr n} -> NoRed (UV f g)
nored-UV ()
nored-PiU : {n : Num} {f g a F : Expr n} -> NoRed (PiU f g a F)
nored-PiU ()
nored-SigU : {n : Num} {f g a F : Expr n} -> NoRed (SigU f g a F)
nored-SigU ()
nored-NatU : {n : Num} {f g : Expr n} -> NoRed (NatU f g)
nored-NatU ()
nored-Fhat : {n : Num} {f g a F : Expr n} -> NoRed (Fhat f g a F)
nored-Fhat ()
nored-Ghat : {n : Num} {f g a F c : Expr n} -> NoRed (Ghat f g a F c)
nored-Ghat ()

HR-det : {n : Num} {t t1 t2 : Expr n} -> HR t t1 -> HR t t2 -> Eq t1 t2
HR-det hr-beta hr-beta = refl
HR-det hr-beta (hr-app ())
HR-det (hr-app ()) hr-beta
HR-det (hr-app r1) (hr-app r2) = Eq-cong (\ x -> App _ _ x _) (HR-det r1 r2)
HR-det hr-fst-pair hr-fst-pair = refl
HR-det hr-fst-pair (hr-fst ())
HR-det (hr-fst ()) hr-fst-pair
HR-det (hr-fst r1) (hr-fst r2) = Eq-cong (Fst _ _) (HR-det r1 r2)
HR-det hr-snd-pair hr-snd-pair = refl
HR-det hr-snd-pair (hr-snd ())
HR-det (hr-snd ()) hr-snd-pair
HR-det (hr-snd r1) (hr-snd r2) = Eq-cong (Snd _ _) (HR-det r1 r2)
HR-det hr-rec-zero hr-rec-zero = refl
HR-det hr-rec-zero (hr-rec ())
HR-det hr-rec-suc hr-rec-suc = refl
HR-det hr-rec-suc (hr-rec ())
HR-det (hr-rec ()) hr-rec-zero
HR-det (hr-rec ()) hr-rec-suc
HR-det (hr-rec r1) (hr-rec r2) = Eq-cong (Rec _ _ _) (HR-det r1 r2)
HR-det (hr-That r1) (hr-That r2) = Eq-cong That (HR-det r1 r2)
HR-det (hr-That ()) hr-That-PiU
HR-det (hr-That ()) hr-That-SigU
HR-det (hr-That ()) hr-That-NatU
HR-det (hr-That ()) hr-That-Fhat
HR-det (hr-That ()) hr-That-Ghat
HR-det hr-That-PiU (hr-That ())
HR-det hr-That-PiU hr-That-PiU = refl
HR-det hr-That-SigU (hr-That ())
HR-det hr-That-SigU hr-That-SigU = refl
HR-det hr-That-NatU (hr-That ())
HR-det hr-That-NatU hr-That-NatU = refl
HR-det hr-That-Fhat (hr-That ())
HR-det hr-That-Fhat hr-That-Fhat = refl
HR-det hr-That-Ghat (hr-That ())
HR-det hr-That-Ghat hr-That-Ghat = refl
HR-det (hr-ElV r1) (hr-ElV r2) = Eq-cong ElV (HR-det r1 r2)
HR-det (hr-ElV ()) hr-El-PiV
HR-det (hr-ElV ()) hr-El-SigV
HR-det (hr-ElV ()) hr-El-NatV
HR-det (hr-ElV ()) hr-El-UV
HR-det hr-El-PiV (hr-ElV ())
HR-det hr-El-PiV hr-El-PiV = refl
HR-det hr-El-SigV (hr-ElV ())
HR-det hr-El-SigV hr-El-SigV = refl
HR-det hr-El-NatV (hr-ElV ())
HR-det hr-El-NatV hr-El-NatV = refl
HR-det hr-El-UV (hr-ElV ())
HR-det hr-El-UV hr-El-UV = refl
HR-det hr-ElU hr-ElU = refl

-- two reductions of the same term to non-reducing terms coincide
HRs-det : {n : Num} {t u v : Expr n} -> HRs t u -> HRs t v -> NoRed u -> NoRed v -> Eq u v
HRs-det hrs-refl hrs-refl nu nv = refl
HRs-det hrs-refl (hrs-step r q) nu nv = Empty-elim (nu r)
HRs-det (hrs-step r p) hrs-refl nu nv = Empty-elim (nv r)
HRs-det (hrs-step r1 p) (hrs-step r2 q) nu nv =
  HRs-det p (transport (\ x -> HRs x _) (Eq-sym (HR-det r1 r2)) q) nu nv

-- a reduction sequence from t can be continued from any reduct on the way
HRs-from-step : {n : Num} {t t1 u : Expr n} -> HR t t1 -> HRs t u -> NoRed u -> HRs t1 u
HRs-from-step r hrs-refl nu = Empty-elim (nu r)
HRs-from-step r (hrs-step r' p) nu = transport (\ x -> HRs x _) (HR-det r' r) p

------------------------------------------------------------------------
-- Injectivity of the reached shapes
------------------------------------------------------------------------

private
  dom1 : {n : Num} -> Expr n -> Expr n
  dom1 (Var _) = Nat
  dom1 (Lam _ _) = Nat
  dom1 (App _ _ _ _) = Nat
  dom1 (Pi A F) = A
  dom1 (Sigma A F) = A
  dom1 (Pair _ _ _ _) = Nat
  dom1 (Fst _ _ _) = Nat
  dom1 (Snd _ _ _) = Nat
  dom1 Nat = Nat
  dom1 Zero = Nat
  dom1 (Suc _) = Nat
  dom1 (Rec _ _ _ _) = Nat
  dom1 V = Nat
  dom1 (ElV _) = Nat
  dom1 (TyU _ _) = Nat
  dom1 (ElU _ _ _) = Nat
  dom1 (PiV _ _) = Nat
  dom1 (SigV _ _) = Nat
  dom1 NatV = Nat
  dom1 (UV _ _) = Nat
  dom1 (PiU _ _ _ _) = Nat
  dom1 (SigU _ _ _ _) = Nat
  dom1 (NatU _ _) = Nat
  dom1 (Fhat _ _ _ _) = Nat
  dom1 (Ghat _ _ _ _ _) = Nat
  dom1 (That _) = Nat

  lamB : {n : Num} -> Expr n -> Expr (suc n)
  lamB (Var _) = Nat
  lamB (Lam X B) = B
  lamB (App _ _ _ _) = Nat
  lamB (Pi _ _) = Nat
  lamB (Sigma _ _) = Nat
  lamB (Pair _ _ _ _) = Nat
  lamB (Fst _ _ _) = Nat
  lamB (Snd _ _ _) = Nat
  lamB Nat = Nat
  lamB Zero = Nat
  lamB (Suc _) = Nat
  lamB (Rec _ _ _ _) = Nat
  lamB V = Nat
  lamB (ElV _) = Nat
  lamB (TyU _ _) = Nat
  lamB (ElU _ _ _) = Nat
  lamB (PiV _ _) = Nat
  lamB (SigV _ _) = Nat
  lamB NatV = Nat
  lamB (UV _ _) = Nat
  lamB (PiU _ _ _ _) = Nat
  lamB (SigU _ _ _ _) = Nat
  lamB (NatU _ _) = Nat
  lamB (Fhat _ _ _ _) = Nat
  lamB (Ghat _ _ _ _ _) = Nat
  lamB (That _) = Nat

  body1 : {n : Num} -> Expr n -> Expr (suc n)
  body1 (Var _) = Nat
  body1 (Lam _ _) = Nat
  body1 (App _ _ _ _) = Nat
  body1 (Pi A F) = lamB F
  body1 (Sigma A F) = lamB F
  body1 (Pair _ _ _ _) = Nat
  body1 (Fst _ _ _) = Nat
  body1 (Snd _ _ _) = Nat
  body1 Nat = Nat
  body1 Zero = Nat
  body1 (Suc _) = Nat
  body1 (Rec _ _ _ _) = Nat
  body1 V = Nat
  body1 (ElV _) = Nat
  body1 (TyU _ _) = Nat
  body1 (ElU _ _ _) = Nat
  body1 (PiV _ _) = Nat
  body1 (SigV _ _) = Nat
  body1 NatV = Nat
  body1 (UV _ _) = Nat
  body1 (PiU _ _ _ _) = Nat
  body1 (SigU _ _ _ _) = Nat
  body1 (NatU _ _) = Nat
  body1 (Fhat _ _ _ _) = Nat
  body1 (Ghat _ _ _ _ _) = Nat
  body1 (That _) = Nat

  pred1 : {n : Num} -> Expr n -> Expr n
  pred1 (Var _) = Nat
  pred1 (Lam _ _) = Nat
  pred1 (App _ _ _ _) = Nat
  pred1 (Pi _ _) = Nat
  pred1 (Sigma _ _) = Nat
  pred1 (Pair _ _ _ _) = Nat
  pred1 (Fst _ _ _) = Nat
  pred1 (Snd _ _ _) = Nat
  pred1 Nat = Nat
  pred1 Zero = Nat
  pred1 (Suc t) = t
  pred1 (Rec _ _ _ _) = Nat
  pred1 V = Nat
  pred1 (ElV _) = Nat
  pred1 (TyU _ _) = Nat
  pred1 (ElU _ _ _) = Nat
  pred1 (PiV _ _) = Nat
  pred1 (SigV _ _) = Nat
  pred1 NatV = Nat
  pred1 (UV _ _) = Nat
  pred1 (PiU _ _ _ _) = Nat
  pred1 (SigU _ _ _ _) = Nat
  pred1 (NatU _ _) = Nat
  pred1 (Fhat _ _ _ _) = Nat
  pred1 (Ghat _ _ _ _ _) = Nat
  pred1 (That _) = Nat

PiB-inj : {n : Num} {A A' : Expr n} {B B' : Expr (suc n)} -> Eq (PiB A B) (PiB A' B') -> Eq A A' * Eq B B'
PiB-inj e = Eq-cong dom1 e , Eq-cong body1 e

SigmaB-inj : {n : Num} {A A' : Expr n} {B B' : Expr (suc n)} -> Eq (SigmaB A B) (SigmaB A' B') -> Eq A A' * Eq B B'
SigmaB-inj e = Eq-cong dom1 e , Eq-cong body1 e

Suc-inj : {n : Num} {t t' : Expr n} -> Eq (Suc t) (Suc t') -> Eq t t'
Suc-inj e = Eq-cong pred1 e

------------------------------------------------------------------------
-- Annotation change in head position, and its simulation by HR
--
-- Ann t t' : t and t' differ only in the annotations of eliminations
-- (App, Fst, Snd) along the head spine.  The reduction ignores the
-- annotations, so it commutes with Ann (hrSim), and an Ann-variant of
-- a canonical form is the form itself.
------------------------------------------------------------------------

data Ann {n : Num} : Expr n -> Expr n -> Set where
  ann-refl : {t : Expr n} -> Ann t t
  ann-app  : {A F A' F' c c' a : Expr n} -> Ann c c' -> Ann (App A F c a) (App A' F' c' a)
  ann-fst  : {A F A' F' t t' : Expr n} -> Ann t t' -> Ann (Fst A F t) (Fst A' F' t')
  ann-snd  : {A F A' F' t t' : Expr n} -> Ann t t' -> Ann (Snd A F t) (Snd A' F' t')
  ann-rec  : {F z s k k' : Expr n} -> Ann k k' -> Ann (Rec F z s k) (Rec F z s k')
  ann-That : {a a' : Expr n} -> Ann a a' -> Ann (That a) (That a')
  ann-ElV  : {a a' : Expr n} -> Ann a a' -> Ann (ElV a) (ElV a')
  ann-ElU  : {f g a a' : Expr n} -> Ann a a' -> Ann (ElU f g a) (ElU f g a')

ann-sym : {n : Num} {t t' : Expr n} -> Ann t t' -> Ann t' t
ann-sym ann-refl = ann-refl
ann-sym (ann-app p) = ann-app (ann-sym p)
ann-sym (ann-fst p) = ann-fst (ann-sym p)
ann-sym (ann-snd p) = ann-snd (ann-sym p)
ann-sym (ann-rec p) = ann-rec (ann-sym p)
ann-sym (ann-That p) = ann-That (ann-sym p)
ann-sym (ann-ElV p) = ann-ElV (ann-sym p)
ann-sym (ann-ElU p) = ann-ElU (ann-sym p)

private
  annLam : {n : Num} {X : Expr n} {b : Expr (suc n)} {c : Expr n} -> Ann (Lam X b) c -> Eq (Lam X b) c
  annLam ann-refl = refl
  annPair : {n : Num} {A F a b c : Expr n} -> Ann (Pair A F a b) c -> Eq (Pair A F a b) c
  annPair ann-refl = refl
  annZero : {n : Num} {c : Expr n} -> Ann Zero c -> Eq Zero c
  annZero ann-refl = refl
  annSuc : {n : Num} {k c : Expr n} -> Ann (Suc k) c -> Eq (Suc k) c
  annSuc ann-refl = refl
  annCode : {n : Num} {a c : Expr n} -> NoRed a -> ({c : Expr n} -> Ann a c -> Eq a c) -> Ann a c -> Eq a c
  annCode _ h p = h p

-- one reduction step on the left is matched on the right
record Sim {n : Num} (t' u : Expr n) : Set where
  constructor sim
  field
    u'  : Expr n
    red : HR t' u'
    an  : Ann u u'

hrSim : {n : Num} {t t' u : Expr n} -> Ann t t' -> HR t u -> Sim t' u
hrSim ann-refl r = sim _ r ann-refl
hrSim (ann-app p) hr-beta with annLam p
... | refl = sim _ hr-beta ann-refl
hrSim (ann-app p) (hr-app r) = let s = hrSim p r in sim _ (hr-app (Sim.red s)) (ann-app (Sim.an s))
hrSim (ann-fst p) hr-fst-pair with annPair p
... | refl = sim _ hr-fst-pair ann-refl
hrSim (ann-fst p) (hr-fst r) = let s = hrSim p r in sim _ (hr-fst (Sim.red s)) (ann-fst (Sim.an s))
hrSim (ann-snd p) hr-snd-pair with annPair p
... | refl = sim _ hr-snd-pair ann-refl
hrSim (ann-snd p) (hr-snd r) = let s = hrSim p r in sim _ (hr-snd (Sim.red s)) (ann-snd (Sim.an s))
hrSim (ann-rec p) hr-rec-zero with annZero p
... | refl = sim _ hr-rec-zero ann-refl
hrSim (ann-rec p) hr-rec-suc with annSuc p
... | refl = sim _ hr-rec-suc ann-refl
hrSim (ann-rec p) (hr-rec r) = let s = hrSim p r in sim _ (hr-rec (Sim.red s)) (ann-rec (Sim.an s))
hrSim (ann-That p) (hr-That r) = let s = hrSim p r in sim _ (hr-That (Sim.red s)) (ann-That (Sim.an s))
hrSim (ann-That ann-refl) hr-That-PiU = sim _ hr-That-PiU ann-refl
hrSim (ann-That ann-refl) hr-That-SigU = sim _ hr-That-SigU ann-refl
hrSim (ann-That ann-refl) hr-That-NatU = sim _ hr-That-NatU ann-refl
hrSim (ann-That ann-refl) hr-That-Fhat = sim _ hr-That-Fhat ann-refl
hrSim (ann-That ann-refl) hr-That-Ghat = sim _ hr-That-Ghat ann-refl
hrSim (ann-ElV p) (hr-ElV r) = let s = hrSim p r in sim _ (hr-ElV (Sim.red s)) (ann-ElV (Sim.an s))
hrSim (ann-ElV ann-refl) hr-El-PiV = sim _ hr-El-PiV ann-refl
hrSim (ann-ElV ann-refl) hr-El-SigV = sim _ hr-El-SigV ann-refl
hrSim (ann-ElV ann-refl) hr-El-NatV = sim _ hr-El-NatV ann-refl
hrSim (ann-ElV ann-refl) hr-El-UV = sim _ hr-El-UV ann-refl
hrSim (ann-ElU p) hr-ElU = sim _ hr-ElU (ann-ElV (ann-That p))

-- many steps
record SimS {n : Num} (t' u : Expr n) : Set where
  constructor simS
  field
    u'  : Expr n
    red : HRs t' u'
    an  : Ann u u'

hrsSim : {n : Num} {t t' u : Expr n} -> Ann t t' -> HRs t u -> SimS t' u
hrsSim p hrs-refl = simS _ hrs-refl p
hrsSim p (hrs-step r rs) =
  let s = hrSim p r ; s' = hrsSim (Sim.an s) rs
  in simS _ (hrs-step (Sim.red s) (SimS.red s')) (SimS.an s')

------------------------------------------------------------------------
-- annotation change followed by reduction
------------------------------------------------------------------------

record AR {n : Num} (t u : Expr n) : Set where
  constructor ar2
  field
    mid  : Expr n
    an   : Ann t mid
    out  : Expr n
    rs   : HRs mid out
    an'  : Ann out u

-- annotation change, then reduction
ar : {n : Num} {t u : Expr n} (m : Expr n) -> Ann t m -> HRs m u -> AR t u
ar m p r = ar2 m p _ r ann-refl

ar-hrs : {n : Num} {t u : Expr n} -> HRs t u -> AR t u
ar-hrs r = ar _ ann-refl r

-- reduction, then annotation change
ar-post : {n : Num} {t m u : Expr n} -> HRs t m -> Ann m u -> AR t u
ar-post r p = ar2 _ ann-refl _ r p

-- a canonical form (rigid under Ann) reached from u is reached from t
Rigid : {n : Num} -> Expr n -> Set
Rigid {n} w = {w' : Expr n} -> Ann w w' -> Eq w w'

ar-to : {n : Num} {t u w : Expr n} -> AR t u -> HRs u w -> Rigid w -> HRs t w
ar-to (ar2 m p o rs p') r rw =
  let s1 = hrsSim (ann-sym p') r
      e1 = rw (SimS.an s1)
      r1 = transport (HRs o) (Eq-sym e1) (SimS.red s1)
      s2 = hrsSim (ann-sym p) (HRs-trans rs r1)
  in transport (HRs _) (Eq-sym (rw (SimS.an s2))) (SimS.red s2)

rigid-Pi : {n : Num} {A F : Expr n} -> Rigid (Pi A F)
rigid-Pi ann-refl = refl
rigid-Sigma : {n : Num} {A F : Expr n} -> Rigid (Sigma A F)
rigid-Sigma ann-refl = refl
rigid-Nat : {n : Num} -> Rigid (Nat {n})
rigid-Nat ann-refl = refl
rigid-V : {n : Num} -> Rigid (V {n})
rigid-V ann-refl = refl
rigid-TyU : {n : Num} {f g : Expr n} -> Rigid (TyU f g)
rigid-TyU ann-refl = refl
rigid-Zero : {n : Num} -> Rigid (Zero {n})
rigid-Zero ann-refl = refl
rigid-Suc : {n : Num} {k : Expr n} -> Rigid (Suc k)
rigid-Suc ann-refl = refl

-- congruences
ar-app : {n : Num} {A F M M1 N : Expr n} -> AR M M1 -> AR (App A F M N) (App A F M1 N)
ar-app {A = A} {F} {N = N} (ar2 m p o rs p') = ar2 (App A F m N) (ann-app p) (App A F o N) (HRs-app rs) (ann-app p')
ar-fst : {n : Num} {A F M M1 : Expr n} -> AR M M1 -> AR (Fst A F M) (Fst A F M1)
ar-fst {A = A} {F} (ar2 m p o rs p') = ar2 (Fst A F m) (ann-fst p) (Fst A F o) (HRs-fst rs) (ann-fst p')
ar-snd : {n : Num} {A F M M1 : Expr n} -> AR M M1 -> AR (Snd A F M) (Snd A F M1)
ar-snd {A = A} {F} (ar2 m p o rs p') = ar2 (Snd A F m) (ann-snd p) (Snd A F o) (HRs-snd rs) (ann-snd p')
ar-ElV : {n : Num} {M M1 : Expr n} -> AR M M1 -> AR (ElV M) (ElV M1)
ar-ElV (ar2 m p o rs p') = ar2 _ (ann-ElV p) _ (HRs-ElV rs) (ann-ElV p')
ar-That : {n : Num} {M M1 : Expr n} -> AR M M1 -> AR (That M) (That M1)
ar-That (ar2 m p o rs p') = ar2 _ (ann-That p) _ (HRs-That rs) (ann-That p')
