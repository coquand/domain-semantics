{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Syntax/Inv.agda
--
-- Inversion of typing for MAHLORT/TarskiTyping, one lemma per term
-- former, by induction on the derivation through ty-conv (ERT style).
-- Tarski has no subsumption, so every result is an equality
--   eq : TyEq G C P
-- of the given type C with the principal type P.  No injectivity is
-- used: the annotations determine everything except the codomain of a
-- Lam, which is returned (B).  An annotation  F  that the rule forces to
-- be a family  Lam A B  comes back as  isF : Eq F (Lam A B).
------------------------------------------------------------------------

module MAHLORT.Syntax.Inv where

open import MAHLO.Basic hiding (Sigma)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Subst
open import MAHLORT.Syntax.Wf
open import MAHLORT.Syntax.Presup

private
  tr : {n : Num} {G : Ctx n} {C C' P : Expr n} -> TyEq G C P -> TyEq G C C' -> TyEq G C' P
  tr e q = tyeq-trans (tyeq-sym q) e

------------------------------------------------------------------------
-- Variables
------------------------------------------------------------------------

record VarInv {n : Num} (G : Ctx n) (i : Fin n) (C : Expr n) : Set where
  constructor varinv
  field
    w  : WfCtx G
    eq : TyEq G C (lookup G i)

invVar : {n : Num} {G : Ctx n} {i : Fin n} {C : Expr n} -> HasType G (Var i) C -> VarInv G i C
invVar d@(ty-var w) = varinv w (tyeq-refl (pTm d))
invVar (ty-conv h q) = varinv w (tr eq q) where open VarInv (invVar h)

------------------------------------------------------------------------
-- Pi
------------------------------------------------------------------------

record LamInv {n : Num} (G : Ctx n) (A : Expr n) (t : Expr (suc n)) (C : Expr n) : Set where
  constructor laminv
  field
    B  : Expr (suc n)
    hA : IsType G A
    hB : IsType (extend G A) B
    ht : HasType (extend G A) t B
    eq : TyEq G C (PiB A B)

invLam : {n : Num} {G : Ctx n} {A C : Expr n} {t : Expr (suc n)} ->
         HasType G (Lam A t) C -> LamInv G A t C
invLam d@(ty-Lam hA hB ht) = laminv _ hA hB ht (tyeq-refl (pTm d))
invLam (ty-conv h q) = laminv B hA hB ht (tr eq q) where open LamInv (invLam h)

record AppInv {n : Num} (G : Ctx n) (A F c a C : Expr n) : Set where
  constructor appinv
  field
    B   : Expr (suc n)
    isF : Eq F (Lam A B)
    hA  : IsType G A
    hB  : IsType (extend G A) B
    hc  : HasType G c (PiB A B)
    ha  : HasType G a A
    eq  : TyEq G C (subst1 B a)

invApp : {n : Num} {G : Ctx n} {A F c a C : Expr n} -> HasType G (App A F c a) C -> AppInv G A F c a C
invApp d@(ty-App hA hB hc ha) = appinv _ refl hA hB hc ha (tyeq-refl (pTm d))
invApp (ty-conv h q) = appinv B isF hA hB hc ha (tr eq q) where open AppInv (invApp h)

------------------------------------------------------------------------
-- Sigma
------------------------------------------------------------------------

record PairInv {n : Num} (G : Ctx n) (A F a b C : Expr n) : Set where
  constructor pairinv
  field
    B   : Expr (suc n)
    isF : Eq F (Lam A B)
    hA  : IsType G A
    hB  : IsType (extend G A) B
    ha  : HasType G a A
    hb  : HasType G b (subst1 B a)
    eq  : TyEq G C (SigmaB A B)

invPair : {n : Num} {G : Ctx n} {A F a b C : Expr n} -> HasType G (Pair A F a b) C -> PairInv G A F a b C
invPair d@(ty-Pair hA hB ha hb) = pairinv _ refl hA hB ha hb (tyeq-refl (pTm d))
invPair (ty-conv h q) = pairinv B isF hA hB ha hb (tr eq q) where open PairInv (invPair h)

record FstInv {n : Num} (G : Ctx n) (A F t C : Expr n) : Set where
  constructor fstinv
  field
    B   : Expr (suc n)
    isF : Eq F (Lam A B)
    hA  : IsType G A
    hB  : IsType (extend G A) B
    ht  : HasType G t (SigmaB A B)
    eq  : TyEq G C A

invFst : {n : Num} {G : Ctx n} {A F t C : Expr n} -> HasType G (Fst A F t) C -> FstInv G A F t C
invFst d@(ty-Fst hA hB ht) = fstinv _ refl hA hB ht (tyeq-refl (pTm d))
invFst (ty-conv h q) = fstinv B isF hA hB ht (tr eq q) where open FstInv (invFst h)

record SndInv {n : Num} (G : Ctx n) (A F t C : Expr n) : Set where
  constructor sndinv
  field
    B   : Expr (suc n)
    isF : Eq F (Lam A B)
    hA  : IsType G A
    hB  : IsType (extend G A) B
    ht  : HasType G t (SigmaB A B)
    eq  : TyEq G C (subst1 B (Fst A (Lam A B) t))

invSnd : {n : Num} {G : Ctx n} {A F t C : Expr n} -> HasType G (Snd A F t) C -> SndInv G A F t C
invSnd d@(ty-Snd hA hB ht) = sndinv _ refl hA hB ht (tyeq-refl (pTm d))
invSnd (ty-conv h q) = sndinv B isF hA hB ht (tr eq q) where open SndInv (invSnd h)

------------------------------------------------------------------------
-- N
------------------------------------------------------------------------

invZero : {n : Num} {G : Ctx n} {C : Expr n} -> HasType G Zero C -> TyEq G C Nat
invZero d@(ty-Zero w) = tyeq-refl (pTm d)
invZero (ty-conv h q) = tr (invZero h) q

record SucInv {n : Num} (G : Ctx n) (t C : Expr n) : Set where
  constructor sucinv
  field
    ht : HasType G t Nat
    eq : TyEq G C Nat

invSuc : {n : Num} {G : Ctx n} {t C : Expr n} -> HasType G (Suc t) C -> SucInv G t C
invSuc d@(ty-Suc ht) = sucinv ht (tyeq-refl (pTm d))
invSuc (ty-conv h q) = sucinv ht (tr eq q) where open SucInv (invSuc h)

record RecInv {n : Num} (G : Ctx n) (M z s k D : Expr n) : Set where
  constructor recinv
  field
    C   : Expr (suc n)
    isM : Eq M (Lam Nat C)
    hC  : IsType (extend G Nat) C
    hz  : HasType G z (subst1 C Zero)
    hs  : HasType G s (RecStep C)
    hk  : HasType G k Nat
    eq  : TyEq G D (subst1 C k)

invRec : {n : Num} {G : Ctx n} {M z s k D : Expr n} -> HasType G (Rec M z s k) D -> RecInv G M z s k D
invRec d@(ty-Rec hC hz hs hk) = recinv _ refl hC hz hs hk (tyeq-refl (pTm d))
invRec (ty-conv h q) = recinv C isM hC hz hs hk (tr eq q) where open RecInv (invRec h)

------------------------------------------------------------------------
-- Codes in V
------------------------------------------------------------------------

record PiVInv {n : Num} (G : Ctx n) (a F C : Expr n) : Set where
  constructor pivinv
  field
    b   : Expr (suc n)
    isF : Eq F (Lam (ElV a) b)
    ha  : HasType G a V
    hb  : HasType (extend G (ElV a)) b V
    eq  : TyEq G C V

invPiV : {n : Num} {G : Ctx n} {a F C : Expr n} -> HasType G (PiV a F) C -> PiVInv G a F C
invPiV d@(ty-PiV ha hb) = pivinv _ refl ha hb (tyeq-refl (pTm d))
invPiV (ty-conv h q) = pivinv b isF ha hb (tr eq q) where open PiVInv (invPiV h)

invSigV : {n : Num} {G : Ctx n} {a F C : Expr n} -> HasType G (SigV a F) C -> PiVInv G a F C
invSigV d@(ty-SigV ha hb) = pivinv _ refl ha hb (tyeq-refl (pTm d))
invSigV (ty-conv h q) = pivinv b isF ha hb (tr eq q) where open PiVInv (invSigV h)

record NatVInv {n : Num} (G : Ctx n) (C : Expr n) : Set where
  constructor natvinv
  field
    w  : WfCtx G
    eq : TyEq G C V

invNatV : {n : Num} {G : Ctx n} {C : Expr n} -> HasType G NatV C -> NatVInv G C
invNatV d@(ty-NatV w) = natvinv w (tyeq-refl (pTm d))
invNatV (ty-conv h q) = natvinv w (tr eq q) where open NatVInv (invNatV h)

record UVInv {n : Num} (G : Ctx n) (f g C : Expr n) : Set where
  constructor uvinv
  field
    hf : HasType G f OpF
    hg : HasType G g (OpG f)
    eq : TyEq G C V

invUV : {n : Num} {G : Ctx n} {f g C : Expr n} -> HasType G (UV f g) C -> UVInv G f g C
invUV d@(ty-UV hf hg) = uvinv hf hg (tyeq-refl (pTm d))
invUV (ty-conv h q) = uvinv hf hg (tr eq q) where open UVInv (invUV h)

------------------------------------------------------------------------
-- Codes in U_{f,g}
------------------------------------------------------------------------

record PiUInv {n : Num} (G : Ctx n) (f g a F C : Expr n) : Set where
  constructor piuinv
  field
    b   : Expr (suc n)
    isF : Eq F (Lam (ElU f g a) b)
    ha  : HasType G a (TyU f g)
    hb  : HasType (extend G (ElU f g a)) b (wkExpr (TyU f g))
    eq  : TyEq G C (TyU f g)

invPiU : {n : Num} {G : Ctx n} {f g a F C : Expr n} -> HasType G (PiU f g a F) C -> PiUInv G f g a F C
invPiU d@(ty-PiU ha hb) = piuinv _ refl ha hb (tyeq-refl (pTm d))
invPiU (ty-conv h q) = piuinv b isF ha hb (tr eq q) where open PiUInv (invPiU h)

invSigU : {n : Num} {G : Ctx n} {f g a F C : Expr n} -> HasType G (SigU f g a F) C -> PiUInv G f g a F C
invSigU d@(ty-SigU ha hb) = piuinv _ refl ha hb (tyeq-refl (pTm d))
invSigU (ty-conv h q) = piuinv b isF ha hb (tr eq q) where open PiUInv (invSigU h)

record NatUInv {n : Num} (G : Ctx n) (f g C : Expr n) : Set where
  constructor natuinv
  field
    hU : IsType G (TyU f g)
    eq : TyEq G C (TyU f g)

invNatU : {n : Num} {G : Ctx n} {f g C : Expr n} -> HasType G (NatU f g) C -> NatUInv G f g C
invNatU d@(ty-NatU hU) = natuinv hU (tyeq-refl (pTm d))
invNatU (ty-conv h q) = natuinv hU (tr eq q) where open NatUInv (invNatU h)

record FhatInv {n : Num} (G : Ctx n) (f g a F C : Expr n) : Set where
  constructor fhatinv
  field
    b   : Expr (suc n)
    isF : Eq F (Lam (ElU f g a) b)
    hf  : HasType G f OpF
    hg  : HasType G g (OpG f)
    ha  : HasType G a (TyU f g)
    hb  : HasType (extend G (ElU f g a)) b (wkExpr (TyU f g))
    eq  : TyEq G C (TyU f g)

invFhat : {n : Num} {G : Ctx n} {f g a F C : Expr n} -> HasType G (Fhat f g a F) C -> FhatInv G f g a F C
invFhat d@(ty-Fhat hf hg ha hb) = fhatinv _ refl hf hg ha hb (tyeq-refl (pTm d))
invFhat (ty-conv h q) = fhatinv b isF hf hg ha hb (tr eq q) where open FhatInv (invFhat h)

record GhatInv {n : Num} (G : Ctx n) (f g a F c C : Expr n) : Set where
  constructor ghatinv
  field
    b   : Expr (suc n)
    isF : Eq F (Lam (ElU f g a) b)
    hf  : HasType G f OpF
    hg  : HasType G g (OpG f)
    ha  : HasType G a (TyU f g)
    hb  : HasType (extend G (ElU f g a)) b (wkExpr (TyU f g))
    hc  : HasType G c (ElU f g (Fhat f g a (Lam (ElU f g a) b)))
    eq  : TyEq G C (TyU f g)

invGhat : {n : Num} {G : Ctx n} {f g a F c C : Expr n} ->
          HasType G (Ghat f g a F c) C -> GhatInv G f g a F c C
invGhat d@(ty-Ghat hf hg ha hb hc) = ghatinv _ refl hf hg ha hb hc (tyeq-refl (pTm d))
invGhat (ty-conv h q) = ghatinv b isF hf hg ha hb hc (tr eq q) where open GhatInv (invGhat h)

-- T^ a : the subuniverse of  a  is returned
record ThatInv {n : Num} (G : Ctx n) (a C : Expr n) : Set where
  constructor thatinv
  field
    f  : Expr n
    g  : Expr n
    ha : HasType G a (TyU f g)
    eq : TyEq G C V

invThat : {n : Num} {G : Ctx n} {a C : Expr n} -> HasType G (That a) C -> ThatInv G a C
invThat d@(ty-That ha) = thatinv _ _ ha (tyeq-refl (pTm d))
invThat (ty-conv h q) = thatinv f g ha (tr eq q) where open ThatInv (invThat h)

------------------------------------------------------------------------
-- Types have no type: V, T_V a, U_{f,g}, T_U a, Pi, Sigma, N are not terms
------------------------------------------------------------------------

noV : {n : Num} {G : Ctx n} {C : Expr n} -> HasType G V C -> Empty
noV (ty-conv h q) = noV h

noElV : {n : Num} {G : Ctx n} {a C : Expr n} -> HasType G (ElV a) C -> Empty
noElV (ty-conv h q) = noElV h

noTyU : {n : Num} {G : Ctx n} {f g C : Expr n} -> HasType G (TyU f g) C -> Empty
noTyU (ty-conv h q) = noTyU h

noElU : {n : Num} {G : Ctx n} {f g a C : Expr n} -> HasType G (ElU f g a) C -> Empty
noElU (ty-conv h q) = noElU h

noPi : {n : Num} {G : Ctx n} {A F C : Expr n} -> HasType G (Pi A F) C -> Empty
noPi (ty-conv h q) = noPi h

noSigma : {n : Num} {G : Ctx n} {A F C : Expr n} -> HasType G (Sigma A F) C -> Empty
noSigma (ty-conv h q) = noSigma h

noNat : {n : Num} {G : Ctx n} {C : Expr n} -> HasType G Nat C -> Empty
noNat (ty-conv h q) = noNat h
