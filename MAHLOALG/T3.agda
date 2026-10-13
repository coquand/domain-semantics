{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOALG/T3.agda
--
-- (T3) for conversion, relative to the fixed point of Gamma only:
--
--   decConv  : Dec (G |- t = t' : C)          for well-typed t, t'
--   decTyEq  : Dec (G |- A = A')               for types A, A'
--   decPi / decSig / decU : the weak-head normal form of a type, with
--              witnesses (the fields of domain-e2's TCHyp)
--   U-inj    : U(f,g) = U(f',g')  ==>  f = f' : OpF,  g = g' : OpG f
--
-- Route: Theorem 16 (MAHLO/Soundness, concrete model) puts both sides
-- in Concrete's S (values with equal eta-normal forms); S is decidable
-- (computed values, etanf, deceq); completeness (MAHLOALG/Complete)
-- turns S + typing into a run of the algorithm, and algsound
-- (MAHLOINJ/Algo) turns the run into a conversion.
--
-- Deferred (d): a DETERMINISTIC variant of the algorithm, i.e. that the
-- algorithm itself terminates and rejects correctly (needed for an
-- implementation, not for the decidability theorems here).  AlgEq is a
-- judgement and admits several derivations; a deterministic variant
-- would require
--   (i)   in `alg`, both reducts weak-head normal (NoRed), hence unique
--         by HRs-det;
--   (ii)  eta only against the other kind: lambda/lambda before
--         lambda/other, pair/pair before pair/other;
--   (iii) no rule for two shapes of different classes.
-- Rejection is then justified by determinism, and the decision
-- procedure is a recursion with the completeness measure (lp, sz) on
-- the values, which exist for well-typed inputs (lfsigma Lemma 9.1).
--
-- MAHLOALG/T3PFix instantiates this module from the principle PFix.
------------------------------------------------------------------------

open import MAHLO.Fixpoint using (Fixpoint)
open import MAHLO.Concrete.Instance using (concreteTM ; concreteModel)

module MAHLOALG.T3 (Fx : Fixpoint concreteTM) where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Typing
open import MAHLO.Concrete.Tm
open import MAHLO.Concrete.Values
open import MAHLO.Concrete.Eta
open import MAHLO.Concrete.DecEq using (Dec ; yes ; no ; deceq)
open import MAHLO.Concrete.Rel using (SR ; sr ; NR ; nr)
open import MAHLO.Concrete.Den using (den)
open import MAHLO.Soundness concreteTM concreteModel Fx using (soundness-ne ; sTy ; sTyEq ; neutralEnv ; sCtx ; wt-safe)
open import MAHLO.Validity concreteTM concreteModel Fx using (TyV)
open import MAHLO.Type concreteTM concreteModel Fx using (safe)
open import MAHLOINJ.Syntax.Wf using (wfTy ; wfTm)
open import MAHLOINJ.Syntax.Presup using (pTE ; opGEq)
open import MAHLOINJ.Valid.HeadRed
open import MAHLOINJ.Final using (injHyp)
open import MAHLOINJ.Inversion.Hyp using (InjHyp)
open import MAHLOINJ.Inversion.Inv injHyp using (invUcode ; PiInv)
import MAHLOINJ.Inversion.Inv
open import MAHLOINJ.Algo.Alg
open import MAHLOINJ.Algo.Eval using (tyRed)
open import MAHLOINJ.Algo.All using (algsound ; algsound-ty)
open import MAHLOALG.Shape
open import MAHLOALG.Whnf
open import MAHLOALG.Complete

------------------------------------------------------------------------
-- soundness at the identity environment
------------------------------------------------------------------------

idN : {n : Num} (i : Fin n) -> NR (idE i) (idE i)
idN i = nr _ _ (⇓-self (v-ne ne-var)) (⇓-self (v-ne ne-var)) ne-var ne-var refl

convS : {n : Num} {G : Ctx n} {t t' C : Expr n} -> ConvTm G t t' C -> SR (den t idE) (den t' idE)
convS c = soundness-ne (wfTm (fst (MAHLOINJ.Syntax.Presup.pCv c))) c idE idN

tyS : {n : Num} {G : Ctx n} {A A' : Expr n} -> TyEq G A A' -> SR (den A idE) (den A' idE)
tyS {G = G} q = safe (TyV.ty (sTyEq q (neutralEnv G (sCtx G (wfTy (fst (pTE q)))) idE idN)))

tmS : {n : Num} {G : Ctx n} {t C : Expr n} -> HasType G t C -> SR (den t idE) (den t idE)
tmS h = wt-safe h idE idN

tySelf : {n : Num} {G : Ctx n} {A : Expr n} -> IsType G A -> SR (den A idE) (den A idE)
tySelf {G = G} iA = safe (TyV.ty (sTy iA (neutralEnv G (sCtx G (wfTy iA)) idE idN)))

private
  -- two S-witnesses for the same terms have the same normal forms
  sameNf : {a b : Tm} (s1 s2 : SR a b) -> Eq (etanf (SR.va s1)) (etanf (SR.vb s1)) ->
           Eq (etanf (SR.va s2)) (etanf (SR.vb s2))
  sameNf s1 s2 e =
    Eq-trans (Eq-cong etanf (⇓-unique (SR.da s2) (SR.da s1)))
      (Eq-trans e (Eq-cong etanf (⇓-unique (SR.db s1) (SR.db s2))))

  decS : {a b : Tm} -> SR a a -> SR b b -> Dec (SR a b)
  decS sa sb = go (deceq (etanf (SR.va sa)) (etanf (SR.va sb)))
    where
      go : Dec (Eq (etanf (SR.va sa)) (etanf (SR.va sb))) -> Dec (SR _ _)
      go (yes e) = yes (sr _ _ (SR.da sa) (SR.da sb) e)
      go (no f) = no (\ s -> f (Eq-trans (Eq-cong etanf (⇓-unique (SR.da sa) (SR.da s)))
                                  (Eq-trans (SR.eq s) (Eq-cong etanf (⇓-unique (SR.db s) (SR.da sb))))))

------------------------------------------------------------------------
-- decidability of conversion
------------------------------------------------------------------------

decConv : {n : Num} {G : Ctx n} {t t' C : Expr n} -> HasType G t C -> HasType G t' C -> Dec (ConvTm G t t' C)
decConv ht ht' = go (decS (tmS ht) (tmS ht'))
  where
    go : Dec (SR _ _) -> Dec (ConvTm _ _ _ _)
    go (yes s) = yes (algsound ht ht' (complete ht ht' s))
    go (no f) = no (\ c -> f (convS c))

decTyEq : {n : Num} {G : Ctx n} {A A' : Expr n} -> IsType G A -> IsType G A' -> Dec (TyEq G A A')
decTyEq iA iA' = go (decS (tySelf iA) (tySelf iA'))
  where
    go : Dec (SR _ _) -> Dec (TyEq _ _ _)
    go (yes s) = yes (algsound-ty iA iA' (complete-ty iA iA' s))
    go (no f) = no (\ q -> f (tyS q))

------------------------------------------------------------------------
-- weak-head normal forms of types
------------------------------------------------------------------------

private
  record TyWhnf {n : Num} (G : Ctx n) (C : Expr n) : Set where
    constructor tywhnf
    field
      w  : Expr n
      q  : TyEq G C w
      iw : IsType G w
      sh : SynSh w
      v  : Tm
      dv : den w idE ⇓ v

  tyWhnf : {n : Num} {G : Ctx n} {C : Expr n} -> IsType G C -> TyWhnf G C
  tyWhnf {C = C} iC =
    let s = tySelf iC ; W = whnfOf C (SR.da s) ; q = tyRed iC (WhnfRes.rs W)
    in tywhnf (WhnfRes.w W) q (snd (pTE q)) (WhnfRes.sh W) (SR.va s) (WhnfRes.dv W)

  -- a whnf type of one shape is not convertible to one of another shape
  notShape : {n : Num} {G : Ctx n} {w w0 : Expr n} (sh : SynSh w) (sh0 : SynSh w0) ->
    TyEq G w w0 -> Distinct (shK sh) (shK sh0) -> Empty
  notShape sh sh0 e dist = let s = tyS e in mismatch sh sh0 (SR.da s) (SR.db s) (SR.eq s) dist

  tyPiF' : {n : Num} {G : Ctx n} {A F : Expr n} -> IsType G (Pi A F) -> Sg (Expr (suc n)) (\ B -> Eq F (Lam A B))
  tyPiF' (isty-el h) = PiInv.B P , PiInv.eF P
    where P = MAHLOINJ.Inversion.Inv.invPi injHyp h
  tyPiF' (isty-Pi iA iB) = _ , refl

  tySigF' : {n : Num} {G : Ctx n} {A F : Expr n} -> IsType G (Sigma A F) -> Sg (Expr (suc n)) (\ B -> Eq F (Lam A B))
  tySigF' (isty-el h) = PiInv.B P , PiInv.eF P
    where P = MAHLOINJ.Inversion.Inv.invSigma injHyp h
  tySigF' (isty-Sigma iA iB) = _ , refl

ΣPi : {n : Num} -> Ctx n -> Expr n -> Set
ΣPi {n} G C = Sg (Expr n) (\ A -> Sg (Expr (suc n)) (\ B -> TyEq G C (PiB A B)))

ΣSig : {n : Num} -> Ctx n -> Expr n -> Set
ΣSig {n} G C = Sg (Expr n) (\ A -> Sg (Expr (suc n)) (\ B -> TyEq G C (SigmaB A B)))

ΣU : {n : Num} -> Ctx n -> Expr n -> Set
ΣU {n} G C = Sg (Expr n) (\ f -> Sg (Expr n) (\ g -> TyEq G C (Ucode f g)))


decPi : {n : Num} {G : Ctx n} {C : Expr n} -> IsType G C -> Dec (ΣPi G C)
decPi iC = go (TyWhnf.sh T) (TyWhnf.q T) (TyWhnf.iw T)
  where
    T = tyWhnf iC
    go : {w : Expr _} -> SynSh w -> TyEq _ _ w -> IsType _ w -> Dec (ΣPi _ _)
    go sh@(sh-ne _) q iw = no (\ r -> notShape sh sh-pi (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
    go sh@sh-lam q iw = no (\ r -> notShape sh sh-pi (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (_ , ()) }) , ((\ { (() , _) }) , (\ { (_ , ()) })))))
    go sh@sh-pair q iw = no (\ r -> notShape sh sh-pi (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (_ , ()) }) , ((\ { (() , _) }) , (\ { (_ , ()) })))))
    go (sh-pi {A} {F}) q iw = yes (A , (fst (tyPiF' iw) , transport (\ X -> TyEq _ _ (Pi A X)) (snd (tyPiF' iw)) q))
    go sh@sh-sig q iw = no (\ r -> notShape sh sh-pi (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
    go sh@sh-nat q iw = no (\ r -> notShape sh sh-pi (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
    go sh@sh-ze q iw = no (\ r -> notShape sh sh-pi (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
    go sh@sh-sc q iw = no (\ r -> notShape sh sh-pi (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
    go sh@sh-V q iw = no (\ r -> notShape sh sh-pi (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
    go sh@sh-U q iw = no (\ r -> notShape sh sh-pi (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))

decSig : {n : Num} {G : Ctx n} {C : Expr n} -> IsType G C -> Dec (ΣSig G C)
decSig iC = go (TyWhnf.sh T) (TyWhnf.q T) (TyWhnf.iw T)
  where
    T = tyWhnf iC
    go : {w : Expr _} -> SynSh w -> TyEq _ _ w -> IsType _ w -> Dec (ΣSig _ _)
    go sh@(sh-ne _) q iw = no (\ r -> notShape sh sh-sig (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
    go sh@sh-lam q iw = no (\ r -> notShape sh sh-sig (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (_ , ()) }) , ((\ { (() , _) }) , (\ { (_ , ()) })))))
    go sh@sh-pair q iw = no (\ r -> notShape sh sh-sig (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (_ , ()) }) , ((\ { (() , _) }) , (\ { (_ , ()) })))))
    go sh@sh-pi q iw = no (\ r -> notShape sh sh-sig (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
    go (sh-sig {A} {F}) q iw = yes (A , (fst (tySigF' iw) , transport (\ X -> TyEq _ _ (Sigma A X)) (snd (tySigF' iw)) q))
    go sh@sh-nat q iw = no (\ r -> notShape sh sh-sig (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
    go sh@sh-ze q iw = no (\ r -> notShape sh sh-sig (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
    go sh@sh-sc q iw = no (\ r -> notShape sh sh-sig (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
    go sh@sh-V q iw = no (\ r -> notShape sh sh-sig (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
    go sh@sh-U q iw = no (\ r -> notShape sh sh-sig (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))

decU : {n : Num} {G : Ctx n} {C : Expr n} -> IsType G C -> Dec (ΣU G C)
decU iC = go (TyWhnf.sh T) (TyWhnf.q T) (TyWhnf.iw T)
  where
    T = tyWhnf iC
    go : {w : Expr _} -> SynSh w -> TyEq _ _ w -> IsType _ w -> Dec (ΣU _ _)
    go sh@(sh-ne _) q iw = no (\ r -> notShape sh sh-U (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
    go sh@sh-lam q iw = no (\ r -> notShape sh sh-U (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (_ , ()) }) , ((\ { (() , _) }) , (\ { (_ , ()) })))))
    go sh@sh-pair q iw = no (\ r -> notShape sh sh-U (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (_ , ()) }) , ((\ { (() , _) }) , (\ { (_ , ()) })))))
    go sh@sh-pi q iw = no (\ r -> notShape sh sh-U (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
    go sh@sh-sig q iw = no (\ r -> notShape sh sh-U (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
    go sh@sh-nat q iw = no (\ r -> notShape sh sh-U (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
    go sh@sh-ze q iw = no (\ r -> notShape sh sh-U (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
    go sh@sh-sc q iw = no (\ r -> notShape sh sh-U (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
    go sh@sh-V q iw = no (\ r -> notShape sh sh-U (tyeq-trans (tyeq-sym q) (snd (snd r))) ((\ ()) , ((\ { (() , _) }) , ((\ { (() , _) }) , (\ { (() , _) })))))
    go (sh-U {f} {g}) q iw = yes (f , (g , q))

------------------------------------------------------------------------
-- injectivity of the codes U(f,g)
------------------------------------------------------------------------

private
  ucInv : {n : Num} {f g f' g' : Expr n} -> AlgEq (Ucode f g) (Ucode f' g') -> AlgEq f f' * AlgEq g g'
  ucInv (alg hrs-refl hrs-refl (w-ucode Rf Rg)) = Rf , Rg
  ucInv (alg hrs-refl hrs-refl (w-ne ()))

  ucTy : {n : Num} {G : Ctx n} {f g : Expr n} -> IsType G (Ucode f g) -> HasType G (Ucode f g) V
  ucTy (isty-el h) = h

U-inj : {n : Num} {G : Ctx n} {f g f' g' : Expr n} -> TyEq G (Ucode f g) (Ucode f' g') ->
  ConvTm G f f' OpF * ConvTm G g g' (OpG f)
U-inj q = cf , algsound hg (ty-conv hg' (tyeq-sym (opGEq (wfTm hf) hf hf' cf))) (snd R)
  where
    iU = fst (pTE q) ; iU' = snd (pTE q)
    R = ucInv (complete-ty iU iU' (tyS q))
    hf = fst (invUcode (ucTy iU)) ; hg = fst (snd (invUcode (ucTy iU)))
    hf' = fst (invUcode (ucTy iU')) ; hg' = fst (snd (invUcode (ucTy iU')))
    cf = algsound hf hf' (fst R)
