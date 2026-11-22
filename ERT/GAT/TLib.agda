{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.GAT.TLib
--
-- Typed substitutions of ERT's T_T, the operations needed to erase GAT
-- derivations (Theorem 16):
--   cmpS, idSub/p/eps/comp/pt for WtSub,
--   refl/pt/sym/trans/comp/sec for ConvTmSub (TarskiMetaCong),
--   CxEq: general context conversion (LiftBack.ConvCtx requires equal
--   erasures, so it is not used here), cx-* along the identity.
------------------------------------------------------------------------

module ERT.GAT.TLib where

open import ERT.Basic
open import ERT.TarskiSyntax
open import ERT.TarskiTyping
open import ERT.TarskiMeta
open import ERT.TarskiMetaCong using (ConvTmSub ; consSub ; consSub-ConvTmSub ; liftSub-ConvTmSub ;
                                      subst-cong-IsType ; subst-cong-HasType)

cmpS : {h k g : Nat} -> Sub k g -> Sub h k -> Sub h g
cmpS s d i = substExpr d (s i)

wkS : {n : Nat} -> Sub (suc n) n
wkS i = Var (fsuc i)

PtEq : {h g : Nat} -> Sub h g -> Sub h g -> Set
PtEq s s' = (i : Fin _) -> Eq (s i) (s' i)

ren-as-subst : {n m : Nat} (r : Ren n m) (e : Expr n) -> Eq (renExpr r e) (substExpr (\ i -> Var (r i)) e)
ren-as-subst r e = Eq-trans (Eq-sym (substExpr-id (renExpr r e))) (subst-ren idSub r e)

------------------------------------------------------------------------
-- WtSub

idSub-WtSub : {n : Nat} {G : Ctx n} -> WfCtx G -> WtSub G G idSub
idSub-WtSub {G = G} wfG i =
  Eq-transport (\ T -> HasType G (Var i) T) (Eq-sym (substExpr-id (lookup G i))) (ty-var wfG)

comp-WtSub : {h k g : Nat} {T : Ctx h} {D : Ctx k} {G : Ctx g} {s : Sub k g} {d : Sub h k}
  -> WtSub T D d -> WfCtx T -> WtSub D G s -> WtSub T G (cmpS s d)
comp-WtSub {T = T} {G = G} {s = s} {d = d} wd wfT ws i =
  Eq-transport (\ X -> HasType T (substExpr d (s i)) X) (subst-subst d s (lookup G i))
    (subst-HasType wd wfT (ws i))

pt-WtSub : {h g : Nat} {H : Ctx h} {G : Ctx g} {s s' : Sub h g}
  -> PtEq s s' -> WtSub H G s -> WtSub H G s'
pt-WtSub {H = H} {G = G} {s} {s'} e ws i =
  Eq-transport (\ X -> HasType H X (substExpr s' (lookup G i))) (e i)
    (Eq-transport (\ X -> HasType H (s i) X) (substExpr-ext s s' e (lookup G i)) (ws i))

p-WtSub : {n : Nat} {G : Ctx n} {A : Expr n} -> IsType G A -> WtSub (extend G A) G wkS
p-WtSub {G = G} {A} dA i =
  Eq-transport (\ X -> HasType (extend G A) (Var (fsuc i)) X) (ren-as-subst wkRen (lookup G i))
    (ty-var (wf-extend dA))

eps0 : {n : Nat} -> Sub n zero
eps0 ()

eps-WtSub : {n : Nat} {H : Ctx n} (s : Sub n zero) -> WtSub H empty s
eps-WtSub s ()

------------------------------------------------------------------------
-- ConvTmSub

cts-refl : {h g : Nat} {H : Ctx h} {G : Ctx g} {s : Sub h g} -> WtSub H G s -> ConvTmSub H G s s
cts-refl ws i = conv-refl (ws i)

cts-pt : {h g : Nat} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} -> WtSub H G s -> PtEq s s' -> ConvTmSub H G s s'
cts-pt {H = H} {G = G} {s} ws e i =
  Eq-transport (\ X -> ConvTm H (s i) X (substExpr s (lookup G i))) (e i) (conv-refl (ws i))

cts-sym : {h g : Nat} {H : Ctx h} {G : Ctx g} {s s' : Sub h g}
  -> WfCtx H -> WfCtx G -> ConvTmSub H G s s' -> ConvTmSub H G s' s
cts-sym wfH wfG c i = conv-conv (conv-sym (c i)) (subst-cong-IsType c wfH (wfCtx-lookup wfG i))

cts-trans : {h g : Nat} {H : Ctx h} {G : Ctx g} {s s' s'' : Sub h g}
  -> WfCtx H -> WfCtx G -> ConvTmSub H G s s' -> ConvTmSub H G s' s'' -> ConvTmSub H G s s''
cts-trans wfH wfG c1 c2 i =
  conv-trans (c1 i) (conv-conv (c2 i) (conv-Ty-sym (subst-cong-IsType c1 wfH (wfCtx-lookup wfG i))))

cts-comp : {h k g : Nat} {T : Ctx h} {D : Ctx k} {G : Ctx g} {s s' : Sub k g} {d d' : Sub h k}
  -> WfCtx T -> WfCtx D -> WfCtx G -> WtSub T D d -> ConvTmSub T D d d'
  -> WtSub D G s' -> ConvTmSub D G s s' -> ConvTmSub T G (cmpS s d) (cmpS s' d')
cts-comp {T = T} {G = G} {s} {s'} {d} {d'} wfT wfD wfG wd cd ws' c i =
  Eq-transport (\ X -> ConvTm T (substExpr d (s i)) (substExpr d' (s' i)) X) (subst-subst d s (lookup G i))
    (conv-trans (subst-ConvTm wd wfT (c i))
       (conv-conv (subst-cong-HasType cd wfT (ws' i))
          (subst-ConvTy wd wfT (conv-Ty-sym (subst-cong-IsType c wfD (wfCtx-lookup wfG i))))))

cts-sec : {n : Nat} {G : Ctx n} {A a a' : Expr n} -> WfCtx G -> ConvTm G a a' A
  -> ConvTmSub G (extend G A) (subst1Sub a) (subst1Sub a')
cts-sec {G = G} {A} {a} {a'} wfG c fzero =
  Eq-transport (\ X -> ConvTm G a a' X) (Eq-sym (subst1-wk A a)) c
cts-sec {G = G} {A} {a} {a'} wfG c (fsuc i) =
  conv-refl (Eq-transport (\ X -> HasType G (Var i) X) (Eq-sym (subst1-wk (lookup G i) a)) (ty-var wfG))

------------------------------------------------------------------------
-- general context conversion

CxEq : {n : Nat} -> Ctx n -> Ctx n -> Set
CxEq empty empty = Top
CxEq (extend G A) (extend G' A') = Pair (CxEq G G') (ConvTy G A A')

cx-subst-id-Ty : {n : Nat} {G : Ctx n} {A B : Expr n} -> ConvTy G (substExpr idSub A) (substExpr idSub B) -> ConvTy G A B
cx-subst-id-Ty {G = G} {A} {B} c =
  Eq-transport (\ X -> ConvTy G A X) (substExpr-id B) (Eq-transport (\ X -> ConvTy G X (substExpr idSub B)) (substExpr-id A) c)

-- the identity is typed from G' to G
cx-WtSub : {n : Nat} (G G' : Ctx n) -> CxEq G G' -> WfCtx G' -> WtSub G' G idSub
cx-WtSub empty empty e wf ()
cx-WtSub (extend G A) (extend G' A') (mkSigma e cA) (wf-extend dA') fzero =
  ty-conv (ty-var (wf-extend dA'))
    (Eq-transport (\ X -> ConvTy (extend G' A') (wkExpr A') X) (Eq-sym (substExpr-id (wkExpr A)))
       (wk-ConvTy dA' (conv-Ty-sym (cx-subst-id-Ty (subst-ConvTy (cx-WtSub G G' e (isType-WfCtx dA')) (isType-WfCtx dA') cA)))))
cx-WtSub (extend G A) (extend G' A') (mkSigma e cA) (wf-extend dA') (fsuc i) =
  Eq-transport (\ X -> HasType (extend G' A') (Var (fsuc i)) X)
    (Eq-trans (Eq-cong wkExpr (substExpr-id (lookup G i))) (Eq-sym (substExpr-id (wkExpr (lookup G i)))))
    (wk-HasType dA' (cx-WtSub G G' e (isType-WfCtx dA') i))

cx-IsType : {n : Nat} {G G' : Ctx n} {A : Expr n} -> CxEq G G' -> WfCtx G' -> IsType G A -> IsType G' A
cx-IsType {G = G} {G'} {A} e wf d =
  Eq-transport (\ X -> IsType G' X) (substExpr-id A) (subst-IsType (cx-WtSub G G' e wf) wf d)

cx-HasType : {n : Nat} {G G' : Ctx n} {M A : Expr n} -> CxEq G G' -> WfCtx G' -> HasType G M A -> HasType G' M A
cx-HasType {G = G} {G'} {M} {A} e wf d =
  Eq-transport (\ X -> HasType G' M X) (substExpr-id A)
    (Eq-transport (\ X -> HasType G' X (substExpr idSub A)) (substExpr-id M) (subst-HasType (cx-WtSub G G' e wf) wf d))

cx-ConvTy : {n : Nat} {G G' : Ctx n} {A B : Expr n} -> CxEq G G' -> WfCtx G' -> ConvTy G A B -> ConvTy G' A B
cx-ConvTy {G = G} {G'} e wf d = cx-subst-id-Ty (subst-ConvTy (cx-WtSub G G' e wf) wf d)

cx-ConvTm : {n : Nat} {G G' : Ctx n} {M N A : Expr n} -> CxEq G G' -> WfCtx G' -> ConvTm G M N A -> ConvTm G' M N A
cx-ConvTm {G = G} {G'} {M} {N} {A} e wf d =
  Eq-transport (\ X -> ConvTm G' M N X) (substExpr-id A)
    (Eq-transport (\ X -> ConvTm G' M X (substExpr idSub A)) (substExpr-id N)
       (Eq-transport (\ X -> ConvTm G' X (substExpr idSub N) (substExpr idSub A)) (substExpr-id M)
          (subst-ConvTm (cx-WtSub G G' e wf) wf d)))

cx-refl : {n : Nat} (G : Ctx n) -> WfCtx G -> CxEq G G
cx-refl empty wf = tt
cx-refl (extend G A) (wf-extend dA) = mkSigma (cx-refl G (isType-WfCtx dA)) (conv-Ty-refl dA)

cx-sym : {n : Nat} (G G' : Ctx n) -> WfCtx G' -> CxEq G G' -> CxEq G' G
cx-sym empty empty wf e = tt
cx-sym (extend G A) (extend G' A') (wf-extend dA') (mkSigma e cA) =
  mkSigma (cx-sym G G' (isType-WfCtx dA') e) (conv-Ty-sym (cx-ConvTy e (isType-WfCtx dA') cA))

------------------------------------------------------------------------
-- record wrappers: WtSub and ConvTmSub unfold to Pi types in which the
-- codomain context only occurs under lookup, so Agda cannot infer it;
-- records are injective type formers.

record WtS {h g : Nat} (H : Ctx h) (G : Ctx g) (s : Sub h g) : Set where
  constructor wts
  field un : WtSub H G s
open WtS public

record CTS {h g : Nat} (H : Ctx h) (G : Ctx g) (s s' : Sub h g) : Set where
  constructor cts
  field unc : ConvTmSub H G s s'
open CTS public

module _ {h g : Nat} {H : Ctx h} {G : Ctx g} {s : Sub h g} where
  sTy : {A : Expr g} -> WtS H G s -> WfCtx H -> IsType G A -> IsType H (substExpr s A)
  sTy w = subst-IsType (un w)
  sTm : {M A : Expr g} -> WtS H G s -> WfCtx H -> HasType G M A -> HasType H (substExpr s M) (substExpr s A)
  sTm w = subst-HasType (un w)
  sCTy : {A B : Expr g} -> WtS H G s -> WfCtx H -> ConvTy G A B -> ConvTy H (substExpr s A) (substExpr s B)
  sCTy w = subst-ConvTy (un w)
  sCTm : {M N A : Expr g} -> WtS H G s -> WfCtx H -> ConvTm G M N A
    -> ConvTm H (substExpr s M) (substExpr s N) (substExpr s A)
  sCTm w = subst-ConvTm (un w)
  liftS : {A : Expr g} -> WtS H G s -> WfCtx H -> IsType G A -> WtS (extend H (substExpr s A)) (extend G A) (liftSub s)
  liftS w wf dA = wts (liftSub-WtSub (un w) wf dA)
  ptS : {s' : Sub h g} -> PtEq s s' -> WtS H G s -> WtS H G s'
  ptS e w = wts (pt-WtSub {G = G} e (un w))
  ctsR : WtS H G s -> CTS H G s s
  ctsR w = cts (cts-refl {G = G} (un w))
  ctsP : {s' : Sub h g} -> WtS H G s -> PtEq s s' -> CTS H G s s'
  ctsP w e = cts (cts-pt {G = G} (un w) e)
  congTy : {s' : Sub h g} {A : Expr g} -> CTS H G s s' -> WfCtx H -> IsType G A -> ConvTy H (substExpr s A) (substExpr s' A)
  congTy c = subst-cong-IsType (unc c)
  congTm : {s' : Sub h g} {M A : Expr g} -> CTS H G s s' -> WfCtx H -> HasType G M A
    -> ConvTm H (substExpr s M) (substExpr s' M) (substExpr s A)
  congTm c = subst-cong-HasType (unc c)
  ctsS : {s' : Sub h g} -> WfCtx H -> WfCtx G -> CTS H G s s' -> CTS H G s' s
  ctsS wfH wfG c = cts (cts-sym wfH wfG (unc c))
  ctsT : {s' s'' : Sub h g} -> WfCtx H -> WfCtx G -> CTS H G s s' -> CTS H G s' s'' -> CTS H G s s''
  ctsT wfH wfG c1 c2 = cts (cts-trans wfH wfG (unc c1) (unc c2))
  ctsL : {s' : Sub h g} {A : Expr g} -> CTS H G s s' -> WfCtx H -> IsType G A
    -> CTS (extend H (substExpr s A)) (extend G A) (liftSub s) (liftSub s')
  ctsL c wf dA = cts (liftSub-ConvTmSub (unc c) wf dA)

idS : {n : Nat} {G : Ctx n} -> WfCtx G -> WtS G G idSub
idS wf = wts (idSub-WtSub wf)

pS : {n : Nat} {G : Ctx n} {A : Expr n} -> IsType G A -> WtS (extend G A) G wkS
pS dA = wts (p-WtSub dA)

epsS : {n : Nat} {H : Ctx n} (s : Sub n zero) -> WtS H empty s
epsS s = wts (eps-WtSub s)

ctsE : {n : Nat} {H : Ctx n} (s t : Sub n zero) -> CTS H empty s t
ctsE s t = cts (\ ())

secS : {n : Nat} {G : Ctx n} {A a : Expr n} -> IsType G A -> HasType G a A -> WtS G (extend G A) (subst1Sub a)
secS dA da = wts (subst1-WtSub dA da)

ctsSec : {n : Nat} {G : Ctx n} {A a a' : Expr n} -> WfCtx G -> ConvTm G a a' A
  -> CTS G (extend G A) (subst1Sub a) (subst1Sub a')
ctsSec wf c = cts (cts-sec wf c)

compS : {h k g : Nat} {T : Ctx h} {D : Ctx k} {G : Ctx g} {s : Sub k g} {d : Sub h k}
  -> WtS T D d -> WfCtx T -> WtS D G s -> WtS T G (cmpS s d)
compS {G = G} wd wf ws = wts (comp-WtSub {G = G} (un wd) wf (un ws))

ctsC : {h k g : Nat} {T : Ctx h} {D : Ctx k} {G : Ctx g} {s s' : Sub k g} {d d' : Sub h k}
  -> WfCtx T -> WfCtx D -> WfCtx G -> WtS T D d -> CTS T D d d'
  -> WtS D G s' -> CTS D G s s' -> CTS T G (cmpS s d) (cmpS s' d')
ctsC wfT wfD wfG wd cd ws' c = cts (cts-comp wfT wfD wfG (un wd) (unc cd) (un ws') (unc c))

cxS : {n : Nat} (G G' : Ctx n) -> CxEq G G' -> WfCtx G' -> WtS G' G idSub
cxS G G' e wf = wts (cx-WtSub G G' e wf)
