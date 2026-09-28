{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.TarskiMeta
--
-- Metatheory of the Tarski system T_T, as BCDE4.RussellMeta is for
-- T_R: renaming, weakening, substitution, context conversion and
-- presupposition (both sides of ConvTy/ConvTm, and the type of a
-- typed term).  Structural recursion throughout.
--
-- The right-hand sides of the decoding and lift equations are typed
-- with the level lemmas of BCDE4.Levels (the order respects level
-- equality and is transitive); the codomain of a Π-code is moved along
-- El_m (↑^m_l a) = El_l a, resp. El_l a = El_l' a, by context conversion.
------------------------------------------------------------------------

module BCDE4.TarskiMeta where

open import BCDE4.Basic
open import BCDE4.TarskiSyntax
open import BCDE4.TarskiTyping
open import BCDE4.Levels
open import BCDE4.TarskiRelevel
open import BCDE4.TarskiLsub

------------------------------------------------------------------------
-- Auxiliary syntactic lemmas
------------------------------------------------------------------------

idSub : {n : Nat} -> Sub n n
idSub i = Var i

substExpr-id : {n : Nat} (e : Expr n) -> Eq (substExpr idSub e) e
substExpr-id (Var i)        = refl
substExpr-id (Pi A B)       =
  Eq-cong2 Pi (substExpr-id A)
    (Eq-trans (substExpr-ext (liftSub idSub) idSub
                 (\ { fzero -> refl ; (fsuc i) -> refl }) B)
              (substExpr-id B))
substExpr-id (U l)      = refl
substExpr-id (Grd c A)  = Eq-cong (Grd c) (substExpr-id A)
substExpr-id (GLam c A t) = Eq-cong2 (GLam c) (substExpr-id A) (substExpr-id t)
substExpr-id Emp        = refl
substExpr-id (LPi A)    = Eq-cong LPi (Eq-trans (substExpr-ext _ idSub (\ i -> refl) A) (substExpr-id A))
substExpr-id (LLam A u) = Eq-cong2 LLam (Eq-trans (substExpr-ext _ idSub (\ i -> refl) A) (substExpr-id A))
                             (Eq-trans (substExpr-ext _ idSub (\ i -> refl) u) (substExpr-id u))
substExpr-id (LApp A t l) = Eq-cong2 (\ X Y -> LApp X Y l) (Eq-trans (substExpr-ext _ idSub (\ i -> refl) A) (substExpr-id A)) (substExpr-id t)
substExpr-id (Lam A B b)    =
  Eq-cong3 Lam (substExpr-id A)
    (Eq-trans (substExpr-ext (liftSub idSub) idSub
                 (\ { fzero -> refl ; (fsuc i) -> refl }) B)
              (substExpr-id B))
    (Eq-trans (substExpr-ext (liftSub idSub) idSub
                 (\ { fzero -> refl ; (fsuc i) -> refl }) b)
              (substExpr-id b))
substExpr-id (App A B c a)  =
  Eq-cong4 App (substExpr-id A)
    (Eq-trans (substExpr-ext (liftSub idSub) idSub
                 (\ { fzero -> refl ; (fsuc i) -> refl }) B)
              (substExpr-id B))
    (substExpr-id c) (substExpr-id a)
substExpr-id (El l a)       = Eq-cong (El l) (substExpr-id a)
substExpr-id (PiCode l a b) =
  Eq-cong2 (PiCode l) (substExpr-id a)
    (Eq-trans (substExpr-ext (liftSub idSub) idSub
                 (\ { fzero -> refl ; (fsuc i) -> refl }) b)
              (substExpr-id b))
substExpr-id (UCode m l)    = refl
substExpr-id (Lift m l a)   = Eq-cong (Lift m l) (substExpr-id a)
substExpr-id (EmpCode l)    = refl

ren-subst1 : {n m : Nat} (r : Ren n m) (B : Expr (suc n)) (a : Expr n)
  -> Eq (renExpr r (subst1 B a))
        (subst1 (renExpr (liftRen r) B) (renExpr r a))
ren-subst1 r B a =
  Eq-trans (ren-subst r (subst1Sub a) B)
    (Eq-trans (substExpr-ext _ _ ext B)
      (Eq-sym (subst-ren (subst1Sub (renExpr r a)) (liftRen r) B)))
  where
    ext : (i : Fin _)
        -> Eq (renExpr r (subst1Sub a i))
              (subst1Sub (renExpr r a) (liftRen r i))
    ext fzero    = refl
    ext (fsuc i) = refl

subst-subst1 : {h g : Nat} (sigma : Sub h g) (B : Expr (suc g)) (a : Expr g)
  -> Eq (substExpr sigma (subst1 B a))
        (subst1 (substExpr (liftSub sigma) B) (substExpr sigma a))
subst-subst1 sigma B a =
  Eq-trans (subst-subst sigma (subst1Sub a) B)
    (Eq-trans (substExpr-ext _ _ ext B)
      (Eq-sym (subst-subst (subst1Sub (substExpr sigma a))
                            (liftSub sigma) B)))
  where
    ext : (i : Fin _)
        -> Eq (substExpr sigma (subst1Sub a i))
              (substExpr (subst1Sub (substExpr sigma a)) (liftSub sigma i))
    ext fzero    = refl
    ext (fsuc i) =
      Eq-sym (Eq-trans (subst-ren (subst1Sub (substExpr sigma a))
                                   wkRen (sigma i))
                       (substExpr-id (sigma i)))

subst1-wk : {n : Nat} (e : Expr n) (a : Expr n)
  -> Eq (substExpr (subst1Sub a) (wkExpr e)) e
subst1-wk e a =
  Eq-trans (subst-ren (subst1Sub a) wkRen e)
    (Eq-trans (substExpr-ext _ idSub (\ i -> refl) e) (substExpr-id e))

liftRen-liftRen-wk-comm : {n m : Nat} (r : Ren n m) (e : Expr (suc n))
  -> Eq (renExpr (liftRen (liftRen r)) (renExpr (liftRen wkRen) e))
        (renExpr (liftRen wkRen) (renExpr (liftRen r) e))
liftRen-liftRen-wk-comm r e =
  Eq-trans (ren-ren (liftRen (liftRen r)) (liftRen wkRen) e)
    (Eq-trans (renExpr-ext _ _ ext e)
      (Eq-sym (ren-ren (liftRen wkRen) (liftRen r) e)))
  where
    ext : (i : Fin _)
        -> Eq (liftRen (liftRen r) (liftRen wkRen i))
              (liftRen wkRen (liftRen r i))
    ext fzero    = refl
    ext (fsuc i) = refl

liftSub-liftSub-wk-comm : {h g : Nat} (sigma : Sub h g) (e : Expr (suc g))
  -> Eq (substExpr (liftSub (liftSub sigma)) (renExpr (liftRen wkRen) e))
        (renExpr (liftRen wkRen) (substExpr (liftSub sigma) e))
liftSub-liftSub-wk-comm sigma e =
  Eq-trans (subst-ren (liftSub (liftSub sigma)) (liftRen wkRen) e)
    (Eq-trans (substExpr-ext _ _ ext e)
      (Eq-sym (ren-subst (liftRen wkRen) (liftSub sigma) e)))
  where
    ext : (i : Fin _)
        -> Eq (liftSub (liftSub sigma) (liftRen wkRen i))
              (renExpr (liftRen wkRen) (liftSub sigma i))
    ext fzero    = refl
    ext (fsuc i) =
      Eq-sym (Eq-trans (ren-ren (liftRen wkRen) wkRen (sigma i))
                (Eq-sym (ren-ren wkRen wkRen (sigma i))))

subst1-liftWk-cancel : {n : Nat} (e : Expr (suc n))
  -> Eq (subst1 (renExpr (liftRen wkRen) e) (Var fzero)) e
subst1-liftWk-cancel e =
  Eq-trans (subst-ren (subst1Sub (Var fzero)) (liftRen wkRen) e)
    (Eq-trans (substExpr-ext _ idSub
                 (\ { fzero -> refl ; (fsuc i) -> refl }) e)
              (substExpr-id e))

------------------------------------------------------------------------
-- Type-preserving renamings
------------------------------------------------------------------------

RenTypes : {n m : Nat} -> Ctx n -> Ctx m -> Ren n m -> Set
RenTypes G H r = (i : Fin _) -> Eq (lookup H (r i)) (renExpr r (lookup G i))

wkRen-RenTypes : {n : Nat} {G : Ctx n} {C : Expr n}
  -> RenTypes G (extend G C) wkRen
wkRen-RenTypes i = refl

liftRen-RenTypes : {n m : Nat} {G : Ctx n} {H : Ctx m}
  {r : Ren n m} {A : Expr n}
  -> RenTypes G H r
  -> RenTypes (extend G A) (extend H (renExpr r A)) (liftRen r)
liftRen-RenTypes {r = r} {A = A} rt fzero = Eq-sym (ren-wk-comm r A)
liftRen-RenTypes {G = G} {r = r} rt (fsuc i) =
  Eq-trans (Eq-cong wkExpr (rt i)) (Eq-sym (ren-wk-comm r (lookup G i)))

------------------------------------------------------------------------
-- Well-typed substitutions
------------------------------------------------------------------------

WtSubTy : {h g : Nat} -> Ctx h -> Ctx g -> Sub h g -> Set
WtSubTy H G sigma =
  (i : Fin _) -> HasType H (sigma i) (substExpr sigma (lookup G i))

-- A well-typed substitution also requires the level constraints of the
-- target to entail those of the source.
record WtSub {h g : Nat} (H : Ctx h) (G : Ctx g) (sigma : Sub h g) : Set where
  constructor mkWt
  field
    wtE : CEnt H G
    wtT : WtSubTy H G sigma
open WtSub public

isType-Pi : {n : Nat} {G : Ctx n} {A : Expr n} {B : Expr (suc n)}
  -> IsType G A -> IsType (extend G A) B -> IsType G (Pi A B)
isType-Pi = is-Pi

-- l < l⁺
lt-next : {Th : LCtx} (l : LExpr) -> LtL Th l (lnext l)
lt-next l = v-idem

isType-U : {n : Nat} {G : Ctx n} {l : LExpr} -> WfCtx G -> IsType G (U l)
isType-U wf = is-U wf

isType-LPi : {n : Nat} {G : Ctx n} {A : Expr n}
  -> WfCtx G -> IsType (addL G) A -> IsType G (LPi A)
isType-LPi = is-LPi

isType-El : {n : Nat} {G : Ctx n} {a : Expr n} {l : LExpr}
  -> HasType G a (U l) -> IsType G (El l a)
isType-El = is-El

-- level weakening / instantiation of well-formedness
wkL-WfCtx : {n : Nat} {G : Ctx n} -> WfCtx G -> WfCtx (addL G)
wkL-WfCtx {G = G} = lsub-WfCtx (lsk-shift G) (lok-shift G)

unL-WfCtx : {n : Nat} {G : Ctx n} -> WfCtx (addL G) -> WfCtx G
unL-WfCtx {G = G} = lsub-WfCtx (lsk-inst G (lvar zero)) (lok-inst G (lvar zero))

-- commutation of term renaming/substitution with instantiation
ren-lsub1 : {n m : Nat} (r : Ren n m) (A : Expr n) (l : LExpr) ->
  Eq (renExpr r (lsub1 A l)) (lsub1 (renExpr r A) l)
ren-lsub1 r A l = Eq-sym (lsubE-ren (lsub1S l) r A)

ren-lshift : {n m : Nat} (r : Ren n m) (t : Expr n) -> Eq (renExpr r (lshiftE t)) (lshiftE (renExpr r t))
ren-lshift r t = Eq-sym (lsubE-ren lwkS r t)

subst-lshift : {h g : Nat} (sigma : Sub h g) (t : Expr g) ->
  Eq (substExpr (\ i -> lshiftE (sigma i)) (lshiftE t)) (lshiftE (substExpr sigma t))
subst-lshift sigma t = Eq-sym (lsubE-subst lwkS sigma t)

subst-lshift2 : {h g : Nat} (sigma : Sub h g) (A : Expr g) ->
  Eq (lsubE (liftL lwkS) (substExpr (\ i -> lshiftE (sigma i)) A))
     (substExpr (\ i -> lshiftE (lshiftE (sigma i))) (lsubE (liftL lwkS) A))
subst-lshift2 sigma A =
  Eq-trans (lsubE-subst (liftL lwkS) (\ i -> lshiftE (sigma i)) A)
    (substExpr-ext _ _ (\ i -> lsubE-liftL-shift lwkS (sigma i)) (lsubE (liftL lwkS) A))

subst-lsub1 : {h g : Nat} (sigma : Sub h g) (A : Expr g) (l : LExpr) ->
  Eq (substExpr sigma (lsub1 A l)) (lsub1 (substExpr (\ i -> lshiftE (sigma i)) A) l)
subst-lsub1 sigma A l =
  Eq-sym (Eq-trans (lsubE-subst (lsub1S l) (\ i -> lshiftE (sigma i)) A)
                   (substExpr-ext _ sigma pt (lsub1 A l)))
  where
    pt : (i : Fin _) -> Eq (lsubE (lsub1S l) (lshiftE (sigma i))) (sigma i)
    pt i = Eq-trans (lsubE-comp (lsub1S l) lwkS (sigma i))
             (Eq-trans (lsubE-ext _ _ (\ j -> refl) (sigma i)) (lsubE-id (sigma i)))

-- A lifted over the shift and instantiated at the fresh level is A
lsub1-lift-var : {n : Nat} (A : Expr n) -> Eq (lsub1 (lsubE (liftL lwkS) A) (lvar zero)) A
lsub1-lift-var A =
  Eq-trans (lsubE-comp (lsub1S (lvar zero)) (liftL lwkS) A)
    (Eq-trans (lsubE-ext _ lidS pt A) (lsubE-id A))
  where
    pt : (i : Nat) -> Eq (lcomp (lsub1S (lvar zero)) (liftL lwkS) i) (lidS i)
    pt zero    = refl
    pt (suc i) = refl

rt-addL : {n m : Nat} {G : Ctx n} {H : Ctx m} {r : Ren n m}
  -> RenTypes G H r -> RenTypes (addL G) (addL H) r
rt-addL {G = G} {H = H} {r = r} rt i =
  Eq-trans (lookup-addL H (r i))
    (Eq-trans (Eq-cong lshiftE (rt i))
      (Eq-trans (Eq-sym (ren-lshift r (lookup G i))) (Eq-cong (renExpr r) (Eq-sym (lookup-addL G i)))))

isType-Grd : {n : Nat} {G : Ctx n} {c : Constr} {A : Expr n}
  -> WfCtx G -> IsType (addC G c) A -> IsType G (Grd c A)
isType-Grd = is-Grd

isType-Emp : {n : Nat} {G : Ctx n} -> WfCtx G -> IsType G Emp
isType-Emp wf = is-Emp wf

-- renamings and substitutions pass under a constraint
rt-addC : {n m : Nat} {G : Ctx n} {H : Ctx m} {r : Ren n m} (c : Constr)
  -> RenTypes G H r -> RenTypes (addC G c) (addC H c) r
rt-addC {G = G} {H = H} {r = r} c rt i =
  Eq-trans (lookup-addC H c (r i))
    (Eq-trans (rt i) (Eq-cong (renExpr r) (Eq-sym (lookup-addC G c i))))

WtSub-addL : {h g : Nat} {H : Ctx h} {G : Ctx g} {sigma : Sub h g}
  -> WtSub H G sigma -> WtSub (addL H) (addL G) (\ i -> lshiftE (sigma i))
WtSub-addL {H = H} {G = G} {sigma = sigma} ws =
  mkWt (ent-addL G H (wtE ws))
       (\ i -> Eq-transport (\ T -> HasType (addL H) (lshiftE (sigma i)) T)
                  (Eq-trans (Eq-sym (subst-lshift sigma (lookup G i)))
                            (Eq-cong (substExpr (\ j -> lshiftE (sigma j))) (Eq-sym (lookup-addL G i))))
                  (lsub-HasType (lsk-shift H) (lok-shift H) (wtT ws i)))

WtSub-addC : {h g : Nat} {H : Ctx h} {G : Ctx g} {sigma : Sub h g} (c : Constr)
  -> WtSub H G sigma -> WtSub (addC H c) (addC G c) sigma
WtSub-addC {H = H} {G = G} {sigma = sigma} c ws =
  mkWt (ent-addC G H c (wtE ws))
       (\ i -> Eq-transport (\ T -> HasType (addC H c) (sigma i) (substExpr sigma T))
                  (Eq-sym (lookup-addC G c i)) (wkC-HasType c (wtT ws i)))

mutual

  typing-WfCtx : {n : Nat} {G : Ctx n} {M A : Expr n}
    -> HasType G M A -> WfCtx G
  typing-WfCtx (ty-GLam dG _ _)    = dG
  typing-WfCtx (ty-LLam dG _ _)    = dG
  typing-WfCtx (ty-LApp _ dt)      = typing-WfCtx dt
  typing-WfCtx (ty-collapse _ dA)  = isType-WfCtx dA
  typing-WfCtx (ty-var dG)         = dG
  typing-WfCtx (ty-conv dM _)      = typing-WfCtx dM
  typing-WfCtx (ty-PiCode da _)    = typing-WfCtx da
  typing-WfCtx (ty-UCode dG _)     = dG
  typing-WfCtx (ty-Lift _ da)      = typing-WfCtx da
  typing-WfCtx (ty-EmpCode dG)     = dG
  typing-WfCtx (ty-Lam dA _ _)     = isType-WfCtx dA
  typing-WfCtx (ty-App dA _ _ _)   = isType-WfCtx dA

  isType-WfCtx : {n : Nat} {G : Ctx n} {A : Expr n}
    -> IsType G A -> WfCtx G
  isType-WfCtx (is-U dG)        = dG
  isType-WfCtx (is-El d)        = typing-WfCtx d
  isType-WfCtx (is-Emp dG)      = dG
  isType-WfCtx (is-Pi dA _)     = isType-WfCtx dA
  isType-WfCtx (is-Grd dG _)    = dG
  isType-WfCtx (is-LPi dG _)    = dG

  presup-l-ConvTy : {n : Nat} {G : Ctx n} {A B : Expr n}
    -> ConvTy G A B -> IsType G A
  presup-l-ConvTy (conv-Ty-Grd dG dA _)    = isType-Grd dG dA
  presup-l-ConvTy (conv-Ty-collapse _ dA)  = dA
  presup-l-ConvTy (conv-Ty-LPi dG dA _)    = isType-LPi dG dA
  presup-l-ConvTy (conv-Ty-refl dA)        = dA
  presup-l-ConvTy (conv-Ty-sym d)          = presup-r-ConvTy d
  presup-l-ConvTy (conv-Ty-trans d1 _)     = presup-l-ConvTy d1
  presup-l-ConvTy (conv-Ty-Pi dA0 dB0 _ _) = isType-Pi dA0 dB0
  presup-l-ConvTy (conv-Ty-El d)           = is-El (presup-l-ConvTm d)
  presup-l-ConvTy (conv-Ty-U-lvl dG _)     = is-U dG
  presup-l-ConvTy (conv-Ty-El-lvl _ da)    = is-El da
  presup-l-ConvTy (conv-Ty-El-UCode dG lt) = is-El (ty-UCode dG lt)
  presup-l-ConvTy (conv-Ty-El-PiCode da db) = is-El (ty-PiCode da db)
  presup-l-ConvTy (conv-Ty-El-Lift le da)  = is-El (ty-Lift le da)
  presup-l-ConvTy (conv-Ty-El-EmpCode dG)  = is-El (ty-EmpCode dG)
  presup-l-ConvTy (conv-Ty-Grd-beta {c = c} v dA) = is-Grd (isType-WfCtx dA) (wkC-IsType c dA)
  presup-l-ConvTy (conv-Ty-Grd-equiv dG q dA)     = is-Grd dG dA

  presup-r-ConvTy : {n : Nat} {G : Ctx n} {A B : Expr n}
    -> ConvTy G A B -> IsType G B
  presup-r-ConvTy (conv-Ty-Grd dG _ dAB)  = isType-Grd dG (presup-r-ConvTy dAB)
  presup-r-ConvTy (conv-Ty-collapse _ dA)  = isType-Emp (isType-WfCtx dA)
  presup-r-ConvTy (conv-Ty-LPi dG _ dAB)   = isType-LPi dG (presup-r-ConvTy dAB)
  presup-r-ConvTy (conv-Ty-refl dA)        = dA
  presup-r-ConvTy (conv-Ty-sym d)          = presup-l-ConvTy d
  presup-r-ConvTy (conv-Ty-trans _ d2)     = presup-r-ConvTy d2
  presup-r-ConvTy (conv-Ty-Pi dA-IT _ dA dB) =
    let dA'-IT = presup-r-ConvTy dA
    in isType-Pi dA'-IT (ctx-conv-IsType dA-IT dA'-IT dA (presup-r-ConvTy dB))
  presup-r-ConvTy (conv-Ty-El d)           = is-El (presup-r-ConvTm d)
  presup-r-ConvTy (conv-Ty-U-lvl dG _)     = is-U dG
  presup-r-ConvTy (conv-Ty-El-lvl v da)    = is-El (ty-conv da (conv-Ty-U-lvl (typing-WfCtx da) v))
  presup-r-ConvTy (conv-Ty-El-UCode dG _)  = is-U dG
  presup-r-ConvTy (conv-Ty-El-PiCode da db) = is-Pi (is-El da) (is-El db)
  presup-r-ConvTy (conv-Ty-El-Lift _ da)   = is-El da
  presup-r-ConvTy (conv-Ty-El-EmpCode dG)  = is-Emp dG
  presup-r-ConvTy (conv-Ty-Grd-beta v dA)  = dA
  presup-r-ConvTy (conv-Ty-Grd-equiv dG q dA) = is-Grd dG (swapC-IsType q dA)


  ----------------------------------------------------------------------
  -- typing-WfCtx, isType-WfCtx, wfCtx-lookup
  ----------------------------------------------------------------------
  wfCtx-lookup : {n : Nat} {G : Ctx n}
    -> WfCtx G -> (i : Fin n) -> IsType G (lookup G i)
  wfCtx-lookup (wf-extend dA) fzero    = wk-IsType dA dA
  wfCtx-lookup (wf-extend dA) (fsuc i) =
    wk-IsType dA (wfCtx-lookup (isType-WfCtx dA) i)

  ----------------------------------------------------------------------
  -- Renaming preserves IsType
  ----------------------------------------------------------------------
  ren-IsType : {n m : Nat} {G : Ctx n} {H : Ctx m}
    {r : Ren n m} {A : Expr n}
    -> RenTypes G H r -> CEnt H G -> WfCtx H
    -> IsType G A -> IsType H (renExpr r A)
  ren-IsType rt e wfH (is-U _)  = is-U wfH
  ren-IsType rt e wfH (is-El d) = is-El (ren-HasType rt e wfH d)
  ren-IsType rt e wfH (is-Emp _) = is-Emp wfH
  ren-IsType rt e wfH (is-Pi dA dB) =
    let dA' = ren-IsType rt e wfH dA
    in is-Pi dA' (ren-IsType (liftRen-RenTypes rt) e (wf-extend dA') dB)
  ren-IsType {G = G} {H = H} rt e wfH (is-Grd {c = c} dG dA) =
    is-Grd wfH (ren-IsType (rt-addC {G = G} {H = H} c rt) (ent-addC G H c e) (wkC-WfCtx c wfH) dA)
  ren-IsType {G = G} {H = H} rt e wfH (is-LPi dG dA) =
    is-LPi wfH (ren-IsType (rt-addL {G = G} {H = H} rt) (ent-addL G H e) (wkL-WfCtx wfH) dA)
  ----------------------------------------------------------------------
  -- Renaming preserves HasType
  ----------------------------------------------------------------------
  ren-HasType : {n m : Nat} {G : Ctx n} {H : Ctx m}
    {r : Ren n m} {M A : Expr n}
    -> RenTypes G H r -> CEnt H G -> WfCtx H
    -> HasType G M A -> HasType H (renExpr r M) (renExpr r A)
  ren-HasType {G = G} {H = H} rt e wfH (ty-GLam {c = c} dG dA dt) =
    ty-GLam wfH (ren-IsType (rt-addC {G = G} {H = H} c rt) (ent-addC G H c e) (wkC-WfCtx c wfH) dA)
                (ren-HasType (rt-addC {G = G} {H = H} c rt) (ent-addC G H c e) (wkC-WfCtx c wfH) dt)
  ren-HasType {G = G} {H = H} rt e wfH (ty-LLam dG dA du) =
    ty-LLam wfH (ren-IsType (rt-addL {G = G} {H = H} rt) (ent-addL G H e) (wkL-WfCtx wfH) dA)
                (ren-HasType (rt-addL {G = G} {H = H} rt) (ent-addL G H e) (wkL-WfCtx wfH) du)
  ren-HasType {G = G} {H = H} {r = r} rt e wfH (ty-LApp {A = A} {t = t} {l = l} dA dt) =
    Eq-transport (\ T -> HasType H (LApp (renExpr r A) (renExpr r t) l) T) (Eq-sym (ren-lsub1 r A l))
      (ty-LApp (ren-IsType (rt-addL {G = G} {H = H} rt) (ent-addL G H e) (wkL-WfCtx wfH) dA) (ren-HasType rt e wfH dt))
  ren-HasType rt e wfH (ty-collapse lp dA) =
    ty-collapse (loop-ent e lp) (ren-IsType rt e wfH dA)
  ren-HasType rt e wfH (ty-PiCode da db) =
    let da'  = ren-HasType rt e wfH da
        wfH' = wf-extend (is-El da')
        rt'  = liftRen-RenTypes rt
    in ty-PiCode da' (ren-HasType rt' e wfH' db)
  ren-HasType rt e wfH (ty-UCode _ v)  = ty-UCode wfH (valid-ent e v)
  ren-HasType rt e wfH (ty-Lift v da)  = ty-Lift (valid-ent e v) (ren-HasType rt e wfH da)
  ren-HasType rt e wfH (ty-EmpCode _)  = ty-EmpCode wfH
  ren-HasType {r = r} rt e wfH (ty-var {i = i} _) =
    Eq-transport (\ T -> HasType _ (Var (r i)) T) (rt i) (ty-var wfH)
  ren-HasType rt e wfH (ty-conv dM dAB) =
    ty-conv (ren-HasType rt e wfH dM) (ren-ConvTy rt e wfH dAB)
  ren-HasType rt e wfH (ty-Lam dA dB db) =
    let dA'  = ren-IsType rt e wfH dA
        wfH' = wf-extend dA'
        rt'  = liftRen-RenTypes rt
    in ty-Lam dA' (ren-IsType rt' e wfH' dB) (ren-HasType rt' e wfH' db)
  ren-HasType {r = r} rt e wfH
              (ty-App {A = A} {B = B} {c = c} {a = a} dA dB dc da) =
    let dA'  = ren-IsType rt e wfH dA
        wfH' = wf-extend dA'
        rt'  = liftRen-RenTypes rt
    in Eq-transport
         (\ T -> HasType _
                   (App (renExpr r A) (renExpr (liftRen r) B)
                        (renExpr r c) (renExpr r a)) T)
         (Eq-sym (ren-subst1 r B a))
         (ty-App dA' (ren-IsType rt' e wfH' dB)
                     (ren-HasType rt e wfH dc) (ren-HasType rt e wfH da))
  ----------------------------------------------------------------------
  -- Renaming preserves ConvTy
  ----------------------------------------------------------------------
  ren-ConvTy : {n m : Nat} {G : Ctx n} {H : Ctx m}
    {r : Ren n m} {A B : Expr n}
    -> RenTypes G H r -> CEnt H G -> WfCtx H
    -> ConvTy G A B -> ConvTy H (renExpr r A) (renExpr r B)
  ren-ConvTy rt e wfH (conv-Ty-El d) = conv-Ty-El (ren-ConvTm rt e wfH d)
  ren-ConvTy rt e wfH (conv-Ty-U-lvl _ v) = conv-Ty-U-lvl wfH (valid-ent e v)
  ren-ConvTy rt e wfH (conv-Ty-El-lvl v da) = conv-Ty-El-lvl (valid-ent e v) (ren-HasType rt e wfH da)
  ren-ConvTy rt e wfH (conv-Ty-El-UCode _ v) = conv-Ty-El-UCode wfH (valid-ent e v)
  ren-ConvTy rt e wfH (conv-Ty-El-PiCode da db) =
    let da'  = ren-HasType rt e wfH da
    in conv-Ty-El-PiCode da' (ren-HasType (liftRen-RenTypes rt) e (wf-extend (is-El da')) db)
  ren-ConvTy rt e wfH (conv-Ty-El-Lift v da) = conv-Ty-El-Lift (valid-ent e v) (ren-HasType rt e wfH da)
  ren-ConvTy rt e wfH (conv-Ty-El-EmpCode _) = conv-Ty-El-EmpCode wfH
  ren-ConvTy rt e wfH (conv-Ty-Grd-beta {c = c} v dA) = conv-Ty-Grd-beta (validC-ent c e v) (ren-IsType rt e wfH dA)
  ren-ConvTy {G = G} {H = H} rt e wfH (conv-Ty-Grd-equiv {c = c} dG q dA) =
    conv-Ty-Grd-equiv wfH (equivC-ent e q)
      (ren-IsType (rt-addC {G = G} {H = H} c rt) (ent-addC G H c e) (wkC-WfCtx c wfH) dA)
  ren-ConvTy {G = G} {H = H} rt e wfH (conv-Ty-Grd {c = c} dG dA dAB) =
    conv-Ty-Grd wfH (ren-IsType (rt-addC {G = G} {H = H} c rt) (ent-addC G H c e) (wkC-WfCtx c wfH) dA)
                    (ren-ConvTy (rt-addC {G = G} {H = H} c rt) (ent-addC G H c e) (wkC-WfCtx c wfH) dAB)
  ren-ConvTy {G = G} {H = H} rt e wfH (conv-Ty-LPi dG dA dAB) =
    conv-Ty-LPi wfH (ren-IsType (rt-addL {G = G} {H = H} rt) (ent-addL G H e) (wkL-WfCtx wfH) dA)
                    (ren-ConvTy (rt-addL {G = G} {H = H} rt) (ent-addL G H e) (wkL-WfCtx wfH) dAB)
  ren-ConvTy rt e wfH (conv-Ty-collapse lp dA) =
    conv-Ty-collapse (loop-ent e lp) (ren-IsType rt e wfH dA)
  ren-ConvTy rt e wfH (conv-Ty-refl dA) =
    conv-Ty-refl (ren-IsType rt e wfH dA)
  ren-ConvTy rt e wfH (conv-Ty-sym d) =
    conv-Ty-sym (ren-ConvTy rt e wfH d)
  ren-ConvTy rt e wfH (conv-Ty-trans d1 d2) =
    conv-Ty-trans (ren-ConvTy rt e wfH d1) (ren-ConvTy rt e wfH d2)
  ren-ConvTy rt e wfH (conv-Ty-Pi dA0 dB0 dA dB) =
    let dA-IT = ren-IsType rt e wfH dA0
        wfH'  = wf-extend dA-IT
        rt'   = liftRen-RenTypes rt
    in conv-Ty-Pi dA-IT (ren-IsType rt' e wfH' dB0) (ren-ConvTy rt e wfH dA) (ren-ConvTy rt' e wfH' dB)
  ----------------------------------------------------------------------
  -- Renaming preserves ConvTm
  ----------------------------------------------------------------------
  ren-ConvTm : {n m : Nat} {G : Ctx n} {H : Ctx m}
    {r : Ren n m} {M N A : Expr n}
    -> RenTypes G H r -> CEnt H G -> WfCtx H
    -> ConvTm G M N A
    -> ConvTm H (renExpr r M) (renExpr r N) (renExpr r A)
  ren-ConvTm rt e wfH (conv-refl dM) = conv-refl (ren-HasType rt e wfH dM)
  ren-ConvTm rt e wfH (conv-cong-PiCode da db daa dbb) =
    let da'  = ren-HasType rt e wfH da
        wfH' = wf-extend (is-El da')
        rt'  = liftRen-RenTypes rt
    in conv-cong-PiCode da' (ren-HasType rt' e wfH' db) (ren-ConvTm rt e wfH daa) (ren-ConvTm rt' e wfH' dbb)
  ren-ConvTm rt e wfH (conv-cong-Lift v daa) = conv-cong-Lift (valid-ent e v) (ren-ConvTm rt e wfH daa)
  ren-ConvTm rt e wfH (conv-Lift-refl v da) = conv-Lift-refl (valid-ent e v) (ren-HasType rt e wfH da)
  ren-ConvTm rt e wfH (conv-Lift-Lift v w da) =
    conv-Lift-Lift (valid-ent e v) (valid-ent e w) (ren-HasType rt e wfH da)
  ren-ConvTm rt e wfH (conv-Lift-UCode _ v w) = conv-Lift-UCode wfH (valid-ent e v) (valid-ent e w)
  ren-ConvTm rt e wfH (conv-Lift-PiCode v da db) =
    let da'  = ren-HasType rt e wfH da
    in conv-Lift-PiCode (valid-ent e v) da' (ren-HasType (liftRen-RenTypes rt) e (wf-extend (is-El da')) db)
  ren-ConvTm rt e wfH (conv-Lift-EmpCode _ v) = conv-Lift-EmpCode wfH (valid-ent e v)
  ren-ConvTm rt e wfH (conv-UCode-lvl _ v w u) =
    conv-UCode-lvl wfH (valid-ent e v) (valid-ent e w) (valid-ent e u)
  ren-ConvTm rt e wfH (conv-Lift-lvl v w u da) =
    conv-Lift-lvl (valid-ent e v) (valid-ent e w) (valid-ent e u) (ren-HasType rt e wfH da)
  ren-ConvTm rt e wfH (conv-PiCode-lvl v da db) =
    let da'  = ren-HasType rt e wfH da
    in conv-PiCode-lvl (valid-ent e v) da' (ren-HasType (liftRen-RenTypes rt) e (wf-extend (is-El da')) db)
  ren-ConvTm rt e wfH (conv-EmpCode-lvl _ v) = conv-EmpCode-lvl wfH (valid-ent e v)
  ren-ConvTm {G = G} {H = H} rt e wfH (conv-cong-GLam {c = c} dG dA dt dtt) =
    conv-cong-GLam wfH (ren-IsType (rt-addC {G = G} {H = H} c rt) (ent-addC G H c e) (wkC-WfCtx c wfH) dA)
                       (ren-HasType (rt-addC {G = G} {H = H} c rt) (ent-addC G H c e) (wkC-WfCtx c wfH) dt)
                       (ren-ConvTm (rt-addC {G = G} {H = H} c rt) (ent-addC G H c e) (wkC-WfCtx c wfH) dtt)
  ren-ConvTm {G = G} {H = H} rt e wfH (conv-GLam-eta {c = c} dG dA dt dt') =
    conv-GLam-eta wfH (ren-IsType (rt-addC {G = G} {H = H} c rt) (ent-addC G H c e) (wkC-WfCtx c wfH) dA)
                      (ren-HasType rt e wfH dt)
                      (ren-HasType (rt-addC {G = G} {H = H} c rt) (ent-addC G H c e) (wkC-WfCtx c wfH) dt')
  ren-ConvTm rt e wfH (conv-GLam-beta {c = c} v dA dt) =
    conv-GLam-beta (validC-ent c e v) (ren-IsType rt e wfH dA) (ren-HasType rt e wfH dt)
  ren-ConvTm {G = G} {H = H} rt e wfH (conv-cong-LLam dG dA du duu) =
    conv-cong-LLam wfH (ren-IsType (rt-addL {G = G} {H = H} rt) (ent-addL G H e) (wkL-WfCtx wfH) dA)
                       (ren-HasType (rt-addL {G = G} {H = H} rt) (ent-addL G H e) (wkL-WfCtx wfH) du)
                       (ren-ConvTm (rt-addL {G = G} {H = H} rt) (ent-addL G H e) (wkL-WfCtx wfH) duu)
  ren-ConvTm {G = G} {H = H} rt e wfH (conv-cong-GLam-Ty {c = c} dG dA dAA dt) =
    conv-cong-GLam-Ty wfH (ren-IsType (rt-addC {G = G} {H = H} c rt) (ent-addC G H c e) (wkC-WfCtx c wfH) dA)
      (ren-ConvTy (rt-addC {G = G} {H = H} c rt) (ent-addC G H c e) (wkC-WfCtx c wfH) dAA)
      (ren-HasType (rt-addC {G = G} {H = H} c rt) (ent-addC G H c e) (wkC-WfCtx c wfH) dt)
  ren-ConvTm {G = G} {H = H} rt e wfH (conv-cong-LLam-Ty dG dA dAA du) =
    conv-cong-LLam-Ty wfH (ren-IsType (rt-addL {G = G} {H = H} rt) (ent-addL G H e) (wkL-WfCtx wfH) dA)
      (ren-ConvTy (rt-addL {G = G} {H = H} rt) (ent-addL G H e) (wkL-WfCtx wfH) dAA)
      (ren-HasType (rt-addL {G = G} {H = H} rt) (ent-addL G H e) (wkL-WfCtx wfH) du)
  ren-ConvTm {G = G} {H = H} {r = r} rt e wfH (conv-cong-LApp-Ty {A = A} {A' = A'} {t = t} {l = l} dA dAA dt) =
    Eq-transport (\ T -> ConvTm H (LApp (renExpr r A) (renExpr r t) l) (LApp (renExpr r A') (renExpr r t) l) T) (Eq-sym (ren-lsub1 r A l))
      (conv-cong-LApp-Ty (ren-IsType (rt-addL {G = G} {H = H} rt) (ent-addL G H e) (wkL-WfCtx wfH) dA)
        (ren-ConvTy (rt-addL {G = G} {H = H} rt) (ent-addL G H e) (wkL-WfCtx wfH) dAA) (ren-HasType rt e wfH dt))
  ren-ConvTm {G = G} {H = H} {r = r} rt e wfH (conv-cong-LApp-fun {A = A} {t = t} {t' = t'} {l = l} dA dtt) =
    Eq-transport (\ T -> ConvTm H (LApp (renExpr r A) (renExpr r t) l) (LApp (renExpr r A) (renExpr r t') l) T) (Eq-sym (ren-lsub1 r A l))
      (conv-cong-LApp-fun (ren-IsType (rt-addL {G = G} {H = H} rt) (ent-addL G H e) (wkL-WfCtx wfH) dA) (ren-ConvTm rt e wfH dtt))
  ren-ConvTm {G = G} {H = H} {r = r} rt e wfH (conv-cong-LApp-lvl {A = A} {t = t} {l = l} {l' = l'} dA dt v dAA) =
    Eq-transport (\ T -> ConvTm H (LApp (renExpr r A) (renExpr r t) l) (LApp (renExpr r A) (renExpr r t) l') T) (Eq-sym (ren-lsub1 r A l))
      (conv-cong-LApp-lvl (ren-IsType (rt-addL {G = G} {H = H} rt) (ent-addL G H e) (wkL-WfCtx wfH) dA)
        (ren-HasType rt e wfH dt) (valid-ent e v)
        (Eq-transport (\ X -> ConvTy H X (lsub1 (renExpr r A) l')) (ren-lsub1 r A l)
          (Eq-transport (ConvTy H (renExpr r (lsub1 A l))) (ren-lsub1 r A l') (ren-ConvTy rt e wfH dAA))))
  ren-ConvTm {G = G} {H = H} rt e wfH (conv-GLam-equiv {c = c} dG q dA dt) =
    conv-GLam-equiv wfH (equivC-ent e q)
      (ren-IsType (rt-addC {G = G} {H = H} c rt) (ent-addC G H c e) (wkC-WfCtx c wfH) dA)
      (ren-HasType (rt-addC {G = G} {H = H} c rt) (ent-addC G H c e) (wkC-WfCtx c wfH) dt)
  ren-ConvTm {G = G} {H = H} {r = r} rt e wfH (conv-LApp-beta {A = A} {u = u} {l = l} dA du) =
    Eq-transport (\ T -> ConvTm H (LApp (renExpr r A) (LLam (renExpr r A) (renExpr r u)) l) (renExpr r (lsub1 u l)) T) (Eq-sym (ren-lsub1 r A l))
      (Eq-transport (\ X -> ConvTm H (LApp (renExpr r A) (LLam (renExpr r A) (renExpr r u)) l) X (lsub1 (renExpr r A) l)) (Eq-sym (ren-lsub1 r u l))
        (conv-LApp-beta (ren-IsType (rt-addL {G = G} {H = H} rt) (ent-addL G H e) (wkL-WfCtx wfH) dA)
                        (ren-HasType (rt-addL {G = G} {H = H} rt) (ent-addL G H e) (wkL-WfCtx wfH) du)))
  ren-ConvTm {G = G} {H = H} {r = r} rt e wfH (conv-LApp-eta {A = A} {t = t} dA dt) =
    Eq-transport (\ X -> ConvTm H (renExpr r t) X (LPi (renExpr r A)))
      (Eq-cong2 (\ Y X -> LLam (renExpr r A) (LApp Y X (lvar zero))) (lsubE-ren (liftL lwkS) r A) (Eq-sym (ren-lshift r t)))
      (conv-LApp-eta (ren-IsType (rt-addL {G = G} {H = H} rt) (ent-addL G H e) (wkL-WfCtx wfH) dA) (ren-HasType rt e wfH dt))
  ren-ConvTm rt e wfH (conv-collapse lp dA dt) =
    conv-collapse (loop-ent e lp) (ren-IsType rt e wfH dA) (ren-HasType rt e wfH dt)
  ren-ConvTm rt e wfH (conv-sym d)   = conv-sym (ren-ConvTm rt e wfH d)
  ren-ConvTm rt e wfH (conv-trans d1 d2) =
    conv-trans (ren-ConvTm rt e wfH d1) (ren-ConvTm rt e wfH d2)
  ren-ConvTm rt e wfH (conv-conv dMN dAB) =
    conv-conv (ren-ConvTm rt e wfH dMN) (ren-ConvTy rt e wfH dAB)
  ren-ConvTm rt e wfH (conv-cong-Lam-body dA dB db0 db) =
    let dA'  = ren-IsType rt e wfH dA
        wfH' = wf-extend dA'
        rt'  = liftRen-RenTypes rt
    in conv-cong-Lam-body dA' (ren-IsType rt' e wfH' dB) (ren-HasType rt' e wfH' db0)
                          (ren-ConvTm rt' e wfH' db)
  ren-ConvTm rt e wfH (conv-cong-Lam-Ty dA0 dB0 dA dB db) =
    let dA-IT = ren-IsType rt e wfH dA0
        wfH'  = wf-extend dA-IT
        rt'   = liftRen-RenTypes rt
    in conv-cong-Lam-Ty dA-IT (ren-IsType rt' e wfH' dB0) (ren-ConvTy rt e wfH dA) (ren-ConvTy rt' e wfH' dB)
                        (ren-HasType rt' e wfH' db)
  ren-ConvTm {r = r} rt e wfH
             (conv-cong-App-fun {A = A} {B = B} {c = c} {c' = c'} {a = a}
                                 dA dB dc da) =
    let dA'  = ren-IsType rt e wfH dA
        wfH' = wf-extend dA'
        rt'  = liftRen-RenTypes rt
        appL = App (renExpr r A) (renExpr (liftRen r) B)
                   (renExpr r c) (renExpr r a)
        appR = App (renExpr r A) (renExpr (liftRen r) B)
                   (renExpr r c') (renExpr r a)
    in Eq-transport (\ T -> ConvTm _ appL appR T)
                    (Eq-sym (ren-subst1 r B a))
        (conv-cong-App-fun dA' (ren-IsType rt' e wfH' dB)
                           (ren-ConvTm rt e wfH dc) (ren-HasType rt e wfH da))
  ren-ConvTm {r = r} rt e wfH
             (conv-cong-App-arg {A = A} {B = B} {c = c} {a = a} {a' = a'}
                                 dA dB dc da Bsubst-conv) =
    let dA'  = ren-IsType rt e wfH dA
        wfH' = wf-extend dA'
        rt'  = liftRen-RenTypes rt
        appL = App (renExpr r A) (renExpr (liftRen r) B)
                   (renExpr r c) (renExpr r a)
        appR = App (renExpr r A) (renExpr (liftRen r) B)
                   (renExpr r c) (renExpr r a')
        Bsubst-conv' =
          Eq-transport (\ X -> ConvTy _ X _) (ren-subst1 r B a)
            (Eq-transport (\ Y -> ConvTy _ _ Y) (ren-subst1 r B a')
              (ren-ConvTy rt e wfH Bsubst-conv))
    in Eq-transport (\ T -> ConvTm _ appL appR T)
                    (Eq-sym (ren-subst1 r B a))
        (conv-cong-App-arg dA' (ren-IsType rt' e wfH' dB)
                           (ren-HasType rt e wfH dc) (ren-ConvTm rt e wfH da)
                           Bsubst-conv')
  ren-ConvTm {r = r} rt e wfH
             (conv-cong-App-Ty {A = A} {A' = A'} {B = B} {B' = B'}
                                {c = c} {a = a} dA0 dB0 dA dB dc da) =
    let dA-IT = ren-IsType rt e wfH dA0
        wfH'  = wf-extend dA-IT
        rt'   = liftRen-RenTypes rt
        appL  = App (renExpr r A) (renExpr (liftRen r) B)
                    (renExpr r c) (renExpr r a)
        appR  = App (renExpr r A') (renExpr (liftRen r) B')
                    (renExpr r c) (renExpr r a)
    in Eq-transport (\ T -> ConvTm _ appL appR T)
                    (Eq-sym (ren-subst1 r B a))
        (conv-cong-App-Ty dA-IT (ren-IsType rt' e wfH' dB0) (ren-ConvTy rt e wfH dA) (ren-ConvTy rt' e wfH' dB)
                          (ren-HasType rt e wfH dc) (ren-HasType rt e wfH da))
  ren-ConvTm {r = r} rt e wfH
             (conv-beta {A = A} {B = B} {b = b} {a = a} dA dB db da) =
    let dA'  = ren-IsType rt e wfH dA
        wfH' = wf-extend dA'
        rt'  = liftRen-RenTypes rt
        core = conv-beta dA' (ren-IsType rt' e wfH' dB)
                         (ren-HasType rt' e wfH' db) (ren-HasType rt e wfH da)
        appL = App (renExpr r A) (renExpr (liftRen r) B)
                   (Lam (renExpr r A) (renExpr (liftRen r) B)
                        (renExpr (liftRen r) b))
                   (renExpr r a)
    in Eq-transport (\ T -> ConvTm _ appL _ T)
                    (Eq-sym (ren-subst1 r B a))
        (Eq-transport (\ M -> ConvTm _ appL M _)
                      (Eq-sym (ren-subst1 r b a))
          core)
  ren-ConvTm {H = H} {r = r} rt e wfH
             (conv-eta {A = A} {B = B} {c = c} dA dB dc) =
    let dA'  = ren-IsType rt e wfH dA
        wfH' = wf-extend dA'
        rt'  = liftRen-RenTypes rt
        core = conv-eta dA' (ren-IsType rt' e wfH' dB) (ren-HasType rt e wfH dc)
        eA   = Eq-sym (ren-wk-comm r A)
        eC   = Eq-sym (ren-wk-comm r c)
        eB   = Eq-sym (liftRen-liftRen-wk-comm r B)
        app-eq = Eq-cong4 App eA eB eC refl
        lam-eq = Eq-cong (Lam (renExpr r A) (renExpr (liftRen r) B)) app-eq
    in Eq-transport
         (\ M -> ConvTm H (renExpr r c) M
                   (Pi (renExpr r A) (renExpr (liftRen r) B)))
         lam-eq core
  ----------------------------------------------------------------------
  -- Weakening corollaries
  ----------------------------------------------------------------------
  wk-IsType : {n : Nat} {G : Ctx n} {C A : Expr n}
    -> IsType G C -> IsType G A -> IsType (extend G C) (wkExpr A)
  wk-IsType {G = G} {C = C} dC dA =
    ren-IsType (wkRen-RenTypes {G = G} {C = C}) ent-refl (wf-extend dC) dA

  wk-HasType : {n : Nat} {G : Ctx n} {C M A : Expr n}
    -> IsType G C -> HasType G M A
    -> HasType (extend G C) (wkExpr M) (wkExpr A)
  wk-HasType {G = G} {C = C} dC dM =
    ren-HasType (wkRen-RenTypes {G = G} {C = C}) ent-refl (wf-extend dC) dM

  wk-ConvTy : {n : Nat} {G : Ctx n} {C A B : Expr n}
    -> IsType G C -> ConvTy G A B
    -> ConvTy (extend G C) (wkExpr A) (wkExpr B)
  wk-ConvTy {G = G} {C = C} dC d =
    ren-ConvTy (wkRen-RenTypes {G = G} {C = C}) ent-refl (wf-extend dC) d

  wk-ConvTm : {n : Nat} {G : Ctx n} {C M N A : Expr n}
    -> IsType G C -> ConvTm G M N A
    -> ConvTm (extend G C) (wkExpr M) (wkExpr N) (wkExpr A)
  wk-ConvTm {G = G} {C = C} dC d =
    ren-ConvTm (wkRen-RenTypes {G = G} {C = C}) ent-refl (wf-extend dC) d

  ----------------------------------------------------------------------
  -- Lifting a well-typed substitution
  ----------------------------------------------------------------------
  liftSub-WtSub : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {sigma : Sub h g} {A : Expr g}
    -> WtSub H G sigma -> WfCtx H -> IsType G A
    -> WtSub (extend H (substExpr sigma A)) (extend G A) (liftSub sigma)
  liftSub-WtSub ws wfH dA = mkWt (wtE ws) (liftSub-WtSubTy ws wfH dA)

  liftSub-WtSubTy : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {sigma : Sub h g} {A : Expr g}
    -> WtSub H G sigma -> WfCtx H -> IsType G A
    -> WtSubTy (extend H (substExpr sigma A)) (extend G A) (liftSub sigma)
  liftSub-WtSubTy {sigma = sigma} {A = A} ws wfH dA fzero =
    Eq-transport (\ T -> HasType (extend _ (substExpr sigma A)) (Var fzero) T)
      (Eq-sym (Eq-trans (subst-ren (liftSub sigma) wkRen A)
                        (Eq-sym (ren-subst wkRen sigma A))))
      (ty-var (wf-extend (subst-IsType ws wfH dA)))
  liftSub-WtSubTy {H = H} {G = G} {sigma = sigma} {A = A} ws wfH dA (fsuc i) =
    Eq-transport
      (\ T -> HasType (extend H (substExpr sigma A)) (wkExpr (sigma i)) T)
      (Eq-sym (Eq-trans (subst-ren (liftSub sigma) wkRen (lookup G i))
                        (Eq-sym (ren-subst wkRen sigma (lookup G i)))))
      (wk-HasType (subst-IsType ws wfH dA) (wtT ws i))

  ----------------------------------------------------------------------
  -- Substitution preserves IsType
  ----------------------------------------------------------------------
  subst-IsType : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {sigma : Sub h g} {A : Expr g}
    -> WtSub H G sigma -> WfCtx H
    -> IsType G A -> IsType H (substExpr sigma A)
  subst-IsType ws wfH (is-U _)   = is-U wfH
  subst-IsType ws wfH (is-El d)  = is-El (subst-HasType ws wfH d)
  subst-IsType ws wfH (is-Emp _) = is-Emp wfH
  subst-IsType ws wfH (is-Pi dA dB) =
    let dA' = subst-IsType ws wfH dA
    in is-Pi dA' (subst-IsType (liftSub-WtSub ws wfH dA) (wf-extend dA') dB)
  subst-IsType ws wfH (is-Grd {c = c} dG dA) =
    is-Grd wfH (subst-IsType (WtSub-addC c ws) (wkC-WfCtx c wfH) dA)
  subst-IsType ws wfH (is-LPi dG dA) =
    is-LPi wfH (subst-IsType (WtSub-addL ws) (wkL-WfCtx wfH) dA)
  ----------------------------------------------------------------------
  -- Substitution preserves HasType
  ----------------------------------------------------------------------
  subst-HasType : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {sigma : Sub h g} {M A : Expr g}
    -> WtSub H G sigma -> WfCtx H
    -> HasType G M A -> HasType H (substExpr sigma M) (substExpr sigma A)
  subst-HasType ws wfH (ty-GLam {c = c} dG dA dt) =
    ty-GLam wfH (subst-IsType (WtSub-addC c ws) (wkC-WfCtx c wfH) dA)
                (subst-HasType (WtSub-addC c ws) (wkC-WfCtx c wfH) dt)
  subst-HasType ws wfH (ty-LLam dG dA du) =
    ty-LLam wfH (subst-IsType (WtSub-addL ws) (wkL-WfCtx wfH) dA)
                (subst-HasType (WtSub-addL ws) (wkL-WfCtx wfH) du)
  subst-HasType {H = H} {sigma = sigma} ws wfH (ty-LApp {A = A} {t = t} {l = l} dA dt) =
    Eq-transport (\ T -> HasType H (LApp (substExpr (\ i -> lshiftE (sigma i)) A) (substExpr sigma t) l) T) (Eq-sym (subst-lsub1 sigma A l))
      (ty-LApp (subst-IsType (WtSub-addL ws) (wkL-WfCtx wfH) dA) (subst-HasType ws wfH dt))
  subst-HasType ws wfH (ty-collapse lp dA) =
    ty-collapse (loop-ent (wtE ws) lp) (subst-IsType ws wfH dA)
  subst-HasType ws wfH (ty-PiCode da db) =
    let da'  = subst-HasType ws wfH da
        wfH' = wf-extend (is-El da')
        ws'  = liftSub-WtSub ws wfH (is-El da)
    in ty-PiCode da' (subst-HasType ws' wfH' db)
  subst-HasType ws wfH (ty-UCode _ v) = ty-UCode wfH (valid-ent (wtE ws) v)
  subst-HasType ws wfH (ty-Lift v da) = ty-Lift (valid-ent (wtE ws) v) (subst-HasType ws wfH da)
  subst-HasType ws wfH (ty-EmpCode _) = ty-EmpCode wfH
  subst-HasType ws wfH (ty-var {i = i} _) = wtT ws i
  subst-HasType ws wfH (ty-conv dM dAB) =
    ty-conv (subst-HasType ws wfH dM) (subst-ConvTy ws wfH dAB)
  subst-HasType ws wfH (ty-Lam dA dB db) =
    let dA'  = subst-IsType ws wfH dA
        wfH' = wf-extend dA'
        ws'  = liftSub-WtSub ws wfH dA
    in ty-Lam dA' (subst-IsType ws' wfH' dB) (subst-HasType ws' wfH' db)
  subst-HasType {sigma = sigma} ws wfH
                (ty-App {A = A} {B = B} {c = c} {a = a} dA dB dc da) =
    let dA'  = subst-IsType ws wfH dA
        wfH' = wf-extend dA'
        ws'  = liftSub-WtSub ws wfH dA
        appE = App (substExpr sigma A) (substExpr (liftSub sigma) B)
                   (substExpr sigma c) (substExpr sigma a)
    in Eq-transport (\ T -> HasType _ appE T)
        (Eq-sym (subst-subst1 sigma B a))
        (ty-App dA' (subst-IsType ws' wfH' dB)
                    (subst-HasType ws wfH dc) (subst-HasType ws wfH da))
  ----------------------------------------------------------------------
  -- Substitution preserves ConvTy
  ----------------------------------------------------------------------
  subst-ConvTy : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {sigma : Sub h g} {A B : Expr g}
    -> WtSub H G sigma -> WfCtx H
    -> ConvTy G A B -> ConvTy H (substExpr sigma A) (substExpr sigma B)
  subst-ConvTy ws wfH (conv-Ty-El d) = conv-Ty-El (subst-ConvTm ws wfH d)
  subst-ConvTy ws wfH (conv-Ty-U-lvl _ v) = conv-Ty-U-lvl wfH (valid-ent (wtE ws) v)
  subst-ConvTy ws wfH (conv-Ty-El-lvl v da) =
    conv-Ty-El-lvl (valid-ent (wtE ws) v) (subst-HasType ws wfH da)
  subst-ConvTy ws wfH (conv-Ty-El-UCode _ v) = conv-Ty-El-UCode wfH (valid-ent (wtE ws) v)
  subst-ConvTy ws wfH (conv-Ty-El-PiCode da db) =
    let da'  = subst-HasType ws wfH da
    in conv-Ty-El-PiCode da' (subst-HasType (liftSub-WtSub ws wfH (is-El da)) (wf-extend (is-El da')) db)
  subst-ConvTy ws wfH (conv-Ty-El-Lift v da) =
    conv-Ty-El-Lift (valid-ent (wtE ws) v) (subst-HasType ws wfH da)
  subst-ConvTy ws wfH (conv-Ty-El-EmpCode _) = conv-Ty-El-EmpCode wfH
  subst-ConvTy ws wfH (conv-Ty-Grd-beta {c = c} v dA) =
    conv-Ty-Grd-beta (validC-ent c (wtE ws) v) (subst-IsType ws wfH dA)
  subst-ConvTy ws wfH (conv-Ty-Grd-equiv {c = c} dG q dA) =
    conv-Ty-Grd-equiv wfH (equivC-ent (wtE ws) q) (subst-IsType (WtSub-addC c ws) (wkC-WfCtx c wfH) dA)
  subst-ConvTy ws wfH (conv-Ty-Grd {c = c} dG dA dAB) =
    conv-Ty-Grd wfH (subst-IsType (WtSub-addC c ws) (wkC-WfCtx c wfH) dA)
                    (subst-ConvTy (WtSub-addC c ws) (wkC-WfCtx c wfH) dAB)
  subst-ConvTy ws wfH (conv-Ty-LPi dG dA dAB) =
    conv-Ty-LPi wfH (subst-IsType (WtSub-addL ws) (wkL-WfCtx wfH) dA)
                    (subst-ConvTy (WtSub-addL ws) (wkL-WfCtx wfH) dAB)
  subst-ConvTy ws wfH (conv-Ty-collapse lp dA) =
    conv-Ty-collapse (loop-ent (wtE ws) lp) (subst-IsType ws wfH dA)
  subst-ConvTy ws wfH (conv-Ty-refl dA) =
    conv-Ty-refl (subst-IsType ws wfH dA)
  subst-ConvTy ws wfH (conv-Ty-sym d) =
    conv-Ty-sym (subst-ConvTy ws wfH d)
  subst-ConvTy ws wfH (conv-Ty-trans d1 d2) =
    conv-Ty-trans (subst-ConvTy ws wfH d1) (subst-ConvTy ws wfH d2)
  subst-ConvTy ws wfH (conv-Ty-Pi dA0 dB0 dA dB) =
    let dA-IT = subst-IsType ws wfH dA0
        wfH'  = wf-extend dA-IT
        ws'   = liftSub-WtSub ws wfH dA0
    in conv-Ty-Pi dA-IT (subst-IsType ws' wfH' dB0) (subst-ConvTy ws wfH dA) (subst-ConvTy ws' wfH' dB)
  ----------------------------------------------------------------------
  -- Substitution preserves ConvTm
  ----------------------------------------------------------------------
  subst-ConvTm : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {sigma : Sub h g} {M N A : Expr g}
    -> WtSub H G sigma -> WfCtx H
    -> ConvTm G M N A
    -> ConvTm H (substExpr sigma M) (substExpr sigma N) (substExpr sigma A)
  subst-ConvTm ws wfH (conv-refl dM) = conv-refl (subst-HasType ws wfH dM)
  subst-ConvTm ws wfH (conv-cong-PiCode da db daa dbb) =
    let da'  = subst-HasType ws wfH da
        wfH' = wf-extend (is-El da')
        ws'  = liftSub-WtSub ws wfH (is-El da)
    in conv-cong-PiCode da' (subst-HasType ws' wfH' db) (subst-ConvTm ws wfH daa) (subst-ConvTm ws' wfH' dbb)
  subst-ConvTm ws wfH (conv-cong-Lift v daa) =
    conv-cong-Lift (valid-ent (wtE ws) v) (subst-ConvTm ws wfH daa)
  subst-ConvTm ws wfH (conv-Lift-refl v da) =
    conv-Lift-refl (valid-ent (wtE ws) v) (subst-HasType ws wfH da)
  subst-ConvTm ws wfH (conv-Lift-Lift v w da) =
    conv-Lift-Lift (valid-ent (wtE ws) v) (valid-ent (wtE ws) w) (subst-HasType ws wfH da)
  subst-ConvTm ws wfH (conv-Lift-UCode _ v w) =
    conv-Lift-UCode wfH (valid-ent (wtE ws) v) (valid-ent (wtE ws) w)
  subst-ConvTm ws wfH (conv-Lift-PiCode v da db) =
    let da'  = subst-HasType ws wfH da
    in conv-Lift-PiCode (valid-ent (wtE ws) v) da'
         (subst-HasType (liftSub-WtSub ws wfH (is-El da)) (wf-extend (is-El da')) db)
  subst-ConvTm ws wfH (conv-Lift-EmpCode _ v) = conv-Lift-EmpCode wfH (valid-ent (wtE ws) v)
  subst-ConvTm ws wfH (conv-UCode-lvl _ v w u) =
    conv-UCode-lvl wfH (valid-ent (wtE ws) v) (valid-ent (wtE ws) w) (valid-ent (wtE ws) u)
  subst-ConvTm ws wfH (conv-Lift-lvl v w u da) =
    conv-Lift-lvl (valid-ent (wtE ws) v) (valid-ent (wtE ws) w) (valid-ent (wtE ws) u) (subst-HasType ws wfH da)
  subst-ConvTm ws wfH (conv-PiCode-lvl v da db) =
    let da'  = subst-HasType ws wfH da
    in conv-PiCode-lvl (valid-ent (wtE ws) v) da'
         (subst-HasType (liftSub-WtSub ws wfH (is-El da)) (wf-extend (is-El da')) db)
  subst-ConvTm ws wfH (conv-EmpCode-lvl _ v) = conv-EmpCode-lvl wfH (valid-ent (wtE ws) v)
  subst-ConvTm ws wfH (conv-cong-GLam {c = c} dG dA dt dtt) =
    conv-cong-GLam wfH (subst-IsType (WtSub-addC c ws) (wkC-WfCtx c wfH) dA)
                       (subst-HasType (WtSub-addC c ws) (wkC-WfCtx c wfH) dt)
                       (subst-ConvTm (WtSub-addC c ws) (wkC-WfCtx c wfH) dtt)
  subst-ConvTm ws wfH (conv-GLam-eta {c = c} dG dA dt dt') =
    conv-GLam-eta wfH (subst-IsType (WtSub-addC c ws) (wkC-WfCtx c wfH) dA)
                      (subst-HasType ws wfH dt)
                      (subst-HasType (WtSub-addC c ws) (wkC-WfCtx c wfH) dt')
  subst-ConvTm ws wfH (conv-GLam-beta {c = c} v dA dt) =
    conv-GLam-beta (validC-ent c (wtE ws) v) (subst-IsType ws wfH dA) (subst-HasType ws wfH dt)
  subst-ConvTm ws wfH (conv-cong-LLam dG dA du duu) =
    conv-cong-LLam wfH (subst-IsType (WtSub-addL ws) (wkL-WfCtx wfH) dA)
                       (subst-HasType (WtSub-addL ws) (wkL-WfCtx wfH) du)
                       (subst-ConvTm (WtSub-addL ws) (wkL-WfCtx wfH) duu)
  subst-ConvTm ws wfH (conv-cong-GLam-Ty {c = c} dG dA dAA dt) =
    conv-cong-GLam-Ty wfH (subst-IsType (WtSub-addC c ws) (wkC-WfCtx c wfH) dA)
      (subst-ConvTy (WtSub-addC c ws) (wkC-WfCtx c wfH) dAA)
      (subst-HasType (WtSub-addC c ws) (wkC-WfCtx c wfH) dt)
  subst-ConvTm ws wfH (conv-cong-LLam-Ty dG dA dAA du) =
    conv-cong-LLam-Ty wfH (subst-IsType (WtSub-addL ws) (wkL-WfCtx wfH) dA)
      (subst-ConvTy (WtSub-addL ws) (wkL-WfCtx wfH) dAA)
      (subst-HasType (WtSub-addL ws) (wkL-WfCtx wfH) du)
  subst-ConvTm {H = H} {sigma = sigma} ws wfH (conv-cong-LApp-Ty {A = A} {A' = A'} {t = t} {l = l} dA dAA dt) =
    Eq-transport (\ T -> ConvTm H (LApp (substExpr (\ i -> lshiftE (sigma i)) A) (substExpr sigma t) l)
                                  (LApp (substExpr (\ i -> lshiftE (sigma i)) A') (substExpr sigma t) l) T)
      (Eq-sym (subst-lsub1 sigma A l))
      (conv-cong-LApp-Ty (subst-IsType (WtSub-addL ws) (wkL-WfCtx wfH) dA)
        (subst-ConvTy (WtSub-addL ws) (wkL-WfCtx wfH) dAA) (subst-HasType ws wfH dt))
  subst-ConvTm {H = H} {sigma = sigma} ws wfH (conv-cong-LApp-fun {A = A} {t = t} {t' = t'} {l = l} dA dtt) =
    Eq-transport (\ T -> ConvTm H (LApp (substExpr (\ i -> lshiftE (sigma i)) A) (substExpr sigma t) l) (LApp (substExpr (\ i -> lshiftE (sigma i)) A) (substExpr sigma t') l) T)
      (Eq-sym (subst-lsub1 sigma A l))
      (conv-cong-LApp-fun (subst-IsType (WtSub-addL ws) (wkL-WfCtx wfH) dA) (subst-ConvTm ws wfH dtt))
  subst-ConvTm {H = H} {sigma = sigma} ws wfH (conv-cong-LApp-lvl {A = A} {t = t} {l = l} {l' = l'} dA dt v dAA) =
    Eq-transport (\ T -> ConvTm H (LApp (substExpr (\ i -> lshiftE (sigma i)) A) (substExpr sigma t) l) (LApp (substExpr (\ i -> lshiftE (sigma i)) A) (substExpr sigma t) l') T)
      (Eq-sym (subst-lsub1 sigma A l))
      (conv-cong-LApp-lvl (subst-IsType (WtSub-addL ws) (wkL-WfCtx wfH) dA) (subst-HasType ws wfH dt)
        (valid-ent (wtE ws) v)
        (Eq-transport (\ X -> ConvTy H X (lsub1 (substExpr (\ i -> lshiftE (sigma i)) A) l')) (subst-lsub1 sigma A l)
          (Eq-transport (ConvTy H (substExpr sigma (lsub1 A l))) (subst-lsub1 sigma A l') (subst-ConvTy ws wfH dAA))))
  subst-ConvTm ws wfH (conv-GLam-equiv {c = c} dG q dA dt) =
    conv-GLam-equiv wfH (equivC-ent (wtE ws) q)
      (subst-IsType (WtSub-addC c ws) (wkC-WfCtx c wfH) dA)
      (subst-HasType (WtSub-addC c ws) (wkC-WfCtx c wfH) dt)
  subst-ConvTm {H = H} {sigma = sigma} ws wfH (conv-LApp-beta {A = A} {u = u} {l = l} dA du) =
    Eq-transport (\ T -> ConvTm H (LApp (substExpr (\ i -> lshiftE (sigma i)) A) (LLam (substExpr (\ i -> lshiftE (sigma i)) A) (substExpr (\ i -> lshiftE (sigma i)) u)) l) (substExpr sigma (lsub1 u l)) T)
      (Eq-sym (subst-lsub1 sigma A l))
      (Eq-transport (\ X -> ConvTm H (LApp (substExpr (\ i -> lshiftE (sigma i)) A) (LLam (substExpr (\ i -> lshiftE (sigma i)) A) (substExpr (\ i -> lshiftE (sigma i)) u)) l) X
                                     (lsub1 (substExpr (\ i -> lshiftE (sigma i)) A) l))
        (Eq-sym (subst-lsub1 sigma u l))
        (conv-LApp-beta (subst-IsType (WtSub-addL ws) (wkL-WfCtx wfH) dA)
                        (subst-HasType (WtSub-addL ws) (wkL-WfCtx wfH) du)))
  subst-ConvTm {H = H} {sigma = sigma} ws wfH (conv-LApp-eta {A = A} {t = t} dA dt) =
    Eq-transport (\ X -> ConvTm H (substExpr sigma t) X (LPi (substExpr (\ i -> lshiftE (sigma i)) A)))
      (Eq-cong2 (\ Y X -> LLam (substExpr (\ i -> lshiftE (sigma i)) A) (LApp Y X (lvar zero))) (subst-lshift2 sigma A) (Eq-sym (subst-lshift sigma t)))
      (conv-LApp-eta (subst-IsType (WtSub-addL ws) (wkL-WfCtx wfH) dA) (subst-HasType ws wfH dt))
  subst-ConvTm ws wfH (conv-collapse lp dA dt) =
    conv-collapse (loop-ent (wtE ws) lp) (subst-IsType ws wfH dA) (subst-HasType ws wfH dt)
  subst-ConvTm ws wfH (conv-sym d)   = conv-sym (subst-ConvTm ws wfH d)
  subst-ConvTm ws wfH (conv-trans d1 d2) =
    conv-trans (subst-ConvTm ws wfH d1) (subst-ConvTm ws wfH d2)
  subst-ConvTm ws wfH (conv-conv dMN dAB) =
    conv-conv (subst-ConvTm ws wfH dMN) (subst-ConvTy ws wfH dAB)
  subst-ConvTm ws wfH (conv-cong-Lam-body dA dB db0 db) =
    let dA'  = subst-IsType ws wfH dA
        wfH' = wf-extend dA'
        ws'  = liftSub-WtSub ws wfH dA
    in conv-cong-Lam-body dA' (subst-IsType ws' wfH' dB) (subst-HasType ws' wfH' db0)
                          (subst-ConvTm ws' wfH' db)
  subst-ConvTm ws wfH (conv-cong-Lam-Ty dA0 dB0 dA dB db) =
    let dA-IT = subst-IsType ws wfH dA0
        wfH'  = wf-extend dA-IT
        ws'   = liftSub-WtSub ws wfH dA0
    in conv-cong-Lam-Ty dA-IT (subst-IsType ws' wfH' dB0) (subst-ConvTy ws wfH dA) (subst-ConvTy ws' wfH' dB)
                        (subst-HasType ws' wfH' db)
  subst-ConvTm {sigma = sigma} ws wfH
               (conv-cong-App-fun {A = A} {B = B} {c = c} {c' = c'} {a = a}
                                   dA dB dc da) =
    let dA'  = subst-IsType ws wfH dA
        wfH' = wf-extend dA'
        ws'  = liftSub-WtSub ws wfH dA
        appL = App (substExpr sigma A) (substExpr (liftSub sigma) B)
                   (substExpr sigma c) (substExpr sigma a)
        appR = App (substExpr sigma A) (substExpr (liftSub sigma) B)
                   (substExpr sigma c') (substExpr sigma a)
    in Eq-transport (\ T -> ConvTm _ appL appR T)
        (Eq-sym (subst-subst1 sigma B a))
        (conv-cong-App-fun dA' (subst-IsType ws' wfH' dB)
                           (subst-ConvTm ws wfH dc) (subst-HasType ws wfH da))
  subst-ConvTm {sigma = sigma} ws wfH
               (conv-cong-App-arg {A = A} {B = B} {c = c} {a = a} {a' = a'}
                                   dA dB dc da Bsubst-conv) =
    let dA'  = subst-IsType ws wfH dA
        wfH' = wf-extend dA'
        ws'  = liftSub-WtSub ws wfH dA
        appL = App (substExpr sigma A) (substExpr (liftSub sigma) B)
                   (substExpr sigma c) (substExpr sigma a)
        appR = App (substExpr sigma A) (substExpr (liftSub sigma) B)
                   (substExpr sigma c) (substExpr sigma a')
        Bsubst-conv' =
          Eq-transport (\ X -> ConvTy _ X _) (subst-subst1 sigma B a)
            (Eq-transport (\ Y -> ConvTy _ _ Y) (subst-subst1 sigma B a')
              (subst-ConvTy ws wfH Bsubst-conv))
    in Eq-transport (\ T -> ConvTm _ appL appR T)
        (Eq-sym (subst-subst1 sigma B a))
        (conv-cong-App-arg dA' (subst-IsType ws' wfH' dB)
                           (subst-HasType ws wfH dc) (subst-ConvTm ws wfH da)
                           Bsubst-conv')
  subst-ConvTm {sigma = sigma} ws wfH
               (conv-cong-App-Ty {A = A} {A' = A'} {B = B} {B' = B'}
                                  {c = c} {a = a} dA0 dB0 dA dB dc da) =
    let dA-IT = subst-IsType ws wfH dA0
        wfH'  = wf-extend dA-IT
        ws'   = liftSub-WtSub ws wfH dA0
        appL  = App (substExpr sigma A) (substExpr (liftSub sigma) B)
                    (substExpr sigma c) (substExpr sigma a)
        appR  = App (substExpr sigma A') (substExpr (liftSub sigma) B')
                    (substExpr sigma c) (substExpr sigma a)
    in Eq-transport (\ T -> ConvTm _ appL appR T)
        (Eq-sym (subst-subst1 sigma B a))
        (conv-cong-App-Ty dA-IT (subst-IsType ws' wfH' dB0) (subst-ConvTy ws wfH dA) (subst-ConvTy ws' wfH' dB)
                          (subst-HasType ws wfH dc) (subst-HasType ws wfH da))
  subst-ConvTm {sigma = sigma} ws wfH
               (conv-beta {A = A} {B = B} {b = b} {a = a} dA dB db da) =
    let dA'  = subst-IsType ws wfH dA
        wfH' = wf-extend dA'
        ws'  = liftSub-WtSub ws wfH dA
        core = conv-beta dA' (subst-IsType ws' wfH' dB)
                         (subst-HasType ws' wfH' db)
                         (subst-HasType ws wfH da)
        appL = App (substExpr sigma A) (substExpr (liftSub sigma) B)
                   (Lam (substExpr sigma A) (substExpr (liftSub sigma) B)
                        (substExpr (liftSub sigma) b))
                   (substExpr sigma a)
    in Eq-transport (\ T -> ConvTm _ appL _ T)
        (Eq-sym (subst-subst1 sigma B a))
        (Eq-transport (\ M -> ConvTm _ appL M _)
          (Eq-sym (subst-subst1 sigma b a))
          core)
  subst-ConvTm {H = H} {sigma = sigma} ws wfH
               (conv-eta {A = A} {B = B} {c = c} dA dB dc) =
    let dA'  = subst-IsType ws wfH dA
        wfH' = wf-extend dA'
        ws'  = liftSub-WtSub ws wfH dA
        core = conv-eta dA' (subst-IsType ws' wfH' dB)
                            (subst-HasType ws wfH dc)
        eA   = Eq-sym
                (Eq-trans (subst-ren (liftSub sigma) wkRen A)
                          (Eq-sym (ren-subst wkRen sigma A)))
        eC   = Eq-sym
                (Eq-trans (subst-ren (liftSub sigma) wkRen c)
                          (Eq-sym (ren-subst wkRen sigma c)))
        eB   = Eq-sym (liftSub-liftSub-wk-comm sigma B)
        app-eq = Eq-cong4 App eA eB eC refl
        lam-eq = Eq-cong (Lam (substExpr sigma A) (substExpr (liftSub sigma) B))
                          app-eq
    in Eq-transport
         (\ M -> ConvTm H (substExpr sigma c) M
                   (Pi (substExpr sigma A) (substExpr (liftSub sigma) B)))
         lam-eq core
  ----------------------------------------------------------------------
  -- Identity-substitution-with-conversion (for context conversion)
  ----------------------------------------------------------------------
  ctx-conv-WtSub : {n : Nat} {G : Ctx n} {A A' : Expr n}
    -> IsType G A -> IsType G A' -> ConvTy G A A'
    -> WtSub (extend G A') (extend G A) idSub
  ctx-conv-WtSub dA dA' AAconv = mkWt ent-refl (ctx-conv-WtSubTy dA dA' AAconv)

  ctx-conv-WtSubTy : {n : Nat} {G : Ctx n} {A A' : Expr n}
    -> IsType G A -> IsType G A' -> ConvTy G A A'
    -> WtSubTy (extend G A') (extend G A) idSub
  ctx-conv-WtSubTy {G = G} {A = A} {A' = A'} dA dA' AAconv fzero =
    Eq-transport (\ T -> HasType (extend G A') (Var fzero) T)
      (Eq-sym (Eq-trans
        (substExpr-ext idSub _ (\ i -> refl) (wkExpr A))
        (substExpr-id (wkExpr A))))
      (ty-conv (ty-var (wf-extend dA'))
               (wk-ConvTy dA' (conv-Ty-sym AAconv)))
  ctx-conv-WtSubTy {G = G} {A' = A'} dA dA' AAconv (fsuc i) =
    Eq-transport (\ T -> HasType (extend G A') (Var (fsuc i)) T)
      (Eq-sym (Eq-trans
        (substExpr-ext idSub _ (\ j -> refl) (wkExpr (lookup G i)))
        (substExpr-id (wkExpr (lookup G i)))))
      (ty-var (wf-extend dA'))

  ----------------------------------------------------------------------
  -- Context conversion
  ----------------------------------------------------------------------
  ctx-conv-IsType : {n : Nat} {G : Ctx n} {A A' : Expr n} {B : Expr (suc n)}
    -> IsType G A -> IsType G A' -> ConvTy G A A'
    -> IsType (extend G A) B -> IsType (extend G A') B
  ctx-conv-IsType {B = B} dA dA' AAconv d =
    let d' = subst-IsType (ctx-conv-WtSub dA dA' AAconv) (wf-extend dA') d
    in Eq-transport (\ X -> IsType (extend _ _) X) (substExpr-id B) d'

  ctx-conv-HasType : {n : Nat} {G : Ctx n} {A A' : Expr n}
    {M B : Expr (suc n)}
    -> IsType G A -> IsType G A' -> ConvTy G A A'
    -> HasType (extend G A) M B -> HasType (extend G A') M B
  ctx-conv-HasType {M = M} {B = B} dA dA' AAconv d =
    let d' = subst-HasType (ctx-conv-WtSub dA dA' AAconv) (wf-extend dA') d
    in Eq-transport (\ X -> HasType (extend _ _) X B) (substExpr-id M)
        (Eq-transport (\ Y -> HasType (extend _ _) (substExpr idSub M) Y)
          (substExpr-id B) d')

  ctx-conv-ConvTy : {n : Nat} {G : Ctx n} {A A' : Expr n}
    {B C : Expr (suc n)}
    -> IsType G A -> IsType G A' -> ConvTy G A A'
    -> ConvTy (extend G A) B C -> ConvTy (extend G A') B C
  ctx-conv-ConvTy {B = B} {C = C} dA dA' AAconv d =
    let d' = subst-ConvTy (ctx-conv-WtSub dA dA' AAconv) (wf-extend dA') d
    in Eq-transport (\ X -> ConvTy (extend _ _) X C) (substExpr-id B)
        (Eq-transport (\ Y -> ConvTy (extend _ _) (substExpr idSub B) Y)
          (substExpr-id C) d')

  ctx-conv-ConvTm : {n : Nat} {G : Ctx n} {A A' : Expr n}
    {M N B : Expr (suc n)}
    -> IsType G A -> IsType G A' -> ConvTy G A A'
    -> ConvTm (extend G A) M N B -> ConvTm (extend G A') M N B
  ctx-conv-ConvTm {M = M} {N = N} {B = B} dA dA' AAconv d =
    let d' = subst-ConvTm (ctx-conv-WtSub dA dA' AAconv) (wf-extend dA') d
    in Eq-transport (\ X -> ConvTm (extend _ _) X N B) (substExpr-id M)
        (Eq-transport (\ Y -> ConvTm (extend _ _) (substExpr idSub M) Y B)
          (substExpr-id N)
          (Eq-transport
            (\ Z -> ConvTm (extend _ _) (substExpr idSub M) (substExpr idSub N) Z)
            (substExpr-id B) d'))

  ----------------------------------------------------------------------
  -- subst1-WtSub: WtSub for the single-substitution (subst1Sub a)
  ----------------------------------------------------------------------
  subst1-WtSub : {n : Nat} {G : Ctx n} {A : Expr n} {a : Expr n}
    -> IsType G A -> HasType G a A
    -> WtSub G (extend G A) (subst1Sub a)
  subst1-WtSub dA da = mkWt ent-refl (subst1-WtSubTy dA da)

  subst1-WtSubTy : {n : Nat} {G : Ctx n} {A : Expr n} {a : Expr n}
    -> IsType G A -> HasType G a A
    -> WtSubTy G (extend G A) (subst1Sub a)
  subst1-WtSubTy {a = a} dA da fzero =
    Eq-transport (\ T -> HasType _ a T) (Eq-sym (subst1-wk _ a)) da
  subst1-WtSubTy {G = G} {a = a} dA da (fsuc i) =
    Eq-transport (\ T -> HasType _ (Var i) T)
      (Eq-sym (subst1-wk (lookup G i) a))
      (ty-var (isType-WfCtx dA))

  ----------------------------------------------------------------------
  -- Left-side presupposition for ConvTy
  ----------------------------------------------------------------------
  ----------------------------------------------------------------------
  -- Right-side presupposition for ConvTy
  ----------------------------------------------------------------------
  ----------------------------------------------------------------------
  -- Left-side presupposition for ConvTm
  ----------------------------------------------------------------------
  presup-l-ConvTm : {n : Nat} {G : Ctx n} {M N A : Expr n}
    -> ConvTm G M N A -> HasType G M A
  presup-l-ConvTm (conv-cong-PiCode da db _ _) = ty-PiCode da db
  presup-l-ConvTm (conv-cong-Lift le daa)     = ty-Lift le (presup-l-ConvTm daa)
  presup-l-ConvTm (conv-Lift-refl v da)       = ty-Lift (leL-refl v) da
  presup-l-ConvTm (conv-Lift-Lift lm mp da)   = ty-Lift mp (ty-Lift lm da)
  presup-l-ConvTm (conv-Lift-UCode dG kl lm)  = ty-Lift lm (ty-UCode dG kl)
  presup-l-ConvTm (conv-Lift-PiCode le da db) = ty-Lift le (ty-PiCode da db)
  presup-l-ConvTm (conv-Lift-EmpCode dG le)   = ty-Lift le (ty-EmpCode dG)
  presup-l-ConvTm (conv-UCode-lvl dG _ _ lt)  = ty-UCode dG lt
  presup-l-ConvTm (conv-Lift-lvl _ _ le da)   = ty-Lift le da
  presup-l-ConvTm (conv-PiCode-lvl _ da db)   = ty-PiCode da db
  presup-l-ConvTm (conv-EmpCode-lvl dG _)     = ty-EmpCode dG
  presup-l-ConvTm (conv-refl dM)              = dM
  presup-l-ConvTm (conv-GLam-eta _ _ dt _)   = dt
  presup-l-ConvTm (conv-cong-GLam dG dA dt _) = ty-GLam dG dA dt
  presup-l-ConvTm (conv-collapse _ _ dt)      = dt
  presup-l-ConvTm (conv-GLam-beta {c = c} v dA dt) =
    ty-conv (ty-GLam (isType-WfCtx dA) (wkC-IsType c dA) (wkC-HasType c dt)) (conv-Ty-Grd-beta v dA)
  presup-l-ConvTm (conv-cong-LLam dG dA du _) = ty-LLam dG dA du
  presup-l-ConvTm (conv-cong-GLam-Ty dG dA _ dt) = ty-GLam dG dA dt
  presup-l-ConvTm (conv-cong-LLam-Ty dG dA _ du) = ty-LLam dG dA du
  presup-l-ConvTm (conv-cong-LApp-Ty dA _ dt)    = ty-LApp dA dt
  presup-l-ConvTm (conv-cong-LApp-fun dA dtt) = ty-LApp dA (presup-l-ConvTm dtt)
  presup-l-ConvTm (conv-cong-LApp-lvl dA dt _ _) = ty-LApp dA dt
  presup-l-ConvTm (conv-GLam-equiv dG _ dA dt)   = ty-GLam dG dA dt
  presup-l-ConvTm (conv-LApp-beta dA du)      =
    ty-LApp dA (ty-LLam (unL-WfCtx (isType-WfCtx dA)) dA du)
  presup-l-ConvTm (conv-LApp-eta _ dt)        = dt
  presup-l-ConvTm (conv-sym d)                = presup-r-ConvTm d
  presup-l-ConvTm (conv-trans d1 _)           = presup-l-ConvTm d1
  presup-l-ConvTm (conv-conv dMN dAB)         =
    ty-conv (presup-l-ConvTm dMN) dAB
  presup-l-ConvTm (conv-cong-Lam-body dA dB db0 _) =
    ty-Lam dA dB db0
  presup-l-ConvTm (conv-cong-Lam-Ty dA0 dB0 _ _ db) =
    ty-Lam dA0 dB0 db
  presup-l-ConvTm (conv-cong-App-fun dA dB dc da) =
    ty-App dA dB (presup-l-ConvTm dc) da
  presup-l-ConvTm (conv-cong-App-arg dA dB dc da _) =
    ty-App dA dB dc (presup-l-ConvTm da)
  presup-l-ConvTm (conv-cong-App-Ty dA0 _ _ dB dc da) =
    ty-App dA0 (presup-l-ConvTy dB) dc da
  presup-l-ConvTm (conv-beta dA dB db da)     =
    ty-App dA dB (ty-Lam dA dB db) da
  presup-l-ConvTm (conv-eta _ _ dc)           = dc
  ----------------------------------------------------------------------
  -- Right-side presupposition for ConvTm
  ----------------------------------------------------------------------
  presup-r-ConvTm : {n : Nat} {G : Ctx n} {M N A : Expr n}
    -> ConvTm G M N A -> HasType G N A
  presup-r-ConvTm (conv-refl dM)              = dM
  presup-r-ConvTm (conv-GLam-eta dG dA _ dt') = ty-GLam dG dA dt'
  presup-r-ConvTm (conv-cong-GLam dG dA _ dtt) = ty-GLam dG dA (presup-r-ConvTm dtt)
  presup-r-ConvTm (conv-GLam-beta _ _ dt)     = dt
  presup-r-ConvTm (conv-collapse lp dA _)     = ty-collapse lp dA
  presup-r-ConvTm (conv-cong-PiCode da _ daa dbb) =
    let da' = presup-r-ConvTm daa
    in ty-PiCode da' (ctx-conv-HasType (is-El da) (is-El da') (conv-Ty-El daa) (presup-r-ConvTm dbb))
  presup-r-ConvTm (conv-cong-Lift le daa)     = ty-Lift le (presup-r-ConvTm daa)
  presup-r-ConvTm (conv-Lift-refl v da)       = ty-conv da (conv-Ty-U-lvl (typing-WfCtx da) v)
  presup-r-ConvTm (conv-Lift-Lift lm mp da)   = ty-Lift (leL-trans lm mp) da
  presup-r-ConvTm (conv-Lift-UCode dG kl lm)  = ty-UCode dG (ltL-leL kl lm)
  presup-r-ConvTm (conv-Lift-PiCode le da db) =
    let dla = ty-Lift le da
    in ty-PiCode dla
         (ctx-conv-HasType (is-El da) (is-El dla) (conv-Ty-sym (conv-Ty-El-Lift le da)) (ty-Lift le db))
  presup-r-ConvTm (conv-Lift-EmpCode dG _)    = ty-EmpCode dG
  presup-r-ConvTm (conv-UCode-lvl dG v w lt)  =
    ty-conv (ty-UCode dG (ltL-resp v w lt)) (conv-Ty-U-lvl dG (v-sym w))
  presup-r-ConvTm (conv-Lift-lvl v w le da)   =
    let dG = typing-WfCtx da
    in ty-conv (ty-Lift (leL-resp v w le) (ty-conv da (conv-Ty-U-lvl dG v))) (conv-Ty-U-lvl dG (v-sym w))
  presup-r-ConvTm (conv-PiCode-lvl v da db)   =
    let dG  = typing-WfCtx da
        da' = ty-conv da (conv-Ty-U-lvl dG v)
        db' = ctx-conv-HasType (is-El da) (is-El da') (conv-Ty-El-lvl v da)
                (ty-conv db (conv-Ty-U-lvl (typing-WfCtx db) v))
    in ty-conv (ty-PiCode da' db') (conv-Ty-U-lvl dG (v-sym v))
  presup-r-ConvTm (conv-EmpCode-lvl dG v)     = ty-conv (ty-EmpCode dG) (conv-Ty-U-lvl dG (v-sym v))
  presup-r-ConvTm (conv-cong-LLam dG dA _ duu) = ty-LLam dG dA (presup-r-ConvTm duu)
  presup-r-ConvTm (conv-cong-GLam-Ty dG dA dAA dt) =
    ty-conv (ty-GLam dG (presup-r-ConvTy dAA) (ty-conv dt dAA)) (conv-Ty-sym (conv-Ty-Grd dG dA dAA))
  presup-r-ConvTm (conv-cong-LLam-Ty dG dA dAA du) =
    ty-conv (ty-LLam dG (presup-r-ConvTy dAA) (ty-conv du dAA)) (conv-Ty-sym (conv-Ty-LPi dG dA dAA))
  presup-r-ConvTm {G = G} (conv-cong-LApp-Ty {l = l} dA dAA dt) =
    ty-conv (ty-LApp (presup-r-ConvTy dAA) (ty-conv dt (conv-Ty-LPi (typing-WfCtx dt) dA dAA)))
            (lsub-ConvTy (lsk-inst G l) (lok-inst G l) (conv-Ty-sym dAA))
  presup-r-ConvTm (conv-cong-LApp-fun dA dtt) = ty-LApp dA (presup-r-ConvTm dtt)
  presup-r-ConvTm (conv-cong-LApp-lvl dA dt _ dAA) = ty-conv (ty-LApp dA dt) (conv-Ty-sym dAA)
  presup-r-ConvTm (conv-GLam-equiv dG q dA dt)   =
    ty-conv (ty-GLam dG (swapC-IsType q dA) (swapC-HasType q dt))
            (conv-Ty-sym (conv-Ty-Grd-equiv dG q dA))
  presup-r-ConvTm {G = G} (conv-LApp-beta {l = l} dA du) =
    lsub-HasType (lsk-inst G l) (lok-inst G l) du
  presup-r-ConvTm {G = G} (conv-LApp-eta {A = A} {t = t} dA dt) =
    ty-LLam (typing-WfCtx dt) dA
      (Eq-transport (\ T -> HasType (addL G) (LApp (lsubE (liftL lwkS) A) (lshiftE t) (lvar zero)) T) (lsub1-lift-var A)
        (ty-LApp (lsub-IsType (lsk-addL (lsk-shift G)) (lok-addL G (addL G) (lok-shift G)) dA)
                 (lsub-HasType (lsk-shift G) (lok-shift G) dt)))
  presup-r-ConvTm (conv-sym d)                = presup-l-ConvTm d
  presup-r-ConvTm (conv-trans _ d2)           = presup-r-ConvTm d2
  presup-r-ConvTm (conv-conv dMN dAB)         =
    ty-conv (presup-r-ConvTm dMN) dAB
  presup-r-ConvTm (conv-cong-Lam-body dA dB _ db) =
    ty-Lam dA dB (presup-r-ConvTm db)
  presup-r-ConvTm (conv-cong-Lam-Ty dA-IT dB-IT dA dB db) =
    let dA'-IT = presup-r-ConvTy dA
        dB'-IT = ctx-conv-IsType dA-IT dA'-IT dA (presup-r-ConvTy dB)
        db'    = ctx-conv-HasType dA-IT dA'-IT dA (ty-conv db dB)
    in ty-conv (ty-Lam dA'-IT dB'-IT db')
               (conv-Ty-sym (conv-Ty-Pi dA-IT dB-IT dA dB))
  presup-r-ConvTm (conv-cong-App-fun dA dB dc da) =
    ty-App dA dB (presup-r-ConvTm dc) da
  presup-r-ConvTm (conv-cong-App-arg dA dB dc da Bsubst-conv) =
    ty-conv (ty-App dA dB dc (presup-r-ConvTm da))
            (conv-Ty-sym Bsubst-conv)
  presup-r-ConvTm (conv-cong-App-Ty dA-IT _ dA dB dc da) =
    let dA'-IT = presup-r-ConvTy dA
        dB'-IT = ctx-conv-IsType dA-IT dA'-IT dA (presup-r-ConvTy dB)
        dc'    = ty-conv dc (conv-Ty-Pi dA-IT (presup-l-ConvTy dB) dA dB)
        da'    = ty-conv da dA
        result-app = ty-App dA'-IT dB'-IT dc' da'
        -- subst1 B' a = subst1 B a (substituting same a into B B')
        Bsubst : ConvTy _ _ _
        Bsubst = subst-ConvTy (subst1-WtSub dA-IT da)
                              (isType-WfCtx dA-IT)
                              (conv-Ty-sym dB)
    in ty-conv result-app Bsubst
  presup-r-ConvTm (conv-beta {A = A} {B = B} {b = b} {a = a}
                              dA dB db da) =
    subst-HasType (subst1-WtSub dA da) (isType-WfCtx dA) db
  presup-r-ConvTm {G = G} (conv-eta {A = A} {B = B} {c = c} dA dB dc) =
    let wfG-A = wf-extend dA
        c-wk  = wk-HasType dA dc
        v0    = ty-var {G = extend G A} {i = fzero} wfG-A
        A-wk-IT = wk-IsType dA dA
        B-wk-IT = ren-IsType
                    (liftRen-RenTypes
                       (wkRen-RenTypes {G = G} {C = A}))
                    ent-refl (wf-extend A-wk-IT) dB
        appE  = App (wkExpr A) (renExpr (liftRen wkRen) B)
                    (wkExpr c) (Var fzero)
        body : HasType (extend G A) appE
                       (subst1 (renExpr (liftRen wkRen) B) (Var fzero))
        body = ty-App A-wk-IT B-wk-IT c-wk v0
        body' = Eq-transport (\ T -> HasType (extend G A) appE T)
                  (subst1-liftWk-cancel B) body
    in ty-Lam dA dB body'
------------------------------------------------------------------------
-- The type of a typed term is a type
------------------------------------------------------------------------

typing-IsType : {n : Nat} {G : Ctx n} {M A : Expr n}
  -> HasType G M A -> IsType G A
typing-IsType (ty-GLam dG dA _)    = isType-Grd dG dA
typing-IsType (ty-LLam dG dA _)    = isType-LPi dG dA
typing-IsType {G = G} (ty-LApp {l = l} dA dt) = lsub-IsType (lsk-inst G l) (lok-inst G l) dA
typing-IsType (ty-collapse _ dA)   = dA
typing-IsType (ty-var {i = i} dG)  = wfCtx-lookup dG i
typing-IsType (ty-conv _ dAB)      = presup-r-ConvTy dAB
typing-IsType (ty-PiCode da _)     = isType-U (typing-WfCtx da)
typing-IsType (ty-UCode dG _)      = isType-U dG
typing-IsType (ty-Lift _ da)       = isType-U (typing-WfCtx da)
typing-IsType (ty-EmpCode dG)      = isType-U dG
typing-IsType (ty-Lam dA dB _)     = isType-Pi dA dB
typing-IsType (ty-App dA dB _ da)  =
  subst-IsType (subst1-WtSub dA da) (isType-WfCtx dA) dB

------------------------------------------------------------------------
-- The binder congruences with their presupposition premises filled in:
-- these are the rules of the paper
------------------------------------------------------------------------

mk-conv-Ty-Pi : {n : Nat} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)}
  -> ConvTy G A A' -> ConvTy (extend G A) B B' -> ConvTy G (Pi A B) (Pi A' B')
mk-conv-Ty-Pi dA dB = conv-Ty-Pi (presup-l-ConvTy dA) (presup-l-ConvTy dB) dA dB

mk-conv-cong-PiCode : {n : Nat} {G : Ctx n} {a a' : Expr n} {b b' : Expr (suc n)} {l : LExpr}
  -> ConvTm G a a' (U l) -> ConvTm (extend G (El l a)) b b' (U l)
  -> ConvTm G (PiCode l a b) (PiCode l a' b') (U l)
mk-conv-cong-PiCode da db = conv-cong-PiCode (presup-l-ConvTm da) (presup-l-ConvTm db) da db

mk-conv-cong-Lam-Ty : {n : Nat} {G : Ctx n} {A A' : Expr n} {B B' b : Expr (suc n)}
  -> ConvTy G A A' -> ConvTy (extend G A) B B' -> HasType (extend G A) b B
  -> ConvTm G (Lam A B b) (Lam A' B' b) (Pi A B)
mk-conv-cong-Lam-Ty dA dB db = conv-cong-Lam-Ty (presup-l-ConvTy dA) (presup-l-ConvTy dB) dA dB db

mk-conv-cong-App-Ty : {n : Nat} {G : Ctx n} {A A' : Expr n} {B B' : Expr (suc n)}
  {c a : Expr n}
  -> ConvTy G A A' -> ConvTy (extend G A) B B' -> HasType G c (Pi A B) -> HasType G a A
  -> ConvTm G (App A B c a) (App A' B' c a) (subst1 B a)
mk-conv-cong-App-Ty dA dB dc da = conv-cong-App-Ty (presup-l-ConvTy dA) (presup-l-ConvTy dB) dA dB dc da

typing-ConvTm : {n : Nat} {G : Ctx n} {M N A : Expr n}
  -> ConvTm G M N A -> Pair (HasType G M A) (HasType G N A)
typing-ConvTm d = mkSigma (presup-l-ConvTm d) (presup-r-ConvTm d)

------------------------------------------------------------------------
-- guard η with the paper-style premises only (the typing of t in Γ,ψ
-- is recovered by constraint weakening and guard β)
------------------------------------------------------------------------

mk-conv-GLam-eta : {n : Nat} {G : Ctx n} {c : Constr} {A t : Expr n}
  -> IsType (addC G c) A -> HasType G t (Grd c A) -> ConvTm G t (GLam c A t) (Grd c A)
mk-conv-GLam-eta {G = G} {c = c} dA dt =
  conv-GLam-eta (typing-WfCtx dt) dA dt
    (ty-conv (wkC-HasType c dt) (conv-Ty-Grd-beta (Eq-transport (\ X -> ValidC X c) (Eq-sym (lctx-addC G c)) (top c)) dA))
  where
    top : {Th : LCtx} (c : Constr) -> ValidC (lcons c Th) c
    top (ceq l m) = v-hyp lhere
