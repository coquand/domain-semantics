{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.TarskiMetaCong  (T_T version of BCDE4.RussellMetaCong)
--
-- Cross-substitution congruence for the Tarski theory:
--
--   subst1-cong-Ty : ConvTm G a a' A
--                 -> IsType G A
--                 -> IsType (extend G A) B
--                 -> ConvTy G (subst1 B a) (subst1 B a')
--
-- Provides the missing premise for `conv-cong-App-arg` when the
-- ConvTm-witness for `a ≡ a'` is given but the cross-substitution
-- equality of the result type is not.
--
-- Strategy: parameterise by a pointwise convertibility witness
--
--   ConvTmSub H G s s' = (i : Fin g) ->
--                          ConvTm H (s i) (s' i) (substExpr s (lookup G i))
--
-- and prove the standard mutual `subst-cong-{IsType,HasType,ConvTy,ConvTm}`
-- lemmas.  Specialise at the end with s = subst1Sub a, s' = subst1Sub a'.
------------------------------------------------------------------------

module BCDE4.TarskiMetaCong where

open import BCDE4.Basic
open import BCDE4.TarskiSyntax
open import BCDE4.TarskiTyping
open import BCDE4.TarskiMeta
open import BCDE4.Levels
open import BCDE4.TarskiRelevel
open import BCDE4.TarskiLsub

------------------------------------------------------------------------
-- Pointwise-convertibility substitution
------------------------------------------------------------------------

ConvTmSubTy : {h g : Nat} -> Ctx h -> Ctx g -> Sub h g -> Sub h g -> Set
ConvTmSubTy H G s s' =
  (i : Fin _) -> ConvTm H (s i) (s' i) (substExpr s (lookup G i))

record ConvTmSub {h g : Nat} (H : Ctx h) (G : Ctx g) (s s' : Sub h g) : Set where
  constructor mkCS
  field
    csE : CEnt H G
    csT : ConvTmSubTy H G s s'
open ConvTmSub public

csL : {h g : Nat} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} -> ConvTmSub H G s s' -> WtSub H G s
csL cs = mkWt (csE cs) (\ i -> presup-l-ConvTm (csT cs i))

ConvTmSub-addL : {h g : Nat} {H : Ctx h} {G : Ctx g} {s s' : Sub h g}
  -> ConvTmSub H G s s' -> ConvTmSub (addL H) (addL G) (\ i -> lshiftE (s i)) (\ i -> lshiftE (s' i))
ConvTmSub-addL {H = H} {G = G} {s = s} {s' = s'} cs =
  mkCS (ent-addL G H (csE cs))
       (\ i -> Eq-transport (\ T -> ConvTm (addL H) (lshiftE (s i)) (lshiftE (s' i)) T)
                  (Eq-trans (Eq-sym (subst-lshift s (lookup G i)))
                            (Eq-cong (substExpr (\ j -> lshiftE (s j))) (Eq-sym (lookup-addL G i))))
                  (lsub-ConvTm (lsk-shift H) (lok-shift H) (csT cs i)))

ConvTmSub-addC : {h g : Nat} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} (c : Constr)
  -> ConvTmSub H G s s' -> ConvTmSub (addC H c) (addC G c) s s'
ConvTmSub-addC {H = H} {G = G} {s = s} {s' = s'} c cs =
  mkCS (ent-addC G H c (csE cs))
       (\ i -> Eq-transport (\ T -> ConvTm (addC H c) (s i) (s' i) (substExpr s T))
                  (Eq-sym (lookup-addC G c i)) (wkC-ConvTm c (csT cs i)))

-- Project the "left" WtSub from a ConvTmSub.  Inlined at call sites
-- as `(csL cs)` to avoid implicit-G inference issues.

------------------------------------------------------------------------
-- Lifting a ConvTmSub through a binder
------------------------------------------------------------------------

liftSub-ConvTmSub :
  {h g : Nat} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {A : Expr g}
  -> ConvTmSub H G s s' -> WfCtx H -> IsType G A
  -> ConvTmSub (extend H (substExpr s A)) (extend G A) (liftSub s) (liftSub s')

liftSub-ConvTmSubTy :
  {h g : Nat} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {A : Expr g}
  -> ConvTmSub H G s s' -> WfCtx H -> IsType G A
  -> ConvTmSubTy (extend H (substExpr s A)) (extend G A) (liftSub s) (liftSub s')
liftSub-ConvTmSubTy {s = s} {A = A} cs wfH dA fzero =
  let sA-IT  = subst-IsType (csL cs) wfH dA
      wfH'   = wf-extend sA-IT
      eq     = Eq-trans (subst-ren (liftSub s) wkRen A)
                 (Eq-sym (ren-subst wkRen s A))
  in Eq-transport
       (\ T -> ConvTm (extend _ (substExpr s A))
                      (Var fzero) (Var fzero) T)
       (Eq-sym eq)
       (conv-refl (ty-var wfH'))
liftSub-ConvTmSubTy {H = H} {G = G} {s = s} {s' = s'} {A = A} cs wfH dA (fsuc i) =
  let sA-IT = subst-IsType (csL cs) wfH dA
      ih    = csT cs i
      ih-wk = wk-ConvTm sA-IT ih
      eq    = Eq-trans (subst-ren (liftSub s) wkRen (lookup G i))
                       (Eq-sym (ren-subst wkRen s (lookup G i)))
  in Eq-transport
       (\ T -> ConvTm (extend H (substExpr s A))
                      (wkExpr (s i)) (wkExpr (s' i)) T)
       (Eq-sym eq)
       ih-wk

liftSub-ConvTmSub cs wfH dA = mkCS (csE cs) (liftSub-ConvTmSubTy cs wfH dA)

------------------------------------------------------------------------
-- Extending a substitution by one term, and the ConvTmSub which
-- varies only that term.  Used in the App case so that the
-- cross-substitution congruence recurses on the original derivation
-- of B, not on its substituted instance.
------------------------------------------------------------------------

consSub : {h g : Nat} -> Sub h g -> Expr h -> Sub h (suc g)
consSub s x fzero    = x
consSub s x (fsuc i) = s i

consSub-wk : {h g : Nat} (s : Sub h g) (x : Expr h) (e : Expr g)
  -> Eq (substExpr (consSub s x) (wkExpr e)) (substExpr s e)
consSub-wk s x e =
  Eq-trans (subst-ren (consSub s x) wkRen e)
           (substExpr-ext _ s (\ i -> refl) e)

consSub-subst1 : {h g : Nat} (s : Sub h g) (x : Expr h) (B : Expr (suc g))
  -> Eq (substExpr (consSub s x) B) (subst1 (substExpr (liftSub s) B) x)
consSub-subst1 s x B =
  Eq-sym (Eq-trans (subst-subst (subst1Sub x) (liftSub s) B)
                   (substExpr-ext _ (consSub s x) pt B))
  where
    pt : (i : Fin _) -> Eq (substExpr (subst1Sub x) (liftSub s i))
                           (consSub s x i)
    pt fzero    = refl
    pt (fsuc i) = subst1-wk (s i) x

consSub-ConvTmSub :
  {h g : Nat} {H : Ctx h} {G : Ctx g} {s : Sub h g} {A : Expr g}
  {x x' : Expr h}
  -> WtSub H G s
  -> ConvTm H x x' (substExpr s A)
  -> ConvTmSub H (extend G A) (consSub s x) (consSub s x')

consSub-ConvTmSubTy :
  {h g : Nat} {H : Ctx h} {G : Ctx g} {s : Sub h g} {A : Expr g}
  {x x' : Expr h}
  -> WtSub H G s
  -> ConvTm H x x' (substExpr s A)
  -> ConvTmSubTy H (extend G A) (consSub s x) (consSub s x')
consSub-ConvTmSubTy {s = s} {A = A} {x = x} ws cx fzero =
  Eq-transport (\ T -> ConvTm _ x _ T) (Eq-sym (consSub-wk s x A)) cx
consSub-ConvTmSubTy {G = G} {s = s} {x = x} ws cx (fsuc i) =
  Eq-transport (\ T -> ConvTm _ (s i) (s i) T)
    (Eq-sym (consSub-wk s x (lookup G i))) (conv-refl (wtT ws i))

consSub-ConvTmSub ws cx = mkCS (wtE ws) (consSub-ConvTmSubTy ws cx)

------------------------------------------------------------------------
-- The mutual congruence block
------------------------------------------------------------------------

mutual

  ----------------------------------------------------------------------
  -- IsType cases
  ----------------------------------------------------------------------
  subst-cong-IsType :
    {h g : Nat} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {A : Expr g}
    -> ConvTmSub H G s s' -> WfCtx H
    -> IsType G A
    -> ConvTy H (substExpr s A) (substExpr s' A)
  subst-cong-IsType cs wfH (is-U _) = conv-Ty-refl (is-U wfH)
  subst-cong-IsType cs wfH (is-El d) =
    conv-Ty-El (subst-cong-HasType cs wfH d)
  subst-cong-IsType cs wfH (is-Emp _) = conv-Ty-refl (is-Emp wfH)
  subst-cong-IsType cs wfH (is-Pi dA dB) =
    let sA = subst-IsType (csL cs) wfH dA
        w' = wf-extend sA
    in conv-Ty-Pi sA (subst-IsType (liftSub-WtSub (csL cs) wfH dA) w' dB)
         (subst-cong-IsType cs wfH dA) (subst-cong-IsType (liftSub-ConvTmSub cs wfH dA) w' dB)
  subst-cong-IsType cs wfH (is-Grd {c = c} dG dA) =
    let cs' = ConvTmSub-addC c cs
        wf' = wkC-WfCtx c wfH
    in conv-Ty-Grd wfH (subst-IsType (csL cs') wf' dA) (subst-cong-IsType cs' wf' dA)
  subst-cong-IsType cs wfH (is-LPi dG dA) =
    let cs' = ConvTmSub-addL cs
        wf' = wkL-WfCtx wfH
    in conv-Ty-LPi wfH (subst-IsType (csL cs') wf' dA) (subst-cong-IsType cs' wf' dA)

  ----------------------------------------------------------------------
  -- HasType cases (produce ConvTm at substExpr s A)
  ----------------------------------------------------------------------
  subst-cong-HasType :
    {h g : Nat} {H : Ctx h} {G : Ctx g} {s s' : Sub h g} {M A : Expr g}
    -> ConvTmSub H G s s' -> WfCtx H
    -> HasType G M A
    -> ConvTm H (substExpr s M) (substExpr s' M) (substExpr s A)
  subst-cong-HasType cs wfH (ty-var {i = i} _) = csT cs i
  subst-cong-HasType cs wfH (ty-GLam {c = c} dG dA dt) =
    let cs' = ConvTmSub-addC c cs
        wf' = wkC-WfCtx c wfH
        ct  = subst-cong-HasType cs' wf' dt
    in conv-trans (conv-cong-GLam wfH (subst-IsType (csL cs') wf' dA) (subst-HasType (csL cs') wf' dt) ct)
                  (conv-cong-GLam-Ty wfH (subst-IsType (csL cs') wf' dA) (subst-cong-IsType cs' wf' dA)
                     (presup-r-ConvTm ct))
  subst-cong-HasType cs wfH (ty-LLam dG dA du) =
    let cs' = ConvTmSub-addL cs
        wf' = wkL-WfCtx wfH
        cu  = subst-cong-HasType cs' wf' du
    in conv-trans (conv-cong-LLam wfH (subst-IsType (csL cs') wf' dA) (subst-HasType (csL cs') wf' du) cu)
                  (conv-cong-LLam-Ty wfH (subst-IsType (csL cs') wf' dA) (subst-cong-IsType cs' wf' dA)
                     (presup-r-ConvTm cu))
  subst-cong-HasType {H = H} {s = s} {s' = s'} cs wfH (ty-LApp {A = A} {t = t} {l = l} dA dt) =
    let cs' = ConvTmSub-addL cs
        wf' = wkL-WfCtx wfH
        ct  = subst-cong-HasType cs wfH dt
    in Eq-transport (\ T -> ConvTm H (LApp (substExpr (\ i -> lshiftE (s i)) A) (substExpr s t) l)
                                     (LApp (substExpr (\ i -> lshiftE (s' i)) A) (substExpr s' t) l) T)
         (Eq-sym (subst-lsub1 s A l))
         (conv-trans (conv-cong-LApp-fun (subst-IsType (csL cs') wf' dA) ct)
                     (conv-cong-LApp-Ty (subst-IsType (csL cs') wf' dA) (subst-cong-IsType cs' wf' dA)
                        (presup-r-ConvTm ct)))
  subst-cong-HasType cs wfH (ty-collapse lp dA) =
    conv-refl (ty-collapse (loop-ent (csE cs) lp) (subst-IsType (csL cs) wfH dA))
  subst-cong-HasType cs wfH (ty-conv dM dAB) =
    conv-conv (subst-cong-HasType cs wfH dM)
              (subst-ConvTy (csL cs) wfH dAB)
  subst-cong-HasType cs wfH (ty-Lam dA dB db) =
    let sA-IT = subst-IsType (csL cs) wfH dA
        wfH'  = wf-extend sA-IT
        cs'   = liftSub-ConvTmSub cs wfH dA
        cA    = subst-cong-IsType cs wfH dA
        cB    = subst-cong-IsType cs' wfH' dB
        cb    = subst-cong-HasType cs' wfH' db
        sB    = subst-IsType (liftSub-WtSub (csL cs) wfH dA) wfH' dB
        sb-r  = presup-r-ConvTm cb
        step1 = conv-cong-Lam-body sA-IT sB (presup-l-ConvTm cb) cb
        step2 = conv-cong-Lam-Ty sA-IT sB cA cB sb-r
    in conv-trans step1 step2
  subst-cong-HasType {H = H} {s = s} {s' = s'} cs wfH
                     (ty-App {A = A} {B = B} {c = c} {a = a}
                              dA dB dc da) =
    let sA-IT = subst-IsType (csL cs) wfH dA
        wfH'  = wf-extend sA-IT
        cs'   = liftSub-ConvTmSub cs wfH dA
        cA    = subst-cong-IsType cs wfH dA
        cB    = subst-cong-IsType cs' wfH' dB
        cc    = subst-cong-HasType cs wfH dc
        ca    = subst-cong-HasType cs wfH da
        sB    = subst-IsType (liftSub-WtSub (csL cs) wfH dA) wfH' dB
        sa-l  = subst-HasType (csL cs) wfH da
        sc-r  = presup-r-ConvTm cc        -- HasType H (s' c) (Pi sA sB)
        sa-r  = presup-r-ConvTm ca        -- HasType H (s' a) sA
        step1 = conv-cong-App-fun sA-IT sB cc sa-l
        BsubstCong =
          Eq-transport (\ T -> ConvTy H T (subst1 (substExpr (liftSub s) B)
                                                  (substExpr s' a)))
            (consSub-subst1 s (substExpr s a) B)
            (Eq-transport (ConvTy H (substExpr (consSub s (substExpr s a)) B))
              (consSub-subst1 s (substExpr s' a) B)
              (subst-cong-IsType
                (consSub-ConvTmSub (csL cs) ca)
                wfH dB))
        step2 = conv-cong-App-arg sA-IT sB sc-r ca BsubstCong
        step3raw = conv-cong-App-Ty sA-IT sB cA cB sc-r sa-r
        step3  = conv-conv step3raw (conv-Ty-sym BsubstCong)
        composite = conv-trans step1 (conv-trans step2 step3)
        appL = App (substExpr s A) (substExpr (liftSub s) B)
                   (substExpr s c) (substExpr s a)
        appR = App (substExpr s' A) (substExpr (liftSub s') B)
                   (substExpr s' c) (substExpr s' a)
    in Eq-transport (\ T -> ConvTm H appL appR T)
         (Eq-sym (subst-subst1 s B a))
         composite
  subst-cong-HasType cs wfH (ty-PiCode da db) =
    let ca    = subst-cong-HasType cs wfH da
        sa    = subst-HasType (csL cs) wfH da
        wfH'  = wf-extend (is-El sa)
        cs'   = liftSub-ConvTmSub cs wfH (is-El da)
        cb    = subst-cong-HasType cs' wfH' db
    in conv-cong-PiCode sa (presup-l-ConvTm cb) ca cb
  subst-cong-HasType cs wfH (ty-UCode _ v) =
    conv-refl (ty-UCode wfH (valid-ent (csE cs) v))
  subst-cong-HasType cs wfH (ty-Lift v da) =
    conv-cong-Lift (valid-ent (csE cs) v) (subst-cong-HasType cs wfH da)
  subst-cong-HasType cs wfH (ty-EmpCode _) = conv-refl (ty-EmpCode wfH)

------------------------------------------------------------------------
-- The wrapper we actually need
------------------------------------------------------------------------

subst1-cong-Ty :
  {n : Nat} {G : Ctx n} {a a' : Expr n} {A : Expr n} {B : Expr (suc n)}
  -> ConvTm G a a' A
  -> IsType G A
  -> IsType (extend G A) B
  -> ConvTy G (subst1 B a) (subst1 B a')
subst1-cong-Ty {G = G} {a = a} {a' = a'} {A = A} {B = B} caa' dA dB =
  subst-cong-IsType (mkCS ent-refl (cs caa')) (isType-WfCtx dA) dB
  where
    dG : WfCtx G
    dG = isType-WfCtx dA
    cs : ConvTm G a a' A
       -> ConvTmSubTy G (extend G A) (subst1Sub a) (subst1Sub a')
    cs caa'' fzero    =
      Eq-transport (\ T -> ConvTm G a a' T)
        (Eq-sym (subst1-wk A a))
        caa''
    cs caa'' (fsuc i) =
      Eq-transport (\ T -> ConvTm G (Var i) (Var i) T)
        (Eq-sym (subst1-wk (lookup G i) a))
        (conv-refl (ty-var dG))
