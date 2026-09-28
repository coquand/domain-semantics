{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.LiftBack
--
-- Stage A of paper Theorem 4.13 (Section of erasure):
-- "context conversion across erase-equality" for all five Tarski
-- judgements.  Mirrors Rocq's `erase_inj_ctx_mutual`
-- (Equivalence.v:1148 in raphael-sterbac/Russell-Tarski-Equivalence).
--
-- Given two well-formed Tarski contexts G, G' with the SAME erasure
-- (eraseCtx G ≡ eraseCtx G'), every Tarski judgement holding in G
-- also holds in G'.  Tarski types at corresponding positions may
-- differ syntactically, as long as their erasures agree.  The proof
-- threads `type-uniq` through every constructor.
------------------------------------------------------------------------

module ERT.LiftBack where

open import ERT.Basic
import ERT.RussellSyntax  as R
import ERT.RussellTyping  as RT
import ERT.TarskiSyntax   as T
import ERT.TarskiTyping   as TT
import ERT.Erasure        as E
import ERT.TarskiMeta     as TM
open import ERT.Injectivity
open import ERT.Uniqueness
open import ERT.UniquenessTermPartial
open import ERT.EraseDeriv using (eraseCtx)


------------------------------------------------------------------------
-- Erase-equal contexts.  Both contexts are well-formed; the head
-- types at each position have the same erasure but possibly
-- different Tarski representations.  Each extension also records the
-- conversion G' ⊢ A' = A (which follows from type-uniq), so that
-- looking up a variable's type is structural in the context and does
-- not re-enter einj.
------------------------------------------------------------------------

data ConvCtx : {n : Nat} -> TT.Ctx n -> TT.Ctx n -> Set where
  conv-empty  : ConvCtx TT.empty TT.empty
  conv-extend : {n : Nat} {G G' : TT.Ctx n} {A A' : T.Expr n}
    -> ConvCtx G G'
    -> TT.IsType G  A
    -> TT.IsType G' A'
    -> Eq (E.erase A) (E.erase A')
    -> TT.ConvTy G' A' A
    -> ConvCtx (TT.extend G A) (TT.extend G' A')

-- Extension by the same type on both sides (the binder cases of einj).
conv-extend-same : {n : Nat} {G G' : TT.Ctx n} {A : T.Expr n}
  -> ConvCtx G G' -> TT.IsType G A -> TT.IsType G' A
  -> ConvCtx (TT.extend G A) (TT.extend G' A)
conv-extend-same c dA dA' = conv-extend c dA dA' refl (TT.conv-Ty-refl dA')

------------------------------------------------------------------------
-- Left / right WfCtx of a ConvCtx (we maintain WfCtx invariants
-- through the data, so we can recover them).
------------------------------------------------------------------------

convCtx-WfCtx-l : {n : Nat} {G G' : TT.Ctx n}
  -> ConvCtx G G' -> TT.WfCtx G
convCtx-WfCtx-l conv-empty                    = TT.wf-empty
convCtx-WfCtx-l (conv-extend _ dA _ _ _)      = TT.wf-extend dA

convCtx-WfCtx-r : {n : Nat} {G G' : TT.Ctx n}
  -> ConvCtx G G' -> TT.WfCtx G'
convCtx-WfCtx-r conv-empty                    = TT.wf-empty
convCtx-WfCtx-r (conv-extend _ _ dA' _ _)     = TT.wf-extend dA'

convCtx-erase : {n : Nat} {G G' : TT.Ctx n}
  -> ConvCtx G G' -> Eq (eraseCtx G) (eraseCtx G')
convCtx-erase conv-empty            = refl
convCtx-erase (conv-extend c _ _ e _) =
  Eq-cong2 RT.extend (convCtx-erase c) e

------------------------------------------------------------------------
-- ConvTy between lookup G' i and lookup G i.
------------------------------------------------------------------------

convCtx-lookup-ConvTy : {n : Nat} {G G' : TT.Ctx n}
  -> ConvCtx G G' -> (i : Fin n)
  -> TT.ConvTy G' (TT.lookup G' i) (TT.lookup G i)
convCtx-lookup-ConvTy conv-empty                     ()
convCtx-lookup-ConvTy (conv-extend _ _ dA' _ cA'A) fzero    =
  TM.wk-ConvTy dA' cA'A
convCtx-lookup-ConvTy (conv-extend c _ dA' _ _)    (fsuc j) =
  TM.wk-ConvTy dA' (convCtx-lookup-ConvTy c j)

------------------------------------------------------------------------
-- Stage A: erase-inj-ctx-{IsType,HasType,ConvTy,ConvTm}.
--
-- Mutually inductive on the Tarski derivation (structural).
------------------------------------------------------------------------

einj-IsType  : {n : Nat} {G G' : TT.Ctx n} {A : T.Expr n}
  -> ConvCtx G G' -> TT.IsType G A -> TT.IsType G' A
einj-HasType : {n : Nat} {G G' : TT.Ctx n} {M A : T.Expr n}
  -> ConvCtx G G' -> TT.HasType G M A -> TT.HasType G' M A
einj-ConvTy  : {n : Nat} {G G' : TT.Ctx n} {A B : T.Expr n}
  -> ConvCtx G G' -> TT.ConvTy G A B -> TT.ConvTy G' A B
einj-ConvTm  : {n : Nat} {G G' : TT.Ctx n} {M N A : T.Expr n}
  -> ConvCtx G G' -> TT.ConvTm G M N A -> TT.ConvTm G' M N A

------------------------------------------------------------------------
-- einj-IsType
------------------------------------------------------------------------

einj-IsType c (TT.is-Ty-U _) =
  TT.is-Ty-U (convCtx-WfCtx-r c)
einj-IsType c (TT.is-Ty-Pi dA dB) =
  let dA' = einj-IsType c dA
      cE  = conv-extend-same c dA dA'
  in TT.is-Ty-Pi dA' (einj-IsType cE dB)
einj-IsType c (TT.is-Ty-El da) =
  TT.is-Ty-El (einj-HasType c da)

------------------------------------------------------------------------
-- einj-HasType
------------------------------------------------------------------------

einj-HasType c (TT.ty-var {i = i} _) =
  TT.ty-conv (TT.ty-var (convCtx-WfCtx-r c))
             (convCtx-lookup-ConvTy c i)
einj-HasType c (TT.ty-conv dM dAB) =
  TT.ty-conv (einj-HasType c dM) (einj-ConvTy c dAB)
einj-HasType c (TT.ty-Lam dA dB db) =
  let dA' = einj-IsType c dA
      cE  = conv-extend-same c dA dA'
  in TT.ty-Lam dA' (einj-IsType cE dB) (einj-HasType cE db)
einj-HasType c (TT.ty-App dA dB dc da) =
  let dA' = einj-IsType c dA
      cE  = conv-extend-same c dA dA'
  in TT.ty-App dA' (einj-IsType cE dB)
               (einj-HasType c dc) (einj-HasType c da)
einj-HasType c (TT.ty-PiCode {l = l} da db) =
  let da' = einj-HasType c da
      dEl  = TT.is-Ty-El {l = l} da
      dEl' = TT.is-Ty-El {l = l} da'
      cE   = conv-extend-same c dEl dEl'
  in TT.ty-PiCode {l = l} da' (einj-HasType cE db)
einj-HasType c (TT.ty-UCode {m = m} {l = l} _ h) =
  TT.ty-UCode {m = m} {l = l} (convCtx-WfCtx-r c) h
einj-HasType c (TT.ty-Lift {m = m} {l = l} h da) =
  TT.ty-Lift {m = m} {l = l} h (einj-HasType c da)

------------------------------------------------------------------------
-- einj-ConvTy
------------------------------------------------------------------------

einj-ConvTy c (TT.conv-Ty-refl dA) =
  TT.conv-Ty-refl (einj-IsType c dA)
einj-ConvTy c (TT.conv-Ty-sym d) =
  TT.conv-Ty-sym (einj-ConvTy c d)
einj-ConvTy c (TT.conv-Ty-trans d1 d2) =
  TT.conv-Ty-trans (einj-ConvTy c d1) (einj-ConvTy c d2)
einj-ConvTy c (TT.conv-Ty-Pi dA-l dA dB) =
  let dA-l'  = einj-IsType c dA-l
      cE     = conv-extend-same c dA-l dA-l'
  in TT.conv-Ty-Pi dA-l' (einj-ConvTy c dA) (einj-ConvTy cE dB)
einj-ConvTy c (TT.conv-Ty-El daa') =
  TT.conv-Ty-El (einj-ConvTm c daa')
einj-ConvTy c (TT.conv-Ty-El-UCode {m = m} {l = l} _ h) =
  TT.conv-Ty-El-UCode {m = m} {l = l} (convCtx-WfCtx-r c) h
einj-ConvTy c (TT.conv-Ty-El-PiCode {l = l} da db) =
  let da'  = einj-HasType c da
      dEl  = TT.is-Ty-El {l = l} da
      dEl' = TT.is-Ty-El {l = l} da'
      cE   = conv-extend-same c dEl dEl'
  in TT.conv-Ty-El-PiCode {l = l} da' (einj-HasType cE db)
einj-ConvTy c (TT.conv-Ty-El-Lift {m = m} {l = l} h da) =
  TT.conv-Ty-El-Lift {m = m} {l = l} h (einj-HasType c da)

------------------------------------------------------------------------
-- einj-ConvTm
------------------------------------------------------------------------

einj-ConvTm c (TT.conv-refl dM) =
  TT.conv-refl (einj-HasType c dM)
einj-ConvTm c (TT.conv-sym d) =
  TT.conv-sym (einj-ConvTm c d)
einj-ConvTm c (TT.conv-trans d1 d2) =
  TT.conv-trans (einj-ConvTm c d1) (einj-ConvTm c d2)
einj-ConvTm c (TT.conv-conv dMN dAB) =
  TT.conv-conv (einj-ConvTm c dMN) (einj-ConvTy c dAB)
einj-ConvTm c (TT.conv-cong-Lam-body dA dB db) =
  let dA' = einj-IsType c dA
      cE  = conv-extend-same c dA dA'
  in TT.conv-cong-Lam-body dA' (einj-IsType cE dB) (einj-ConvTm cE db)
einj-ConvTm c (TT.conv-cong-Lam-Ty dA-l dA dB db) =
  let dA-l' = einj-IsType c dA-l
      cE    = conv-extend-same c dA-l dA-l'
  in TT.conv-cong-Lam-Ty dA-l' (einj-ConvTy c dA)
                         (einj-ConvTy cE dB)
                         (einj-HasType cE db)
einj-ConvTm c (TT.conv-cong-App-fun dA dB dc da) =
  let dA' = einj-IsType c dA
      cE  = conv-extend-same c dA dA'
  in TT.conv-cong-App-fun dA' (einj-IsType cE dB)
                          (einj-ConvTm c dc) (einj-HasType c da)
einj-ConvTm c (TT.conv-cong-App-arg dA dB dc da Bsubst-conv) =
  let dA' = einj-IsType c dA
      cE  = conv-extend-same c dA dA'
  in TT.conv-cong-App-arg dA' (einj-IsType cE dB)
                          (einj-HasType c dc) (einj-ConvTm c da)
                          (einj-ConvTy c Bsubst-conv)
einj-ConvTm c (TT.conv-cong-App-Ty dA-l dA dB dc da) =
  let dA-l' = einj-IsType c dA-l
      cE    = conv-extend-same c dA-l dA-l'
  in TT.conv-cong-App-Ty dA-l' (einj-ConvTy c dA) (einj-ConvTy cE dB)
                         (einj-HasType c dc) (einj-HasType c da)
einj-ConvTm c (TT.conv-cong-PiCode {l = l} daa-l daa' dbb') =
  let daa-l'  = einj-HasType c daa-l
      dEl     = TT.is-Ty-El {l = l} daa-l
      dEl'    = TT.is-Ty-El {l = l} daa-l'
      cE      = conv-extend-same c dEl dEl'
  in TT.conv-cong-PiCode {l = l} daa-l' (einj-ConvTm c daa')
                                 (einj-ConvTm cE dbb')
einj-ConvTm c (TT.conv-cong-Lift {m = m} {l = l} h daa') =
  TT.conv-cong-Lift {m = m} {l = l} h (einj-ConvTm c daa')
einj-ConvTm c (TT.conv-beta dA dB db da) =
  let dA' = einj-IsType c dA
      cE  = conv-extend-same c dA dA'
  in TT.conv-beta dA' (einj-IsType cE dB)
                  (einj-HasType cE db) (einj-HasType c da)
einj-ConvTm c (TT.conv-eta dA dB dc) =
  let dA' = einj-IsType c dA
      cE  = conv-extend-same c dA dA'
  in TT.conv-eta dA' (einj-IsType cE dB) (einj-HasType c dc)
einj-ConvTm c (TT.conv-Lift-Lift {nu = nu} {m = m} {l = l} hlm hmnu da) =
  TT.conv-Lift-Lift {nu = nu} {m = m} {l = l}
    hlm hmnu (einj-HasType c da)
einj-ConvTm c (TT.conv-Lift-UCode {m = m} {l = l} {nu = nu} _ hnul hlm) =
  TT.conv-Lift-UCode {m = m} {l = l} {nu = nu}
    (convCtx-WfCtx-r c) hnul hlm
einj-ConvTm c (TT.conv-Lift-PiCode {m = m} {l = l} h da db) =
  let da'  = einj-HasType c da
      dEl  = TT.is-Ty-El {l = l} da
      dEl' = TT.is-Ty-El {l = l} da'
      cE   = conv-extend-same c dEl dEl'
  in TT.conv-Lift-PiCode {m = m} {l = l} h da'
       (einj-HasType cE db)

------------------------------------------------------------------------
-- Stage B helpers
--
-- These are used by Equivalence.agda to prove the four lift-*
-- statements.  They live here (rather than in Equivalence.agda) so
-- the einj-* lemmas are in scope.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Tarski HasType-presupposition: every type appearing as the RHS of
-- HasType is itself an IsType.  This is by induction on the HasType
-- derivation; each Tarski typing rule produces a type that is
-- demonstrably IsType.
------------------------------------------------------------------------

typing-IsType : {n : Nat} {G : TT.Ctx n} {M A : T.Expr n}
  -> TT.HasType G M A -> TT.IsType G A
typing-IsType (TT.ty-var {i = i} dG) =
  TM.wfCtx-lookup dG i
typing-IsType (TT.ty-conv _ dAB) =
  TM.presup-r-ConvTy dAB
typing-IsType (TT.ty-Lam dA dB _) =
  TT.is-Ty-Pi dA dB
typing-IsType (TT.ty-App dA dB _ da) =
  TM.subst-IsType (TM.subst1-WtSub dA da) (TM.isType-WfCtx dA) dB
typing-IsType (TT.ty-PiCode {l = l} da _) =
  TT.is-Ty-U {l = l} (TM.typing-WfCtx da)
typing-IsType (TT.ty-UCode {m = m} dG _) =
  TT.is-Ty-U {l = m} dG
typing-IsType (TT.ty-Lift {m = m} _ da) =
  TT.is-Ty-U {l = m} (TM.typing-WfCtx da)

------------------------------------------------------------------------
-- Build a ConvCtx between two well-formed contexts with the same
-- erasure.  Mirrors Rocq's `conv_ctx_from_erase`.
------------------------------------------------------------------------

R-extend-inj : {n : Nat} {G G' : RT.Ctx n} {A A' : R.Expr n}
  -> Eq (RT.extend G A) (RT.extend G' A')
  -> Pair (Eq G G') (Eq A A')
R-extend-inj refl = mkSigma refl refl

mkConvCtx-from-erase : {n : Nat} (G G' : TT.Ctx n)
  -> TT.WfCtx G -> TT.WfCtx G'
  -> Eq (eraseCtx G) (eraseCtx G')
  -> ConvCtx G G'
mkConvCtx-from-erase TT.empty TT.empty _ _ _ = conv-empty
mkConvCtx-from-erase (TT.extend G A) (TT.extend G' A')
                     (TT.wf-extend dA) (TT.wf-extend dA') eq =
  let mkSigma eqG eqA = R-extend-inj eq
      cinner = mkConvCtx-from-erase G G'
                 (TM.isType-WfCtx dA) (TM.isType-WfCtx dA') eqG
      cA'A   = type-uniq dA' (einj-IsType cinner dA) (Eq-sym eqA)
  in conv-extend cinner dA dA' eqA cA'A

------------------------------------------------------------------------
-- Given HasType G M A with erase A ≡ R.U l, coerce to HasType G M (T.U l)
-- using type-uniq.  This is the workhorse for assembling Tarski
-- universe-typed derivations from arbitrary lifts.
------------------------------------------------------------------------

coerce-to-U : {n : Nat} {G : TT.Ctx n} {M A : T.Expr n} {l : Nat}
  -> TT.HasType G M A -> Eq (E.erase A) (R.U l)
  -> TT.HasType G M (T.U l)
coerce-to-U {l = l} der eq =
  let dA  = typing-IsType der
      dUl = TT.is-Ty-U {l = l} (TM.isType-WfCtx dA)
      c   = type-uniq dA dUl eq
  in TT.ty-conv der c

------------------------------------------------------------------------
-- Given ConvTm G M N A with erase A ≡ R.U l, coerce to
-- ConvTm G M N (T.U l) similarly.
------------------------------------------------------------------------

coerce-ConvTm-to-U : {n : Nat} {G : TT.Ctx n} {M N A : T.Expr n} {l : Nat}
  -> TT.ConvTm G M N A -> Eq (E.erase A) (R.U l)
  -> TT.ConvTm G M N (T.U l)
coerce-ConvTm-to-U {l = l} d eq =
  let dA  = typing-IsType (TM.presup-l-ConvTm d)
      dUl = TT.is-Ty-U {l = l} (TM.isType-WfCtx dA)
      c   = type-uniq dA dUl eq
  in TT.conv-conv d c

------------------------------------------------------------------------
-- Given IsType G A with erase A ≡ R.U l, coerce to ConvTy G A (T.U l).
------------------------------------------------------------------------

coerce-IsType-to-U : {n : Nat} {G : TT.Ctx n} {A : T.Expr n} {l : Nat}
  -> TT.IsType G A -> Eq (E.erase A) (R.U l)
  -> TT.ConvTy G A (T.U l)
coerce-IsType-to-U {l = l} dA eq =
  let dUl = TT.is-Ty-U {l = l} (TM.isType-WfCtx dA)
  in type-uniq dA dUl eq

------------------------------------------------------------------------
-- Generic "move" helpers: translate a Tarski derivation from one
-- context to another with the same erasure.
------------------------------------------------------------------------

move-IsType : {n : Nat} (G_src G_tgt : TT.Ctx n) {A : T.Expr n}
  -> TT.WfCtx G_tgt
  -> Eq (eraseCtx G_src) (eraseCtx G_tgt)
  -> TT.IsType G_src A -> TT.IsType G_tgt A
move-IsType G_src G_tgt wf_tgt eq d =
  einj-IsType
    (mkConvCtx-from-erase G_src G_tgt (TM.isType-WfCtx d) wf_tgt eq) d

move-HasType : {n : Nat} (G_src G_tgt : TT.Ctx n) {M A : T.Expr n}
  -> TT.WfCtx G_tgt
  -> Eq (eraseCtx G_src) (eraseCtx G_tgt)
  -> TT.HasType G_src M A -> TT.HasType G_tgt M A
move-HasType G_src G_tgt wf_tgt eq d =
  einj-HasType
    (mkConvCtx-from-erase G_src G_tgt (TM.typing-WfCtx d) wf_tgt eq) d

move-ConvTy : {n : Nat} (G_src G_tgt : TT.Ctx n) {A B : T.Expr n}
  -> TT.WfCtx G_tgt
  -> Eq (eraseCtx G_src) (eraseCtx G_tgt)
  -> TT.ConvTy G_src A B -> TT.ConvTy G_tgt A B
move-ConvTy G_src G_tgt wf_tgt eq d =
  einj-ConvTy
    (mkConvCtx-from-erase G_src G_tgt
       (TM.isType-WfCtx (TM.presup-l-ConvTy d)) wf_tgt eq) d

move-ConvTm : {n : Nat} (G_src G_tgt : TT.Ctx n) {M N A : T.Expr n}
  -> TT.WfCtx G_tgt
  -> Eq (eraseCtx G_src) (eraseCtx G_tgt)
  -> TT.ConvTm G_src M N A -> TT.ConvTm G_tgt M N A
move-ConvTm G_src G_tgt wf_tgt eq d =
  einj-ConvTm
    (mkConvCtx-from-erase G_src G_tgt
       (TM.typing-WfCtx (TM.presup-l-ConvTm d)) wf_tgt eq) d

------------------------------------------------------------------------
-- Coerce a HasType to a target type, given a proof that the
-- erasures coincide.
------------------------------------------------------------------------

coerce-HasType-to : {n : Nat} {G : TT.Ctx n} {M A B : T.Expr n}
  -> TT.HasType G M A -> TT.IsType G B
  -> Eq (E.erase A) (E.erase B)
  -> TT.HasType G M B
coerce-HasType-to dM dB eq =
  TT.ty-conv dM (type-uniq (typing-IsType dM) dB eq)

coerce-ConvTm-to : {n : Nat} {G : TT.Ctx n} {M N A B : T.Expr n}
  -> TT.ConvTm G M N A -> TT.IsType G B
  -> Eq (E.erase A) (E.erase B)
  -> TT.ConvTm G M N B
coerce-ConvTm-to dMN dB eq =
  TT.conv-conv dMN
    (type-uniq (typing-IsType (TM.presup-l-ConvTm dMN)) dB eq)

------------------------------------------------------------------------
-- Bridge two ConvTys ConvTy G A B and ConvTy G C D where B and C
-- both erase to the same thing, into ConvTy G A D.
------------------------------------------------------------------------

bridge-ConvTy : {n : Nat} {G : TT.Ctx n} {A B C D : T.Expr n}
  -> TT.ConvTy G A B -> TT.ConvTy G C D
  -> Eq (E.erase B) (E.erase C)
  -> TT.ConvTy G A D
bridge-ConvTy dAB dCD eq =
  let dB = TM.presup-r-ConvTy dAB
      dC = TM.presup-l-ConvTy dCD
      bridge = type-uniq dB dC eq
  in TT.conv-Ty-trans dAB (TT.conv-Ty-trans bridge dCD)
