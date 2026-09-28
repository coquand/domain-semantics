{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.UniquenessTermPartial
--
-- Total proof of `term-uniq` (paper Lemma 4.10, "catch-up" lemma).
--
-- Discharged cases:
--   * ty-conv peeling on either side
--   * (Var, Var)
--   * (Lam, Lam)              -- recurses on body
--   * (App, App)              -- uses subst1-cong-Ty for cross-subst
--   * (PiCode, PiCode)        -- uses PiCode-inj-T (same-level branch)
--                                and three-way comparison ka vs kb
--                                (CommonLift branch, paper §4.2)
--   * cross-shape impossible cases (Var-vs-Lam, etc.)
--   * (UCode, UCode)          -- direct CommonLift via canonical
--                                witness UCode (suc l) l : U (suc l)
--   * (Lift, *)               -- recurse on inner of left Lift,
--                                build CommonLift via Lift-cong
--                                and conv-Lift-Lift
--   * (*, Lift)               -- symmetric to (Lift, *)
--
-- The (PiCode, PiCode) inr-branch (paper Lemma 4.10 "Code for a
-- universe" generalised to dependent product) is handled by a
-- three-way case split on the inner-`a` common base level (ka) vs
-- the body common base level (kb), mirroring the Rocq formalisation
-- (raphael-sterbac/Russell-Tarski-Equivalence, `erase_cprod_inv`).
-- The level-alignment uses the strict-Lift versions of the Tarski
-- equations (4) Lift-Lift, (6) Lift-PiCode.
--
-- No postulates.  U-inj-Ty-T comes from ERT.Injectivity.
------------------------------------------------------------------------

module ERT.UniquenessTermPartial where

open import ERT.Basic
import ERT.RussellSyntax  as R
import ERT.TarskiSyntax   as T
import ERT.TarskiTyping   as TT
import ERT.Erasure        as E
import ERT.TarskiMeta     as TM
import ERT.TarskiMetaCong as TMC
open import ERT.Injectivity
open import ERT.Uniqueness

------------------------------------------------------------------------
-- Lt-trans helper (Lt is Le ∘ suc; transitivity by chaining)
------------------------------------------------------------------------

Lt-trans-Lt : {a b c : Nat} -> Lt a b -> Lt b c -> Lt a c
Lt-trans-Lt {a = a} {b = b} {c = c} h1 h2 =
  Le-trans (suc a) (suc b) c
    (Le-trans (suc a) b (suc b) h1 (Le-suc b b (Le-refl b))) h2

------------------------------------------------------------------------
-- Lt is anti-reflexive
------------------------------------------------------------------------

Lt-not-self : (n : Nat) -> Lt n n -> Empty
Lt-not-self zero    ()
Lt-not-self (suc n) h = Lt-not-self n h

------------------------------------------------------------------------
-- Three-way comparison on naturals
------------------------------------------------------------------------

Nat-trichotomy : (a b : Nat) -> Either (Lt a b) (Either (Eq a b) (Lt b a))
Nat-trichotomy zero    zero    = inr (inl refl)
Nat-trichotomy zero    (suc b) = inl tt
Nat-trichotomy (suc a) zero    = inr (inr tt)
Nat-trichotomy (suc a) (suc b) with Nat-trichotomy a b
... | inl h           = inl h
... | inr (inl refl)  = inr (inl refl)
... | inr (inr h)     = inr (inr h)

------------------------------------------------------------------------
-- Build ConvTy G (El l a) (El k v) from a LiftStep G a l k v (U l).
-- Used to bring two well-typed contexts (extend G (El l_i a_i)) into
-- the common context (extend G (El k v)) when (l_i, a_i) and (k, v)
-- are related by a LiftStep.
------------------------------------------------------------------------

build-eqEl :
  {n : Nat} {G : TT.Ctx n} {a v : T.Expr n} {l k : Nat}
  -> TT.HasType G a (T.U l)
  -> TT.HasType G v (T.U k)
  -> LiftStep G a l k v (T.U l)
  -> TT.ConvTy G (T.El l a) (T.El k v)
build-eqEl {l = l} {k = k} _ _ (trivial e ctm) =
  -- e : Eq l k, ctm : ConvTm G a v (U l).
  -- conv-Ty-El gives (El l a) ≡ (El l v).
  -- Eq-transport with e rewrites l ↦ k in the right factor.
  Eq-transport (\ kk -> TT.ConvTy _ (T.El l _) (T.El kk _)) e
    (TT.conv-Ty-El {l = l} ctm)
build-eqEl {l = l} {k = k} _ dv (proper h ctm) =
  -- h : Lt k l, ctm : ConvTm G a (Lift l k v) (U l).
  -- conv-Ty-El : (El l a) ≡ (El l (Lift l k v))
  -- conv-Ty-El-Lift : (El l (Lift l k v)) ≡ (El k v)
  TT.conv-Ty-trans (TT.conv-Ty-El {l = l} ctm)
                    (TT.conv-Ty-El-Lift {m = l} {l = k} h dv)

------------------------------------------------------------------------
-- Move a LiftStep across a context conversion at the binder.
------------------------------------------------------------------------

liftStep-conv-ctx :
  {n : Nat} {G : TT.Ctx n} {A A' : T.Expr n}
  {u v B : T.Expr (suc n)} {m k : Nat}
  -> TT.IsType G A -> TT.IsType G A' -> TT.ConvTy G A A'
  -> LiftStep (TT.extend G A) u m k v B
  -> LiftStep (TT.extend G A') u m k v B
liftStep-conv-ctx dA dA' AA' (trivial e tm) =
  trivial e (TM.ctx-conv-ConvTm dA dA' AA' tm)
liftStep-conv-ctx dA dA' AA' (proper h tm) =
  proper h (TM.ctx-conv-ConvTm dA dA' AA' tm)

------------------------------------------------------------------------
-- Algebraic identity, ka < kb < m case:
--
--   Lift m kb (PiCode kb (Lift kb ka va) vb)
--     ≡  PiCode m (Lift m ka va) (Lift m kb vb)  : U m
--
-- Combines rule (6) Lift-PiCode and rule (4) Lift-Lift, plus
-- conv-cong-PiCode on the first argument.
------------------------------------------------------------------------

Lift-Lift-PiCode-fwd :
  {n : Nat} {G : TT.Ctx n} {ka kb m : Nat}
  {va : T.Expr n} {vb : T.Expr (suc n)}
  -> Lt ka kb -> Lt kb m
  -> TT.HasType G va (T.U ka)
  -> TT.HasType (TT.extend G (T.El ka va)) vb (T.U kb)
  -> TT.ConvTm G (T.Lift m kb (T.PiCode kb (T.Lift kb ka va) vb))
                  (T.PiCode m (T.Lift m ka va) (T.Lift m kb vb))
                  (T.U m)
Lift-Lift-PiCode-fwd {ka = ka} {kb = kb} {m = m} {va = va} {vb = vb}
                     ka<kb kb<m va-ty vb-ty =
  let Lift-typed : TT.HasType _ (T.Lift kb ka va) (T.U kb)
      Lift-typed = TT.ty-Lift {m = kb} {l = ka} ka<kb va-ty
      ElEq-kb : TT.ConvTy _ (T.El kb (T.Lift kb ka va)) (T.El ka va)
      ElEq-kb = TT.conv-Ty-El-Lift {m = kb} {l = ka} ka<kb va-ty
      vb-in-Lift : TT.HasType (TT.extend _ (T.El kb (T.Lift kb ka va))) vb (T.U kb)
      vb-in-Lift = TM.ctx-conv-HasType
                     (TT.is-Ty-El {l = ka} va-ty)
                     (TT.is-Ty-El {l = kb} Lift-typed)
                     (TT.conv-Ty-sym ElEq-kb) vb-ty
      step-a = TT.conv-Lift-PiCode {m = m} {l = kb} kb<m Lift-typed vb-in-Lift
      ll-conv = TT.conv-Lift-Lift {nu = m} {m = kb} {l = ka} ka<kb kb<m va-ty
      LiftLift-typed : TT.HasType _ (T.Lift m kb (T.Lift kb ka va)) (T.U m)
      LiftLift-typed = TT.ty-Lift {m = m} {l = kb} kb<m Lift-typed
      ElEq-m : TT.ConvTy _ (T.El m (T.Lift m kb (T.Lift kb ka va))) (T.El ka va)
      ElEq-m = TT.conv-Ty-trans
                 (TT.conv-Ty-El-Lift {m = m} {l = kb} kb<m Lift-typed)
                 ElEq-kb
      vb-in-LL : TT.HasType (TT.extend _ (T.El m (T.Lift m kb (T.Lift kb ka va))))
                             vb (T.U kb)
      vb-in-LL = TM.ctx-conv-HasType (TT.is-Ty-El {l = ka} va-ty)
                                       (TT.is-Ty-El {l = m} LiftLift-typed)
                                       (TT.conv-Ty-sym ElEq-m) vb-ty
      Lift-vb-LL = TT.ty-Lift {m = m} {l = kb} kb<m vb-in-LL
      body-refl = TT.conv-refl Lift-vb-LL
      step-b = TM.mk-conv-cong-PiCode {l = m} ll-conv body-refl
  in TT.conv-trans step-a step-b

------------------------------------------------------------------------
-- Algebraic identity, kb < ka < m case:
--
--   Lift m ka (PiCode ka va (Lift ka kb vb))
--     ≡  PiCode m (Lift m ka va) (Lift m kb vb)  : U m
--
-- Combines rule (6) Lift-PiCode and rule (4) Lift-Lift in the body,
-- plus conv-cong-PiCode.
------------------------------------------------------------------------

Lift-Lift-PiCode-bwd :
  {n : Nat} {G : TT.Ctx n} {ka kb m : Nat}
  {va : T.Expr n} {vb : T.Expr (suc n)}
  -> Lt kb ka -> Lt ka m
  -> TT.HasType G va (T.U ka)
  -> TT.HasType (TT.extend G (T.El ka va)) vb (T.U kb)
  -> TT.ConvTm G (T.Lift m ka (T.PiCode ka va (T.Lift ka kb vb)))
                  (T.PiCode m (T.Lift m ka va) (T.Lift m kb vb))
                  (T.U m)
Lift-Lift-PiCode-bwd {ka = ka} {kb = kb} {m = m} {va = va} {vb = vb}
                     kb<ka ka<m va-ty vb-ty =
  let Lift-vb : TT.HasType _ (T.Lift ka kb vb) (T.U ka)
      Lift-vb = TT.ty-Lift {m = ka} {l = kb} kb<ka vb-ty
      step-a = TT.conv-Lift-PiCode {m = m} {l = ka} ka<m va-ty Lift-vb
      -- Move vb to extend G (El m (Lift m ka va)) to apply conv-Lift-Lift there
      Lift-va-typed : TT.HasType _ (T.Lift m ka va) (T.U m)
      Lift-va-typed = TT.ty-Lift {m = m} {l = ka} ka<m va-ty
      ElEq-m : TT.ConvTy _ (T.El m (T.Lift m ka va)) (T.El ka va)
      ElEq-m = TT.conv-Ty-El-Lift {m = m} {l = ka} ka<m va-ty
      vb-in-Lift-ctx : TT.HasType (TT.extend _ (T.El m (T.Lift m ka va))) vb (T.U kb)
      vb-in-Lift-ctx = TM.ctx-conv-HasType
                         (TT.is-Ty-El {l = ka} va-ty)
                         (TT.is-Ty-El {l = m} Lift-va-typed)
                         (TT.conv-Ty-sym ElEq-m) vb-ty
      ll-conv = TT.conv-Lift-Lift {nu = m} {m = ka} {l = kb}
                  kb<ka ka<m vb-in-Lift-ctx
      Lift-va-refl = TT.conv-refl Lift-va-typed
      step-b = TM.mk-conv-cong-PiCode {l = m} Lift-va-refl ll-conv
  in TT.conv-trans step-a step-b

------------------------------------------------------------------------
-- Extract a direct ConvTm from a same-type CommonLift.
--
-- When CommonLift relates u₀ : A and u₁ : A (the same type on both
-- sides), we can extract `ConvTm G u₀ u₁ A` directly:
--
--   * (trivial, trivial): u₀ ≡ v₀, u₁ ≡ v₁, v₀ ≡ v₁ ⇒ u₀ ≡ u₁.
--   * (proper,  proper):  u₀ ≡ Lift n k v₀, u₁ ≡ Lift n k v₁,
--                          and Lift n k v₀ ≡ Lift n k v₁ via cong.
--   * (trivial, proper) and (proper, trivial): impossible because
--     they force `n = k` and `Lt k n` simultaneously.
------------------------------------------------------------------------

commonLift-same-A :
  {n : Nat} {G : TT.Ctx n} {u₀ u₁ A : T.Expr n}
  -> CommonLift G u₀ u₁ A A
  -> TT.ConvTm G u₀ u₁ A
commonLift-same-A {A = A} cl
  with U-inj-Ty-T (TT.conv-Ty-trans
                    (TT.conv-Ty-sym (CommonLift.A₀≡U cl))
                    (CommonLift.A₁≡U cl))
... | n₀≡n₁ = go n₀≡n₁ (CommonLift.u₀≡ cl) (CommonLift.u₁≡ cl)
  where
    go : Eq (CommonLift.n₀ cl) (CommonLift.n₁ cl)
       -> LiftStep _ _ (CommonLift.n₀ cl) (CommonLift.k cl)
                       (CommonLift.v₀ cl) A
       -> LiftStep _ _ (CommonLift.n₁ cl) (CommonLift.k cl)
                       (CommonLift.v₁ cl) A
       -> TT.ConvTm _ _ _ A
    go refl (trivial e₀ ctm₀) (trivial e₁ ctm₁) =
      let vv = CommonLift.v₀≡v₁ cl
          A₀U = CommonLift.A₀≡U cl
          v₀ = CommonLift.v₀ cl
          v₁ = CommonLift.v₁ cl
          n₀ = CommonLift.n₀ cl
          vv-at-Un₀ : TT.ConvTm _ v₀ v₁ (T.U n₀)
          vv-at-Un₀ =
            Eq-transport (\ kk -> TT.ConvTm _ v₀ v₁ (T.U kk))
              (Eq-sym e₀) vv
          vv-at-A = TT.conv-conv vv-at-Un₀ (TT.conv-Ty-sym A₀U)
      in TT.conv-trans ctm₀ (TT.conv-trans vv-at-A (TT.conv-sym ctm₁))
    go refl (trivial e₀ _) (proper h _) =
      absurd (Lt-not-self (CommonLift.k cl)
               (Eq-transport (\ nn -> Lt (CommonLift.k cl) nn)
                 e₀ h))
    go refl (proper h _) (trivial e₁ _) =
      absurd (Lt-not-self (CommonLift.k cl)
               (Eq-transport (\ nn -> Lt (CommonLift.k cl) nn)
                 e₁ h))
    go refl (proper h₀ ctm₀) (proper h₁ ctm₁) =
      let vv = CommonLift.v₀≡v₁ cl
          A₀U = CommonLift.A₀≡U cl
          n₀ = CommonLift.n₀ cl
          k  = CommonLift.k  cl
          v₀ = CommonLift.v₀ cl
          v₁ = CommonLift.v₁ cl
          lc : TT.ConvTm _ (T.Lift n₀ k v₀) (T.Lift n₀ k v₁) (T.U n₀)
          lc = TT.conv-cong-Lift {m = n₀} {l = k} h₀ vv
          lc-at-A = TT.conv-conv lc (TT.conv-Ty-sym A₀U)
      in TT.conv-trans ctm₀ (TT.conv-trans lc-at-A (TT.conv-sym ctm₁))

------------------------------------------------------------------------
-- Extract a ConvTm from any TermUniqResult at same type on both sides.
------------------------------------------------------------------------

extract-conv-same :
  {n : Nat} {G : TT.Ctx n} {u₀ u₁ A : T.Expr n}
  -> TermUniqResult G u₀ u₁ A A
  -> TT.ConvTm G u₀ u₁ A
extract-conv-same (inl (mkSigma _ ctm)) = ctm
extract-conv-same (inr cl)              = commonLift-same-A cl

------------------------------------------------------------------------
-- term-uniq, with structural cases proved
------------------------------------------------------------------------

-- As in the paper, the recursion is on the Tarski expressions (the
-- implicit arguments), not on the derivations: the recursive calls are
-- on context-converted derivations and on sub-derivations peeled out
-- by inv-Lift / inv-PiCode, but always at strictly smaller expressions.
--
-- uniq-El is the paper's third statement (|B| = |a| gives B = El a).
-- It takes the code a as a separate argument, so the cases (El a, U)
-- and (El a, Pi) call it directly instead of re-entering type-uniq
-- with the arguments swapped, which Agda cannot see as decreasing.

term-uniq : TermUniqStatement
type-uniq : TypeUniqStatement
uniq-El : {n : Nat} {G : TT.Ctx n} {B : T.Expr n} {a : T.Expr n} {l : Nat}
  -> TT.IsType G B
  -> TT.HasType G a (T.U l)
  -> Eq (E.erase B) (E.erase a)
  -> TT.ConvTy G B (T.El l a)

------------------------------------------------------------------------
-- ty-conv peeling on the left
------------------------------------------------------------------------
term-uniq (TT.ty-conv d c) dM₁ eq with term-uniq d dM₁ eq
... | inl (mkSigma cTy ctm) =
      inl (mkSigma (TT.conv-Ty-trans (TT.conv-Ty-sym c) cTy)
                   (TT.conv-conv ctm c))
... | inr cl =
      inr (mkCommonLift
            (CommonLift.n₀ cl) (CommonLift.n₁ cl) (CommonLift.k cl)
            (CommonLift.v₀ cl) (CommonLift.v₁ cl)
            (TT.conv-Ty-trans (TT.conv-Ty-sym c) (CommonLift.A₀≡U cl))
            (CommonLift.A₁≡U cl)
            (liftStep-conv-Ty c (CommonLift.u₀≡ cl))
            (CommonLift.u₁≡ cl)
            (CommonLift.v₀≡v₁ cl))

------------------------------------------------------------------------
-- ty-conv peeling on the right
------------------------------------------------------------------------
term-uniq dM₀ (TT.ty-conv d c) eq with term-uniq dM₀ d eq
... | inl (mkSigma cTy ctm) =
      inl (mkSigma (TT.conv-Ty-trans cTy c) ctm)
... | inr cl =
      inr (mkCommonLift
            (CommonLift.n₀ cl) (CommonLift.n₁ cl) (CommonLift.k cl)
            (CommonLift.v₀ cl) (CommonLift.v₁ cl)
            (CommonLift.A₀≡U cl)
            (TT.conv-Ty-trans (TT.conv-Ty-sym c) (CommonLift.A₁≡U cl))
            (CommonLift.u₀≡ cl)
            (liftStep-conv-Ty c (CommonLift.u₁≡ cl))
            (CommonLift.v₀≡v₁ cl))

------------------------------------------------------------------------
-- (Var, Var) — erasure forces same index
------------------------------------------------------------------------
term-uniq {G = G} (TT.ty-var {i = i} dG) (TT.ty-var dG') refl =
  inl (mkSigma (TT.conv-Ty-refl (TM.wfCtx-lookup dG i))
               (TT.conv-refl (TT.ty-var dG)))

------------------------------------------------------------------------
-- Cross-shape impossible cases (non-Lift on both sides).
-- erase reveals the head, and Russell-side constructors are distinct.
------------------------------------------------------------------------
term-uniq (TT.ty-var _) (TT.ty-Lam _ _ _) ()
term-uniq (TT.ty-var _) (TT.ty-App _ _ _ _) ()
term-uniq (TT.ty-var _) (TT.ty-PiCode _ _) ()
term-uniq (TT.ty-var _) (TT.ty-UCode _ _) ()
term-uniq (TT.ty-Lam _ _ _) (TT.ty-var _) ()
term-uniq (TT.ty-Lam _ _ _) (TT.ty-App _ _ _ _) ()
term-uniq (TT.ty-Lam _ _ _) (TT.ty-PiCode _ _) ()
term-uniq (TT.ty-Lam _ _ _) (TT.ty-UCode _ _) ()
term-uniq (TT.ty-App _ _ _ _) (TT.ty-var _) ()
term-uniq (TT.ty-App _ _ _ _) (TT.ty-Lam _ _ _) ()
term-uniq (TT.ty-App _ _ _ _) (TT.ty-PiCode _ _) ()
term-uniq (TT.ty-App _ _ _ _) (TT.ty-UCode _ _) ()
term-uniq (TT.ty-PiCode _ _) (TT.ty-var _) ()
term-uniq (TT.ty-PiCode _ _) (TT.ty-Lam _ _ _) ()
term-uniq (TT.ty-PiCode _ _) (TT.ty-App _ _ _ _) ()
term-uniq (TT.ty-PiCode _ _) (TT.ty-UCode _ _) ()
term-uniq (TT.ty-UCode _ _) (TT.ty-var _) ()
term-uniq (TT.ty-UCode _ _) (TT.ty-Lam _ _ _) ()
term-uniq (TT.ty-UCode _ _) (TT.ty-App _ _ _ _) ()
term-uniq (TT.ty-UCode _ _) (TT.ty-PiCode _ _) ()

------------------------------------------------------------------------
-- (Lam, Lam) — recurse on body
------------------------------------------------------------------------
term-uniq {G = G} (TT.ty-Lam {A = A1} {B = B1} {b = b1} dA1 dB1 db1)
                  (TT.ty-Lam {A = A2} {B = B2} {b = b2} dA2 dB2 db2) eq =
  let mkSigma eqA (mkSigma eqB eqb) = R-Lam-inj eq
      cA = type-uniq dA1 dA2 eqA
      dA2-conv = TM.ctx-conv-IsType dA2 dA1 (TT.conv-Ty-sym cA)
      dB2' = dA2-conv dB2
      db2' = TM.ctx-conv-HasType dA2 dA1 (TT.conv-Ty-sym cA) db2
      cB = type-uniq dB1 dB2' eqB
      db2'' = TT.ty-conv db2' (TT.conv-Ty-sym cB)
      cb = extract-conv-same (term-uniq db1 db2'' eqb)
      lam-body-conv = TT.conv-cong-Lam-body
        (TM.presup-l-ConvTy cA)
        (TM.presup-l-ConvTy cB)
        cb
      lam-Ty-conv = TM.mk-conv-cong-Lam-Ty cA cB (TM.presup-r-ConvTm cb)
  in inl (mkSigma (TM.mk-conv-Ty-Pi cA cB)
                  (TT.conv-trans lam-body-conv lam-Ty-conv))

------------------------------------------------------------------------
-- (PiCode, PiCode) — uses PiCode-inj-T
------------------------------------------------------------------------
term-uniq {G = G} (TT.ty-PiCode {a = a1} {b = b1} {l = l1} da1 db1)
                  (TT.ty-PiCode {a = a2} {b = b2} {l = l2} da2 db2) eq =
  let mkSigma eqA eqB = R-Pi-inj eq
      ihA = term-uniq da1 da2 eqA
  in case-PiCode-a eqB ihA
  where
    case-PiCode-a :
         Eq (E.erase b1) (E.erase b2)
      -> TermUniqResult G a1 a2 (T.U l1) (T.U l2)
      -> TermUniqResult G (T.PiCode l1 a1 b1) (T.PiCode l2 a2 b2)
                           (T.U l1) (T.U l2)
    case-PiCode-a eqB (inl (mkSigma cTy ca)) =
      case-PiCode-eq eqB (U-inj-Ty-T cTy) ca
      where
        case-PiCode-eq :
             Eq (E.erase b1) (E.erase b2)
          -> Eq l1 l2 -> TT.ConvTm G a1 a2 (T.U l1)
          -> TermUniqResult G (T.PiCode l1 a1 b1) (T.PiCode l2 a2 b2)
                               (T.U l1) (T.U l2)
        case-PiCode-eq eqB refl ca =
          let aEl-conv : TT.ConvTy G (T.El l1 a1) (T.El l1 a2)
              aEl-conv = TT.conv-Ty-El {l = l1} ca
              db2' = TM.ctx-conv-HasType
                       (TT.is-Ty-El {l = l1} da2)
                       (TT.is-Ty-El {l = l1} da1)
                       (TT.conv-Ty-sym aEl-conv) db2
              cb = extract-conv-same (term-uniq db1 db2' eqB)
          in inl (mkSigma (TT.conv-Ty-refl
                            (TT.is-Ty-U {l = l1} (TM.typing-WfCtx da1)))
                          (TM.mk-conv-cong-PiCode {l = l1} ca cb))
    case-PiCode-a eqB (inr cl_a) = case-PiCode-inr eqB cl_a
      where
        case-PiCode-inr :
             Eq (E.erase b1) (E.erase b2)
          -> CommonLift G a1 a2 (T.U l1) (T.U l2)
          -> TermUniqResult G (T.PiCode l1 a1 b1) (T.PiCode l2 a2 b2)
                               (T.U l1) (T.U l2)
        case-PiCode-inr eqB
          (mkCommonLift _ _ ka va va' A0U A1U u0 u1 vv)
          with U-inj-Ty-T A0U | U-inj-Ty-T A1U
        ... | refl | refl =
          -- After both pattern matches:
          --   u0 : LiftStep G a1 l1 ka va  (U l1)
          --   u1 : LiftStep G a2 l2 ka va' (U l2)
          --   vv : ConvTm  G va va' (U ka)
          let dG : TT.WfCtx G
              dG = TM.typing-WfCtx da1
              va-ty  : TT.HasType G va  (T.U ka)
              va-ty  = TM.presup-l-ConvTm vv
              va'-ty : TT.HasType G va' (T.U ka)
              va'-ty = TM.presup-r-ConvTm vv
              ka-IsTy : TT.IsType G (T.El ka va)
              ka-IsTy = TT.is-Ty-El {l = ka} va-ty
              eqEl1 : TT.ConvTy G (T.El l1 a1) (T.El ka va)
              eqEl1 = build-eqEl da1 va-ty u0
              eqEl2-raw : TT.ConvTy G (T.El l2 a2) (T.El ka va')
              eqEl2-raw = build-eqEl da2 va'-ty u1
              eqEl2 : TT.ConvTy G (T.El l2 a2) (T.El ka va)
              eqEl2 = TT.conv-Ty-trans eqEl2-raw
                        (TT.conv-Ty-sym (TT.conv-Ty-El {l = ka} vv))
              db1' : TT.HasType (TT.extend G (T.El ka va)) b1 (T.U l1)
              db1' = TM.ctx-conv-HasType
                       (TT.is-Ty-El {l = l1} da1) ka-IsTy eqEl1 db1
              db2' : TT.HasType (TT.extend G (T.El ka va)) b2 (T.U l2)
              db2' = TM.ctx-conv-HasType
                       (TT.is-Ty-El {l = l2} da2) ka-IsTy eqEl2 db2
              ihb = term-uniq db1' db2' eqB
          in handle-ihb ihb va-ty va'-ty ka-IsTy u0 u1 vv eqEl1 eqEl2

          where
            ----------------------------------------------------------------
            -- inl branch: same level forced.  Build a same-type result.
            -- inr branch: defer to the three-way comparison via postulate
            -- (to be discharged separately below).
            ----------------------------------------------------------------
            handle-ihb :
                 TermUniqResult (TT.extend G (T.El ka va)) b1 b2 (T.U l1) (T.U l2)
              -> TT.HasType G va  (T.U ka)
              -> TT.HasType G va' (T.U ka)
              -> TT.IsType G (T.El ka va)
              -> LiftStep G a1 l1 ka va  (T.U l1)
              -> LiftStep G a2 l2 ka va' (T.U l2)
              -> TT.ConvTm G va va' (T.U ka)
              -> TT.ConvTy G (T.El l1 a1) (T.El ka va)
              -> TT.ConvTy G (T.El l2 a2) (T.El ka va)
              -> TermUniqResult G (T.PiCode l1 a1 b1) (T.PiCode l2 a2 b2)
                                  (T.U l1) (T.U l2)
            handle-ihb (inl (mkSigma cTy cb))
                       va-ty va'-ty ka-IsTy u0 u1 vv eqEl1 eqEl2
              with U-inj-Ty-T cTy
            ... | refl =
              -- l1 = l2; rebuild cl_a as same-type CommonLift to get a-conv.
              let isU-l1 = TT.is-Ty-U {l = l1} (TM.typing-WfCtx da1)
                  cl-same : CommonLift G a1 a2 (T.U l1) (T.U l1)
                  cl-same = mkCommonLift l1 l1 ka va va'
                              (TT.conv-Ty-refl isU-l1)
                              (TT.conv-Ty-refl isU-l1)
                              u0 u1 vv
                  ca : TT.ConvTm G a1 a2 (T.U l1)
                  ca = commonLift-same-A cl-same
                  cb' : TT.ConvTm (TT.extend G (T.El l1 a1)) b1 b2 (T.U l1)
                  cb' = TM.ctx-conv-ConvTm ka-IsTy
                          (TT.is-Ty-El {l = l1} da1)
                          (TT.conv-Ty-sym eqEl1) cb
              in inl (mkSigma (TT.conv-Ty-refl isU-l1)
                              (TM.mk-conv-cong-PiCode {l = l1} ca cb'))
            handle-ihb (inr (mkCommonLift _ _ kb vb vb' B0U B1U ub0 ub1 vvb))
                       va-ty va'-ty ka-IsTy u0 u1 vv eqEl1 eqEl2
              with U-inj-Ty-T B0U | U-inj-Ty-T B1U
            ... | refl | refl =
              dispatch-tri (Nat-trichotomy ka kb)
              where
                -- Local data, shadowed-clean.
                vb-ty  : TT.HasType (TT.extend G (T.El ka va)) vb  (T.U kb)
                vb-ty  = TM.presup-l-ConvTm vvb
                vb'-ty : TT.HasType (TT.extend G (T.El ka va)) vb' (T.U kb)
                vb'-ty = TM.presup-r-ConvTm vvb
                isU-l1 : TT.IsType G (T.U l1)
                isU-l1 = TT.is-Ty-U {l = l1} (TM.typing-WfCtx da1)
                isU-l2 : TT.IsType G (T.U l2)
                isU-l2 = TT.is-Ty-U {l = l2} (TM.typing-WfCtx da2)

                dispatch-tri :
                     Either (Lt ka kb) (Either (Eq ka kb) (Lt kb ka))
                  -> TermUniqResult G (T.PiCode l1 a1 b1) (T.PiCode l2 a2 b2)
                                     (T.U l1) (T.U l2)
                dispatch-tri (inl ka<kb)      =
                  -- ka < kb.  k_pi := kb.
                  -- v0_pi := PiCode kb (Lift kb ka va) vb.
                  -- v1_pi := PiCode kb (Lift kb ka va') vb' (vb' moved).
                  let -- v_pi conversion on the inner code.
                      Lift-va-conv : TT.ConvTm G (T.Lift kb ka va)
                                                  (T.Lift kb ka va') (T.U kb)
                      Lift-va-conv = TT.conv-cong-Lift {m = kb} {l = ka} ka<kb vv
                      Lift-typed-va : TT.HasType G (T.Lift kb ka va) (T.U kb)
                      Lift-typed-va = TT.ty-Lift {m = kb} {l = ka} ka<kb va-ty
                      ElEq-Lift-va : TT.ConvTy G (T.El kb (T.Lift kb ka va))
                                                  (T.El ka va)
                      ElEq-Lift-va = TT.conv-Ty-El-Lift {m = kb} {l = ka}
                                       ka<kb va-ty
                      vvb-in-Lift : TT.ConvTm (TT.extend G (T.El kb (T.Lift kb ka va)))
                                                vb vb' (T.U kb)
                      vvb-in-Lift = TM.ctx-conv-ConvTm
                                      (TT.is-Ty-El {l = ka} va-ty)
                                      (TT.is-Ty-El {l = kb} Lift-typed-va)
                                      (TT.conv-Ty-sym ElEq-Lift-va) vvb
                      vv-outer : TT.ConvTm G
                                  (T.PiCode kb (T.Lift kb ka va) vb)
                                  (T.PiCode kb (T.Lift kb ka va') vb')
                                  (T.U kb)
                      vv-outer = TM.mk-conv-cong-PiCode {l = kb}
                                   Lift-va-conv vvb-in-Lift
                      step1 = build-lt-side l1 da1 db1 vb-ty u0 ub0
                                eqEl1 va-ty ka<kb
                      step2 = build-lt-side-r l2 da2 db2 vb'-ty u1 ub1
                                eqEl2 va'-ty ka<kb
                  in inr (mkCommonLift l1 l2 kb
                            (T.PiCode kb (T.Lift kb ka va)  vb)
                            (T.PiCode kb (T.Lift kb ka va') vb')
                            (TT.conv-Ty-refl isU-l1)
                            (TT.conv-Ty-refl isU-l2)
                            step1 step2 vv-outer)
                  where
                    -- LEFT side: vb stays in extend G (El ka va).
                    -- conv-Lift-PiCode applied to PiCode kb (Lift kb ka va) vb
                    -- needs vb in extend G (El kb (Lift kb ka va)).
                    build-lt-side :
                         (li : Nat)
                      -> TT.HasType G a1 (T.U li)
                      -> TT.HasType (TT.extend G (T.El li a1)) b1 (T.U li)
                      -> TT.HasType (TT.extend G (T.El ka va)) vb (T.U kb)
                      -> LiftStep G a1 li ka va (T.U li)
                      -> LiftStep (TT.extend G (T.El ka va)) b1 li kb vb (T.U li)
                      -> TT.ConvTy G (T.El li a1) (T.El ka va)
                      -> TT.HasType G va (T.U ka)
                      -> Lt ka kb
                      -> LiftStep G (T.PiCode li a1 b1) li kb
                                    (T.PiCode kb (T.Lift kb ka va) vb) (T.U li)
                    -- u0 trivial: l1 = ka.  ub0 cases are absurd.
                    build-lt-side li dai dbi vbi-ty (trivial e_a _)
                                  (trivial e_b _) eqEl-i va_-ty ka<kb' =
                      let eq : Eq ka kb
                          eq = Eq-trans (Eq-sym e_a) e_b
                      in absurd (Lt-not-self ka
                                  (Eq-transport (\ x -> Lt ka x)
                                    (Eq-sym eq) ka<kb'))
                    build-lt-side li dai dbi vbi-ty (trivial e_a _)
                                  (proper h_b _) eqEl-i va_-ty ka<kb' =
                      let h_b' : Lt kb ka
                          h_b' = Eq-transport (\ x -> Lt kb x) e_a h_b
                      in absurd (Lt-not-self kb
                                  (Lt-trans-Lt {a = kb} {b = ka} {c = kb}
                                    h_b' ka<kb'))
                    -- u0 proper, ub0 trivial: l1 = kb.
                    build-lt-side li dai dbi vbi-ty (proper h_a ctm-a)
                                  (trivial refl ctm-b) eqEl-i va_-ty ka<kb' =
                      let cb : TT.ConvTm (TT.extend G (T.El li a1)) b1 vb (T.U li)
                          cb = TM.ctx-conv-ConvTm
                                 (TT.is-Ty-El {l = ka} va_-ty)
                                 (TT.is-Ty-El {l = li} dai)
                                 (TT.conv-Ty-sym eqEl-i) ctm-b
                          tm = TM.mk-conv-cong-PiCode {l = li} ctm-a cb
                      in trivial refl tm
                    -- u0 proper, ub0 proper: kb < l1.
                    build-lt-side li dai dbi vbi-ty (proper h_a ctm-a)
                                  (proper h_b ctm-b) eqEl-i va_-ty ka<kb' =
                      let cb : TT.ConvTm (TT.extend G (T.El li a1)) b1
                                          (T.Lift li kb vb) (T.U li)
                          cb = TM.ctx-conv-ConvTm
                                 (TT.is-Ty-El {l = ka} va_-ty)
                                 (TT.is-Ty-El {l = li} dai)
                                 (TT.conv-Ty-sym eqEl-i) ctm-b
                          tm0 = TM.mk-conv-cong-PiCode {l = li} ctm-a cb
                          tm1 = Lift-Lift-PiCode-fwd
                                  {ka = ka} {kb = kb} {m = li}
                                  ka<kb' h_b va_-ty vbi-ty
                          tm = TT.conv-trans tm0 (TT.conv-sym tm1)
                      in proper h_b tm

                    -- RIGHT side: similar but with vb' (in Γext = extend G (El ka va)).
                    -- Need vb' in extend G (El ka va') and extend G (El kb (Lift kb ka va')).
                    build-lt-side-r :
                         (li : Nat)
                      -> TT.HasType G a2 (T.U li)
                      -> TT.HasType (TT.extend G (T.El li a2)) b2 (T.U li)
                      -> TT.HasType (TT.extend G (T.El ka va)) vb' (T.U kb)
                      -> LiftStep G a2 li ka va' (T.U li)
                      -> LiftStep (TT.extend G (T.El ka va)) b2 li kb vb' (T.U li)
                      -> TT.ConvTy G (T.El li a2) (T.El ka va)
                      -> TT.HasType G va' (T.U ka)
                      -> Lt ka kb
                      -> LiftStep G (T.PiCode li a2 b2) li kb
                                    (T.PiCode kb (T.Lift kb ka va') vb') (T.U li)
                    build-lt-side-r li dai dbi vbi-ty (trivial e_a _)
                                    (trivial e_b _) eqEl-i va_-ty ka<kb' =
                      let eq : Eq ka kb
                          eq = Eq-trans (Eq-sym e_a) e_b
                      in absurd (Lt-not-self ka
                                  (Eq-transport (\ x -> Lt ka x)
                                    (Eq-sym eq) ka<kb'))
                    build-lt-side-r li dai dbi vbi-ty (trivial e_a _)
                                    (proper h_b _) eqEl-i va_-ty ka<kb' =
                      let h_b' : Lt kb ka
                          h_b' = Eq-transport (\ x -> Lt kb x) e_a h_b
                      in absurd (Lt-not-self kb
                                  (Lt-trans-Lt {a = kb} {b = ka} {c = kb}
                                    h_b' ka<kb'))
                    build-lt-side-r li dai dbi vbi-ty (proper h_a ctm-a)
                                    (trivial refl ctm-b) eqEl-i va_-ty ka<kb' =
                      let cb : TT.ConvTm (TT.extend G (T.El li a2)) b2 vb' (T.U li)
                          cb = TM.ctx-conv-ConvTm
                                 (TT.is-Ty-El {l = ka} va-ty)
                                 (TT.is-Ty-El {l = li} dai)
                                 (TT.conv-Ty-sym eqEl-i) ctm-b
                          tm = TM.mk-conv-cong-PiCode {l = li} ctm-a cb
                      in trivial refl tm
                    build-lt-side-r li dai dbi vbi-ty (proper h_a ctm-a)
                                    (proper h_b ctm-b) eqEl-i va_-ty ka<kb' =
                      let cb : TT.ConvTm (TT.extend G (T.El li a2)) b2
                                          (T.Lift li kb vb') (T.U li)
                          cb = TM.ctx-conv-ConvTm
                                 (TT.is-Ty-El {l = ka} va-ty)
                                 (TT.is-Ty-El {l = li} dai)
                                 (TT.conv-Ty-sym eqEl-i) ctm-b
                          -- Move vb' from extend G (El ka va) to extend G (El ka va')
                          ElEq : TT.ConvTy G (T.El ka va) (T.El ka va')
                          ElEq = TT.conv-Ty-El {l = ka} vv
                          vb'-in-va' : TT.HasType (TT.extend G (T.El ka va'))
                                                    vb' (T.U kb)
                          vb'-in-va' = TM.ctx-conv-HasType
                                         (TT.is-Ty-El {l = ka} va-ty)
                                         (TT.is-Ty-El {l = ka} va_-ty)
                                         ElEq vbi-ty
                          tm0 = TM.mk-conv-cong-PiCode {l = li} ctm-a cb
                          tm1 = Lift-Lift-PiCode-fwd
                                  {ka = ka} {kb = kb} {m = li}
                                  ka<kb' h_b va_-ty vb'-in-va'
                          tm = TT.conv-trans tm0 (TT.conv-sym tm1)
                      in proper h_b tm
                dispatch-tri (inr (inr kb<ka)) =
                  -- kb < ka.  k_pi := ka.
                  -- v0_pi := PiCode ka va  (Lift ka kb vb).
                  -- v1_pi := PiCode ka va' (Lift ka kb vb') (vb' moved).
                  let -- Conversion on body Lift code.
                      Lift-vb-conv : TT.ConvTm (TT.extend G (T.El ka va))
                                                (T.Lift ka kb vb)
                                                (T.Lift ka kb vb') (T.U ka)
                      Lift-vb-conv = TT.conv-cong-Lift {m = ka} {l = kb}
                                       kb<ka vvb
                      vv-outer : TT.ConvTm G
                                  (T.PiCode ka va  (T.Lift ka kb vb))
                                  (T.PiCode ka va' (T.Lift ka kb vb'))
                                  (T.U ka)
                      vv-outer = TM.mk-conv-cong-PiCode {l = ka} vv Lift-vb-conv
                      step1 = build-gt-side l1 da1 db1 vb-ty u0 ub0
                                eqEl1 va-ty kb<ka
                      step2 = build-gt-side-r l2 da2 db2 vb'-ty u1 ub1
                                eqEl2 va'-ty kb<ka
                  in inr (mkCommonLift l1 l2 ka
                            (T.PiCode ka va  (T.Lift ka kb vb))
                            (T.PiCode ka va' (T.Lift ka kb vb'))
                            (TT.conv-Ty-refl isU-l1)
                            (TT.conv-Ty-refl isU-l2)
                            step1 step2 vv-outer)
                  where
                    -- LEFT side: build LiftStep G (PiCode l1 a1 b1) l1 ka v0_pi (U l1).
                    build-gt-side :
                         (li : Nat)
                      -> TT.HasType G a1 (T.U li)
                      -> TT.HasType (TT.extend G (T.El li a1)) b1 (T.U li)
                      -> TT.HasType (TT.extend G (T.El ka va)) vb (T.U kb)
                      -> LiftStep G a1 li ka va (T.U li)
                      -> LiftStep (TT.extend G (T.El ka va)) b1 li kb vb (T.U li)
                      -> TT.ConvTy G (T.El li a1) (T.El ka va)
                      -> TT.HasType G va (T.U ka)
                      -> Lt kb ka
                      -> LiftStep G (T.PiCode li a1 b1) li ka
                                    (T.PiCode ka va (T.Lift ka kb vb)) (T.U li)
                    -- ub0 trivial cases are absurd in kb<ka.
                    build-gt-side li dai dbi vbi-ty (trivial e_a _)
                                  (trivial e_b _) eqEl-i va_-ty kb<ka' =
                      let eq : Eq ka kb
                          eq = Eq-trans (Eq-sym e_a) e_b
                      in absurd (Lt-not-self kb
                                  (Eq-transport (\ x -> Lt kb x)
                                    eq kb<ka'))
                    build-gt-side li dai dbi vbi-ty (proper h_a _)
                                  (trivial e_b _) eqEl-i va_-ty kb<ka' =
                      let h_a' : Lt ka kb
                          h_a' = Eq-transport (\ x -> Lt ka x) e_b h_a
                      in absurd (Lt-not-self kb
                                  (Lt-trans-Lt {a = kb} {b = ka} {c = kb}
                                    kb<ka' h_a'))
                    -- u0 trivial, ub0 proper: l1 = ka.  Outer LiftStep trivial.
                    build-gt-side li dai dbi vbi-ty (trivial refl ctm-a)
                                  (proper h_b ctm-b) eqEl-i va_-ty kb<ka' =
                      let cb : TT.ConvTm (TT.extend G (T.El li a1)) b1
                                          (T.Lift li kb vb) (T.U li)
                          cb = TM.ctx-conv-ConvTm
                                 (TT.is-Ty-El {l = ka} va_-ty)
                                 (TT.is-Ty-El {l = li} dai)
                                 (TT.conv-Ty-sym eqEl-i) ctm-b
                          tm = TM.mk-conv-cong-PiCode {l = li} ctm-a cb
                      in trivial refl tm
                    -- u0 proper, ub0 proper: ka < l1.
                    build-gt-side li dai dbi vbi-ty (proper h_a ctm-a)
                                  (proper h_b ctm-b) eqEl-i va_-ty kb<ka' =
                      let cb : TT.ConvTm (TT.extend G (T.El li a1)) b1
                                          (T.Lift li kb vb) (T.U li)
                          cb = TM.ctx-conv-ConvTm
                                 (TT.is-Ty-El {l = ka} va_-ty)
                                 (TT.is-Ty-El {l = li} dai)
                                 (TT.conv-Ty-sym eqEl-i) ctm-b
                          tm0 = TM.mk-conv-cong-PiCode {l = li} ctm-a cb
                          tm1 = Lift-Lift-PiCode-bwd
                                  {ka = ka} {kb = kb} {m = li}
                                  kb<ka' h_a va_-ty vbi-ty
                          tm = TT.conv-trans tm0 (TT.conv-sym tm1)
                      in proper h_a tm

                    -- RIGHT side: vb' moved from extend G (El ka va) to extend G (El ka va').
                    build-gt-side-r :
                         (li : Nat)
                      -> TT.HasType G a2 (T.U li)
                      -> TT.HasType (TT.extend G (T.El li a2)) b2 (T.U li)
                      -> TT.HasType (TT.extend G (T.El ka va)) vb' (T.U kb)
                      -> LiftStep G a2 li ka va' (T.U li)
                      -> LiftStep (TT.extend G (T.El ka va)) b2 li kb vb' (T.U li)
                      -> TT.ConvTy G (T.El li a2) (T.El ka va)
                      -> TT.HasType G va' (T.U ka)
                      -> Lt kb ka
                      -> LiftStep G (T.PiCode li a2 b2) li ka
                                    (T.PiCode ka va' (T.Lift ka kb vb')) (T.U li)
                    build-gt-side-r li dai dbi vbi-ty (trivial e_a _)
                                    (trivial e_b _) eqEl-i va_-ty kb<ka' =
                      let eq : Eq ka kb
                          eq = Eq-trans (Eq-sym e_a) e_b
                      in absurd (Lt-not-self kb
                                  (Eq-transport (\ x -> Lt kb x)
                                    eq kb<ka'))
                    build-gt-side-r li dai dbi vbi-ty (proper h_a _)
                                    (trivial e_b _) eqEl-i va_-ty kb<ka' =
                      let h_a' : Lt ka kb
                          h_a' = Eq-transport (\ x -> Lt ka x) e_b h_a
                      in absurd (Lt-not-self kb
                                  (Lt-trans-Lt {a = kb} {b = ka} {c = kb}
                                    kb<ka' h_a'))
                    build-gt-side-r li dai dbi vbi-ty (trivial refl ctm-a)
                                    (proper h_b ctm-b) eqEl-i va_-ty kb<ka' =
                      let cb : TT.ConvTm (TT.extend G (T.El li a2)) b2
                                          (T.Lift li kb vb') (T.U li)
                          cb = TM.ctx-conv-ConvTm
                                 (TT.is-Ty-El {l = ka} va-ty)
                                 (TT.is-Ty-El {l = li} dai)
                                 (TT.conv-Ty-sym eqEl-i) ctm-b
                          tm = TM.mk-conv-cong-PiCode {l = li} ctm-a cb
                      in trivial refl tm
                    build-gt-side-r li dai dbi vbi-ty (proper h_a ctm-a)
                                    (proper h_b ctm-b) eqEl-i va_-ty kb<ka' =
                      let cb : TT.ConvTm (TT.extend G (T.El li a2)) b2
                                          (T.Lift li kb vb') (T.U li)
                          cb = TM.ctx-conv-ConvTm
                                 (TT.is-Ty-El {l = ka} va-ty)
                                 (TT.is-Ty-El {l = li} dai)
                                 (TT.conv-Ty-sym eqEl-i) ctm-b
                          -- Move vb' from extend G (El ka va) to extend G (El ka va').
                          ElEq : TT.ConvTy G (T.El ka va) (T.El ka va')
                          ElEq = TT.conv-Ty-El {l = ka} vv
                          vb'-in-va' : TT.HasType (TT.extend G (T.El ka va'))
                                                    vb' (T.U kb)
                          vb'-in-va' = TM.ctx-conv-HasType
                                         (TT.is-Ty-El {l = ka} va-ty)
                                         (TT.is-Ty-El {l = ka} va_-ty)
                                         ElEq vbi-ty
                          tm0 = TM.mk-conv-cong-PiCode {l = li} ctm-a cb
                          tm1 = Lift-Lift-PiCode-bwd
                                  {ka = ka} {kb = kb} {m = li}
                                  kb<ka' h_a va_-ty vb'-in-va'
                          tm = TT.conv-trans tm0 (TT.conv-sym tm1)
                      in proper h_a tm
                dispatch-tri (inr (inl refl)) =
                  -- ka = kb.  k_pi := ka.  v0_pi := PiCode ka va vb,
                  -- v1_pi := PiCode ka va' vb'.
                  let k = ka
                      -- Move vb' to extend G (El k va') for typing PiCode ka va' vb'.
                      ElEq : TT.ConvTy G (T.El k va) (T.El k va')
                      ElEq = TT.conv-Ty-El {l = k} vv
                      -- vv-outer : ConvTm G (PiCode k va vb) (PiCode k va' vb') (U k)
                      vv-outer : TT.ConvTm G (T.PiCode k va vb)
                                              (T.PiCode k va' vb') (T.U k)
                      vv-outer = TM.mk-conv-cong-PiCode {l = k} vv vvb
                      step1 = build-eq-side l1 da1 db1 vb-ty u0 ub0
                                eqEl1 va-ty
                      step2 = build-eq-side-r l2 da2 db2 vb'-ty u1 ub1
                                eqEl2 va'-ty ElEq
                  in inr (mkCommonLift l1 l2 k
                            (T.PiCode k va  vb)
                            (T.PiCode k va' vb')
                            (TT.conv-Ty-refl isU-l1)
                            (TT.conv-Ty-refl isU-l2)
                            step1 step2 vv-outer)
                  where
                    -- LEFT side helper: builds LiftStep on PiCode using va and vb.
                    -- ub_i is in extend G (El ka va), already vai-ctx for LEFT.
                    build-eq-side :
                         (li : Nat)
                      -> TT.HasType G a1 (T.U li)
                      -> TT.HasType (TT.extend G (T.El li a1)) b1 (T.U li)
                      -> TT.HasType (TT.extend G (T.El ka va)) vb (T.U ka)
                      -> LiftStep G a1 li ka va (T.U li)
                      -> LiftStep (TT.extend G (T.El ka va)) b1 li ka vb (T.U li)
                      -> TT.ConvTy G (T.El li a1) (T.El ka va)
                      -> TT.HasType G va (T.U ka)
                      -> LiftStep G (T.PiCode li a1 b1) li ka
                                    (T.PiCode ka va vb) (T.U li)
                    build-eq-side li dai dbi vbi-ty (trivial refl ctm-a)
                                  (trivial _ ctm-b) eqEl-i va_-ty =
                      -- li = ka.  Build conv-cong-PiCode in (extend G (El li a1)).
                      let cb : TT.ConvTm (TT.extend G (T.El li a1)) b1 vb (T.U li)
                          cb = TM.ctx-conv-ConvTm
                                 (TT.is-Ty-El {l = ka} va_-ty)
                                 (TT.is-Ty-El {l = li} dai)
                                 (TT.conv-Ty-sym eqEl-i) ctm-b
                          tm = TM.mk-conv-cong-PiCode {l = li} ctm-a cb
                      in trivial refl tm
                    build-eq-side li dai dbi vbi-ty (trivial refl _) (proper h _)
                                  eqEl-i va_-ty =
                      absurd (Lt-not-self li h)
                    build-eq-side li dai dbi vbi-ty (proper h _) (trivial refl _)
                                  eqEl-i va_-ty =
                      absurd (Lt-not-self li h)
                    build-eq-side li dai dbi vbi-ty (proper h-a ctm-a)
                                  (proper h-b ctm-b) eqEl-i va_-ty =
                      -- ka < li.  Build proper LiftStep.
                      let cb : TT.ConvTm (TT.extend G (T.El li a1)) b1
                                          (T.Lift li ka vb) (T.U li)
                          cb = TM.ctx-conv-ConvTm
                                 (TT.is-Ty-El {l = ka} va_-ty)
                                 (TT.is-Ty-El {l = li} dai)
                                 (TT.conv-Ty-sym eqEl-i) ctm-b
                          tm0 = TM.mk-conv-cong-PiCode {l = li} ctm-a cb
                          tm1 = TT.conv-Lift-PiCode {m = li} {l = ka}
                                  h-a va_-ty vbi-ty
                          tm = TT.conv-trans tm0 (TT.conv-sym tm1)
                      in proper h-a tm

                    -- RIGHT side helper: similar but vb' needs ctx-conv
                    -- to typecheck PiCode ka va' vb', and conv-Lift-PiCode
                    -- needs vb' moved.
                    build-eq-side-r :
                         (li : Nat)
                      -> TT.HasType G a2 (T.U li)
                      -> TT.HasType (TT.extend G (T.El li a2)) b2 (T.U li)
                      -> TT.HasType (TT.extend G (T.El ka va)) vb' (T.U ka)
                      -> LiftStep G a2 li ka va' (T.U li)
                      -> LiftStep (TT.extend G (T.El ka va)) b2 li ka vb' (T.U li)
                      -> TT.ConvTy G (T.El li a2) (T.El ka va)
                      -> TT.HasType G va' (T.U ka)
                      -> TT.ConvTy G (T.El ka va) (T.El ka va')
                      -> LiftStep G (T.PiCode li a2 b2) li ka
                                    (T.PiCode ka va' vb') (T.U li)
                    build-eq-side-r li dai dbi vbi-ty (trivial refl ctm-a)
                                    (trivial _ ctm-b) eqEl-i va_-ty ElEq =
                      let cb : TT.ConvTm (TT.extend G (T.El li a2)) b2 vb' (T.U li)
                          cb = TM.ctx-conv-ConvTm
                                 (TT.is-Ty-El {l = ka} va-ty)
                                 (TT.is-Ty-El {l = li} dai)
                                 (TT.conv-Ty-sym eqEl-i) ctm-b
                          tm = TM.mk-conv-cong-PiCode {l = li} ctm-a cb
                      in trivial refl tm
                    build-eq-side-r li dai dbi vbi-ty (trivial refl _)
                                    (proper h _) eqEl-i va_-ty ElEq =
                      absurd (Lt-not-self li h)
                    build-eq-side-r li dai dbi vbi-ty (proper h _)
                                    (trivial refl _) eqEl-i va_-ty ElEq =
                      absurd (Lt-not-self li h)
                    build-eq-side-r li dai dbi vbi-ty (proper h-a ctm-a)
                                    (proper h-b ctm-b) eqEl-i va_-ty ElEq =
                      let cb : TT.ConvTm (TT.extend G (T.El li a2)) b2
                                          (T.Lift li ka vb') (T.U li)
                          cb = TM.ctx-conv-ConvTm
                                 (TT.is-Ty-El {l = ka} va-ty)
                                 (TT.is-Ty-El {l = li} dai)
                                 (TT.conv-Ty-sym eqEl-i) ctm-b
                          -- Move vb' to extend G (El ka va') for conv-Lift-PiCode.
                          vb'-in-va' : TT.HasType (TT.extend G (T.El ka va')) vb'
                                                   (T.U ka)
                          vb'-in-va' = TM.ctx-conv-HasType
                                         (TT.is-Ty-El {l = ka} va-ty)
                                         (TT.is-Ty-El {l = ka} va_-ty)
                                         ElEq vbi-ty
                          tm0 = TM.mk-conv-cong-PiCode {l = li} ctm-a cb
                          tm1 = TT.conv-Lift-PiCode {m = li} {l = ka}
                                  h-a va_-ty vb'-in-va'
                          tm = TT.conv-trans tm0 (TT.conv-sym tm1)
                      in proper h-a tm

------------------------------------------------------------------------
-- (App, App) — uses subst1-cong-Ty for cross-substitution.
------------------------------------------------------------------------
term-uniq {G = G} (TT.ty-App {A = A1} {B = B1} {c = c1} {a = a1} dA1 dB1 dc1 da1)
                  (TT.ty-App {A = A2} {B = B2} {c = c2} {a = a2} dA2 dB2 dc2 da2) eq =
  let mkSigma eqA (mkSigma eqB (mkSigma eqc eqa)) = R-App-inj eq
      cA = type-uniq dA1 dA2 eqA
      dA2-conv : {X : T.Expr (suc _)} -> TT.IsType (TT.extend G A2) X -> TT.IsType (TT.extend G A1) X
      dA2-conv = TM.ctx-conv-IsType dA2 dA1 (TT.conv-Ty-sym cA)
      dB2'  = dA2-conv dB2
      cB    = type-uniq dB1 dB2' eqB
      da2-c : TT.HasType G a2 A1
      da2-c = TT.ty-conv da2 (TT.conv-Ty-sym cA)
      dc2-c : TT.HasType G c2 (T.Pi A1 B1)
      dc2-c = TT.ty-conv dc2 (TT.conv-Ty-sym (TM.mk-conv-Ty-Pi cA cB))
      ca = extract-conv-same (term-uniq da1 da2-c eqa)
      cc = extract-conv-same (term-uniq dc1 dc2-c eqc)
      BsubstCong : TT.ConvTy G (T.subst1 B1 a1) (T.subst1 B1 a2)
      BsubstCong = TMC.subst1-cong-Ty ca dA1 dB1
      step1 = TT.conv-cong-App-fun dA1 dB1 cc da1
      step2 = TT.conv-cong-App-arg dA1 dB1 dc2-c ca BsubstCong
      step3raw = TM.mk-conv-cong-App-Ty cA cB dc2-c da2-c
      step3 = TT.conv-conv step3raw (TT.conv-Ty-sym BsubstCong)
      composite = TT.conv-trans step1 (TT.conv-trans step2 step3)
      subst1-tyConv : TT.ConvTy G (T.subst1 B1 a1) (T.subst1 B2 a2)
      subst1-tyConv =
        TT.conv-Ty-trans BsubstCong
          (TM.subst-ConvTy (TM.subst1-WtSub dA1 da2-c)
                            (TM.isType-WfCtx dA1) cB)
  in inl (mkSigma subst1-tyConv composite)

------------------------------------------------------------------------
-- (UCode, UCode) — same inner level (forced by erasure), possibly
-- different outer levels.  Direct CommonLift construction.
------------------------------------------------------------------------
term-uniq {G = G} (TT.ty-UCode {m = m₀} {l = l₀} dG h₀)
                  (TT.ty-UCode {m = m₁} {l = l₁} _ h₁) refl =
  -- erase (UCode m₀ l₀) = R.U l₀; erase (UCode m₁ l₁) = R.U l₁; refl ⇒ l₀ = l₁
  -- l = l₀ = l₁; pick canonical witness UCode (suc l) l : U (suc l).
  let v₀ = T.UCode (suc l₀) l₀
      sucl<m₀ : Lt l₀ m₀
      sucl<m₀ = h₀
      sucl<m₁ : Lt l₁ m₁
      sucl<m₁ = h₁
      isU-m₀ : TT.IsType G (T.U m₀)
      isU-m₀ = TT.is-Ty-U {l = m₀} dG
      isU-m₁ : TT.IsType G (T.U m₁)
      isU-m₁ = TT.is-Ty-U {l = m₁} dG
      -- u₀≡ : LiftStep G (UCode m₀ l₀) m₀ (suc l₀) (UCode (suc l₀) l₀) (U m₀)
      --       i.e. relate UCode m₀ l₀ to v₀ via either trivial or proper Lift.
      --       Trivial when m₀ = suc l₀; proper when suc l₀ < m₀.
      step₀ : LiftStep G (T.UCode m₀ l₀) m₀ (suc l₀) v₀ (T.U m₀)
      step₀ = mk-step h₀ dG
      step₁ : LiftStep G (T.UCode m₁ l₀) m₁ (suc l₀) v₀ (T.U m₁)
      step₁ = mk-step h₁ dG
  in inr (mkCommonLift m₀ m₁ (suc l₀) v₀ v₀
            (TT.conv-Ty-refl isU-m₀)
            (TT.conv-Ty-refl isU-m₁)
            step₀ step₁
            (TT.conv-refl (TT.ty-UCode {m = suc l₀} {l = l₀} dG (Le-refl l₀))))
  where
    -- Build the LiftStep for UCode m l : U m given Lt l m and dG.
    -- If m = suc l, use trivial; otherwise proper via conv-sym (Lift-UCode).
    mk-step : {m l : Nat}
            -> Lt l m -> TT.WfCtx G
            -> LiftStep G (T.UCode m l) m (suc l) (T.UCode (suc l) l) (T.U m)
    mk-step {m = m} {l = l} h dG with Le-cases (suc l) m h
    ... | inl refl =
            -- m = suc l: trivial step
            trivial refl (TT.conv-refl (TT.ty-UCode {m = m} {l = l} dG h))
    ... | inr h' =
            -- suc l < m: proper.  conv-Lift-UCode :
            --   Lift m (suc l) (UCode (suc l) l) ≡ UCode m l : U m
            -- We need:  ConvTm G (UCode m l) (Lift m (suc l) (UCode (suc l) l)) (U m)
            -- (sym).  Here `nu = l` in conv-Lift-UCode's API (the inner
            -- universe code's level), `l = suc l` (the intermediate level
            -- of the Lift), `m = m` (the outer).
            proper h'
              (TT.conv-sym
                 (TT.conv-Lift-UCode
                    {m = m} {l = suc l} {nu = l}
                    dG (Le-refl l) h'))

------------------------------------------------------------------------
-- (Lift, *) — recurse on the inner of the Lift on the left.
-- Catches all (Lift, X) including (Lift, Lift) by recursion.
------------------------------------------------------------------------
term-uniq {G = G} (TT.ty-Lift {m = m₀} {l = k₀} h₀ da₀) dM₁ eq =
  case-Lift-l (term-uniq da₀ dM₁ eq)
  where
    dG : TT.WfCtx G
    dG = TM.typing-WfCtx da₀

    case-Lift-l : TermUniqResult G _ _ (T.U k₀) _
               -> TermUniqResult G (T.Lift m₀ k₀ _) _ (T.U m₀) _
    case-Lift-l (inl (mkSigma cTy ctm)) =
      inr (mkCommonLift m₀ k₀ k₀ _ _
            (TT.conv-Ty-refl (TT.is-Ty-U {l = m₀} dG))
            (TT.conv-Ty-sym cTy)
            (proper h₀ (TT.conv-refl
                         (TT.ty-Lift {m = m₀} {l = k₀} h₀ da₀)))
            (trivial refl (TT.conv-refl dM₁))
            ctm)
    case-Lift-l (inr cl) =
      go (CommonLift.u₀≡ cl) (U-inj-Ty-T (CommonLift.A₀≡U cl))
      where
        n₀ = CommonLift.n₀ cl
        n₁ = CommonLift.n₁ cl
        k  = CommonLift.k  cl
        v₀ = CommonLift.v₀ cl
        v₁ = CommonLift.v₁ cl
        wrap : LiftStep G (T.Lift m₀ k₀ _) m₀ k v₀ (T.U m₀)
            -> TermUniqResult G (T.Lift m₀ k₀ _) _ (T.U m₀) _
        wrap step =
          inr (mkCommonLift m₀ n₁ k v₀ v₁
                 (TT.conv-Ty-refl (TT.is-Ty-U {l = m₀} dG))
                 (CommonLift.A₁≡U cl)
                 step
                 (CommonLift.u₁≡ cl)
                 (CommonLift.v₀≡v₁ cl))
        go : LiftStep G _ n₀ k v₀ (T.U k₀)
          -> Eq k₀ n₀
          -> TermUniqResult G (T.Lift m₀ k₀ _) _ (T.U m₀) _
        go (trivial e ctm) refl =
          -- e : Eq n₀ k = Eq k₀ k.  ctm : ConvTm G a₀ v₀ (U k₀).
          -- Goal: LiftStep G (Lift m₀ k₀ a₀) m₀ k v₀ (U m₀).
          -- Build with cl.k → k₀ via Eq-transport on e.
          wrap (Eq-transport
                 (\ kk -> LiftStep G (T.Lift m₀ k₀ _) m₀ kk v₀ (T.U m₀))
                 e
                 (proper {n = _} {G = G} {u = T.Lift m₀ k₀ _}
                         {m = m₀} {k = k₀} {v = v₀} {A = T.U m₀}
                         h₀
                         (TT.conv-cong-Lift {m = m₀} {l = k₀} h₀ ctm)))
        go (proper h ctm) refl =
          -- h : Lt k n₀ = Lt k k₀.  ctm : ConvTm G a₀ (Lift k₀ k v₀) (U k₀).
          -- Goal: LiftStep G (Lift m₀ k₀ a₀) m₀ k v₀ (U m₀)
          let lift-cong = TT.conv-cong-Lift {m = m₀} {l = k₀} h₀ ctm
              v₀-typed : TT.HasType G v₀ (T.U k)
              v₀-typed = TM.presup-l-ConvTm (CommonLift.v₀≡v₁ cl)
              ll-eq = TT.conv-Lift-Lift {nu = m₀} {m = k₀} {l = k}
                                         h h₀ v₀-typed
              composite = TT.conv-trans lift-cong ll-eq
              k<m₀ : Lt k m₀
              k<m₀ = Lt-trans-Lt {a = k} {b = k₀} {c = m₀} h h₀
          in wrap (proper {n = _} {G = G} {u = T.Lift m₀ k₀ _}
                          {m = m₀} {k = k} {v = v₀} {A = T.U m₀}
                          k<m₀ composite)

------------------------------------------------------------------------
-- (X, Lift) — symmetric to (Lift, *) for non-Lift left.
------------------------------------------------------------------------
term-uniq {G = G} dM₀ (TT.ty-Lift {m = m₁} {l = k₁} h₁ da₁) eq =
  case-Lift-r (term-uniq dM₀ da₁ eq)
  where
    dG : TT.WfCtx G
    dG = TM.typing-WfCtx da₁

    case-Lift-r : TermUniqResult G _ _ _ (T.U k₁)
               -> TermUniqResult G _ (T.Lift m₁ k₁ _) _ (T.U m₁)
    case-Lift-r (inl (mkSigma cTy ctm)) =
      inr (mkCommonLift k₁ m₁ k₁ _ _
            cTy
            (TT.conv-Ty-refl (TT.is-Ty-U {l = m₁} dG))
            (trivial refl (TT.conv-refl dM₀))
            (proper h₁ (TT.conv-refl
                         (TT.ty-Lift {m = m₁} {l = k₁} h₁ da₁)))
            (TT.conv-conv ctm cTy))
    case-Lift-r (inr cl) =
      go (CommonLift.u₁≡ cl) (U-inj-Ty-T (CommonLift.A₁≡U cl))
      where
        n₀ = CommonLift.n₀ cl
        n₁ = CommonLift.n₁ cl
        k  = CommonLift.k  cl
        v₀ = CommonLift.v₀ cl
        v₁ = CommonLift.v₁ cl
        wrap : LiftStep G (T.Lift m₁ k₁ _) m₁ k v₁ (T.U m₁)
            -> TermUniqResult G _ (T.Lift m₁ k₁ _) _ (T.U m₁)
        wrap step =
          inr (mkCommonLift n₀ m₁ k v₀ v₁
                 (CommonLift.A₀≡U cl)
                 (TT.conv-Ty-refl (TT.is-Ty-U {l = m₁} dG))
                 (CommonLift.u₀≡ cl)
                 step
                 (CommonLift.v₀≡v₁ cl))
        go : LiftStep G _ n₁ k v₁ (T.U k₁)
          -> Eq k₁ n₁
          -> TermUniqResult G _ (T.Lift m₁ k₁ _) _ (T.U m₁)
        go (trivial e ctm) refl =
          wrap (Eq-transport
                 (\ kk -> LiftStep G (T.Lift m₁ k₁ _) m₁ kk v₁ (T.U m₁))
                 e
                 (proper {n = _} {G = G} {u = T.Lift m₁ k₁ _}
                         {m = m₁} {k = k₁} {v = v₁} {A = T.U m₁}
                         h₁
                         (TT.conv-cong-Lift {m = m₁} {l = k₁} h₁ ctm)))
        go (proper h ctm) refl =
          let lift-cong = TT.conv-cong-Lift {m = m₁} {l = k₁} h₁ ctm
              v₁-typed : TT.HasType G v₁ (T.U k)
              v₁-typed = TM.presup-r-ConvTm (CommonLift.v₀≡v₁ cl)
              ll-eq = TT.conv-Lift-Lift {nu = m₁} {m = k₁} {l = k}
                                         h h₁ v₁-typed
              composite = TT.conv-trans lift-cong ll-eq
              k<m₁ : Lt k m₁
              k<m₁ = Lt-trans-Lt {a = k} {b = k₁} {c = m₁} h h₁
          in wrap (proper {n = _} {G = G} {u = T.Lift m₁ k₁ _}
                          {m = m₁} {k = k} {v = v₁} {A = T.U m₁}
                          k<m₁ composite)

------------------------------------------------------------------------
-- Remaining UCode-against-non-Lift impossibilities are already
-- absurd (covered by the cross-shape () patterns earlier).
-- Note: (UCode, Lift) and (Lift, UCode) are absorbed into the (Lift, *)
-- and (*, Lift) cases above.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- type-uniq: complete proof, mutually recursive with term-uniq.
------------------------------------------------------------------------

-- (U, U)
type-uniq (TT.is-Ty-U {l = l1} dG) (TT.is-Ty-U {l = l2} _) refl =
  TT.conv-Ty-refl (TT.is-Ty-U {l = l1} dG)

-- (U, Pi) — impossible (erasure heads U vs Pi)
type-uniq (TT.is-Ty-U _) (TT.is-Ty-Pi _ _) ()

-- (Pi, U) — impossible
type-uniq (TT.is-Ty-Pi _ _) (TT.is-Ty-U _) ()

-- (Pi, Pi)
type-uniq (TT.is-Ty-Pi {A = A1} {B = B1} dA1 dB1)
          (TT.is-Ty-Pi {A = A2} {B = B2} dA2 dB2) eq =
  let mkSigma eqA eqB = R-Pi-inj eq
      cA = type-uniq dA1 dA2 eqA
      dB2' = TM.ctx-conv-IsType dA2 dA1 (TT.conv-Ty-sym cA) dB2
      cB = type-uniq dB1 dB2' eqB
  in TM.mk-conv-Ty-Pi cA cB

-- (X, El a) and (El a, X)
type-uniq dB@(TT.is-Ty-U _) (TT.is-Ty-El da) eq = uniq-El dB da eq
type-uniq dB@(TT.is-Ty-Pi _ _) (TT.is-Ty-El da) eq = uniq-El dB da eq
type-uniq (TT.is-Ty-El da) dB@(TT.is-Ty-U _) eq =
  TT.conv-Ty-sym (uniq-El dB da (Eq-sym eq))
type-uniq (TT.is-Ty-El da) dB@(TT.is-Ty-Pi _ _) eq =
  TT.conv-Ty-sym (uniq-El dB da (Eq-sym eq))
type-uniq dB@(TT.is-Ty-El _) (TT.is-Ty-El da) eq = uniq-El dB da eq

------------------------------------------------------------------------
-- uniq-El: by cases on B, and on the code a when B is U or Pi.
------------------------------------------------------------------------

-- (El a1, a2)
uniq-El {G = G} {a = a2} {l = l2} (TT.is-Ty-El {a = a1} {l = l1} da1)
        da2 eq =
  case-tu (term-uniq da1 da2 eq)
  where
    case-tu : TermUniqResult G a1 a2 (T.U l1) (T.U l2)
      -> TT.ConvTy G (T.El l1 a1) (T.El l2 a2)
    case-tu (inl (mkSigma cTy ctm)) =
      let l1≡l2 = U-inj-Ty-T cTy
          elConv : TT.ConvTy G (T.El l1 a1) (T.El l1 a2)
          elConv = TT.conv-Ty-El {l = l1} ctm
      in Eq-transport (\ k -> TT.ConvTy G (T.El l1 a1) (T.El k a2))
           l1≡l2 elConv
    case-tu (inr cl) =
      let n0 = CommonLift.n₀ cl
          n1 = CommonLift.n₁ cl
          k  = CommonLift.k  cl
          v0 = CommonLift.v₀ cl
          v1 = CommonLift.v₁ cl
          l1≡n0 = U-inj-Ty-T (CommonLift.A₀≡U cl)
          l2≡n1 = U-inj-Ty-T (CommonLift.A₁≡U cl)
          step-a1 : TT.ConvTy G (T.El l1 a1) (T.El k v0)
          step-a1 = step-from-LiftStep l1 n0 k v0 a1
                      l1≡n0 (CommonLift.u₀≡ cl)
          step-a2 : TT.ConvTy G (T.El l2 a2) (T.El k v1)
          step-a2 = step-from-LiftStep l2 n1 k v1 a2
                      l2≡n1 (CommonLift.u₁≡ cl)
          v-conv : TT.ConvTy G (T.El k v0) (T.El k v1)
          v-conv = TT.conv-Ty-El {l = k} (CommonLift.v₀≡v₁ cl)
      in TT.conv-Ty-trans step-a1
           (TT.conv-Ty-trans v-conv (TT.conv-Ty-sym step-a2))
      where
        step-from-LiftStep : (l m k' : Nat) (v a : T.Expr _)
          -> Eq l m -> LiftStep G a m k' v (T.U l)
          -> TT.ConvTy G (T.El l a) (T.El k' v)
        step-from-LiftStep l m k' v a refl (trivial m≡k' tm) =
          Eq-transport (\ j -> TT.ConvTy G (T.El l a) (T.El j v))
            m≡k' (TT.conv-Ty-El {l = l} tm)
        step-from-LiftStep l m k' v a refl (proper k'<m tm) =
          let invL = inv-Lift (TM.presup-r-ConvTm tm)
              ELLift : TT.ConvTy G (T.El m (T.Lift m k' v)) (T.El k' v)
              ELLift = TT.conv-Ty-El-Lift {m = m} {l = k'}
                         (InvLift.h invL) (InvLift.da invL)
          in TT.conv-Ty-trans (TT.conv-Ty-El {l = l} tm) ELLift

-- (U, El a) — case on shape of a
uniq-El {a = T.Var i} (TT.is-Ty-U {l = l1} dG)
          da ()
uniq-El {a = T.Pi A' B'} (TT.is-Ty-U {l = l1} dG)
          da eq =
  absurd (no-Pi-HasType da)
uniq-El {a = T.U l'} (TT.is-Ty-U {l = l1} dG)
          da eq =
  absurd (no-U-HasType da)
uniq-El {a = T.El l' a'} (TT.is-Ty-U {l = l1} dG)
          da eq =
  absurd (no-El-HasType da)
uniq-El {a = T.Lam _ _ _} (TT.is-Ty-U {l = l1} dG)
          da ()
uniq-El {a = T.App _ _ _ _} (TT.is-Ty-U {l = l1} dG)
          da ()
uniq-El {a = T.PiCode _ _ _} (TT.is-Ty-U {l = l1} dG)
          da ()
uniq-El {G = G} {a = T.UCode m l'} (TT.is-Ty-U {l = l1} dG)
          da refl =
  let r = inv-UCode da
      m≡l2 = U-inj-Ty-T (InvUCode.Tconv r)
  in Eq-transport (\ k -> TT.ConvTy G (T.U l1) (T.El k (T.UCode m l1)))
       m≡l2
       (TT.conv-Ty-sym (TT.conv-Ty-El-UCode {m = m} {l = l1}
                                            (InvUCode.dG r) (InvUCode.h r)))
uniq-El {G = G} {a = T.Lift m k a''} (TT.is-Ty-U {l = l1} dG)
          da eq =
  let r = inv-Lift da
      m≡l2 = U-inj-Ty-T (InvLift.Tconv r)
      h = InvLift.h r
      da'' = InvLift.da r
      recur : TT.ConvTy G (T.U l1) (T.El k a'')
      recur = uniq-El (TT.is-Ty-U {l = l1} dG) da'' eq
      shrink : TT.ConvTy G (T.El m (T.Lift m k a'')) (T.El k a'')
      shrink = TT.conv-Ty-El-Lift {m = m} {l = k} h da''
      bridge : TT.ConvTy G (T.U l1) (T.El m (T.Lift m k a''))
      bridge = TT.conv-Ty-trans recur (TT.conv-Ty-sym shrink)
  in Eq-transport (\ j -> TT.ConvTy G (T.U l1) (T.El j (T.Lift m k a'')))
       m≡l2 bridge

-- (Pi, El a) — case on shape of a
uniq-El {a = T.Var i} (TT.is-Ty-Pi {A = A1} {B = B1} dA1 dB1)
          da ()
uniq-El {a = T.Pi A' B'} (TT.is-Ty-Pi dA1 dB1)
          da eq =
  absurd (no-Pi-HasType da)
uniq-El {a = T.U l'} (TT.is-Ty-Pi dA1 dB1)
          da eq =
  absurd (no-U-HasType da)
uniq-El {a = T.El l' a'} (TT.is-Ty-Pi dA1 dB1)
          da eq =
  absurd (no-El-HasType da)
uniq-El {a = T.Lam _ _ _} (TT.is-Ty-Pi dA1 dB1)
          da ()
uniq-El {a = T.App _ _ _ _} (TT.is-Ty-Pi dA1 dB1)
          da ()
uniq-El {a = T.UCode _ _} (TT.is-Ty-Pi dA1 dB1)
          da ()
uniq-El {G = G} {a = T.PiCode l' a' b'} (TT.is-Ty-Pi {A = A1} {B = B1} dA1 dB1)
          da eq =
  let mkSigma eqA eqB = R-Pi-inj eq
      r = inv-PiCode da
      l'≡l2 = U-inj-Ty-T (InvPiCode.Tconv r)
      da' = InvPiCode.da r
      db' = InvPiCode.db r
      a'-IT = TT.is-Ty-El {l = l'} da'
      b'-IT = TT.is-Ty-El {l = l'} db'
      cA : TT.ConvTy G A1 (T.El l' a')
      cA = uniq-El dA1 da' eqA
      db'-inA1 : TT.HasType (TT.extend G A1) b' (T.U l')
      db'-inA1 = TM.ctx-conv-HasType a'-IT dA1 (TT.conv-Ty-sym cA) db'
      cB : TT.ConvTy (TT.extend G A1) B1 (T.El l' b')
      cB = uniq-El dB1 db'-inA1 eqB
      bridge : TT.ConvTy G (T.Pi A1 B1) (T.Pi (T.El l' a') (T.El l' b'))
      bridge = TM.mk-conv-Ty-Pi cA cB
      elPiCode : TT.ConvTy G (T.El l' (T.PiCode l' a' b'))
                              (T.Pi (T.El l' a') (T.El l' b'))
      elPiCode = TT.conv-Ty-El-PiCode {l = l'} da' db'
      result : TT.ConvTy G (T.Pi A1 B1) (T.El l' (T.PiCode l' a' b'))
      result = TT.conv-Ty-trans bridge (TT.conv-Ty-sym elPiCode)
  in Eq-transport (\ j -> TT.ConvTy G (T.Pi A1 B1)
                                     (T.El j (T.PiCode l' a' b')))
       l'≡l2 result
uniq-El {G = G} {a = T.Lift m k a''} (TT.is-Ty-Pi {A = A1} {B = B1} dA1 dB1)
          da eq =
  let r = inv-Lift da
      m≡l2 = U-inj-Ty-T (InvLift.Tconv r)
      h = InvLift.h r
      da'' = InvLift.da r
      recur : TT.ConvTy G (T.Pi A1 B1) (T.El k a'')
      recur = uniq-El (TT.is-Ty-Pi dA1 dB1) da'' eq
      shrink : TT.ConvTy G (T.El m (T.Lift m k a'')) (T.El k a'')
      shrink = TT.conv-Ty-El-Lift {m = m} {l = k} h da''
      bridge : TT.ConvTy G (T.Pi A1 B1) (T.El m (T.Lift m k a''))
      bridge = TT.conv-Ty-trans recur (TT.conv-Ty-sym shrink)
  in Eq-transport (\ j -> TT.ConvTy G (T.Pi A1 B1)
                                     (T.El j (T.Lift m k a'')))
       m≡l2 bridge
