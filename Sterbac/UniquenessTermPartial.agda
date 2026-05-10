{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Sterbac.UniquenessTermPartial
--
-- Partial proof of `term-uniq`.
--
-- Discharged cases:
--   * ty-conv peeling on either side
--   * (Var, Var)
--   * (Lam, Lam)              -- recurses on body
--   * (App, App)              -- uses subst1-cong-Ty for cross-subst
--   * (PiCode, PiCode)        -- uses PiCode-inj-T
--   * cross-shape impossible cases (Var-vs-Lam, etc.)
--   * (UCode, UCode)          -- direct CommonLift via canonical
--                                witness UCode (suc l) l : U (suc l)
--   * (Lift, *)               -- recurse on inner of left Lift,
--                                build CommonLift via Lift-cong
--                                and conv-Lift-Lift
--   * (*, Lift)               -- symmetric to (Lift, *)
--
-- Remaining `term-uniq-Lift-cases` postulate: now used in exactly
-- one place — the (PiCode, PiCode) case when the inner `a` recursion
-- returns CommonLift, i.e., when the two PiCodes have potentially
-- different outer universe levels.  Building a CommonLift on the
-- outer PiCodes requires constructing a "common base" PiCode at a
-- shared lower level; deferred for future work.
------------------------------------------------------------------------

module Sterbac.UniquenessTermPartial where

open import Sterbac.Basic
import Sterbac.RussellSyntax  as R
import Sterbac.TarskiSyntax   as T
import Sterbac.TarskiTyping   as TT
import Sterbac.Erasure        as E
import Sterbac.TarskiMeta     as TM
import Sterbac.TarskiMetaCong as TMC
open import Sterbac.Postulates
open import Sterbac.Uniqueness hiding (term-uniq)

------------------------------------------------------------------------
-- Auxiliary postulate.  After dismantling the (Lam, Lam), (App, App),
-- and (PiCode, PiCode) inr-fallbacks via `extract-conv-same`, this
-- postulate is used only in ONE place: the (PiCode, PiCode) case
-- when the inner-`a` recursion returns CommonLift with potentially
-- different outer universe levels (l1 ≠ l2 is permitted, since
-- `erase (PiCode l a b) = R.Pi (erase a) (erase b)` discards `l`).
------------------------------------------------------------------------

postulate
  term-uniq-Lift-cases :
    {n : Nat} {G : TT.Ctx n} {u₀ u₁ A₀ A₁ : T.Expr n}
    -> TT.HasType G u₀ A₀
    -> TT.HasType G u₁ A₁
    -> Eq (E.erase u₀) (E.erase u₁)
    -> TermUniqResult G u₀ u₁ A₀ A₁

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

{-# TERMINATING #-}
term-uniq : TermUniqStatement

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
      lam-Ty-conv = TT.conv-cong-Lam-Ty cA cB (TM.presup-r-ConvTm cb)
  in inl (mkSigma (TT.conv-Ty-Pi cA cB)
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
                          (TT.conv-cong-PiCode {l = l1} ca cb))
    case-PiCode-a eqB (inr _) =
      term-uniq-Lift-cases (TT.ty-PiCode da1 db1)
                            (TT.ty-PiCode da2 db2) eq

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
      dc2-c = TT.ty-conv dc2 (TT.conv-Ty-sym (TT.conv-Ty-Pi cA cB))
      ca = extract-conv-same (term-uniq da1 da2-c eqa)
      cc = extract-conv-same (term-uniq dc1 dc2-c eqc)
      BsubstCong : TT.ConvTy G (T.subst1 B1 a1) (T.subst1 B1 a2)
      BsubstCong = TMC.subst1-cong-Ty ca dA1 dB1
      step1 = TT.conv-cong-App-fun dA1 dB1 cc da1
      step2 = TT.conv-cong-App-arg dA1 dB1 dc2-c ca BsubstCong
      step3raw = TT.conv-cong-App-Ty cA cB dc2-c da2-c
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
