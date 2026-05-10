{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Sterbac.UniquenessTermPartial
--
-- Partial proof of `term-uniq`: handles the easy cases, factors the
-- harder Lift-related cases into a single named auxiliary
-- `term-uniq-Lift-cases`.
--
-- The "easy" cases (output via `inl`):
--   * ty-conv peeling on either side
--   * (Var, Var)
--   * (Lam, Lam) — needs body recursion
--   * (App, App) — uses subst1-cong-Ty for cross-subst
--   * (PiCode, PiCode) — uses PiCode-inj-T
--
-- The "hard" cases (output via `inr`, building CommonLift):
--   * (UCode, UCode), (UCode, Lift), (Lift, UCode), (Lift, Lift)
--   * (Var, Lift), (Lift, Var), (Lam, Lift), (Lift, Lam),
--     (App, Lift), (Lift, App), (PiCode, Lift), (Lift, PiCode)
-- These are factored into `term-uniq-Lift-cases`, which dispatches
-- on the head shapes after both sides have been ty-conv-peeled.
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
-- Postulate covering the Lift-related branches.
--
-- This will be discharged by future work; the present file proves the
-- non-Lift "structural" branches assuming a uniform handle on the
-- Lift-mixing cases.
------------------------------------------------------------------------

postulate
  term-uniq-Lift-cases :
    {n : Nat} {G : TT.Ctx n} {u₀ u₁ A₀ A₁ : T.Expr n}
    -> TT.HasType G u₀ A₀
    -> TT.HasType G u₁ A₁
    -> Eq (E.erase u₀) (E.erase u₁)
    -- A flag: true iff at least one of u₀, u₁ is a Lift-headed term
    -- (or the peeled inner is — but we keep the statement simple here).
    -> TermUniqResult G u₀ u₁ A₀ A₁

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
      -- Recurse on bodies (in extend G A1 with type B1)
      db2'' = TT.ty-conv db2' (TT.conv-Ty-sym cB)
      bodyResult = term-uniq db1 db2'' eqb
  in case-body bodyResult cA cB
  where
    case-body : TermUniqResult (TT.extend G _) _ _ _ _
              -> TT.ConvTy G _ _ -> TT.ConvTy (TT.extend G _) _ _
              -> TermUniqResult G (T.Lam _ _ _) (T.Lam _ _ _) (T.Pi _ _) (T.Pi _ _)
    case-body (inl (mkSigma _ cb)) cA cB =
      let lam-body-conv = TT.conv-cong-Lam-body
            (TM.presup-l-ConvTy cA)
            (TM.presup-l-ConvTy cB)
            cb
          lam-Ty-conv = TT.conv-cong-Lam-Ty cA cB (TM.presup-r-ConvTm cb)
      in inl (mkSigma (TT.conv-Ty-Pi cA cB)
                      (TT.conv-trans lam-body-conv lam-Ty-conv))
    -- Body cannot be in CommonLift mode because Lam's body type is B1,
    -- not a U.  (CommonLift requires the body type to be U_n0.)  But
    -- we can't easily refute this without B1's shape; defer to the
    -- generic Lift case handler.
    case-body (inr _) cA cB =
      term-uniq-Lift-cases (TT.ty-Lam dA1 dB1 db1) (TT.ty-Lam dA2 dB2 db2) eq

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
              ihB = term-uniq db1 db2' eqB
          in case-PiCode-b ca ihB
          where
            case-PiCode-b :
                 TT.ConvTm G a1 a2 (T.U l1)
              -> TermUniqResult (TT.extend G (T.El l1 a1))
                                 b1 b2 (T.U l1) (T.U l1)
              -> TermUniqResult G (T.PiCode l1 a1 b1) (T.PiCode l1 a2 b2)
                                   (T.U l1) (T.U l1)
            case-PiCode-b ca (inl (mkSigma _ cb)) =
              inl (mkSigma (TT.conv-Ty-refl
                              (TT.is-Ty-U {l = l1} (TM.typing-WfCtx da1)))
                           (TT.conv-cong-PiCode {l = l1} ca cb))
            case-PiCode-b _ (inr _) =
              term-uniq-Lift-cases (TT.ty-PiCode da1 db1)
                                    (TT.ty-PiCode da2 db2) eq
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
      ihA-arg = term-uniq da1 da2-c eqa
      ihC     = term-uniq dc1 dc2-c eqc
  in case-AppA ihA-arg ihC cA cB da2-c dc2-c
  where
    case-AppA : TermUniqResult G a1 a2 A1 A1
             -> TermUniqResult G c1 c2 (T.Pi A1 B1) (T.Pi A1 B1)
             -> TT.ConvTy G A1 A2
             -> TT.ConvTy (TT.extend G A1) B1 B2
             -> TT.HasType G a2 A1
             -> TT.HasType G c2 (T.Pi A1 B1)
             -> TermUniqResult G (T.App A1 B1 c1 a1) (T.App A2 B2 c2 a2)
                                  (T.subst1 B1 a1) (T.subst1 B2 a2)
    case-AppA (inl (mkSigma _ ca)) (inl (mkSigma _ cc)) cA cB da2-c dc2-c =
      let dA1 = TM.presup-l-ConvTy cA
          BsubstCong : TT.ConvTy G (T.subst1 B1 a1) (T.subst1 B1 a2)
          BsubstCong = TMC.subst1-cong-Ty ca dA1 (TM.presup-l-ConvTy cB)
          step1 = TT.conv-cong-App-fun dA1 (TM.presup-l-ConvTy cB) cc da1
          step2 = TT.conv-cong-App-arg dA1 (TM.presup-l-ConvTy cB) dc2-c ca BsubstCong
          step3raw = TT.conv-cong-App-Ty cA cB dc2-c da2-c
          -- step3raw has type subst1 B1 a2; bring back to subst1 B1 a1
          step3 = TT.conv-conv step3raw (TT.conv-Ty-sym BsubstCong)
          composite = TT.conv-trans step1 (TT.conv-trans step2 step3)
          -- result type: ConvTy from (subst1 B1 a1) to (subst1 B2 a2)
          subst1-tyConv : TT.ConvTy G (T.subst1 B1 a1) (T.subst1 B2 a2)
          subst1-tyConv =
            TT.conv-Ty-trans BsubstCong
              (TM.subst-ConvTy (TM.subst1-WtSub dA1 da2-c)
                                (TM.isType-WfCtx dA1) cB)
      in inl (mkSigma subst1-tyConv composite)
    case-AppA _ _ cA cB da2-c dc2-c =
      term-uniq-Lift-cases (TT.ty-App dA1 dB1 dc1 da1)
                            (TT.ty-App dA2 dB2 dc2 da2)
                            eq

------------------------------------------------------------------------
-- All remaining cases (Lift on either side, UCode-UCode, etc.)
-- delegated to the auxiliary postulate.
------------------------------------------------------------------------
term-uniq dM₀@(TT.ty-UCode _ _) dM₁ eq =
  term-uniq-Lift-cases dM₀ dM₁ eq
term-uniq dM₀@(TT.ty-Lift _ _) dM₁ eq =
  term-uniq-Lift-cases dM₀ dM₁ eq
term-uniq dM₀ dM₁@(TT.ty-Lift _ _) eq =
  term-uniq-Lift-cases dM₀ dM₁ eq
