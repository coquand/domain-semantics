{-# OPTIONS --without-K #-}
------------------------------------------------------------------------
-- YTest.agda  —  machine-check of the two Y (fixpoint) test terms.
--   Test 1:  Y (Lam U U)            is valid at UCode  (explicit n=1 witness)
--   Test 2:  Y (Lam U (Var fzero))  is valid only at Bot
--            (UCode is unreachable: EvalRel ... UCode -> Empty)
------------------------------------------------------------------------
module NAT.YTest where

open import NAT.Domain.Basic using
  ( Nat ; zero ; suc ; FinEl ; Bot ; UCode ; FunEl ; cons ; nil
  ; mkSigma ; fst ; snd ; Pair ; Sigma ; Top ; tt ; Empty )
open import NAT.Domain.Kernel using
  ( FinMem ; Coherent ; LeCode ; LeCode-trans ; Coherent-singleton-key
  ; Coherent-singleton-val ; FinMem-coh-u ; mkCFT )
open import NAT.Syntax.Raw using ( Expr ; Lam ; U ; Var ; Y ; Pi ; Fin ; fzero )
open import NAT.Model.Selection using ( Selection ; sel-nil ; sel-skip ; sel-take ; Edge ; EdgeIn ; here )
open import NAT.Model.Eval using
  ( EvalRel ; Approx ; EnvApprox ; emptyEnv ; extendEnv
  ; EvalRel-coh ; Lam-edgewise ; Coherent-val-LeBot-absurd )

------------------------------------------------------------------------
-- Test 1 :  Y (Lam U U)  valid at UCode
------------------------------------------------------------------------

-- The single edge  Bot |-> UCode  of  (λx.U).
lamUU-edge : EvalRel (Lam U U) emptyEnv (FunEl (cons (mkSigma Bot UCode) nil))
lamUU-edge =
  mkSigma UCode (mkSigma (mkCFT tt tt tt tt tt) (mkSigma tt (mkSigma (mkSigma tt tt) body)))
  where
    body : (u v : FinEl) -> Selection (cons (mkSigma Bot UCode) nil) u v ->
      Sigma FinEl (\ x -> Pair (LeCode x u)
                               (Pair (FinMem x UCode)
                                     (EvalRel U (extendEnv emptyEnv x) v)))
    body _ _ (sel-skip sel-nil)     = mkSigma Bot (mkSigma tt (mkSigma tt (mkSigma tt tt)))
    body _ _ (sel-take _ _ sel-nil) = mkSigma Bot (mkSigma tt (mkSigma tt (mkSigma tt tt)))

-- n = 1 witness:  UCode <= Y_1 = (λx.U) Y_0 = (λx.U) Bot = U.
test1 : EvalRel (Y (Lam U U)) emptyEnv UCode
test1 = mkSigma (suc zero) (mkSigma Bot (mkSigma (mkSigma tt tt) lamUU-edge))

------------------------------------------------------------------------
-- Test 2 :  Y (Lam U (Var fzero))  valid only at Bot
------------------------------------------------------------------------

stepId : FinEl -> FinEl -> Set
stepId p w = EvalRel (Lam U (Var fzero)) emptyEnv (FunEl (cons (mkSigma p w) nil))

-- The identity sends p |-> w only if w <= p.
idedge : (p w : FinEl) -> stepId p w -> LeCode w p
idedge p w ev =
  let ew   = Lam-edgewise U (Var fzero) emptyEnv (cons (mkSigma p w) nil) ev
      a    = fst ew
      wf   = snd (snd (snd (snd ew)))
      wpw  = wf (mkSigma p w) here
      x    = fst wpw
      lxp  = fst (snd wpw)
      memx = fst (snd (snd wpw))
      evV  = snd (snd (snd wpw))        -- (Coherent w , LeCode w x)
      cohF = EvalRel-coh (Lam U (Var fzero)) emptyEnv
               (FunEl (cons (mkSigma p w) nil)) ev
  in LeCode-trans w x p (fst evV) (FinMem-coh-u x a memx)
       (Coherent-singleton-key p w cohF) (snd evV) lxp

-- Every Kleene approximant of the identity collapses to Bot.
idApprox : (k : Nat) (u : FinEl) -> Approx stepId k u -> LeCode u Bot
idApprox zero    u ev = snd ev
idApprox (suc j) u ev =
  let p    = fst ev
      ap   = fst (snd ev)
      sp   = snd (snd ev)
      cohF = EvalRel-coh (Lam U (Var fzero)) emptyEnv
               (FunEl (cons (mkSigma p u) nil)) sp
  in LeCode-trans u p Bot
       (Coherent-singleton-val p u cohF)
       (Coherent-singleton-key p u cohF) tt
       (idedge p u sp) (idApprox j p ap)

test2 : EvalRel (Y (Lam U (Var fzero))) emptyEnv UCode -> Empty
test2 ev = Coherent-val-LeBot-absurd UCode (mkSigma tt tt) (idApprox (fst ev) UCode (snd ev))

------------------------------------------------------------------------
-- Adequacy demonstration : the fundamental theorem yields Val2 for Y.
--   Y (λx.U) : U   is VALID at the U-information UCode.
------------------------------------------------------------------------

open import NAT.Syntax.Typing using
  ( empty ; extend ; WfCtx ; wf-empty ; wf-extend ; HasType ; ty-U ; ty-Lam ; ty-Y )
open import NAT.Syntax.Reduction using ( idSub )
open import NAT.Adequacy.Helpers using ( ValidSub2 ; ValidSub2-empty ; idSub-WtSub )
open import NAT.Adequacy.Value using ( adequacySub2 )
open import NAT.Validity.Stratified using ( Val2 )
open import NAT.Domain.Kernel using ( LeCode-refl )

wfU1 : WfCtx (extend empty U)
wfU1 = wf-extend (ty-U wf-empty)

-- λx.U  :  U → U  ( = Π U (wk U) ),  in the empty context
dgUU : HasType empty (Lam U U) (Pi U U)
dgUU = ty-Lam (ty-U wf-empty) (ty-U wfU1) (ty-U wfU1)

tyYUU : HasType empty (Y (Lam U U)) U
tyYUU = ty-Y (ty-U wf-empty) dgUU

-- Fundamental theorem (adequacySub2) applied to the closed Y-term:
test-adq : Val2 empty (Y (Lam U U)) U UCode UCode
test-adq =
  adequacySub2 tyYUU idSub emptyEnv tt
    (ValidSub2-empty idSub emptyEnv) tt
    (idSub-WtSub wf-empty) wf-empty
    UCode test1
    UCode (mkSigma tt (LeCode-refl UCode tt)) tt

------------------------------------------------------------------------
-- Normalising  test-adq  (Agda C-c C-n) yields a FINITE term — it does
-- NOT chase Y's infinite unfolding, because the adequacy witness is
-- pinned to the finite Kleene index n = 1 coming from test1's EvalRel
-- evidence.  Val2 at (UCode, UCode) is a pair of Red3 = (HeadRed × ConvTm)
-- bundles, and the term-side bundle is exactly the operational story
-- "Y (λx.U) is the type U":
--
--   mkSigma
--     -- type side (T = U): U is already canonical
--     (mkRed3 headred-refl (conv-refl (ty-U wf-empty)))
--     -- term side (M = Y (Lam U U)): the head-reduction to U
--     (mkRed3
--        (headred-step headred-Y                 -- Y g  →  (λx.U) (Y g)
--          (headred-step headred-beta            -- (λx.U)(Y g)  →  U
--            headred-refl))                       -- stop: U is normal
--        (conv-trans
--           (conv-conv (conv-Y  (ty-U wf-empty) (ty-Lam …)) …)   -- Y g ≈ (λx.U)(Y g)
--           (conv-trans
--              (conv-conv (conv-beta … (ty-Y …)) …)              -- (λx.U)(Y g) ≈ U
--              (conv-refl (ty-U wf-empty)))))                    -- ≈ U
--
-- i.e. the proof's normal form literally contains the head-reduction
--   Y (λx.U)  →  (λx.U) (Y (λx.U))  →  U
-- and the matching conv-Y / conv-beta chain proving  Y (λx.U) ≈ U : U.
------------------------------------------------------------------------
