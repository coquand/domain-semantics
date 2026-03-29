{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- FinFunGeneric.agda
--
-- Generic FinFun operations that depend on FinEl only through the
-- semilattice interface (Sup, LeCode, Comp, Coherent, leFinEl, etc.)
-- but NEVER pattern-match on specific FinEl constructors
-- (UCode, PropCode, FunEl, PiCode).
--
-- The goal is to identify and collect the operations that would not
-- need modification when adding new type formers (e.g., Sigma).
--
-- LIMITATION: Most of these operations live inside {-# TERMINATING #-}
-- mutual blocks in PaperSemantics.agda together with constructor-specific
-- functions (Comp, LeCode, Coherent, etc.). They cannot be literally
-- extracted as standalone definitions because they are mutually recursive
-- with the specific ones.
--
-- What this file DOES: re-exports and provides thin wrappers for
-- the generic operations that ARE defined outside mutual blocks,
-- plus standalone generic lemmas.  Everything here type-checks
-- without postulates and never mentions UCode/PropCode/FunEl/PiCode.
------------------------------------------------------------------------

module FinFunGeneric where

open import Basic
  using ( Top ; tt ; Empty
        ; Nat ; zero ; suc ; max
        ; Le ; Le-refl ; Le-suc ; Le-trans ; Le-max-l ; Le-max-r
        ; Eq ; refl ; Eq-transport ; Eq-sym ; Eq-cong
        ; Sigma ; mkSigma ; fst ; snd ; Pair
        ; List ; nil ; cons ; All
        ; FinEl ; Bot ; FinFun
        ; rk ; rkFun
        ; min ; isPos ; min-isPos
        ; pair-eq ; cons-eq
        )

open import PaperSemantics
  using ( append
        -- From the main mutual block (FinEl-specific at top level,
        -- but the FinFun-level projections are generic):
        ; leFinEl ; leFun
        ; EvalFun ; EvalFun-step
        ; LeCode ; LeFunCode
        -- Compatibility
        ; Comp ; CompFun ; CompStepFun ; CompStepStep
        -- Coherence
        ; CoherentFun ; CoherentFunTail ; CFTcons ; mkCFT ; CoherentWith
        ; cft-from-cf
        -- Soundness / completeness
        ; leFinEl-sound ; leFun-sound
        ; leFinEl-complete ; leFun-complete
        ; isPos-min
        -- Comp lemmas
        ; comp-Bot-r ; comp-Bot-l
        ; comp-Sup ; comp-Sup-sym
        ; Comp-sym ; CompFun-sym ; CompFun-sym-col ; CompFun-drop-col
        ; Comp-refl ; CompFun-refl
        ; Comp-down
        -- LeCode lemmas
        ; LeCode-Bot
        ; LeCode-Sup-Bot
        ; LeCode-Sup-left ; LeCode-Sup-right ; LeCode-Sup-lub
        ; LeCode-trans ; LeCode-refl
        ; LeCode-Comp
        ; LeCode-trans-to-Bot
        -- Generic standalone lemmas
        ; compStepFun-append ; compFun-append
        ; LeFunCode-append-nil
        ; coherentWith-to-compStepFun ; compStepFun-to-coherentWith
        ; CompFun-cons-right
        ; coherentWith-append
        ; append-assoc
        -- EvalFun lemmas
        ; EvalFun-step-le-Bot ; EvalFun-le-Bot
        ; LeFunCode-trans-to-nil
        ; LeFunCode-nil-CompFun ; LeFunCode-nil-CompStepFun
        ; LeCode-Bot-Comp
        ; LeFunCode-CompFun-trans ; build-CompStepFun ; extract-col
        ; EvalFun-guarded-comp ; EvalFun-guarded-comp-step
        ; Comp-value-EvalFun ; Comp-value-EvalFun-step
        ; comp-EvalFun ; comp-EvalFun-step
        ; EvalFun-append-eq ; EvalFun-append-eq-step
        ; Sup-assoc
        ; Coherent-Sup
        ; CoherentFunTail-append ; CoherentFun-append
        ; Coherent-EvalFun ; Coherent-EvalFun-step
        ; LeFunCode-refl ; LeFunCode-refl-head-step
        ; LeFunCode-cons-lift
        ; EvalFun-cons-mono ; EvalFun-cons-mono-step
        ; LeFunCode-trans
        ; LeFunCode-nil-any
        ; EvalFun-mon ; EvalFun-mon-step
        ; LeFunCode-append-combine
        ; LeFunCode-append-left ; LeFunCode-append-right
        ; LeFunCode-append-right-go
        ; EvalFun-mon-arg ; EvalFun-mon-arg-step ; EvalFun-mon-arg-suc
        )

------------------------------------------------------------------------
-- Section 1: Truly standalone generic lemmas
--
-- These are operations that ONLY use FinFun structure (nil/cons)
-- and Nat structure (zero/suc), never FinEl constructors.
-- They are defined outside mutual blocks in PaperSemantics.agda
-- and can be used directly.
------------------------------------------------------------------------

-- Re-export: append is generic (only case-splits on nil/cons of FinFun)
-- append : FinFun -> FinFun -> FinFun

-- Re-export: compStepFun-append distributes CompStepFun over append
-- compStepFun-append : (s : Pair FinEl FinEl) (g h : FinFun) ->
--   CompStepFun s g -> CompStepFun s h -> CompStepFun s (append g h)

-- Re-export: compFun-append distributes CompFun over append
-- compFun-append : (g h j : FinFun) ->
--   CompFun g h -> CompFun g j -> CompFun g (append h j)

-- Re-export: LeFunCode-append-nil
-- LeFunCode-append-nil : (g h : FinFun) ->
--   LeFunCode g nil -> LeFunCode h nil -> LeFunCode (append g h) nil

-- Re-export: coherentWith-to-compStepFun / compStepFun-to-coherentWith
-- These two show CoherentWith and CompStepFun are the same structure.

-- Re-export: coherentWith-append
-- coherentWith-append : (q : Pair FinEl FinEl) (qs h : FinFun) ->
--   CoherentWith q qs -> CoherentWith q h -> CoherentWith q (append qs h)

-- Re-export: append-assoc
-- append-assoc : (f g h : FinFun) ->
--   Eq (append f (append g h)) (append (append f g) h)

-- Re-export: LeFunCode-append-combine
-- LeFunCode-append-combine : (g h k : FinFun) ->
--   LeFunCode g k -> LeFunCode h k -> LeFunCode (append g h) k

-- Re-export: cft-from-cf
-- cft-from-cf : (g : FinFun) -> CoherentFun g -> CoherentFunTail g

------------------------------------------------------------------------
-- Section 2: New generic lemmas (not in PaperSemantics.agda)
--
-- These demonstrate the kind of lemmas that belong in a generic
-- FinFun module — they only use the FinFun list structure.
------------------------------------------------------------------------

-- Generic: CompStepFun is reflexive when the step is self-compatible
compStepFun-refl-from-comp : (s : Pair FinEl FinEl) (g : FinFun) ->
  Comp (snd s) (snd s) -> CoherentWith s g -> CompStepFun s g
compStepFun-refl-from-comp s nil css cw = tt
compStepFun-refl-from-comp s (cons r rs) css cw =
  mkSigma (fst cw) (compStepFun-refl-from-comp s rs css (snd cw))

-- Generic: CompFun for nil on the right is trivial
compFun-nil-right : (g : FinFun) -> CompFun g nil
compFun-nil-right nil         = tt
compFun-nil-right (cons s ss) = mkSigma tt (compFun-nil-right ss)

-- Generic: LeFunCode nil on the left is trivial
leFunCode-nil-left : (h : FinFun) -> LeFunCode nil h
leFunCode-nil-left h = tt

-- Generic: CompStepFun is preserved by weakening the tail
compStepFun-weaken : (s : Pair FinEl FinEl) (t : Pair FinEl FinEl)
  (g : FinFun) -> CompStepFun s (cons t g) -> CompStepFun s g
compStepFun-weaken s t g csf = snd csf

-- Generic: Extract head compatibility from CompStepFun
compStepFun-head : (s t : Pair FinEl FinEl) (g : FinFun) ->
  CompStepFun s (cons t g) -> CompStepStep s t
compStepFun-head s t g csf = fst csf

-- Generic: CompFun is preserved under tail of left argument
compFun-tail : (s : Pair FinEl FinEl) (ss h : FinFun) ->
  CompFun (cons s ss) h -> CompFun ss h
compFun-tail s ss h cf = snd cf

-- Generic: Extract CompStepFun from head of CompFun
compFun-head-step : (s : Pair FinEl FinEl) (ss h : FinFun) ->
  CompFun (cons s ss) h -> CompStepFun s h
compFun-head-step s ss h cf = fst cf

-- Generic: LeFunCode distributes over append on the left
leFunCode-append-left-split : (g h k : FinFun) ->
  LeFunCode (append g h) k ->
  Pair (LeFunCode g k) (LeFunCode h k)
leFunCode-append-left-split nil         h k le = mkSigma tt le
leFunCode-append-left-split (cons p ps) h k le =
  let ih = leFunCode-append-left-split ps h k (snd le)
  in mkSigma (mkSigma (fst le) (fst ih)) (snd ih)

-- Generic: CoherentWith for nil is trivial
coherentWith-nil : (p : Pair FinEl FinEl) -> CoherentWith p nil
coherentWith-nil p = tt

-- Generic: CoherentFunTail nil is trivial
coherentFunTail-nil : CoherentFunTail nil
coherentFunTail-nil = tt

-- Generic: Extract tail coherence
coherentFunTail-tail : (p : Pair FinEl FinEl) (ps : FinFun) ->
  CoherentFunTail (cons p ps) -> CoherentFunTail ps
coherentFunTail-tail p ps coh = CFTcons.tail-coh coh

-- Generic: length of a FinFun
lengthFun : FinFun -> Nat
lengthFun nil         = zero
lengthFun (cons p ps) = suc (lengthFun ps)

-- Generic: map over FinFun preserving structure
-- (Identity map, demonstrating the pattern)
mapFun-id : FinFun -> FinFun
mapFun-id nil         = nil
mapFun-id (cons p ps) = cons p (mapFun-id ps)

mapFun-id-eq : (g : FinFun) -> Eq (mapFun-id g) g
mapFun-id-eq nil         = refl
mapFun-id-eq (cons p ps) = cons-eq refl (mapFun-id-eq ps)

------------------------------------------------------------------------
-- Section 3: Generic EvalFun properties (re-exported)
--
-- These functions live inside mutual blocks in PaperSemantics but
-- their BODIES only case-split on FinFun (nil/cons) and Nat (zero/suc).
-- They call into the FinEl-specific functions (leFinEl, Comp, etc.)
-- but treat them as black boxes.
--
-- In a fully modular architecture, these would be parameterized over
-- the FinEl semilattice operations.
------------------------------------------------------------------------

-- EvalFun-step-le-Bot / EvalFun-le-Bot:
--   If all values ≤ Bot, evaluation yields ≤ Bot.
--   Bodies: case-split on Nat (zero/suc) and FinFun (nil/cons).

-- Comp-value-EvalFun / Comp-value-EvalFun-step:
--   If q's key ≤ xi (Coherent xi), q compatible with rest,
--   then q's value is compatible with EvalFun rest xi.
--   Bodies: case-split on FinFun (nil/cons) and Nat (zero/suc).

-- comp-EvalFun / comp-EvalFun-step:
--   Evaluations of compatible functions at same point are compatible.
--   Bodies: case-split on FinFun (nil/cons) and Nat (zero/suc).

-- EvalFun-append-eq / EvalFun-append-eq-step:
--   EvalFun (append k h) xi = Sup (EvalFun k xi) (EvalFun h xi)
--   Bodies: case-split on FinFun (nil/cons) and Nat (zero/suc).

-- Coherent-EvalFun / Coherent-EvalFun-step:
--   Evaluation of coherent function at coherent input is coherent.
--   Bodies: case-split on FinFun (nil/cons) and Nat (zero/suc).

-- LeFunCode-refl / LeFunCode-refl-head-step:
--   Reflexivity of LeFunCode.
--   Bodies: case-split on FinFun (nil/cons) and Nat (zero/suc).

-- EvalFun-mon / EvalFun-mon-step:
--   Monotonicity of EvalFun in function argument.
--   Bodies: case-split on FinFun (nil/cons) and Nat (zero/suc).

-- EvalFun-mon-arg / EvalFun-mon-arg-step / EvalFun-mon-arg-suc:
--   Monotonicity of EvalFun in element argument.
--   Bodies: case-split on FinFun (nil/cons) and Nat (zero/suc).
