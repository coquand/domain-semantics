{-# OPTIONS --without-K #-}
-- BCDE4: Russell, cumulative universes U_l (bcde.pdf App. B) + internal levels, level products [α]A / ⟨α⟩u / t l,
-- constraint products [ψ]A / ⟨ψ⟩t, ∅ and the loop-collapse rules
-- (bcde.pdf Fig. 12–14, App. C), with the Bezem–Coquand loop checker.
module BCDE4.All where
import BCDE4.Model.RussellSound   -- soundness of the guard-aware domain model
import BCDE4.RussellLsub          -- level-substitution lemma
import BCDE4.RussellLeq           -- invariance under level equality (syntactic)
import BCDE4.Adeq.Driver          -- adequacy (fundamental theorem), all level substitutions
import BCDE4.PiInjectivityR       -- Π-, [α]- and U-injectivity in loop-free contexts
import BCDE4.LC.Decide            -- Bezem–Coquand: decidability of level equality
import BCDE4.LC.Test              -- closed tests of the decision procedure
import BCDE4.Main                 -- the above with the level codes discharged
import BCDE4.CollapseTest         -- [α⁺≤α](U→U) ≡ [α⁺≤α]U in a loop-free context
import BCDE4.LeqTest              -- level equality, U_α = U_β, cumulativity; closed examples
import BCDE4.LC.Loop              -- decidability of loops (decLoop)
-- Tarski side and Russell ⇔ Tarski (binders ⟨ψ⟩t, ⟨α⟩u, t l annotated)
import BCDE4.TarskiTyping         -- T_T: El, codes Π^l/U^m_l/↑^m_l/∅^l, lift equations
import BCDE4.EraseDeriv           -- Lemma 4.6: erasure preserves all judgements
import BCDE4.TarskiMetaCong       -- Tarski metatheory (renaming, substitution, levels, presuppositions)
import BCDE4.TarskiInj            -- U-injectivity for T_T (loop-free contexts)
import BCDE4.Uniqueness           -- Lemma 4.10: uniqueness up to conversion / agreement at the join
import BCDE4.Equivalence          -- Theorem 4.13: section of erasure; the equivalence record
-- T_P side (Sterbac 4.15/4.18/4.19 analogues)
import BCDE4.GrdNoConf            -- [ψ]-injectivity and no-confusion, in the guard-β-aware form
import BCDE4.PTyping              -- T_P: unannotated Russell (bcde.pdf's own presentation), with guard η
import BCDE4.StripDeriv           -- Theorem 4.15: strip : T_R -> T_P preserves all judgements
import BCDE4.StripUniqNF          -- Lemma 4.18 without normalisation (η-coercions, joins; Coerce, JoinProps)
import BCDE4.SectionR             -- Theorem 4.19: every T_P judgement lifts into every T_R context over it
import BCDE4.StripUniqNFTest      -- Gap417 with levels, also under ⟨ψ⟩ and ⟨β⟩
