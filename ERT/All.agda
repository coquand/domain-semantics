{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.All — every module of ERT/ (Equivalence Russell–Tarski)
------------------------------------------------------------------------

module ERT.All where

-- §4.2: Tarski T_T ⇔ Russell T_R
import ERT.EraseDeriv             -- Lemma 4.6: erasure preserves all judgements
import ERT.Injectivity            -- U-injectivity and U/Π no-confusion, from the model
import ERT.UniquenessTermPartial  -- Lemma 4.10 (type-uniq, term-uniq, uniq-El)
import ERT.Equivalence            -- Theorem 4.13: section of erasure
-- §4.3: annotated T_R ⇔ unannotated T_P
import ERT.PiInjectivityR         -- Π-injectivity of T_R, from domain-model adequacy
import ERT.StripDeriv             -- Theorem 4.15
import ERT.Gap417                 -- the gap in the paper's proof of Lemma 4.17
import ERT.StripUniq              -- Lemma 4.18 under weak normalisation of T_P (superseded)
import ERT.SubjectReductionR
import ERT.StripUniqNF            -- Lemma 4.18 without normalisation
import ERT.SectionR               -- Theorem 4.19
import ERT.StripUniqNFTest        -- the Gap417 example, settled
