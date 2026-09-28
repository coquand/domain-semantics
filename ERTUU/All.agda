{-# OPTIONS --without-K --safe #-}
-- Everything in ERTUU (U : U): §4.2 Tarski ⇔ Russell and §4.3 T_R ⇔ T_P.
module ERTUU.All where
import ERTUU.Equivalence      -- Thm 4.13 (Tarski ⇔ Russell)
import ERTUU.PiInjectivityR   -- Π-injectivity of T_R (domain model adequacy)
import ERTUU.StripDeriv       -- Thm 4.15
import ERTUU.StripUniq        -- Lemma 4.17/4.18
import ERTUU.SectionR         -- Thm 4.19
