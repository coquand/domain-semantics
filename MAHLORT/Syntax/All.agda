{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Syntax/All.agda
--
-- Metatheory of the Tarski Mahlo universe (MAHLORT/TarskiTyping):
-- renaming/substitution algebra, weakening, substitution, well-formed
-- contexts, context conversion, operator typings and congruences,
-- code congruences with moving f, g (by reflection), functionality,
-- presupposition.  Port of MAHLOINJ/Syntax.
------------------------------------------------------------------------

module MAHLORT.Syntax.All where

import MAHLORT.Syntax.SubstLemmas
import MAHLORT.Syntax.Lemmas
import MAHLORT.Syntax.Weaken
import MAHLORT.Syntax.Subst
import MAHLORT.Syntax.Wf
import MAHLORT.Syntax.CtxConv
import MAHLORT.Syntax.Ops
import MAHLORT.Syntax.CodeCong
import MAHLORT.Syntax.Funct
import MAHLORT.Syntax.Presup
import MAHLORT.Syntax.Inv
