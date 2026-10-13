{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Syntax/All.agda
--
-- Metatheory of the frozen typing MAHLO/Typing.agda (phase P3,
-- syntactic part).  Imports only MAHLO.Basic, MAHLO.Syntax and
-- MAHLO.Typing.
--
--   Lemmas    syntactic equalities (OpG, RecStep, sucSub, consSub)
--   Weaken    renaming / weakening for all judgements
--   Subst     well-typed substitution; single substitution
--   Wf        well-formed contexts; types of variables
--   CtxConv   context conversion
--   Funct     functionality: convertible substitutions (CSub, MIN's
--             WtConvSub) give equal types / convertible terms
--   Presup    presupposition for HasType, TyEq, ConvTm;
--             OpF, OpG f types;  f = f' : OpF  ==>  OpG f = OpG f'
------------------------------------------------------------------------

module MAHLOINJ.Syntax.All where

import MAHLOINJ.Syntax.Lemmas
import MAHLOINJ.Syntax.Weaken
import MAHLOINJ.Syntax.Subst
import MAHLOINJ.Syntax.Wf
import MAHLOINJ.Syntax.CtxConv
import MAHLOINJ.Syntax.Funct
import MAHLOINJ.Syntax.Presup
