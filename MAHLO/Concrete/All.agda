{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Concrete/All.agda
--
-- The concrete beta-delta term model (plan Sec. 6.2), discharging the
-- Model hypothesis of P2.
--
--   Tm          erased untyped terms, renaming, substitution
--   Red         beta/pi/iota reduction (delta is performed by den)
--   Confluence  parallel reduction, complete development, Church-Rosser
--   Conv        conversion = common reduct; (A1)
--   Values      neutral values, values, ⇓ (by arbitrary reduction)
--   DecEq       decidable syntactic equality
--   Eta         computed eta-normal forms
--   EtaLemmas   etanf preserves values; commutes with injective renamings
--   Bnd         free-variable bounds, the fresh-variable renaming
--   Rel         N, S, NatR: PERs closed under conversion
--   Ext         (A3): ext and ext-pair
--   Den         the denotation and its substitution laws
--   Instance    concreteTM : TermModel, concreteModel : Model concreteTM
--   Sound       Theorem 16 and (T2a), relative to the Fixpoint only
------------------------------------------------------------------------

module MAHLO.Concrete.All where

import MAHLO.Concrete.Tm
import MAHLO.Concrete.Red
import MAHLO.Concrete.Confluence
import MAHLO.Concrete.Conv
import MAHLO.Concrete.Values
import MAHLO.Concrete.DecEq
import MAHLO.Concrete.Eta
import MAHLO.Concrete.EtaLemmas
import MAHLO.Concrete.Bnd
import MAHLO.Concrete.Rel
import MAHLO.Concrete.Ext
import MAHLO.Concrete.Den
import MAHLO.Concrete.Instance
import MAHLO.Concrete.Sound
