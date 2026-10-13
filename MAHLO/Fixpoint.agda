{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Fixpoint.agda
--
-- The fixed point of Gamma is taken as a HYPOTHESIS (a record, not a
-- postulate): its existence is Lemma 14 of mahlo-plan.tex, proved there
-- by a transfinite iteration, and it is exactly the place where Mahlo
-- strength is needed.  From it we prove Lemma 15 (the Mahlo property),
-- which validates the universe rules.
------------------------------------------------------------------------

open import MAHLO.Basic
open import MAHLO.TermModel

module MAHLO.Fixpoint (TM : TermModel) where

open TermModel TM
open import MAHLO.Candidate TM
open import MAHLO.Pre TM
open import MAHLO.Congruence TM
open import MAHLO.Gamma TM
open import MAHLO.EndExt TM

record Fixpoint : Set1 where
  field
    V      : Cand
    unfold : V << Gam V
    fold   : Gam V << V

module Mahlo (Fx : Fixpoint) where
  open Fixpoint Fx
  open Cand V
  private
    module RV = IsPER R-per

  car : D -> Set
  car a = R a a

  -- interpretation of the type of operators on families in V
  OpV : D -> D -> D -> D -> Set
  OpV f g f' g' = Op V car f g f' g'

  -- Lemma 15 (1): an operator on V satisfies Indep
  mahlo-indep : {f g : D} -> OpV f g f g -> Indep V f g
  mahlo-indep {f} {g} op A F pA rF hF =
    (_<<_.inc fold (gpi (mkPi A A F F ~~-refl ~~-refl rAA rF)) ,
     _<<_.inc fold (gsig (mkSig A A F F ~~-refl ~~-refl rAA rF))) ,
    (fst o , (\ c i -> snd o c c i))
    where
      rAA = Pre-car V pA
      hC : FamIn V car A F
      hC v i = Pre-car V (hF v i)
      o = op A A F F rAA rAA rAA rF hC hC

  OpV-l : {f g f' g' : D} -> OpV f g f' g' -> OpV f g f g
  OpV-l op = Op-trans V op (Op-sym V op)

  OpV-r : {f g f' g' : D} -> OpV f g f' g' -> OpV f' g' f' g'
  OpV-r op = Op-trans V (Op-sym V op) op

  -- Lemma 15 (1) and (4): codes are in V, and equal operators give
  -- equal codes  (validates  U_{f,g} : V  and its congruence rule)
  mahlo-code : {f g f' g' : D} -> OpV f g f' g' -> R (U f g) (U f' g')
  mahlo-code op =
    _<<_.inc fold
      (gU (mkU _ _ _ _ ~~-refl ~~-refl
             (mahlo-indep (OpV-l op)) (mahlo-indep (OpV-r op))
             (Op-pred V (\ a p -> Pre-car V p) op)))

  -- the interpretation of a code is V restricted to pre(f,g,V)
  -- (validates subsumption and rule (R'))
  mahlo-int : {f g : D} -> OpV f g f g -> I (U f g) ~ Res V (Pre V f g)
  mahlo-int {f} {g} op =
    ~-trans (~-sym (_<<_.int fold (U f g) self)) (GI-U V (U f g) f g ~~-refl)
    where
      self : Cand.R (Gam V) (U f g) (U f g)
      self = gU (mkU f g f g ~~-refl ~~-refl (mahlo-indep op) (mahlo-indep op)
                   (Op-pred V (\ a p -> Pre-car V p) op))

  -- Lemma 15 (2): closure of pre(f,g,V)
  module _ {f g : D} (op : OpV f g f g) where
    private
      ind = mahlo-indep op

    close-pi : (A F : D) -> Pre V f g A -> FamResp V A F ->
               FamIn V (Pre V f g) A F -> Pre V f g (Pi A F)
    close-pi A F pA r h = pre-pi (Pi A F) A F ~~-refl pA r h (fst (fst (ind A F pA r h)))

    close-sig : (A F : D) -> Pre V f g A -> FamResp V A F ->
                FamIn V (Pre V f g) A F -> Pre V f g (Sig A F)
    close-sig A F pA r h = pre-sig (Sig A F) A F ~~-refl pA r h (snd (fst (ind A F pA r h)))

    close-f : (A F : D) -> Pre V f g A -> FamResp V A F ->
              FamIn V (Pre V f g) A F -> Pre V f g (FA f A F)
    close-f A F pA r h = pre-f (FA f A F) A F ~~-refl pA r h (fst (snd (ind A F pA r h)))

    close-g : (A F c : D) -> Pre V f g A -> FamResp V A F ->
              FamIn V (Pre V f g) A F -> I (FA f A F) c c ->
              Pre V f g (GA g A F c)
    close-g A F c pA r h i =
      pre-g (GA g A F c) A F c ~~-refl pA r h (fst (snd (ind A F pA r h))) i
            (snd (snd (ind A F pA r h)) c i)
