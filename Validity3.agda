{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Validity3.agda
--
-- Two-layer bundled validity: Val2 = Pair HasType Val2c
-- where Val2c is the structural content (Top at leaves).
--
-- No Prop, no Sigma. Minimal test for the modular design.
-- 0 postulates.
------------------------------------------------------------------------

module Validity3 where

import Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ;
              fst ; snd ; Pair ; Eq ; refl ; Eq-transport ; Eq-sym ;
              Eq-cong ;
              FinEl ; Bot ; UCode ; PropCode ; FunEl ; PiCode ; FinFun ;
              List ; nil ; cons)
open import RawSyntax using (Expr ; Var ; U ; Pi ; Lam ; App ; wkExpr ;
  subst1 ; Fin ; fzero ; fsuc)
open import TypingRules using (Ctx ; empty ; extend ;
  HasType ; ConvTm ;
  WfCtx ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-Pi ; ty-conv)
open import Reduction using (HeadRed ; HeadRed-trans ;
  HeadRed-App ; HeadRed-strip-Pi ;
  headred-refl ; headred-step)
open import SubstitutionLemma using (typing-ConvTm)
open import PaperSemantics using (EvalFun ;
  CoherentFun ; FinMemFun ; FinMemAllU ;
  Coherent ; CoherentFunTail ;
  FinMem ; LeCode ;
  coh-from-aU ; cft-from-cf ;
  Coherent-EvalFun)
open import Validity using (
  Selection ; sel-nil ; sel-skip ; sel-take ;
  Selection-le-EvalFun ; Coherent-Selection ; Coherent-Selection-val)

-- Red3: HeadRed bundled with ConvTm (paper's definition)
data Red3 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Set where
  mkRed3 : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
    HeadRed M N -> ConvTm G M N A -> Red3 G M N A

Red3-hr : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
  Red3 G M N A -> HeadRed M N
Red3-hr (mkRed3 hr _) = hr

Red3-conv : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
  Red3 G M N A -> ConvTm G M N A
Red3-conv (mkRed3 _ ct) = ct

Red3-refl : {n : Nat} {G : Ctx n} {M A : Expr n} ->
  HasType G M A -> Red3 G M M A
Red3-refl ht = mkRed3 headred-refl (conv-refl ht)

Red3-unique-Pi : {n : Nat} {G : Ctx n} {A B B' : Expr n}
  {F : Expr (suc n)} {F' : Expr (suc n)} ->
  Red3 G A (Pi B F) U -> Red3 G A (Pi B' F') U ->
  Pair (Eq B B') (Eq F F')
Red3-unique-Pi (mkRed3 r1 _) (mkRed3 r2 _) = HeadRed-unique-Pi r1 r2
  where
    open import Reduction using (HeadRed-unique-Pi)

------------------------------------------------------------------------
-- Inner layer: Val2c / EqVal2c — structural content, Top at leaves
-- This is exactly Validity2's Val2/EqVal2 definition.
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual

  Val2c : {n : Nat} -> Ctx n -> Expr n -> Expr n ->
    FinEl -> FinEl -> Set

  EqVal2c : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n ->
    FinEl -> FinEl -> Set

  ValTy2 : {n : Nat} -> Ctx n -> Expr n -> FinEl -> Set

  EqValTy2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> Set

  ValTyPi2 : {n : Nat} -> Ctx n -> Expr n -> FinEl -> FinFun -> Set

  EqValTyPi2 : {n : Nat} -> Ctx n -> Expr n -> Expr n ->
    FinEl -> FinFun -> Set

  ValPi2 : {n : Nat} -> Ctx n -> Expr n -> Expr n ->
    FinFun -> FinEl -> FinFun -> Set

  EqValPi2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n ->
    FinFun -> FinEl -> FinFun -> Set

  PiEdgeVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) ->
    FinEl -> FinFun -> Set

  PiEdgeEq2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) ->
    FinEl -> FinFun -> Set

  PiEdgeEqTy2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) ->
    Expr (suc n) -> FinEl -> FinFun -> Set

  PiAppVal2 : {n : Nat} -> Ctx n -> Expr n ->
    Expr n -> Expr (suc n) -> FinEl -> FinFun -> FinFun -> Set

  PiAppEq2 : {n : Nat} -> Ctx n -> Expr n ->
    Expr n -> Expr (suc n) -> FinEl -> FinFun -> FinFun -> Set

  PiAppEqVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr n ->
    Expr n -> Expr (suc n) -> FinEl -> FinFun -> FinFun -> Set

  --------------------------------------------------------------------
  -- Val2c: Top at leaves, structured at UCode / FunEl+PiCode
  --------------------------------------------------------------------

  Val2c G M A u Bot              = Top
  Val2c G M A Bot UCode          = Top
  Val2c G M A UCode UCode        = ValTy2 G M UCode
  Val2c G M A (FunEl g) UCode    = ValTy2 G M (FunEl g)
  Val2c G M A (PiCode a' f') UCode = ValTy2 G M (PiCode a' f')
  Val2c G M A PropCode UCode     = Top
  Val2c G M A (PiCode a' f') PropCode = ValTy2 G M (PiCode a' f')
  Val2c G M A Bot PropCode            = Top
  Val2c G M A UCode PropCode          = Top
  Val2c G M A PropCode PropCode       = Top
  Val2c G M A (FunEl g) PropCode      = Top
  Val2c G M A u (FunEl h)        = Top
  Val2c G M A Bot            (PiCode b f) = Top
  Val2c G M A UCode          (PiCode b f) = Top
  Val2c G M A PropCode       (PiCode b f) = Top
  Val2c G M A (FunEl g)      (PiCode b f) =
    Pair (ValTy2 G A (PiCode b f)) (ValPi2 G M A g b f)
  Val2c G M A (PiCode a' f') (PiCode b f) = Top

  --------------------------------------------------------------------
  -- EqVal2c: Top at leaves
  --------------------------------------------------------------------

  EqVal2c G M N A u Bot              = Top
  EqVal2c G M N A Bot UCode          = Top
  EqVal2c G M N A UCode UCode        =
    Pair (ValTy2 G M UCode) (Pair (ValTy2 G N UCode) (EqValTy2 G M N UCode))
  EqVal2c G M N A (FunEl g) UCode    =
    Pair (ValTy2 G M (FunEl g)) (Pair (ValTy2 G N (FunEl g)) (EqValTy2 G M N (FunEl g)))
  EqVal2c G M N A (PiCode a' f') UCode =
    Pair (ValTy2 G M (PiCode a' f')) (Pair (ValTy2 G N (PiCode a' f')) (EqValTy2 G M N (PiCode a' f')))
  EqVal2c G M N A PropCode UCode    = Top
  EqVal2c G M N A (PiCode a' f') PropCode =
    Pair (ValTy2 G M (PiCode a' f')) (Pair (ValTy2 G N (PiCode a' f')) (EqValTy2 G M N (PiCode a' f')))
  EqVal2c G M N A Bot PropCode            = Top
  EqVal2c G M N A UCode PropCode          = Top
  EqVal2c G M N A PropCode PropCode       = Top
  EqVal2c G M N A (FunEl g) PropCode      = Top
  EqVal2c G M N A u (FunEl h)       = Top
  EqVal2c G M N A Bot            (PiCode b f) = Top
  EqVal2c G M N A UCode          (PiCode b f) = Top
  EqVal2c G M N A PropCode       (PiCode b f) = Top
  EqVal2c G M N A (FunEl g)      (PiCode b f) =
    Pair (ValTy2 G A (PiCode b f))
         (Pair (ValPi2 G M A g b f)
               (Pair (ValPi2 G N A g b f)
                     (EqValPi2 G M N A g b f)))
  EqVal2c G M N A (PiCode a' f') (PiCode b f) = Top

  --------------------------------------------------------------------
  -- ValTy2 / EqValTy2 / ValTyPi2 / EqValTyPi2 / Pi structures
  -- All unchanged from Validity2
  --------------------------------------------------------------------

  ValTy2 G M Bot          = Top
  ValTy2 G M UCode        = Top
  ValTy2 G M PropCode     = Top
  ValTy2 G M (FunEl g)    = Top
  ValTy2 G M (PiCode b f) = ValTyPi2 G M b f

  EqValTy2 G M N Bot          = Top
  EqValTy2 G M N UCode        = Top
  EqValTy2 G M N PropCode     = Top
  EqValTy2 G M N (FunEl g)    = Top
  EqValTy2 G M N (PiCode b f) =
    Pair (ValTyPi2 G M b f)
         (Pair (ValTyPi2 G N b f)
               (EqValTyPi2 G M N b f))

  ValTyPi2 {n} G M b f =
    Sigma (Expr n) \ A ->
    Sigma (Expr (suc n)) \ B ->
    Sigma (Red3 G M (Pi A B) U) \ _ ->
    Sigma (CoherentFunTail f) \ _ ->
    Sigma (FinMemAllU f b) \ _ ->
    Sigma (HasType G A U) \ _ ->
    Sigma (HasType (extend G A) B U) \ _ ->
    Pair (ValTy2 G A b)
         (Pair (PiEdgeVal2 G A B b f)
               (PiEdgeEq2 G A B b f))

  EqValTyPi2 {n} G M N b f =
    Sigma (Expr n) \ A ->
    Sigma (Expr (suc n)) \ B ->
    Sigma (Expr n) \ A' ->
    Sigma (Expr (suc n)) \ B' ->
    Sigma (Red3 G M (Pi A B) U) \ _ ->
    Sigma (Red3 G N (Pi A' B') U) \ _ ->
    Sigma (CoherentFunTail f) \ _ ->
    Sigma (FinMemAllU f b) \ _ ->
    Sigma (ConvTm G A A' U) \ _ ->
    Sigma (ConvTm (extend G A) B B' U) \ _ ->
    Pair (EqValTy2 G A A' b)
         (PiEdgeEqTy2 G A B B' b f)

  ValPi2 {n} G M A g b f =
    Sigma (Expr n) \ A0 ->
    Sigma (Expr (suc n)) \ B0 ->
    Sigma (Red3 G A (Pi A0 B0) U) \ _ ->
    Sigma (CoherentFun g) \ _ ->
    Sigma (FinMemFun g b f) \ _ ->
    Pair (PiAppVal2 G M A0 B0 b f g)
         (PiAppEq2 G M A0 B0 b f g)

  EqValPi2 {n} G M N A g b f =
    Sigma (Expr n) \ A0 ->
    Sigma (Expr (suc n)) \ B0 ->
    Sigma (Red3 G A (Pi A0 B0) U) \ _ ->
    Sigma (CoherentFun g) \ _ ->
    Sigma (FinMemFun g b f) \ _ ->
    PiAppEqVal2 G M N A0 B0 b f g

  -- Edge functions use Val2 (outer layer), not Val2c
  PiEdgeVal2 {n} G A B b f =
    (u v : FinEl) -> Selection f u v ->
    (N : Expr n) -> HasType G N A -> Val2 G N A u b ->
    ValTy2 G (subst1 B N) v

  PiEdgeEq2 {n} G A B b f =
    (u v : FinEl) -> Selection f u v ->
    (N1 N2 : Expr n) -> HasType G N1 A -> HasType G N2 A ->
    ConvTm G N1 N2 A -> EqVal2 G N1 N2 A u b ->
    EqValTy2 G (subst1 B N1) (subst1 B N2) v

  PiEdgeEqTy2 {n} G A B B' b f =
    (u v : FinEl) -> Selection f u v ->
    (P : Expr n) -> HasType G P A -> Val2 G P A u b ->
    EqValTy2 G (subst1 B P) (subst1 B' P) v

  PiAppVal2 {n} G M A0 B0 b f g =
    (u v : FinEl) -> Selection g u v ->
    (N : Expr n) -> HasType G N A0 -> Val2 G N A0 u b ->
    Val2 G (App M N) (subst1 B0 N) v (EvalFun f u)

  PiAppEq2 {n} G M A0 B0 b f g =
    (u v : FinEl) -> Selection g u v ->
    (N1 N2 : Expr n) -> HasType G N1 A0 -> HasType G N2 A0 ->
    ConvTm G N1 N2 A0 -> EqVal2 G N1 N2 A0 u b ->
    EqVal2 G (App M N1) (App M N2) (subst1 B0 N1) v (EvalFun f u)

  PiAppEqVal2 {n} G M N A0 B0 b f g =
    (u v : FinEl) -> Selection g u v ->
    (P : Expr n) -> HasType G P A0 -> Val2 G P A0 u b ->
    EqVal2 G (App M P) (App N P) (subst1 B0 P) v (EvalFun f u)

  --------------------------------------------------------------------
  -- Outer layer: Val2 = Pair HasType Val2c
  --              EqVal2 = Pair ConvTm EqVal2c
  --------------------------------------------------------------------

  Val2 : {n : Nat} -> Ctx n -> Expr n -> Expr n ->
    FinEl -> FinEl -> Set
  Val2 G M A u a = Pair (HasType G M A) (Val2c G M A u a)

  EqVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n ->
    FinEl -> FinEl -> Set
  EqVal2 G M N A u a = Pair (ConvTm G M N A) (EqVal2c G M N A u a)

------------------------------------------------------------------------
-- Outer layer operations: generic, handle HasType/ConvTm
------------------------------------------------------------------------

Val2-ht : {n : Nat} {G : Ctx n} {M A : Expr n} {u a : FinEl} ->
  Val2 G M A u a -> HasType G M A
Val2-ht = fst

Val2-core : {n : Nat} {G : Ctx n} {M A : Expr n} {u a : FinEl} ->
  Val2 G M A u a -> Val2c G M A u a
Val2-core = snd

EqVal2-ct : {n : Nat} {G : Ctx n} {M N A : Expr n} {u a : FinEl} ->
  EqVal2 G M N A u a -> ConvTm G M N A
EqVal2-ct = fst

EqVal2-core : {n : Nat} {G : Ctx n} {M N A : Expr n} {u a : FinEl} ->
  EqVal2 G M N A u a -> EqVal2c G M N A u a
EqVal2-core = snd

Val2-Bot : {n : Nat} {G : Ctx n} {M A : Expr n} ->
  HasType G M A -> (a : FinEl) -> Val2 G M A Bot a
Val2-Bot ht Bot          = mkSigma ht tt
Val2-Bot ht UCode        = mkSigma ht tt
Val2-Bot ht PropCode     = mkSigma ht tt
Val2-Bot ht (FunEl h)    = mkSigma ht tt
Val2-Bot ht (PiCode b f) = mkSigma ht tt

EqVal2-Bot : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
  ConvTm G M N A -> (a : FinEl) -> EqVal2 G M N A Bot a
EqVal2-Bot ct Bot          = mkSigma ct tt
EqVal2-Bot ct UCode        = mkSigma ct tt
EqVal2-Bot ct PropCode     = mkSigma ct tt
EqVal2-Bot ct (FunEl h)    = mkSigma ct tt
EqVal2-Bot ct (PiCode b f) = mkSigma ct tt

Val2-to-EqVal2 : {n : Nat} {G : Ctx n} {M A : Expr n}
  (u a : FinEl) -> Val2 G M A u a -> EqVal2 G M M A u a
Val2-to-EqVal2 u a (mkSigma ht inner) =
  mkSigma (conv-refl ht) (Val2c-to-EqVal2c u a inner)
  where
    Val2c-to-EqVal2c : {n : Nat} {G : Ctx n} {M A : Expr n}
      (u a : FinEl) -> Val2c G M A u a -> EqVal2c G M M A u a
    Val2c-to-EqVal2c = {!!}  -- TODO: same as old Val2-to-EqVal2

Val2-from-EqVal2-first : {n : Nat} {G : Ctx n} {M N A : Expr n}
  (u a : FinEl) -> EqVal2 G M N A u a -> Val2 G M A u a
Val2-from-EqVal2-first u a (mkSigma ct inner) =
  mkSigma (fst (typing-ConvTm ct)) (Val2c-from-EqVal2c-first u a inner)
  where
    Val2c-from-EqVal2c-first : {n : Nat} {G : Ctx n} {M N A : Expr n}
      (u a : FinEl) -> EqVal2c G M N A u a -> Val2c G M A u a
    Val2c-from-EqVal2c-first = {!!}  -- TODO: same as old Val2-from-EqVal2-first

Val2-from-EqVal2-second : {n : Nat} {G : Ctx n} {M N A : Expr n}
  (u a : FinEl) -> EqVal2 G M N A u a -> Val2 G N A u a
Val2-from-EqVal2-second u a (mkSigma ct inner) =
  mkSigma (snd (typing-ConvTm ct)) (Val2c-from-EqVal2c-second u a inner)
  where
    Val2c-from-EqVal2c-second : {n : Nat} {G : Ctx n} {M N A : Expr n}
      (u a : FinEl) -> EqVal2c G M N A u a -> Val2c G N A u a
    Val2c-from-EqVal2c-second = {!!}  -- TODO: same as old Val2-from-EqVal2-second

EqVal2-sym : {n : Nat} {G : Ctx n} {M N A : Expr n}
  (u a : FinEl) -> Coherent u -> Coherent a ->
  EqVal2 G M N A u a -> EqVal2 G N M A u a
EqVal2-sym u a cu ca (mkSigma ct inner) =
  mkSigma (conv-sym ct) (EqVal2c-sym u a cu ca inner)
  where
    EqVal2c-sym : {n : Nat} {G : Ctx n} {M N A : Expr n}
      (u a : FinEl) -> Coherent u -> Coherent a ->
      EqVal2c G M N A u a -> EqVal2c G N M A u a
    EqVal2c-sym = {!!}  -- TODO: same as old EqVal2-sym

Val2-beta-expand : {n : Nat} {G : Ctx n} {M M' T : Expr n}
  (u a : FinEl) -> HeadRed M' M -> ConvTm G M' M T ->
  Val2 G M T u a -> Val2 G M' T u a
Val2-beta-expand u a hr ct (mkSigma ht inner) =
  mkSigma (fst (typing-ConvTm ct)) (Val2c-beta-expand u a hr inner)
  where
    Val2c-beta-expand : {n : Nat} {G : Ctx n} {M M' T : Expr n}
      (u a : FinEl) -> HeadRed M' M ->
      Val2c G M T u a -> Val2c G M' T u a
    Val2c-beta-expand = {!!}  -- TODO: same as old Val2-beta-expand (no ConvTm needed!)
