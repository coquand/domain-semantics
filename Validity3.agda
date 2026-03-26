{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Validity3.agda
--
-- Full paper bundling: Val2 bundles HasType, EqVal2 bundles ConvTm,
-- at EVERY code pair. Red3 bundles HeadRed + ConvTm.
--
-- Pi + U only (no Prop, no Sigma). Test for the design.
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
  ty-conv ; conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-Pi)
open import Reduction using (HeadRed ; HeadRed-trans ;
  HeadRed-App ; HeadRed-strip-Pi ; HeadRed-unique-Pi ;
  headred-refl ; headred-step)
open import SubstitutionLemma using (typing-ConvTm)
open import PaperSemantics using (EvalFun ;
  CoherentFun ; FinMemFun ; FinMemAllU ;
  Coherent ; CoherentFunTail ;
  FinMem ; LeCode ; LeCode-refl ; LeCode-trans ;
  Comp ; Comp-down ; Sup ;
  coh-from-aU ; cft-from-cf ; FinMem-coh-u ;
  LeCode-Sup-left ; LeCode-Sup-right ;
  Coherent-Sup ; Coherent-EvalFun ;
  FinMem-a-in-U ; finMem-upward ;
  finMem-Sup-left ; finMem-Sup-right ;
  finMemUCode-Sup ; EvalFun-mon-arg ;
  EvalFun-in-UCode)
open import Validity using (
  Selection ; sel-nil ; sel-skip ; sel-take ;
  Selection-le-EvalFun ; Coherent-Selection ; Coherent-Selection-val ;
  bU-from-cf-fmU)

-- Red3: HeadRed bundled with ConvTm
data Red3 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Set where
  mkRed3 : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
    HeadRed M N -> ConvTm G M N A -> Red3 G M N A

Red3-hr : {n : Nat} {G : Ctx n} {M N A : Expr n} -> Red3 G M N A -> HeadRed M N
Red3-hr (mkRed3 hr _) = hr

Red3-conv : {n : Nat} {G : Ctx n} {M N A : Expr n} -> Red3 G M N A -> ConvTm G M N A
Red3-conv (mkRed3 _ ct) = ct

Red3-refl : {n : Nat} {G : Ctx n} {M A : Expr n} -> HasType G M A -> Red3 G M M A
Red3-refl ht = mkRed3 headred-refl (conv-refl ht)

Red3-unique-Pi : {n : Nat} {G : Ctx n} {A B B' : Expr n}
  {F : Expr (suc n)} {F' : Expr (suc n)} ->
  Red3 G A (Pi B F) U -> Red3 G A (Pi B' F') U -> Pair (Eq B B') (Eq F F')
Red3-unique-Pi (mkRed3 r1 _) (mkRed3 r2 _) = HeadRed-unique-Pi r1 r2

------------------------------------------------------------------------
-- Mutual definitions — full paper bundling
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual

  -- Val2: HasType at leaves, structured + HasType at Pi codes
  Val2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> FinEl -> Set

  EqVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n ->
    FinEl -> FinEl -> Set

  ValTy2 : {n : Nat} -> Ctx n -> Expr n -> FinEl -> Set
  EqValTy2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> Set
  ValTyPi2 : {n : Nat} -> Ctx n -> Expr n -> FinEl -> FinFun -> Set
  EqValTyPi2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> FinFun -> Set
  ValPi2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinFun -> FinEl -> FinFun -> Set
  EqValPi2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n ->
    FinFun -> FinEl -> FinFun -> Set
  PiEdgeVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> Set
  PiEdgeEq2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> Set
  PiEdgeEqTy2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) ->
    Expr (suc n) -> FinEl -> FinFun -> Set
  PiAppVal2 : {n : Nat} -> Ctx n -> Expr n ->
    Expr n -> Expr (suc n) -> FinEl -> FinFun -> FinFun -> Set
  PiAppEq2 : {n : Nat} -> Ctx n -> Expr n ->
    Expr n -> Expr (suc n) -> FinEl -> FinFun -> FinFun -> Set
  PiAppEqVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr n ->
    Expr n -> Expr (suc n) -> FinEl -> FinFun -> FinFun -> Set

  -- FinMem-Coherent
  FinMem-Coherent : (u a : FinEl) -> FinMem u a -> Coherent u
  FinMem-Coherent u a fm = FinMem-coh-u u a fm

  --------------------------------------------------------------------
  -- Val2: HasType G M A at every code pair
  --------------------------------------------------------------------

  Val2 G M A u Bot              = HasType G M A
  Val2 G M A Bot UCode          = HasType G M A
  Val2 G M A UCode UCode        = Pair (HasType G M A) (ValTy2 G M UCode)
  Val2 G M A (FunEl g) UCode    = Pair (HasType G M A) (ValTy2 G M (FunEl g))
  Val2 G M A (PiCode a' f') UCode = Pair (HasType G M A) (ValTy2 G M (PiCode a' f'))
  Val2 G M A PropCode UCode     = HasType G M A
  Val2 G M A (PiCode a' f') PropCode = Pair (HasType G M A) (ValTy2 G M (PiCode a' f'))
  Val2 G M A Bot PropCode            = HasType G M A
  Val2 G M A UCode PropCode          = HasType G M A
  Val2 G M A PropCode PropCode       = HasType G M A
  Val2 G M A (FunEl g) PropCode      = HasType G M A
  Val2 G M A u (FunEl h)        = HasType G M A
  Val2 G M A Bot            (PiCode b f) = HasType G M A
  Val2 G M A UCode          (PiCode b f) = HasType G M A
  Val2 G M A PropCode       (PiCode b f) = HasType G M A
  Val2 G M A (FunEl g)      (PiCode b f) =
    Pair (HasType G M A)
         (Pair (ValTy2 G A (PiCode b f)) (ValPi2 G M A g b f))
  Val2 G M A (PiCode a' f') (PiCode b f) = HasType G M A

  --------------------------------------------------------------------
  -- EqVal2: ConvTm G M N A at every code pair
  --------------------------------------------------------------------

  EqVal2 G M N A u Bot              = ConvTm G M N A
  EqVal2 G M N A Bot UCode          = ConvTm G M N A
  EqVal2 G M N A UCode UCode        =
    Pair (ConvTm G M N A)
         (Pair (ValTy2 G M UCode) (Pair (ValTy2 G N UCode) (EqValTy2 G M N UCode)))
  EqVal2 G M N A (FunEl g) UCode    =
    Pair (ConvTm G M N A)
         (Pair (ValTy2 G M (FunEl g)) (Pair (ValTy2 G N (FunEl g)) (EqValTy2 G M N (FunEl g))))
  EqVal2 G M N A (PiCode a' f') UCode =
    Pair (ConvTm G M N A)
         (Pair (ValTy2 G M (PiCode a' f')) (Pair (ValTy2 G N (PiCode a' f')) (EqValTy2 G M N (PiCode a' f'))))
  EqVal2 G M N A PropCode UCode    = ConvTm G M N A
  EqVal2 G M N A (PiCode a' f') PropCode =
    Pair (ConvTm G M N A)
         (Pair (ValTy2 G M (PiCode a' f')) (Pair (ValTy2 G N (PiCode a' f')) (EqValTy2 G M N (PiCode a' f'))))
  EqVal2 G M N A Bot PropCode            = ConvTm G M N A
  EqVal2 G M N A UCode PropCode          = ConvTm G M N A
  EqVal2 G M N A PropCode PropCode       = ConvTm G M N A
  EqVal2 G M N A (FunEl g) PropCode      = ConvTm G M N A
  EqVal2 G M N A u (FunEl h)       = ConvTm G M N A
  EqVal2 G M N A Bot            (PiCode b f) = ConvTm G M N A
  EqVal2 G M N A UCode          (PiCode b f) = ConvTm G M N A
  EqVal2 G M N A PropCode       (PiCode b f) = ConvTm G M N A
  EqVal2 G M N A (FunEl g)      (PiCode b f) =
    Pair (ConvTm G M N A)
         (Pair (ValTy2 G A (PiCode b f))
               (Pair (ValPi2 G M A g b f)
                     (Pair (ValPi2 G N A g b f)
                           (EqValPi2 G M N A g b f))))
  EqVal2 G M N A (PiCode a' f') (PiCode b f) = ConvTm G M N A

  -- ValTy2 / EqValTy2: unchanged (Top at leaves)
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

  -- Pi structures: Red3 instead of Red, but otherwise same
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

------------------------------------------------------------------------
-- Extraction helpers
------------------------------------------------------------------------

Val2-ht : {n : Nat} {G : Ctx n} {M A : Expr n} {u a : FinEl} ->
  Val2 G M A u a -> HasType G M A
Val2-ht {u = u}          {a = Bot} v = v
Val2-ht {u = Bot}        {a = UCode} v = v
Val2-ht {u = UCode}      {a = UCode} v = fst v
Val2-ht {u = FunEl g}    {a = UCode} v = fst v
Val2-ht {u = PiCode _ _} {a = UCode} v = fst v
Val2-ht {u = PropCode}   {a = UCode} v = v
Val2-ht {u = PiCode _ _} {a = PropCode} v = fst v
Val2-ht {u = Bot}        {a = PropCode} v = v
Val2-ht {u = UCode}      {a = PropCode} v = v
Val2-ht {u = PropCode}   {a = PropCode} v = v
Val2-ht {u = FunEl _}    {a = PropCode} v = v
Val2-ht {u = u}          {a = FunEl _} v = v
Val2-ht {u = Bot}        {a = PiCode _ _} v = v
Val2-ht {u = UCode}      {a = PiCode _ _} v = v
Val2-ht {u = PropCode}   {a = PiCode _ _} v = v
Val2-ht {u = FunEl _}    {a = PiCode _ _} v = fst v
Val2-ht {u = PiCode _ _} {a = PiCode _ _} v = v

EqVal2-ct : {n : Nat} {G : Ctx n} {M N A : Expr n} {u a : FinEl} ->
  EqVal2 G M N A u a -> ConvTm G M N A
EqVal2-ct {u = u}          {a = Bot} v = v
EqVal2-ct {u = Bot}        {a = UCode} v = v
EqVal2-ct {u = UCode}      {a = UCode} v = fst v
EqVal2-ct {u = FunEl g}    {a = UCode} v = fst v
EqVal2-ct {u = PiCode _ _} {a = UCode} v = fst v
EqVal2-ct {u = PropCode}   {a = UCode} v = v
EqVal2-ct {u = PiCode _ _} {a = PropCode} v = fst v
EqVal2-ct {u = Bot}        {a = PropCode} v = v
EqVal2-ct {u = UCode}      {a = PropCode} v = v
EqVal2-ct {u = PropCode}   {a = PropCode} v = v
EqVal2-ct {u = FunEl _}    {a = PropCode} v = v
EqVal2-ct {u = u}          {a = FunEl _} v = v
EqVal2-ct {u = Bot}        {a = PiCode _ _} v = v
EqVal2-ct {u = UCode}      {a = PiCode _ _} v = v
EqVal2-ct {u = PropCode}   {a = PiCode _ _} v = v
EqVal2-ct {u = FunEl _}    {a = PiCode _ _} v = fst v
EqVal2-ct {u = PiCode _ _} {a = PiCode _ _} v = v
