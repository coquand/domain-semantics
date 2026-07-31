{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.IterFun
--
-- MUTUAL ITERATION, function-parameterised (the vector analogue of
-- `PrecFun.precFun` / `PrecFun.RecData`).
--
-- A block of r mutually defined functions f_1,...,f_r of arity 1+n:
--
--   f_i(0,      ybar) = u_i(ybar)
--   f_i(S(x),   ybar) = g_i(f_1(x,ybar), ..., f_r(x,ybar), ybar)
--
-- Note there is NO x in the step: primitive recursion is coded
-- denotationally by iteration + pairing (manuscript, Introduction), so
-- mutual ITERATION is the general case and the step functions read only
-- the r previous values and ybar.  This is what fixes the slot layout:
--
--   slots 0 .. r-1      the previous values f_1(x,ybar) .. f_r(x,ybar)
--   slots r .. r+n-1    ybar
--
-- Base and step are packaged tuple-valued:  G, H : FTup -> FTup, each
-- returning r results (`lenG`, `lenH`), with joint obstination `UOMall`
-- from `PropertyVec`.  Nothing here inspects PR syntax -- same seam as
-- `RecData`.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.IterFun where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Meet using (BndT ; meetT)
open import OBSTINATION.PropertyVec using (UOMall)

------------------------------------------------------------------------
-- Append and constant tuples, on finite tuples
------------------------------------------------------------------------

appF : FTup -> FTup -> FTup
appF nil        B = B
appF (cons a A) B = cons a (appF A B)

repF : Nat -> FEl -> FTup
repF zero    v = nil
repF (suc r) v = cons v (repF r v)

length-repF : (r : Nat) (v : FEl) -> Eq (length (repF r v)) r
length-repF zero    v = refl
length-repF (suc r) v = Eq-cong suc (length-repF r v)

-- the r-fold bottom tuple
botF : Nat -> FTup
botF r = repF r (fbot zero)

length-botF : (r : Nat) -> Eq (length (botF r)) r
length-botF r = length-repF r (fbot zero)

-- it is below every tuple of the same length
botF-le : (r : Nat) (Z : FTup) -> Eq (length Z) r -> LeFTup (botF r) Z
botF-le zero    nil         e = tt
botF-le zero    (cons _ _)  ()
botF-le (suc r) nil         ()
botF-le (suc r) (cons z zs) e =
  mkSigma (LeD-botD (embed z)) (botF-le r zs (suc-inj e))

appF-mono : {A B C E : FTup} ->
  LeFTup A B -> LeFTup C E -> LeFTup (appF A C) (appF B E)
appF-mono {nil}      {nil}      lAB lCE = lCE
appF-mono {nil}      {cons _ _} ()  lCE
appF-mono {cons _ _} {nil}      ()  lCE
appF-mono {cons a A} {cons b B} lAB lCE =
  mkSigma (fst lAB) (appF-mono {A} {B} (snd lAB) lCE)

------------------------------------------------------------------------
-- Monotonicity / stability of a tuple-valued function
------------------------------------------------------------------------

MonoT : (FTup -> FTup) -> Set
MonoT F = {A B : FTup} -> LeFTup A B -> LeFTup (F A) (F B)

StableT : (FTup -> FTup) -> Set
StableT F = {A B : FTup} -> BndT A B -> Eq (F (meetT A B)) (meetT (F A) (F B))

------------------------------------------------------------------------
-- The mutual iteration operator (mirrors PrecFun.precFun)
--
-- The state is now a whole r-tuple of previous values, appended in front
-- of ybar before the step is applied.
------------------------------------------------------------------------

iterVec : (G H : FTup -> FTup) -> Nat -> FEl -> FTup -> FTup
iterVec G H r (fbot zero)    Y = botF r
iterVec G H r (fbot (suc j)) Y = H (appF (iterVec G H r (fbot j) Y) Y)
iterVec G H r (fcpl zero)    Y = G Y
iterVec G H r (fcpl (suc j)) Y = H (appF (iterVec G H r (fcpl j) Y) Y)

-- as a function of a whole tuple (mirrors PrecFun.PF)
IV : (G H : FTup -> FTup) -> Nat -> FTup -> FTup
IV G H r nil        = botF r
IV G H r (cons a Y) = iterVec G H r a Y

------------------------------------------------------------------------
-- The block always returns r results
------------------------------------------------------------------------

iterVec-length : (G H : FTup -> FTup) (r : Nat) ->
  ((Y : FTup) -> Eq (length (G Y)) r) ->
  ((X : FTup) -> Eq (length (H X)) r) ->
  (a : FEl) (Y : FTup) -> Eq (length (iterVec G H r a Y)) r
iterVec-length G H r lg lh (fbot zero)    Y = length-botF r
iterVec-length G H r lg lh (fbot (suc j)) Y = lh (appF (iterVec G H r (fbot j) Y) Y)
iterVec-length G H r lg lh (fcpl zero)    Y = lg Y
iterVec-length G H r lg lh (fcpl (suc j)) Y = lh (appF (iterVec G H r (fcpl j) Y) Y)

IV-length : (G H : FTup -> FTup) (r : Nat) ->
  ((Y : FTup) -> Eq (length (G Y)) r) ->
  ((X : FTup) -> Eq (length (H X)) r) ->
  (X : FTup) -> Eq (length (IV G H r X)) r
IV-length G H r lg lh nil        = length-botF r
IV-length G H r lg lh (cons a Y) = iterVec-length G H r lg lh a Y

------------------------------------------------------------------------
-- Monotonicity of the abstract mutual iteration
-- (port of PrecFun.precFun-mono; the bottom case now needs the length
-- invariant, since LeFTup is Empty on a length mismatch)
------------------------------------------------------------------------

iterVec-mono : (G H : FTup -> FTup) (r : Nat)
  (lg : (Y : FTup) -> Eq (length (G Y)) r)
  (lh : (X : FTup) -> Eq (length (H X)) r) ->
  MonoT G -> MonoT H ->
  {a a' : FEl} {Y Y' : FTup} ->
  LeF a a' -> LeFTup Y Y' -> LeFTup (iterVec G H r a Y) (iterVec G H r a' Y')
iterVec-mono G H r lg lh mg mh {fbot zero}    {fbot k}       {Y} {Y'} la lY =
  botF-le r (iterVec G H r (fbot k) Y') (iterVec-length G H r lg lh (fbot k) Y')
iterVec-mono G H r lg lh mg mh {fbot (suc j)} {fbot zero}    {Y} {Y'} () lY
iterVec-mono G H r lg lh mg mh {fbot (suc j)} {fbot (suc k)} {Y} {Y'} la lY =
  mh (appF-mono (iterVec-mono G H r lg lh mg mh {fbot j} {fbot k} {Y} {Y'} la lY) lY)
iterVec-mono G H r lg lh mg mh {fbot zero}    {fcpl k}       {Y} {Y'} la lY =
  botF-le r (iterVec G H r (fcpl k) Y') (iterVec-length G H r lg lh (fcpl k) Y')
iterVec-mono G H r lg lh mg mh {fbot (suc j)} {fcpl zero}    {Y} {Y'} () lY
iterVec-mono G H r lg lh mg mh {fbot (suc j)} {fcpl (suc k)} {Y} {Y'} la lY =
  mh (appF-mono (iterVec-mono G H r lg lh mg mh {fbot j} {fcpl k} {Y} {Y'} la lY) lY)
iterVec-mono G H r lg lh mg mh {fcpl j}       {fbot k}       {Y} {Y'} () lY
iterVec-mono G H r lg lh mg mh {fcpl zero}    {fcpl zero}    {Y} {Y'} refl lY = mg lY
iterVec-mono G H r lg lh mg mh {fcpl (suc j)} {fcpl (suc j)} {Y} {Y'} refl lY =
  mh (appF-mono
       (iterVec-mono G H r lg lh mg mh {fcpl j} {fcpl j} {Y} {Y'} refl lY) lY)

IV-mono : (G H : FTup -> FTup) (r : Nat)
  (lg : (Y : FTup) -> Eq (length (G Y)) r)
  (lh : (X : FTup) -> Eq (length (H X)) r) ->
  MonoT G -> MonoT H -> MonoT (IV G H r)
IV-mono G H r lg lh mg mh {nil}      {nil}       le = LeFTup-refl (botF r)
IV-mono G H r lg lh mg mh {nil}      {cons _ _}  ()
IV-mono G H r lg lh mg mh {cons _ _} {nil}       ()
IV-mono G H r lg lh mg mh {cons a Y} {cons a' Y'} le =
  iterVec-mono G H r lg lh mg mh {a} {a'} {Y} {Y'} (fst le) (snd le)

------------------------------------------------------------------------
-- The iteration data: the abstract interface the chain consumes.
-- (vector analogue of PrecFun.RecData; `uog`/`uoh` are JOINT, i.e. one
-- shared approximant carrying r verdicts -- see PropertyVec)
------------------------------------------------------------------------

record IterData : Set where
  constructor mkIterData
  field
    ar      : Nat                  -- r, the number of mutually defined functions
    G H     : FTup -> FTup
    lenG    : (Y : FTup) -> Eq (length (G Y)) ar
    lenH    : (X : FTup) -> Eq (length (H X)) ar
    monoG   : MonoT G
    monoH   : MonoT H
    stableH : StableT H
    uog     : UOMall G ar
    uoh     : UOMall H ar

-- the block of functions an IterData denotes
module _ (idt : IterData) where
  open IterData idt

  block : FTup -> FTup
  block = IV G H ar

  block-length : (X : FTup) -> Eq (length (block X)) ar
  block-length = IV-length G H ar lenG lenH

  block-mono : MonoT block
  block-mono = IV-mono G H ar lenG lenH monoG monoH
