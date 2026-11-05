{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- LAZY/InvarianceL.agda        (L5 -- rule [L])
--
--     mu (p)  = (FUNARG pl th)      mu (pl) = (LABEL x p1)
--     mu'     = mu [ (FUNARG p1 x p th) / p ]
--
-- the rule that "creates a circular structure": the new binding sends
-- the recursive variable x back to p itself.
--
-- This file proves the direction the paper calls difficult, its
-- V mu  |=  V mu' ("The proof in the other direction is more
-- difficult.  The difficulty seems to be that V mu involves a loop,
-- represented by the Y, within a loop, represented by the definition of
-- V").  Their fix is to cut BOTH loops, with two nested indices V_i and
-- Y_i.  Here there is one induction, on the derivation, and no fixed
-- point is constructed: `label-unfold` below is exactly their argument,
-- with derivation height in place of the index i.
--
-- Each obs-label step of the input derivation becomes one obs-funarg
-- step through the circular binding of the output.  Bot is the base
-- (their Y_0 = bottom), and the two ideal rules pass straight through.
------------------------------------------------------------------------

module LAZY.InvarianceL where

open import LAZY.Domain.Basic
open import LAZY.Domain.Order
open import LAZY.Syntax.Heap
open import LAZY.Syntax.Step
open import LAZY.Obs
open import LAZY.ObsIdeal
open import LAZY.ObsTransfer

module _ (mu : Heap) (p pl p1 : Addr) (th : Alist) (x : Var)
         (qp  : Eq (mu p)  (just (efunarg pl th)))
         (qpl : Eq (mu pl) (just (elabel x p1)))
         where

  nu : Heap
  nu = upd mu p (efunarg p1 (cons (mkSigma x p) th))

  step : Step mu nu
  step = st-L qp qpl

  -- p and pl are distinct: their cells hold different forms.
  private
    p-not-pl : Neg (Eq pl p)
    p-not-pl e = absurd (cell-clash mu p
                          (Eq-transport (\ z -> Eq (mu z) (just (elabel x p1))) e qpl)
                          qp)

    nu-pl : Eq (nu pl) (just (elabel x p1))
    nu-pl = Eq-trans (upd-miss mu p pl _ p-not-pl) qpl

    nu-p : Eq (nu p) (just (efunarg p1 (cons (mkSigma x p) th)))
    nu-p = upd-hit mu p _

    agree : (r : Addr) -> Neg (Eq r p) -> Eq (mu r) (nu r)
    agree r ne = Eq-sym (upd-miss mu p r _ ne)

  ----------------------------------------------------------------------
  -- THE ARGUMENT.
  --
  -- Everything observable of the LABEL cell in nu, in an environment
  -- rho2, is observable of p itself in rho, PROVIDED rho2 is the
  -- environment the FUNARG at p builds from rho.  Induction on the
  -- derivation; the obs-label case consumes one unfolding and produces
  -- one trip through the circular binding.
  ----------------------------------------------------------------------

  private
    -- rewriting along the injectivity of the cell contents
    lab-fix : {xb : Var} {pb : Addr} -> Eq x xb -> Eq p1 pb ->
      (rho2 : FinEnv) (u0 w : FinEl) ->
      Obs nu pb (ext rho2 xb u0) w -> Obs nu p1 (ext rho2 x u0) w
    lab-fix refl refl rho2 u0 w o = o

  label-unfold : (rho : FinEnv) (bs : FinEnv) ->
    ObsAlist nu rho th bs ->
    (w : FinEl) -> Obs nu pl (appendEnv bs rho) w -> Obs nu p rho w
  label-unfold rho bs oa w obs-bot = obs-bot
  label-unfold rho bs oa w (obs-var q2) = absurd (cell-clash nu pl nu-pl q2)
  label-unfold rho bs oa w (obs-quote q2) = absurd (cell-clash nu pl nu-pl q2)
  label-unfold rho bs oa w (obs-cons q2 _ _) = absurd (cell-clash nu pl nu-pl q2)
  label-unfold rho bs oa w (obs-car q2 _) = absurd (cell-clash nu pl nu-pl q2)
  label-unfold rho bs oa w (obs-cdr q2 _) = absurd (cell-clash nu pl nu-pl q2)
  label-unfold rho bs oa w (obs-atom-T q2 _) = absurd (cell-clash nu pl nu-pl q2)
  label-unfold rho bs oa w (obs-atom-NIL q2 _) = absurd (cell-clash nu pl nu-pl q2)
  label-unfold rho bs oa w (obs-eq-T q2 _ _ _) = absurd (cell-clash nu pl nu-pl q2)
  label-unfold rho bs oa w (obs-eq-NIL q2 _ _ _) = absurd (cell-clash nu pl nu-pl q2)
  label-unfold rho bs oa w (obs-if-T q2 _ _) = absurd (cell-clash nu pl nu-pl q2)
  label-unfold rho bs oa w (obs-if-NIL q2 _ _) = absurd (cell-clash nu pl nu-pl q2)
  label-unfold rho bs oa w (obs-app q2 _ _ _) = absurd (cell-clash nu pl nu-pl q2)
  label-unfold rho bs oa w (obs-lam q2 _ _) = absurd (cell-clash nu pl nu-pl q2)
  label-unfold rho bs oa w (obs-funarg q2 _ _) = absurd (cell-clash nu pl nu-pl q2)
  label-unfold rho bs oa w (obs-plus q2 _ _) = absurd (cell-clash nu pl nu-pl q2)
  label-unfold rho bs oa w (obs-label {p' = pb} {x = xb} {u = u0} q2 o0 o1) =
    -- u0 is what the recursion has been unfolded to so far; o0 is the
    -- SHORTER derivation of it, o1 the body one step further on.
    -- One obs-label step in, one trip through the circular binding out.
    obs-funarg nu-p
      (oa-cons (label-unfold rho bs oa u0 o0) oa)
      (lab-fix (elabel-inj1 (cell-eq {mu = nu} {p = pl} nu-pl q2))
               (elabel-inj2 (cell-eq {mu = nu} {p = pl} nu-pl q2))
               (appendEnv bs rho) u0 w o1)
  label-unfold rho bs oa w (obs-down o cu le) =
    obs-down (label-unfold rho bs oa _ o) cu le
  label-unfold rho bs oa w (obs-sup o1 o2 c) =
    obs-sup (label-unfold rho bs oa _ o1) (label-unfold rho bs oa _ o2) c

  ----------------------------------------------------------------------
  -- The local obligation of obs-transfer at the rewritten cell.
  ----------------------------------------------------------------------

  private
    local : (rho : FinEnv) (u : FinEl) ->
            CohEnv rho -> ObsAt mu nu p rho u -> Obs nu p rho u
    local rho u ce (at-var q2)         = absurd (cell-clash mu p qp q2)
    local rho u ce (at-quote q2)       = absurd (cell-clash mu p qp q2)
    local rho u ce (at-cons q2 _ _)    = absurd (cell-clash mu p qp q2)
    local rho u ce (at-car q2 _)       = absurd (cell-clash mu p qp q2)
    local rho u ce (at-cdr q2 _)       = absurd (cell-clash mu p qp q2)
    local rho u ce (at-atom-T q2 _)    = absurd (cell-clash mu p qp q2)
    local rho u ce (at-atom-NIL q2 _)  = absurd (cell-clash mu p qp q2)
    local rho u ce (at-eq-T q2 _ _ _)  = absurd (cell-clash mu p qp q2)
    local rho u ce (at-eq-NIL q2 _ _ _)= absurd (cell-clash mu p qp q2)
    local rho u ce (at-if-T q2 _ _)    = absurd (cell-clash mu p qp q2)
    local rho u ce (at-if-NIL q2 _ _)  = absurd (cell-clash mu p qp q2)
    local rho u ce (at-app q2 _ _ _)   = absurd (cell-clash mu p qp q2)
    local rho u ce (at-lam q2 _ _)     = absurd (cell-clash mu p qp q2)
    local rho u ce (at-label q2 _ _)   = absurd (cell-clash mu p qp q2)
    local rho u ce (at-plus q2 _ _)    = absurd (cell-clash mu p qp q2)
    local rho u ce (at-funarg {p0 = p0b} {th = thb} {bs = bs} q2 oa o) =
      fa-fix (efunarg-inj1 (cell-eq {mu = mu} {p = p} qp q2))
             (efunarg-inj2 (cell-eq {mu = mu} {p = p} qp q2))
             rho bs u oa o
      where
        fa-fix : {p0b : Addr} {thb : Alist} -> Eq pl p0b -> Eq th thb ->
          (rho2 bs2 : FinEnv) (u2 : FinEl) ->
          ObsAlist nu rho2 thb bs2 -> Obs nu p0b (appendEnv bs2 rho2) u2 ->
          Obs nu p rho2 u2
        fa-fix refl refl rho2 bs2 u2 oa2 o2 = label-unfold rho2 bs2 oa2 u2 o2

  ----------------------------------------------------------------------
  -- Rule [L] preserves every observation, at every cell.
  ----------------------------------------------------------------------

  L-forward : (r : Addr) (rho : FinEnv) (u : FinEl) ->
    CohEnv rho -> Obs mu r rho u -> Obs nu r rho u
  L-forward = obs-transfer mu nu p agree local
