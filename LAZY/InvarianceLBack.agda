{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- LAZY/InvarianceLBack.agda        (L5 -- rule [L], the other direction)
--
-- The paper calls this one simple: "It is simple to show that V mu
-- satisfies the equation for V mu' so V mu' |= V mu."
--
-- In the finite-element presentation it is the HARDER of the two, and
-- the reason is precise.  In nu the cell p holds
--
--     (FUNARG p1 x p th)
--
-- so every trip through the circular binding re-observes the alist th
-- INDEPENDENTLY and may choose different values each time.  In mu the
-- cell holds (FUNARG pl th) with mu(pl) = (LABEL x p1), and the LABEL
-- re-observes itself in ONE fixed environment: a single binding list
-- serves every unfolding.
--
-- So turning a nu-derivation into a mu-derivation means collapsing many
-- independently chosen binding lists into one.  That is a JOIN, and a
-- join of two observations of the same cell needs them to be
-- compatible: this direction rests on CONSISTENCY, which the forward
-- direction (LAZY.InvarianceL) never needed.
------------------------------------------------------------------------

module LAZY.InvarianceLBack where

open import LAZY.Domain.Basic
open import LAZY.Domain.Order
open import LAZY.Syntax.Heap
open import LAZY.Syntax.Step
open import LAZY.Obs
open import LAZY.ObsIdeal
open import LAZY.ObsConsistent
open import LAZY.ObsTransfer

private
  ifNatEq-Le : (m n : Nat) (t t' e e' : FinEl) ->
    LeCode t t' -> LeCode e e' -> LeCode (ifNatEq m n t e) (ifNatEq m n t' e')
  ifNatEq-Le zero    zero    t t' e e' lt le = lt
  ifNatEq-Le zero    (suc n) t t' e e' lt le = le
  ifNatEq-Le (suc m) zero    t t' e e' lt le = le
  ifNatEq-Le (suc m) (suc n) t t' e e' lt le = ifNatEq-Le m n t t' e e' lt le

------------------------------------------------------------------------
-- The join of two observations of the same alist.
--
-- Consistency (obs-comp) supplies the compatibility at each entry, so
-- the entries can be joined with obs-sup; the two LeEnv fields say the
-- joint bindings dominate both.
------------------------------------------------------------------------

record AJoin (mu : Heap) (rho : FinEnv) (th : Alist) (b1 b2 : FinEnv) : Set where
  constructor mkAJoin
  field
    bJ  : FinEnv
    oaJ : ObsAlist mu rho th bJ
    cJ  : CohEnv bJ
    l1  : LeEnv (appendEnv b1 rho) (appendEnv bJ rho)
    l2  : LeEnv (appendEnv b2 rho) (appendEnv bJ rho)

alist-join : {mu : Heap} (rho : FinEnv) -> CohEnv rho -> (th : Alist) ->
  {b1 b2 : FinEnv} ->
  ObsAlist mu rho th b1 -> ObsAlist mu rho th b2 -> AJoin mu rho th b1 b2
alist-join rho ce nil oa-nil oa-nil =
  mkAJoin nil oa-nil tt (LeEnv-refl rho ce) (LeEnv-refl rho ce)
alist-join rho ce (cons b bs) (oa-cons {u = u1} o1 os1) (oa-cons {u = u2} o2 os2) =
  let r   = alist-join rho ce bs os1 os2
      c   = obs-comp (CompEnv-refl rho ce) o1 o2
      cu1 = Obs-Coherent ce o1
      cu2 = Obs-Coherent ce o2
  in mkAJoin
       (cons (mkSigma (fst b) (Sup u1 u2)) (AJoin.bJ r))
       (oa-cons (obs-sup o1 o2 c) (AJoin.oaJ r))
       (mkSigma (Coherent-Sup u1 u2 c cu1 cu2) (AJoin.cJ r))
       (\ y -> ifNatEq-Le (fst b) y u1 (Sup u1 u2) _ _
                  (LeCode-Sup-left u1 u2 c cu1 cu2) (AJoin.l1 r y))
       (\ y -> ifNatEq-Le (fst b) y u2 (Sup u1 u2) _ _
                  (LeCode-Sup-right u1 u2 c cu1 cu2) (AJoin.l2 r y))

------------------------------------------------------------------------
-- The all-Bot bindings (the base case of funarg-into).
------------------------------------------------------------------------

allBot : Alist -> FinEnv
allBot nil         = nil
allBot (cons b bs) = cons (mkSigma (fst b) Bot) (allBot bs)

alist-bot : {mu : Heap} {rho : FinEnv} (th : Alist) ->
  ObsAlist mu rho th (allBot th)
alist-bot nil         = oa-nil
alist-bot (cons b bs) = oa-cons obs-bot (alist-bot bs)

allBot-Coh : (th : Alist) -> CohEnv (allBot th)
allBot-Coh nil         = tt
allBot-Coh (cons b bs) = mkSigma tt (allBot-Coh bs)

------------------------------------------------------------------------

module _ (mu : Heap) (p pl p1 : Addr) (th : Alist) (x : Var)
         (qp  : Eq (mu p)  (just (efunarg pl th)))
         (qpl : Eq (mu pl) (just (elabel x p1)))
         where

  nu : Heap
  nu = upd mu p (efunarg p1 (cons (mkSigma x p) th))

  ----------------------------------------------------------------------
  -- Every observation of the FUNARG cell p in mu comes with its OWN
  -- binding list, and is an observation of the LABEL cell under it.
  --
  -- The obs-sup case is where consistency is spent: two sub-derivations
  -- arrive with two different binding lists, which have to be joined.
  ----------------------------------------------------------------------

  record IntoLabel (rho : FinEnv) (w : FinEl) : Set where
    constructor mkInto
    field
      bnds : FinEnv
      obsA : ObsAlist mu rho th bnds
      obsL : Obs mu pl (appendEnv bnds rho) w

  funarg-into : (rho : FinEnv) -> CohEnv rho ->
    (w : FinEl) -> Obs mu p rho w -> IntoLabel rho w
  funarg-into rho ce w obs-bot = mkInto (allBot th) (alist-bot th) obs-bot
  funarg-into rho ce w (obs-var q2) = absurd (cell-clash mu p qp q2)
  funarg-into rho ce w (obs-quote q2) = absurd (cell-clash mu p qp q2)
  funarg-into rho ce w (obs-cons q2 _ _) = absurd (cell-clash mu p qp q2)
  funarg-into rho ce w (obs-car q2 _) = absurd (cell-clash mu p qp q2)
  funarg-into rho ce w (obs-cdr q2 _) = absurd (cell-clash mu p qp q2)
  funarg-into rho ce w (obs-atom-T q2 _) = absurd (cell-clash mu p qp q2)
  funarg-into rho ce w (obs-atom-NIL q2 _) = absurd (cell-clash mu p qp q2)
  funarg-into rho ce w (obs-eq-T q2 _ _ _) = absurd (cell-clash mu p qp q2)
  funarg-into rho ce w (obs-eq-NIL q2 _ _ _) = absurd (cell-clash mu p qp q2)
  funarg-into rho ce w (obs-if-T q2 _ _) = absurd (cell-clash mu p qp q2)
  funarg-into rho ce w (obs-if-NIL q2 _ _) = absurd (cell-clash mu p qp q2)
  funarg-into rho ce w (obs-app q2 _ _ _) = absurd (cell-clash mu p qp q2)
  funarg-into rho ce w (obs-lam q2 _ _) = absurd (cell-clash mu p qp q2)
  funarg-into rho ce w (obs-label q2 _ _) = absurd (cell-clash mu p qp q2)
  funarg-into rho ce w (obs-plus q2 _ _) = absurd (cell-clash mu p qp q2)
  funarg-into rho ce w (obs-funarg {p0 = p0b} {th = thb} {bs = bs} q2 oa o)
    with cell-eq {mu = mu} {p = p} qp q2
  ... | refl = mkInto bs oa o
  funarg-into rho ce w (obs-down o cu le) =
    let r = funarg-into rho ce _ o
    in mkInto (IntoLabel.bnds r) (IntoLabel.obsA r)
              (obs-down (IntoLabel.obsL r) cu le)
  funarg-into rho ce w (obs-sup {u = w1} {v = w2} o1 o2 c) =
    let r1 = funarg-into rho ce w1 o1
        r2 = funarg-into rho ce w2 o2
        b1 = IntoLabel.bnds r1
        b2 = IntoLabel.bnds r2
        c1 = ObsAlist-Coherent ce (IntoLabel.obsA r1)
        c2 = ObsAlist-Coherent ce (IntoLabel.obsA r2)
        j  = alist-join rho ce th (IntoLabel.obsA r1) (IntoLabel.obsA r2)
    in mkInto (AJoin.bJ j) (AJoin.oaJ j)
         (obs-sup
           (obs-env-mono (CohEnv-append b1 rho c1 ce) (AJoin.l1 j) (IntoLabel.obsL r1))
           (obs-env-mono (CohEnv-append b2 rho c2 ce) (AJoin.l2 j) (IntoLabel.obsL r2))
           c)

  ----------------------------------------------------------------------
  -- The local obligation, and the theorem.
  ----------------------------------------------------------------------

  private
    nu-p : Eq (nu p) (just (efunarg p1 (cons (mkSigma x p) th)))
    nu-p = upd-hit mu p _

    agree : (r : Addr) -> Neg (Eq r p) -> Eq (nu r) (mu r)
    agree r ne = upd-miss mu p r _ ne

    local : (rho : FinEnv) (u : FinEl) ->
            CohEnv rho -> ObsAt nu mu p rho u -> Obs mu p rho u
    local rho u ce (at-var q2)          = absurd (cell-clash nu p nu-p q2)
    local rho u ce (at-quote q2)        = absurd (cell-clash nu p nu-p q2)
    local rho u ce (at-cons q2 _ _)     = absurd (cell-clash nu p nu-p q2)
    local rho u ce (at-car q2 _)        = absurd (cell-clash nu p nu-p q2)
    local rho u ce (at-cdr q2 _)        = absurd (cell-clash nu p nu-p q2)
    local rho u ce (at-atom-T q2 _)     = absurd (cell-clash nu p nu-p q2)
    local rho u ce (at-atom-NIL q2 _)   = absurd (cell-clash nu p nu-p q2)
    local rho u ce (at-eq-T q2 _ _ _)   = absurd (cell-clash nu p nu-p q2)
    local rho u ce (at-eq-NIL q2 _ _ _) = absurd (cell-clash nu p nu-p q2)
    local rho u ce (at-if-T q2 _ _)     = absurd (cell-clash nu p nu-p q2)
    local rho u ce (at-if-NIL q2 _ _)   = absurd (cell-clash nu p nu-p q2)
    local rho u ce (at-app q2 _ _ _)    = absurd (cell-clash nu p nu-p q2)
    local rho u ce (at-lam q2 _ _)      = absurd (cell-clash nu p nu-p q2)
    local rho u ce (at-label q2 _ _)    = absurd (cell-clash nu p nu-p q2)
    local rho u ce (at-plus q2 _ _)     = absurd (cell-clash nu p nu-p q2)
    local rho u ce (at-funarg q2 oa o) with cell-eq {mu = nu} {p = p} nu-p q2
    ... | refl = go oa o
      where
        go : {bs' : FinEnv} ->
             ObsAlist mu rho (cons (mkSigma x p) th) bs' ->
             Obs mu p1 (appendEnv bs' rho) u -> Obs mu p rho u
        go (oa-cons {bs = bs2} {u = w} ow oas) o2 =
          let r  = funarg-into rho ce w ow
              b1 = IntoLabel.bnds r
              c1 = ObsAlist-Coherent ce (IntoLabel.obsA r)
              c2 = ObsAlist-Coherent ce oas
              j  = alist-join rho ce th (IntoLabel.obsA r) oas
              -- the LABEL's own unfolding, lifted to the joint bindings
              oL = obs-env-mono (CohEnv-append b1 rho c1 ce) (AJoin.l1 j)
                     (IntoLabel.obsL r)
              -- the body, lifted to the joint bindings
              oB = obs-env-mono
                     (CohEnv-ext (appendEnv bs2 rho) x w
                       (CohEnv-append bs2 rho c2 ce) (Obs-Coherent ce ow))
                     (LeEnv-ext (appendEnv bs2 rho) (appendEnv (AJoin.bJ j) rho) x w
                       (AJoin.l2 j) (Obs-Coherent ce ow))
                     o2
          in obs-funarg qp (AJoin.oaJ j) (obs-label qpl oL oB)

  L-backward : (r : Addr) (rho : FinEnv) (u : FinEl) ->
    CohEnv rho -> Obs nu r rho u -> Obs mu r rho u
  L-backward = obs-transfer nu mu p agree local
