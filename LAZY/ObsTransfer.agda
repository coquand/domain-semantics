{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- LAZY/ObsTransfer.agda        (L5, part 2 -- the transfer machinery)
--
-- Every one of the paper's rules rewrites a SINGLE cell (rules Fc and
-- Fd additionally allocate; see below).  So the invariance proof has
-- the same shape every time:
--
--   * at a cell OTHER than the rewritten one the two memories agree, so
--     the derivation is rebuilt verbatim from transported premises;
--   * at the rewritten cell we must say something specific to the rule.
--
-- `ObsAt mu nu p rho u' reifies exactly the second obligation: ONE
-- syntax-directed unfolding, reading the cell in `mu' but taking all
-- sub-observations in `nu'.  Then `obs-transfer' does the induction
-- once and for all, and each rule contributes only a short local lemma
--
--     (rho : FinEnv) (u : FinEl) -> ObsAt mu nu p0 rho u -> Obs nu p0 rho u
--
-- Bot, obs-down and obs-sup carry no cell, so they never reach the
-- local lemma: the generic part discharges them.
------------------------------------------------------------------------

module LAZY.ObsTransfer where

open import LAZY.Domain.Basic
open import LAZY.Domain.Order
open import LAZY.Syntax.Heap
open import LAZY.Obs
open import LAZY.ObsIdeal

------------------------------------------------------------------------
-- One syntax-directed unfolding: cell read in mu, premises in nu.
------------------------------------------------------------------------

data ObsAt (mu nu : Heap) (p : Addr) (rho : FinEnv) : FinEl -> Set where

  at-var :
    {x : Var} -> Eq (mu p) (just (evar x)) ->
    ObsAt mu nu p rho (lookupEnv rho x)

  at-quote :
    {a : Atom} -> Eq (mu p) (just (equote a)) ->
    ObsAt mu nu p rho (At a)

  at-cons :
    {p1 p2 : Addr} {u v : FinEl} ->
    Eq (mu p) (just (econs p1 p2)) ->
    Obs nu p1 rho u -> Obs nu p2 rho v ->
    ObsAt mu nu p rho (Prd u v)

  at-car :
    {p' : Addr} {u v : FinEl} ->
    Eq (mu p) (just (ecar p')) -> Obs nu p' rho (Prd u v) ->
    ObsAt mu nu p rho u

  at-cdr :
    {p' : Addr} {u v : FinEl} ->
    Eq (mu p) (just (ecdr p')) -> Obs nu p' rho (Prd u v) ->
    ObsAt mu nu p rho v

  at-atom-T :
    {p' : Addr} {a : Atom} ->
    Eq (mu p) (just (eatom p')) -> Obs nu p' rho (At a) ->
    ObsAt mu nu p rho (At T)

  at-atom-NIL :
    {p' : Addr} {u v : FinEl} ->
    Eq (mu p) (just (eatom p')) -> Obs nu p' rho (Prd u v) ->
    ObsAt mu nu p rho (At NIL)

  at-eq-T :
    {p1 p2 : Addr} {a1 a2 : Atom} ->
    Eq (mu p) (just (eeq p1 p2)) ->
    Obs nu p1 rho (At a1) -> Obs nu p2 rho (At a2) -> AtEq a1 a2 ->
    ObsAt mu nu p rho (At T)

  at-eq-NIL :
    {p1 p2 : Addr} {a1 a2 : Atom} ->
    Eq (mu p) (just (eeq p1 p2)) ->
    Obs nu p1 rho (At a1) -> Obs nu p2 rho (At a2) -> Neg (AtEq a1 a2) ->
    ObsAt mu nu p rho (At NIL)

  at-if-T :
    {p0 p1 p2 : Addr} {u : FinEl} ->
    Eq (mu p) (just (eif p0 p1 p2)) ->
    Obs nu p0 rho (At T) -> Obs nu p1 rho u ->
    ObsAt mu nu p rho u

  at-if-NIL :
    {p0 p1 p2 : Addr} {u : FinEl} ->
    Eq (mu p) (just (eif p0 p1 p2)) ->
    Obs nu p0 rho (At NIL) -> Obs nu p2 rho u ->
    ObsAt mu nu p rho u

  at-app :
    {p0 p1 : Addr} {g : FinFun} {u v : FinEl} ->
    Eq (mu p) (just (eapp p0 p1)) ->
    Obs nu p0 rho (Fn g) -> Obs nu p1 rho u -> InFun u v g ->
    ObsAt mu nu p rho v

  at-lam :
    {p' : Addr} {x : Var} {g : FinFun} ->
    Eq (mu p) (just (elam x p')) ->
    CoherentFun g -> ObsGraph nu p' x rho g ->
    ObsAt mu nu p rho (Fn g)

  at-label :
    {p' : Addr} {x : Var} {u v : FinEl} ->
    Eq (mu p) (just (elabel x p')) ->
    Obs nu p rho u -> Obs nu p' (ext rho x u) v ->
    ObsAt mu nu p rho v

  at-funarg :
    {p0 : Addr} {th : Alist} {bs : FinEnv} {u : FinEl} ->
    Eq (mu p) (just (efunarg p0 th)) ->
    ObsAlist nu rho th bs -> Obs nu p0 (appendEnv bs rho) u ->
    ObsAt mu nu p rho u

  at-plus :
    {p1 p2 : Addr} {m n : Nat} ->
    Eq (mu p) (just (eplus p1 p2)) ->
    Obs nu p1 rho (At (num m)) -> Obs nu p2 rho (At (num n)) ->
    ObsAt mu nu p rho (At (num (add m n)))

------------------------------------------------------------------------
-- Any unfolding that reads a cell OTHER than p0 is realised directly.
------------------------------------------------------------------------

module _ (mu nu : Heap) (p0 : Addr)
         (agree : (p : Addr) -> Neg (Eq p p0) -> Eq (mu p) (nu p))
         (local : (rho : FinEnv) (u : FinEl) ->
                  CohEnv rho -> ObsAt mu nu p0 rho u -> Obs nu p0 rho u)
         where

  private
    tr : (p : Addr) (e : Expr) -> Neg (Eq p p0) ->
         Eq (mu p) (just e) -> Eq (nu p) (just e)
    tr p e ne q = Eq-trans (Eq-sym (agree p ne)) q

  mutual
    obs-transfer : (p : Addr) (rho : FinEnv) (u : FinEl) ->
      CohEnv rho -> Obs mu p rho u -> Obs nu p rho u
    obs-transfer p rho u ce obs-bot = obs-bot
    obs-transfer p rho u ce (obs-down o cu le) =
      obs-down (obs-transfer p rho _ ce o) cu le
    obs-transfer p rho u ce (obs-sup o1 o2 c) =
      obs-sup (obs-transfer p rho _ ce o1) (obs-transfer p rho _ ce o2) c
    obs-transfer p rho u ce (obs-var q) with decEqNat p p0
    ... | inl refl = local rho u ce (at-var q)
    ... | inr ne   = obs-var (tr p _ ne q) 
    obs-transfer p rho u ce (obs-quote q) with decEqNat p p0
    ... | inl refl = local rho u ce (at-quote q)
    ... | inr ne   = obs-quote (tr p _ ne q) 
    obs-transfer p rho u ce (obs-cons q o1 o2) with decEqNat p p0
    ... | inl refl = local rho u ce (at-cons q (obs-transfer _ _ _ ce o1) (obs-transfer _ _ _ ce o2))
    ... | inr ne   = obs-cons (tr p _ ne q) (obs-transfer _ _ _ ce o1) (obs-transfer _ _ _ ce o2)
    obs-transfer p rho u ce (obs-car q o) with decEqNat p p0
    ... | inl refl = local rho u ce (at-car q (obs-transfer _ _ _ ce o))
    ... | inr ne   = obs-car (tr p _ ne q) (obs-transfer _ _ _ ce o)
    obs-transfer p rho u ce (obs-cdr q o) with decEqNat p p0
    ... | inl refl = local rho u ce (at-cdr q (obs-transfer _ _ _ ce o))
    ... | inr ne   = obs-cdr (tr p _ ne q) (obs-transfer _ _ _ ce o)
    obs-transfer p rho u ce (obs-atom-T q o) with decEqNat p p0
    ... | inl refl = local rho u ce (at-atom-T q (obs-transfer _ _ _ ce o))
    ... | inr ne   = obs-atom-T (tr p _ ne q) (obs-transfer _ _ _ ce o)
    obs-transfer p rho u ce (obs-atom-NIL q o) with decEqNat p p0
    ... | inl refl = local rho u ce (at-atom-NIL q (obs-transfer _ _ _ ce o))
    ... | inr ne   = obs-atom-NIL (tr p _ ne q) (obs-transfer _ _ _ ce o)
    obs-transfer p rho u ce (obs-eq-T q o1 o2 h) with decEqNat p p0
    ... | inl refl = local rho u ce (at-eq-T q (obs-transfer _ _ _ ce o1) (obs-transfer _ _ _ ce o2) h)
    ... | inr ne   = obs-eq-T (tr p _ ne q) (obs-transfer _ _ _ ce o1) (obs-transfer _ _ _ ce o2) h
    obs-transfer p rho u ce (obs-eq-NIL q o1 o2 h) with decEqNat p p0
    ... | inl refl = local rho u ce (at-eq-NIL q (obs-transfer _ _ _ ce o1) (obs-transfer _ _ _ ce o2) h)
    ... | inr ne   = obs-eq-NIL (tr p _ ne q) (obs-transfer _ _ _ ce o1) (obs-transfer _ _ _ ce o2) h
    obs-transfer p rho u ce (obs-if-T q o0 o1) with decEqNat p p0
    ... | inl refl = local rho u ce (at-if-T q (obs-transfer _ _ _ ce o0) (obs-transfer _ _ _ ce o1))
    ... | inr ne   = obs-if-T (tr p _ ne q) (obs-transfer _ _ _ ce o0) (obs-transfer _ _ _ ce o1)
    obs-transfer p rho u ce (obs-if-NIL q o0 o2) with decEqNat p p0
    ... | inl refl = local rho u ce (at-if-NIL q (obs-transfer _ _ _ ce o0) (obs-transfer _ _ _ ce o2))
    ... | inr ne   = obs-if-NIL (tr p _ ne q) (obs-transfer _ _ _ ce o0) (obs-transfer _ _ _ ce o2)
    obs-transfer p rho u ce (obs-app q of oa i) with decEqNat p p0
    ... | inl refl = local rho u ce (at-app q (obs-transfer _ _ _ ce of) (obs-transfer _ _ _ ce oa) i)
    ... | inr ne   = obs-app (tr p _ ne q) (obs-transfer _ _ _ ce of) (obs-transfer _ _ _ ce oa) i
    obs-transfer p rho u ce (obs-label {x = x} {u = u0} q o0 o1) with decEqNat p p0
    ... | inl refl =
      local rho u ce (at-label q (obs-transfer _ _ _ ce o0)
        (obs-transfer _ _ _ (CohEnv-ext rho x u0 ce (Obs-Coherent ce o0)) o1))
    ... | inr ne   =
      obs-label (tr p _ ne q) (obs-transfer _ _ _ ce o0)
        (obs-transfer _ _ _ (CohEnv-ext rho x u0 ce (Obs-Coherent ce o0)) o1)
    obs-transfer p rho u ce (obs-plus q o1 o2) with decEqNat p p0
    ... | inl refl = local rho u ce (at-plus q (obs-transfer _ _ _ ce o1) (obs-transfer _ _ _ ce o2))
    ... | inr ne   = obs-plus (tr p _ ne q) (obs-transfer _ _ _ ce o1) (obs-transfer _ _ _ ce o2)
    obs-transfer p rho u ce (obs-lam {p' = pb} {x = x} {g = g} q coh og) with decEqNat p p0
    ... | inl refl = local rho u ce (at-lam q coh (graph-transfer pb rho x g ce coh og))
    ... | inr ne   = obs-lam (tr p _ ne q) coh (graph-transfer pb rho x g ce coh og)
    obs-transfer p rho u ce (obs-funarg {bs = bs} q oa o) with decEqNat p p0
    ... | inl refl =
      local rho u ce (at-funarg q (alist-transfer rho _ bs ce oa)
        (obs-transfer _ _ _ (CohEnv-append bs rho (ObsAlist-Coherent ce oa) ce) o))
    ... | inr ne   =
      obs-funarg (tr p _ ne q) (alist-transfer rho _ bs ce oa)
        (obs-transfer _ _ _ (CohEnv-append bs rho (ObsAlist-Coherent ce oa) ce) o)

    graph-transfer : (p' : Addr) (rho : FinEnv) (x : Var) (g : FinFun) ->
      CohEnv rho -> CoherentFun g ->
      ObsGraph mu p' x rho g -> ObsGraph nu p' x rho g
    graph-transfer p' rho x nil        ce coh og-nil = og-nil
    graph-transfer p' rho x (cons q qs) ce coh (og-cons o og) =
      og-cons (obs-transfer _ _ _
                (CohEnv-ext rho x (fst q) ce (CFcons.key-coh coh)) o)
              (graph-transfer p' rho x qs ce (CFcons.tail-coh coh) og)

    alist-transfer : (rho : FinEnv) (th : Alist) (bs : FinEnv) ->
      CohEnv rho -> ObsAlist mu rho th bs -> ObsAlist nu rho th bs
    alist-transfer rho nil bs ce oa-nil = oa-nil
    alist-transfer rho (cons b th) (cons c bs) ce (oa-cons o oas) =
      oa-cons (obs-transfer _ _ _ ce o) (alist-transfer rho th bs ce oas)
