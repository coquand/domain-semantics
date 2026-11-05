{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- LAZY/ObsConsistent.agda        (L4, completed -- CONSISTENCY)
--
-- The third ideal property: two observations of the same cell are
-- always compatible.  Stated for two POSSIBLY DIFFERENT environments,
-- because the LAMBDA clause compares the body under two different
-- bindings of the abstracted variable and the induction has to follow.
--
--     CompEnv rho1 rho2 -> Obs mu p rho1 u -> Obs mu p rho2 v -> Comp u v
--
-- Induction on both derivations.  The three ideal constructors are
-- handled first on each side (Comp-down / comp-Sup / comp-Sup-sym); the
-- remaining pairs are decided by the cell contents, and the impossible
-- ones -- one cell cannot hold two different forms -- are killed
-- uniformly by matching `cell-eq' at refl.
--
-- Consequences: the observations at a cell really are a consistent
-- ideal, so the SHAPE of the value is well defined (no cell is both an
-- atom and a pair); and the alist of a FUNARG has a well-defined join,
-- which is what rule [L]'s easy direction needs.

-- (--exact-split is off here only for the three clauses that dispatch on
-- the RIGHT ideal constructor with the left derivation still abstract;
-- that catch-all is deliberate and saves 48 clauses.)
------------------------------------------------------------------------

module LAZY.ObsConsistent where

open import LAZY.Domain.Basic
open import LAZY.Domain.Order
open import LAZY.Syntax.Heap
open import LAZY.Obs
open import LAZY.ObsIdeal

------------------------------------------------------------------------
-- Compatible environments
------------------------------------------------------------------------

CompEnv : FinEnv -> FinEnv -> Set
CompEnv rho1 rho2 = (x : Var) -> Comp (lookupEnv rho1 x) (lookupEnv rho2 x)

-- two binding lists for the SAME alist: same variables, compatible values
data CompBnd : FinEnv -> FinEnv -> Set where
  cb-nil  : CompBnd nil nil
  cb-cons : {x : Var} {u v : FinEl} {b1 b2 : FinEnv} ->
            Comp u v -> CompBnd b1 b2 ->
            CompBnd (cons (mkSigma x u) b1) (cons (mkSigma x v) b2)

private
  ifNatEq-Comp : (m n : Nat) (t t' e e' : FinEl) ->
    Comp t t' -> Comp e e' -> Comp (ifNatEq m n t e) (ifNatEq m n t' e')
  ifNatEq-Comp zero    zero    t t' e e' ct ce = ct
  ifNatEq-Comp zero    (suc n) t t' e e' ct ce = ce
  ifNatEq-Comp (suc m) zero    t t' e e' ct ce = ce
  ifNatEq-Comp (suc m) (suc n) t t' e e' ct ce = ifNatEq-Comp m n t t' e e' ct ce

  add-comp : {ma na mb nb : Nat} ->
    Comp (At (num ma)) (At (num mb)) -> Comp (At (num na)) (At (num nb)) ->
    Comp (At (num (add ma na))) (At (num (add mb nb)))
  add-comp {ma} {na} {mb} {nb} c1 c2 =
    AtEq-of-Eq (num (add ma na)) (num (add mb nb))
      (Eq-cong num (add-eq (NatEq-sound ma mb c1) (NatEq-sound na nb c2)))
    where
      add-eq : {a b c d : Nat} -> Eq a b -> Eq c d -> Eq (add a c) (add b d)
      add-eq refl refl = refl

CompEnv-ext : {rho1 rho2 : FinEnv} {x : Var} {u v : FinEl} ->
  CompEnv rho1 rho2 -> Comp u v -> CompEnv (ext rho1 x u) (ext rho2 x v)
CompEnv-ext {rho1} {rho2} {x} {u} {v} ce c y =
  ifNatEq-Comp x y u v (lookupEnv rho1 y) (lookupEnv rho2 y) c (ce y)

CompEnv-append : {b1 b2 rho1 rho2 : FinEnv} ->
  CompBnd b1 b2 -> CompEnv rho1 rho2 ->
  CompEnv (appendEnv b1 rho1) (appendEnv b2 rho2)
CompEnv-append cb-nil                       ce = ce
CompEnv-append (cb-cons {x = x} {u} {v} c cb) ce y =
  ifNatEq-Comp x y u v _ _ c (CompEnv-append cb ce y)

------------------------------------------------------------------------
-- Reading a compatible pair of finite graphs
------------------------------------------------------------------------

private
  CompStep-lookup : (s : Pair FinEl FinEl) (h : FinFun) {u2 v2 : FinEl} ->
    CompStepFun s h -> InFun u2 v2 h -> Comp (fst s) u2 -> Comp (snd s) v2
  CompStep-lookup s (cons t hs) csf in-here      c = fst csf c
  CompStep-lookup s (cons t hs) csf (in-there i) c =
    CompStep-lookup s hs (snd csf) i c

CompFun-lookup : (g h : FinFun) {u v u2 v2 : FinEl} ->
  CompFun g h -> InFun u v g -> InFun u2 v2 h -> Comp u u2 -> Comp v v2
CompFun-lookup (cons s gs) h cf in-here      i2 c = CompStep-lookup s h (fst cf) i2 c
CompFun-lookup (cons s gs) h cf (in-there i) i2 c = CompFun-lookup gs h (snd cf) i i2 c

------------------------------------------------------------------------
-- CONSISTENCY
------------------------------------------------------------------------

mutual
  obs-comp : {mu : Heap} {p : Addr} {rho1 rho2 : FinEnv} {u v : FinEl} ->
    CompEnv rho1 rho2 -> Obs mu p rho1 u -> Obs mu p rho2 v -> Comp u v

  -- the ideal constructors, left then right
  obs-comp ce obs-bot ob = tt
  obs-comp {v = v} ce (obs-down {u = w} {u' = w'} o cu le) ob =
    Comp-down w' w v le (obs-comp ce o ob)
  obs-comp {v = v} ce (obs-sup {u = w1} {v = w2} o1 o2 c) ob =
    comp-Sup-sym w1 w2 v (obs-comp ce o1 ob) (obs-comp ce o2 ob)
  obs-comp {u = u} ce oa obs-bot = comp-Bot-r u
  obs-comp {u = u} ce oa (obs-down {u = w} {u' = w'} o cu le) =
    Comp-sym w' u (Comp-down w' w u le (Comp-sym u w (obs-comp ce oa o)))
  obs-comp {u = u} ce oa (obs-sup {u = w1} {v = w2} o1 o2 c) =
    comp-Sup u w1 w2 (obs-comp ce oa o1) (obs-comp ce oa o2)

  -- both syntax-directed: the cell decides
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-var {x = xa} qa) (obs-var {x = xb} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | refl = ce xa
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-var {x = xa} qa) (obs-quote {a = ta} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-var {x = xa} qa) (obs-cons qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-var {x = xa} qa) (obs-car qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-var {x = xa} qa) (obs-cdr qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-var {x = xa} qa) (obs-atom-T qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-var {x = xa} qa) (obs-atom-NIL qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-var {x = xa} qa) (obs-eq-T {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-var {x = xa} qa) (obs-eq-NIL {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-var {x = xa} qa) (obs-if-T qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-var {x = xa} qa) (obs-if-NIL qb b0 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-var {x = xa} qa) (obs-app qb bf ba ib)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-var {x = xa} qa) (obs-lam qb cb ogb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-var {x = xa} qa) (obs-label {x = xb} {u = ub} qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-var {x = xa} qa) (obs-funarg qb oab ab)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-var {x = xa} qa) (obs-plus {m = mb} {n = nb} qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-quote {a = sa} qa) (obs-var {x = xb} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-quote {a = sa} qa) (obs-quote {a = ta} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | refl = AtEq-refl sa
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-quote {a = sa} qa) (obs-cons qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-quote {a = sa} qa) (obs-car qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-quote {a = sa} qa) (obs-cdr qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-quote {a = sa} qa) (obs-atom-T qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-quote {a = sa} qa) (obs-atom-NIL qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-quote {a = sa} qa) (obs-eq-T {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-quote {a = sa} qa) (obs-eq-NIL {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-quote {a = sa} qa) (obs-if-T qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-quote {a = sa} qa) (obs-if-NIL qb b0 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-quote {a = sa} qa) (obs-app qb bf ba ib)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-quote {a = sa} qa) (obs-lam qb cb ogb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-quote {a = sa} qa) (obs-label {x = xb} {u = ub} qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-quote {a = sa} qa) (obs-funarg qb oab ab)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-quote {a = sa} qa) (obs-plus {m = mb} {n = nb} qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cons qa a1 a2) (obs-var {x = xb} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cons qa a1 a2) (obs-quote {a = ta} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cons qa a1 a2) (obs-cons qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | refl = mkSigma (obs-comp ce a1 b1) (obs-comp ce a2 b2)
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cons qa a1 a2) (obs-car qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cons qa a1 a2) (obs-cdr qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cons qa a1 a2) (obs-atom-T qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cons qa a1 a2) (obs-atom-NIL qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cons qa a1 a2) (obs-eq-T {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cons qa a1 a2) (obs-eq-NIL {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cons qa a1 a2) (obs-if-T qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cons qa a1 a2) (obs-if-NIL qb b0 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cons qa a1 a2) (obs-app qb bf ba ib)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cons qa a1 a2) (obs-lam qb cb ogb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cons qa a1 a2) (obs-label {x = xb} {u = ub} qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cons qa a1 a2) (obs-funarg qb oab ab)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cons qa a1 a2) (obs-plus {m = mb} {n = nb} qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-car qa a1) (obs-var {x = xb} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-car qa a1) (obs-quote {a = ta} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-car qa a1) (obs-cons qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-car qa a1) (obs-car qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | refl = fst (obs-comp ce a1 b1)
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-car qa a1) (obs-cdr qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-car qa a1) (obs-atom-T qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-car qa a1) (obs-atom-NIL qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-car qa a1) (obs-eq-T {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-car qa a1) (obs-eq-NIL {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-car qa a1) (obs-if-T qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-car qa a1) (obs-if-NIL qb b0 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-car qa a1) (obs-app qb bf ba ib)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-car qa a1) (obs-lam qb cb ogb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-car qa a1) (obs-label {x = xb} {u = ub} qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-car qa a1) (obs-funarg qb oab ab)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-car qa a1) (obs-plus {m = mb} {n = nb} qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cdr qa a1) (obs-var {x = xb} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cdr qa a1) (obs-quote {a = ta} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cdr qa a1) (obs-cons qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cdr qa a1) (obs-car qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cdr qa a1) (obs-cdr qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | refl = snd (obs-comp ce a1 b1)
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cdr qa a1) (obs-atom-T qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cdr qa a1) (obs-atom-NIL qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cdr qa a1) (obs-eq-T {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cdr qa a1) (obs-eq-NIL {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cdr qa a1) (obs-if-T qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cdr qa a1) (obs-if-NIL qb b0 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cdr qa a1) (obs-app qb bf ba ib)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cdr qa a1) (obs-lam qb cb ogb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cdr qa a1) (obs-label {x = xb} {u = ub} qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cdr qa a1) (obs-funarg qb oab ab)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-cdr qa a1) (obs-plus {m = mb} {n = nb} qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-T qa a1) (obs-var {x = xb} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-T qa a1) (obs-quote {a = ta} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-T qa a1) (obs-cons qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-T qa a1) (obs-car qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-T qa a1) (obs-cdr qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-T qa a1) (obs-atom-T qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | refl = tt
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-T qa a1) (obs-atom-NIL qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | refl = absurd (obs-comp ce a1 b1)
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-T qa a1) (obs-eq-T {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-T qa a1) (obs-eq-NIL {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-T qa a1) (obs-if-T qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-T qa a1) (obs-if-NIL qb b0 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-T qa a1) (obs-app qb bf ba ib)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-T qa a1) (obs-lam qb cb ogb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-T qa a1) (obs-label {x = xb} {u = ub} qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-T qa a1) (obs-funarg qb oab ab)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-T qa a1) (obs-plus {m = mb} {n = nb} qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-NIL qa a1) (obs-var {x = xb} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-NIL qa a1) (obs-quote {a = ta} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-NIL qa a1) (obs-cons qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-NIL qa a1) (obs-car qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-NIL qa a1) (obs-cdr qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-NIL qa a1) (obs-atom-T qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | refl = absurd (obs-comp ce a1 b1)
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-NIL qa a1) (obs-atom-NIL qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | refl = tt
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-NIL qa a1) (obs-eq-T {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-NIL qa a1) (obs-eq-NIL {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-NIL qa a1) (obs-if-T qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-NIL qa a1) (obs-if-NIL qb b0 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-NIL qa a1) (obs-app qb bf ba ib)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-NIL qa a1) (obs-lam qb cb ogb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-NIL qa a1) (obs-label {x = xb} {u = ub} qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-NIL qa a1) (obs-funarg qb oab ab)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-atom-NIL qa a1) (obs-plus {m = mb} {n = nb} qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-T {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-var {x = xb} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-T {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-quote {a = ta} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-T {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-cons qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-T {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-car qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-T {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-cdr qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-T {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-atom-T qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-T {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-atom-NIL qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-T {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-eq-T {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | refl = tt
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-T {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-eq-NIL {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | refl = absurd (hb (AtEq-trans t1 s1 t2 (AtEq-sym s1 t1 (obs-comp ce a1 b1))
                            (AtEq-trans s1 s2 t2 ha (obs-comp ce a2 b2))))
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-T {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-if-T qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-T {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-if-NIL qb b0 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-T {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-app qb bf ba ib)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-T {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-lam qb cb ogb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-T {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-label {x = xb} {u = ub} qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-T {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-funarg qb oab ab)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-T {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-plus {m = mb} {n = nb} qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-NIL {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-var {x = xb} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-NIL {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-quote {a = ta} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-NIL {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-cons qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-NIL {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-car qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-NIL {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-cdr qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-NIL {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-atom-T qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-NIL {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-atom-NIL qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-NIL {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-eq-T {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | refl = absurd (ha (AtEq-trans s1 t1 s2 (obs-comp ce a1 b1)
                            (AtEq-trans t1 t2 s2 hb (AtEq-sym s2 t2 (obs-comp ce a2 b2)))))
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-NIL {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-eq-NIL {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | refl = tt
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-NIL {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-if-T qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-NIL {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-if-NIL qb b0 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-NIL {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-app qb bf ba ib)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-NIL {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-lam qb cb ogb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-NIL {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-label {x = xb} {u = ub} qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-NIL {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-funarg qb oab ab)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-eq-NIL {a1 = s1} {a2 = s2} qa a1 a2 ha) (obs-plus {m = mb} {n = nb} qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-T qa a0 a1) (obs-var {x = xb} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-T qa a0 a1) (obs-quote {a = ta} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-T qa a0 a1) (obs-cons qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-T qa a0 a1) (obs-car qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-T qa a0 a1) (obs-cdr qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-T qa a0 a1) (obs-atom-T qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-T qa a0 a1) (obs-atom-NIL qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-T qa a0 a1) (obs-eq-T {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-T qa a0 a1) (obs-eq-NIL {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-T qa a0 a1) (obs-if-T qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | refl = obs-comp ce a1 b1
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-T qa a0 a1) (obs-if-NIL qb b0 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | refl = absurd (obs-comp ce a0 b0)
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-T qa a0 a1) (obs-app qb bf ba ib)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-T qa a0 a1) (obs-lam qb cb ogb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-T qa a0 a1) (obs-label {x = xb} {u = ub} qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-T qa a0 a1) (obs-funarg qb oab ab)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-T qa a0 a1) (obs-plus {m = mb} {n = nb} qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-NIL qa a0 a2) (obs-var {x = xb} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-NIL qa a0 a2) (obs-quote {a = ta} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-NIL qa a0 a2) (obs-cons qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-NIL qa a0 a2) (obs-car qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-NIL qa a0 a2) (obs-cdr qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-NIL qa a0 a2) (obs-atom-T qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-NIL qa a0 a2) (obs-atom-NIL qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-NIL qa a0 a2) (obs-eq-T {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-NIL qa a0 a2) (obs-eq-NIL {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-NIL qa a0 a2) (obs-if-T qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | refl = absurd (obs-comp ce a0 b0)
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-NIL qa a0 a2) (obs-if-NIL qb b0 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | refl = obs-comp ce a2 b2
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-NIL qa a0 a2) (obs-app qb bf ba ib)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-NIL qa a0 a2) (obs-lam qb cb ogb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-NIL qa a0 a2) (obs-label {x = xb} {u = ub} qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-NIL qa a0 a2) (obs-funarg qb oab ab)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-if-NIL qa a0 a2) (obs-plus {m = mb} {n = nb} qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-app qa af aa ia) (obs-var {x = xb} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-app qa af aa ia) (obs-quote {a = ta} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-app qa af aa ia) (obs-cons qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-app qa af aa ia) (obs-car qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-app qa af aa ia) (obs-cdr qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-app qa af aa ia) (obs-atom-T qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-app qa af aa ia) (obs-atom-NIL qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-app qa af aa ia) (obs-eq-T {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-app qa af aa ia) (obs-eq-NIL {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-app qa af aa ia) (obs-if-T qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-app qa af aa ia) (obs-if-NIL qb b0 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-app qa af aa ia) (obs-app qb bf ba ib)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | refl = CompFun-lookup _ _ (obs-comp ce af bf) ia ib (obs-comp ce aa ba)
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-app qa af aa ia) (obs-lam qb cb ogb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-app qa af aa ia) (obs-label {x = xb} {u = ub} qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-app qa af aa ia) (obs-funarg qb oab ab)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-app qa af aa ia) (obs-plus {m = mb} {n = nb} qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-lam qa ca oga) (obs-var {x = xb} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-lam qa ca oga) (obs-quote {a = ta} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-lam qa ca oga) (obs-cons qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-lam qa ca oga) (obs-car qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-lam qa ca oga) (obs-cdr qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-lam qa ca oga) (obs-atom-T qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-lam qa ca oga) (obs-atom-NIL qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-lam qa ca oga) (obs-eq-T {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-lam qa ca oga) (obs-eq-NIL {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-lam qa ca oga) (obs-if-T qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-lam qa ca oga) (obs-if-NIL qb b0 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-lam qa ca oga) (obs-app qb bf ba ib)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-lam qa ca oga) (obs-lam qb cb ogb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | refl = graph-comp ce oga ogb
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-lam qa ca oga) (obs-label {x = xb} {u = ub} qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-lam qa ca oga) (obs-funarg qb oab ab)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-lam qa ca oga) (obs-plus {m = mb} {n = nb} qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-label {x = xa} {u = ua} qa a0 a1) (obs-var {x = xb} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-label {x = xa} {u = ua} qa a0 a1) (obs-quote {a = ta} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-label {x = xa} {u = ua} qa a0 a1) (obs-cons qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-label {x = xa} {u = ua} qa a0 a1) (obs-car qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-label {x = xa} {u = ua} qa a0 a1) (obs-cdr qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-label {x = xa} {u = ua} qa a0 a1) (obs-atom-T qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-label {x = xa} {u = ua} qa a0 a1) (obs-atom-NIL qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-label {x = xa} {u = ua} qa a0 a1) (obs-eq-T {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-label {x = xa} {u = ua} qa a0 a1) (obs-eq-NIL {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-label {x = xa} {u = ua} qa a0 a1) (obs-if-T qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-label {x = xa} {u = ua} qa a0 a1) (obs-if-NIL qb b0 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-label {x = xa} {u = ua} qa a0 a1) (obs-app qb bf ba ib)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-label {x = xa} {u = ua} qa a0 a1) (obs-lam qb cb ogb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-label {x = xa} {u = ua} qa a0 a1) (obs-label {x = xb} {u = ub} qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | refl = obs-comp (CompEnv-ext {rho1} {rho2} {xa} {ua} {ub} ce (obs-comp ce a0 b0)) a1 b1
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-label {x = xa} {u = ua} qa a0 a1) (obs-funarg qb oab ab)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-label {x = xa} {u = ua} qa a0 a1) (obs-plus {m = mb} {n = nb} qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-funarg qa oaa aa) (obs-var {x = xb} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-funarg qa oaa aa) (obs-quote {a = ta} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-funarg qa oaa aa) (obs-cons qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-funarg qa oaa aa) (obs-car qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-funarg qa oaa aa) (obs-cdr qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-funarg qa oaa aa) (obs-atom-T qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-funarg qa oaa aa) (obs-atom-NIL qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-funarg qa oaa aa) (obs-eq-T {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-funarg qa oaa aa) (obs-eq-NIL {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-funarg qa oaa aa) (obs-if-T qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-funarg qa oaa aa) (obs-if-NIL qb b0 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-funarg qa oaa aa) (obs-app qb bf ba ib)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-funarg qa oaa aa) (obs-lam qb cb ogb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-funarg qa oaa aa) (obs-label {x = xb} {u = ub} qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-funarg qa oaa aa) (obs-funarg qb oab ab)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | refl = obs-comp (CompEnv-append (alist-comp ce oaa oab) ce) aa ab
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-funarg qa oaa aa) (obs-plus {m = mb} {n = nb} qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-plus {m = ma} {n = na} qa a1 a2) (obs-var {x = xb} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-plus {m = ma} {n = na} qa a1 a2) (obs-quote {a = ta} qb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-plus {m = ma} {n = na} qa a1 a2) (obs-cons qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-plus {m = ma} {n = na} qa a1 a2) (obs-car qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-plus {m = ma} {n = na} qa a1 a2) (obs-cdr qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-plus {m = ma} {n = na} qa a1 a2) (obs-atom-T qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-plus {m = ma} {n = na} qa a1 a2) (obs-atom-NIL qb b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-plus {m = ma} {n = na} qa a1 a2) (obs-eq-T {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-plus {m = ma} {n = na} qa a1 a2) (obs-eq-NIL {a1 = t1} {a2 = t2} qb b1 b2 hb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-plus {m = ma} {n = na} qa a1 a2) (obs-if-T qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-plus {m = ma} {n = na} qa a1 a2) (obs-if-NIL qb b0 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-plus {m = ma} {n = na} qa a1 a2) (obs-app qb bf ba ib)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-plus {m = ma} {n = na} qa a1 a2) (obs-lam qb cb ogb)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-plus {m = ma} {n = na} qa a1 a2) (obs-label {x = xb} {u = ub} qb b0 b1)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-plus {m = ma} {n = na} qa a1 a2) (obs-funarg qb oab ab)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | ()
  obs-comp {mu} {p} {rho1} {rho2} ce (obs-plus {m = ma} {n = na} qa a1 a2) (obs-plus {m = mb} {n = nb} qb b1 b2)
    with cell-eq {mu = mu} {p = p} qa qb
  ... | refl = add-comp {ma} {na} {mb} {nb} (obs-comp ce a1 b1) (obs-comp ce a2 b2)

  graph-comp : {mu : Heap} {p' : Addr} {x : Var} {rho1 rho2 : FinEnv}
    {g1 g2 : FinFun} -> CompEnv rho1 rho2 ->
    ObsGraph mu p' x rho1 g1 -> ObsGraph mu p' x rho2 g2 -> CompFun g1 g2
  graph-comp ce og-nil        og2 = tt
  graph-comp ce (og-cons o og) og2 =
    mkSigma (graph-step ce o og2) (graph-comp ce og og2)

  graph-step : {mu : Heap} {p' : Addr} {x : Var} {rho1 rho2 : FinEnv}
    {u v : FinEl} {g2 : FinFun} -> CompEnv rho1 rho2 ->
    Obs mu p' (ext rho1 x u) v -> ObsGraph mu p' x rho2 g2 ->
    CompStepFun (mkSigma u v) g2
  graph-step ce o og-nil = tt
  graph-step {mu} {p'} {x} {rho1} {rho2} {u} {v} ce o (og-cons {u = u2} o2 og2) =
    mkSigma (\ ck -> obs-comp (CompEnv-ext {rho1} {rho2} {x} {u} {u2} ce ck) o o2)
            (graph-step {mu} {p'} {x} {rho1} {rho2} {u} {v} ce o og2)

  alist-comp : {mu : Heap} {rho1 rho2 : FinEnv} {th : Alist} {b1 b2 : FinEnv} ->
    CompEnv rho1 rho2 ->
    ObsAlist mu rho1 th b1 -> ObsAlist mu rho2 th b2 -> CompBnd b1 b2
  alist-comp ce oa-nil          oa-nil            = cb-nil
  alist-comp ce (oa-cons o oas) (oa-cons o' oas') =
    cb-cons (obs-comp ce o o') (alist-comp ce oas oas')

CompEnv-refl : (rho : FinEnv) -> CohEnv rho -> CompEnv rho rho
CompEnv-refl rho ce x = Comp-refl (lookupEnv rho x) (lookupEnv-Coh rho x ce)
