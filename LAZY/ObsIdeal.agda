{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- LAZY/ObsIdeal.agda        (L4)
--
-- The observations at a cell form an IDEAL of coherent finite elements.
--
-- Two of the three facts are constructors of Obs (that is the point of
-- the ideal presentation), and are re-exported here under names that
-- read as lemmas:
--
--     obs-mono   downward closure
--     obs-join   directedness
--
-- What is proved here:
--
--     Obs-Coherent    every observation is a genuine finite element
--     obs-env-mono    monotone in the environment
--
-- and, on top of them, the derived forms L5 will actually use.
--
-- CONSISTENCY (any two observations at the same cell are Comp) is the
-- one ideal property that is NOT a constructor and NOT proved here; see
-- the note at the foot of this file.
------------------------------------------------------------------------

module LAZY.ObsIdeal where

open import LAZY.Domain.Basic
open import LAZY.Domain.Order
open import LAZY.Syntax.Heap
open import LAZY.Obs

------------------------------------------------------------------------
-- The ideal closure rules, named.
------------------------------------------------------------------------

obs-mono : {mu : Heap} {p : Addr} {rho : FinEnv} {u u' : FinEl} ->
  Obs mu p rho u -> Coherent u' -> LeCode u' u -> Obs mu p rho u'
obs-mono = obs-down

obs-join : {mu : Heap} {p : Addr} {rho : FinEnv} {u v : FinEl} ->
  Obs mu p rho u -> Obs mu p rho v -> Comp u v -> Obs mu p rho (Sup u v)
obs-join = obs-sup

------------------------------------------------------------------------
-- Coherent environments
------------------------------------------------------------------------

CohEnv : FinEnv -> Set
CohEnv nil         = Top
CohEnv (cons b bs) = Pair (Coherent (snd b)) (CohEnv bs)

private
  ifNatEq-Coh : (m n : Nat) (t e : FinEl) ->
    Coherent t -> Coherent e -> Coherent (ifNatEq m n t e)
  ifNatEq-Coh zero    zero    t e ct ce = ct
  ifNatEq-Coh zero    (suc n) t e ct ce = ce
  ifNatEq-Coh (suc m) zero    t e ct ce = ce
  ifNatEq-Coh (suc m) (suc n) t e ct ce = ifNatEq-Coh m n t e ct ce

lookupEnv-Coh : (rho : FinEnv) (x : Var) -> CohEnv rho -> Coherent (lookupEnv rho x)
lookupEnv-Coh nil         x ce = tt
lookupEnv-Coh (cons b bs) x ce =
  ifNatEq-Coh (fst b) x (snd b) (lookupEnv bs x)
    (fst ce) (lookupEnv-Coh bs x (snd ce))

CohEnv-ext : (rho : FinEnv) (x : Var) (u : FinEl) ->
  CohEnv rho -> Coherent u -> CohEnv (ext rho x u)
CohEnv-ext rho x u ce cu = mkSigma cu ce

CohEnv-append : (bs rho : FinEnv) ->
  CohEnv bs -> CohEnv rho -> CohEnv (appendEnv bs rho)
CohEnv-append nil         rho cb cr = cr
CohEnv-append (cons b bs) rho cb cr =
  mkSigma (fst cb) (CohEnv-append bs rho (snd cb) cr)

------------------------------------------------------------------------
-- Every observation is a coherent finite element.
------------------------------------------------------------------------

private
  InFun-val-Coh : (u v : FinEl) (g : FinFun) ->
    CoherentFun g -> InFun u v g -> Coherent v
  InFun-val-Coh u v (cons p ps) coh in-here      = CFcons.val-coh coh
  InFun-val-Coh u v (cons p ps) coh (in-there i) =
    InFun-val-Coh u v ps (CFcons.tail-coh coh) i

mutual
  Obs-Coherent : {mu : Heap} {p : Addr} {rho : FinEnv} {u : FinEl} ->
    CohEnv rho -> Obs mu p rho u -> Coherent u
  Obs-Coherent ce obs-bot                       = tt
  Obs-Coherent {rho = rho} ce (obs-var {x = x} e) = lookupEnv-Coh rho x ce
  Obs-Coherent ce (obs-quote e)                 = tt
  Obs-Coherent ce (obs-cons e o1 o2)            =
    mkSigma (Obs-Coherent ce o1) (Obs-Coherent ce o2)
  Obs-Coherent ce (obs-car e o)                 = fst (Obs-Coherent ce o)
  Obs-Coherent ce (obs-cdr e o)                 = snd (Obs-Coherent ce o)
  Obs-Coherent ce (obs-atom-T e o)              = tt
  Obs-Coherent ce (obs-atom-NIL e o)            = tt
  Obs-Coherent ce (obs-eq-T e o1 o2 q)          = tt
  Obs-Coherent ce (obs-eq-NIL e o1 o2 q)        = tt
  Obs-Coherent ce (obs-if-T e o0 o1)            = Obs-Coherent ce o1
  Obs-Coherent ce (obs-if-NIL e o0 o2)          = Obs-Coherent ce o2
  Obs-Coherent {u = v} ce (obs-app {g = g} {u = u} e of oa i) =
    InFun-val-Coh u v g (Obs-Coherent ce of) i
  Obs-Coherent ce (obs-lam e coh og)            = coh
  Obs-Coherent {rho = rho} ce (obs-label {x = x} {u = u} e o0 o1) =
    Obs-Coherent (CohEnv-ext rho x u ce (Obs-Coherent ce o0)) o1
  Obs-Coherent {rho = rho} ce (obs-funarg {bs = bs} e oa o) =
    Obs-Coherent (CohEnv-append bs rho (ObsAlist-Coherent ce oa) ce) o
  Obs-Coherent ce (obs-down o cu' le)           = cu'
  Obs-Coherent ce (obs-sup {u = u} {v = v} o1 o2 c) =
    Coherent-Sup u v c (Obs-Coherent ce o1) (Obs-Coherent ce o2)
  Obs-Coherent ce (obs-plus e o1 o2)            = tt

  ObsAlist-Coherent : {mu : Heap} {rho bs : FinEnv} {th : Alist} ->
    CohEnv rho -> ObsAlist mu rho th bs -> CohEnv bs
  ObsAlist-Coherent ce oa-nil          = tt
  ObsAlist-Coherent ce (oa-cons o oas) =
    mkSigma (Obs-Coherent ce o) (ObsAlist-Coherent ce oas)

------------------------------------------------------------------------
-- Monotonicity in the environment.
------------------------------------------------------------------------

LeEnv : FinEnv -> FinEnv -> Set
LeEnv rho rho' = (x : Var) -> LeCode (lookupEnv rho x) (lookupEnv rho' x)

LeEnv-refl : (rho : FinEnv) -> CohEnv rho -> LeEnv rho rho
LeEnv-refl rho ce x = LeCode-refl (lookupEnv rho x) (lookupEnv-Coh rho x ce)

private
  ifNatEq-Le : (m n : Nat) (t t' e e' : FinEl) ->
    LeCode t t' -> LeCode e e' -> LeCode (ifNatEq m n t e) (ifNatEq m n t' e')
  ifNatEq-Le zero    zero    t t' e e' lt le = lt
  ifNatEq-Le zero    (suc n) t t' e e' lt le = le
  ifNatEq-Le (suc m) zero    t t' e e' lt le = le
  ifNatEq-Le (suc m) (suc n) t t' e e' lt le = ifNatEq-Le m n t t' e e' lt le

LeEnv-ext : (rho rho' : FinEnv) (x : Var) (u : FinEl) ->
  LeEnv rho rho' -> Coherent u -> LeEnv (ext rho x u) (ext rho' x u)
LeEnv-ext rho rho' x u le cu y =
  ifNatEq-Le x y u u (lookupEnv rho y) (lookupEnv rho' y)
    (LeCode-refl u cu) (le y)

LeEnv-append : (bs rho rho' : FinEnv) ->
  CohEnv bs -> LeEnv rho rho' -> LeEnv (appendEnv bs rho) (appendEnv bs rho')
LeEnv-append nil         rho rho' cb le = le
LeEnv-append (cons b bs) rho rho' cb le y =
  ifNatEq-Le (fst b) y (snd b) (snd b)
    (lookupEnv (appendEnv bs rho) y) (lookupEnv (appendEnv bs rho') y)
    (LeCode-refl (snd b) (fst cb))
    (LeEnv-append bs rho rho' (snd cb) le y)

mutual
  obs-env-mono : {mu : Heap} {p : Addr} {rho rho' : FinEnv} {u : FinEl} ->
    CohEnv rho -> LeEnv rho rho' -> Obs mu p rho u -> Obs mu p rho' u
  obs-env-mono ce lr obs-bot            = obs-bot
  obs-env-mono {rho = rho} ce lr (obs-var {x = x} e) =
    obs-down (obs-var e) (lookupEnv-Coh rho x ce) (lr x)
  obs-env-mono ce lr (obs-quote e)      = obs-quote e
  obs-env-mono ce lr (obs-cons e o1 o2) =
    obs-cons e (obs-env-mono ce lr o1) (obs-env-mono ce lr o2)
  obs-env-mono ce lr (obs-car e o)      = obs-car e (obs-env-mono ce lr o)
  obs-env-mono ce lr (obs-cdr e o)      = obs-cdr e (obs-env-mono ce lr o)
  obs-env-mono ce lr (obs-atom-T e o)   = obs-atom-T e (obs-env-mono ce lr o)
  obs-env-mono ce lr (obs-atom-NIL e o) = obs-atom-NIL e (obs-env-mono ce lr o)
  obs-env-mono ce lr (obs-eq-T e o1 o2 q) =
    obs-eq-T e (obs-env-mono ce lr o1) (obs-env-mono ce lr o2) q
  obs-env-mono ce lr (obs-eq-NIL e o1 o2 q) =
    obs-eq-NIL e (obs-env-mono ce lr o1) (obs-env-mono ce lr o2) q
  obs-env-mono ce lr (obs-if-T e o0 o1) =
    obs-if-T e (obs-env-mono ce lr o0) (obs-env-mono ce lr o1)
  obs-env-mono ce lr (obs-if-NIL e o0 o2) =
    obs-if-NIL e (obs-env-mono ce lr o0) (obs-env-mono ce lr o2)
  obs-env-mono ce lr (obs-app e of oa i) =
    obs-app e (obs-env-mono ce lr of) (obs-env-mono ce lr oa) i
  obs-env-mono {rho = rho} {rho' = rho'} ce lr (obs-lam {x = x} {g = g} e coh og) =
    obs-lam e coh (obsgraph-env-mono {rho = rho} {rho' = rho'} g x ce lr coh og)
  obs-env-mono {rho = rho} {rho' = rho'} ce lr (obs-label {x = x} {u = u} e o0 o1) =
    obs-label e (obs-env-mono ce lr o0)
      (obs-env-mono (CohEnv-ext rho x u ce (Obs-Coherent ce o0))
                    (LeEnv-ext rho rho' x u lr (Obs-Coherent ce o0)) o1)
  obs-env-mono {rho = rho} {rho' = rho'} ce lr (obs-funarg {bs = bs} e oa o) =
    obs-funarg e (obsalist-env-mono ce lr oa)
      (obs-env-mono
        (CohEnv-append bs rho (ObsAlist-Coherent ce oa) ce)
        (LeEnv-append bs rho rho' (ObsAlist-Coherent ce oa) lr) o)
  obs-env-mono ce lr (obs-down o cu' le) = obs-down (obs-env-mono ce lr o) cu' le
  obs-env-mono ce lr (obs-sup o1 o2 c)   =
    obs-sup (obs-env-mono ce lr o1) (obs-env-mono ce lr o2) c
  obs-env-mono ce lr (obs-plus e o1 o2)  =
    obs-plus e (obs-env-mono ce lr o1) (obs-env-mono ce lr o2)

  -- the alist observations are made in the OUTER environment, and the
  -- bindings they produce do not change: they are re-derived in the
  -- larger environment at exactly the same values.
  obsalist-env-mono : {mu : Heap} {rho rho' bs : FinEnv} {th : Alist} ->
    CohEnv rho -> LeEnv rho rho' -> ObsAlist mu rho th bs -> ObsAlist mu rho' th bs
  obsalist-env-mono ce lr oa-nil          = oa-nil
  obsalist-env-mono ce lr (oa-cons o oas) =
    oa-cons (obs-env-mono ce lr o) (obsalist-env-mono ce lr oas)

  obsgraph-env-mono : {mu : Heap} {p' : Addr} {rho rho' : FinEnv}
    (g : FinFun) (x : Var) ->
    CohEnv rho -> LeEnv rho rho' -> CoherentFun g ->
    ObsGraph mu p' x rho g -> ObsGraph mu p' x rho' g
  obsgraph-env-mono nil         x ce lr coh og-nil = og-nil
  obsgraph-env-mono {rho = rho} {rho' = rho'} (cons q qs) x ce lr coh (og-cons o og) =
    og-cons
      (obs-env-mono (CohEnv-ext rho x (fst q) ce (CFcons.key-coh coh))
                    (LeEnv-ext rho rho' x (fst q) lr (CFcons.key-coh coh)) o)
      (obsgraph-env-mono {rho = rho} {rho' = rho'} qs x ce lr (CFcons.tail-coh coh) og)

------------------------------------------------------------------------
-- What is NOT here: CONSISTENCY
--
--     Obs mu p rho u -> Obs mu p rho v -> Comp u v
--
-- the third ideal property.  It is not needed for the invariance
-- theorem (L5); it is needed to read off the ANSWER (L6), where it is
-- what makes "the shape of the value" well defined -- no cell can be
-- observed both as an atom and as a pair.  It is the one place where
-- the rules of LAZY.Obs could still turn out to be too generous.
------------------------------------------------------------------------
