{-# OPTIONS --without-K --exact-split #-}
------------------------------------------------------------------------
-- KeyJoinLemma.agda  (MIN/ -- Pi + U fragment)
--
-- The "key-join approximant" lemma (the suggested Lemma of the
-- RankCouple handoff):
--
--   if   y <= EvalFun l x    (l coherent, x coherent),
--   then there is  u  with   u <= x,   RANK u <= RANKFun l,
--   and  y <= EvalFun l u.
--
-- Mathematically  u  is the join of the firing keys of l at x; here it
-- is produced by `selectionBelow l x`, whose domain join `u` satisfies
-- `u <= x` and `EvalFun l x = v` with `v <= EvalFun l u` (selection is
-- below the identity cap).  The rank bound is by induction on the
-- Selection derivation: every selected key has rank <= RANKFun l and
-- Sup does not raise the rank.
--
-- NB: this settles the VALUE half of the singleton family obligation in
-- RankCouple's UCODE-PI-step.  It does NOT supply the typing `u : w1_0`
-- (the reduced-domain membership) -- that gap remains.
------------------------------------------------------------------------
module ID.Domain.KeyJoinLemma where

open import ID.Domain.Basic
  using ( Nat ; max ; Le ; Le-trans ; Le-max-l ; Le-max-r ; tt
        ; FinEl ; FinFun ; Bot ; UCode ; cons
        ; Pair ; Sigma ; mkSigma ; fst ; snd ; Eq ; Eq-transport )
open import ID.Domain.Order
  using ( RANK ; RANKFun ; RANK-Sup ; Le-max-lub ; Sup
        ; Coherent ; CoherentFunTail ; EvalFun ; LeCode ; LeFunCode
        ; LeCode-trans ; LeFunCode-refl ; Coherent-EvalFun )
open import ID.Model.Selection
  using ( Edge ; Selection ; sel-nil ; sel-skip ; sel-take
        ; selectionBelow ; Selection-le-EvalFun ; Coherent-Selection
        ; FinMemAllU-Selection )
open import ID.Domain.MemStage using ( finMemC )
open import ID.Domain.Membership using ( FinMemAllU )

------------------------------------------------------------------------
-- RANKFun g <= RANKFun (cons p g)  (the tail is below the cons).
------------------------------------------------------------------------
tail-le : (p : Edge) (g : FinFun) -> Le (RANKFun g) (RANKFun (cons p g))
tail-le p g =
  Le-trans (RANKFun g) (max (RANK (snd p)) (RANKFun g)) (RANKFun (cons p g))
    (Le-max-r (RANK (snd p)) (RANKFun g))
    (Le-max-r (RANK (fst p)) (max (RANK (snd p)) (RANKFun g)))

------------------------------------------------------------------------
-- A selection domain has rank <= RANKFun of the function.
------------------------------------------------------------------------
sel-rank : {l : FinFun} {u v : FinEl} -> Selection l u v -> Le (RANK u) (RANKFun l)
sel-rank sel-nil = tt
sel-rank (sel-skip {p} {g} {u} {v} sel) =
  Le-trans (RANK u) (RANKFun g) (RANKFun (cons p g))
    (sel-rank sel) (tail-le p g)
sel-rank (sel-take {p} {u} {v} {g} ck cv sel) =
  Le-trans (RANK (Sup (fst p) u)) (max (RANK (fst p)) (RANK u)) (RANKFun (cons p g))
    (RANK-Sup (fst p) u)
    (Le-max-lub (RANK (fst p)) (RANK u) (RANKFun (cons p g))
      (Le-max-l (RANK (fst p)) (max (RANK (snd p)) (RANKFun g)))
      (Le-trans (RANK u) (RANKFun g) (RANKFun (cons p g))
        (sel-rank sel) (tail-le p g)))

------------------------------------------------------------------------
-- The key-join approximant lemma.
------------------------------------------------------------------------
keyJoinLemma : (l : FinFun) (x y : FinEl) ->
  CoherentFunTail l -> Coherent x -> Coherent y ->
  LeCode y (EvalFun l x) ->
  Sigma FinEl (\ u ->
    Pair (LeCode u x)
    (Pair (Le (RANK u) (RANKFun l))
    (Pair (LeCode y (EvalFun l u)) (Coherent u))))
keyJoinLemma l x y cl cx cy ley =
  mkSigma u (mkSigma lux (mkSigma rku (mkSigma y-lu cu)))
  where
    sb  = selectionBelow l x cl cx
    u   = fst sb
    v   = fst (snd sb)
    sel : Selection l u v
    sel = fst (snd (snd sb))
    lux : LeCode u x
    lux = fst (snd (snd (snd sb)))
    ev=v : Eq (EvalFun l x) v
    ev=v = snd (snd (snd (snd sb)))
    cu : Coherent u
    cu = Coherent-Selection sel cl
    lvlu : LeCode v (EvalFun l u)
    lvlu = Selection-le-EvalFun {l} {u} {v} l sel (LeFunCode-refl l cl) cl cl cu
    cex : Coherent (EvalFun l x)
    cex = Coherent-EvalFun l x cl cx
    cv : Coherent v
    cv = Eq-transport Coherent ev=v cex
    celu : Coherent (EvalFun l u)
    celu = Coherent-EvalFun l u cl cu
    ley-v : LeCode y v
    ley-v = Eq-transport (\ w -> LeCode y w) ev=v ley
    y-lu : LeCode y (EvalFun l u)
    y-lu = LeCode-trans y v (EvalFun l u) cy cv celu ley-v lvlu
    rku : Le (RANK u) (RANKFun l)
    rku = sel-rank sel

------------------------------------------------------------------------
-- TYPED key-join: when l : x0 -> U (FinMemAllU l x0) and x0 : U, the
-- approximant u is itself a member of x0.
------------------------------------------------------------------------
typedKeyJoin : (l : FinFun) (x0 x y : FinEl) ->
  CoherentFunTail l -> Coherent x -> Coherent y ->
  Coherent x0 -> finMemC x0 UCode -> FinMemAllU l x0 ->
  LeCode y (EvalFun l x) ->
  Sigma FinEl (\ u ->
    Pair (LeCode u x)
    (Pair (Le (RANK u) (RANKFun l))
    (Pair (LeCode y (EvalFun l u)) (finMemC u x0))))
typedKeyJoin l x0 x y cl cx cy cx0 x0U allU ley =
  mkSigma u (mkSigma lux (mkSigma rku (mkSigma y-lu ux0)))
  where
    sb  = selectionBelow l x cl cx
    u   = fst sb
    v   = fst (snd sb)
    sel : Selection l u v
    sel = fst (snd (snd sb))
    lux : LeCode u x
    lux = fst (snd (snd (snd sb)))
    ev=v : Eq (EvalFun l x) v
    ev=v = snd (snd (snd (snd sb)))
    cu : Coherent u
    cu = Coherent-Selection sel cl
    lvlu : LeCode v (EvalFun l u)
    lvlu = Selection-le-EvalFun {l} {u} {v} l sel (LeFunCode-refl l cl) cl cl cu
    cex : Coherent (EvalFun l x)
    cex = Coherent-EvalFun l x cl cx
    cv : Coherent v
    cv = Eq-transport Coherent ev=v cex
    celu : Coherent (EvalFun l u)
    celu = Coherent-EvalFun l u cl cu
    ley-v : LeCode y v
    ley-v = Eq-transport (\ w -> LeCode y w) ev=v ley
    y-lu : LeCode y (EvalFun l u)
    y-lu = LeCode-trans y v (EvalFun l u) cy cv celu ley-v lvlu
    rku : Le (RANK u) (RANKFun l)
    rku = sel-rank sel
    ux0 : finMemC u x0
    ux0 = FinMemAllU-Selection x0 sel allU cl cx0 x0U
