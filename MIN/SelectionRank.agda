{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- SelectionRank.agda  (MIN/)
--
-- The realizers reachable by a Selection of f have RANK bounded by
-- RANKFun f.  Since `Selection f u v` builds u as Bot Sup'd with a
-- sub-multiset of f's keys, RANK u <= RANKFun f (and likewise RANK v).
--
-- Consequence: the edge quantifier `forall u v, Selection f u v -> ...`
-- in the validity records never ranges over realizers of rank exceeding
-- RANKFun f < RANK (PiCode b f).  So the relation is stable above the
-- code's rank, and no separate `RANK u < lev` hypothesis is needed.
------------------------------------------------------------------------

module MIN.SelectionRank where

open import MIN.Basic
  using (FinEl ; Bot ; FinFun ; nil ; cons ; fst ; snd ; tt ; max ;
         Le ; Le-trans ; Le-max-l ; Le-max-r)
open import MIN.PaperSemantics using (Sup)
open import MIN.Selection using (Selection ; sel-nil ; sel-skip ; sel-take ; Edge)
open import MIN.Rank using (RANK ; RANKFun ; RANK-Sup ; Le-max-lub)

-- RANKFun g <= RANKFun (cons p g)
RANKFun-tail-le : (p : Edge) (g : FinFun) -> Le (RANKFun g) (RANKFun (cons p g))
RANKFun-tail-le p g =
  Le-trans (RANKFun g) (max (RANK (snd p)) (RANKFun g)) (RANKFun (cons p g))
    (Le-max-r (RANK (snd p)) (RANKFun g))
    (Le-max-r (RANK (fst p)) (max (RANK (snd p)) (RANKFun g)))

Selection-RANK-u : {f : FinFun} {u v : FinEl} ->
  Selection f u v -> Le (RANK u) (RANKFun f)
Selection-RANK-u sel-nil = tt
Selection-RANK-u (sel-skip {p} {g} {u} {v} sel) =
  Le-trans (RANK u) (RANKFun g) (RANKFun (cons p g))
    (Selection-RANK-u sel) (RANKFun-tail-le p g)
Selection-RANK-u (sel-take {p} {u} {v} {g} ck cv sel) =
  Le-trans (RANK (Sup (fst p) u))
           (max (RANK (fst p)) (RANK u))
           (RANKFun (cons p g))
    (RANK-Sup (fst p) u)
    (Le-max-lub (RANK (fst p)) (RANK u) (RANKFun (cons p g))
      (Le-max-l (RANK (fst p)) (max (RANK (snd p)) (RANKFun g)))
      (Le-trans (RANK u) (RANKFun g) (RANKFun (cons p g))
        (Selection-RANK-u sel) (RANKFun-tail-le p g)))

-- RANK (snd p) <= RANKFun (cons p g)
RANK-snd-le : (p : Edge) (g : FinFun) -> Le (RANK (snd p)) (RANKFun (cons p g))
RANK-snd-le p g =
  Le-trans (RANK (snd p)) (max (RANK (snd p)) (RANKFun g)) (RANKFun (cons p g))
    (Le-max-l (RANK (snd p)) (RANKFun g))
    (Le-max-r (RANK (fst p)) (max (RANK (snd p)) (RANKFun g)))

Selection-RANK-v : {f : FinFun} {u v : FinEl} ->
  Selection f u v -> Le (RANK v) (RANKFun f)
Selection-RANK-v sel-nil = tt
Selection-RANK-v (sel-skip {p} {g} {u} {v} sel) =
  Le-trans (RANK v) (RANKFun g) (RANKFun (cons p g))
    (Selection-RANK-v sel) (RANKFun-tail-le p g)
Selection-RANK-v (sel-take {p} {u} {v} {g} ck cv sel) =
  Le-trans (RANK (Sup (snd p) v))
           (max (RANK (snd p)) (RANK v))
           (RANKFun (cons p g))
    (RANK-Sup (snd p) v)
    (Le-max-lub (RANK (snd p)) (RANK v) (RANKFun (cons p g))
      (RANK-snd-le p g)
      (Le-trans (RANK v) (RANKFun g) (RANKFun (cons p g))
        (Selection-RANK-v sel) (RANKFun-tail-le p g)))
