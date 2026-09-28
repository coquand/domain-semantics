{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Model.Guard
--
-- The interpretation of a guarded construct [ψ]A / ⟨ψ⟩t: its finite
-- elements are ⊥, and the elements of A when ψ holds in the ambient
-- level theory.  `Guard V P` is this predicate, for V the validity of
-- ψ and P the finite elements of A; generic closure properties.
--
-- `NBody b X` is the shape of the application clauses: ⊤ at ⊥, X at
-- every other code (with generic helpers).
------------------------------------------------------------------------

module BCDE4.Model.Guard where

import BCDE4.Dom.Basic as S
open S using (Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ; Eq ; refl ; Nat ;
              Eq-transport ; Eq-sym ; FinEl ; Bot ; UCode ; LevTy ; LevEl ; FunEl ; PiCode ; LPiCode)
open import BCDE4.Basic using (Either ; inl ; inr)
open import BCDE4.Dom.Kernel using (LeCode ; Coherent ; Comp ; Sup ; NotBot ;
  comp-Bot-l ; comp-Bot-r ; Sup-Bot-r)

------------------------------------------------------------------------
-- Elementary facts about ⊥
------------------------------------------------------------------------

leBot-eq : (v : FinEl) -> LeCode v Bot -> Eq v Bot
leBot-eq Bot          le = refl
leBot-eq (UCode _)    ()
leBot-eq LevTy        ()
leBot-eq (LevEl _)    ()
leBot-eq (FunEl _)    ()
leBot-eq (PiCode _ _) ()
leBot-eq (LPiCode _)  ()

nb-dec : (b : FinEl) -> Either (Eq b Bot) (NotBot b)
nb-dec Bot          = inl refl
nb-dec (UCode _)    = inr tt
nb-dec LevTy        = inr tt
nb-dec (LevEl _)    = inr tt
nb-dec (FunEl _)    = inr tt
nb-dec (PiCode _ _) = inr tt
nb-dec (LPiCode _)  = inr tt

-- eliminate on ⊥ / non-⊥
nb-elim : (P : FinEl -> Set) -> P Bot -> ((b : FinEl) -> NotBot b -> P b) -> (b : FinEl) -> P b
nb-elim P pb pn Bot          = pb
nb-elim P pb pn (UCode l)    = pn (UCode l) tt
nb-elim P pb pn LevTy        = pn LevTy tt
nb-elim P pb pn (LevEl k)    = pn (LevEl k) tt
nb-elim P pb pn (FunEl g)    = pn (FunEl g) tt
nb-elim P pb pn (PiCode a f) = pn (PiCode a f) tt
nb-elim P pb pn (LPiCode f)  = pn (LPiCode f) tt

------------------------------------------------------------------------
-- NBody
------------------------------------------------------------------------

NBody : FinEl -> Set -> Set
NBody Bot          X = Top
NBody (UCode _)    X = X
NBody LevTy        X = X
NBody (LevEl _)    X = X
NBody (FunEl _)    X = X
NBody (PiCode _ _) X = X
NBody (LPiCode _)  X = X

nbody-in : {X : Set} (b : FinEl) -> NotBot b -> X -> NBody b X
nbody-in Bot          () x
nbody-in (UCode _)    nb x = x
nbody-in LevTy        nb x = x
nbody-in (LevEl _)    nb x = x
nbody-in (FunEl _)    nb x = x
nbody-in (PiCode _ _) nb x = x
nbody-in (LPiCode _)  nb x = x

nbody-inN : {X : Set} (b : FinEl) -> (NotBot b -> X) -> NBody b X
nbody-inN Bot          x = tt
nbody-inN (UCode _)    x = x tt
nbody-inN LevTy        x = x tt
nbody-inN (LevEl _)    x = x tt
nbody-inN (FunEl _)    x = x tt
nbody-inN (PiCode _ _) x = x tt
nbody-inN (LPiCode _)  x = x tt

nbody-out : {X : Set} (b : FinEl) -> NotBot b -> NBody b X -> X
nbody-out Bot          () x
nbody-out (UCode _)    nb x = x
nbody-out LevTy        nb x = x
nbody-out (LevEl _)    nb x = x
nbody-out (FunEl _)    nb x = x
nbody-out (PiCode _ _) nb x = x
nbody-out (LPiCode _)  nb x = x

nbody-map : {X Y : Set} (b : FinEl) -> (X -> Y) -> NBody b X -> NBody b Y
nbody-map Bot          h x = tt
nbody-map (UCode _)    h x = h x
nbody-map LevTy        h x = h x
nbody-map (LevEl _)    h x = h x
nbody-map (FunEl _)    h x = h x
nbody-map (PiCode _ _) h x = h x
nbody-map (LPiCode _)  h x = h x

-- dependent version: the body may use NotBot b
nbody-mapN : {X Y : Set} (b : FinEl) -> (NotBot b -> X -> Y) -> NBody b X -> NBody b Y
nbody-mapN Bot          h x = tt
nbody-mapN (UCode _)    h x = h tt x
nbody-mapN LevTy        h x = h tt x
nbody-mapN (LevEl _)    h x = h tt x
nbody-mapN (FunEl _)    h x = h tt x
nbody-mapN (PiCode _ _) h x = h tt x
nbody-mapN (LPiCode _)  h x = h tt x

nbody-out' : {X : Set} (b : FinEl) -> NBody b X -> Either (Eq b Bot) (Pair (NotBot b) X)
nbody-out' Bot          x = inl refl
nbody-out' (UCode _)    x = inr (mkSigma tt x)
nbody-out' LevTy        x = inr (mkSigma tt x)
nbody-out' (LevEl _)    x = inr (mkSigma tt x)
nbody-out' (FunEl _)    x = inr (mkSigma tt x)
nbody-out' (PiCode _ _) x = inr (mkSigma tt x)
nbody-out' (LPiCode _)  x = inr (mkSigma tt x)

------------------------------------------------------------------------
-- Guard
------------------------------------------------------------------------

Guard : Set -> (FinEl -> Set) -> FinEl -> Set
Guard V P Bot          = Top
Guard V P (UCode l)    = Pair V (P (UCode l))
Guard V P LevTy        = Pair V (P LevTy)
Guard V P (LevEl k)    = Pair V (P (LevEl k))
Guard V P (FunEl g)    = Pair V (P (FunEl g))
Guard V P (PiCode a f) = Pair V (P (PiCode a f))
Guard V P (LPiCode f)  = Pair V (P (LPiCode f))

guard-in : {V : Set} {P : FinEl -> Set} (b : FinEl) -> V -> P b -> Guard V P b
guard-in Bot          v p = tt
guard-in (UCode l)    v p = mkSigma v p
guard-in LevTy        v p = mkSigma v p
guard-in (LevEl k)    v p = mkSigma v p
guard-in (FunEl g)    v p = mkSigma v p
guard-in (PiCode a f) v p = mkSigma v p
guard-in (LPiCode f)  v p = mkSigma v p

guard-out : {V : Set} {P : FinEl -> Set} (b : FinEl) -> Guard V P b ->
  Either (Eq b Bot) (Pair V (P b))
guard-out Bot          g = inl refl
guard-out (UCode l)    g = inr g
guard-out LevTy        g = inr g
guard-out (LevEl k)    g = inr g
guard-out (FunEl f)    g = inr g
guard-out (PiCode a f) g = inr g
guard-out (LPiCode f)  g = inr g

guard-map : {V V' : Set} {P Q : FinEl -> Set} -> (V -> V') -> ((b : FinEl) -> P b -> Q b) ->
  (b : FinEl) -> Guard V P b -> Guard V' Q b
guard-map fv fp Bot          g = tt
guard-map fv fp (UCode l)    g = mkSigma (fv (fst g)) (fp _ (snd g))
guard-map fv fp LevTy        g = mkSigma (fv (fst g)) (fp _ (snd g))
guard-map fv fp (LevEl k)    g = mkSigma (fv (fst g)) (fp _ (snd g))
guard-map fv fp (FunEl f)    g = mkSigma (fv (fst g)) (fp _ (snd g))
guard-map fv fp (PiCode a f) g = mkSigma (fv (fst g)) (fp _ (snd g))
guard-map fv fp (LPiCode f)  g = mkSigma (fv (fst g)) (fp _ (snd g))

guard-mapV : {V V' : Set} {P Q : FinEl -> Set} -> (V -> V') -> ((b : FinEl) -> V -> P b -> Q b) ->
  (b : FinEl) -> Guard V P b -> Guard V' Q b
guard-mapV fv fp Bot          g = tt
guard-mapV fv fp (UCode l)    g = mkSigma (fv (fst g)) (fp _ (fst g) (snd g))
guard-mapV fv fp LevTy        g = mkSigma (fv (fst g)) (fp _ (fst g) (snd g))
guard-mapV fv fp (LevEl k)    g = mkSigma (fv (fst g)) (fp _ (fst g) (snd g))
guard-mapV fv fp (FunEl f)    g = mkSigma (fv (fst g)) (fp _ (fst g) (snd g))
guard-mapV fv fp (PiCode a f) g = mkSigma (fv (fst g)) (fp _ (fst g) (snd g))
guard-mapV fv fp (LPiCode f)  g = mkSigma (fv (fst g)) (fp _ (fst g) (snd g))

guard-coh : {V : Set} {P : FinEl -> Set} -> ((b : FinEl) -> P b -> Coherent b) ->
  (b : FinEl) -> Guard V P b -> Coherent b
guard-coh {V} {P} h b g = cases b (guard-out b g)
  where
    cases : (b : FinEl) -> Either (Eq b Bot) (Pair V (P b)) -> Coherent b
    cases .Bot (inl refl) = tt
    cases b (inr vp) = h b (snd vp)

private
  comp-cases : {V : Set} {P : FinEl -> Set} -> ((u v : FinEl) -> P u -> P v -> Comp u v) ->
    (u v : FinEl) -> Either (Eq u Bot) (Pair V (P u)) -> Either (Eq v Bot) (Pair V (P v)) -> Comp u v
  comp-cases h .Bot v (inl refl) ov = comp-Bot-l v
  comp-cases h u .Bot (inr pu) (inl refl) = comp-Bot-r u
  comp-cases h u v (inr pu) (inr pv) = h u v (snd pu) (snd pv)

guard-Comp : {V : Set} {P : FinEl -> Set} -> ((u v : FinEl) -> P u -> P v -> Comp u v) ->
  (u v : FinEl) -> Guard V P u -> Guard V P v -> Comp u v
guard-Comp h u v gu gv = comp-cases h u v (guard-out u gu) (guard-out v gv)

-- downward closure
guard-down : {V : Set} {P : FinEl -> Set} ->
  ((u u' : FinEl) -> Coherent u' -> P u -> LeCode u' u -> P u') ->
  (u u' : FinEl) -> Coherent u' -> Guard V P u -> LeCode u' u -> Guard V P u'
guard-down {V} {P} h u u' cu' g le = cases u (guard-out u g) le
  where
    cases : (u : FinEl) -> Either (Eq u Bot) (Pair V (P u)) -> LeCode u' u -> Guard V P u'
    cases .Bot (inl refl) le = Eq-transport (Guard V P) (Eq-sym (leBot-eq u' le)) tt
    cases u (inr vp) le = guard-in u' (fst vp) (h u u' cu' (snd vp) le)

-- closure under compatible joins
private
  sup-cases : {V : Set} {P : FinEl -> Set} -> {u0 v0 : FinEl} -> (P u0 -> P v0 -> P (Sup u0 v0)) ->
    (u v : FinEl) -> Eq u u0 -> Eq v v0 -> Guard V P u -> Guard V P v ->
    Either (Eq u Bot) (Pair V (P u)) -> Either (Eq v Bot) (Pair V (P v)) -> Guard V P (Sup u v)
  sup-cases h .Bot v eu ev gu gv (inl refl) ov = gv
  sup-cases {V} {P} h u .Bot eu ev gu gv (inr pu) (inl refl) =
    Eq-transport (Guard V P) (Eq-sym (Sup-Bot-r u)) gu
  sup-cases h u v refl refl gu gv (inr pu) (inr pv) = guard-in (Sup u v) (fst pu) (h (snd pu) (snd pv))

guard-Sup : {V : Set} {P : FinEl -> Set} (u v : FinEl) -> (P u -> P v -> P (Sup u v)) ->
  Guard V P u -> Guard V P v -> Guard V P (Sup u v)
guard-Sup u v h gu gv = sup-cases h u v refl refl gu gv (guard-out u gu) (guard-out v gv)

------------------------------------------------------------------------
-- Generic closure properties of NBody
------------------------------------------------------------------------

nbody-coh : {X : FinEl -> Set} -> ((b : FinEl) -> NotBot b -> X b -> Coherent b) ->
  (b : FinEl) -> NBody b (X b) -> Coherent b
nbody-coh {X} h = nb-elim (\ b -> NBody b (X b) -> Coherent b) (\ _ -> tt)
  (\ b nb e -> h b nb (nbody-out b nb e))

nbody-Comp : {X : FinEl -> Set} ->
  ((u v : FinEl) -> NotBot u -> NotBot v -> X u -> X v -> Comp u v) ->
  (u v : FinEl) -> NBody u (X u) -> NBody v (X v) -> Comp u v
nbody-Comp {X} h u v eu ev = cases u v (nbody-out' u eu) (nbody-out' v ev)
  where
    cases : (u v : FinEl) -> Either (Eq u Bot) (Pair (NotBot u) (X u)) ->
      Either (Eq v Bot) (Pair (NotBot v) (X v)) -> Comp u v
    cases .Bot v (inl refl) o = comp-Bot-l v
    cases u .Bot (inr p) (inl refl) = comp-Bot-r u
    cases u v (inr p) (inr q) = h u v (fst p) (fst q) (snd p) (snd q)

nbody-down : {X : FinEl -> Set} (u u' : FinEl) ->
  (NotBot u -> NotBot u' -> X u -> X u') ->
  NBody u (X u) -> LeCode u' u -> NBody u' (X u')
nbody-down {X} u u' h eu le = cases (nbody-out' u eu)
  where
    cases : Either (Eq u Bot) (Pair (NotBot u) (X u)) -> NBody u' (X u')
    cases (inl e) =
      Eq-transport (\ z -> NBody z (X z)) (Eq-sym (leBot-eq u' (Eq-transport (LeCode u') e le))) tt
    cases (inr p) = nbody-inN u' (\ nw -> h (fst p) nw (snd p))

nbody-Sup : {X : FinEl -> Set} ->
  ((u v : FinEl) -> NotBot u -> NotBot v -> Comp u v -> X u -> X v -> X (Sup u v)) ->
  (nbs : (u v : FinEl) -> NotBot u -> Comp u v -> NotBot (Sup u v)) ->
  (u v : FinEl) -> Comp u v -> NBody u (X u) -> NBody v (X v) -> NBody (Sup u v) (X (Sup u v))
nbody-Sup {X} h nbs u v comp eu ev = cases u v comp eu ev (nbody-out' u eu) (nbody-out' v ev)
  where
    cases : (u v : FinEl) -> Comp u v -> NBody u (X u) -> NBody v (X v) ->
      Either (Eq u Bot) (Pair (NotBot u) (X u)) ->
      Either (Eq v Bot) (Pair (NotBot v) (X v)) -> NBody (Sup u v) (X (Sup u v))
    cases .Bot v comp eu ev (inl refl) o = ev
    cases u .Bot comp eu ev (inr p) (inl refl) =
      Eq-transport (\ z -> NBody z (X z)) (Eq-sym (Sup-Bot-r u)) eu
    cases u v comp eu ev (inr p) (inr q) =
      nbody-in (Sup u v) (nbs u v (fst p) comp) (h u v (fst p) (fst q) comp (snd p) (snd q))
