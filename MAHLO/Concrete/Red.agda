{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Concrete/Red.agda
--
-- One-step beta/pi/iota reduction (in any position) and its reflexive
-- transitive closure, with congruence lemmas and stability under
-- renaming and substitution.
------------------------------------------------------------------------

module MAHLO.Concrete.Red where

open import MAHLO.Basic
open import MAHLO.Syntax using (Num ; zero ; suc)
open import MAHLO.Concrete.Tm

data Step : Tm -> Tm -> Set where
  s-beta  : {b a : Tm} -> Step (tapp (tlam b) a) (inst b a)
  s-fstp  : {a b : Tm} -> Step (tfst (tpair a b)) a
  s-sndp  : {a b : Tm} -> Step (tsnd (tpair a b)) b
  s-rec0  : {C z s : Tm} -> Step (trec C z s tze) z
  s-recS  : {C z s n : Tm} -> Step (trec C z s (tsc n)) (tapp (tapp s n) (trec C z s n))
  s-lam   : {b b' : Tm} -> Step b b' -> Step (tlam b) (tlam b')
  s-app1  : {t t' u : Tm} -> Step t t' -> Step (tapp t u) (tapp t' u)
  s-app2  : {t u u' : Tm} -> Step u u' -> Step (tapp t u) (tapp t u')
  s-pi1   : {A A' F : Tm} -> Step A A' -> Step (tpi A F) (tpi A' F)
  s-pi2   : {A F F' : Tm} -> Step F F' -> Step (tpi A F) (tpi A F')
  s-sig1  : {A A' F : Tm} -> Step A A' -> Step (tsig A F) (tsig A' F)
  s-sig2  : {A F F' : Tm} -> Step F F' -> Step (tsig A F) (tsig A F')
  s-pair1 : {t t' u : Tm} -> Step t t' -> Step (tpair t u) (tpair t' u)
  s-pair2 : {t u u' : Tm} -> Step u u' -> Step (tpair t u) (tpair t u')
  s-fst   : {t t' : Tm} -> Step t t' -> Step (tfst t) (tfst t')
  s-snd   : {t t' : Tm} -> Step t t' -> Step (tsnd t) (tsnd t')
  s-sc    : {t t' : Tm} -> Step t t' -> Step (tsc t) (tsc t')
  s-rec1  : {C C' z s n : Tm} -> Step C C' -> Step (trec C z s n) (trec C' z s n)
  s-rec2  : {C z z' s n : Tm} -> Step z z' -> Step (trec C z s n) (trec C z' s n)
  s-rec3  : {C z s s' n : Tm} -> Step s s' -> Step (trec C z s n) (trec C z s' n)
  s-rec4  : {C z s n n' : Tm} -> Step n n' -> Step (trec C z s n) (trec C z s n')
  s-U1    : {f f' g : Tm} -> Step f f' -> Step (tU f g) (tU f' g)
  s-U2    : {f g g' : Tm} -> Step g g' -> Step (tU f g) (tU f g')

data Red : Tm -> Tm -> Set where
  r-refl : {a : Tm} -> Red a a
  r-step : {a b c : Tm} -> Step a b -> Red b c -> Red a c

Red-trans : {a b c : Tm} -> Red a b -> Red b c -> Red a c
Red-trans r-refl q = q
Red-trans (r-step s p) q = r-step s (Red-trans p q)

Red-one : {a b : Tm} -> Step a b -> Red a b
Red-one s = r-step s r-refl

-- lifting a step-preserving map to reduction sequences
Red-map : (f : Tm -> Tm) -> ({a b : Tm} -> Step a b -> Step (f a) (f b)) ->
          {a b : Tm} -> Red a b -> Red (f a) (f b)
Red-map f h r-refl = r-refl
Red-map f h (r-step s p) = r-step (h s) (Red-map f h p)

-- congruences
R-lam : {b b' : Tm} -> Red b b' -> Red (tlam b) (tlam b')
R-lam = Red-map tlam s-lam

R-app : {t t' u u' : Tm} -> Red t t' -> Red u u' -> Red (tapp t u) (tapp t' u')
R-app {t' = t'} {u = u} p q = Red-trans (Red-map (\ x -> tapp x u) s-app1 p) (Red-map (tapp t') s-app2 q)

R-pi : {A A' F F' : Tm} -> Red A A' -> Red F F' -> Red (tpi A F) (tpi A' F')
R-pi {A' = A'} {F = F} p q = Red-trans (Red-map (\ x -> tpi x F) s-pi1 p) (Red-map (tpi A') s-pi2 q)

R-sig : {A A' F F' : Tm} -> Red A A' -> Red F F' -> Red (tsig A F) (tsig A' F')
R-sig {A' = A'} {F = F} p q = Red-trans (Red-map (\ x -> tsig x F) s-sig1 p) (Red-map (tsig A') s-sig2 q)

R-pair : {t t' u u' : Tm} -> Red t t' -> Red u u' -> Red (tpair t u) (tpair t' u')
R-pair {t' = t'} {u = u} p q =
  Red-trans (Red-map (\ x -> tpair x u) s-pair1 p) (Red-map (tpair t') s-pair2 q)

R-fst : {t t' : Tm} -> Red t t' -> Red (tfst t) (tfst t')
R-fst = Red-map tfst s-fst

R-snd : {t t' : Tm} -> Red t t' -> Red (tsnd t) (tsnd t')
R-snd = Red-map tsnd s-snd

R-sc : {t t' : Tm} -> Red t t' -> Red (tsc t) (tsc t')
R-sc = Red-map tsc s-sc

R-rec : {C C' z z' s s' n n' : Tm} -> Red C C' -> Red z z' -> Red s s' -> Red n n' ->
        Red (trec C z s n) (trec C' z' s' n')
R-rec {C} {C'} {z} {z'} {s} {s'} {n} {n'} p1 p2 p3 p4 =
  Red-trans (Red-map (\ x -> trec x z s n) s-rec1 p1)
    (Red-trans (Red-map (\ x -> trec C' x s n) s-rec2 p2)
      (Red-trans (Red-map (\ x -> trec C' z' x n) s-rec3 p3)
                 (Red-map (\ x -> trec C' z' s' x) s-rec4 p4)))

R-U : {f f' g g' : Tm} -> Red f f' -> Red g g' -> Red (tU f g) (tU f' g')
R-U {f' = f'} {g = g} p q = Red-trans (Red-map (\ x -> tU x g) s-U1 p) (Red-map (tU f') s-U2 q)

------------------------------------------------------------------------
-- Stability under renaming and substitution
------------------------------------------------------------------------

Step-ren : (r : Rn) {a b : Tm} -> Step a b -> Step (ren r a) (ren r b)
Step-ren r (s-beta {b} {a}) = transport (Step (tapp (tlam (ren (liftR r) b)) (ren r a)))
                                        (Eq-sym (ren-inst r b a)) s-beta
Step-ren r s-fstp = s-fstp
Step-ren r s-sndp = s-sndp
Step-ren r s-rec0 = s-rec0
Step-ren r s-recS = s-recS
Step-ren r (s-lam p) = s-lam (Step-ren (liftR r) p)
Step-ren r (s-app1 p) = s-app1 (Step-ren r p)
Step-ren r (s-app2 p) = s-app2 (Step-ren r p)
Step-ren r (s-pi1 p) = s-pi1 (Step-ren r p)
Step-ren r (s-pi2 p) = s-pi2 (Step-ren r p)
Step-ren r (s-sig1 p) = s-sig1 (Step-ren r p)
Step-ren r (s-sig2 p) = s-sig2 (Step-ren r p)
Step-ren r (s-pair1 p) = s-pair1 (Step-ren r p)
Step-ren r (s-pair2 p) = s-pair2 (Step-ren r p)
Step-ren r (s-fst p) = s-fst (Step-ren r p)
Step-ren r (s-snd p) = s-snd (Step-ren r p)
Step-ren r (s-sc p) = s-sc (Step-ren r p)
Step-ren r (s-rec1 p) = s-rec1 (Step-ren r p)
Step-ren r (s-rec2 p) = s-rec2 (Step-ren r p)
Step-ren r (s-rec3 p) = s-rec3 (Step-ren r p)
Step-ren r (s-rec4 p) = s-rec4 (Step-ren r p)
Step-ren r (s-U1 p) = s-U1 (Step-ren r p)
Step-ren r (s-U2 p) = s-U2 (Step-ren r p)

Red-ren : (r : Rn) {a b : Tm} -> Red a b -> Red (ren r a) (ren r b)
Red-ren r = Red-map (ren r) (Step-ren r)

Step-sub : (s : Sb) {a b : Tm} -> Step a b -> Step (sub s a) (sub s b)
Step-sub s (s-beta {b} {a}) = transport (Step (tapp (tlam (sub (liftS s) b)) (sub s a)))
                                        (Eq-sym (sub-inst s b a)) s-beta
Step-sub s s-fstp = s-fstp
Step-sub s s-sndp = s-sndp
Step-sub s s-rec0 = s-rec0
Step-sub s s-recS = s-recS
Step-sub s (s-lam p) = s-lam (Step-sub (liftS s) p)
Step-sub s (s-app1 p) = s-app1 (Step-sub s p)
Step-sub s (s-app2 p) = s-app2 (Step-sub s p)
Step-sub s (s-pi1 p) = s-pi1 (Step-sub s p)
Step-sub s (s-pi2 p) = s-pi2 (Step-sub s p)
Step-sub s (s-sig1 p) = s-sig1 (Step-sub s p)
Step-sub s (s-sig2 p) = s-sig2 (Step-sub s p)
Step-sub s (s-pair1 p) = s-pair1 (Step-sub s p)
Step-sub s (s-pair2 p) = s-pair2 (Step-sub s p)
Step-sub s (s-fst p) = s-fst (Step-sub s p)
Step-sub s (s-snd p) = s-snd (Step-sub s p)
Step-sub s (s-sc p) = s-sc (Step-sub s p)
Step-sub s (s-rec1 p) = s-rec1 (Step-sub s p)
Step-sub s (s-rec2 p) = s-rec2 (Step-sub s p)
Step-sub s (s-rec3 p) = s-rec3 (Step-sub s p)
Step-sub s (s-rec4 p) = s-rec4 (Step-sub s p)
Step-sub s (s-U1 p) = s-U1 (Step-sub s p)
Step-sub s (s-U2 p) = s-U2 (Step-sub s p)

Red-sub : (s : Sb) {a b : Tm} -> Red a b -> Red (sub s a) (sub s b)
Red-sub s = Red-map (sub s) (Step-sub s)
