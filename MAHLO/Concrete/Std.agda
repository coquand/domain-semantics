{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Concrete/Std.agda
--
-- Weak-head standardisation for beta/pi/iota on Tm (Takahashi), in the
-- minimal form needed by the conversion algorithm:
--
--   factor : Par a b  ->  a ->wh* c  and  c =>internal b
--   wn     : a ⇓ v    ->  a weak-head normalises
--
-- Weak-head reduction (Wh) contracts the head redex only: beta at the
-- head of an application spine, projections of pairs, rec on 0 / S.
-- Internal parallel reduction (IPar) is parallel reduction that does
-- not contract the head redex.  The proof:
--   * factor, by induction on Par, using a substitution lemma
--     (stdSub) for the beta case;
--   * postponement of one internal step after one weak-head step;
--   * an internal reduct of a weak-head normal form is one, backwards.
------------------------------------------------------------------------

module MAHLO.Concrete.Std where

open import MAHLO.Basic
open import MAHLO.Syntax using (Num ; zero ; suc)
open import MAHLO.Concrete.Tm
open import MAHLO.Concrete.Red
open import MAHLO.Concrete.Confluence
open import MAHLO.Concrete.Values

------------------------------------------------------------------------
-- Weak-head reduction
------------------------------------------------------------------------

data Wh : Tm -> Tm -> Set where
  wh-beta : {b a : Tm} -> Wh (tapp (tlam b) a) (inst b a)
  wh-app  : {t t' u : Tm} -> Wh t t' -> Wh (tapp t u) (tapp t' u)
  wh-fstp : {a b : Tm} -> Wh (tfst (tpair a b)) a
  wh-sndp : {a b : Tm} -> Wh (tsnd (tpair a b)) b
  wh-fst  : {t t' : Tm} -> Wh t t' -> Wh (tfst t) (tfst t')
  wh-snd  : {t t' : Tm} -> Wh t t' -> Wh (tsnd t) (tsnd t')
  wh-rec0 : {C z s : Tm} -> Wh (trec C z s tze) z
  wh-recS : {C z s n : Tm} -> Wh (trec C z s (tsc n)) (tapp (tapp s n) (trec C z s n))
  wh-rec  : {C z s n n' : Tm} -> Wh n n' -> Wh (trec C z s n) (trec C z s n')

data Whs : Tm -> Tm -> Set where
  whs-refl : {a : Tm} -> Whs a a
  whs-step : {a b c : Tm} -> Wh a b -> Whs b c -> Whs a c

Whs-trans : {a b c : Tm} -> Whs a b -> Whs b c -> Whs a c
Whs-trans whs-refl q = q
Whs-trans (whs-step s p) q = whs-step s (Whs-trans p q)

Whs-map : (f : Tm -> Tm) -> ({a b : Tm} -> Wh a b -> Wh (f a) (f b)) -> {a b : Tm} -> Whs a b -> Whs (f a) (f b)
Whs-map f h whs-refl = whs-refl
Whs-map f h (whs-step s p) = whs-step (h s) (Whs-map f h p)

Wh-sub : (s : Sb) {a b : Tm} -> Wh a b -> Wh (sub s a) (sub s b)
Wh-sub s (wh-beta {b} {a}) = transport (Wh (tapp (tlam (sub (liftS s) b)) (sub s a))) (Eq-sym (sub-inst s b a)) wh-beta
Wh-sub s (wh-app p) = wh-app (Wh-sub s p)
Wh-sub s wh-fstp = wh-fstp
Wh-sub s wh-sndp = wh-sndp
Wh-sub s (wh-fst p) = wh-fst (Wh-sub s p)
Wh-sub s (wh-snd p) = wh-snd (Wh-sub s p)
Wh-sub s wh-rec0 = wh-rec0
Wh-sub s wh-recS = wh-recS
Wh-sub s (wh-rec p) = wh-rec (Wh-sub s p)

Whs-sub : (s : Sb) {a b : Tm} -> Whs a b -> Whs (sub s a) (sub s b)
Whs-sub s = Whs-map (sub s) (Wh-sub s)

------------------------------------------------------------------------
-- Internal parallel reduction
------------------------------------------------------------------------

data IPar : Tm -> Tm -> Set where
  ip-var  : {i : Num} -> IPar (tvar i) (tvar i)
  ip-lam  : {b b' : Tm} -> Par b b' -> IPar (tlam b) (tlam b')
  ip-app  : {t t' u u' : Tm} -> IPar t t' -> Par u u' -> IPar (tapp t u) (tapp t' u')
  ip-pi   : {A A' F F' : Tm} -> Par A A' -> Par F F' -> IPar (tpi A F) (tpi A' F')
  ip-sig  : {A A' F F' : Tm} -> Par A A' -> Par F F' -> IPar (tsig A F) (tsig A' F')
  ip-pair : {t t' u u' : Tm} -> Par t t' -> Par u u' -> IPar (tpair t u) (tpair t' u')
  ip-fst  : {t t' : Tm} -> IPar t t' -> IPar (tfst t) (tfst t')
  ip-snd  : {t t' : Tm} -> IPar t t' -> IPar (tsnd t) (tsnd t')
  ip-nat  : IPar tnat tnat
  ip-ze   : IPar tze tze
  ip-sc   : {t t' : Tm} -> Par t t' -> IPar (tsc t) (tsc t')
  ip-rec  : {C C' z z' s s' n n' : Tm} -> Par C C' -> Par z z' -> Par s s' -> IPar n n' ->
            IPar (trec C z s n) (trec C' z' s' n')
  ip-V    : IPar tV tV
  ip-U    : {f f' g g' : Tm} -> Par f f' -> Par g g' -> IPar (tU f g) (tU f' g')

ipar-par : {a b : Tm} -> IPar a b -> Par a b
ipar-par ip-var = p-var
ipar-par (ip-lam p) = p-lam p
ipar-par (ip-app p q) = p-app (ipar-par p) q
ipar-par (ip-pi p q) = p-pi p q
ipar-par (ip-sig p q) = p-sig p q
ipar-par (ip-pair p q) = p-pair p q
ipar-par (ip-fst p) = p-fst (ipar-par p)
ipar-par (ip-snd p) = p-snd (ipar-par p)
ipar-par ip-nat = p-nat
ipar-par ip-ze = p-ze
ipar-par (ip-sc p) = p-sc p
ipar-par (ip-rec p1 p2 p3 p4) = p-rec p1 p2 p3 (ipar-par p4)
ipar-par ip-V = p-V
ipar-par (ip-U p q) = p-U p q

-- standard parallel reduction:  weak-head steps, then an internal step
Std : Tm -> Tm -> Set
Std a b = Sigma Tm (\ c -> Whs a c * IPar c b)

std-wh : {a b c : Tm} -> Wh a b -> Std b c -> Std a c
std-wh s (d , (p , q)) = d , (whs-step s p , q)

std-whs : {a b c : Tm} -> Whs a b -> Std b c -> Std a c
std-whs p (d , (q , r)) = d , (Whs-trans p q , r)

std-ipar : {a b : Tm} -> IPar a b -> Std a b
std-ipar p = _ , (whs-refl , p)

------------------------------------------------------------------------
-- Substitution lemma
------------------------------------------------------------------------

StdS : Sb -> Sb -> Set
StdS s s' = (i : Num) -> Std (s i) (s' i)

stdSub : {s s' : Sb} -> ParS s s' -> StdS s s' -> {a b : Tm} -> IPar a b -> Std (sub s a) (sub s' b)
stdSub ps ss (ip-var {i}) = ss i
stdSub ps ss (ip-lam p) = std-ipar (ip-lam (Par-sub (ParS-lift ps) p))
stdSub {s} ps ss (ip-app {u = u} p q) =
  let r = stdSub ps ss p
  in tapp (fst r) (sub s u) , (Whs-map (\ x -> tapp x (sub s u)) wh-app (fst (snd r)) , ip-app (snd (snd r)) (Par-sub ps q))
stdSub ps ss (ip-pi p q) = std-ipar (ip-pi (Par-sub ps p) (Par-sub ps q))
stdSub ps ss (ip-sig p q) = std-ipar (ip-sig (Par-sub ps p) (Par-sub ps q))
stdSub ps ss (ip-pair p q) = std-ipar (ip-pair (Par-sub ps p) (Par-sub ps q))
stdSub ps ss (ip-fst p) =
  let r = stdSub ps ss p in tfst (fst r) , (Whs-map tfst wh-fst (fst (snd r)) , ip-fst (snd (snd r)))
stdSub ps ss (ip-snd p) =
  let r = stdSub ps ss p in tsnd (fst r) , (Whs-map tsnd wh-snd (fst (snd r)) , ip-snd (snd (snd r)))
stdSub ps ss ip-nat = std-ipar ip-nat
stdSub ps ss ip-ze = std-ipar ip-ze
stdSub ps ss (ip-sc p) = std-ipar (ip-sc (Par-sub ps p))
stdSub {s} ps ss (ip-rec {C} {z = z} {s = s0} p1 p2 p3 p4) =
  let r = stdSub ps ss p4
  in trec (sub s C) (sub s z) (sub s s0) (fst r) ,
     (Whs-map (trec (sub s C) (sub s z) (sub s s0)) wh-rec (fst (snd r)) ,
      ip-rec (Par-sub ps p1) (Par-sub ps p2) (Par-sub ps p3) (snd (snd r)))
stdSub ps ss ip-V = std-ipar ip-V
stdSub ps ss (ip-U p q) = std-ipar (ip-U (Par-sub ps p) (Par-sub ps q))

------------------------------------------------------------------------
-- Factorisation
------------------------------------------------------------------------

factor : {a b : Tm} -> Par a b -> Std a b
factor p-var = std-ipar ip-var
factor (p-lam p) = std-ipar (ip-lam p)
factor (p-app {u = u} p q) =
  let r = factor p in tapp (fst r) u , (Whs-map (\ x -> tapp x u) wh-app (fst (snd r)) , ip-app (snd (snd r)) q)
factor (p-beta {b} {b'} {a} {a'} p q) =
  std-wh wh-beta (std-whs (Whs-sub (sub0 a) (fst (snd rb))) (stdSub ps ss (snd (snd rb))))
  where
    rb = factor p
    ps : ParS (sub0 a) (sub0 a')
    ps zero = q
    ps (suc i) = p-var
    ss : StdS (sub0 a) (sub0 a')
    ss zero = factor q
    ss (suc i) = std-ipar ip-var
factor (p-pi p q) = std-ipar (ip-pi p q)
factor (p-sig p q) = std-ipar (ip-sig p q)
factor (p-pair p q) = std-ipar (ip-pair p q)
factor (p-fst p) = let r = factor p in tfst (fst r) , (Whs-map tfst wh-fst (fst (snd r)) , ip-fst (snd (snd r)))
factor (p-snd p) = let r = factor p in tsnd (fst r) , (Whs-map tsnd wh-snd (fst (snd r)) , ip-snd (snd (snd r)))
factor (p-fstp p) = std-wh wh-fstp (factor p)
factor (p-sndp p) = std-wh wh-sndp (factor p)
factor p-nat = std-ipar ip-nat
factor p-ze = std-ipar ip-ze
factor (p-sc p) = std-ipar (ip-sc p)
factor (p-rec {C} {z = z} {s = s} p1 p2 p3 p4) =
  let r = factor p4
  in trec C z s (fst r) , (Whs-map (trec C z s) wh-rec (fst (snd r)) , ip-rec p1 p2 p3 (snd (snd r)))
factor (p-rec0 p) = std-wh wh-rec0 (factor p)
factor (p-recS {C} {z = z} {s = s} {n = n} p1 p2 p3 p4) =
  let r = factor p3
  in std-wh wh-recS
       (tapp (tapp (fst r) n) (trec C z s n) ,
        (Whs-map (\ x -> tapp (tapp x n) (trec C z s n)) (\ w -> wh-app (wh-app w)) (fst (snd r)) ,
         ip-app (ip-app (snd (snd r)) p4) (p-rec p1 p2 p3 p4)))
factor p-V = std-ipar ip-V
factor (p-U p q) = std-ipar (ip-U p q)

------------------------------------------------------------------------
-- Postponement of an internal step after a weak-head step
------------------------------------------------------------------------

postpone : {a b c : Tm} -> IPar a b -> Wh b c -> Sigma Tm (\ d -> Wh a d * Par d c)
postpone (ip-app p q) (wh-app w) = let r = postpone p w in _ , (wh-app (fst (snd r)) , p-app (snd (snd r)) q)
postpone (ip-fst p) (wh-fst w) = let r = postpone p w in _ , (wh-fst (fst (snd r)) , p-fst (snd (snd r)))
postpone (ip-snd p) (wh-snd w) = let r = postpone p w in _ , (wh-snd (fst (snd r)) , p-snd (snd (snd r)))
postpone (ip-rec p1 p2 p3 p4) (wh-rec w) =
  let r = postpone p4 w in _ , (wh-rec (fst (snd r)) , p-rec p1 p2 p3 (snd (snd r)))
postpone (ip-app (ip-lam p) q) wh-beta = _ , (wh-beta , Par-inst p q)
postpone (ip-fst (ip-pair p q)) wh-fstp = _ , (wh-fstp , p)
postpone (ip-snd (ip-pair p q)) wh-sndp = _ , (wh-sndp , q)
postpone (ip-rec p1 p2 p3 ip-ze) wh-rec0 = _ , (wh-rec0 , p2)
postpone (ip-rec p1 p2 p3 (ip-sc p4)) wh-recS = _ , (wh-recS , p-app (p-app p3 p4) (p-rec p1 p2 p3 p4))

------------------------------------------------------------------------
-- Weak-head normal forms
------------------------------------------------------------------------

WhNF : Tm -> Set
WhNF a = {b : Tm} -> Wh a b -> Empty

-- weak-head normalisation
WN : Tm -> Set
WN a = Sigma Tm (\ w -> Whs a w * WhNF w)

-- the head shapes, preserved backwards by internal parallel reduction
mutual
  data WNe : Tm -> Set where
    wn-var : {i : Num} -> WNe (tvar i)
    wn-app : {t u : Tm} -> WNe t -> WNe (tapp t u)
    wn-fst : {t : Tm} -> WNe t -> WNe (tfst t)
    wn-snd : {t : Tm} -> WNe t -> WNe (tsnd t)
    wn-rec : {C z s n : Tm} -> WNe n -> WNe (trec C z s n)

  data WShape : Tm -> Set where
    ws-ne   : {t : Tm} -> WNe t -> WShape t
    ws-lam  : {b : Tm} -> WShape (tlam b)
    ws-pair : {a b : Tm} -> WShape (tpair a b)
    ws-pi   : {a b : Tm} -> WShape (tpi a b)
    ws-sig  : {a b : Tm} -> WShape (tsig a b)
    ws-nat  : WShape tnat
    ws-ze   : WShape tze
    ws-sc   : {a : Tm} -> WShape (tsc a)
    ws-V    : WShape tV
    ws-U    : {a b : Tm} -> WShape (tU a b)

wne-nf : {t : Tm} -> WNe t -> WhNF t
wne-nf wn-var ()
wne-nf (wn-app ()) wh-beta
wne-nf (wn-app n) (wh-app w) = wne-nf n w
wne-nf (wn-fst ()) wh-fstp
wne-nf (wn-fst n) (wh-fst w) = wne-nf n w
wne-nf (wn-snd ()) wh-sndp
wne-nf (wn-snd n) (wh-snd w) = wne-nf n w
wne-nf (wn-rec ()) wh-rec0
wne-nf (wn-rec ()) wh-recS
wne-nf (wn-rec n) (wh-rec w) = wne-nf n w

wshape-nf : {t : Tm} -> WShape t -> WhNF t
wshape-nf (ws-ne n) w = wne-nf n w
wshape-nf ws-lam ()
wshape-nf ws-pair ()
wshape-nf ws-pi ()
wshape-nf ws-sig ()
wshape-nf ws-nat ()
wshape-nf ws-ze ()
wshape-nf ws-sc ()
wshape-nf ws-V ()
wshape-nf ws-U ()

ipar-wne : {a b : Tm} -> IPar a b -> WNe b -> WNe a
ipar-wne ip-var wn-var = wn-var
ipar-wne (ip-app p q) (wn-app n) = wn-app (ipar-wne p n)
ipar-wne (ip-fst p) (wn-fst n) = wn-fst (ipar-wne p n)
ipar-wne (ip-snd p) (wn-snd n) = wn-snd (ipar-wne p n)
ipar-wne (ip-rec p1 p2 p3 p4) (wn-rec n) = wn-rec (ipar-wne p4 n)

ipar-shape : {a b : Tm} -> IPar a b -> WShape b -> WShape a
ipar-shape p (ws-ne n) = ws-ne (ipar-wne p n)
ipar-shape (ip-lam p) ws-lam = ws-lam
ipar-shape (ip-pair p q) ws-pair = ws-pair
ipar-shape (ip-pi p q) ws-pi = ws-pi
ipar-shape (ip-sig p q) ws-sig = ws-sig
ipar-shape ip-nat ws-nat = ws-nat
ipar-shape ip-ze ws-ze = ws-ze
ipar-shape (ip-sc p) ws-sc = ws-sc
ipar-shape ip-V ws-V = ws-V
ipar-shape (ip-U p q) ws-U = ws-U

-- values have a weak-head shape
mutual
  ne-wne : {t : Tm} -> Ne t -> WNe t
  ne-wne ne-var = wn-var
  ne-wne (ne-app n v) = wn-app (ne-wne n)
  ne-wne (ne-fst n) = wn-fst (ne-wne n)
  ne-wne (ne-snd n) = wn-snd (ne-wne n)
  ne-wne (ne-rec C z s n) = wn-rec (ne-wne n)

val-shape : {t : Tm} -> Val t -> WShape t
val-shape (v-ne n) = ws-ne (ne-wne n)
val-shape (v-lam b) = ws-lam
val-shape (v-pair a b) = ws-pair
val-shape (v-pi a b) = ws-pi
val-shape (v-sig a b) = ws-sig
val-shape v-nat = ws-nat
val-shape v-ze = ws-ze
val-shape (v-sc a) = ws-sc
val-shape v-V = ws-V
val-shape (v-U a b) = ws-U

------------------------------------------------------------------------
-- Reaching a weak-head shape by arbitrary reduction  ==>  weak-head
-- normalisation
------------------------------------------------------------------------

-- weak-head reduction to a shape
WS : Tm -> Set
WS a = Sigma Tm (\ w -> Whs a w * WShape w)

-- an internal reduct of a term that reaches a shape: so does the term
ipar-ws : {a b : Tm} -> IPar a b -> {w : Tm} -> Whs b w -> WShape w -> WS a
ipar-ws p whs-refl sh = _ , (whs-refl , ipar-shape p sh)
ipar-ws p (whs-step s rest) sh =
  let r = postpone p s
      f = factor (snd (snd r))
      k = ipar-ws (snd (snd f)) rest sh
  in fst k , (whs-step (fst (snd r)) (Whs-trans (fst (snd f)) (fst (snd k))) , snd (snd k))

red-ws : {a b : Tm} -> Red a b -> WShape b -> WS a
red-ws r-refl sh = _ , (whs-refl , sh)
red-ws (r-step s r) sh =
  let k = red-ws r sh
      f = factor (step-par s)
      m = ipar-ws (snd (snd f)) (fst (snd k)) (snd (snd k))
  in fst m , (Whs-trans (fst (snd f)) (fst (snd m)) , snd (snd m))

-- a term with a value weak-head normalises (to a weak-head shape)
wn : {a v : Tm} -> a ⇓ v -> WS a
wn (r , vv) = red-ws r (val-shape vv)

wn-nf : {a v : Tm} -> a ⇓ v -> WN a
wn-nf e = let k = wn e in fst k , (fst (snd k) , wshape-nf (snd (snd k)))
