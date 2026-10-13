{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Concrete/Confluence.agda
--
-- Church-Rosser for beta/pi/iota on Tm, by parallel reduction and
-- Takahashi's complete development:  Par t t'  ==>  Par t' (dev t)
-- (the triangle), hence the diamond for Par, hence confluence of Red.
-- (After MIN/Syntax/Confluence.agda, Tait--Martin-Loef.)
------------------------------------------------------------------------

module MAHLO.Concrete.Confluence where

open import MAHLO.Basic
open import MAHLO.Syntax using (Num ; zero ; suc)
open import MAHLO.Concrete.Tm
open import MAHLO.Concrete.Red

------------------------------------------------------------------------
-- Parallel reduction
------------------------------------------------------------------------

data Par : Tm -> Tm -> Set where
  p-var   : {i : Num} -> Par (tvar i) (tvar i)
  p-lam   : {b b' : Tm} -> Par b b' -> Par (tlam b) (tlam b')
  p-app   : {t t' u u' : Tm} -> Par t t' -> Par u u' -> Par (tapp t u) (tapp t' u')
  p-beta  : {b b' a a' : Tm} -> Par b b' -> Par a a' -> Par (tapp (tlam b) a) (inst b' a')
  p-pi    : {A A' F F' : Tm} -> Par A A' -> Par F F' -> Par (tpi A F) (tpi A' F')
  p-sig   : {A A' F F' : Tm} -> Par A A' -> Par F F' -> Par (tsig A F) (tsig A' F')
  p-pair  : {t t' u u' : Tm} -> Par t t' -> Par u u' -> Par (tpair t u) (tpair t' u')
  p-fst   : {t t' : Tm} -> Par t t' -> Par (tfst t) (tfst t')
  p-snd   : {t t' : Tm} -> Par t t' -> Par (tsnd t) (tsnd t')
  p-fstp  : {a a' b : Tm} -> Par a a' -> Par (tfst (tpair a b)) a'
  p-sndp  : {a b b' : Tm} -> Par b b' -> Par (tsnd (tpair a b)) b'
  p-nat   : Par tnat tnat
  p-ze    : Par tze tze
  p-sc    : {t t' : Tm} -> Par t t' -> Par (tsc t) (tsc t')
  p-rec   : {C C' z z' s s' n n' : Tm} -> Par C C' -> Par z z' -> Par s s' -> Par n n' ->
            Par (trec C z s n) (trec C' z' s' n')
  p-rec0  : {C z z' s : Tm} -> Par z z' -> Par (trec C z s tze) z'
  p-recS  : {C C' z z' s s' n n' : Tm} -> Par C C' -> Par z z' -> Par s s' -> Par n n' ->
            Par (trec C z s (tsc n)) (tapp (tapp s' n') (trec C' z' s' n'))
  p-V     : Par tV tV
  p-U     : {f f' g g' : Tm} -> Par f f' -> Par g g' -> Par (tU f g) (tU f' g')

par-refl : (t : Tm) -> Par t t
par-refl (tvar i) = p-var
par-refl (tlam b) = p-lam (par-refl b)
par-refl (tapp t u) = p-app (par-refl t) (par-refl u)
par-refl (tpi A F) = p-pi (par-refl A) (par-refl F)
par-refl (tsig A F) = p-sig (par-refl A) (par-refl F)
par-refl (tpair t u) = p-pair (par-refl t) (par-refl u)
par-refl (tfst t) = p-fst (par-refl t)
par-refl (tsnd t) = p-snd (par-refl t)
par-refl tnat = p-nat
par-refl tze = p-ze
par-refl (tsc t) = p-sc (par-refl t)
par-refl (trec C z s n) = p-rec (par-refl C) (par-refl z) (par-refl s) (par-refl n)
par-refl tV = p-V
par-refl (tU f g) = p-U (par-refl f) (par-refl g)

-- Step <= Par <= Red
step-par : {a b : Tm} -> Step a b -> Par a b
step-par (s-beta {b} {a}) = p-beta (par-refl b) (par-refl a)
step-par (s-fstp {a} {b}) = p-fstp (par-refl a)
step-par (s-sndp {a} {b}) = p-sndp (par-refl b)
step-par (s-rec0 {C} {z} {s}) = p-rec0 (par-refl z)
step-par (s-recS {C} {z} {s} {n}) = p-recS (par-refl C) (par-refl z) (par-refl s) (par-refl n)
step-par (s-lam p) = p-lam (step-par p)
step-par (s-app1 {u = u} p) = p-app (step-par p) (par-refl u)
step-par (s-app2 {t = t} p) = p-app (par-refl t) (step-par p)
step-par (s-pi1 {F = F} p) = p-pi (step-par p) (par-refl F)
step-par (s-pi2 {A = A} p) = p-pi (par-refl A) (step-par p)
step-par (s-sig1 {F = F} p) = p-sig (step-par p) (par-refl F)
step-par (s-sig2 {A = A} p) = p-sig (par-refl A) (step-par p)
step-par (s-pair1 {u = u} p) = p-pair (step-par p) (par-refl u)
step-par (s-pair2 {t = t} p) = p-pair (par-refl t) (step-par p)
step-par (s-fst p) = p-fst (step-par p)
step-par (s-snd p) = p-snd (step-par p)
step-par (s-sc p) = p-sc (step-par p)
step-par (s-rec1 {z = z} {s} {n} p) = p-rec (step-par p) (par-refl z) (par-refl s) (par-refl n)
step-par (s-rec2 {C = C} {s = s} {n} p) = p-rec (par-refl C) (step-par p) (par-refl s) (par-refl n)
step-par (s-rec3 {C = C} {z} {n = n} p) = p-rec (par-refl C) (par-refl z) (step-par p) (par-refl n)
step-par (s-rec4 {C = C} {z} {s} p) = p-rec (par-refl C) (par-refl z) (par-refl s) (step-par p)
step-par (s-U1 {g = g} p) = p-U (step-par p) (par-refl g)
step-par (s-U2 {f = f} p) = p-U (par-refl f) (step-par p)

par-red : {a b : Tm} -> Par a b -> Red a b
par-red p-var = r-refl
par-red (p-lam p) = R-lam (par-red p)
par-red (p-app p q) = R-app (par-red p) (par-red q)
par-red (p-beta p q) = Red-trans (R-app (R-lam (par-red p)) (par-red q)) (Red-one s-beta)
par-red (p-pi p q) = R-pi (par-red p) (par-red q)
par-red (p-sig p q) = R-sig (par-red p) (par-red q)
par-red (p-pair p q) = R-pair (par-red p) (par-red q)
par-red (p-fst p) = R-fst (par-red p)
par-red (p-snd p) = R-snd (par-red p)
par-red (p-fstp p) = r-step s-fstp (par-red p)
par-red (p-sndp p) = r-step s-sndp (par-red p)
par-red p-nat = r-refl
par-red p-ze = r-refl
par-red (p-sc p) = R-sc (par-red p)
par-red (p-rec p1 p2 p3 p4) = R-rec (par-red p1) (par-red p2) (par-red p3) (par-red p4)
par-red (p-rec0 p) = r-step s-rec0 (par-red p)
par-red (p-recS p1 p2 p3 p4) =
  Red-trans (R-rec (par-red p1) (par-red p2) (par-red p3) (R-sc (par-red p4)))
    (Red-one s-recS)
par-red p-V = r-refl
par-red (p-U p q) = R-U (par-red p) (par-red q)

------------------------------------------------------------------------
-- Par under renaming and substitution
------------------------------------------------------------------------

Par-ren : (r : Rn) {a b : Tm} -> Par a b -> Par (ren r a) (ren r b)
Par-ren r p-var = p-var
Par-ren r (p-lam p) = p-lam (Par-ren (liftR r) p)
Par-ren r (p-app p q) = p-app (Par-ren r p) (Par-ren r q)
Par-ren r (p-beta {b} {b'} {a} {a'} p q) =
  transport (Par (tapp (tlam (ren (liftR r) b)) (ren r a))) (Eq-sym (ren-inst r b' a'))
    (p-beta (Par-ren (liftR r) p) (Par-ren r q))
Par-ren r (p-pi p q) = p-pi (Par-ren r p) (Par-ren r q)
Par-ren r (p-sig p q) = p-sig (Par-ren r p) (Par-ren r q)
Par-ren r (p-pair p q) = p-pair (Par-ren r p) (Par-ren r q)
Par-ren r (p-fst p) = p-fst (Par-ren r p)
Par-ren r (p-snd p) = p-snd (Par-ren r p)
Par-ren r (p-fstp p) = p-fstp (Par-ren r p)
Par-ren r (p-sndp p) = p-sndp (Par-ren r p)
Par-ren r p-nat = p-nat
Par-ren r p-ze = p-ze
Par-ren r (p-sc p) = p-sc (Par-ren r p)
Par-ren r (p-rec p1 p2 p3 p4) = p-rec (Par-ren r p1) (Par-ren r p2) (Par-ren r p3) (Par-ren r p4)
Par-ren r (p-rec0 p) = p-rec0 (Par-ren r p)
Par-ren r (p-recS p1 p2 p3 p4) = p-recS (Par-ren r p1) (Par-ren r p2) (Par-ren r p3) (Par-ren r p4)
Par-ren r p-V = p-V
Par-ren r (p-U p q) = p-U (Par-ren r p) (Par-ren r q)

ParS : Sb -> Sb -> Set
ParS s s' = (i : Num) -> Par (s i) (s' i)

ParS-lift : {s s' : Sb} -> ParS s s' -> ParS (liftS s) (liftS s')
ParS-lift ps zero = p-var
ParS-lift ps (suc i) = Par-ren suc (ps i)

Par-sub : {s s' : Sb} -> ParS s s' -> {a b : Tm} -> Par a b -> Par (sub s a) (sub s' b)
Par-sub ps (p-var {i}) = ps i
Par-sub ps (p-lam p) = p-lam (Par-sub (ParS-lift ps) p)
Par-sub ps (p-app p q) = p-app (Par-sub ps p) (Par-sub ps q)
Par-sub {s} {s'} ps (p-beta {b} {b'} {a} {a'} p q) =
  transport (Par (tapp (tlam (sub (liftS s) b)) (sub s a))) (Eq-sym (sub-inst s' b' a'))
    (p-beta (Par-sub (ParS-lift ps) p) (Par-sub ps q))
Par-sub ps (p-pi p q) = p-pi (Par-sub ps p) (Par-sub ps q)
Par-sub ps (p-sig p q) = p-sig (Par-sub ps p) (Par-sub ps q)
Par-sub ps (p-pair p q) = p-pair (Par-sub ps p) (Par-sub ps q)
Par-sub ps (p-fst p) = p-fst (Par-sub ps p)
Par-sub ps (p-snd p) = p-snd (Par-sub ps p)
Par-sub ps (p-fstp p) = p-fstp (Par-sub ps p)
Par-sub ps (p-sndp p) = p-sndp (Par-sub ps p)
Par-sub ps p-nat = p-nat
Par-sub ps p-ze = p-ze
Par-sub ps (p-sc p) = p-sc (Par-sub ps p)
Par-sub ps (p-rec p1 p2 p3 p4) = p-rec (Par-sub ps p1) (Par-sub ps p2) (Par-sub ps p3) (Par-sub ps p4)
Par-sub ps (p-rec0 p) = p-rec0 (Par-sub ps p)
Par-sub ps (p-recS p1 p2 p3 p4) = p-recS (Par-sub ps p1) (Par-sub ps p2) (Par-sub ps p3) (Par-sub ps p4)
Par-sub ps p-V = p-V
Par-sub ps (p-U p q) = p-U (Par-sub ps p) (Par-sub ps q)

Par-inst : {b b' a a' : Tm} -> Par b b' -> Par a a' -> Par (inst b a) (inst b' a')
Par-inst p q = Par-sub ps p
  where
    ps : ParS (sub0 _) (sub0 _)
    ps zero = q
    ps (suc i) = p-var

------------------------------------------------------------------------
-- Complete development
------------------------------------------------------------------------

mutual
  dev : Tm -> Tm
  dev (tvar i) = tvar i
  dev (tlam b) = tlam (dev b)
  dev (tapp t u) = devApp t (dev u)
  dev (tpi A F) = tpi (dev A) (dev F)
  dev (tsig A F) = tsig (dev A) (dev F)
  dev (tpair t u) = tpair (dev t) (dev u)
  dev (tfst t) = devFst t
  dev (tsnd t) = devSnd t
  dev tnat = tnat
  dev tze = tze
  dev (tsc t) = tsc (dev t)
  dev (trec C z s n) = devRec C z s n
  dev tV = tV
  dev (tU f g) = tU (dev f) (dev g)

  devApp : Tm -> Tm -> Tm
  devApp (tlam b) u' = inst (dev b) u'
  devApp (tvar i) u' = tapp (tvar i) u'
  devApp (tapp t u) u' = tapp (dev (tapp t u)) u'
  devApp (tpi A F) u' = tapp (dev (tpi A F)) u'
  devApp (tsig A F) u' = tapp (dev (tsig A F)) u'
  devApp (tpair t u) u' = tapp (dev (tpair t u)) u'
  devApp (tfst t) u' = tapp (dev (tfst t)) u'
  devApp (tsnd t) u' = tapp (dev (tsnd t)) u'
  devApp tnat u' = tapp tnat u'
  devApp tze u' = tapp tze u'
  devApp (tsc t) u' = tapp (dev (tsc t)) u'
  devApp (trec C z s n) u' = tapp (dev (trec C z s n)) u'
  devApp tV u' = tapp tV u'
  devApp (tU f g) u' = tapp (dev (tU f g)) u'

  devFst : Tm -> Tm
  devFst (tpair a b) = dev a
  devFst (tvar i) = tfst (tvar i)
  devFst (tlam b) = tfst (dev (tlam b))
  devFst (tapp t u) = tfst (dev (tapp t u))
  devFst (tpi A F) = tfst (dev (tpi A F))
  devFst (tsig A F) = tfst (dev (tsig A F))
  devFst (tfst t) = tfst (dev (tfst t))
  devFst (tsnd t) = tfst (dev (tsnd t))
  devFst tnat = tfst tnat
  devFst tze = tfst tze
  devFst (tsc t) = tfst (dev (tsc t))
  devFst (trec C z s n) = tfst (dev (trec C z s n))
  devFst tV = tfst tV
  devFst (tU f g) = tfst (dev (tU f g))

  devSnd : Tm -> Tm
  devSnd (tpair a b) = dev b
  devSnd (tvar i) = tsnd (tvar i)
  devSnd (tlam b) = tsnd (dev (tlam b))
  devSnd (tapp t u) = tsnd (dev (tapp t u))
  devSnd (tpi A F) = tsnd (dev (tpi A F))
  devSnd (tsig A F) = tsnd (dev (tsig A F))
  devSnd (tfst t) = tsnd (dev (tfst t))
  devSnd (tsnd t) = tsnd (dev (tsnd t))
  devSnd tnat = tsnd tnat
  devSnd tze = tsnd tze
  devSnd (tsc t) = tsnd (dev (tsc t))
  devSnd (trec C z s n) = tsnd (dev (trec C z s n))
  devSnd tV = tsnd tV
  devSnd (tU f g) = tsnd (dev (tU f g))

  devRec : Tm -> Tm -> Tm -> Tm -> Tm
  devRec C z s tze = dev z
  devRec C z s (tsc n) = tapp (tapp (dev s) (dev n)) (trec (dev C) (dev z) (dev s) (dev n))
  devRec C z s (tvar i) = trec (dev C) (dev z) (dev s) (tvar i)
  devRec C z s (tlam b) = trec (dev C) (dev z) (dev s) (dev (tlam b))
  devRec C z s (tapp t u) = trec (dev C) (dev z) (dev s) (dev (tapp t u))
  devRec C z s (tpi A F) = trec (dev C) (dev z) (dev s) (dev (tpi A F))
  devRec C z s (tsig A F) = trec (dev C) (dev z) (dev s) (dev (tsig A F))
  devRec C z s (tpair t u) = trec (dev C) (dev z) (dev s) (dev (tpair t u))
  devRec C z s (tfst t) = trec (dev C) (dev z) (dev s) (dev (tfst t))
  devRec C z s (tsnd t) = trec (dev C) (dev z) (dev s) (dev (tsnd t))
  devRec C z s tnat = trec (dev C) (dev z) (dev s) tnat
  devRec C z s (trec C1 z1 s1 n1) = trec (dev C) (dev z) (dev s) (dev (trec C1 z1 s1 n1))
  devRec C z s tV = trec (dev C) (dev z) (dev s) tV
  devRec C z s (tU f g) = trec (dev C) (dev z) (dev s) (dev (tU f g))

------------------------------------------------------------------------
-- The triangle:  Par t t'  ==>  Par t' (dev t)
------------------------------------------------------------------------

mutual
  tri : {t t' : Tm} -> Par t t' -> Par t' (dev t)
  tri p-var = p-var
  tri (p-lam p) = p-lam (tri p)
  tri (p-app p q) = triApp p (tri p) (tri q)
  tri (p-beta p q) = Par-inst (tri p) (tri q)
  tri (p-pi p q) = p-pi (tri p) (tri q)
  tri (p-sig p q) = p-sig (tri p) (tri q)
  tri (p-pair p q) = p-pair (tri p) (tri q)
  tri (p-fst p) = triFst p (tri p)
  tri (p-snd p) = triSnd p (tri p)
  tri (p-fstp p) = tri p
  tri (p-sndp p) = tri p
  tri p-nat = p-nat
  tri p-ze = p-ze
  tri (p-sc p) = p-sc (tri p)
  tri (p-rec p1 p2 p3 p4) = triRec p4 (tri p1) (tri p2) (tri p3) (tri p4)
  tri (p-rec0 p) = tri p
  tri (p-recS p1 p2 p3 p4) =
    p-app (p-app (tri p3) (tri p4)) (p-rec (tri p1) (tri p2) (tri p3) (tri p4))
  tri p-V = p-V
  tri (p-U p q) = p-U (tri p) (tri q)

  triApp : {t t' u' du : Tm} -> Par t t' -> Par t' (dev t) -> Par u' du ->
           Par (tapp t' u') (devApp t du)
  triApp (p-lam p) (p-lam h) hu = p-beta h hu
  triApp p-var h hu = p-app h hu
  triApp (p-app p q) h hu = p-app h hu
  triApp (p-beta p q) h hu = p-app h hu
  triApp (p-pi p q) h hu = p-app h hu
  triApp (p-sig p q) h hu = p-app h hu
  triApp (p-pair p q) h hu = p-app h hu
  triApp (p-fst p) h hu = p-app h hu
  triApp (p-snd p) h hu = p-app h hu
  triApp (p-fstp p) h hu = p-app h hu
  triApp (p-sndp p) h hu = p-app h hu
  triApp p-nat h hu = p-app h hu
  triApp p-ze h hu = p-app h hu
  triApp (p-sc p) h hu = p-app h hu
  triApp (p-rec p1 p2 p3 p4) h hu = p-app h hu
  triApp (p-rec0 p) h hu = p-app h hu
  triApp (p-recS p1 p2 p3 p4) h hu = p-app h hu
  triApp p-V h hu = p-app h hu
  triApp (p-U p q) h hu = p-app h hu

  triFst : {t t' : Tm} -> Par t t' -> Par t' (dev t) -> Par (tfst t') (devFst t)
  triFst (p-pair p q) (p-pair h k) = p-fstp h
  triFst p-var h = p-fst h
  triFst (p-lam p) h = p-fst h
  triFst (p-app p q) h = p-fst h
  triFst (p-beta p q) h = p-fst h
  triFst (p-pi p q) h = p-fst h
  triFst (p-sig p q) h = p-fst h
  triFst (p-fst p) h = p-fst h
  triFst (p-snd p) h = p-fst h
  triFst (p-fstp p) h = p-fst h
  triFst (p-sndp p) h = p-fst h
  triFst p-nat h = p-fst h
  triFst p-ze h = p-fst h
  triFst (p-sc p) h = p-fst h
  triFst (p-rec p1 p2 p3 p4) h = p-fst h
  triFst (p-rec0 p) h = p-fst h
  triFst (p-recS p1 p2 p3 p4) h = p-fst h
  triFst p-V h = p-fst h
  triFst (p-U p q) h = p-fst h

  triSnd : {t t' : Tm} -> Par t t' -> Par t' (dev t) -> Par (tsnd t') (devSnd t)
  triSnd (p-pair p q) (p-pair h k) = p-sndp k
  triSnd p-var h = p-snd h
  triSnd (p-lam p) h = p-snd h
  triSnd (p-app p q) h = p-snd h
  triSnd (p-beta p q) h = p-snd h
  triSnd (p-pi p q) h = p-snd h
  triSnd (p-sig p q) h = p-snd h
  triSnd (p-fst p) h = p-snd h
  triSnd (p-snd p) h = p-snd h
  triSnd (p-fstp p) h = p-snd h
  triSnd (p-sndp p) h = p-snd h
  triSnd p-nat h = p-snd h
  triSnd p-ze h = p-snd h
  triSnd (p-sc p) h = p-snd h
  triSnd (p-rec p1 p2 p3 p4) h = p-snd h
  triSnd (p-rec0 p) h = p-snd h
  triSnd (p-recS p1 p2 p3 p4) h = p-snd h
  triSnd p-V h = p-snd h
  triSnd (p-U p q) h = p-snd h

  triRec : {C' z' s' n n' : Tm} {C z s : Tm} -> Par n n' ->
           Par C' (dev C) -> Par z' (dev z) -> Par s' (dev s) -> Par n' (dev n) ->
           Par (trec C' z' s' n') (devRec C z s n)
  triRec p-ze hC hz hs hn = p-rec0 hz
  triRec (p-sc p) hC hz hs (p-sc hn) = p-recS hC hz hs hn
  triRec p-var hC hz hs hn = p-rec hC hz hs hn
  triRec (p-lam p) hC hz hs hn = p-rec hC hz hs hn
  triRec (p-app p q) hC hz hs hn = p-rec hC hz hs hn
  triRec (p-beta p q) hC hz hs hn = p-rec hC hz hs hn
  triRec (p-pi p q) hC hz hs hn = p-rec hC hz hs hn
  triRec (p-sig p q) hC hz hs hn = p-rec hC hz hs hn
  triRec (p-pair p q) hC hz hs hn = p-rec hC hz hs hn
  triRec (p-fst p) hC hz hs hn = p-rec hC hz hs hn
  triRec (p-snd p) hC hz hs hn = p-rec hC hz hs hn
  triRec (p-fstp p) hC hz hs hn = p-rec hC hz hs hn
  triRec (p-sndp p) hC hz hs hn = p-rec hC hz hs hn
  triRec p-nat hC hz hs hn = p-rec hC hz hs hn
  triRec (p-rec p1 p2 p3 p4) hC hz hs hn = p-rec hC hz hs hn
  triRec (p-rec0 p) hC hz hs hn = p-rec hC hz hs hn
  triRec (p-recS p1 p2 p3 p4) hC hz hs hn = p-rec hC hz hs hn
  triRec p-V hC hz hs hn = p-rec hC hz hs hn
  triRec (p-U p q) hC hz hs hn = p-rec hC hz hs hn

------------------------------------------------------------------------
-- Confluence
------------------------------------------------------------------------

-- reflexive-transitive closure of Par
data PRed : Tm -> Tm -> Set where
  pr-refl : {a : Tm} -> PRed a a
  pr-step : {a b c : Tm} -> Par a b -> PRed b c -> PRed a c

-- strip lemma
strip : {a b c : Tm} -> Par a b -> PRed a c -> Sigma Tm (\ d -> PRed b d * Par c d)
strip {b = b} p pr-refl = b , (pr-refl , p)
strip p (pr-step q r) =
  let s = strip (tri q) r in fst s , (pr-step (tri p) (fst (snd s)) , snd (snd s))

PRed-confluent : {a b c : Tm} -> PRed a b -> PRed a c -> Sigma Tm (\ d -> PRed b d * PRed c d)
PRed-confluent {c = c} pr-refl q = c , (q , pr-refl)
PRed-confluent (pr-step p r) q =
  let s1 = strip p q
      s2 = PRed-confluent r (fst (snd s1))
  in fst s2 , (fst (snd s2) , pr-step (snd (snd s1)) (snd (snd s2)))

red-pred : {a b : Tm} -> Red a b -> PRed a b
red-pred r-refl = pr-refl
red-pred (r-step s r) = pr-step (step-par s) (red-pred r)

pred-red : {a b : Tm} -> PRed a b -> Red a b
pred-red pr-refl = r-refl
pred-red (pr-step p r) = Red-trans (par-red p) (pred-red r)

-- Church-Rosser
confluent : {a b c : Tm} -> Red a b -> Red a c -> Sigma Tm (\ d -> Red b d * Red c d)
confluent p q =
  let s = PRed-confluent (red-pred p) (red-pred q)
  in fst s , (pred-red (fst (snd s)) , pred-red (snd (snd s)))
