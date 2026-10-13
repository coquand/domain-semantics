{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Concrete/Tm.agda
--
-- The carrier of the concrete term model (plan Sec. 6.2): erased,
-- untyped terms with unbounded de Bruijn indices (an infinite supply of
-- free variables, for the fresh neutrals of (A3)).  No lambda
-- annotations (erasure), and no fhat/ghat: the denotation performs the
-- delta-steps, so the reductions are beta, pi and iota only.
-- Renaming, substitution and their composition laws.
------------------------------------------------------------------------

module MAHLO.Concrete.Tm where

open import MAHLO.Basic
open import MAHLO.Syntax using (Num ; zero ; suc ; cong2 ; cong4)

data Tm : Set where
  tvar  : Num -> Tm
  tlam  : Tm -> Tm
  tapp  : Tm -> Tm -> Tm
  tpi   : Tm -> Tm -> Tm
  tsig  : Tm -> Tm -> Tm
  tpair : Tm -> Tm -> Tm
  tfst  : Tm -> Tm
  tsnd  : Tm -> Tm
  tnat  : Tm
  tze   : Tm
  tsc   : Tm -> Tm
  trec  : Tm -> Tm -> Tm -> Tm -> Tm
  tV    : Tm
  tU    : Tm -> Tm -> Tm

------------------------------------------------------------------------
-- Renaming
------------------------------------------------------------------------

Rn : Set
Rn = Num -> Num

liftR : Rn -> Rn
liftR r zero    = zero
liftR r (suc i) = suc (r i)

ren : Rn -> Tm -> Tm
ren r (tvar i)       = tvar (r i)
ren r (tlam b)       = tlam (ren (liftR r) b)
ren r (tapp t u)     = tapp (ren r t) (ren r u)
ren r (tpi A F)      = tpi (ren r A) (ren r F)
ren r (tsig A F)     = tsig (ren r A) (ren r F)
ren r (tpair t u)    = tpair (ren r t) (ren r u)
ren r (tfst t)       = tfst (ren r t)
ren r (tsnd t)       = tsnd (ren r t)
ren r tnat           = tnat
ren r tze            = tze
ren r (tsc t)        = tsc (ren r t)
ren r (trec C z s n) = trec (ren r C) (ren r z) (ren r s) (ren r n)
ren r tV             = tV
ren r (tU f g)       = tU (ren r f) (ren r g)

shift : Tm -> Tm
shift = ren suc

------------------------------------------------------------------------
-- Substitution
------------------------------------------------------------------------

Sb : Set
Sb = Num -> Tm

liftS : Sb -> Sb
liftS s zero    = tvar zero
liftS s (suc i) = shift (s i)

sub : Sb -> Tm -> Tm
sub s (tvar i)       = s i
sub s (tlam b)       = tlam (sub (liftS s) b)
sub s (tapp t u)     = tapp (sub s t) (sub s u)
sub s (tpi A F)      = tpi (sub s A) (sub s F)
sub s (tsig A F)     = tsig (sub s A) (sub s F)
sub s (tpair t u)    = tpair (sub s t) (sub s u)
sub s (tfst t)       = tfst (sub s t)
sub s (tsnd t)       = tsnd (sub s t)
sub s tnat           = tnat
sub s tze            = tze
sub s (tsc t)        = tsc (sub s t)
sub s (trec C z u n) = trec (sub s C) (sub s z) (sub s u) (sub s n)
sub s tV             = tV
sub s (tU f g)       = tU (sub s f) (sub s g)

-- [a/0]
sub0 : Tm -> Sb
sub0 a zero    = a
sub0 a (suc i) = tvar i

inst : Tm -> Tm -> Tm
inst b a = sub (sub0 a) b

------------------------------------------------------------------------
-- Composition laws (pointwise-general forms, as in MAHLO/Syntax.agda)
------------------------------------------------------------------------

ren-ren-gen : (r1 r2 r : Rn) -> ((i : Num) -> Eq (r1 (r2 i)) (r i)) ->
              (t : Tm) -> Eq (ren r1 (ren r2 t)) (ren r t)
ren-ren-gen r1 r2 r e (tvar i) = Eq-cong tvar (e i)
ren-ren-gen r1 r2 r e (tlam b) = Eq-cong tlam (ren-ren-gen (liftR r1) (liftR r2) (liftR r) e' b)
  where
    e' : (i : Num) -> Eq (liftR r1 (liftR r2 i)) (liftR r i)
    e' zero    = refl
    e' (suc i) = Eq-cong suc (e i)
ren-ren-gen r1 r2 r e (tapp t u) = cong2 tapp (ren-ren-gen r1 r2 r e t) (ren-ren-gen r1 r2 r e u)
ren-ren-gen r1 r2 r e (tpi A F) = cong2 tpi (ren-ren-gen r1 r2 r e A) (ren-ren-gen r1 r2 r e F)
ren-ren-gen r1 r2 r e (tsig A F) = cong2 tsig (ren-ren-gen r1 r2 r e A) (ren-ren-gen r1 r2 r e F)
ren-ren-gen r1 r2 r e (tpair t u) = cong2 tpair (ren-ren-gen r1 r2 r e t) (ren-ren-gen r1 r2 r e u)
ren-ren-gen r1 r2 r e (tfst t) = Eq-cong tfst (ren-ren-gen r1 r2 r e t)
ren-ren-gen r1 r2 r e (tsnd t) = Eq-cong tsnd (ren-ren-gen r1 r2 r e t)
ren-ren-gen r1 r2 r e tnat = refl
ren-ren-gen r1 r2 r e tze = refl
ren-ren-gen r1 r2 r e (tsc t) = Eq-cong tsc (ren-ren-gen r1 r2 r e t)
ren-ren-gen r1 r2 r e (trec C z s n) =
  cong4 trec (ren-ren-gen r1 r2 r e C) (ren-ren-gen r1 r2 r e z)
             (ren-ren-gen r1 r2 r e s) (ren-ren-gen r1 r2 r e n)
ren-ren-gen r1 r2 r e tV = refl
ren-ren-gen r1 r2 r e (tU f g) = cong2 tU (ren-ren-gen r1 r2 r e f) (ren-ren-gen r1 r2 r e g)

sub-ren-gen : (s : Sb) (r : Rn) (s' : Sb) -> ((i : Num) -> Eq (s (r i)) (s' i)) ->
              (t : Tm) -> Eq (sub s (ren r t)) (sub s' t)
sub-ren-gen s r s' e (tvar i) = e i
sub-ren-gen s r s' e (tlam b) = Eq-cong tlam (sub-ren-gen (liftS s) (liftR r) (liftS s') e' b)
  where
    e' : (i : Num) -> Eq (liftS s (liftR r i)) (liftS s' i)
    e' zero    = refl
    e' (suc i) = Eq-cong shift (e i)
sub-ren-gen s r s' e (tapp t u) = cong2 tapp (sub-ren-gen s r s' e t) (sub-ren-gen s r s' e u)
sub-ren-gen s r s' e (tpi A F) = cong2 tpi (sub-ren-gen s r s' e A) (sub-ren-gen s r s' e F)
sub-ren-gen s r s' e (tsig A F) = cong2 tsig (sub-ren-gen s r s' e A) (sub-ren-gen s r s' e F)
sub-ren-gen s r s' e (tpair t u) = cong2 tpair (sub-ren-gen s r s' e t) (sub-ren-gen s r s' e u)
sub-ren-gen s r s' e (tfst t) = Eq-cong tfst (sub-ren-gen s r s' e t)
sub-ren-gen s r s' e (tsnd t) = Eq-cong tsnd (sub-ren-gen s r s' e t)
sub-ren-gen s r s' e tnat = refl
sub-ren-gen s r s' e tze = refl
sub-ren-gen s r s' e (tsc t) = Eq-cong tsc (sub-ren-gen s r s' e t)
sub-ren-gen s r s' e (trec C z u n) =
  cong4 trec (sub-ren-gen s r s' e C) (sub-ren-gen s r s' e z)
             (sub-ren-gen s r s' e u) (sub-ren-gen s r s' e n)
sub-ren-gen s r s' e tV = refl
sub-ren-gen s r s' e (tU f g) = cong2 tU (sub-ren-gen s r s' e f) (sub-ren-gen s r s' e g)

ren-shift-comm : (r : Rn) (t : Tm) -> Eq (ren (liftR r) (shift t)) (shift (ren r t))
ren-shift-comm r t =
  Eq-trans (ren-ren-gen (liftR r) suc (\ i -> suc (r i)) (\ i -> refl) t)
           (Eq-sym (ren-ren-gen suc r (\ i -> suc (r i)) (\ i -> refl) t))

ren-sub-gen : (r : Rn) (s : Sb) (s' : Sb) -> ((i : Num) -> Eq (ren r (s i)) (s' i)) ->
              (t : Tm) -> Eq (ren r (sub s t)) (sub s' t)
ren-sub-gen r s s' e (tvar i) = e i
ren-sub-gen r s s' e (tlam b) = Eq-cong tlam (ren-sub-gen (liftR r) (liftS s) (liftS s') e' b)
  where
    e' : (i : Num) -> Eq (ren (liftR r) (liftS s i)) (liftS s' i)
    e' zero    = refl
    e' (suc i) = Eq-trans (ren-shift-comm r (s i)) (Eq-cong shift (e i))
ren-sub-gen r s s' e (tapp t u) = cong2 tapp (ren-sub-gen r s s' e t) (ren-sub-gen r s s' e u)
ren-sub-gen r s s' e (tpi A F) = cong2 tpi (ren-sub-gen r s s' e A) (ren-sub-gen r s s' e F)
ren-sub-gen r s s' e (tsig A F) = cong2 tsig (ren-sub-gen r s s' e A) (ren-sub-gen r s s' e F)
ren-sub-gen r s s' e (tpair t u) = cong2 tpair (ren-sub-gen r s s' e t) (ren-sub-gen r s s' e u)
ren-sub-gen r s s' e (tfst t) = Eq-cong tfst (ren-sub-gen r s s' e t)
ren-sub-gen r s s' e (tsnd t) = Eq-cong tsnd (ren-sub-gen r s s' e t)
ren-sub-gen r s s' e tnat = refl
ren-sub-gen r s s' e tze = refl
ren-sub-gen r s s' e (tsc t) = Eq-cong tsc (ren-sub-gen r s s' e t)
ren-sub-gen r s s' e (trec C z u n) =
  cong4 trec (ren-sub-gen r s s' e C) (ren-sub-gen r s s' e z)
             (ren-sub-gen r s s' e u) (ren-sub-gen r s s' e n)
ren-sub-gen r s s' e tV = refl
ren-sub-gen r s s' e (tU f g) = cong2 tU (ren-sub-gen r s s' e f) (ren-sub-gen r s s' e g)

sub-shift-comm : (s : Sb) (t : Tm) -> Eq (sub (liftS s) (shift t)) (shift (sub s t))
sub-shift-comm s t =
  Eq-trans (sub-ren-gen (liftS s) suc (\ i -> shift (s i)) (\ i -> refl) t)
           (Eq-sym (ren-sub-gen suc s (\ i -> shift (s i)) (\ i -> refl) t))

sub-sub-gen : (s2 s1 s : Sb) -> ((i : Num) -> Eq (sub s2 (s1 i)) (s i)) ->
              (t : Tm) -> Eq (sub s2 (sub s1 t)) (sub s t)
sub-sub-gen s2 s1 s e (tvar i) = e i
sub-sub-gen s2 s1 s e (tlam b) = Eq-cong tlam (sub-sub-gen (liftS s2) (liftS s1) (liftS s) e' b)
  where
    e' : (i : Num) -> Eq (sub (liftS s2) (liftS s1 i)) (liftS s i)
    e' zero    = refl
    e' (suc i) = Eq-trans (sub-shift-comm s2 (s1 i)) (Eq-cong shift (e i))
sub-sub-gen s2 s1 s e (tapp t u) = cong2 tapp (sub-sub-gen s2 s1 s e t) (sub-sub-gen s2 s1 s e u)
sub-sub-gen s2 s1 s e (tpi A F) = cong2 tpi (sub-sub-gen s2 s1 s e A) (sub-sub-gen s2 s1 s e F)
sub-sub-gen s2 s1 s e (tsig A F) = cong2 tsig (sub-sub-gen s2 s1 s e A) (sub-sub-gen s2 s1 s e F)
sub-sub-gen s2 s1 s e (tpair t u) = cong2 tpair (sub-sub-gen s2 s1 s e t) (sub-sub-gen s2 s1 s e u)
sub-sub-gen s2 s1 s e (tfst t) = Eq-cong tfst (sub-sub-gen s2 s1 s e t)
sub-sub-gen s2 s1 s e (tsnd t) = Eq-cong tsnd (sub-sub-gen s2 s1 s e t)
sub-sub-gen s2 s1 s e tnat = refl
sub-sub-gen s2 s1 s e tze = refl
sub-sub-gen s2 s1 s e (tsc t) = Eq-cong tsc (sub-sub-gen s2 s1 s e t)
sub-sub-gen s2 s1 s e (trec C z u n) =
  cong4 trec (sub-sub-gen s2 s1 s e C) (sub-sub-gen s2 s1 s e z)
             (sub-sub-gen s2 s1 s e u) (sub-sub-gen s2 s1 s e n)
sub-sub-gen s2 s1 s e tV = refl
sub-sub-gen s2 s1 s e (tU f g) = cong2 tU (sub-sub-gen s2 s1 s e f) (sub-sub-gen s2 s1 s e g)

liftS-ext : (s s' : Sb) -> ((i : Num) -> Eq (s i) (s' i)) -> (i : Num) -> Eq (liftS s i) (liftS s' i)
liftS-ext s s' e zero    = refl
liftS-ext s s' e (suc i) = Eq-cong shift (e i)

sub-ext : (s s' : Sb) -> ((i : Num) -> Eq (s i) (s' i)) -> (t : Tm) -> Eq (sub s t) (sub s' t)
sub-ext s s' e t = Eq-trans (Eq-sym (sub-sub-gen s tvar s (\ i -> refl) t))
                            (sub-sub-gen s tvar s' e t)

-- the identity substitution
sub-id-gen : (s : Sb) -> ((i : Num) -> Eq (s i) (tvar i)) -> (t : Tm) -> Eq (sub s t) t
sub-id-gen s e (tvar i) = e i
sub-id-gen s e (tlam b) = Eq-cong tlam (sub-id-gen (liftS s) e' b)
  where
    e' : (i : Num) -> Eq (liftS s i) (tvar i)
    e' zero    = refl
    e' (suc i) = Eq-cong shift (e i)
sub-id-gen s e (tapp t u) = cong2 tapp (sub-id-gen s e t) (sub-id-gen s e u)
sub-id-gen s e (tpi A F) = cong2 tpi (sub-id-gen s e A) (sub-id-gen s e F)
sub-id-gen s e (tsig A F) = cong2 tsig (sub-id-gen s e A) (sub-id-gen s e F)
sub-id-gen s e (tpair t u) = cong2 tpair (sub-id-gen s e t) (sub-id-gen s e u)
sub-id-gen s e (tfst t) = Eq-cong tfst (sub-id-gen s e t)
sub-id-gen s e (tsnd t) = Eq-cong tsnd (sub-id-gen s e t)
sub-id-gen s e tnat = refl
sub-id-gen s e tze = refl
sub-id-gen s e (tsc t) = Eq-cong tsc (sub-id-gen s e t)
sub-id-gen s e (trec C z u n) =
  cong4 trec (sub-id-gen s e C) (sub-id-gen s e z) (sub-id-gen s e u) (sub-id-gen s e n)
sub-id-gen s e tV = refl
sub-id-gen s e (tU f g) = cong2 tU (sub-id-gen s e f) (sub-id-gen s e g)

-- shift then instantiate cancels
inst-shift : (t a : Tm) -> Eq (inst (shift t) a) t
inst-shift t a = Eq-trans (sub-ren-gen (sub0 a) suc tvar (\ i -> refl) t) (sub-id-gen tvar (\ i -> refl) t)

-- substitution commutes with instantiation:  (lift s b)[s a] = s (b[a])
sub-inst : (s : Sb) (b a : Tm) -> Eq (sub s (inst b a)) (inst (sub (liftS s) b) (sub s a))
sub-inst s b a =
  Eq-trans (sub-sub-gen s (sub0 a) s0 e b)
           (Eq-sym (sub-sub-gen (sub0 (sub s a)) (liftS s) s0 e' b))
  where
    s0 : Sb
    s0 zero    = sub s a
    s0 (suc i) = s i
    e : (i : Num) -> Eq (sub s (sub0 a i)) (s0 i)
    e zero    = refl
    e (suc i) = refl
    e' : (i : Num) -> Eq (sub (sub0 (sub s a)) (liftS s i)) (s0 i)
    e' zero    = refl
    e' (suc i) = inst-shift (s i) (sub s a)

-- renaming as substitution
ren-as-sub : (r : Rn) (t : Tm) -> Eq (ren r t) (sub (\ i -> tvar (r i)) t)
ren-as-sub r t =
  Eq-trans (Eq-sym (sub-id-gen tvar (\ i -> refl) (ren r t)))
           (sub-ren-gen tvar r (\ i -> tvar (r i)) (\ i -> refl) t)

-- renaming commutes with instantiation
ren-inst : (r : Rn) (b a : Tm) -> Eq (ren r (inst b a)) (inst (ren (liftR r) b) (ren r a))
ren-inst r b a =
  Eq-trans (ren-sub-gen r (sub0 a) s0 e b)
           (Eq-sym (sub-ren-gen (sub0 (ren r a)) (liftR r) s0 e' b))
  where
    s0 : Sb
    s0 zero    = ren r a
    s0 (suc i) = tvar (r i)
    e : (i : Num) -> Eq (ren r (sub0 a i)) (s0 i)
    e zero    = refl
    e (suc i) = refl
    e' : (i : Num) -> Eq (sub0 (ren r a) (liftR r i)) (s0 i)
    e' zero    = refl
    e' (suc i) = refl
