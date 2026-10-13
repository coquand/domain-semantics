{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOALG/Shape.agda
--
-- Shapes and values for completeness:
--   * the identity environment idE (variables to variables);
--   * reduction of a term with a weak-head shape keeps the shape, and
--     the value decomposes along it;
--   * a syntactic weak-head normal form (NoRed) denotes a weak-head
--     normal form, and its syntactic shape is read off den;
--   * sizes: lp (lambda and pair nodes) and sz, invariant under shift.
------------------------------------------------------------------------

module MAHLOALG.Shape where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Concrete.Tm
open import MAHLO.Concrete.Red
open import MAHLO.Concrete.Values
open import MAHLO.Concrete.Den
open import MAHLO.Concrete.Std
open import MAHLOINJ.Valid.HeadRed

------------------------------------------------------------------------
-- the identity environment
------------------------------------------------------------------------

f2n : {n : Num} -> Fin n -> Num
f2n fzero = zero
f2n (fsuc i) = suc (f2n i)

f2n-inj : {n : Num} {i j : Fin n} -> Eq (f2n i) (f2n j) -> Eq i j
f2n-inj {i = fzero} {fzero} e = refl
f2n-inj {i = fzero} {fsuc j} ()
f2n-inj {i = fsuc i} {fzero} ()
f2n-inj {i = fsuc i} {fsuc j} e = Eq-cong fsuc (f2n-inj (sucInj e))
  where
    sucInj : {a b : Num} -> Eq (suc a) (suc b) -> Eq a b
    sucInj refl = refl

idE : {n : Num} -> TEnv n
idE i = tvar (f2n i)

up-idE : {n : Num} -> PW (up (idE {n})) idE
up-idE fzero = refl
up-idE (fsuc i) = refl

denU : {n : Num} (b : Expr (suc n)) -> Eq (den b (up idE)) (den b idE)
denU b = den-ext up-idE b

------------------------------------------------------------------------
-- weak-head neutrals are stable under reduction
------------------------------------------------------------------------

wne-step : {a b : Tm} -> WNe a -> Step a b -> WNe b
wne-step wn-var ()
wne-step (wn-app ()) s-beta
wne-step (wn-app n) (s-app1 s) = wn-app (wne-step n s)
wne-step (wn-app n) (s-app2 s) = wn-app n
wne-step (wn-fst ()) s-fstp
wne-step (wn-fst n) (s-fst s) = wn-fst (wne-step n s)
wne-step (wn-snd ()) s-sndp
wne-step (wn-snd n) (s-snd s) = wn-snd (wne-step n s)
wne-step (wn-rec ()) s-rec0
wne-step (wn-rec ()) s-recS
wne-step (wn-rec n) (s-rec1 s) = wn-rec n
wne-step (wn-rec n) (s-rec2 s) = wn-rec n
wne-step (wn-rec n) (s-rec3 s) = wn-rec n
wne-step (wn-rec n) (s-rec4 s) = wn-rec (wne-step n s)

------------------------------------------------------------------------
-- inversion of reductions along shapes
------------------------------------------------------------------------

red-lam : {x v : Tm} -> Red (tlam x) v -> Sg Tm (\ y -> Eq v (tlam y) * Red x y)
red-lam r-refl = _ , (refl , r-refl)
red-lam (r-step (s-lam s) r) = let k = red-lam r in fst k , (fst (snd k) , r-step s (snd (snd k)))

Red2 : Tm -> Tm -> Tm -> Tm -> Set
Red2 a b a' b' = Red a a' * Red b b'

red-pair : {x y v : Tm} -> Red (tpair x y) v -> Sg Tm (\ x' -> Sg Tm (\ y' -> Eq v (tpair x' y') * Red2 x y x' y'))
red-pair r-refl = _ , (_ , (refl , (r-refl , r-refl)))
red-pair (r-step (s-pair1 s) r) = let k = red-pair r in _ , (_ , (fst (snd (snd k)) , (r-step s (fst (snd (snd (snd k)))) , snd (snd (snd (snd k))))))
red-pair (r-step (s-pair2 s) r) = let k = red-pair r in _ , (_ , (fst (snd (snd k)) , (fst (snd (snd (snd k))) , r-step s (snd (snd (snd (snd k)))))))

red-pi : {x y v : Tm} -> Red (tpi x y) v -> Sg Tm (\ x' -> Sg Tm (\ y' -> Eq v (tpi x' y') * Red2 x y x' y'))
red-pi r-refl = _ , (_ , (refl , (r-refl , r-refl)))
red-pi (r-step (s-pi1 s) r) = let k = red-pi r in _ , (_ , (fst (snd (snd k)) , (r-step s (fst (snd (snd (snd k)))) , snd (snd (snd (snd k))))))
red-pi (r-step (s-pi2 s) r) = let k = red-pi r in _ , (_ , (fst (snd (snd k)) , (fst (snd (snd (snd k))) , r-step s (snd (snd (snd (snd k)))))))

red-sig : {x y v : Tm} -> Red (tsig x y) v -> Sg Tm (\ x' -> Sg Tm (\ y' -> Eq v (tsig x' y') * Red2 x y x' y'))
red-sig r-refl = _ , (_ , (refl , (r-refl , r-refl)))
red-sig (r-step (s-sig1 s) r) = let k = red-sig r in _ , (_ , (fst (snd (snd k)) , (r-step s (fst (snd (snd (snd k)))) , snd (snd (snd (snd k))))))
red-sig (r-step (s-sig2 s) r) = let k = red-sig r in _ , (_ , (fst (snd (snd k)) , (fst (snd (snd (snd k))) , r-step s (snd (snd (snd (snd k)))))))

red-U : {x y v : Tm} -> Red (tU x y) v -> Sg Tm (\ x' -> Sg Tm (\ y' -> Eq v (tU x' y') * Red2 x y x' y'))
red-U r-refl = _ , (_ , (refl , (r-refl , r-refl)))
red-U (r-step (s-U1 s) r) = let k = red-U r in _ , (_ , (fst (snd (snd k)) , (r-step s (fst (snd (snd (snd k)))) , snd (snd (snd (snd k))))))
red-U (r-step (s-U2 s) r) = let k = red-U r in _ , (_ , (fst (snd (snd k)) , (fst (snd (snd (snd k))) , r-step s (snd (snd (snd (snd k)))))))

red-sc : {x v : Tm} -> Red (tsc x) v -> Sg Tm (\ y -> Eq v (tsc y) * Red x y)
red-sc r-refl = _ , (refl , r-refl)
red-sc (r-step (s-sc s) r) = let k = red-sc r in fst k , (fst (snd k) , r-step s (snd (snd k)))

data Const : Tm -> Set where
  nat-c : Const tnat
  ze-c  : Const tze
  V-c   : Const tV

red-const : {a v : Tm} -> Const a -> Red a v -> Eq v a
red-const nat-c r-refl = refl
red-const ze-c r-refl = refl
red-const V-c r-refl = refl
red-const nat-c (r-step () r)
red-const ze-c (r-step () r)
red-const V-c (r-step () r)

-- neutral spines
red-app : {t u v : Tm} -> WNe t -> Red (tapp t u) v ->
  Sg Tm (\ t' -> Sg Tm (\ u' -> Eq v (tapp t' u') * Red2 t u t' u'))
red-app n r-refl = _ , (_ , (refl , (r-refl , r-refl)))
red-app () (r-step s-beta r)
red-app n (r-step (s-app1 s) r) =
  let k = red-app (wne-step n s) r in _ , (_ , (fst (snd (snd k)) , (r-step s (fst (snd (snd (snd k)))) , snd (snd (snd (snd k))))))
red-app n (r-step (s-app2 s) r) =
  let k = red-app n r in _ , (_ , (fst (snd (snd k)) , (fst (snd (snd (snd k))) , r-step s (snd (snd (snd (snd k)))))))

red-fst : {t v : Tm} -> WNe t -> Red (tfst t) v -> Sg Tm (\ t' -> Eq v (tfst t') * Red t t')
red-fst n r-refl = _ , (refl , r-refl)
red-fst () (r-step s-fstp r)
red-fst n (r-step (s-fst s) r) = let k = red-fst (wne-step n s) r in fst k , (fst (snd k) , r-step s (snd (snd k)))

red-snd : {t v : Tm} -> WNe t -> Red (tsnd t) v -> Sg Tm (\ t' -> Eq v (tsnd t') * Red t t')
red-snd n r-refl = _ , (refl , r-refl)
red-snd () (r-step s-sndp r)
red-snd n (r-step (s-snd s) r) = let k = red-snd (wne-step n s) r in fst k , (fst (snd k) , r-step s (snd (snd k)))

record RecRed (C z s k v : Tm) : Set where
  constructor recred
  field
    C' z' s' k' : Tm
    ev : Eq v (trec C' z' s' k')
    rC : Red C C'
    rz : Red z z'
    rs : Red s s'
    rk : Red k k'

red-rec : {C z s k v : Tm} -> WNe k -> Red (trec C z s k) v -> RecRed C z s k v
red-rec n r-refl = recred _ _ _ _ refl r-refl r-refl r-refl r-refl
red-rec () (r-step s-rec0 r)
red-rec () (r-step s-recS r)
red-rec n (r-step (s-rec1 x) r) = let k = red-rec n r ; open RecRed k in recred C' z' s' k' ev (r-step x rC) rz rs rk
red-rec n (r-step (s-rec2 x) r) = let k = red-rec n r ; open RecRed k in recred C' z' s' k' ev rC (r-step x rz) rs rk
red-rec n (r-step (s-rec3 x) r) = let k = red-rec n r ; open RecRed k in recred C' z' s' k' ev rC rz (r-step x rs) rk
red-rec n (r-step (s-rec4 x) r) = let k = red-rec (wne-step n x) r ; open RecRed k in recred C' z' s' k' ev rC rz rs (r-step x rk)

------------------------------------------------------------------------
-- syntactic weak-head normal forms
------------------------------------------------------------------------

data SNe {n : Num} : Expr n -> Set where
  sne-var : {i : Fin n} -> SNe (Var i)
  sne-app : {u v : Expr n} -> SNe u -> SNe (App u v)
  sne-fst : {u : Expr n} -> SNe u -> SNe (Fst u)
  sne-snd : {u : Expr n} -> SNe u -> SNe (Snd u)
  sne-rec : {C z s k : Expr n} -> SNe k -> SNe (Rec C z s k)

data SynSh {n : Num} : Expr n -> Set where
  sh-ne   : {w : Expr n} -> SNe w -> SynSh w
  sh-lam  : {A : Expr n} {b : Expr (suc n)} -> SynSh (Lam A b)
  sh-pair : {a b : Expr n} -> SynSh (Pair a b)
  sh-pi   : {A F : Expr n} -> SynSh (Pi A F)
  sh-sig  : {A F : Expr n} -> SynSh (Sigma A F)
  sh-nat  : SynSh Nat
  sh-ze   : SynSh Zero
  sh-sc   : {k : Expr n} -> SynSh (Suc k)
  sh-V    : SynSh V
  sh-U    : {f g : Expr n} -> SynSh (Ucode f g)

wneSyn : {n : Num} (t : Expr n) -> NoRed t -> WNe (den t idE) -> SNe t
wneSyn (Var i) nr n = sne-var
wneSyn (App t u) nr (wn-app n) = sne-app (wneSyn t (\ r -> nr (hr-app r)) n)
wneSyn (Fst t) nr (wn-fst n) = sne-fst (wneSyn t (\ r -> nr (hr-fst r)) n)
wneSyn (Snd t) nr (wn-snd n) = sne-snd (wneSyn t (\ r -> nr (hr-snd r)) n)
wneSyn (Rec C z s k) nr (wn-rec n) = sne-rec (wneSyn k (\ r -> nr (hr-rec r)) n)
wneSyn (Fhat f g A F) nr n = Empty-elim (nr hr-fhat)
wneSyn (Ghat f g A F c) nr n = Empty-elim (nr hr-ghat)

synSh : {n : Num} (w : Expr n) -> NoRed w -> WShape (den w idE) -> SynSh w
synSh (Var i) nr sh = sh-ne sne-var
synSh (Lam A b) nr sh = sh-lam
synSh (App t u) nr (ws-ne n) = sh-ne (wneSyn (App t u) nr n)
synSh (Pi A F) nr sh = sh-pi
synSh (Sigma A F) nr sh = sh-sig
synSh (Pair a b) nr sh = sh-pair
synSh (Fst t) nr (ws-ne n) = sh-ne (wneSyn (Fst t) nr n)
synSh (Snd t) nr (ws-ne n) = sh-ne (wneSyn (Snd t) nr n)
synSh Nat nr sh = sh-nat
synSh Zero nr sh = sh-ze
synSh (Suc k) nr sh = sh-sc
synSh (Rec C z s k) nr (ws-ne n) = sh-ne (wneSyn (Rec C z s k) nr n)
synSh V nr sh = sh-V
synSh (Ucode f g) nr sh = sh-U
synSh (Fhat f g A F) nr sh = Empty-elim (nr hr-fhat)
synSh (Ghat f g A F c) nr sh = Empty-elim (nr hr-ghat)

------------------------------------------------------------------------
-- a syntactic weak-head normal form denotes one
------------------------------------------------------------------------

private
  whApp : {a u b : Tm} -> Wh (tapp a u) b -> Sg Tm (\ x -> Eq a (tlam x)) + Sg Tm (\ a' -> Wh a a')
  whApp wh-beta = inl (_ , refl)
  whApp (wh-app w) = inr (_ , w)

  whFst : {a b : Tm} -> Wh (tfst a) b -> Sg Tm (\ x -> Sg Tm (\ y -> Eq a (tpair x y))) + Sg Tm (\ a' -> Wh a a')
  whFst wh-fstp = inl (_ , (_ , refl))
  whFst (wh-fst w) = inr (_ , w)

  whSnd : {a b : Tm} -> Wh (tsnd a) b -> Sg Tm (\ x -> Sg Tm (\ y -> Eq a (tpair x y))) + Sg Tm (\ a' -> Wh a a')
  whSnd wh-sndp = inl (_ , (_ , refl))
  whSnd (wh-snd w) = inr (_ , w)

  whRec : {C z s k b : Tm} -> Wh (trec C z s k) b ->
    Eq k tze + (Sg Tm (\ m -> Eq k (tsc m)) + Sg Tm (\ k' -> Wh k k'))
  whRec wh-rec0 = inl refl
  whRec wh-recS = inr (inl (_ , refl))
  whRec (wh-rec w) = inr (inr (_ , w))

  denLam : {n : Num} (t : Expr n) {x : Tm} -> Eq (den t idE) (tlam x) ->
    Sg (Expr n) (\ A -> Sg (Expr (suc n)) (\ b -> Eq t (Lam A b)))
  denLam (Lam A b) e = A , (b , refl)
  denLam (Var i) ()
  denLam (App _ _) ()
  denLam (Pi _ _) ()
  denLam (Sigma _ _) ()
  denLam (Pair _ _) ()
  denLam (Fst _) ()
  denLam (Snd _) ()
  denLam Nat ()
  denLam Zero ()
  denLam (Suc _) ()
  denLam (Rec _ _ _ _) ()
  denLam V ()
  denLam (Ucode _ _) ()
  denLam (Fhat _ _ _ _) ()
  denLam (Ghat _ _ _ _ _) ()

  denPair : {n : Num} (t : Expr n) {x y : Tm} -> Eq (den t idE) (tpair x y) ->
    Sg (Expr n) (\ a -> Sg (Expr n) (\ b -> Eq t (Pair a b)))
  denPair (Pair a b) e = a , (b , refl)
  denPair (Var i) ()
  denPair (App _ _) ()
  denPair (Pi _ _) ()
  denPair (Sigma _ _) ()
  denPair (Lam _ _) ()
  denPair (Fst _) ()
  denPair (Snd _) ()
  denPair Nat ()
  denPair Zero ()
  denPair (Suc _) ()
  denPair (Rec _ _ _ _) ()
  denPair V ()
  denPair (Ucode _ _) ()
  denPair (Fhat _ _ _ _) ()
  denPair (Ghat _ _ _ _ _) ()

  denZe : {n : Num} (t : Expr n) -> Eq (den t idE) tze -> Eq t Zero
  denZe Zero e = refl
  denZe (Var i) ()
  denZe (App _ _) ()
  denZe (Pi _ _) ()
  denZe (Sigma _ _) ()
  denZe (Lam _ _) ()
  denZe (Pair _ _) ()
  denZe (Fst _) ()
  denZe (Snd _) ()
  denZe Nat ()
  denZe (Suc _) ()
  denZe (Rec _ _ _ _) ()
  denZe V ()
  denZe (Ucode _ _) ()
  denZe (Fhat _ _ _ _) ()
  denZe (Ghat _ _ _ _ _) ()

  denSc : {n : Num} (t : Expr n) {m : Tm} -> Eq (den t idE) (tsc m) -> Sg (Expr n) (\ k -> Eq t (Suc k))
  denSc (Suc k) e = k , refl
  denSc (Var i) ()
  denSc (App _ _) ()
  denSc (Pi _ _) ()
  denSc (Sigma _ _) ()
  denSc (Lam _ _) ()
  denSc (Pair _ _) ()
  denSc (Fst _) ()
  denSc (Snd _) ()
  denSc Nat ()
  denSc Zero ()
  denSc (Rec _ _ _ _) ()
  denSc V ()
  denSc (Ucode _ _) ()
  denSc (Fhat _ _ _ _) ()
  denSc (Ghat _ _ _ _ _) ()

nfDen : {n : Num} (w : Expr n) -> NoRed w -> WhNF (den w idE)
nfDen (App t u) nr w = go (whApp w)
  where
    go : _ -> Empty
    go (inl (x , e)) = let d = denLam t e in nr (snd (transport (\ X -> Sg (Expr _) (\ y -> HR (App X u) y)) (Eq-sym (snd (snd d))) (_ , hr-beta)))
    go (inr (a' , w')) = nfDen t (\ r -> nr (hr-app r)) w'
nfDen (Fst t) nr w = go (whFst w)
  where
    go : _ -> Empty
    go (inl (x , (y , e))) = let d = denPair t e in nr (snd (transport (\ X -> Sg (Expr _) (\ y -> HR (Fst X) y)) (Eq-sym (snd (snd d))) (_ , hr-fst-pair)))
    go (inr (a' , w')) = nfDen t (\ r -> nr (hr-fst r)) w'
nfDen (Snd t) nr w = go (whSnd w)
  where
    go : _ -> Empty
    go (inl (x , (y , e))) = let d = denPair t e in nr (snd (transport (\ X -> Sg (Expr _) (\ y -> HR (Snd X) y)) (Eq-sym (snd (snd d))) (_ , hr-snd-pair)))
    go (inr (a' , w')) = nfDen t (\ r -> nr (hr-snd r)) w'
nfDen (Rec C z s k) nr w = go (whRec w)
  where
    go : _ -> Empty
    go (inl e) = nr (snd (transport (\ X -> Sg (Expr _) (\ y -> HR (Rec C z s X) y)) (Eq-sym (denZe k e)) (_ , hr-rec-zero)))
    go (inr (inl (m , e))) = let d = denSc k e in nr (snd (transport (\ X -> Sg (Expr _) (\ y -> HR (Rec C z s X) y)) (Eq-sym (snd d)) (_ , hr-rec-suc)))
    go (inr (inr (k' , w'))) = nfDen k (\ r -> nr (hr-rec r)) w'
nfDen (Fhat f g A F) nr w = nr hr-fhat
nfDen (Ghat f g A F c) nr w = nr hr-ghat
nfDen (Var i) nr ()
nfDen (Lam A b) nr ()
nfDen (Pi A F) nr ()
nfDen (Sigma A F) nr ()
nfDen (Pair a b) nr ()
nfDen Nat nr ()
nfDen Zero nr ()
nfDen (Suc k) nr ()
nfDen V nr ()
nfDen (Ucode f g) nr ()
