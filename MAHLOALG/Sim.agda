{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOALG/Sim.agda
--
-- (b) Simulation of the syntactic weak-head reduction HR (beta, pi,
-- iota, delta; Valid/HeadRed) by the weak-head reduction Wh of the
-- concrete model (Concrete/Std), through den:
--   * a beta/pi/iota step of HR is a Wh step of den;
--   * a delta step leaves den unchanged and lowers the number of
--     fhat/ghat on the head spine (hd) by one.
-- Hence: if den t weak-head normalises (to a shape), then the
-- syntactic weak-head reduction of t terminates (synWN).
------------------------------------------------------------------------

module MAHLOALG.Sim where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Concrete.Tm
open import MAHLO.Concrete.Red
open import MAHLO.Concrete.Den
open import MAHLO.Concrete.Std
open import MAHLOINJ.Valid.HeadRed

------------------------------------------------------------------------
-- fhat/ghat on the head spine
------------------------------------------------------------------------

hd : {n : Num} -> Expr n -> Num
hd (App t u) = hd t
hd (Fst t) = hd t
hd (Snd t) = hd t
hd (Rec C z s k) = hd k
hd (Fhat f g A F) = suc (hd f)
hd (Ghat f g A F c) = suc (hd g)
hd (Var _) = zero
hd (Lam _ _) = zero
hd (Pi _ _) = zero
hd (Sigma _ _) = zero
hd (Pair _ _) = zero
hd Nat = zero
hd Zero = zero
hd (Suc _) = zero
hd V = zero
hd (Ucode _ _) = zero

------------------------------------------------------------------------
-- one step
------------------------------------------------------------------------

private
  -- den of a substitution instance
  denInst : {n : Num} (rho : TEnv n) (b : Expr (suc n)) (a : Expr n) ->
    Eq (inst (den b (up rho)) (den a rho)) (den (subst1 b a) rho)
  denInst rho b a =
    Eq-trans (sub-den (sub0 (den a rho)) (up rho) b)
      (Eq-trans (den-ext e b) (Eq-sym (den-subE (subst1Sub a) rho b)))
    where
      e : PW (\ i -> sub (sub0 (den a rho)) (up rho i)) (\ i -> den (subst1Sub a i) rho)
      e fzero = refl
      e (fsuc i) = inst-shift (rho i) (den a rho)

DStep : {n : Num} -> TEnv n -> Expr n -> Expr n -> Set
DStep rho t t1 = Wh (den t rho) (den t1 rho) + (Eq (den t rho) (den t1 rho) * Eq (hd t) (suc (hd t1)))

hrDen : {n : Num} (rho : TEnv n) {t t1 : Expr n} -> HR t t1 -> DStep rho t t1
hrDen rho (hr-beta {A} {a} {t}) = inl (transport (Wh _) (denInst rho t a) wh-beta)
hrDen rho (hr-app r) = go (hrDen rho r)
  where
    go : _ -> _
    go (inl w) = inl (wh-app w)
    go (inr (e , h)) = inr (Eq-cong (\ x -> tapp x _) e , h)
hrDen rho hr-fst-pair = inl wh-fstp
hrDen rho hr-snd-pair = inl wh-sndp
hrDen rho (hr-fst r) = go (hrDen rho r)
  where
    go : _ -> _
    go (inl w) = inl (wh-fst w)
    go (inr (e , h)) = inr (Eq-cong tfst e , h)
hrDen rho (hr-snd r) = go (hrDen rho r)
  where
    go : _ -> _
    go (inl w) = inl (wh-snd w)
    go (inr (e , h)) = inr (Eq-cong tsnd e , h)
hrDen rho hr-rec-zero = inl wh-rec0
hrDen rho hr-rec-suc = inl wh-recS
hrDen rho (hr-rec r) = go (hrDen rho r)
  where
    go : _ -> _
    go (inl w) = inl (wh-rec w)
    go (inr (e , h)) = inr (Eq-cong (trec _ _ _) e , h)
hrDen rho hr-fhat = inr (refl , refl)
hrDen rho hr-ghat = inr (refl , refl)

-- den of a syntactic weak-head reduction is a reduction
hrsRed : {n : Num} (rho : TEnv n) {t w : Expr n} -> HRs t w -> Red (den t rho) (den w rho)
hrsRed rho hrs-refl = r-refl
hrsRed rho (hrs-step r rs) = go (hrDen rho r)
  where
    go : _ -> _
    go (inl w) = r-step (whStep w) (hrsRed rho rs)
      where
        whStep : {a b : Tm} -> Wh a b -> Step a b
        whStep wh-beta = s-beta
        whStep (wh-app x) = s-app1 (whStep x)
        whStep wh-fstp = s-fstp
        whStep wh-sndp = s-sndp
        whStep (wh-fst x) = s-fst (whStep x)
        whStep (wh-snd x) = s-snd (whStep x)
        whStep wh-rec0 = s-rec0
        whStep wh-recS = s-recS
        whStep (wh-rec x) = s-rec4 (whStep x)
    go (inr (e , h)) = transport (\ x -> Red x _) (Eq-sym e) (hrsRed rho rs)

------------------------------------------------------------------------
-- a syntactic step, or weak-head normal
------------------------------------------------------------------------

-- views
private
  data LamV {n : Num} : Expr n -> Set where
    isLam : {A : Expr n} {b : Expr (suc n)} -> LamV (Lam A b)
    notLam : {t : Expr n} -> ({A : Expr n} {b : Expr (suc n)} -> Eq t (Lam A b) -> Empty) -> LamV t

  lamV : {n : Num} (t : Expr n) -> LamV t
  lamV (Lam A b) = isLam
  lamV (Var i) = notLam (\ ())
  lamV (App _ _) = notLam (\ ())
  lamV (Pi _ _) = notLam (\ ())
  lamV (Sigma _ _) = notLam (\ ())
  lamV (Pair _ _) = notLam (\ ())
  lamV (Fst _) = notLam (\ ())
  lamV (Snd _) = notLam (\ ())
  lamV Nat = notLam (\ ())
  lamV Zero = notLam (\ ())
  lamV (Suc _) = notLam (\ ())
  lamV (Rec _ _ _ _) = notLam (\ ())
  lamV V = notLam (\ ())
  lamV (Ucode _ _) = notLam (\ ())
  lamV (Fhat _ _ _ _) = notLam (\ ())
  lamV (Ghat _ _ _ _ _) = notLam (\ ())

  data PairV {n : Num} : Expr n -> Set where
    isPair : {a b : Expr n} -> PairV (Pair a b)
    notPair : {t : Expr n} -> ({a b : Expr n} -> Eq t (Pair a b) -> Empty) -> PairV t

  pairV : {n : Num} (t : Expr n) -> PairV t
  pairV (Pair a b) = isPair
  pairV (Var i) = notPair (\ ())
  pairV (App _ _) = notPair (\ ())
  pairV (Pi _ _) = notPair (\ ())
  pairV (Sigma _ _) = notPair (\ ())
  pairV (Lam _ _) = notPair (\ ())
  pairV (Fst _) = notPair (\ ())
  pairV (Snd _) = notPair (\ ())
  pairV Nat = notPair (\ ())
  pairV Zero = notPair (\ ())
  pairV (Suc _) = notPair (\ ())
  pairV (Rec _ _ _ _) = notPair (\ ())
  pairV V = notPair (\ ())
  pairV (Ucode _ _) = notPair (\ ())
  pairV (Fhat _ _ _ _) = notPair (\ ())
  pairV (Ghat _ _ _ _ _) = notPair (\ ())

  data NumV {n : Num} : Expr n -> Set where
    isZero : NumV Zero
    isSuc : {k : Expr n} -> NumV (Suc k)
    notNum : {t : Expr n} -> (Eq t Zero -> Empty) -> ({k : Expr n} -> Eq t (Suc k) -> Empty) -> NumV t

  numV : {n : Num} (t : Expr n) -> NumV t
  numV Zero = isZero
  numV (Suc k) = isSuc
  numV (Var i) = notNum (\ ()) (\ ())
  numV (App _ _) = notNum (\ ()) (\ ())
  numV (Pi _ _) = notNum (\ ()) (\ ())
  numV (Sigma _ _) = notNum (\ ()) (\ ())
  numV (Lam _ _) = notNum (\ ()) (\ ())
  numV (Pair _ _) = notNum (\ ()) (\ ())
  numV (Fst _) = notNum (\ ()) (\ ())
  numV (Snd _) = notNum (\ ()) (\ ())
  numV Nat = notNum (\ ()) (\ ())
  numV (Rec _ _ _ _) = notNum (\ ()) (\ ())
  numV V = notNum (\ ()) (\ ())
  numV (Ucode _ _) = notNum (\ ()) (\ ())
  numV (Fhat _ _ _ _) = notNum (\ ()) (\ ())
  numV (Ghat _ _ _ _ _) = notNum (\ ()) (\ ())

hrStep : {n : Num} (t : Expr n) -> Sg (Expr n) (\ t1 -> HR t t1) + NoRed t
hrStep (App t u) = app (lamV t) (hrStep t)
  where
    app : LamV t -> (Sg (Expr _) (\ x -> HR t x) + NoRed t) -> (Sg (Expr _) (\ x -> HR (App t u) x) + NoRed (App t u))
    app isLam _ = inl (_ , hr-beta)
    app (notLam nl) (inl (t1 , r)) = inl (_ , hr-app r)
    app (notLam nl) (inr nr) = inr nr'
      where
        nr' : {x : Expr _} -> HR (App t u) x -> Empty
        nr' hr-beta = nl refl
        nr' (hr-app r) = nr r
hrStep (Fst t) = pr (pairV t) (hrStep t)
  where
    pr : PairV t -> (Sg (Expr _) (\ x -> HR t x) + NoRed t) -> (Sg (Expr _) (\ x -> HR (Fst t) x) + NoRed (Fst t))
    pr isPair _ = inl (_ , hr-fst-pair)
    pr (notPair np) (inl (t1 , r)) = inl (_ , hr-fst r)
    pr (notPair np) (inr nr) = inr nr'
      where
        nr' : {x : Expr _} -> HR (Fst t) x -> Empty
        nr' hr-fst-pair = np refl
        nr' (hr-fst r) = nr r
hrStep (Snd t) = pr (pairV t) (hrStep t)
  where
    pr : PairV t -> (Sg (Expr _) (\ x -> HR t x) + NoRed t) -> (Sg (Expr _) (\ x -> HR (Snd t) x) + NoRed (Snd t))
    pr isPair _ = inl (_ , hr-snd-pair)
    pr (notPair np) (inl (t1 , r)) = inl (_ , hr-snd r)
    pr (notPair np) (inr nr) = inr nr'
      where
        nr' : {x : Expr _} -> HR (Snd t) x -> Empty
        nr' hr-snd-pair = np refl
        nr' (hr-snd r) = nr r
hrStep (Rec C z s k) = rc (numV k) (hrStep k)
  where
    rc : NumV k -> (Sg (Expr _) (\ x -> HR k x) + NoRed k) -> (Sg (Expr _) (\ x -> HR (Rec C z s k) x) + NoRed (Rec C z s k))
    rc isZero _ = inl (_ , hr-rec-zero)
    rc isSuc _ = inl (_ , hr-rec-suc)
    rc (notNum nz ns) (inl (k1 , r)) = inl (_ , hr-rec r)
    rc (notNum nz ns) (inr nr) = inr nr'
      where
        nr' : {x : Expr _} -> HR (Rec C z s k) x -> Empty
        nr' hr-rec-zero = nz refl
        nr' hr-rec-suc = ns refl
        nr' (hr-rec r) = nr r
hrStep (Fhat f g A F) = inl (_ , hr-fhat)
hrStep (Ghat f g A F c) = inl (_ , hr-ghat)
hrStep (Var i) = inr (\ ())
hrStep (Lam A b) = inr (\ ())
hrStep (Pi A F) = inr (\ ())
hrStep (Sigma A F) = inr (\ ())
hrStep (Pair a b) = inr (\ ())
hrStep Nat = inr (\ ())
hrStep Zero = inr (\ ())
hrStep (Suc k) = inr (\ ())
hrStep V = inr (\ ())
hrStep (Ucode f g) = inr (\ ())

------------------------------------------------------------------------
-- syntactic weak-head normalisation
------------------------------------------------------------------------

Wh-det : {a b c : Tm} -> Wh a b -> Wh a c -> Eq b c
Wh-det wh-beta wh-beta = refl
Wh-det wh-beta (wh-app ())
Wh-det (wh-app ()) wh-beta
Wh-det (wh-app p) (wh-app q) = Eq-cong (\ x -> tapp x _) (Wh-det p q)
Wh-det wh-fstp wh-fstp = refl
Wh-det wh-fstp (wh-fst ())
Wh-det (wh-fst ()) wh-fstp
Wh-det (wh-fst p) (wh-fst q) = Eq-cong tfst (Wh-det p q)
Wh-det wh-sndp wh-sndp = refl
Wh-det wh-sndp (wh-snd ())
Wh-det (wh-snd ()) wh-sndp
Wh-det (wh-snd p) (wh-snd q) = Eq-cong tsnd (Wh-det p q)
Wh-det wh-rec0 wh-rec0 = refl
Wh-det wh-rec0 (wh-rec ())
Wh-det wh-recS wh-recS = refl
Wh-det wh-recS (wh-rec ())
Wh-det (wh-rec ()) wh-rec0
Wh-det (wh-rec ()) wh-recS
Wh-det (wh-rec p) (wh-rec q) = Eq-cong (trec _ _ _) (Wh-det p q)

SynWN : {n : Num} -> Expr n -> Set
SynWN {n} t = Sg (Expr n) (\ w -> HRs t w * NoRed w)

private
  go : {n : Num} (rho : TEnv n) (t : Expr n) {a w : Tm} -> Whs a w -> WShape w ->
       (k : Num) -> Eq (hd t) k -> Eq a (den t rho) -> SynWN t
  go rho t {w = w} ws sh k ek ea = step (hrStep t)
    where
      step : _ -> SynWN t
      step (inr nr) = t , (hrs-refl , nr)
      step (inl (t1 , r)) = cont (hrDen rho r)
        where
          prep : SynWN t1 -> SynWN t
          prep (w' , (rs , nr)) = w' , (hrs-step r rs , nr)
          cont : DStep rho t t1 -> SynWN t
          cont (inl wh) = adv ws ea
            where
              adv : {a' : Tm} -> Whs a' w -> Eq a' (den t rho) -> SynWN t
              adv whs-refl e = Empty-elim (wshape-nf sh (transport (\ x -> Wh x _) (Eq-sym e) wh))
              adv (whs-step s rest) e =
                prep (go rho t1 rest sh (hd t1) refl (Wh-det (transport (\ x -> Wh x _) e s) wh))
          cont (inr (e , h)) = dlt k ek
            where
              dlt : (k : Num) -> Eq (hd t) k -> SynWN t
              dlt zero e0 = Empty-elim (sucZero (Eq-trans (Eq-sym h) e0))
                where
                  sucZero : {m : Num} -> Eq (suc m) zero -> Empty
                  sucZero ()
              dlt (suc k') e1 = prep (go rho t1 ws sh k' (sucInj (Eq-trans (Eq-sym h) e1)) (Eq-trans ea e))
                where
                  sucInj : {m m' : Num} -> Eq (suc m) (suc m') -> Eq m m'
                  sucInj refl = refl

-- if den t weak-head normalises to a shape, so does t syntactically
synWN : {n : Num} (rho : TEnv n) (t : Expr n) -> WS (den t rho) -> SynWN t
synWN rho t (w , (ws , sh)) = go rho t ws sh (hd t) refl refl
