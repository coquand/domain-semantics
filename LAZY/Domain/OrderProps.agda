{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- LAZY/Domain/OrderProps.agda        (L1, part 2)
--
-- Per-stage facts about the stratified order: the Set-valued `leq' and
-- the numeric decision `lei' agree at every stage, and Sup is a least
-- upper bound at every stage.
--
-- Port of MIN/Domain/OrderProps.agda.
------------------------------------------------------------------------

module LAZY.Domain.OrderProps where

open import LAZY.Domain.Basic
open import LAZY.Domain.OrderStage

------------------------------------------------------------------------
-- Decidability at every stage:  isPos (lei n u v)  <->  leq n u v.
--
-- On atoms the two sides are the SAME term (leq is defined as
-- isPos of the decision), so those clauses are `h'.
------------------------------------------------------------------------

mutual
  lei-sound : (n : Nat) (u v : FinEl) ->
    isPos (OB.lei n u v) -> OB.leq n u v
  -- Stage 0
  lei-sound zero    Bot        v         h = tt
  lei-sound zero    (At a)     Bot       ()
  lei-sound zero    (At a)     (At b)    h = h
  lei-sound zero    (At a)     (Prd _ _) ()
  lei-sound zero    (At a)     (Fn _)    ()
  lei-sound zero    (Prd _ _)  Bot       ()
  lei-sound zero    (Prd _ _)  (At _)    ()
  lei-sound zero    (Prd _ _)  (Prd _ _) ()
  lei-sound zero    (Prd _ _)  (Fn _)    ()
  lei-sound zero    (Fn _)     Bot       ()
  lei-sound zero    (Fn _)     (At _)    ()
  lei-sound zero    (Fn _)     (Prd _ _) ()
  lei-sound zero    (Fn _)     (Fn _)    ()
  -- Stage (suc n)
  lei-sound (suc n) Bot        v           h = tt
  lei-sound (suc n) (At a)     Bot         ()
  lei-sound (suc n) (At a)     (At b)      h = h
  lei-sound (suc n) (At a)     (Prd _ _)   ()
  lei-sound (suc n) (At a)     (Fn _)      ()
  lei-sound (suc n) (Prd _ _)  Bot         ()
  lei-sound (suc n) (Prd _ _)  (At _)      ()
  lei-sound (suc n) (Prd u v)  (Prd u' v') p =
    let pp = min-isPos (OB.lei n u u') (OB.lei n v v') p
    in mkSigma (lei-sound n u u' (fst pp)) (lei-sound n v v' (snd pp))
  lei-sound (suc n) (Prd _ _)  (Fn _)      ()
  lei-sound (suc n) (Fn _)     Bot         ()
  lei-sound (suc n) (Fn _)     (At _)      ()
  lei-sound (suc n) (Fn _)     (Prd _ _)   ()
  lei-sound (suc n) (Fn g)     (Fn h)      p = lef-sound (suc n) g h p

  lef-sound : (n : Nat) (g h : FinFun) ->
    isPos (OB.lef n g h) -> OB.leqf n g h
  lef-sound zero    nil        h p = tt
  lef-sound zero    (cons _ _) h ()
  lef-sound (suc n) nil        h p = tt
  lef-sound (suc n) (cons p ps) h q =
    let pp = min-isPos (OB.lei n (snd p) (OB.ev (suc n) h (fst p)))
                       (OB.lef (suc n) ps h) q
    in mkSigma (lei-sound n (snd p) (OB.ev (suc n) h (fst p)) (fst pp))
               (lef-sound (suc n) ps h (snd pp))

mutual
  lei-complete : (n : Nat) (u v : FinEl) ->
    OB.leq n u v -> isPos (OB.lei n u v)
  lei-complete zero    Bot        v         h = tt
  lei-complete zero    (At a)     Bot       ()
  lei-complete zero    (At a)     (At b)    h = h
  lei-complete zero    (At a)     (Prd _ _) ()
  lei-complete zero    (At a)     (Fn _)    ()
  lei-complete zero    (Prd _ _)  Bot       ()
  lei-complete zero    (Prd _ _)  (At _)    ()
  lei-complete zero    (Prd _ _)  (Prd _ _) ()
  lei-complete zero    (Prd _ _)  (Fn _)    ()
  lei-complete zero    (Fn _)     Bot       ()
  lei-complete zero    (Fn _)     (At _)    ()
  lei-complete zero    (Fn _)     (Prd _ _) ()
  lei-complete zero    (Fn _)     (Fn _)    ()
  lei-complete (suc n) Bot        v           h = tt
  lei-complete (suc n) (At a)     Bot         ()
  lei-complete (suc n) (At a)     (At b)      h = h
  lei-complete (suc n) (At a)     (Prd _ _)   ()
  lei-complete (suc n) (At a)     (Fn _)      ()
  lei-complete (suc n) (Prd _ _)  Bot         ()
  lei-complete (suc n) (Prd _ _)  (At _)      ()
  lei-complete (suc n) (Prd u v)  (Prd u' v') p =
    isPos-min (OB.lei n u u') (OB.lei n v v')
      (lei-complete n u u' (fst p)) (lei-complete n v v' (snd p))
  lei-complete (suc n) (Prd _ _)  (Fn _)      ()
  lei-complete (suc n) (Fn _)     Bot         ()
  lei-complete (suc n) (Fn _)     (At _)      ()
  lei-complete (suc n) (Fn _)     (Prd _ _)   ()
  lei-complete (suc n) (Fn g)     (Fn h)      p = lef-complete (suc n) g h p

  lef-complete : (n : Nat) (g h : FinFun) ->
    OB.leqf n g h -> isPos (OB.lef n g h)
  lef-complete zero    nil        h p = tt
  lef-complete zero    (cons _ _) h ()
  lef-complete (suc n) nil        h p = tt
  lef-complete (suc n) (cons p ps) h q =
    isPos-min (OB.lei n (snd p) (OB.ev (suc n) h (fst p))) (OB.lef (suc n) ps h)
      (lei-complete n (snd p) (OB.ev (suc n) h (fst p)) (fst q))
      (lef-complete (suc n) ps h (snd q))

------------------------------------------------------------------------
-- Sup is a least upper bound at every stage (no Coherent needed).
------------------------------------------------------------------------

leq-Bot-any : (n : Nat) (c : FinEl) -> OB.leq n Bot c
leq-Bot-any zero    c = tt
leq-Bot-any (suc n) c = tt

-- append-combine works at any FIXED stage (pure list rearrangement).
leqf-append-combine : (n : Nat) (g h k : FinFun) ->
  OB.leqf n g k -> OB.leqf n h k -> OB.leqf n (append g h) k
leqf-append-combine zero    nil         h k gk hk = hk
leqf-append-combine zero    (cons _ _)  h k () hk
leqf-append-combine (suc n) nil         h k gk hk = hk
leqf-append-combine (suc n) (cons p ps) h k gk hk =
  mkSigma (fst gk) (leqf-append-combine (suc n) ps h k (snd gk) hk)

-- the atom join: At a ⊔ At b is At a when they agree, Bot otherwise
leq-supAt : (n : Nat) (w : Nat) (a b : Atom) (c : FinEl) ->
  OB.leq n (At a) c -> OB.leq n (supAt w a b) c
leq-supAt n zero    a b c ac = leq-Bot-any n c
leq-supAt n (suc _) a b c ac = ac

leq-Sup-lub : (n : Nat) (a b c : FinEl) ->
  OB.leq n a c -> OB.leq n b c -> OB.leq n (Sup a b) c
leq-Sup-lub n Bot       b           c ac bc = bc
leq-Sup-lub n (At a)    Bot         c ac bc = ac
leq-Sup-lub n (At a)    (At b)      c ac bc = leq-supAt n (atEqN a b) a b c ac
leq-Sup-lub n (At a)    (Prd _ _)   c ac bc = leq-Bot-any n c
leq-Sup-lub n (At a)    (Fn _)      c ac bc = leq-Bot-any n c
leq-Sup-lub n (Prd u v) Bot         c ac bc = ac
leq-Sup-lub n (Prd u v) (At b)      c ac bc = leq-Bot-any n c
leq-Sup-lub zero    (Prd u v) (Prd u' v') c           () bc
leq-Sup-lub (suc n) (Prd u v) (Prd u' v') Bot         () bc
leq-Sup-lub (suc n) (Prd u v) (Prd u' v') (At _)      () bc
leq-Sup-lub (suc n) (Prd u v) (Prd u' v') (Prd c1 c2) ac bc =
  mkSigma (leq-Sup-lub n u u' c1 (fst ac) (fst bc))
          (leq-Sup-lub n v v' c2 (snd ac) (snd bc))
leq-Sup-lub (suc n) (Prd u v) (Prd u' v') (Fn _)      () bc
leq-Sup-lub n (Prd u v) (Fn _)      c ac bc = leq-Bot-any n c
leq-Sup-lub n (Fn g)    Bot         c ac bc = ac
leq-Sup-lub n (Fn g)    (At b)      c ac bc = leq-Bot-any n c
leq-Sup-lub n (Fn g)    (Prd _ _)   c ac bc = leq-Bot-any n c
leq-Sup-lub zero    (Fn g) (Fn h) c         () bc
leq-Sup-lub (suc n) (Fn g) (Fn h) Bot       () bc
leq-Sup-lub (suc n) (Fn g) (Fn h) (At _)    () bc
leq-Sup-lub (suc n) (Fn g) (Fn h) (Prd _ _) () bc
leq-Sup-lub (suc n) (Fn g) (Fn h) (Fn k)    ac bc =
  leqf-append-combine (suc n) g h k ac bc
