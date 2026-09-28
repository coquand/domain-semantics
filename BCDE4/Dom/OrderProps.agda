{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- LeqStageProps.agda  (MIN/ — Pi + U fragment)
--
-- Per-stage properties of the stratified order: all the expected
-- properties HOLD AT STAGE n, proved by induction on n.  File 2 of 3
-- (definition = LeqStage, collapse/stability = LeqStageStable).
--
--   * decidability: isPos (lei n u v)  <->  leq n u v   (lei/lef-sound/-complete)
--   * [TODO] the big mutual property pack PropsPack n + goodProps:
--       monotonicity, refl, trans, Sup-lub/-left/-right, Comp.
--
-- NO postulates.
------------------------------------------------------------------------

module BCDE4.Dom.OrderProps where

open import BCDE4.Dom.Basic using (U0 ; EqL ; eqL ; EqL-refl ; EqL-sym ; EqL-trans ; EqL-Eq ; eqL-EqL ; EqL-eqL ; eqL-refl)

open import BCDE4.Dom.Basic
  using ( Top ; tt ; Empty
        ; Nat ; zero ; suc ; max ; min ; isPos ; min-isPos
        ; Le ; Le-refl ; Le-trans ; Le-max-l ; Le-max-r
        ; Pair ; mkSigma ; fst ; snd ; Sigma ; Eq ; refl
        ; FinEl ; Bot ; UCode ; LevTy ; LevEl ; FunEl ; PiCode ; LPiCode ; FinFun ; nil ; cons )
open import BCDE4.Dom.OrderStage

private
  isPos-min : (m k : Nat) -> isPos m -> isPos k -> isPos (min m k)
  isPos-min zero    k       () _
  isPos-min (suc m) zero    _  ()
  isPos-min (suc m) (suc k) _  _ = tt

------------------------------------------------------------------------
-- Decidability at every stage.
------------------------------------------------------------------------

mutual
  lei-sound : (n : Nat) (u v : FinEl) ->
    isPos (OB.lei n u v) -> OB.leq n u v
  -- Stage 0 (trivBundle)
  lei-sound zero    Bot          v             h = tt
  lei-sound zero    (UCode lu)        Bot           ()
  lei-sound zero    (UCode lu)        (UCode lv)         h = eqL-EqL lu lv h
  lei-sound zero    (UCode lu)        (FunEl _)     ()
  lei-sound zero    (UCode lu)        (PiCode _ _)  ()
  lei-sound zero    (FunEl _)    Bot           ()
  lei-sound zero    (FunEl _)    (UCode lu)         ()
  lei-sound zero    (FunEl _)    (FunEl _)     ()
  lei-sound zero    (FunEl _)    (PiCode _ _)  ()
  lei-sound zero    (PiCode _ _) Bot           ()
  lei-sound zero    (PiCode _ _) (UCode lu)         ()
  lei-sound zero    (PiCode _ _) (FunEl _)     ()
  lei-sound zero    (UCode _)      (LPiCode _)    ()
  lei-sound zero    LevTy          (LPiCode _)    ()
  lei-sound zero    (LevEl _)      (LPiCode _)    ()
  lei-sound zero    (FunEl _)      (LPiCode _)    ()
  lei-sound zero    (PiCode _ _)   (LPiCode _)    ()
  lei-sound zero    (LPiCode _)    Bot            ()
  lei-sound zero    (LPiCode _)    (UCode _)      ()
  lei-sound zero    (LPiCode _)    LevTy          ()
  lei-sound zero    (LPiCode _)    (LevEl _)      ()
  lei-sound zero    (LPiCode _)    (FunEl _)      ()
  lei-sound zero    (LPiCode _)    (PiCode _ _)   ()
  lei-sound zero    (LPiCode _)    (LPiCode _)    ()
  lei-sound zero    (UCode _)      LevTy          ()
  lei-sound zero    (UCode _)      (LevEl lv)     ()
  lei-sound zero    LevTy          Bot            ()
  lei-sound zero    LevTy          (UCode _)      ()
  lei-sound zero    LevTy          LevTy          h = tt
  lei-sound zero    LevTy          (LevEl lv)     ()
  lei-sound zero    LevTy          (FunEl _)      ()
  lei-sound zero    LevTy          (PiCode _ _)   ()
  lei-sound zero    (LevEl lu)     Bot            ()
  lei-sound zero    (LevEl lu)     (UCode _)      ()
  lei-sound zero    (LevEl lu)     LevTy          ()
  lei-sound zero    (LevEl lu)     (LevEl lv)     h = eqL-EqL lu lv h
  lei-sound zero    (LevEl lu)     (FunEl _)      ()
  lei-sound zero    (LevEl lu)     (PiCode _ _)   ()
  lei-sound zero    (FunEl _)      LevTy          ()
  lei-sound zero    (FunEl _)      (LevEl lv)     ()
  lei-sound zero    (PiCode _ _)   LevTy          ()
  lei-sound zero    (PiCode _ _)   (LevEl lv)     ()
  lei-sound zero    (PiCode _ _) (PiCode _ _)  ()
  -- Stage (suc n)
  lei-sound (suc n) Bot          v             h = tt
  lei-sound (suc n) (UCode lu)        Bot           ()
  lei-sound (suc n) (UCode lu)        (UCode lv)         h = eqL-EqL lu lv h
  lei-sound (suc n) (UCode lu)        (FunEl _)     ()
  lei-sound (suc n) (UCode lu)        (PiCode _ _)  ()
  lei-sound (suc n) (FunEl _)    Bot           ()
  lei-sound (suc n) (FunEl _)    (UCode lu)         ()
  lei-sound (suc n) (FunEl g)    (FunEl h)     p = lef-sound (suc n) g h p
  lei-sound (suc n) (FunEl _)    (PiCode _ _)  ()
  lei-sound (suc n) (PiCode _ _) Bot           ()
  lei-sound (suc n) (PiCode _ _) (UCode lu)         ()
  lei-sound (suc n) (PiCode _ _) (FunEl _)     ()
  lei-sound (suc n) (UCode _)      (LPiCode g)    ()
  lei-sound (suc n) LevTy          (LPiCode g)    ()
  lei-sound (suc n) (LevEl _)      (LPiCode g)    ()
  lei-sound (suc n) (FunEl _)      (LPiCode g)    ()
  lei-sound (suc n) (PiCode _ _)   (LPiCode g)    ()
  lei-sound (suc n) (LPiCode f)    Bot            ()
  lei-sound (suc n) (LPiCode f)    (UCode _)      ()
  lei-sound (suc n) (LPiCode f)    LevTy          ()
  lei-sound (suc n) (LPiCode f)    (LevEl _)      ()
  lei-sound (suc n) (LPiCode f)    (FunEl _)      ()
  lei-sound (suc n) (LPiCode f)    (PiCode _ _)   ()
  lei-sound (suc n) (LPiCode f)    (LPiCode g)    p = lef-sound (suc n) f g p
  lei-sound (suc n) (UCode _)      LevTy          ()
  lei-sound (suc n) (UCode _)      (LevEl lv)     ()
  lei-sound (suc n) LevTy          Bot            ()
  lei-sound (suc n) LevTy          (UCode _)      ()
  lei-sound (suc n) LevTy          LevTy          h = tt
  lei-sound (suc n) LevTy          (LevEl lv)     ()
  lei-sound (suc n) LevTy          (FunEl _)      ()
  lei-sound (suc n) LevTy          (PiCode _ _)   ()
  lei-sound (suc n) (LevEl lu)     Bot            ()
  lei-sound (suc n) (LevEl lu)     (UCode _)      ()
  lei-sound (suc n) (LevEl lu)     LevTy          ()
  lei-sound (suc n) (LevEl lu)     (LevEl lv)     h = eqL-EqL lu lv h
  lei-sound (suc n) (LevEl lu)     (FunEl _)      ()
  lei-sound (suc n) (LevEl lu)     (PiCode _ _)   ()
  lei-sound (suc n) (FunEl _)      LevTy          ()
  lei-sound (suc n) (FunEl _)      (LevEl lv)     ()
  lei-sound (suc n) (PiCode _ _)   LevTy          ()
  lei-sound (suc n) (PiCode _ _)   (LevEl lv)     ()
  lei-sound (suc n) (PiCode a f) (PiCode b g)  p =
    let pp = min-isPos (OB.lei n a b) (OB.lef (suc n) f g) p
    in mkSigma (lei-sound n a b (fst pp)) (lef-sound (suc n) f g (snd pp))

  lef-sound : (n : Nat) (g h : FinFun) ->
    isPos (OB.lef n g h) -> OB.leqf n g h
  lef-sound zero    nil         h p = tt
  lef-sound zero    (cons _ _)  h ()
  lef-sound (suc n) nil         h p = tt
  lef-sound (suc n) (cons p ps) h q =
    let pp = min-isPos (OB.lei n (snd p) (OB.ev (suc n) h (fst p)))
                       (OB.lef (suc n) ps h) q
    in mkSigma (lei-sound n (snd p) (OB.ev (suc n) h (fst p)) (fst pp))
               (lef-sound (suc n) ps h (snd pp))

mutual
  lei-complete : (n : Nat) (u v : FinEl) ->
    OB.leq n u v -> isPos (OB.lei n u v)
  lei-complete zero    Bot          v             h = tt
  lei-complete zero    (UCode lu)        Bot           ()
  lei-complete zero    (UCode lu)        (UCode lv)         h = EqL-eqL lu lv h
  lei-complete zero    (UCode lu)        (FunEl _)     ()
  lei-complete zero    (UCode lu)        (PiCode _ _)  ()
  lei-complete zero    (FunEl _)    Bot           ()
  lei-complete zero    (FunEl _)    (UCode lu)         ()
  lei-complete zero    (FunEl _)    (FunEl _)     ()
  lei-complete zero    (FunEl _)    (PiCode _ _)  ()
  lei-complete zero    (PiCode _ _) Bot           ()
  lei-complete zero    (PiCode _ _) (UCode lu)         ()
  lei-complete zero    (PiCode _ _) (FunEl _)     ()
  lei-complete zero    (UCode _)      (LPiCode _)    ()
  lei-complete zero    LevTy          (LPiCode _)    ()
  lei-complete zero    (LevEl _)      (LPiCode _)    ()
  lei-complete zero    (FunEl _)      (LPiCode _)    ()
  lei-complete zero    (PiCode _ _)   (LPiCode _)    ()
  lei-complete zero    (LPiCode _)    Bot            ()
  lei-complete zero    (LPiCode _)    (UCode _)      ()
  lei-complete zero    (LPiCode _)    LevTy          ()
  lei-complete zero    (LPiCode _)    (LevEl _)      ()
  lei-complete zero    (LPiCode _)    (FunEl _)      ()
  lei-complete zero    (LPiCode _)    (PiCode _ _)   ()
  lei-complete zero    (LPiCode _)    (LPiCode _)    ()
  lei-complete zero    (UCode _)      LevTy          ()
  lei-complete zero    (UCode _)      (LevEl lv)     ()
  lei-complete zero    LevTy          Bot            ()
  lei-complete zero    LevTy          (UCode _)      ()
  lei-complete zero    LevTy          LevTy          h = tt
  lei-complete zero    LevTy          (LevEl lv)     ()
  lei-complete zero    LevTy          (FunEl _)      ()
  lei-complete zero    LevTy          (PiCode _ _)   ()
  lei-complete zero    (LevEl lu)     Bot            ()
  lei-complete zero    (LevEl lu)     (UCode _)      ()
  lei-complete zero    (LevEl lu)     LevTy          ()
  lei-complete zero    (LevEl lu)     (LevEl lv)     h = EqL-eqL lu lv h
  lei-complete zero    (LevEl lu)     (FunEl _)      ()
  lei-complete zero    (LevEl lu)     (PiCode _ _)   ()
  lei-complete zero    (FunEl _)      LevTy          ()
  lei-complete zero    (FunEl _)      (LevEl lv)     ()
  lei-complete zero    (PiCode _ _)   LevTy          ()
  lei-complete zero    (PiCode _ _)   (LevEl lv)     ()
  lei-complete zero    (PiCode _ _) (PiCode _ _)  ()
  lei-complete (suc n) Bot          v             h = tt
  lei-complete (suc n) (UCode lu)        Bot           ()
  lei-complete (suc n) (UCode lu)        (UCode lv)         h = EqL-eqL lu lv h
  lei-complete (suc n) (UCode lu)        (FunEl _)     ()
  lei-complete (suc n) (UCode lu)        (PiCode _ _)  ()
  lei-complete (suc n) (FunEl _)    Bot           ()
  lei-complete (suc n) (FunEl _)    (UCode lu)         ()
  lei-complete (suc n) (FunEl g)    (FunEl h)     p = lef-complete (suc n) g h p
  lei-complete (suc n) (FunEl _)    (PiCode _ _)  ()
  lei-complete (suc n) (PiCode _ _) Bot           ()
  lei-complete (suc n) (PiCode _ _) (UCode lu)         ()
  lei-complete (suc n) (PiCode _ _) (FunEl _)     ()
  lei-complete (suc n) (UCode _)      (LPiCode g)    ()
  lei-complete (suc n) LevTy          (LPiCode g)    ()
  lei-complete (suc n) (LevEl _)      (LPiCode g)    ()
  lei-complete (suc n) (FunEl _)      (LPiCode g)    ()
  lei-complete (suc n) (PiCode _ _)   (LPiCode g)    ()
  lei-complete (suc n) (LPiCode f)    Bot            ()
  lei-complete (suc n) (LPiCode f)    (UCode _)      ()
  lei-complete (suc n) (LPiCode f)    LevTy          ()
  lei-complete (suc n) (LPiCode f)    (LevEl _)      ()
  lei-complete (suc n) (LPiCode f)    (FunEl _)      ()
  lei-complete (suc n) (LPiCode f)    (PiCode _ _)   ()
  lei-complete (suc n) (LPiCode f)    (LPiCode g)    p = lef-complete (suc n) f g p
  lei-complete (suc n) (UCode _)      LevTy          ()
  lei-complete (suc n) (UCode _)      (LevEl lv)     ()
  lei-complete (suc n) LevTy          Bot            ()
  lei-complete (suc n) LevTy          (UCode _)      ()
  lei-complete (suc n) LevTy          LevTy          h = tt
  lei-complete (suc n) LevTy          (LevEl lv)     ()
  lei-complete (suc n) LevTy          (FunEl _)      ()
  lei-complete (suc n) LevTy          (PiCode _ _)   ()
  lei-complete (suc n) (LevEl lu)     Bot            ()
  lei-complete (suc n) (LevEl lu)     (UCode _)      ()
  lei-complete (suc n) (LevEl lu)     LevTy          ()
  lei-complete (suc n) (LevEl lu)     (LevEl lv)     h = EqL-eqL lu lv h
  lei-complete (suc n) (LevEl lu)     (FunEl _)      ()
  lei-complete (suc n) (LevEl lu)     (PiCode _ _)   ()
  lei-complete (suc n) (FunEl _)      LevTy          ()
  lei-complete (suc n) (FunEl _)      (LevEl lv)     ()
  lei-complete (suc n) (PiCode _ _)   LevTy          ()
  lei-complete (suc n) (PiCode _ _)   (LevEl lv)     ()
  lei-complete (suc n) (PiCode a f) (PiCode b g)  p =
    isPos-min (OB.lei n a b) (OB.lef (suc n) f g)
      (lei-complete n a b (fst p)) (lef-complete (suc n) f g (snd p))

  lef-complete : (n : Nat) (g h : FinFun) ->
    OB.leqf n g h -> isPos (OB.lef n g h)
  lef-complete zero    nil         h p = tt
  lef-complete zero    (cons _ _)  h ()
  lef-complete (suc n) nil         h p = tt
  lef-complete (suc n) (cons p ps) h q =
    isPos-min (OB.lei n (snd p) (OB.ev (suc n) h (fst p))) (OB.lef (suc n) ps h)
      (lei-complete n (snd p) (OB.ev (suc n) h (fst p)) (fst q))
      (lef-complete (suc n) ps h (snd q))

------------------------------------------------------------------------
-- Sup-lub (self-contained: no Coherent needed).  leq (Sup a b) c when
-- a <= c and b <= c.  Mirrors PaperOrder LeCode-Sup-lub, stage-indexed.
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

leq-Sup-lub : (n : Nat) (a b c : FinEl) ->
  OB.leq n a c -> OB.leq n b c -> OB.leq n (Sup a b) c
leq-Sup-lub n Bot          b            c ac bc = bc
leq-Sup-lub n (UCode lu)        Bot          c ac bc = ac
leq-Sup-lub n (UCode lu)        (UCode lv)        c ac bc = ac
leq-Sup-lub n (UCode lu)        (FunEl _)    c ac bc = leq-Bot-any n c
leq-Sup-lub n (UCode lu)        (PiCode _ _) c ac bc = leq-Bot-any n c
leq-Sup-lub n (FunEl g)    Bot          c ac bc = ac
leq-Sup-lub n (FunEl g)    (UCode lu)        c ac bc = leq-Bot-any n c
leq-Sup-lub zero    (FunEl g) (FunEl h) c            () bc
leq-Sup-lub (suc n) (FunEl g) (FunEl h) Bot          () bc
leq-Sup-lub (suc n) (FunEl g) (FunEl h) (UCode lu)        () bc
leq-Sup-lub (suc n) (FunEl g) (FunEl h) (FunEl k)    ac bc =
  leqf-append-combine (suc n) g h k ac bc
leq-Sup-lub (suc n) (FunEl g) (FunEl h) (PiCode _ _) () bc
leq-Sup-lub (suc n) (FunEl g) (FunEl h) LevTy        () bc
leq-Sup-lub (suc n) (FunEl g) (FunEl h) (LevEl _)    () bc
leq-Sup-lub (suc n) (FunEl g) (FunEl h) (LPiCode _)  () bc
leq-Sup-lub n (FunEl g)    (PiCode _ _) c ac bc = leq-Bot-any n c
leq-Sup-lub n (PiCode a f) Bot          c ac bc = ac
leq-Sup-lub n (PiCode a f) (UCode lu)        c ac bc = leq-Bot-any n c
leq-Sup-lub n (PiCode a f) (FunEl _)    c ac bc = leq-Bot-any n c
leq-Sup-lub n (UCode _)      (LPiCode _)    c ac bc = leq-Bot-any n c
leq-Sup-lub n LevTy          (LPiCode _)    c ac bc = leq-Bot-any n c
leq-Sup-lub n (LevEl _)      (LPiCode _)    c ac bc = leq-Bot-any n c
leq-Sup-lub n (FunEl _)      (LPiCode _)    c ac bc = leq-Bot-any n c
leq-Sup-lub n (PiCode _ _)   (LPiCode _)    c ac bc = leq-Bot-any n c
leq-Sup-lub n (LPiCode _)    Bot            c ac bc = ac
leq-Sup-lub n (LPiCode _)    (UCode _)      c ac bc = leq-Bot-any n c
leq-Sup-lub n (LPiCode _)    LevTy          c ac bc = leq-Bot-any n c
leq-Sup-lub n (LPiCode _)    (LevEl _)      c ac bc = leq-Bot-any n c
leq-Sup-lub n (LPiCode _)    (FunEl _)      c ac bc = leq-Bot-any n c
leq-Sup-lub n (LPiCode _)    (PiCode _ _)   c ac bc = leq-Bot-any n c
leq-Sup-lub zero    (LPiCode f) (LPiCode g) c ()  bc
leq-Sup-lub (suc n) (LPiCode f) (LPiCode g) Bot () bc
leq-Sup-lub (suc n) (LPiCode f) (LPiCode g) (UCode _) () bc
leq-Sup-lub (suc n) (LPiCode f) (LPiCode g) LevTy () bc
leq-Sup-lub (suc n) (LPiCode f) (LPiCode g) (LevEl _) () bc
leq-Sup-lub (suc n) (LPiCode f) (LPiCode g) (FunEl _) () bc
leq-Sup-lub (suc n) (LPiCode f) (LPiCode g) (PiCode _ _) () bc
leq-Sup-lub (suc n) (LPiCode f) (LPiCode g) (LPiCode k) ac bc =
  leqf-append-combine (suc n) f g k ac bc
leq-Sup-lub n (UCode _)      LevTy          c ac bc = leq-Bot-any n c
leq-Sup-lub n (UCode _)      (LevEl _)      c ac bc = leq-Bot-any n c
leq-Sup-lub n LevTy          Bot            c ac bc = ac
leq-Sup-lub n LevTy          (UCode _)      c ac bc = leq-Bot-any n c
leq-Sup-lub n LevTy          LevTy          c ac bc = ac
leq-Sup-lub n LevTy          (LevEl _)      c ac bc = leq-Bot-any n c
leq-Sup-lub n LevTy          (FunEl _)      c ac bc = leq-Bot-any n c
leq-Sup-lub n LevTy          (PiCode _ _)   c ac bc = leq-Bot-any n c
leq-Sup-lub n (LevEl _)      Bot            c ac bc = ac
leq-Sup-lub n (LevEl _)      (UCode _)      c ac bc = leq-Bot-any n c
leq-Sup-lub n (LevEl _)      LevTy          c ac bc = leq-Bot-any n c
leq-Sup-lub n (LevEl _)      (LevEl _)      c ac bc = ac
leq-Sup-lub n (LevEl _)      (FunEl _)      c ac bc = leq-Bot-any n c
leq-Sup-lub n (LevEl _)      (PiCode _ _)   c ac bc = leq-Bot-any n c
leq-Sup-lub n (FunEl _)      LevTy          c ac bc = leq-Bot-any n c
leq-Sup-lub n (FunEl _)      (LevEl _)      c ac bc = leq-Bot-any n c
leq-Sup-lub n (PiCode _ _)   LevTy          c ac bc = leq-Bot-any n c
leq-Sup-lub n (PiCode _ _)   (LevEl _)      c ac bc = leq-Bot-any n c
leq-Sup-lub zero    (PiCode a f) (PiCode b g) c            () bc
leq-Sup-lub (suc n) (PiCode a f) (PiCode b g) Bot          ac ()
leq-Sup-lub (suc n) (PiCode a f) (PiCode b g) (UCode lu)        ac ()
leq-Sup-lub (suc n) (PiCode a f) (PiCode b g) (FunEl _)    ac ()
leq-Sup-lub (suc n) (PiCode a f) (PiCode b g) LevTy        ac ()
leq-Sup-lub (suc n) (PiCode a f) (PiCode b g) (LevEl _)    ac ()
leq-Sup-lub (suc n) (PiCode a f) (PiCode b g) (LPiCode _)  ac ()
leq-Sup-lub (suc n) (PiCode a f) (PiCode b g) (PiCode c k) ac bc =
  mkSigma (leq-Sup-lub n a b c (fst ac) (fst bc))
          (leqf-append-combine (suc n) f g k (snd ac) (snd bc))
