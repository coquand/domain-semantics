{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- LeqStageProps.agda  (NAT/ — Pi + U fragment)
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

module NAT.Domain.OrderProps where

open import NAT.Domain.Basic
  using ( Top ; tt ; Empty
        ; Nat ; zero ; suc ; max ; min ; isPos ; min-isPos
        ; Le ; Le-refl ; Le-trans ; Le-max-l ; Le-max-r
        ; Pair ; mkSigma ; fst ; snd ; Sigma ; Eq ; refl
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; FinFun ; nil ; cons )
open import NAT.Domain.OrderStage

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
  lei-sound zero    UCode        Bot           ()
  lei-sound zero    UCode        UCode         h = tt
  lei-sound zero    UCode        (FunEl _)     ()
  lei-sound zero    UCode        (PiCode _ _)  ()
  lei-sound zero    (FunEl _)    Bot           ()
  lei-sound zero    (FunEl _)    UCode         ()
  lei-sound zero    (FunEl _)    (FunEl _)     ()
  lei-sound zero    (FunEl _)    (PiCode _ _)  ()
  lei-sound zero    (PiCode _ _) Bot           ()
  lei-sound zero    (PiCode _ _) UCode         ()
  lei-sound zero    (PiCode _ _) (FunEl _)     ()
  lei-sound zero    (PiCode _ _) (PiCode _ _)  ()
  -- Stage (suc n)
  lei-sound (suc n) Bot          v             h = tt
  lei-sound (suc n) UCode        Bot           ()
  lei-sound (suc n) UCode        UCode         h = tt
  lei-sound (suc n) UCode        (FunEl _)     ()
  lei-sound (suc n) UCode        (PiCode _ _)  ()
  lei-sound (suc n) (FunEl _)    Bot           ()
  lei-sound (suc n) (FunEl _)    UCode         ()
  lei-sound (suc n) (FunEl g)    (FunEl h)     p = lef-sound (suc n) g h p
  lei-sound (suc n) (FunEl _)    (PiCode _ _)  ()
  lei-sound (suc n) (PiCode _ _) Bot           ()
  lei-sound (suc n) (PiCode _ _) UCode         ()
  lei-sound (suc n) (PiCode _ _) (FunEl _)     ()
  lei-sound (suc n) (PiCode a f) (PiCode b g)  p =
    let pp = min-isPos (OB.lei n a b) (OB.lef (suc n) f g) p
    in mkSigma (lei-sound n a b (fst pp)) (lef-sound (suc n) f g (snd pp))
  lei-sound zero    UCode        NatCode       ()
  lei-sound zero    UCode        ZeroEl        ()
  lei-sound zero    UCode        (SucEl _)     ()
  lei-sound zero    (FunEl _)    NatCode       ()
  lei-sound zero    (FunEl _)    ZeroEl        ()
  lei-sound zero    (FunEl _)    (SucEl _)     ()
  lei-sound zero    (PiCode _ _) NatCode       ()
  lei-sound zero    (PiCode _ _) ZeroEl        ()
  lei-sound zero    (PiCode _ _) (SucEl _)     ()
  lei-sound zero    NatCode      Bot           ()
  lei-sound zero    NatCode      UCode         ()
  lei-sound zero    NatCode      (FunEl _)     ()
  lei-sound zero    NatCode      (PiCode _ _)  ()
  lei-sound zero    NatCode      NatCode       h = tt
  lei-sound zero    NatCode      ZeroEl        ()
  lei-sound zero    NatCode      (SucEl _)     ()
  lei-sound zero    ZeroEl       Bot           ()
  lei-sound zero    ZeroEl       UCode         ()
  lei-sound zero    ZeroEl       (FunEl _)     ()
  lei-sound zero    ZeroEl       (PiCode _ _)  ()
  lei-sound zero    ZeroEl       NatCode       ()
  lei-sound zero    ZeroEl       ZeroEl        h = tt
  lei-sound zero    ZeroEl       (SucEl _)     ()
  lei-sound zero    (SucEl _)    v             ()
  lei-sound (suc n) UCode        NatCode       ()
  lei-sound (suc n) UCode        ZeroEl        ()
  lei-sound (suc n) UCode        (SucEl _)     ()
  lei-sound (suc n) (FunEl _)    NatCode       ()
  lei-sound (suc n) (FunEl _)    ZeroEl        ()
  lei-sound (suc n) (FunEl _)    (SucEl _)     ()
  lei-sound (suc n) (PiCode _ _) NatCode       ()
  lei-sound (suc n) (PiCode _ _) ZeroEl        ()
  lei-sound (suc n) (PiCode _ _) (SucEl _)     ()
  lei-sound (suc n) NatCode      Bot           ()
  lei-sound (suc n) NatCode      UCode         ()
  lei-sound (suc n) NatCode      (FunEl _)     ()
  lei-sound (suc n) NatCode      (PiCode _ _)  ()
  lei-sound (suc n) NatCode      NatCode       h = tt
  lei-sound (suc n) NatCode      ZeroEl        ()
  lei-sound (suc n) NatCode      (SucEl _)     ()
  lei-sound (suc n) ZeroEl       Bot           ()
  lei-sound (suc n) ZeroEl       UCode         ()
  lei-sound (suc n) ZeroEl       (FunEl _)     ()
  lei-sound (suc n) ZeroEl       (PiCode _ _)  ()
  lei-sound (suc n) ZeroEl       NatCode       ()
  lei-sound (suc n) ZeroEl       ZeroEl        h = tt
  lei-sound (suc n) ZeroEl       (SucEl _)     ()
  lei-sound (suc n) (SucEl u)    Bot           ()
  lei-sound (suc n) (SucEl u)    UCode         ()
  lei-sound (suc n) (SucEl u)    (FunEl _)     ()
  lei-sound (suc n) (SucEl u)    (PiCode _ _)  ()
  lei-sound (suc n) (SucEl u)    NatCode       ()
  lei-sound (suc n) (SucEl u)    ZeroEl        ()
  lei-sound (suc n) (SucEl u)    (SucEl v)     p = lei-sound n u v p

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
  lei-complete zero    UCode        Bot           ()
  lei-complete zero    UCode        UCode         h = tt
  lei-complete zero    UCode        (FunEl _)     ()
  lei-complete zero    UCode        (PiCode _ _)  ()
  lei-complete zero    (FunEl _)    Bot           ()
  lei-complete zero    (FunEl _)    UCode         ()
  lei-complete zero    (FunEl _)    (FunEl _)     ()
  lei-complete zero    (FunEl _)    (PiCode _ _)  ()
  lei-complete zero    (PiCode _ _) Bot           ()
  lei-complete zero    (PiCode _ _) UCode         ()
  lei-complete zero    (PiCode _ _) (FunEl _)     ()
  lei-complete zero    (PiCode _ _) (PiCode _ _)  ()
  lei-complete (suc n) Bot          v             h = tt
  lei-complete (suc n) UCode        Bot           ()
  lei-complete (suc n) UCode        UCode         h = tt
  lei-complete (suc n) UCode        (FunEl _)     ()
  lei-complete (suc n) UCode        (PiCode _ _)  ()
  lei-complete (suc n) (FunEl _)    Bot           ()
  lei-complete (suc n) (FunEl _)    UCode         ()
  lei-complete (suc n) (FunEl g)    (FunEl h)     p = lef-complete (suc n) g h p
  lei-complete (suc n) (FunEl _)    (PiCode _ _)  ()
  lei-complete (suc n) (PiCode _ _) Bot           ()
  lei-complete (suc n) (PiCode _ _) UCode         ()
  lei-complete (suc n) (PiCode _ _) (FunEl _)     ()
  lei-complete (suc n) (PiCode a f) (PiCode b g)  p =
    isPos-min (OB.lei n a b) (OB.lef (suc n) f g)
      (lei-complete n a b (fst p)) (lef-complete (suc n) f g (snd p))
  lei-complete zero    UCode        NatCode       ()
  lei-complete zero    UCode        ZeroEl        ()
  lei-complete zero    UCode        (SucEl _)     ()
  lei-complete zero    (FunEl _)    NatCode       ()
  lei-complete zero    (FunEl _)    ZeroEl        ()
  lei-complete zero    (FunEl _)    (SucEl _)     ()
  lei-complete zero    (PiCode _ _) NatCode       ()
  lei-complete zero    (PiCode _ _) ZeroEl        ()
  lei-complete zero    (PiCode _ _) (SucEl _)     ()
  lei-complete zero    NatCode      Bot           ()
  lei-complete zero    NatCode      UCode         ()
  lei-complete zero    NatCode      (FunEl _)     ()
  lei-complete zero    NatCode      (PiCode _ _)  ()
  lei-complete zero    NatCode      NatCode       h = tt
  lei-complete zero    NatCode      ZeroEl        ()
  lei-complete zero    NatCode      (SucEl _)     ()
  lei-complete zero    ZeroEl       Bot           ()
  lei-complete zero    ZeroEl       UCode         ()
  lei-complete zero    ZeroEl       (FunEl _)     ()
  lei-complete zero    ZeroEl       (PiCode _ _)  ()
  lei-complete zero    ZeroEl       NatCode       ()
  lei-complete zero    ZeroEl       ZeroEl        h = tt
  lei-complete zero    ZeroEl       (SucEl _)     ()
  lei-complete zero    (SucEl _)    v             ()
  lei-complete (suc n) UCode        NatCode       ()
  lei-complete (suc n) UCode        ZeroEl        ()
  lei-complete (suc n) UCode        (SucEl _)     ()
  lei-complete (suc n) (FunEl _)    NatCode       ()
  lei-complete (suc n) (FunEl _)    ZeroEl        ()
  lei-complete (suc n) (FunEl _)    (SucEl _)     ()
  lei-complete (suc n) (PiCode _ _) NatCode       ()
  lei-complete (suc n) (PiCode _ _) ZeroEl        ()
  lei-complete (suc n) (PiCode _ _) (SucEl _)     ()
  lei-complete (suc n) NatCode      Bot           ()
  lei-complete (suc n) NatCode      UCode         ()
  lei-complete (suc n) NatCode      (FunEl _)     ()
  lei-complete (suc n) NatCode      (PiCode _ _)  ()
  lei-complete (suc n) NatCode      NatCode       h = tt
  lei-complete (suc n) NatCode      ZeroEl        ()
  lei-complete (suc n) NatCode      (SucEl _)     ()
  lei-complete (suc n) ZeroEl       Bot           ()
  lei-complete (suc n) ZeroEl       UCode         ()
  lei-complete (suc n) ZeroEl       (FunEl _)     ()
  lei-complete (suc n) ZeroEl       (PiCode _ _)  ()
  lei-complete (suc n) ZeroEl       NatCode       ()
  lei-complete (suc n) ZeroEl       ZeroEl        h = tt
  lei-complete (suc n) ZeroEl       (SucEl _)     ()
  lei-complete (suc n) (SucEl u)    Bot           ()
  lei-complete (suc n) (SucEl u)    UCode         ()
  lei-complete (suc n) (SucEl u)    (FunEl _)     ()
  lei-complete (suc n) (SucEl u)    (PiCode _ _)  ()
  lei-complete (suc n) (SucEl u)    NatCode       ()
  lei-complete (suc n) (SucEl u)    ZeroEl        ()
  lei-complete (suc n) (SucEl u)    (SucEl v)     p = lei-complete n u v p

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
leq-Sup-lub n UCode        Bot          c ac bc = ac
leq-Sup-lub n UCode        UCode        c ac bc = ac
leq-Sup-lub n UCode        (FunEl _)    c ac bc = leq-Bot-any n c
leq-Sup-lub n UCode        (PiCode _ _) c ac bc = leq-Bot-any n c
leq-Sup-lub n (FunEl g)    Bot          c ac bc = ac
leq-Sup-lub n (FunEl g)    UCode        c ac bc = leq-Bot-any n c
leq-Sup-lub zero    (FunEl g) (FunEl h) c            () bc
leq-Sup-lub (suc n) (FunEl g) (FunEl h) Bot          () bc
leq-Sup-lub (suc n) (FunEl g) (FunEl h) UCode        () bc
leq-Sup-lub (suc n) (FunEl g) (FunEl h) (FunEl k)    ac bc =
  leqf-append-combine (suc n) g h k ac bc
leq-Sup-lub (suc n) (FunEl g) (FunEl h) (PiCode _ _) () bc
leq-Sup-lub n (FunEl g)    (PiCode _ _) c ac bc = leq-Bot-any n c
leq-Sup-lub n (PiCode a f) Bot          c ac bc = ac
leq-Sup-lub n (PiCode a f) UCode        c ac bc = leq-Bot-any n c
leq-Sup-lub n (PiCode a f) (FunEl _)    c ac bc = leq-Bot-any n c
leq-Sup-lub zero    (PiCode a f) (PiCode b g) c            () bc
leq-Sup-lub (suc n) (PiCode a f) (PiCode b g) Bot          ac ()
leq-Sup-lub (suc n) (PiCode a f) (PiCode b g) UCode        ac ()
leq-Sup-lub (suc n) (PiCode a f) (PiCode b g) (FunEl _)    ac ()
leq-Sup-lub (suc n) (PiCode a f) (PiCode b g) (PiCode c k) ac bc =
  mkSigma (leq-Sup-lub n a b c (fst ac) (fst bc))
          (leqf-append-combine (suc n) f g k (snd ac) (snd bc))
leq-Sup-lub n UCode        NatCode      c ac bc = leq-Bot-any n c
leq-Sup-lub n UCode        ZeroEl       c ac bc = leq-Bot-any n c
leq-Sup-lub n UCode        (SucEl _)    c ac bc = leq-Bot-any n c
leq-Sup-lub n (FunEl g)    NatCode      c ac bc = leq-Bot-any n c
leq-Sup-lub n (FunEl g)    ZeroEl       c ac bc = leq-Bot-any n c
leq-Sup-lub n (FunEl g)    (SucEl _)    c ac bc = leq-Bot-any n c
leq-Sup-lub n (PiCode a f) NatCode      c ac bc = leq-Bot-any n c
leq-Sup-lub n (PiCode a f) ZeroEl       c ac bc = leq-Bot-any n c
leq-Sup-lub n (PiCode a f) (SucEl _)    c ac bc = leq-Bot-any n c
leq-Sup-lub n NatCode      Bot          c ac bc = ac
leq-Sup-lub n NatCode      UCode        c ac bc = leq-Bot-any n c
leq-Sup-lub n NatCode      (FunEl _)    c ac bc = leq-Bot-any n c
leq-Sup-lub n NatCode      (PiCode _ _) c ac bc = leq-Bot-any n c
leq-Sup-lub n NatCode      NatCode      c ac bc = ac
leq-Sup-lub n NatCode      ZeroEl       c ac bc = leq-Bot-any n c
leq-Sup-lub n NatCode      (SucEl _)    c ac bc = leq-Bot-any n c
leq-Sup-lub n ZeroEl       Bot          c ac bc = ac
leq-Sup-lub n ZeroEl       UCode        c ac bc = leq-Bot-any n c
leq-Sup-lub n ZeroEl       (FunEl _)    c ac bc = leq-Bot-any n c
leq-Sup-lub n ZeroEl       (PiCode _ _) c ac bc = leq-Bot-any n c
leq-Sup-lub n ZeroEl       NatCode      c ac bc = leq-Bot-any n c
leq-Sup-lub n ZeroEl       ZeroEl       c ac bc = ac
leq-Sup-lub n ZeroEl       (SucEl _)    c ac bc = leq-Bot-any n c
leq-Sup-lub n (SucEl a)    Bot          c ac bc = ac
leq-Sup-lub n (SucEl a)    UCode        c ac bc = leq-Bot-any n c
leq-Sup-lub n (SucEl a)    (FunEl _)    c ac bc = leq-Bot-any n c
leq-Sup-lub n (SucEl a)    (PiCode _ _) c ac bc = leq-Bot-any n c
leq-Sup-lub n (SucEl a)    NatCode      c ac bc = leq-Bot-any n c
leq-Sup-lub n (SucEl a)    ZeroEl       c ac bc = leq-Bot-any n c
leq-Sup-lub zero    (SucEl a) (SucEl b) c            () bc
leq-Sup-lub (suc n) (SucEl a) (SucEl b) Bot          () bc
leq-Sup-lub (suc n) (SucEl a) (SucEl b) UCode        () bc
leq-Sup-lub (suc n) (SucEl a) (SucEl b) (FunEl _)    () bc
leq-Sup-lub (suc n) (SucEl a) (SucEl b) (PiCode _ _) () bc
leq-Sup-lub (suc n) (SucEl a) (SucEl b) NatCode      () bc
leq-Sup-lub (suc n) (SucEl a) (SucEl b) ZeroEl       () bc
leq-Sup-lub (suc n) (SucEl a) (SucEl b) (SucEl c)    ac bc = leq-Sup-lub n a b c ac bc
