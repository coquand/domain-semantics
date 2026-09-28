{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- LeqStageComp.agda  (MIN/ — Pi + U fragment)
--
-- The STRUCTURAL Comp / Coherent / Sup lemmas, extracted verbatim from
-- PaperOrder.  These mention only Comp / CompFun / Coherent /
-- CoherentFunTail / NotBot / Sup / append (all defined in LeqStage) and
-- NEVER the order `leq`/`lei` or the evaluation `ev`/`EvalFun`.  Hence
-- they are ordinary structural recursions on FinEl (descending RANK) or
-- FinFun (descending the list) and need no
-- stage index.
--
-- Re-founded PaperOrder re-exports these; LeqStageProps uses the
-- Coherent/Comp ones (Coherent-Sup etc.) in the stage-indexed order
-- property pack.
--
-- NO postulates.
------------------------------------------------------------------------

module BCDE4.Dom.OrderComp where

open import BCDE4.Dom.Basic using (U0 ; EqL ; eqL ; EqL-refl ; EqL-sym ; EqL-trans ; EqL-Eq ; eqL-EqL ; EqL-eqL ; eqL-refl)

open import BCDE4.Dom.Basic
  using ( Top ; tt ; Empty
        ; Pair ; mkSigma ; fst ; snd
        ; Eq ; refl ; Eq-sym ; Eq-cong ; Eq-transport
        ; cons-eq
        ; FinEl ; Bot ; UCode ; LevTy ; LevEl ; FunEl ; PiCode ; LPiCode ; FinFun ; nil ; cons )
open import BCDE4.Dom.OrderStage
  using ( append ; Sup
        ; Comp ; CompFun ; CompStepFun ; CompStepStep
        ; NotBot
        ; Coherent ; CoherentFun ; CFTcons ; mkCFT ; CoherentFunTail ; CoherentWith
        ; cft-from-cf )

------------------------------------------------------------------------
-- Sup with Bot
------------------------------------------------------------------------

Sup-Bot-l : (v : FinEl) -> Eq (Sup Bot v) v
Sup-Bot-l Bot             = refl
Sup-Bot-l (UCode lu)           = refl
Sup-Bot-l (LPiCode f)  = refl
Sup-Bot-l LevTy          = refl
Sup-Bot-l (LevEl _)      = refl
Sup-Bot-l (FunEl g)       = refl
Sup-Bot-l (PiCode b g)    = refl

Sup-Bot-r : (u : FinEl) -> Eq (Sup u Bot) u
Sup-Bot-r Bot             = refl
Sup-Bot-r (UCode lu)           = refl
Sup-Bot-r (LPiCode f)  = refl
Sup-Bot-r LevTy          = refl
Sup-Bot-r (LevEl _)      = refl
Sup-Bot-r (FunEl g)       = refl
Sup-Bot-r (PiCode a f)    = refl

Sup-Bot-right : (x : FinEl) -> Eq (Sup x Bot) x
Sup-Bot-right Bot             = refl
Sup-Bot-right (UCode lu)           = refl
Sup-Bot-right (LPiCode f)  = refl
Sup-Bot-right LevTy          = refl
Sup-Bot-right (LevEl _)      = refl
Sup-Bot-right (FunEl g)       = refl
Sup-Bot-right (PiCode a f)    = refl

------------------------------------------------------------------------
-- Congruences
------------------------------------------------------------------------

PiCode-cong : {a b : FinEl} {f g : FinFun} ->
  Eq a b -> Eq f g -> Eq (PiCode a f) (PiCode b g)
PiCode-cong refl refl = refl

LPiCode-cong : {f g : FinFun} -> Eq f g -> Eq (LPiCode f) (LPiCode g)
LPiCode-cong refl = refl

append-assoc : (f g h : FinFun) -> Eq (append f (append g h)) (append (append f g) h)
append-assoc nil         g h = refl
append-assoc (cons p ps) g h = cons-eq refl (append-assoc ps g h)

------------------------------------------------------------------------
-- Comp with Bot
------------------------------------------------------------------------

comp-Bot-r : (u : FinEl) -> Comp u Bot
comp-Bot-r Bot             = tt
comp-Bot-r (UCode lu)           = tt
comp-Bot-r (LPiCode f)  = tt
comp-Bot-r LevTy          = tt
comp-Bot-r (LevEl _)      = tt
comp-Bot-r (FunEl g)       = tt
comp-Bot-r (PiCode a f)    = tt

comp-Bot-l : (u : FinEl) -> Comp Bot u
comp-Bot-l Bot             = tt
comp-Bot-l (UCode lu)           = tt
comp-Bot-l (LPiCode f)  = tt
comp-Bot-l LevTy          = tt
comp-Bot-l (LevEl _)      = tt
comp-Bot-l (FunEl g)       = tt
comp-Bot-l (PiCode a f)    = tt

------------------------------------------------------------------------
-- CompFun / CompStepFun append
------------------------------------------------------------------------

compStepFun-append : (s : Pair FinEl FinEl) (g h : FinFun) ->
  CompStepFun s g -> CompStepFun s h -> CompStepFun s (append g h)
compStepFun-append s nil         h cg ch = ch
compStepFun-append s (cons t ts) h cg ch =
  mkSigma (fst cg) (compStepFun-append s ts h (snd cg) ch)

compFun-append : (g h j : FinFun) ->
  CompFun g h -> CompFun g j -> CompFun g (append h j)
compFun-append nil         h j ch cj = tt
compFun-append (cons s ss) h j ch cj =
  mkSigma (compStepFun-append s h j (fst ch) (fst cj))
          (compFun-append ss h j (snd ch) (snd cj))

------------------------------------------------------------------------
-- comp-Sup  (structural on the first FinEl arg)
------------------------------------------------------------------------

comp-Sup : (a b c : FinEl) -> Comp a b -> Comp a c -> Comp a (Sup b c)
comp-Sup Bot b c ab ac = comp-Bot-l (Sup b c)
comp-Sup (UCode lu) Bot c ab ac = ac
comp-Sup (UCode lu) (UCode lv) Bot             ab ac = ab
comp-Sup (UCode lu) (UCode lv) (UCode lw)           ab ac = ab
comp-Sup (UCode lu) (UCode lv) (FunEl j)       ab ac = tt
comp-Sup (UCode lu) (UCode lv) (PiCode e j)    ab ac = tt
comp-Sup (UCode lu) (FunEl h) c () ac
comp-Sup (UCode lu) (PiCode d k) c () ac
comp-Sup (FunEl g) Bot c ab ac = ac
comp-Sup (FunEl g) (UCode lu) c () ac
comp-Sup (FunEl g) (FunEl h) Bot ab ac = ab
comp-Sup (FunEl g) (FunEl h) (UCode lu) ab ()
comp-Sup (FunEl g) (FunEl h) (FunEl j) ab ac = compFun-append g h j ab ac
comp-Sup (FunEl g) (FunEl h) (PiCode d k) ab ()
comp-Sup (FunEl g) (PiCode d k) c () ac
comp-Sup (PiCode a f) Bot c ab ac = ac
comp-Sup (PiCode a f) (UCode lu) c () ac
comp-Sup (PiCode a f) (FunEl h) c () ac
comp-Sup (UCode _)     (UCode _)     (LPiCode h)   ab ac = tt
comp-Sup (UCode _)     (LPiCode g)   c             () ac
comp-Sup LevTy         LevTy         (LPiCode h)   ab ac = tt
comp-Sup LevTy         (LPiCode g)   c             () ac
comp-Sup (LevEl _)     (LevEl _)     (LPiCode h)   ab ac = tt
comp-Sup (LevEl _)     (LPiCode g)   c             () ac
comp-Sup (FunEl _)     (FunEl _)     (LPiCode h)   ab ()
comp-Sup (FunEl _)     (LPiCode g)   c             () ac
comp-Sup (PiCode _ _)  (PiCode _ _)  (LPiCode h)   ab ()
comp-Sup (PiCode _ _)  (LPiCode g)   c             () ac
comp-Sup (LPiCode f)   Bot           c             ab ac = ac
comp-Sup (LPiCode f)   (UCode _)     c             () ac
comp-Sup (LPiCode f)   LevTy         c             () ac
comp-Sup (LPiCode f)   (LevEl _)     c             () ac
comp-Sup (LPiCode f)   (FunEl _)     c             () ac
comp-Sup (LPiCode f)   (PiCode _ _)  c             () ac
comp-Sup (LPiCode f)   (LPiCode g)   Bot           ab ac = ab
comp-Sup (LPiCode f)   (LPiCode g)   (UCode _)     ab ()
comp-Sup (LPiCode f)   (LPiCode g)   LevTy         ab ()
comp-Sup (LPiCode f)   (LPiCode g)   (LevEl _)     ab ()
comp-Sup (LPiCode f)   (LPiCode g)   (FunEl _)     ab ()
comp-Sup (LPiCode f)   (LPiCode g)   (PiCode _ _)  ab ()
comp-Sup (LPiCode f)   (LPiCode g)   (LPiCode h)   ab ac = compFun-append f g h ab ac
comp-Sup (UCode _)     (UCode _)     LevTy         ab ac = tt
comp-Sup (UCode _)     (UCode _)     (LevEl lw)    ab ac = tt
comp-Sup (UCode _)     LevTy         c             () ac
comp-Sup (UCode _)     (LevEl lv)    c             () ac
comp-Sup LevTy         Bot           c             ab ac = ac
comp-Sup LevTy         (UCode _)     c             () ac
comp-Sup LevTy         LevTy         Bot           ab ac = ab
comp-Sup LevTy         LevTy         (UCode _)     ab ac = tt
comp-Sup LevTy         LevTy         LevTy         ab ac = ab
comp-Sup LevTy         LevTy         (LevEl lw)    ab ac = tt
comp-Sup LevTy         LevTy         (FunEl _)     ab ac = tt
comp-Sup LevTy         LevTy         (PiCode _ _)  ab ac = tt
comp-Sup LevTy         (LevEl lv)    c             () ac
comp-Sup LevTy         (FunEl _)     c             () ac
comp-Sup LevTy         (PiCode _ _)  c             () ac
comp-Sup (LevEl lu)    Bot           c             ab ac = ac
comp-Sup (LevEl lu)    (UCode _)     c             () ac
comp-Sup (LevEl lu)    LevTy         c             () ac
comp-Sup (LevEl lu)    (LevEl lv)    Bot           ab ac = ab
comp-Sup (LevEl lu)    (LevEl lv)    (UCode _)     ab ac = tt
comp-Sup (LevEl lu)    (LevEl lv)    LevTy         ab ac = tt
comp-Sup (LevEl lu)    (LevEl lv)    (LevEl lw)    ab ac = ab
comp-Sup (LevEl lu)    (LevEl lv)    (FunEl _)     ab ac = tt
comp-Sup (LevEl lu)    (LevEl lv)    (PiCode _ _)  ab ac = tt
comp-Sup (LevEl lu)    (FunEl _)     c             () ac
comp-Sup (LevEl lu)    (PiCode _ _)  c             () ac
comp-Sup (FunEl _)     LevTy         c             () ac
comp-Sup (FunEl _)     (LevEl lv)    c             () ac
comp-Sup (FunEl _)     (FunEl _)     LevTy         ab ()
comp-Sup (FunEl _)     (FunEl _)     (LevEl lw)    ab ()
comp-Sup (PiCode _ _)  LevTy         c             () ac
comp-Sup (PiCode _ _)  (LevEl lv)    c             () ac
comp-Sup (PiCode _ _)  (PiCode _ _)  LevTy         ab ()
comp-Sup (PiCode _ _)  (PiCode _ _)  (LevEl lw)    ab ()
comp-Sup (PiCode a f) (PiCode d k) Bot ab ac = ab
comp-Sup (PiCode a f) (PiCode d k) (UCode lu) ab ()
comp-Sup (PiCode a f) (PiCode d k) (FunEl h) ab ()
comp-Sup (PiCode a f) (PiCode d k) (PiCode e j) ab ac =
  mkSigma (comp-Sup a d e (fst ab) (fst ac))
          (compFun-append f k j (snd ab) (snd ac))

------------------------------------------------------------------------
-- Comp-sym
------------------------------------------------------------------------

mutual
  Comp-sym : (u v : FinEl) -> Comp u v -> Comp v u
  Comp-sym Bot Bot c = tt
  Comp-sym Bot (UCode lu) c = tt
  Comp-sym Bot (FunEl h) c = tt
  Comp-sym Bot (PiCode b g) c = tt
  Comp-sym (UCode lu) Bot c = tt
  Comp-sym (UCode lu) (UCode lv) c = EqL-sym lu lv c
  Comp-sym (UCode lu) (FunEl h) c = c
  Comp-sym (UCode lu) (PiCode b g) ()
  Comp-sym (FunEl g) Bot c = tt
  Comp-sym (FunEl g) (UCode lu) c = c
  Comp-sym (FunEl g) (FunEl h) c = CompFun-sym g h c
  Comp-sym (FunEl g) (PiCode b h) c = c
  Comp-sym (PiCode a f) Bot c = tt
  Comp-sym (PiCode a f) (UCode lu) ()
  Comp-sym (PiCode a f) (FunEl h) c = c
  Comp-sym Bot (LPiCode g) c = tt
  Comp-sym (UCode _)      (LPiCode g)    ()
  Comp-sym LevTy          (LPiCode g)    ()
  Comp-sym (LevEl _)      (LPiCode g)    ()
  Comp-sym (FunEl _)      (LPiCode g)    ()
  Comp-sym (PiCode _ _)   (LPiCode g)    ()
  Comp-sym (LPiCode f)    Bot            c = tt
  Comp-sym (LPiCode f)    (UCode _)      ()
  Comp-sym (LPiCode f)    LevTy          ()
  Comp-sym (LPiCode f)    (LevEl _)      ()
  Comp-sym (LPiCode f)    (FunEl _)      ()
  Comp-sym (LPiCode f)    (PiCode _ _)   ()
  Comp-sym (LPiCode f)    (LPiCode g)    c = CompFun-sym f g c
  Comp-sym Bot LevTy c = tt
  Comp-sym Bot (LevEl lv) c = tt
  Comp-sym (UCode _)      LevTy          ()
  Comp-sym (UCode _)      (LevEl lv)     ()
  Comp-sym LevTy          Bot            c = tt
  Comp-sym LevTy          (UCode _)      ()
  Comp-sym LevTy          LevTy          c = c
  Comp-sym LevTy          (LevEl lv)     ()
  Comp-sym LevTy          (FunEl _)      ()
  Comp-sym LevTy          (PiCode _ _)   ()
  Comp-sym (LevEl lu)     Bot            c = tt
  Comp-sym (LevEl lu)     (UCode _)      ()
  Comp-sym (LevEl lu)     LevTy          ()
  Comp-sym (LevEl lu)     (LevEl lv)     c = EqL-sym lu lv c
  Comp-sym (LevEl lu)     (FunEl _)      ()
  Comp-sym (LevEl lu)     (PiCode _ _)   ()
  Comp-sym (FunEl _)      LevTy          ()
  Comp-sym (FunEl _)      (LevEl lv)     ()
  Comp-sym (PiCode _ _)   LevTy          ()
  Comp-sym (PiCode _ _)   (LevEl lv)     ()
  Comp-sym (PiCode a f) (PiCode b g) c =
    mkSigma (Comp-sym a b (fst c)) (CompFun-sym f g (snd c))

  CompFun-sym : (g h : FinFun) -> CompFun g h -> CompFun h g
  CompFun-sym g nil cf = tt
  CompFun-sym g (cons t ts) cf =
    mkSigma (CompFun-sym-col g t ts cf)
            (CompFun-sym g ts (CompFun-drop-col g t ts cf))

  CompFun-sym-col : (g : FinFun) (t : Pair FinEl FinEl) (ts : FinFun) ->
    CompFun g (cons t ts) -> CompStepFun t g
  CompFun-sym-col nil t ts cf = tt
  CompFun-sym-col (cons s ss) t ts cf =
    mkSigma (\ c -> Comp-sym (snd s) (snd t) (fst (fst cf) (Comp-sym (fst t) (fst s) c)))
            (CompFun-sym-col ss t ts (snd cf))

  CompFun-drop-col : (g : FinFun) (t : Pair FinEl FinEl) (ts : FinFun) ->
    CompFun g (cons t ts) -> CompFun g ts
  CompFun-drop-col nil t ts cf = tt
  CompFun-drop-col (cons s ss) t ts cf =
    mkSigma (snd (fst cf)) (CompFun-drop-col ss t ts (snd cf))

------------------------------------------------------------------------
-- coherentWith <-> compStepFun
------------------------------------------------------------------------

coherentWith-to-compStepFun : (q : Pair FinEl FinEl) (qs : FinFun) ->
  CoherentWith q qs -> CompStepFun q qs
coherentWith-to-compStepFun q nil cw = tt
coherentWith-to-compStepFun q (cons r rs) cw =
  mkSigma (fst cw) (coherentWith-to-compStepFun q rs (snd cw))

compStepFun-to-coherentWith : (q : Pair FinEl FinEl) (h : FinFun) ->
  CompStepFun q h -> CoherentWith q h
compStepFun-to-coherentWith q nil csf = tt
compStepFun-to-coherentWith q (cons r rs) csf =
  mkSigma (fst csf) (compStepFun-to-coherentWith q rs (snd csf))

coherentWith-append : (q : Pair FinEl FinEl) (qs h : FinFun) ->
  CoherentWith q qs -> CoherentWith q h -> CoherentWith q (append qs h)
coherentWith-append q nil h cw1 cw2 = cw2
coherentWith-append q (cons r rs) h cw1 cw2 =
  mkSigma (fst cw1) (coherentWith-append q rs h (snd cw1) cw2)

------------------------------------------------------------------------
-- Comp-refl
------------------------------------------------------------------------

CompFun-cons-right : (s : Pair FinEl FinEl) (ss hs : FinFun) ->
  CoherentWith s ss -> CompFun ss hs -> CompFun ss (cons s hs)
CompFun-cons-right s nil hs cw cf = tt
CompFun-cons-right s (cons t ts) hs cw cf =
  mkSigma (mkSigma (\ c -> Comp-sym (snd s) (snd t) (fst cw (Comp-sym (fst t) (fst s) c)))
                    (fst cf))
          (CompFun-cons-right s ts hs (snd cw) (snd cf))

mutual
  Comp-refl : (v : FinEl) -> Coherent v -> Comp v v
  Comp-refl Bot coh = tt
  Comp-refl (UCode lu) coh = EqL-refl lu
  Comp-refl LevTy coh = tt
  Comp-refl (LevEl lu) coh = EqL-refl lu
  Comp-refl (LPiCode f) coh = CompFun-refl f coh
  Comp-refl (FunEl g) coh = CompFun-refl g (cft-from-cf g coh)
  Comp-refl (PiCode a f) coh =
    mkSigma (Comp-refl a (fst coh)) (CompFun-refl f (snd coh))

  CompFun-refl : (g : FinFun) -> CoherentFunTail g -> CompFun g g
  CompFun-refl nil coh = tt
  CompFun-refl (cons s ss) coh =
    mkSigma (mkSigma (\ _ -> Comp-refl (snd s) (CFTcons.val-coh coh))
                      (coherentWith-to-compStepFun s ss (CFTcons.compat coh)))
            (CompFun-cons-right s ss ss (CFTcons.compat coh)
              (CompFun-refl ss (CFTcons.tail-coh coh)))

------------------------------------------------------------------------
-- comp-Sup-sym
------------------------------------------------------------------------

comp-Sup-sym : (a b v : FinEl) -> Comp a v -> Comp b v -> Comp (Sup a b) v
comp-Sup-sym a b v ca cb =
  Comp-sym v (Sup a b) (comp-Sup v a b (Comp-sym a v ca) (Comp-sym b v cb))

------------------------------------------------------------------------
-- NotBot-Sup-Comp
------------------------------------------------------------------------

NotBot-Sup-Comp : (u v : FinEl) -> NotBot u -> Comp u v -> NotBot (Sup u v)
NotBot-Sup-Comp Bot v ()
NotBot-Sup-Comp (UCode lu) Bot nb c = tt
NotBot-Sup-Comp (UCode lu) (UCode lv) nb c = tt
NotBot-Sup-Comp (UCode lu) (FunEl h) nb ()
NotBot-Sup-Comp (UCode lu) (PiCode b g) nb ()
NotBot-Sup-Comp (FunEl g) Bot nb c = tt
NotBot-Sup-Comp (FunEl g) (UCode lu) nb ()
NotBot-Sup-Comp (FunEl g) (FunEl h) nb c = tt
NotBot-Sup-Comp (FunEl g) (PiCode b h) nb ()
NotBot-Sup-Comp (PiCode a f) Bot nb c = tt
NotBot-Sup-Comp (PiCode a f) (UCode lu) nb ()
NotBot-Sup-Comp (PiCode a f) (FunEl h) nb ()
NotBot-Sup-Comp (UCode _)      (LPiCode _)    nb ()
NotBot-Sup-Comp LevTy          (LPiCode _)    nb ()
NotBot-Sup-Comp (LevEl _)      (LPiCode _)    nb ()
NotBot-Sup-Comp (FunEl _)      (LPiCode _)    nb ()
NotBot-Sup-Comp (PiCode _ _)   (LPiCode _)    nb ()
NotBot-Sup-Comp (LPiCode _)    Bot            nb c = tt
NotBot-Sup-Comp (LPiCode _)    (UCode _)      nb ()
NotBot-Sup-Comp (LPiCode _)    LevTy          nb ()
NotBot-Sup-Comp (LPiCode _)    (LevEl _)      nb ()
NotBot-Sup-Comp (LPiCode _)    (FunEl _)      nb ()
NotBot-Sup-Comp (LPiCode _)    (PiCode _ _)   nb ()
NotBot-Sup-Comp (LPiCode _)    (LPiCode _)    nb c = tt
NotBot-Sup-Comp (UCode _)      LevTy          nb ()
NotBot-Sup-Comp (UCode _)      (LevEl _)      nb ()
NotBot-Sup-Comp LevTy          Bot            nb c = tt
NotBot-Sup-Comp LevTy          (UCode _)      nb ()
NotBot-Sup-Comp LevTy          LevTy          nb c = tt
NotBot-Sup-Comp LevTy          (LevEl _)      nb ()
NotBot-Sup-Comp LevTy          (FunEl _)      nb ()
NotBot-Sup-Comp LevTy          (PiCode _ _)   nb ()
NotBot-Sup-Comp (LevEl _)      Bot            nb c = tt
NotBot-Sup-Comp (LevEl _)      (UCode _)      nb ()
NotBot-Sup-Comp (LevEl _)      LevTy          nb ()
NotBot-Sup-Comp (LevEl _)      (LevEl _)      nb c = tt
NotBot-Sup-Comp (LevEl _)      (FunEl _)      nb ()
NotBot-Sup-Comp (LevEl _)      (PiCode _ _)   nb ()
NotBot-Sup-Comp (FunEl _)      LevTy          nb ()
NotBot-Sup-Comp (FunEl _)      (LevEl _)      nb ()
NotBot-Sup-Comp (PiCode _ _)   LevTy          nb ()
NotBot-Sup-Comp (PiCode _ _)   (LevEl _)      nb ()
NotBot-Sup-Comp (PiCode a f) (PiCode b g) nb c = tt

------------------------------------------------------------------------
-- Sup-assoc  (structural on the first FinEl arg)
------------------------------------------------------------------------

Sup-assoc : (a b c : FinEl) -> Comp a b -> Comp b c ->
  Eq (Sup (Sup a b) c) (Sup a (Sup b c))
Sup-assoc Bot b c cab cbc = refl
Sup-assoc (UCode lu) Bot c cab cbc = refl
Sup-assoc (UCode lu) (UCode lv) Bot cab cbc = refl
Sup-assoc (UCode lu) (UCode lv) (UCode lw) cab cbc = refl
Sup-assoc (UCode lu) (UCode lv) (FunEl j) cab ()
Sup-assoc (UCode lu) (UCode lv) (PiCode e j) cab ()
Sup-assoc (UCode lu) (FunEl h) c () cbc
Sup-assoc (UCode lu) (PiCode d h) c () cbc
Sup-assoc (FunEl g) Bot c cab cbc = refl
Sup-assoc (FunEl g) (UCode lu) c () cbc
Sup-assoc (FunEl g) (FunEl h) Bot cab cbc = refl
Sup-assoc (FunEl g) (FunEl h) (UCode lu) cab ()
Sup-assoc (FunEl g) (FunEl h) (FunEl j) cab cbc =
  Eq-cong FunEl (Eq-sym (append-assoc g h j))
Sup-assoc (FunEl g) (FunEl h) (PiCode e j) cab ()
Sup-assoc (FunEl g) (PiCode d h) c () cbc
Sup-assoc (PiCode a f) Bot c cab cbc = refl
Sup-assoc (PiCode a f) (UCode lu) c () cbc
Sup-assoc (PiCode a f) (FunEl h) c () cbc
Sup-assoc (UCode _)     (UCode _)     (LPiCode h)   cab ()
Sup-assoc (UCode _)     (LPiCode g)   c             () cbc
Sup-assoc LevTy         LevTy         (LPiCode h)   cab ()
Sup-assoc LevTy         (LPiCode g)   c             () cbc
Sup-assoc (LevEl _)     (LevEl _)     (LPiCode h)   cab ()
Sup-assoc (LevEl _)     (LPiCode g)   c             () cbc
Sup-assoc (FunEl _)     (FunEl _)     (LPiCode h)   cab ()
Sup-assoc (FunEl _)     (LPiCode g)   c             () cbc
Sup-assoc (PiCode _ _)  (PiCode _ _)  (LPiCode h)   cab ()
Sup-assoc (PiCode _ _)  (LPiCode g)   c             () cbc
Sup-assoc (LPiCode f)   Bot           c             cab cbc = refl
Sup-assoc (LPiCode f)   (UCode _)     c             () cbc
Sup-assoc (LPiCode f)   LevTy         c             () cbc
Sup-assoc (LPiCode f)   (LevEl _)     c             () cbc
Sup-assoc (LPiCode f)   (FunEl _)     c             () cbc
Sup-assoc (LPiCode f)   (PiCode _ _)  c             () cbc
Sup-assoc (LPiCode f)   (LPiCode g)   Bot           cab cbc = refl
Sup-assoc (LPiCode f)   (LPiCode g)   (UCode _)     cab ()
Sup-assoc (LPiCode f)   (LPiCode g)   LevTy         cab ()
Sup-assoc (LPiCode f)   (LPiCode g)   (LevEl _)     cab ()
Sup-assoc (LPiCode f)   (LPiCode g)   (FunEl _)     cab ()
Sup-assoc (LPiCode f)   (LPiCode g)   (PiCode _ _)  cab ()
Sup-assoc (LPiCode f)   (LPiCode g)   (LPiCode h)   cab cbc =
  Eq-cong LPiCode (Eq-sym (append-assoc f g h))
Sup-assoc (UCode _)     (UCode _)     LevTy         cab ()
Sup-assoc (UCode _)     (UCode _)     (LevEl _)     cab ()
Sup-assoc (UCode _)     LevTy         c             () cbc
Sup-assoc (UCode _)     (LevEl _)     c             () cbc
Sup-assoc LevTy         Bot           c             cab cbc = refl
Sup-assoc LevTy         (UCode _)     c             () cbc
Sup-assoc LevTy         LevTy         Bot           cab cbc = refl
Sup-assoc LevTy         LevTy         (UCode _)     cab ()
Sup-assoc LevTy         LevTy         LevTy         cab cbc = refl
Sup-assoc LevTy         LevTy         (LevEl _)     cab ()
Sup-assoc LevTy         LevTy         (FunEl _)     cab ()
Sup-assoc LevTy         LevTy         (PiCode _ _)  cab ()
Sup-assoc LevTy         (LevEl _)     c             () cbc
Sup-assoc LevTy         (FunEl _)     c             () cbc
Sup-assoc LevTy         (PiCode _ _)  c             () cbc
Sup-assoc (LevEl _)     Bot           c             cab cbc = refl
Sup-assoc (LevEl _)     (UCode _)     c             () cbc
Sup-assoc (LevEl _)     LevTy         c             () cbc
Sup-assoc (LevEl _)     (LevEl _)     Bot           cab cbc = refl
Sup-assoc (LevEl _)     (LevEl _)     (UCode _)     cab ()
Sup-assoc (LevEl _)     (LevEl _)     LevTy         cab ()
Sup-assoc (LevEl _)     (LevEl _)     (LevEl _)     cab cbc = refl
Sup-assoc (LevEl _)     (LevEl _)     (FunEl _)     cab ()
Sup-assoc (LevEl _)     (LevEl _)     (PiCode _ _)  cab ()
Sup-assoc (LevEl _)     (FunEl _)     c             () cbc
Sup-assoc (LevEl _)     (PiCode _ _)  c             () cbc
Sup-assoc (FunEl _)     LevTy         c             () cbc
Sup-assoc (FunEl _)     (LevEl _)     c             () cbc
Sup-assoc (FunEl _)     (FunEl _)     LevTy         cab ()
Sup-assoc (FunEl _)     (FunEl _)     (LevEl _)     cab ()
Sup-assoc (PiCode _ _)  LevTy         c             () cbc
Sup-assoc (PiCode _ _)  (LevEl _)     c             () cbc
Sup-assoc (PiCode _ _)  (PiCode _ _)  LevTy         cab ()
Sup-assoc (PiCode _ _)  (PiCode _ _)  (LevEl _)     cab ()
Sup-assoc (PiCode a f) (PiCode d h) Bot cab cbc = refl
Sup-assoc (PiCode a f) (PiCode d h) (UCode lu) cab ()
Sup-assoc (PiCode a f) (PiCode d h) (FunEl j) cab ()
Sup-assoc (PiCode a f) (PiCode d h) (PiCode e j) cab cbc =
  PiCode-cong (Sup-assoc a d e (fst cab) (fst cbc))
              (Eq-sym (append-assoc f h j))

------------------------------------------------------------------------
-- Coherent-Sup / CoherentFunTail-append
------------------------------------------------------------------------

mutual
  Coherent-Sup : (a b : FinEl) -> Comp a b -> Coherent a -> Coherent b ->
    Coherent (Sup a b)
  Coherent-Sup Bot b comp coha cohb = cohb
  Coherent-Sup (UCode lu) Bot comp coha cohb = tt
  Coherent-Sup (UCode lu) (UCode lv) comp coha cohb = tt
  Coherent-Sup (UCode lu) (FunEl h) comp coha cohb = tt
  Coherent-Sup (UCode lu) (PiCode c h) () coha cohb
  Coherent-Sup (FunEl g) Bot comp coha cohb = coha
  Coherent-Sup (FunEl g) (UCode lu) comp coha cohb = tt
  Coherent-Sup (FunEl g) (FunEl h) comp coha cohb =
    CoherentFun-append g h coha cohb comp
  Coherent-Sup (FunEl g) (PiCode c h) () coha cohb
  Coherent-Sup (PiCode a f) Bot comp coha cohb = coha
  Coherent-Sup (PiCode a f) (UCode lu) () coha cohb
  Coherent-Sup (PiCode a f) (FunEl h) () coha cohb
  Coherent-Sup (UCode _)      (LPiCode h)    comp coha cohb = tt
  Coherent-Sup LevTy          (LPiCode h)    comp coha cohb = tt
  Coherent-Sup (LevEl _)      (LPiCode h)    comp coha cohb = tt
  Coherent-Sup (FunEl _)      (LPiCode h)    comp coha cohb = tt
  Coherent-Sup (PiCode _ _)   (LPiCode h)    comp coha cohb = tt
  Coherent-Sup (LPiCode f)    Bot            comp coha cohb = coha
  Coherent-Sup (LPiCode f)    (UCode _)      comp coha cohb = tt
  Coherent-Sup (LPiCode f)    LevTy          comp coha cohb = tt
  Coherent-Sup (LPiCode f)    (LevEl _)      comp coha cohb = tt
  Coherent-Sup (LPiCode f)    (FunEl _)      comp coha cohb = tt
  Coherent-Sup (LPiCode f)    (PiCode _ _)   comp coha cohb = tt
  Coherent-Sup (LPiCode f)    (LPiCode h)    comp coha cohb =
    CoherentFunTail-append f h coha cohb comp
  Coherent-Sup (UCode _)      LevTy          comp coha cohb = tt
  Coherent-Sup (UCode _)      (LevEl _)      comp coha cohb = tt
  Coherent-Sup LevTy          Bot            comp coha cohb = tt
  Coherent-Sup LevTy          (UCode _)      comp coha cohb = tt
  Coherent-Sup LevTy          LevTy          comp coha cohb = tt
  Coherent-Sup LevTy          (LevEl _)      comp coha cohb = tt
  Coherent-Sup LevTy          (FunEl _)      comp coha cohb = tt
  Coherent-Sup LevTy          (PiCode _ _)   comp coha cohb = tt
  Coherent-Sup (LevEl _)      Bot            comp coha cohb = tt
  Coherent-Sup (LevEl _)      (UCode _)      comp coha cohb = tt
  Coherent-Sup (LevEl _)      LevTy          comp coha cohb = tt
  Coherent-Sup (LevEl _)      (LevEl _)      comp coha cohb = tt
  Coherent-Sup (LevEl _)      (FunEl _)      comp coha cohb = tt
  Coherent-Sup (LevEl _)      (PiCode _ _)   comp coha cohb = tt
  Coherent-Sup (FunEl _)      LevTy          comp coha cohb = tt
  Coherent-Sup (FunEl _)      (LevEl _)      comp coha cohb = tt
  Coherent-Sup (PiCode _ _)   LevTy          comp coha cohb = tt
  Coherent-Sup (PiCode _ _)   (LevEl _)      comp coha cohb = tt
  Coherent-Sup (PiCode a f) (PiCode c h) comp coha cohb =
    mkSigma (Coherent-Sup a c (fst comp) (fst coha) (fst cohb))
            (CoherentFunTail-append f h (snd coha) (snd cohb) (snd comp))

  CoherentFunTail-append : (g h : FinFun) ->
    CoherentFunTail g -> CoherentFunTail h -> CompFun g h ->
    CoherentFunTail (append g h)
  CoherentFunTail-append nil h cohg cohh cgh = cohh
  CoherentFunTail-append (cons p ps) h cohg cohh cgh =
    mkCFT (CFTcons.key-coh cohg) (CFTcons.val-coh cohg) (CFTcons.val-nbot cohg)
          (coherentWith-append p ps h (CFTcons.compat cohg)
            (compStepFun-to-coherentWith p h (fst cgh)))
          (CoherentFunTail-append ps h (CFTcons.tail-coh cohg) cohh (snd cgh))

  CoherentFun-append : (g h : FinFun) ->
    CoherentFun g -> CoherentFun h -> CompFun g h ->
    CoherentFun (append g h)
  CoherentFun-append nil h () cohh cgh
  CoherentFun-append (cons p ps) h cohg cohh cgh =
    CoherentFunTail-append (cons p ps) h cohg (cft-from-cf h cohh) cgh

------------------------------------------------------------------------
-- Coherent-keys
------------------------------------------------------------------------

Coherent-keys : FinFun -> Set
Coherent-keys nil         = Top
Coherent-keys (cons p ps) = Pair (Coherent (fst p)) (Coherent-keys ps)

CoherentFun-keys : (g : FinFun) -> CoherentFunTail g -> Coherent-keys g
CoherentFun-keys nil         coh = tt
CoherentFun-keys (cons p ps) coh =
  mkSigma (CFTcons.key-coh coh) (CoherentFun-keys ps (CFTcons.tail-coh coh))

Coherent-singleton-key : (u v : FinEl) ->
  Coherent (FunEl (cons (mkSigma u v) nil)) -> Coherent u
Coherent-singleton-key u v coh = CFTcons.key-coh coh

Coherent-singleton-val : (u v : FinEl) ->
  Coherent (FunEl (cons (mkSigma u v) nil)) -> Coherent v
Coherent-singleton-val u v coh = CFTcons.val-coh coh

------------------------------------------------------------------------
-- absurdEl
------------------------------------------------------------------------

absurdEl : {A : Set} -> Empty -> A
absurdEl ()
