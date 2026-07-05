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

module ID.Domain.OrderComp where

open import ID.Domain.Basic
  using ( Top ; tt ; Empty
        ; Pair ; mkSigma ; fst ; snd
        ; Eq ; refl ; Eq-sym ; Eq-cong ; Eq-transport
        ; cons-eq
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; IdCode ; RefEl ; FinFun ; nil ; cons )
open import ID.Domain.OrderStage
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
Sup-Bot-l UCode           = refl
Sup-Bot-l (FunEl g)       = refl
Sup-Bot-l (PiCode b g)    = refl
Sup-Bot-l (IdCode t u v)  = refl
Sup-Bot-l (RefEl w)       = refl

Sup-Bot-r : (u : FinEl) -> Eq (Sup u Bot) u
Sup-Bot-r Bot             = refl
Sup-Bot-r UCode           = refl
Sup-Bot-r (FunEl g)       = refl
Sup-Bot-r (PiCode a f)    = refl
Sup-Bot-r (IdCode t u v)  = refl
Sup-Bot-r (RefEl w)       = refl

Sup-Bot-right : (x : FinEl) -> Eq (Sup x Bot) x
Sup-Bot-right Bot             = refl
Sup-Bot-right UCode           = refl
Sup-Bot-right (FunEl g)       = refl
Sup-Bot-right (PiCode a f)    = refl
Sup-Bot-right (IdCode t u v)  = refl
Sup-Bot-right (RefEl w)       = refl

------------------------------------------------------------------------
-- Congruences
------------------------------------------------------------------------

PiCode-cong : {a b : FinEl} {f g : FinFun} ->
  Eq a b -> Eq f g -> Eq (PiCode a f) (PiCode b g)
PiCode-cong refl refl = refl

IdCode-cong : {t t' u u' v v' : FinEl} ->
  Eq t t' -> Eq u u' -> Eq v v' -> Eq (IdCode t u v) (IdCode t' u' v')
IdCode-cong refl refl refl = refl

append-assoc : (f g h : FinFun) -> Eq (append f (append g h)) (append (append f g) h)
append-assoc nil         g h = refl
append-assoc (cons p ps) g h = cons-eq refl (append-assoc ps g h)

------------------------------------------------------------------------
-- Comp with Bot
------------------------------------------------------------------------

comp-Bot-r : (u : FinEl) -> Comp u Bot
comp-Bot-r Bot             = tt
comp-Bot-r UCode           = tt
comp-Bot-r (FunEl g)       = tt
comp-Bot-r (PiCode a f)    = tt
comp-Bot-r (IdCode t u v)  = tt
comp-Bot-r (RefEl w)       = tt

comp-Bot-l : (u : FinEl) -> Comp Bot u
comp-Bot-l Bot             = tt
comp-Bot-l UCode           = tt
comp-Bot-l (FunEl g)       = tt
comp-Bot-l (PiCode a f)    = tt
comp-Bot-l (IdCode t u v)  = tt
comp-Bot-l (RefEl w)       = tt

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
comp-Sup UCode Bot c ab ac = ac
comp-Sup UCode UCode Bot             ab ac = tt
comp-Sup UCode UCode UCode           ab ac = tt
comp-Sup UCode UCode (FunEl j)       ab ac = tt
comp-Sup UCode UCode (PiCode e j)    ab ac = tt
comp-Sup UCode (FunEl h) c () ac
comp-Sup UCode (PiCode d k) c () ac
comp-Sup (FunEl g) Bot c ab ac = ac
comp-Sup (FunEl g) UCode c () ac
comp-Sup (FunEl g) (FunEl h) Bot ab ac = ab
comp-Sup (FunEl g) (FunEl h) UCode ab ()
comp-Sup (FunEl g) (FunEl h) (FunEl j) ab ac = compFun-append g h j ab ac
comp-Sup (FunEl g) (FunEl h) (PiCode d k) ab ()
comp-Sup (FunEl g) (PiCode d k) c () ac
comp-Sup (PiCode a f) Bot c ab ac = ac
comp-Sup (PiCode a f) UCode c () ac
comp-Sup (PiCode a f) (FunEl h) c () ac
comp-Sup (PiCode a f) (PiCode d k) Bot ab ac = ab
comp-Sup (PiCode a f) (PiCode d k) UCode ab ()
comp-Sup (PiCode a f) (PiCode d k) (FunEl h) ab ()
comp-Sup (PiCode a f) (PiCode d k) (PiCode e j) ab ac =
  mkSigma (comp-Sup a d e (fst ab) (fst ac))
          (compFun-append f k j (snd ab) (snd ac))
-- Id fragment
comp-Sup UCode UCode (IdCode _ _ _) ab ac = tt
comp-Sup UCode UCode (RefEl _)      ab ac = tt
comp-Sup UCode (IdCode _ _ _) c () ac
comp-Sup UCode (RefEl _)      c () ac
comp-Sup (FunEl g) (FunEl h) (IdCode _ _ _) ab ()
comp-Sup (FunEl g) (FunEl h) (RefEl _)      ab ()
comp-Sup (FunEl g) (IdCode _ _ _) c () ac
comp-Sup (FunEl g) (RefEl _)      c () ac
comp-Sup (PiCode a f) (PiCode d k) (IdCode _ _ _) ab ()
comp-Sup (PiCode a f) (PiCode d k) (RefEl _)      ab ()
comp-Sup (PiCode a f) (IdCode _ _ _) c () ac
comp-Sup (PiCode a f) (RefEl _)      c () ac
comp-Sup (IdCode t u v) Bot c ab ac = ac
comp-Sup (IdCode t u v) UCode c () ac
comp-Sup (IdCode t u v) (FunEl _) c () ac
comp-Sup (IdCode t u v) (PiCode _ _) c () ac
comp-Sup (IdCode t u v) (RefEl _) c () ac
comp-Sup (IdCode t u v) (IdCode t1 u1 v1) Bot ab ac = ab
comp-Sup (IdCode t u v) (IdCode t1 u1 v1) UCode ab ()
comp-Sup (IdCode t u v) (IdCode t1 u1 v1) (FunEl _) ab ()
comp-Sup (IdCode t u v) (IdCode t1 u1 v1) (PiCode _ _) ab ()
comp-Sup (IdCode t u v) (IdCode t1 u1 v1) (RefEl _) ab ()
comp-Sup (IdCode t u v) (IdCode t1 u1 v1) (IdCode t2 u2 v2) ab ac =
  mkSigma (comp-Sup t t1 t2 (fst ab) (fst ac))
          (mkSigma (comp-Sup u u1 u2 (fst (snd ab)) (fst (snd ac)))
                   (comp-Sup v v1 v2 (snd (snd ab)) (snd (snd ac))))
comp-Sup (RefEl w) Bot c ab ac = ac
comp-Sup (RefEl w) UCode c () ac
comp-Sup (RefEl w) (FunEl _) c () ac
comp-Sup (RefEl w) (PiCode _ _) c () ac
comp-Sup (RefEl w) (IdCode _ _ _) c () ac
comp-Sup (RefEl w) (RefEl w1) Bot ab ac = ab
comp-Sup (RefEl w) (RefEl w1) UCode ab ()
comp-Sup (RefEl w) (RefEl w1) (FunEl _) ab ()
comp-Sup (RefEl w) (RefEl w1) (PiCode _ _) ab ()
comp-Sup (RefEl w) (RefEl w1) (IdCode _ _ _) ab ()
comp-Sup (RefEl w) (RefEl w1) (RefEl w2) ab ac = comp-Sup w w1 w2 ab ac

------------------------------------------------------------------------
-- Comp-sym
------------------------------------------------------------------------

mutual
  Comp-sym : (u v : FinEl) -> Comp u v -> Comp v u
  Comp-sym Bot Bot c = tt
  Comp-sym Bot UCode c = tt
  Comp-sym Bot (FunEl h) c = tt
  Comp-sym Bot (PiCode b g) c = tt
  Comp-sym UCode Bot c = tt
  Comp-sym UCode UCode c = tt
  Comp-sym UCode (FunEl h) c = c
  Comp-sym UCode (PiCode b g) ()
  Comp-sym (FunEl g) Bot c = tt
  Comp-sym (FunEl g) UCode c = c
  Comp-sym (FunEl g) (FunEl h) c = CompFun-sym g h c
  Comp-sym (FunEl g) (PiCode b h) c = c
  Comp-sym (PiCode a f) Bot c = tt
  Comp-sym (PiCode a f) UCode ()
  Comp-sym (PiCode a f) (FunEl h) c = c
  Comp-sym (PiCode a f) (PiCode b g) c =
    mkSigma (Comp-sym a b (fst c)) (CompFun-sym f g (snd c))
  Comp-sym Bot (IdCode _ _ _) c = tt
  Comp-sym Bot (RefEl _)      c = tt
  Comp-sym UCode (IdCode _ _ _) ()
  Comp-sym UCode (RefEl _)      ()
  Comp-sym (FunEl g) (IdCode _ _ _) ()
  Comp-sym (FunEl g) (RefEl _)      ()
  Comp-sym (PiCode a f) (IdCode _ _ _) ()
  Comp-sym (PiCode a f) (RefEl _)      ()
  Comp-sym (IdCode t u v) Bot c = tt
  Comp-sym (IdCode t u v) UCode ()
  Comp-sym (IdCode t u v) (FunEl _) ()
  Comp-sym (IdCode t u v) (PiCode _ _) ()
  Comp-sym (IdCode t u v) (RefEl _) ()
  Comp-sym (IdCode t u v) (IdCode t' u' v') c =
    mkSigma (Comp-sym t t' (fst c))
            (mkSigma (Comp-sym u u' (fst (snd c))) (Comp-sym v v' (snd (snd c))))
  Comp-sym (RefEl w) Bot c = tt
  Comp-sym (RefEl w) UCode ()
  Comp-sym (RefEl w) (FunEl _) ()
  Comp-sym (RefEl w) (PiCode _ _) ()
  Comp-sym (RefEl w) (IdCode _ _ _) ()
  Comp-sym (RefEl w) (RefEl w') c = Comp-sym w w' c

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
  Comp-refl UCode coh = tt
  Comp-refl (FunEl g) coh = CompFun-refl g (cft-from-cf g coh)
  Comp-refl (PiCode a f) coh =
    mkSigma (Comp-refl a (fst coh)) (CompFun-refl f (snd coh))
  Comp-refl (IdCode t u v) coh =
    mkSigma (Comp-refl t (fst coh))
            (mkSigma (Comp-refl u (fst (snd coh))) (Comp-refl v (snd (snd coh))))
  Comp-refl (RefEl w) coh = Comp-refl w coh

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
NotBot-Sup-Comp UCode Bot nb c = tt
NotBot-Sup-Comp UCode UCode nb c = tt
NotBot-Sup-Comp UCode (FunEl h) nb ()
NotBot-Sup-Comp UCode (PiCode b g) nb ()
NotBot-Sup-Comp (FunEl g) Bot nb c = tt
NotBot-Sup-Comp (FunEl g) UCode nb ()
NotBot-Sup-Comp (FunEl g) (FunEl h) nb c = tt
NotBot-Sup-Comp (FunEl g) (PiCode b h) nb ()
NotBot-Sup-Comp (PiCode a f) Bot nb c = tt
NotBot-Sup-Comp (PiCode a f) UCode nb ()
NotBot-Sup-Comp (PiCode a f) (FunEl h) nb ()
NotBot-Sup-Comp (PiCode a f) (PiCode b g) nb c = tt
NotBot-Sup-Comp UCode (IdCode _ _ _) nb ()
NotBot-Sup-Comp UCode (RefEl _)      nb ()
NotBot-Sup-Comp (FunEl g) (IdCode _ _ _) nb ()
NotBot-Sup-Comp (FunEl g) (RefEl _)      nb ()
NotBot-Sup-Comp (PiCode a f) (IdCode _ _ _) nb ()
NotBot-Sup-Comp (PiCode a f) (RefEl _)      nb ()
NotBot-Sup-Comp (IdCode t u v) Bot nb c = tt
NotBot-Sup-Comp (IdCode t u v) UCode nb ()
NotBot-Sup-Comp (IdCode t u v) (FunEl _) nb ()
NotBot-Sup-Comp (IdCode t u v) (PiCode _ _) nb ()
NotBot-Sup-Comp (IdCode t u v) (RefEl _) nb ()
NotBot-Sup-Comp (IdCode t u v) (IdCode _ _ _) nb c = tt
NotBot-Sup-Comp (RefEl w) Bot nb c = tt
NotBot-Sup-Comp (RefEl w) UCode nb ()
NotBot-Sup-Comp (RefEl w) (FunEl _) nb ()
NotBot-Sup-Comp (RefEl w) (PiCode _ _) nb ()
NotBot-Sup-Comp (RefEl w) (IdCode _ _ _) nb ()
NotBot-Sup-Comp (RefEl w) (RefEl _) nb c = tt

------------------------------------------------------------------------
-- Sup-assoc  (structural on the first FinEl arg)
------------------------------------------------------------------------

Sup-assoc : (a b c : FinEl) -> Comp a b -> Comp b c ->
  Eq (Sup (Sup a b) c) (Sup a (Sup b c))
Sup-assoc Bot b c cab cbc = refl
Sup-assoc UCode Bot c cab cbc = refl
Sup-assoc UCode UCode Bot cab cbc = refl
Sup-assoc UCode UCode UCode cab cbc = refl
Sup-assoc UCode UCode (FunEl j) cab ()
Sup-assoc UCode UCode (PiCode e j) cab ()
Sup-assoc UCode (FunEl h) c () cbc
Sup-assoc UCode (PiCode d h) c () cbc
Sup-assoc (FunEl g) Bot c cab cbc = refl
Sup-assoc (FunEl g) UCode c () cbc
Sup-assoc (FunEl g) (FunEl h) Bot cab cbc = refl
Sup-assoc (FunEl g) (FunEl h) UCode cab ()
Sup-assoc (FunEl g) (FunEl h) (FunEl j) cab cbc =
  Eq-cong FunEl (Eq-sym (append-assoc g h j))
Sup-assoc (FunEl g) (FunEl h) (PiCode e j) cab ()
Sup-assoc (FunEl g) (PiCode d h) c () cbc
Sup-assoc (PiCode a f) Bot c cab cbc = refl
Sup-assoc (PiCode a f) UCode c () cbc
Sup-assoc (PiCode a f) (FunEl h) c () cbc
Sup-assoc (PiCode a f) (PiCode d h) Bot cab cbc = refl
Sup-assoc (PiCode a f) (PiCode d h) UCode cab ()
Sup-assoc (PiCode a f) (PiCode d h) (FunEl j) cab ()
Sup-assoc (PiCode a f) (PiCode d h) (PiCode e j) cab cbc =
  PiCode-cong (Sup-assoc a d e (fst cab) (fst cbc))
              (Eq-sym (append-assoc f h j))
-- Id fragment
Sup-assoc UCode UCode (IdCode _ _ _) cab ()
Sup-assoc UCode UCode (RefEl _)      cab ()
Sup-assoc UCode (IdCode _ _ _) c () cbc
Sup-assoc UCode (RefEl _)      c () cbc
Sup-assoc (FunEl g) (FunEl h) (IdCode _ _ _) cab ()
Sup-assoc (FunEl g) (FunEl h) (RefEl _)      cab ()
Sup-assoc (FunEl g) (IdCode _ _ _) c () cbc
Sup-assoc (FunEl g) (RefEl _)      c () cbc
Sup-assoc (PiCode a f) (PiCode d h) (IdCode _ _ _) cab ()
Sup-assoc (PiCode a f) (PiCode d h) (RefEl _)      cab ()
Sup-assoc (PiCode a f) (IdCode _ _ _) c () cbc
Sup-assoc (PiCode a f) (RefEl _)      c () cbc
Sup-assoc (IdCode t u v) Bot c cab cbc = refl
Sup-assoc (IdCode t u v) UCode c () cbc
Sup-assoc (IdCode t u v) (FunEl _) c () cbc
Sup-assoc (IdCode t u v) (PiCode _ _) c () cbc
Sup-assoc (IdCode t u v) (RefEl _) c () cbc
Sup-assoc (IdCode t u v) (IdCode t1 u1 v1) Bot cab cbc = refl
Sup-assoc (IdCode t u v) (IdCode t1 u1 v1) UCode cab ()
Sup-assoc (IdCode t u v) (IdCode t1 u1 v1) (FunEl _) cab ()
Sup-assoc (IdCode t u v) (IdCode t1 u1 v1) (PiCode _ _) cab ()
Sup-assoc (IdCode t u v) (IdCode t1 u1 v1) (RefEl _) cab ()
Sup-assoc (IdCode t u v) (IdCode t1 u1 v1) (IdCode t2 u2 v2) cab cbc =
  IdCode-cong (Sup-assoc t t1 t2 (fst cab) (fst cbc))
              (Sup-assoc u u1 u2 (fst (snd cab)) (fst (snd cbc)))
              (Sup-assoc v v1 v2 (snd (snd cab)) (snd (snd cbc)))
Sup-assoc (RefEl w) Bot c cab cbc = refl
Sup-assoc (RefEl w) UCode c () cbc
Sup-assoc (RefEl w) (FunEl _) c () cbc
Sup-assoc (RefEl w) (PiCode _ _) c () cbc
Sup-assoc (RefEl w) (IdCode _ _ _) c () cbc
Sup-assoc (RefEl w) (RefEl w1) Bot cab cbc = refl
Sup-assoc (RefEl w) (RefEl w1) UCode cab ()
Sup-assoc (RefEl w) (RefEl w1) (FunEl _) cab ()
Sup-assoc (RefEl w) (RefEl w1) (PiCode _ _) cab ()
Sup-assoc (RefEl w) (RefEl w1) (IdCode _ _ _) cab ()
Sup-assoc (RefEl w) (RefEl w1) (RefEl w2) cab cbc =
  Eq-cong RefEl (Sup-assoc w w1 w2 cab cbc)

------------------------------------------------------------------------
-- Coherent-Sup / CoherentFunTail-append
------------------------------------------------------------------------

mutual
  Coherent-Sup : (a b : FinEl) -> Comp a b -> Coherent a -> Coherent b ->
    Coherent (Sup a b)
  Coherent-Sup Bot b comp coha cohb = cohb
  Coherent-Sup UCode Bot comp coha cohb = tt
  Coherent-Sup UCode UCode comp coha cohb = tt
  Coherent-Sup UCode (FunEl h) comp coha cohb = tt
  Coherent-Sup UCode (PiCode c h) () coha cohb
  Coherent-Sup (FunEl g) Bot comp coha cohb = coha
  Coherent-Sup (FunEl g) UCode comp coha cohb = tt
  Coherent-Sup (FunEl g) (FunEl h) comp coha cohb =
    CoherentFun-append g h coha cohb comp
  Coherent-Sup (FunEl g) (PiCode c h) () coha cohb
  Coherent-Sup (PiCode a f) Bot comp coha cohb = coha
  Coherent-Sup (PiCode a f) UCode () coha cohb
  Coherent-Sup (PiCode a f) (FunEl h) () coha cohb
  Coherent-Sup (PiCode a f) (PiCode c h) comp coha cohb =
    mkSigma (Coherent-Sup a c (fst comp) (fst coha) (fst cohb))
            (CoherentFunTail-append f h (snd coha) (snd cohb) (snd comp))
  Coherent-Sup UCode (IdCode _ _ _) () coha cohb
  Coherent-Sup UCode (RefEl _)      () coha cohb
  Coherent-Sup (FunEl g) (IdCode _ _ _) () coha cohb
  Coherent-Sup (FunEl g) (RefEl _)      () coha cohb
  Coherent-Sup (PiCode a f) (IdCode _ _ _) () coha cohb
  Coherent-Sup (PiCode a f) (RefEl _)      () coha cohb
  Coherent-Sup (IdCode t u v) Bot comp coha cohb = coha
  Coherent-Sup (IdCode t u v) UCode () coha cohb
  Coherent-Sup (IdCode t u v) (FunEl _) () coha cohb
  Coherent-Sup (IdCode t u v) (PiCode _ _) () coha cohb
  Coherent-Sup (IdCode t u v) (RefEl _) () coha cohb
  Coherent-Sup (IdCode t u v) (IdCode t1 u1 v1) comp coha cohb =
    mkSigma (Coherent-Sup t t1 (fst comp) (fst coha) (fst cohb))
            (mkSigma (Coherent-Sup u u1 (fst (snd comp)) (fst (snd coha)) (fst (snd cohb)))
                     (Coherent-Sup v v1 (snd (snd comp)) (snd (snd coha)) (snd (snd cohb))))
  Coherent-Sup (RefEl w) Bot comp coha cohb = coha
  Coherent-Sup (RefEl w) UCode () coha cohb
  Coherent-Sup (RefEl w) (FunEl _) () coha cohb
  Coherent-Sup (RefEl w) (PiCode _ _) () coha cohb
  Coherent-Sup (RefEl w) (IdCode _ _ _) () coha cohb
  Coherent-Sup (RefEl w) (RefEl w1) comp coha cohb = Coherent-Sup w w1 comp coha cohb

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
