{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- LeqStageComp.agda  (NAT/ — Pi + U fragment)
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

module NAT.Domain.OrderComp where

open import NAT.Domain.Basic
  using ( Top ; tt ; Empty
        ; Pair ; mkSigma ; fst ; snd
        ; Eq ; refl ; Eq-sym ; Eq-cong ; Eq-transport
        ; cons-eq
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; FinFun ; nil ; cons )
open import NAT.Domain.OrderStage
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
Sup-Bot-l NatCode         = refl
Sup-Bot-l ZeroEl          = refl
Sup-Bot-l (SucEl v)       = refl

Sup-Bot-r : (u : FinEl) -> Eq (Sup u Bot) u
Sup-Bot-r Bot             = refl
Sup-Bot-r UCode           = refl
Sup-Bot-r (FunEl g)       = refl
Sup-Bot-r (PiCode a f)    = refl
Sup-Bot-r NatCode         = refl
Sup-Bot-r ZeroEl          = refl
Sup-Bot-r (SucEl u)       = refl

Sup-Bot-right : (x : FinEl) -> Eq (Sup x Bot) x
Sup-Bot-right Bot             = refl
Sup-Bot-right UCode           = refl
Sup-Bot-right (FunEl g)       = refl
Sup-Bot-right (PiCode a f)    = refl
Sup-Bot-right NatCode         = refl
Sup-Bot-right ZeroEl          = refl
Sup-Bot-right (SucEl x)       = refl

------------------------------------------------------------------------
-- Congruences
------------------------------------------------------------------------

PiCode-cong : {a b : FinEl} {f g : FinFun} ->
  Eq a b -> Eq f g -> Eq (PiCode a f) (PiCode b g)
PiCode-cong refl refl = refl

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
comp-Bot-r NatCode         = tt
comp-Bot-r ZeroEl          = tt
comp-Bot-r (SucEl u)       = tt

comp-Bot-l : (u : FinEl) -> Comp Bot u
comp-Bot-l Bot             = tt
comp-Bot-l UCode           = tt
comp-Bot-l (FunEl g)       = tt
comp-Bot-l (PiCode a f)    = tt
comp-Bot-l NatCode         = tt
comp-Bot-l ZeroEl          = tt
comp-Bot-l (SucEl u)       = tt

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
comp-Sup UCode UCode NatCode ab ac = tt
comp-Sup UCode UCode ZeroEl ab ac = tt
comp-Sup UCode UCode (SucEl j) ab ac = tt
comp-Sup (FunEl g) (FunEl h) NatCode ab ac = tt
comp-Sup (FunEl g) (FunEl h) ZeroEl ab ac = tt
comp-Sup (FunEl g) (FunEl h) (SucEl j) ab ac = tt
comp-Sup (PiCode a f) (PiCode d k) NatCode ab ac = tt
comp-Sup (PiCode a f) (PiCode d k) ZeroEl ab ac = tt
comp-Sup (PiCode a f) (PiCode d k) (SucEl j) ab ac = tt
comp-Sup NatCode Bot c ab ac = ac
comp-Sup NatCode NatCode Bot ab ac = tt
comp-Sup NatCode NatCode UCode ab ac = tt
comp-Sup NatCode NatCode (FunEl j) ab ac = tt
comp-Sup NatCode NatCode (PiCode e j) ab ac = tt
comp-Sup NatCode NatCode NatCode ab ac = tt
comp-Sup NatCode NatCode ZeroEl ab ac = tt
comp-Sup NatCode NatCode (SucEl j) ab ac = tt
comp-Sup NatCode UCode c () ac
comp-Sup NatCode (FunEl h) c () ac
comp-Sup NatCode (PiCode d k) c () ac
comp-Sup NatCode ZeroEl c () ac
comp-Sup NatCode (SucEl h) c () ac
comp-Sup ZeroEl Bot c ab ac = ac
comp-Sup ZeroEl ZeroEl Bot ab ac = tt
comp-Sup ZeroEl ZeroEl UCode ab ac = tt
comp-Sup ZeroEl ZeroEl (FunEl j) ab ac = tt
comp-Sup ZeroEl ZeroEl (PiCode e j) ab ac = tt
comp-Sup ZeroEl ZeroEl NatCode ab ac = tt
comp-Sup ZeroEl ZeroEl ZeroEl ab ac = tt
comp-Sup ZeroEl ZeroEl (SucEl j) ab ac = tt
comp-Sup ZeroEl UCode c () ac
comp-Sup ZeroEl (FunEl h) c () ac
comp-Sup ZeroEl (PiCode d k) c () ac
comp-Sup ZeroEl NatCode c () ac
comp-Sup ZeroEl (SucEl h) c () ac
comp-Sup (SucEl a) Bot c ab ac = ac
comp-Sup (SucEl a) (SucEl b) Bot ab ac = ab
comp-Sup (SucEl a) (SucEl b) UCode ab ac = tt
comp-Sup (SucEl a) (SucEl b) (FunEl j) ab ac = tt
comp-Sup (SucEl a) (SucEl b) (PiCode e j) ab ac = tt
comp-Sup (SucEl a) (SucEl b) NatCode ab ac = tt
comp-Sup (SucEl a) (SucEl b) ZeroEl ab ac = tt
comp-Sup (SucEl a) (SucEl b) (SucEl c) ab ac = comp-Sup a b c ab ac
comp-Sup (SucEl a) UCode c () ac
comp-Sup (SucEl a) (FunEl h) c () ac
comp-Sup (SucEl a) (PiCode d k) c () ac
comp-Sup (SucEl a) NatCode c () ac
comp-Sup (SucEl a) ZeroEl c () ac

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
  Comp-sym Bot NatCode c = tt
  Comp-sym Bot ZeroEl c = tt
  Comp-sym Bot (SucEl v) c = tt
  Comp-sym UCode NatCode ()
  Comp-sym UCode ZeroEl ()
  Comp-sym UCode (SucEl v) ()
  Comp-sym (FunEl g) NatCode ()
  Comp-sym (FunEl g) ZeroEl ()
  Comp-sym (FunEl g) (SucEl v) ()
  Comp-sym (PiCode a f) NatCode ()
  Comp-sym (PiCode a f) ZeroEl ()
  Comp-sym (PiCode a f) (SucEl v) ()
  Comp-sym NatCode Bot c = tt
  Comp-sym NatCode UCode ()
  Comp-sym NatCode (FunEl h) ()
  Comp-sym NatCode (PiCode b g) ()
  Comp-sym NatCode NatCode c = tt
  Comp-sym NatCode ZeroEl ()
  Comp-sym NatCode (SucEl v) ()
  Comp-sym ZeroEl Bot c = tt
  Comp-sym ZeroEl UCode ()
  Comp-sym ZeroEl (FunEl h) ()
  Comp-sym ZeroEl (PiCode b g) ()
  Comp-sym ZeroEl NatCode ()
  Comp-sym ZeroEl ZeroEl c = tt
  Comp-sym ZeroEl (SucEl v) ()
  Comp-sym (SucEl u) Bot c = tt
  Comp-sym (SucEl u) UCode ()
  Comp-sym (SucEl u) (FunEl h) ()
  Comp-sym (SucEl u) (PiCode b g) ()
  Comp-sym (SucEl u) NatCode ()
  Comp-sym (SucEl u) ZeroEl ()
  Comp-sym (SucEl u) (SucEl v) c = Comp-sym u v c

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
  Comp-refl NatCode coh = tt
  Comp-refl ZeroEl coh = tt
  Comp-refl (SucEl v) coh = Comp-refl v coh

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
NotBot-Sup-Comp UCode NatCode nb ()
NotBot-Sup-Comp UCode ZeroEl nb ()
NotBot-Sup-Comp UCode (SucEl v) nb ()
NotBot-Sup-Comp (FunEl g) NatCode nb ()
NotBot-Sup-Comp (FunEl g) ZeroEl nb ()
NotBot-Sup-Comp (FunEl g) (SucEl v) nb ()
NotBot-Sup-Comp (PiCode a f) NatCode nb ()
NotBot-Sup-Comp (PiCode a f) ZeroEl nb ()
NotBot-Sup-Comp (PiCode a f) (SucEl v) nb ()
NotBot-Sup-Comp NatCode Bot nb c = tt
NotBot-Sup-Comp NatCode UCode nb ()
NotBot-Sup-Comp NatCode (FunEl h) nb ()
NotBot-Sup-Comp NatCode (PiCode b g) nb ()
NotBot-Sup-Comp NatCode NatCode nb c = tt
NotBot-Sup-Comp NatCode ZeroEl nb ()
NotBot-Sup-Comp NatCode (SucEl v) nb ()
NotBot-Sup-Comp ZeroEl Bot nb c = tt
NotBot-Sup-Comp ZeroEl UCode nb ()
NotBot-Sup-Comp ZeroEl (FunEl h) nb ()
NotBot-Sup-Comp ZeroEl (PiCode b g) nb ()
NotBot-Sup-Comp ZeroEl NatCode nb ()
NotBot-Sup-Comp ZeroEl ZeroEl nb c = tt
NotBot-Sup-Comp ZeroEl (SucEl v) nb ()
NotBot-Sup-Comp (SucEl u) Bot nb c = tt
NotBot-Sup-Comp (SucEl u) UCode nb ()
NotBot-Sup-Comp (SucEl u) (FunEl h) nb ()
NotBot-Sup-Comp (SucEl u) (PiCode b g) nb ()
NotBot-Sup-Comp (SucEl u) NatCode nb ()
NotBot-Sup-Comp (SucEl u) ZeroEl nb ()
NotBot-Sup-Comp (SucEl u) (SucEl v) nb c = tt

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
Sup-assoc UCode UCode NatCode cab ()
Sup-assoc UCode UCode ZeroEl cab ()
Sup-assoc UCode UCode (SucEl j) cab ()
Sup-assoc UCode NatCode c () cbc
Sup-assoc UCode ZeroEl c () cbc
Sup-assoc UCode (SucEl h) c () cbc
Sup-assoc (FunEl g) (FunEl h) NatCode cab ()
Sup-assoc (FunEl g) (FunEl h) ZeroEl cab ()
Sup-assoc (FunEl g) (FunEl h) (SucEl j) cab ()
Sup-assoc (FunEl g) NatCode c () cbc
Sup-assoc (FunEl g) ZeroEl c () cbc
Sup-assoc (FunEl g) (SucEl h) c () cbc
Sup-assoc (PiCode a f) (PiCode d h) NatCode cab ()
Sup-assoc (PiCode a f) (PiCode d h) ZeroEl cab ()
Sup-assoc (PiCode a f) (PiCode d h) (SucEl j) cab ()
Sup-assoc (PiCode a f) NatCode c () cbc
Sup-assoc (PiCode a f) ZeroEl c () cbc
Sup-assoc (PiCode a f) (SucEl h) c () cbc
Sup-assoc NatCode Bot c cab cbc = refl
Sup-assoc NatCode NatCode Bot cab cbc = refl
Sup-assoc NatCode NatCode UCode cab ()
Sup-assoc NatCode NatCode (FunEl j) cab ()
Sup-assoc NatCode NatCode (PiCode e j) cab ()
Sup-assoc NatCode NatCode NatCode cab cbc = refl
Sup-assoc NatCode NatCode ZeroEl cab ()
Sup-assoc NatCode NatCode (SucEl j) cab ()
Sup-assoc NatCode UCode c () cbc
Sup-assoc NatCode (FunEl h) c () cbc
Sup-assoc NatCode (PiCode d k) c () cbc
Sup-assoc NatCode ZeroEl c () cbc
Sup-assoc NatCode (SucEl h) c () cbc
Sup-assoc ZeroEl Bot c cab cbc = refl
Sup-assoc ZeroEl ZeroEl Bot cab cbc = refl
Sup-assoc ZeroEl ZeroEl UCode cab ()
Sup-assoc ZeroEl ZeroEl (FunEl j) cab ()
Sup-assoc ZeroEl ZeroEl (PiCode e j) cab ()
Sup-assoc ZeroEl ZeroEl NatCode cab ()
Sup-assoc ZeroEl ZeroEl ZeroEl cab cbc = refl
Sup-assoc ZeroEl ZeroEl (SucEl j) cab ()
Sup-assoc ZeroEl UCode c () cbc
Sup-assoc ZeroEl (FunEl h) c () cbc
Sup-assoc ZeroEl (PiCode d k) c () cbc
Sup-assoc ZeroEl NatCode c () cbc
Sup-assoc ZeroEl (SucEl h) c () cbc
Sup-assoc (SucEl a) Bot c cab cbc = refl
Sup-assoc (SucEl a) (SucEl b) Bot cab cbc = refl
Sup-assoc (SucEl a) (SucEl b) UCode cab ()
Sup-assoc (SucEl a) (SucEl b) (FunEl j) cab ()
Sup-assoc (SucEl a) (SucEl b) (PiCode e j) cab ()
Sup-assoc (SucEl a) (SucEl b) NatCode cab ()
Sup-assoc (SucEl a) (SucEl b) ZeroEl cab ()
Sup-assoc (SucEl a) (SucEl b) (SucEl c) cab cbc = Eq-cong SucEl (Sup-assoc a b c cab cbc)
Sup-assoc (SucEl a) UCode c () cbc
Sup-assoc (SucEl a) (FunEl h) c () cbc
Sup-assoc (SucEl a) (PiCode d k) c () cbc
Sup-assoc (SucEl a) NatCode c () cbc
Sup-assoc (SucEl a) ZeroEl c () cbc

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
  Coherent-Sup UCode NatCode () coha cohb
  Coherent-Sup UCode ZeroEl () coha cohb
  Coherent-Sup UCode (SucEl c) () coha cohb
  Coherent-Sup (FunEl g) NatCode () coha cohb
  Coherent-Sup (FunEl g) ZeroEl () coha cohb
  Coherent-Sup (FunEl g) (SucEl c) () coha cohb
  Coherent-Sup (PiCode a f) NatCode () coha cohb
  Coherent-Sup (PiCode a f) ZeroEl () coha cohb
  Coherent-Sup (PiCode a f) (SucEl c) () coha cohb
  Coherent-Sup NatCode Bot comp coha cohb = tt
  Coherent-Sup NatCode UCode () coha cohb
  Coherent-Sup NatCode (FunEl h) () coha cohb
  Coherent-Sup NatCode (PiCode c h) () coha cohb
  Coherent-Sup NatCode NatCode comp coha cohb = tt
  Coherent-Sup NatCode ZeroEl () coha cohb
  Coherent-Sup NatCode (SucEl c) () coha cohb
  Coherent-Sup ZeroEl Bot comp coha cohb = tt
  Coherent-Sup ZeroEl UCode () coha cohb
  Coherent-Sup ZeroEl (FunEl h) () coha cohb
  Coherent-Sup ZeroEl (PiCode c h) () coha cohb
  Coherent-Sup ZeroEl NatCode () coha cohb
  Coherent-Sup ZeroEl ZeroEl comp coha cohb = tt
  Coherent-Sup ZeroEl (SucEl c) () coha cohb
  Coherent-Sup (SucEl a) Bot comp coha cohb = coha
  Coherent-Sup (SucEl a) UCode () coha cohb
  Coherent-Sup (SucEl a) (FunEl h) () coha cohb
  Coherent-Sup (SucEl a) (PiCode c h) () coha cohb
  Coherent-Sup (SucEl a) NatCode () coha cohb
  Coherent-Sup (SucEl a) ZeroEl () coha cohb
  Coherent-Sup (SucEl a) (SucEl b) comp coha cohb = Coherent-Sup a b comp coha cohb

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
