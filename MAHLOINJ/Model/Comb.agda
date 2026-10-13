{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Model/Comb.agda
--
-- Semantic combinators on approximation predicates  P : FinEl -> Set
-- ("u is a finite approximant of the denotation"), and their ideal
-- properties, proved ONCE generically.  The relational semantics
-- (Model/Eval) is assembled from these, so e.g. fhat/ghat (iterated
-- applications) and V / U(f,g) (the code UCode) need no separate
-- proofs.
--
--   Guard u X   : Top at u = Bot, X otherwise
--   AppS P Q    : application  (P function, Q argument)
--
-- An Ideal is a predicate that is coherent, contains Bot, is downward
-- closed, pairwise compatible and closed under Sup.
------------------------------------------------------------------------

module MAHLOINJ.Model.Comb where

open import MAHLOINJ.Domain.Basic
  using ( Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ; Sigma
        ; Eq ; refl ; Eq-transport ; Eq-sym
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl
        ; PairEl ; SigmaCode ; FinFun ; nil ; cons )
open import MAHLOINJ.Domain.Kernel
open import MAHLOINJ.Model.Selection

------------------------------------------------------------------------
-- Bot / non-Bot
------------------------------------------------------------------------

bot-or : (u : FinEl) -> Or (Eq u Bot) (NotBot u)
bot-or Bot             = left refl
bot-or UCode           = right tt
bot-or (FunEl g)       = right tt
bot-or (PiCode a f)    = right tt
bot-or NatCode         = right tt
bot-or ZeroEl          = right tt
bot-or (SucEl a)       = right tt
bot-or (PairEl a b)    = right tt
bot-or (SigmaCode a f) = right tt

Empty-elim : {A : Set} -> Empty -> A
Empty-elim ()

------------------------------------------------------------------------
-- Guard
------------------------------------------------------------------------

Guard : FinEl -> Set -> Set
Guard Bot             X = Top
Guard UCode           X = X
Guard (FunEl g)       X = X
Guard (PiCode a f)    X = X
Guard NatCode         X = X
Guard ZeroEl          X = X
Guard (SucEl a)       X = X
Guard (PairEl a b)    X = X
Guard (SigmaCode a f) X = X

guard-intro : (u : FinEl) {X : Set} -> NotBot u -> X -> Guard u X
guard-intro Bot             () x
guard-intro UCode           nb x = x
guard-intro (FunEl g)       nb x = x
guard-intro (PiCode a f)    nb x = x
guard-intro NatCode         nb x = x
guard-intro ZeroEl          nb x = x
guard-intro (SucEl a)       nb x = x
guard-intro (PairEl a b)    nb x = x
guard-intro (SigmaCode a f) nb x = x

guard-build : (u : FinEl) {X : Set} -> (NotBot u -> X) -> Guard u X
guard-build Bot             h = tt
guard-build UCode           h = h tt
guard-build (FunEl _)       h = h tt
guard-build (PiCode _ _)    h = h tt
guard-build NatCode         h = h tt
guard-build ZeroEl          h = h tt
guard-build (SucEl _)       h = h tt
guard-build (PairEl _ _)    h = h tt
guard-build (SigmaCode _ _) h = h tt

guard-elim : (u : FinEl) {X : Set} -> NotBot u -> Guard u X -> X
guard-elim Bot             () g
guard-elim UCode           nb g = g
guard-elim (FunEl _)       nb g = g
guard-elim (PiCode _ _)    nb g = g
guard-elim NatCode         nb g = g
guard-elim ZeroEl          nb g = g
guard-elim (SucEl _)       nb g = g
guard-elim (PairEl _ _)    nb g = g
guard-elim (SigmaCode _ _) nb g = g

guard-map : (u : FinEl) {X Y : Set} -> (NotBot u -> X -> Y) -> Guard u X -> Guard u Y
guard-map Bot             h g = tt
guard-map UCode           h g = h tt g
guard-map (FunEl _)       h g = h tt g
guard-map (PiCode _ _)    h g = h tt g
guard-map NatCode         h g = h tt g
guard-map ZeroEl          h g = h tt g
guard-map (SucEl _)       h g = h tt g
guard-map (PairEl _ _)    h g = h tt g
guard-map (SigmaCode _ _) h g = h tt g

------------------------------------------------------------------------
-- Ideals
------------------------------------------------------------------------

Pred : Set1
Pred = FinEl -> Set

record Ideal (P : Pred) : Set where
  field
    coh  : (u : FinEl) -> P u -> Coherent u
    bot  : P Bot
    down : (u u' : FinEl) -> P u -> Coherent u' -> LeCode u' u -> P u'
    comp : (u v : FinEl) -> P u -> P v -> Comp u v
    sup  : (u v : FinEl) -> P u -> P v -> P (Sup u v)

------------------------------------------------------------------------
-- small domain facts
------------------------------------------------------------------------

NotBot-from-Le : (u v : FinEl) -> NotBot u -> LeCode u v -> NotBot v
NotBot-from-Le Bot             v               () le
NotBot-from-Le UCode           UCode           nb le = tt
NotBot-from-Le (FunEl _)       (FunEl _)       nb le = tt
NotBot-from-Le (PiCode _ _)    (PiCode _ _)    nb le = tt
NotBot-from-Le NatCode         NatCode         nb le = tt
NotBot-from-Le ZeroEl          ZeroEl          nb le = tt
NotBot-from-Le (SucEl _)       (SucEl _)       nb le = tt
NotBot-from-Le (PairEl _ _)    (PairEl _ _)    nb le = tt
NotBot-from-Le (SigmaCode _ _) (SigmaCode _ _) nb le = tt

NotBot-Sup-l : (u v : FinEl) -> NotBot u -> Comp u v -> NotBot (Sup u v)
NotBot-Sup-l = NotBot-Sup-Comp

LeBot-is-Bot : (u : FinEl) -> LeCode u Bot -> Eq u Bot
LeBot-is-Bot Bot le = refl

-- singleton functions
sing : FinEl -> FinEl -> FinEl
sing v u = FunEl (cons (mkSigma v u) nil)

sing-coh : (v u : FinEl) -> Coherent v -> Coherent u -> NotBot u -> Coherent (sing v u)
sing-coh v u cv cu nb = mkCFT cv cu nb tt tt

sing-val-coh : (v u : FinEl) -> Coherent (sing v u) -> Coherent u
sing-val-coh v u c = CFTcons.val-coh c

sing-key-coh : (v u : FinEl) -> Coherent (sing v u) -> Coherent v
sing-key-coh v u c = CFTcons.key-coh c

-- EvalFun of a singleton at an argument above the key
sing-EvalFun : (v u x : FinEl) -> Coherent (sing v u) -> Coherent x -> LeCode v x ->
  LeCode u (EvalFun (cons (mkSigma v u) nil) x)
sing-EvalFun v u x c cx le =
  let sel = singleton-selection (mkSigma v u) (cons (mkSigma v u) nil) here
      lf  = LeFunCode-refl (cons (mkSigma v u) nil) c
      cv  = CFTcons.key-coh c
      cu  = CFTcons.val-coh c
      cvb = Eq-transport Coherent (Eq-sym (Sup-Bot-r v)) cv
      le0 = Selection-le-EvalFun (cons (mkSigma v u) nil) sel lf c c cvb
      le1 = Eq-transport (\ z -> LeCode z (EvalFun (cons (mkSigma v u) nil) (Sup v Bot)))
              (Sup-Bot-r u) le0
      le2 = Eq-transport (\ z -> LeCode u (EvalFun (cons (mkSigma v u) nil) z))
              (Sup-Bot-r v) le1
      mon = EvalFun-mon-arg (cons (mkSigma v u) nil) v x le c cv cx
  in LeCode-trans u (EvalFun (cons (mkSigma v u) nil) v) (EvalFun (cons (mkSigma v u) nil) x)
       cu (Coherent-EvalFun (cons (mkSigma v u) nil) v c cv)
       (Coherent-EvalFun (cons (mkSigma v u) nil) x c cx) le2 mon

-- {v |-> u'} <= {v |-> u}  when u' <= u
sing-le-val : (v u u' : FinEl) -> Coherent (sing v u) -> Coherent u' -> LeCode u' u ->
  LeCode (sing v u') (sing v u)
sing-le-val v u u' c cu' le =
  mkSigma (LeCode-trans u' u (EvalFun (cons (mkSigma v u) nil) v)
             cu' (CFTcons.val-coh c)
             (Coherent-EvalFun (cons (mkSigma v u) nil) v c (CFTcons.key-coh c))
             le (sing-EvalFun v u v c (CFTcons.key-coh c) (LeCode-refl v (CFTcons.key-coh c))))
          tt

-- {Sup v1 v2 |-> Sup u1 u2} <= {v1 |-> u1, v2 |-> u2}
LeFunCode-Sup-pair :
  (v1 u1 v2 u2 : FinEl) ->
  Comp v1 v2 -> Comp u1 u2 ->
  CoherentFun (cons (mkSigma v1 u1) (cons (mkSigma v2 u2) nil)) ->
  Coherent (Sup v1 v2) ->
  LeFunCode (cons (mkSigma (Sup v1 v2) (Sup u1 u2)) nil)
            (cons (mkSigma v1 u1) (cons (mkSigma v2 u2) nil))
LeFunCode-Sup-pair v1 u1 v2 u2 comp-v comp-u cf c-supv =
  let sel-inner = sel-take (comp-Bot-r v2) (comp-Bot-r u2) (sel-skip-all nil)
      comp-v1-sv2 = Eq-transport (Comp v1) (Eq-sym (Sup-Bot-r v2)) comp-v
      comp-u1-su2 = Eq-transport (Comp u1) (Eq-sym (Sup-Bot-r u2)) comp-u
      sel-both = sel-take comp-v1-sv2 comp-u1-su2 sel-inner
      eq-key = Eq-transport (\ z -> Eq (Sup v1 (Sup v2 Bot)) (Sup v1 z)) (Sup-Bot-r v2) refl
      eq-val = Eq-transport (\ z -> Eq (Sup u1 (Sup u2 Bot)) (Sup u1 z)) (Sup-Bot-r u2) refl
      g2 = cons (mkSigma v1 u1) (cons (mkSigma v2 u2) nil)
      ctf = cft-from-cf g2 cf
      lf-refl = LeFunCode-refl g2 ctf
      c-key = Eq-transport Coherent (Eq-sym eq-key) c-supv
      le-raw = Selection-le-EvalFun g2 sel-both lf-refl cf cf c-key
      le-trans = Eq-transport (\ z -> LeCode z (EvalFun g2 (Sup v1 (Sup v2 Bot)))) eq-val le-raw
      le-result = Eq-transport (\ z -> LeCode (Sup u1 u2) (EvalFun g2 z)) eq-key le-trans
  in mkSigma le-result tt

------------------------------------------------------------------------
-- Application
------------------------------------------------------------------------

AppBody : Pred -> Pred -> FinEl -> Set
AppBody P Q u = Sigma FinEl (\ v -> Pair (Q v) (P (sing v u)))

AppS : Pred -> Pred -> Pred
AppS P Q u = Guard u (AppBody P Q u)

AppS-bot : (P Q : Pred) -> AppS P Q Bot
AppS-bot P Q = tt

AppS-map : (P P' Q Q' : Pred) -> ((u : FinEl) -> P u -> P' u) -> ((u : FinEl) -> Q u -> Q' u) ->
  (u : FinEl) -> AppS P Q u -> AppS P' Q' u
AppS-map P P' Q Q' hp hq u =
  guard-map u (\ nb b -> mkSigma (fst b) (mkSigma (hq (fst b) (fst (snd b)))
                                                  (hp (sing (fst b) u) (snd (snd b)))))

AppS-coh : (P Q : Pred) -> Ideal P -> (u : FinEl) -> AppS P Q u -> Coherent u
AppS-coh P Q iP u ev = go (bot-or u)
  where
    go : Or (Eq u Bot) (NotBot u) -> Coherent u
    go (left e) = Eq-transport Coherent (Eq-sym e) tt
    go (right nb) =
      let b = guard-elim u nb ev
      in sing-val-coh (fst b) u (Ideal.coh iP (sing (fst b) u) (snd (snd b)))

AppS-down : (P Q : Pred) -> Ideal P -> Ideal Q ->
  (u u' : FinEl) -> AppS P Q u -> Coherent u' -> LeCode u' u -> AppS P Q u'
AppS-down P Q iP iQ u u' ev cu' le = go (bot-or u')
  where
    go : Or (Eq u' Bot) (NotBot u') -> AppS P Q u'
    go (left e) = Eq-transport (AppS P Q) (Eq-sym e) tt
    go (right nb') =
      let nb = NotBot-from-Le u' u nb' le
          b  = guard-elim u nb ev
          v  = fst b
          cs = Ideal.coh iP (sing v u) (snd (snd b))
      in guard-intro u' nb'
           (mkSigma v (mkSigma (fst (snd b))
              (Ideal.down iP (sing v u) (sing v u') (snd (snd b))
                 (sing-coh v u' (sing-key-coh v u cs) cu' nb')
                 (sing-le-val v u u' cs cu' le))))

AppS-comp : (P Q : Pred) -> Ideal P -> Ideal Q ->
  (u1 u2 : FinEl) -> AppS P Q u1 -> AppS P Q u2 -> Comp u1 u2
AppS-comp P Q iP iQ u1 u2 e1 e2 = go (bot-or u1) (bot-or u2)
  where
    go : Or (Eq u1 Bot) (NotBot u1) -> Or (Eq u2 Bot) (NotBot u2) -> Comp u1 u2
    go (left e) o = Eq-transport (\ z -> Comp z u2) (Eq-sym e) (comp-Bot-l u2)
    go (right nb) (left e) = Eq-transport (Comp u1) (Eq-sym e) (comp-Bot-r u1)
    go (right nb1) (right nb2) =
      let b1 = guard-elim u1 nb1 e1
          b2 = guard-elim u2 nb2 e2
          cf = Ideal.comp iP (sing (fst b1) u1) (sing (fst b2) u2) (snd (snd b1)) (snd (snd b2))
          cv = Ideal.comp iQ (fst b1) (fst b2) (fst (snd b1)) (fst (snd b2))
      in fst (fst cf) cv

AppS-sup : (P Q : Pred) -> Ideal P -> Ideal Q ->
  (u1 u2 : FinEl) -> AppS P Q u1 -> AppS P Q u2 -> AppS P Q (Sup u1 u2)
AppS-sup P Q iP iQ u1 u2 e1 e2 = go (bot-or u1) (bot-or u2)
  where
    go : Or (Eq u1 Bot) (NotBot u1) -> Or (Eq u2 Bot) (NotBot u2) -> AppS P Q (Sup u1 u2)
    go (left refl) o = e2
    go (right nb) (left refl) = Eq-transport (AppS P Q) (Eq-sym (Sup-Bot-r u1)) e1
    go (right nb1) (right nb2) =
      let b1 = guard-elim u1 nb1 e1
          b2 = guard-elim u2 nb2 e2
          v1 = fst b1 ; v2 = fst b2
          p1 = snd (snd b1) ; p2 = snd (snd b2)
          q1 = fst (snd b1) ; q2 = fst (snd b2)
          cuv = AppS-comp P Q iP iQ u1 u2 e1 e2
          cvv = Ideal.comp iQ v1 v2 q1 q2
          cs1 = Ideal.coh iP (sing v1 u1) p1
          cs2 = Ideal.coh iP (sing v2 u2) p2
          psup = Ideal.sup iP (sing v1 u1) (sing v2 u2) p1 p2
          cpsup = Ideal.coh iP _ psup
          cv1 = sing-key-coh v1 u1 cs1 ; cv2 = sing-key-coh v2 u2 cs2
          cu1 = sing-val-coh v1 u1 cs1 ; cu2 = sing-val-coh v2 u2 cs2
          csv = Coherent-Sup v1 v2 cvv cv1 cv2
          csu = Coherent-Sup u1 u2 cuv cu1 cu2
          nbs = NotBot-Sup-l u1 u2 nb1 cuv
          lef = LeFunCode-Sup-pair v1 u1 v2 u2 cvv cuv cpsup csv
      in guard-intro (Sup u1 u2) nbs
           (mkSigma (Sup v1 v2)
             (mkSigma (Ideal.sup iQ v1 v2 q1 q2)
               (Ideal.down iP _ (sing (Sup v1 v2) (Sup u1 u2)) psup
                  (sing-coh (Sup v1 v2) (Sup u1 u2) csv csu nbs) lef)))

AppS-ideal : (P Q : Pred) -> Ideal P -> Ideal Q -> Ideal (AppS P Q)
AppS-ideal P Q iP iQ = record
  { coh  = AppS-coh P Q iP
  ; bot  = tt
  ; down = AppS-down P Q iP iQ
  ; comp = AppS-comp P Q iP iQ
  ; sup  = AppS-sup P Q iP iQ }

------------------------------------------------------------------------
-- misc
------------------------------------------------------------------------

Comp-mono : (u v w1 w2 : FinEl) ->
  Coherent u -> Coherent v -> Coherent w1 -> Coherent w2 ->
  LeCode u w1 -> LeCode v w2 -> Comp w1 w2 -> Comp u v
Comp-mono u v w1 w2 cu cv cw1 cw2 le1 le2 comp =
  let c-sup = Coherent-Sup w1 w2 comp cw1 cw2
      le-w1 = LeCode-Sup-left w1 w2 comp cw1 cw2
      le-w2 = LeCode-Sup-right w1 w2 comp cw1 cw2
      le-u  = LeCode-trans u w1 (Sup w1 w2) cu cw1 c-sup le1 le-w1
      le-v  = LeCode-trans v w2 (Sup w1 w2) cv cw2 c-sup le2 le-w2
  in LeCode-Comp u v (Sup w1 w2) c-sup le-u le-v

append-nil-r : (f : FinFun) -> Eq (append f nil) f
append-nil-r nil = refl
append-nil-r (cons p ps) = cons-eq' (append-nil-r ps)
  where
    cons-eq' : {xs ys : FinFun} -> Eq xs ys -> Eq (cons p xs) (cons p ys)
    cons-eq' refl = refl

CompFun-nil-r : (f : FinFun) -> CompFun f nil
CompFun-nil-r nil = tt
CompFun-nil-r (cons p ps) = mkSigma tt (CompFun-nil-r ps)

-- a coherent non-empty function is never below the empty one
cft-not-le-nil : (p : Pair FinEl FinEl) (ps : FinFun) ->
  CoherentFunTail (cons p ps) -> LeFunCode (cons p ps) nil -> Empty
cft-not-le-nil p ps c le = val-not-bot (snd p) (CFTcons.val-nbot c) (fst le)
  where
    val-not-bot : (v : FinEl) -> NotBot v -> LeCode v Bot -> Empty
    val-not-bot Bot () le

------------------------------------------------------------------------
-- Atoms: U, Nat, 0
------------------------------------------------------------------------

AtomS : FinEl -> Pred
AtomS c b = Pair (Coherent b) (LeCode b c)

AtomS-ideal : (c : FinEl) -> Coherent c -> Ideal (AtomS c)
AtomS-ideal c cc = record
  { coh  = \ u e -> fst e
  ; bot  = mkSigma tt tt
  ; down = \ u u' e cu' le -> mkSigma cu' (LeCode-trans u' u c cu' (fst e) cc le (snd e))
  ; comp = \ u v eu ev -> LeCode-Comp u v c cc (snd eu) (snd ev)
  ; sup  = \ u v eu ev ->
      mkSigma (Coherent-Sup u v (LeCode-Comp u v c cc (snd eu) (snd ev)) (fst eu) (fst ev))
              (LeCode-Sup-lub u v c (snd eu) (snd ev)) }

------------------------------------------------------------------------
-- Successor
------------------------------------------------------------------------

SucS : Pred -> Pred
SucS P b = Pair (Coherent b) (Sigma FinEl (\ v -> Pair (P v) (LeCode b (SucEl v))))

SucS-map : (P P' : Pred) -> ((u : FinEl) -> P u -> P' u) -> (u : FinEl) -> SucS P u -> SucS P' u
SucS-map P P' h u e = mkSigma (fst e) (mkSigma (fst (snd e))
                        (mkSigma (h _ (fst (snd (snd e)))) (snd (snd (snd e)))))

SucS-ideal : (P : Pred) -> Ideal P -> Ideal (SucS P)
SucS-ideal P iP = record
  { coh  = \ u e -> fst e
  ; bot  = mkSigma tt (mkSigma Bot (mkSigma (Ideal.bot iP) tt))
  ; down = \ u u' e cu' le ->
      let v = fst (snd e) ; cv = Ideal.coh iP v (fst (snd (snd e)))
      in mkSigma cu' (mkSigma v (mkSigma (fst (snd (snd e)))
           (LeCode-trans u' u (SucEl v) cu' (fst e) cv le (snd (snd (snd e))))))
  ; comp = \ u w eu ew ->
      let v1 = fst (snd eu) ; v2 = fst (snd ew)
          p1 = fst (snd (snd eu)) ; p2 = fst (snd (snd ew))
      in Comp-mono u w (SucEl v1) (SucEl v2) (fst eu) (fst ew)
           (Ideal.coh iP v1 p1) (Ideal.coh iP v2 p2)
           (snd (snd (snd eu))) (snd (snd (snd ew))) (Ideal.comp iP v1 v2 p1 p2)
  ; sup  = \ u w eu ew ->
      let v1 = fst (snd eu) ; v2 = fst (snd ew)
          p1 = fst (snd (snd eu)) ; p2 = fst (snd (snd ew))
          cv1 = Ideal.coh iP v1 p1 ; cv2 = Ideal.coh iP v2 p2
          cvv = Ideal.comp iP v1 v2 p1 p2
          csv = Coherent-Sup v1 v2 cvv cv1 cv2
          cuw = Comp-mono u w (SucEl v1) (SucEl v2) (fst eu) (fst ew) cv1 cv2
                  (snd (snd (snd eu))) (snd (snd (snd ew))) cvv
          l1 = LeCode-trans u (SucEl v1) (SucEl (Sup v1 v2)) (fst eu) cv1 csv
                 (snd (snd (snd eu))) (LeCode-Sup-left v1 v2 cvv cv1 cv2)
          l2 = LeCode-trans w (SucEl v2) (SucEl (Sup v1 v2)) (fst ew) cv2 csv
                 (snd (snd (snd ew))) (LeCode-Sup-right v1 v2 cvv cv1 cv2)
      in mkSigma (Coherent-Sup u w cuw (fst eu) (fst ew))
           (mkSigma (Sup v1 v2) (mkSigma (Ideal.sup iP v1 v2 p1 p2)
             (LeCode-Sup-lub u w (SucEl (Sup v1 v2)) l1 l2))) }

------------------------------------------------------------------------
-- Pairs
------------------------------------------------------------------------

PairS : Pred -> Pred -> Pred
PairS P Q Bot             = Top
PairS P Q UCode           = Empty
PairS P Q (FunEl _)       = Empty
PairS P Q (PiCode _ _)    = Empty
PairS P Q NatCode         = Empty
PairS P Q ZeroEl          = Empty
PairS P Q (SucEl _)       = Empty
PairS P Q (PairEl a b)    = Pair (Coherent (PairEl a b)) (Pair (P a) (Q b))
PairS P Q (SigmaCode _ _) = Empty

PairS-map : (P P' Q Q' : Pred) -> ((u : FinEl) -> P u -> P' u) -> ((u : FinEl) -> Q u -> Q' u) ->
  (u : FinEl) -> PairS P Q u -> PairS P' Q' u
PairS-map P P' Q Q' hp hq Bot e = tt
PairS-map P P' Q Q' hp hq (PairEl a b) e =
  mkSigma (fst e) (mkSigma (hp a (fst (snd e))) (hq b (snd (snd e))))

PairS-ideal : (P Q : Pred) -> Ideal P -> Ideal Q -> Ideal (PairS P Q)
PairS-ideal P Q iP iQ = record
  { coh = coh' ; bot = tt ; down = down' ; comp = comp' ; sup = sup' }
  where
    coh' : (u : FinEl) -> PairS P Q u -> Coherent u
    coh' Bot e = tt
    coh' (PairEl a b) e = fst e
    down' : (u u' : FinEl) -> PairS P Q u -> Coherent u' -> LeCode u' u -> PairS P Q u'
    down' Bot Bot e cu' le = tt
    down' (PairEl a b) Bot e cu' le = tt
    down' (PairEl a b) (PairEl a' b') e cu' le =
      mkSigma cu' (mkSigma (Ideal.down iP a a' (fst (snd e)) (fst cu') (fst le))
                           (Ideal.down iQ b b' (snd (snd e)) (fst (snd cu')) (snd le)))
    comp' : (u v : FinEl) -> PairS P Q u -> PairS P Q v -> Comp u v
    comp' Bot v e1 e2 = comp-Bot-l v
    comp' (PairEl a b) Bot e1 e2 = tt
    comp' (PairEl a b) (PairEl a' b') e1 e2 =
      mkSigma (Ideal.comp iP a a' (fst (snd e1)) (fst (snd e2)))
              (Ideal.comp iQ b b' (snd (snd e1)) (snd (snd e2)))
    sup' : (u v : FinEl) -> PairS P Q u -> PairS P Q v -> PairS P Q (Sup u v)
    sup' Bot v e1 e2 = e2
    sup' (PairEl a b) Bot e1 e2 = e1
    sup' (PairEl a b) (PairEl a' b') e1 e2 =
      let c = comp' (PairEl a b) (PairEl a' b') e1 e2
      in mkSigma (Coherent-Sup (PairEl a b) (PairEl a' b') c (fst e1) (fst e2))
           (mkSigma (Ideal.sup iP a a' (fst (snd e1)) (fst (snd e2)))
                    (Ideal.sup iQ b b' (snd (snd e1)) (snd (snd e2))))

------------------------------------------------------------------------
-- Projections
------------------------------------------------------------------------

FstS : Pred -> Pred
FstS P u = Guard u (P (PairEl u Bot))

SndS : Pred -> Pred
SndS P v = Guard v (P (PairEl Bot v))

FstS-map : (P P' : Pred) -> ((u : FinEl) -> P u -> P' u) -> (u : FinEl) -> FstS P u -> FstS P' u
FstS-map P P' h u = guard-map u (\ nb e -> h _ e)

SndS-map : (P P' : Pred) -> ((u : FinEl) -> P u -> P' u) -> (u : FinEl) -> SndS P u -> SndS P' u
SndS-map P P' h u = guard-map u (\ nb e -> h _ e)

pairNB-l : (u : FinEl) -> NotBot u -> PairNB u Bot
pairNB-l u nb = PairNB-intro1 u Bot nb

FstS-ideal : (P : Pred) -> Ideal P -> Ideal (FstS P)
FstS-ideal P iP = record { coh = coh' ; bot = tt ; down = down' ; comp = comp' ; sup = sup' }
  where
    coh' : (u : FinEl) -> FstS P u -> Coherent u
    coh' u e = go (bot-or u)
      where
        go : Or (Eq u Bot) (NotBot u) -> Coherent u
        go (left refl) = tt
        go (right nb) = fst (Ideal.coh iP (PairEl u Bot) (guard-elim u nb e))
    down' : (u u' : FinEl) -> FstS P u -> Coherent u' -> LeCode u' u -> FstS P u'
    down' u u' e cu' le = go (bot-or u')
      where
        go : Or (Eq u' Bot) (NotBot u') -> FstS P u'
        go (left refl) = tt
        go (right nb') =
          let nb = NotBot-from-Le u' u nb' le
          in guard-intro u' nb'
               (Ideal.down iP (PairEl u Bot) (PairEl u' Bot) (guard-elim u nb e)
                  (mkSigma cu' (mkSigma tt (pairNB-l u' nb'))) (mkSigma le tt))
    comp' : (u v : FinEl) -> FstS P u -> FstS P v -> Comp u v
    comp' u v e1 e2 = go (bot-or u) (bot-or v)
      where
        go : Or (Eq u Bot) (NotBot u) -> Or (Eq v Bot) (NotBot v) -> Comp u v
        go (left refl) o = comp-Bot-l v
        go (right nb) (left refl) = comp-Bot-r u
        go (right nb1) (right nb2) =
          fst (Ideal.comp iP (PairEl u Bot) (PairEl v Bot) (guard-elim u nb1 e1) (guard-elim v nb2 e2))
    sup' : (u v : FinEl) -> FstS P u -> FstS P v -> FstS P (Sup u v)
    sup' u v e1 e2 = go (bot-or u) (bot-or v)
      where
        go : Or (Eq u Bot) (NotBot u) -> Or (Eq v Bot) (NotBot v) -> FstS P (Sup u v)
        go (left refl) o = e2
        go (right nb) (left refl) = Eq-transport (FstS P) (Eq-sym (Sup-Bot-r u)) e1
        go (right nb1) (right nb2) =
          let c = comp' u v e1 e2
          in guard-intro (Sup u v) (NotBot-Sup-l u v nb1 c)
               (Ideal.sup iP (PairEl u Bot) (PairEl v Bot) (guard-elim u nb1 e1) (guard-elim v nb2 e2))

SndS-ideal : (P : Pred) -> Ideal P -> Ideal (SndS P)
SndS-ideal P iP = record { coh = coh' ; bot = tt ; down = down' ; comp = comp' ; sup = sup' }
  where
    coh' : (u : FinEl) -> SndS P u -> Coherent u
    coh' u e = go (bot-or u)
      where
        go : Or (Eq u Bot) (NotBot u) -> Coherent u
        go (left refl) = tt
        go (right nb) = fst (snd (Ideal.coh iP (PairEl Bot u) (guard-elim u nb e)))
    down' : (u u' : FinEl) -> SndS P u -> Coherent u' -> LeCode u' u -> SndS P u'
    down' u u' e cu' le = go (bot-or u')
      where
        go : Or (Eq u' Bot) (NotBot u') -> SndS P u'
        go (left refl) = tt
        go (right nb') =
          let nb = NotBot-from-Le u' u nb' le
          in guard-intro u' nb'
               (Ideal.down iP (PairEl Bot u) (PairEl Bot u') (guard-elim u nb e)
                  (mkSigma tt (mkSigma cu' nb')) (mkSigma tt le))
    comp' : (u v : FinEl) -> SndS P u -> SndS P v -> Comp u v
    comp' u v e1 e2 = go (bot-or u) (bot-or v)
      where
        go : Or (Eq u Bot) (NotBot u) -> Or (Eq v Bot) (NotBot v) -> Comp u v
        go (left refl) o = comp-Bot-l v
        go (right nb) (left refl) = comp-Bot-r u
        go (right nb1) (right nb2) =
          snd (Ideal.comp iP (PairEl Bot u) (PairEl Bot v) (guard-elim u nb1 e1) (guard-elim v nb2 e2))
    sup' : (u v : FinEl) -> SndS P u -> SndS P v -> SndS P (Sup u v)
    sup' u v e1 e2 = go (bot-or u) (bot-or v)
      where
        go : Or (Eq u Bot) (NotBot u) -> Or (Eq v Bot) (NotBot v) -> SndS P (Sup u v)
        go (left refl) o = e2
        go (right nb) (left refl) = Eq-transport (SndS P) (Eq-sym (Sup-Bot-r u)) e1
        go (right nb1) (right nb2) =
          let c = comp' u v e1 e2
          in guard-intro (Sup u v) (NotBot-Sup-l u v nb1 c)
               (Ideal.sup iP (PairEl Bot u) (PairEl Bot v) (guard-elim u nb1 e1) (guard-elim v nb2 e2))

------------------------------------------------------------------------
-- Lambda: a body family  B x v  ("v approximates the body at x")
------------------------------------------------------------------------

record BodyOK (B : FinEl -> Pred) : Set where
  field
    ideal : (x : FinEl) -> Coherent x -> Ideal (B x)
    mon   : (x x' v : FinEl) -> Coherent x -> Coherent x' -> LeCode x x' -> B x v -> B x' v

LamBody : Pred -> (FinEl -> Pred) -> FinFun -> Set
LamBody PA B g =
  Sigma FinEl (\ a ->
    Pair (CoherentFun g)
      (Pair (FinMem a UCode)
        (Pair (PA a)
          ((u v : FinEl) -> Selection g u v ->
            Sigma FinEl (\ x -> Pair (LeCode x u) (Pair (FinMem x a) (B x v)))))))

LamS : Pred -> (FinEl -> Pred) -> Pred
LamS PA B Bot             = Top
LamS PA B UCode           = Empty
LamS PA B (FunEl g)       = LamBody PA B g
LamS PA B (PiCode _ _)    = Empty
LamS PA B NatCode         = Empty
LamS PA B ZeroEl          = Empty
LamS PA B (SucEl _)       = Empty
LamS PA B (PairEl _ _)    = Empty
LamS PA B (SigmaCode _ _) = Empty

LamS-map : (PA PA' : Pred) (B B' : FinEl -> Pred) ->
  ((u : FinEl) -> PA u -> PA' u) -> ((x v : FinEl) -> Coherent x -> B x v -> B' x v) ->
  (u : FinEl) -> LamS PA B u -> LamS PA' B' u
LamS-map PA PA' B B' ha hb Bot e = tt
LamS-map PA PA' B B' ha hb (FunEl g) e =
  let a = fst e ; aU = fst (snd (snd e)) ; body = snd (snd (snd (snd e)))
  in mkSigma a (mkSigma (fst (snd e)) (mkSigma aU (mkSigma (ha a (fst (snd (snd (snd e)))))
       (\ u v sel -> let w = body u v sel ; x = fst w ; mem = fst (snd (snd w))
                     in mkSigma x (mkSigma (fst (snd w)) (mkSigma mem
                          (hb x v (FinMem-coh-u x a mem) (snd (snd (snd w))))))))))

-- edges of a Lam approximant
LamBody-edge : (a : FinEl) (B : FinEl -> Pred) (g : FinFun) ->
  ((u v : FinEl) -> Selection g u v ->
     Sigma FinEl (\ x -> Pair (LeCode x u) (Pair (FinMem x a) (B x v)))) ->
  (p : Edge) -> EdgeIn p g ->
  Sigma FinEl (\ x -> Pair (LeCode x (fst p)) (Pair (FinMem x a) (B x (snd p))))
LamBody-edge a B g body p ein =
  let sel = singleton-selection p g ein
      w   = body (Sup (fst p) Bot) (Sup (snd p) Bot) sel
      x   = fst w
      lxu = Eq-transport (LeCode x) (Sup-Bot-r (fst p)) (fst (snd w))
      evB = Eq-transport (B x) (Sup-Bot-r (snd p)) (snd (snd (snd w)))
  in mkSigma x (mkSigma lxu (mkSigma (fst (snd (snd w))) evB))

module LamProps (PA : Pred) (B : FinEl -> Pred) (iA : Ideal PA) (bB : BodyOK B) where

  open BodyOK bB

  Bdown : (x v v' : FinEl) -> Coherent x -> B x v -> Coherent v' -> LeCode v' v -> B x v'
  Bdown x v v' cx e cv' le = Ideal.down (ideal x cx) v v' e cv' le

  -- downward closure of the selection clause (NAT EvalRel-down, Lam case)
  body-down : (a : FinEl) (g g' : FinFun) -> CoherentFun g -> CoherentFun g' ->
    LeFunCode g' g ->
    ((u v : FinEl) -> Selection g u v ->
       Sigma FinEl (\ x -> Pair (LeCode x u) (Pair (FinMem x a) (B x v)))) ->
    (u v : FinEl) -> Selection g' u v ->
       Sigma FinEl (\ x -> Pair (LeCode x u) (Pair (FinMem x a) (B x v)))
  body-down a g g' cg cg' le body u v sel =
    let ctg' = cft-from-cf g' cg'
        ctg  = cft-from-cf g cg
        cu  = Coherent-Selection sel ctg'
        cv  = Coherent-Selection-val sel ctg'
        lf-g' = LeFunCode-refl g' ctg'
        le-v-efg' = Selection-le-EvalFun g' sel lf-g' ctg' ctg' cu
        le-efg'-efg = EvalFun-mon g' g u ctg' ctg cu le
        c-efg'u = Coherent-EvalFun g' u ctg' cu
        c-efgu  = Coherent-EvalFun g u ctg cu
        le-v-efgu = LeCode-trans v (EvalFun g' u) (EvalFun g u)
                      cv c-efg'u c-efgu le-v-efg' le-efg'-efg
        sb     = selectionBelow g u ctg cu
        u0     = fst sb
        v0     = fst (snd sb)
        sel-g  = fst (snd (snd sb))
        le-u0  = fst (snd (snd (snd sb)))
        eq-v0  = snd (snd (snd (snd sb)))
        w      = body u0 v0 sel-g
        x      = fst w
        mem-x  = fst (snd (snd w))
        cx     = FinMem-coh-u x a mem-x
        le-x-u = LeCode-trans x u0 u cx
                   (Coherent-Selection sel-g ctg) cu (fst (snd w)) le-u0
        le-v-v0 = Eq-transport (LeCode v) eq-v0 le-v-efgu
    in mkSigma x (mkSigma le-x-u (mkSigma mem-x (Bdown x v0 v cx (snd (snd (snd w))) cv le-v-v0)))

  -- compatibility, edge by edge (NAT Lam-CompStepFun / Lam-CompFun)
  comp-via-body : (x1 x2 v1 v2 : FinEl) -> Comp x1 x2 -> Coherent x1 -> Coherent x2 ->
    B x1 v1 -> B x2 v2 -> Comp v1 v2
  comp-via-body x1 x2 v1 v2 c cx1 cx2 e1 e2 =
    let cs = Coherent-Sup x1 x2 c cx1 cx2
        e1' = mon x1 (Sup x1 x2) v1 cx1 cs (LeCode-Sup-left x1 x2 c cx1 cx2) e1
        e2' = mon x2 (Sup x1 x2) v2 cx2 cs (LeCode-Sup-right x1 x2 c cx1 cx2) e2
    in Ideal.comp (ideal (Sup x1 x2) cs) v1 v2 e1' e2'

  EdgeW : FinEl -> FinFun -> Set
  EdgeW a g = (p : Edge) -> EdgeIn p g ->
    Sigma FinEl (\ x -> Pair (LeCode x (fst p)) (Pair (FinMem x a) (B x (snd p))))

  compStepFun : (a1 a2 : FinEl) (s : Edge) (g2 : FinFun) -> CoherentFunTail g2 ->
    Sigma FinEl (\ xs -> Pair (LeCode xs (fst s)) (Pair (FinMem xs a1) (B xs (snd s)))) ->
    EdgeW a2 g2 -> CompStepFun s g2
  compStepFun a1 a2 s nil cg2 ws wf = tt
  compStepFun a1 a2 s (cons t rest) cg2 ws wf =
    let xs = fst ws ; le-xs = fst (snd ws) ; mem-s = fst (snd (snd ws)) ; ev-s = snd (snd (snd ws))
        wt = wf t here
        xt = fst wt ; le-xt = fst (snd wt) ; mem-t = fst (snd (snd wt)) ; ev-t = snd (snd (snd wt))
        step : CompStepStep s t
        step comp-keys =
          let cxs = FinMem-coh-u xs a1 mem-s
              cxt = FinMem-coh-u xt a2 mem-t
              step-a = Comp-down xs (fst s) (fst t) le-xs comp-keys
              step-b = Comp-down xt (fst t) xs le-xt (Comp-sym xs (fst t) step-a)
              comp-x = Comp-sym xt xs step-b
          in comp-via-body xs xt (snd s) (snd t) comp-x cxs cxt ev-s ev-t
    in mkSigma step (compStepFun a1 a2 s rest (CFTcons.tail-coh cg2) ws (\ t' ein -> wf t' (there ein)))

  compFun : (a1 a2 : FinEl) (g1 g2 : FinFun) -> CoherentFunTail g1 -> CoherentFunTail g2 ->
    EdgeW a1 g1 -> EdgeW a2 g2 -> CompFun g1 g2
  compFun a1 a2 nil g2 cg1 cg2 wf1 wf2 = tt
  compFun a1 a2 (cons s rest) g2 cg1 cg2 wf1 wf2 =
    mkSigma (compStepFun a1 a2 s g2 cg2 (wf1 s here) wf2)
            (compFun a1 a2 rest g2 (CFTcons.tail-coh cg1) cg2 (\ s' ein -> wf1 s' (there ein)) wf2)

  ideal-Lam : Ideal (LamS PA B)
  ideal-Lam = record { coh = coh' ; bot = tt ; down = down' ; comp = comp' ; sup = sup' }
    where
      coh' : (u : FinEl) -> LamS PA B u -> Coherent u
      coh' Bot e = tt
      coh' (FunEl g) e = fst (snd e)

      down' : (u u' : FinEl) -> LamS PA B u -> Coherent u' -> LeCode u' u -> LamS PA B u'
      down' Bot Bot e cu' le = tt
      down' (FunEl g) Bot e cu' le = tt
      down' (FunEl g) (FunEl g') e cu' le =
        let a = fst e
        in mkSigma a (mkSigma cu' (mkSigma (fst (snd (snd e))) (mkSigma (fst (snd (snd (snd e))))
             (body-down a g g' (fst (snd e)) cu' le (snd (snd (snd (snd e))))))))

      comp' : (u v : FinEl) -> LamS PA B u -> LamS PA B v -> Comp u v
      comp' Bot v e1 e2 = comp-Bot-l v
      comp' (FunEl g) Bot e1 e2 = tt
      comp' (FunEl g1) (FunEl g2) e1 e2 =
        compFun (fst e1) (fst e2) g1 g2 (cft-from-cf g1 (fst (snd e1))) (cft-from-cf g2 (fst (snd e2)))
          (LamBody-edge (fst e1) B g1 (snd (snd (snd (snd e1)))))
          (LamBody-edge (fst e2) B g2 (snd (snd (snd (snd e2)))))

      sup' : (u v : FinEl) -> LamS PA B u -> LamS PA B v -> LamS PA B (Sup u v)
      sup' Bot v e1 e2 = e2
      sup' (FunEl g) Bot e1 e2 = e1
      sup' (FunEl g1) (FunEl g2) eu ev =
        let comp = comp' (FunEl g1) (FunEl g2) eu ev
            a1    = fst eu
            cg1   = fst (snd eu)
            a1U   = fst (snd (snd eu))
            evA1  = fst (snd (snd (snd eu)))
            body1 = snd (snd (snd (snd eu)))
            a2    = fst ev
            cg2   = fst (snd ev)
            a2U   = fst (snd (snd ev))
            evA2  = fst (snd (snd (snd ev)))
            body2 = snd (snd (snd (snd ev)))
            ca1   = Ideal.coh iA a1 evA1
            ca2   = Ideal.coh iA a2 evA2
            comp-a = Ideal.comp iA a1 a2 evA1 evA2
            evA-sup = Ideal.sup iA a1 a2 evA1 evA2
            c-sup-a = Coherent-Sup a1 a2 comp-a ca1 ca2
            supU = FinMem-Sup-element a1 a2 UCode comp-a tt a1U a2U
            c-gab = CoherentFun-append g1 g2 cg1 cg2 comp
            ct-gab = cft-from-cf (append g1 g2) c-gab
        in mkSigma (Sup a1 a2) (mkSigma c-gab (mkSigma supU (mkSigma evA-sup
             (\ u v sel ->
                let cu-sel = Coherent-Selection sel ct-gab
                    cv-sel = Coherent-Selection-val sel ct-gab
                    sb1    = selectionBelow g1 u (cft-from-cf g1 cg1) cu-sel
                    u1     = fst sb1
                    v1     = fst (snd sb1)
                    sel1   = fst (snd (snd sb1))
                    le-u1  = fst (snd (snd (snd sb1)))
                    eq-v1  = snd (snd (snd (snd sb1)))
                    sb2    = selectionBelow g2 u (cft-from-cf g2 cg2) cu-sel
                    u2     = fst sb2
                    v2     = fst (snd sb2)
                    sel2   = fst (snd (snd sb2))
                    le-u2  = fst (snd (snd (snd sb2)))
                    eq-v2  = snd (snd (snd (snd sb2)))
                    w1     = body1 u1 v1 sel1
                    x1     = fst w1
                    mem-x1 = fst (snd (snd w1))
                    evM-x1 = snd (snd (snd w1))
                    w2     = body2 u2 v2 sel2
                    x2     = fst w2
                    mem-x2 = fst (snd (snd w2))
                    evM-x2 = snd (snd (snd w2))
                    cx1    = FinMem-coh-u x1 a1 mem-x1
                    cx2    = FinMem-coh-u x2 a2 mem-x2
                    le-x1-u = LeCode-trans x1 u1 u cx1 (Coherent-Selection sel1 (cft-from-cf g1 cg1)) cu-sel (fst (snd w1)) le-u1
                    le-x2-u = LeCode-trans x2 u2 u cx2 (Coherent-Selection sel2 (cft-from-cf g2 cg2)) cu-sel (fst (snd w2)) le-u2
                    comp-x  = LeCode-Comp x1 x2 u cu-sel le-x1-u le-x2-u
                    c-supx  = Coherent-Sup x1 x2 comp-x cx1 cx2
                    le-supx-u = LeCode-Sup-lub x1 x2 u le-x1-u le-x2-u
                    le-a1-sup = LeCode-Sup-left a1 a2 comp-a ca1 ca2
                    le-a2-sup = LeCode-Sup-right a1 a2 comp-a ca1 ca2
                    mem-x1-sup = finMem-upward x1 a1 (Sup a1 a2) le-a1-sup ca1 c-sup-a mem-x1 supU
                    mem-x2-sup = finMem-upward x2 a2 (Sup a1 a2) le-a2-sup ca2 c-sup-a mem-x2 supU
                    mem-supx   = FinMem-Sup-element x1 x2 (Sup a1 a2) comp-x c-sup-a mem-x1-sup mem-x2-sup
                    evM-sup1 = mon x1 (Sup x1 x2) v1 cx1 c-supx (LeCode-Sup-left x1 x2 comp-x cx1 cx2) evM-x1
                    evM-sup2 = mon x2 (Sup x1 x2) v2 cx2 c-supx (LeCode-Sup-right x1 x2 comp-x cx1 cx2) evM-x2
                    iS = ideal (Sup x1 x2) c-supx
                    evM-supv = Ideal.sup iS v1 v2 evM-sup1 evM-sup2
                    lf-gab = LeFunCode-refl (append g1 g2) ct-gab
                    le-v-ef = Selection-le-EvalFun (append g1 g2) sel lf-gab ct-gab ct-gab cu-sel
                    ctg1   = cft-from-cf g1 cg1
                    eq-ef  = EvalFun-append-eq g1 g2 u comp ctg1 cu-sel
                    le-v-supef = Eq-transport (LeCode v) eq-ef le-v-ef
                    eq-sup = Eq-transport (\ z -> Eq (Sup z (EvalFun g2 u)) (Sup v1 v2))
                               (Eq-sym eq-v1)
                               (Eq-transport (\ z -> Eq (Sup v1 z) (Sup v1 v2))
                                 (Eq-sym eq-v2) refl)
                    le-v-supv = Eq-transport (LeCode v) eq-sup le-v-supef
                    evM-v  = Ideal.down iS (Sup v1 v2) v evM-supv cv-sel le-v-supv
                in mkSigma (Sup x1 x2) (mkSigma le-supx-u (mkSigma mem-supx evM-v))))))

------------------------------------------------------------------------
-- Pi / Sigma codes over a FAMILY predicate PF (the family is a term;
-- PF (FunEl f) says the codomain function f approximates it).
------------------------------------------------------------------------

FamRel : Pred -> FinFun -> Set
FamRel PF nil         = Top
FamRel PF (cons e es) = PF (FunEl (cons e es))

CodeBody : Pred -> Pred -> FinEl -> FinFun -> Set
CodeBody PA PF a f = Pair (Pair (Coherent a) (CoherentFunTail f)) (Pair (PA a) (FamRel PF f))

PiS : Pred -> Pred -> Pred
PiS PA PF Bot             = Top
PiS PA PF UCode           = Empty
PiS PA PF (FunEl _)       = Empty
PiS PA PF (PiCode a f)    = CodeBody PA PF a f
PiS PA PF NatCode         = Empty
PiS PA PF ZeroEl          = Empty
PiS PA PF (SucEl _)       = Empty
PiS PA PF (PairEl _ _)    = Empty
PiS PA PF (SigmaCode _ _) = Empty

SigS : Pred -> Pred -> Pred
SigS PA PF Bot             = Top
SigS PA PF UCode           = Empty
SigS PA PF (FunEl _)       = Empty
SigS PA PF (PiCode _ _)    = Empty
SigS PA PF NatCode         = Empty
SigS PA PF ZeroEl          = Empty
SigS PA PF (SucEl _)       = Empty
SigS PA PF (PairEl _ _)    = Empty
SigS PA PF (SigmaCode a f) = CodeBody PA PF a f

FamRel-map : (PF PF' : Pred) -> ((u : FinEl) -> PF u -> PF' u) -> (f : FinFun) -> FamRel PF f -> FamRel PF' f
FamRel-map PF PF' h nil e = tt
FamRel-map PF PF' h (cons p ps) e = h _ e

CodeBody-map : (PA PA' PF PF' : Pred) -> ((u : FinEl) -> PA u -> PA' u) -> ((u : FinEl) -> PF u -> PF' u) ->
  (a : FinEl) (f : FinFun) -> CodeBody PA PF a f -> CodeBody PA' PF' a f
CodeBody-map PA PA' PF PF' ha hf a f e =
  mkSigma (fst e) (mkSigma (ha a (fst (snd e))) (FamRel-map PF PF' hf f (snd (snd e))))

PiS-map : (PA PA' PF PF' : Pred) -> ((u : FinEl) -> PA u -> PA' u) -> ((u : FinEl) -> PF u -> PF' u) ->
  (u : FinEl) -> PiS PA PF u -> PiS PA' PF' u
PiS-map PA PA' PF PF' ha hf Bot e = tt
PiS-map PA PF PA' PF' ha hf (PiCode a f) e = CodeBody-map PA PF PA' PF' ha hf a f e

SigS-map : (PA PA' PF PF' : Pred) -> ((u : FinEl) -> PA u -> PA' u) -> ((u : FinEl) -> PF u -> PF' u) ->
  (u : FinEl) -> SigS PA PF u -> SigS PA' PF' u
SigS-map PA PA' PF PF' ha hf Bot e = tt
SigS-map PA PF PA' PF' ha hf (SigmaCode a f) e = CodeBody-map PA PF PA' PF' ha hf a f e

module CodeProps (PA PF : Pred) (iA : Ideal PA) (iF : Ideal PF) where

  fam-down : (f f' : FinFun) -> CoherentFunTail f' -> LeFunCode f' f -> FamRel PF f -> FamRel PF f'
  fam-down f nil cf' le e = tt
  fam-down nil (cons p ps) cf' le e = Empty-elim (cft-not-le-nil p ps cf' le)
  fam-down (cons q qs) (cons p ps) cf' le e = Ideal.down iF (FunEl (cons q qs)) (FunEl (cons p ps)) e cf' le

  fam-comp : (f f' : FinFun) -> FamRel PF f -> FamRel PF f' -> CompFun f f'
  fam-comp nil f' e1 e2 = tt
  fam-comp (cons p ps) nil e1 e2 = CompFun-nil-r (cons p ps)
  fam-comp (cons p ps) (cons q qs) e1 e2 = Ideal.comp iF (FunEl (cons p ps)) (FunEl (cons q qs)) e1 e2

  fam-sup : (f f' : FinFun) -> FamRel PF f -> FamRel PF f' -> FamRel PF (append f f')
  fam-sup nil f' e1 e2 = e2
  fam-sup (cons p ps) nil e1 e2 = Eq-transport (FamRel PF) (Eq-sym (append-nil-r (cons p ps))) e1
  fam-sup (cons p ps) (cons q qs) e1 e2 = Ideal.sup iF (FunEl (cons p ps)) (FunEl (cons q qs)) e1 e2

  body-down : (a : FinEl) (f : FinFun) (a' : FinEl) (f' : FinFun) -> CodeBody PA PF a f -> Pair (Coherent a') (CoherentFunTail f') ->
    LeCode a' a -> LeFunCode f' f -> CodeBody PA PF a' f'
  body-down a f a' f' e c' la lf =
    mkSigma c' (mkSigma (Ideal.down iA a a' (fst (snd e)) (fst c') la)
                        (fam-down f f' (snd c') lf (snd (snd e))))

  body-comp : (a : FinEl) (f : FinFun) (a' : FinEl) (f' : FinFun) -> CodeBody PA PF a f -> CodeBody PA PF a' f' ->
    Pair (Comp a a') (CompFun f f')
  body-comp a f a' f' e1 e2 =
    mkSigma (Ideal.comp iA a a' (fst (snd e1)) (fst (snd e2)))
            (fam-comp f f' (snd (snd e1)) (snd (snd e2)))

  body-sup : (a : FinEl) (f : FinFun) (a' : FinEl) (f' : FinFun) -> CodeBody PA PF a f -> CodeBody PA PF a' f' ->
    CodeBody PA PF (Sup a a') (append f f')
  body-sup a f a' f' e1 e2 =
    let c = body-comp a f a' f' e1 e2
    in mkSigma (mkSigma (Coherent-Sup a a' (fst c) (fst (fst e1)) (fst (fst e2)))
                        (CoherentFunTail-append f f' (snd (fst e1)) (snd (fst e2)) (snd c)))
         (mkSigma (Ideal.sup iA a a' (fst (snd e1)) (fst (snd e2)))
                  (fam-sup f f' (snd (snd e1)) (snd (snd e2))))

  ideal-Pi : Ideal (PiS PA PF)
  ideal-Pi = record { coh = coh' ; bot = tt ; down = down' ; comp = comp' ; sup = sup' }
    where
      coh' : (u : FinEl) -> PiS PA PF u -> Coherent u
      coh' Bot e = tt
      coh' (PiCode a f) e = fst e
      down' : (u u' : FinEl) -> PiS PA PF u -> Coherent u' -> LeCode u' u -> PiS PA PF u'
      down' Bot Bot e c le = tt
      down' (PiCode a f) Bot e c le = tt
      down' (PiCode a f) (PiCode a' f') e c le = body-down a f a' f' e c (fst le) (snd le)
      comp' : (u v : FinEl) -> PiS PA PF u -> PiS PA PF v -> Comp u v
      comp' Bot v e1 e2 = comp-Bot-l v
      comp' (PiCode a f) Bot e1 e2 = tt
      comp' (PiCode a f) (PiCode a' f') e1 e2 = body-comp a f a' f' e1 e2
      sup' : (u v : FinEl) -> PiS PA PF u -> PiS PA PF v -> PiS PA PF (Sup u v)
      sup' Bot v e1 e2 = e2
      sup' (PiCode a f) Bot e1 e2 = e1
      sup' (PiCode a f) (PiCode a' f') e1 e2 = body-sup a f a' f' e1 e2

  ideal-Sig : Ideal (SigS PA PF)
  ideal-Sig = record { coh = coh' ; bot = tt ; down = down' ; comp = comp' ; sup = sup' }
    where
      coh' : (u : FinEl) -> SigS PA PF u -> Coherent u
      coh' Bot e = tt
      coh' (SigmaCode a f) e = fst e
      down' : (u u' : FinEl) -> SigS PA PF u -> Coherent u' -> LeCode u' u -> SigS PA PF u'
      down' Bot Bot e c le = tt
      down' (SigmaCode a f) Bot e c le = tt
      down' (SigmaCode a f) (SigmaCode a' f') e c le = body-down a f a' f' e c (fst le) (snd le)
      comp' : (u v : FinEl) -> SigS PA PF u -> SigS PA PF v -> Comp u v
      comp' Bot v e1 e2 = comp-Bot-l v
      comp' (SigmaCode a f) Bot e1 e2 = tt
      comp' (SigmaCode a f) (SigmaCode a' f') e1 e2 = body-comp a f a' f' e1 e2
      sup' : (u v : FinEl) -> SigS PA PF u -> SigS PA PF v -> SigS PA PF (Sup u v)
      sup' Bot v e1 e2 = e2
      sup' (SigmaCode a f) Bot e1 e2 = e1
      sup' (SigmaCode a f) (SigmaCode a' f') e1 e2 = body-sup a f a' f' e1 e2

------------------------------------------------------------------------
-- Primitive recursion: structural recursion on the Nat approximant w.
--   RecB c w : "c (non-Bot) is below rec z s w"
--   rec z s (S w) = s w (rec z s w),  the inner value r may be Bot.
------------------------------------------------------------------------

RecB : Pred -> Pred -> FinEl -> FinEl -> Set
RecB Pz Ps c Bot             = Empty
RecB Pz Ps c UCode           = Empty
RecB Pz Ps c (FunEl _)       = Empty
RecB Pz Ps c (PiCode _ _)    = Empty
RecB Pz Ps c NatCode         = Empty
RecB Pz Ps c ZeroEl          = Pz c
RecB Pz Ps c (SucEl w)       =
  Sigma FinEl (\ r -> Pair (Guard r (RecB Pz Ps r w)) (Ps (sing w (sing r c))))
RecB Pz Ps c (PairEl _ _)    = Empty
RecB Pz Ps c (SigmaCode _ _) = Empty

RecS : Pred -> Pred -> Pred -> Pred
RecS Pz Ps Pk c = Guard c (Sigma FinEl (\ w -> Pair (Pk w) (RecB Pz Ps c w)))

RecB-map : (Pz Pz' Ps Ps' : Pred) -> ((u : FinEl) -> Pz u -> Pz' u) -> ((u : FinEl) -> Ps u -> Ps' u) ->
  (c w : FinEl) -> RecB Pz Ps c w -> RecB Pz' Ps' c w
RecB-map Pz Pz' Ps Ps' hz hs c ZeroEl e = hz c e
RecB-map Pz Pz' Ps Ps' hz hs c (SucEl w) e =
  mkSigma (fst e) (mkSigma (guard-map (fst e) (\ nb b -> RecB-map Pz Pz' Ps Ps' hz hs (fst e) w b) (fst (snd e)))
                           (hs _ (snd (snd e))))

RecS-map : (Pz Pz' Ps Ps' Pk Pk' : Pred) -> ((u : FinEl) -> Pz u -> Pz' u) ->
  ((u : FinEl) -> Ps u -> Ps' u) -> ((u : FinEl) -> Pk u -> Pk' u) ->
  (c : FinEl) -> RecS Pz Ps Pk c -> RecS Pz' Ps' Pk' c
RecS-map Pz Pz' Ps Ps' Pk Pk' hz hs hk c =
  guard-map c (\ nb b -> mkSigma (fst b) (mkSigma (hk _ (fst (snd b)))
                            (RecB-map Pz Pz' Ps Ps' hz hs c (fst b) (snd (snd b)))))

sing-le-key : (v v' y : FinEl) -> Coherent (sing v y) -> Coherent v' -> LeCode v v' ->
  LeCode (sing v' y) (sing v y)
sing-le-key v v' y c cv' le = mkSigma (sing-EvalFun v y v' c cv' le) tt

module RecProps (Pz Ps : Pred) (iz : Ideal Pz) (is : Ideal Ps) where

  coh-B : (c w : FinEl) -> NotBot c -> RecB Pz Ps c w -> Coherent c
  coh-B c ZeroEl nb e = Ideal.coh iz c e
  coh-B c (SucEl w) nb e =
    let r = fst e
        cs = Ideal.coh is (sing w (sing r c)) (snd (snd e))
    in sing-val-coh r c (sing-val-coh w (sing r c) cs)

  -- monotone in the Nat argument
  monw : (c w w' : FinEl) -> Coherent w' -> LeCode w w' -> RecB Pz Ps c w -> RecB Pz Ps c w'
  monw c ZeroEl ZeroEl cw' le e = e
  monw c (SucEl v) (SucEl v') cw' le e =
    let r = fst e
        cs = Ideal.coh is (sing v (sing r c)) (snd (snd e))
        cv = sing-key-coh v (sing r c) cs
        csrc = sing-val-coh v (sing r c) cs
        nbsrc : NotBot (sing r c)
        nbsrc = tt
    in mkSigma r (mkSigma (guard-map r (\ nb b -> monw r v v' cw' le b) (fst (snd e)))
         (Ideal.down is (sing v (sing r c)) (sing v' (sing r c)) (snd (snd e))
            (sing-coh v' (sing r c) cw' csrc nbsrc) (sing-le-key v v' (sing r c) cs cw' le)))

  down-B : (c c' w : FinEl) -> RecB Pz Ps c w -> NotBot c' -> Coherent c' -> LeCode c' c -> RecB Pz Ps c' w
  down-B c c' ZeroEl e nb' cc' le = Ideal.down iz c c' e cc' le
  down-B c c' (SucEl w) e nb' cc' le =
    let r = fst e
        cs = Ideal.coh is (sing w (sing r c)) (snd (snd e))
        cw = sing-key-coh w (sing r c) cs
        crc = sing-val-coh w (sing r c) cs
        cr = sing-key-coh r c crc
        crc' = sing-coh r c' cr cc' nb'
        lrc = sing-le-val r c c' crc cc' le
    in mkSigma r (mkSigma (fst (snd e))
         (Ideal.down is (sing w (sing r c)) (sing w (sing r c')) (snd (snd e))
            (sing-coh w (sing r c') cw crc' tt) (sing-le-val w (sing r c) (sing r c') cs crc' lrc)))

  comp-B : (c1 c2 w1 w2 : FinEl) -> NotBot c1 -> NotBot c2 -> Comp w1 w2 ->
    RecB Pz Ps c1 w1 -> RecB Pz Ps c2 w2 -> Comp c1 c2
  comp-B c1 c2 ZeroEl ZeroEl nb1 nb2 cw e1 e2 = Ideal.comp iz c1 c2 e1 e2
  comp-B c1 c2 (SucEl v1) (SucEl v2) nb1 nb2 cw e1 e2 =
    let r1 = fst e1 ; r2 = fst e2
        cf = Ideal.comp is (sing v1 (sing r1 c1)) (sing v2 (sing r2 c2)) (snd (snd e1)) (snd (snd e2))
        crr = comp-r (bot-or r1) (bot-or r2)
    in fst (fst (fst (fst cf) cw)) crr
    where
      comp-r : Or (Eq (fst e1) Bot) (NotBot (fst e1)) -> Or (Eq (fst e2) Bot) (NotBot (fst e2)) ->
        Comp (fst e1) (fst e2)
      comp-r (left q) o = Eq-transport (\ z -> Comp z (fst e2)) (Eq-sym q) (comp-Bot-l (fst e2))
      comp-r (right n1) (left q) = Eq-transport (Comp (fst e1)) (Eq-sym q) (comp-Bot-r (fst e1))
      comp-r (right n1) (right n2) =
        comp-B (fst e1) (fst e2) v1 v2 n1 n2 cw
          (guard-elim (fst e1) n1 (fst (snd e1))) (guard-elim (fst e2) n2 (fst (snd e2)))

  sup-B : (c1 c2 w1 w2 : FinEl) -> NotBot c1 -> NotBot c2 -> Comp w1 w2 -> Coherent w1 -> Coherent w2 ->
    RecB Pz Ps c1 w1 -> RecB Pz Ps c2 w2 -> RecB Pz Ps (Sup c1 c2) (Sup w1 w2)
  sup-B c1 c2 ZeroEl ZeroEl nb1 nb2 cw cw1 cw2 e1 e2 = Ideal.sup iz c1 c2 e1 e2
  sup-B c1 c2 (SucEl v1) (SucEl v2) nb1 nb2 cw cv1 cv2 e1 e2 =
    let r1 = fst e1 ; r2 = fst e2
        p1 = snd (snd e1) ; p2 = snd (snd e2)
        cs1 = Ideal.coh is _ p1 ; cs2 = Ideal.coh is _ p2
        crc1 = sing-val-coh v1 (sing r1 c1) cs1 ; crc2 = sing-val-coh v2 (sing r2 c2) cs2
        cr1 = sing-key-coh r1 c1 crc1 ; cr2 = sing-key-coh r2 c2 crc2
        cc1 = sing-val-coh r1 c1 crc1 ; cc2 = sing-val-coh r2 c2 crc2
        ccc = comp-B c1 c2 (SucEl v1) (SucEl v2) nb1 nb2 cw e1 e2
        crr = comp-r (bot-or r1) (bot-or r2)
        csv = Coherent-Sup v1 v2 cw cv1 cv2
        csr = Coherent-Sup r1 r2 crr cr1 cr2
        csc = Coherent-Sup c1 c2 ccc cc1 cc2
        nbc = NotBot-Sup-l c1 c2 nb1 ccc
        -- compatibility of the two inner singletons, then of the outer ones
        cinner : Comp (sing r1 c1) (sing r2 c2)
        cinner = mkSigma (mkSigma (\ _ -> ccc) tt) tt
        psup = Ideal.sup is _ _ p1 p2
        cpsup = Ideal.coh is _ psup
        le1 = LeFunCode-Sup-pair v1 (sing r1 c1) v2 (sing r2 c2) cw cinner cpsup csv
        inner2 : CoherentFun (cons (mkSigma r1 c1) (cons (mkSigma r2 c2) nil))
        inner2 = Coherent-Sup (sing r1 c1) (sing r2 c2) cinner crc1 crc2
        le2 = LeFunCode-Sup-pair r1 c1 r2 c2 crr ccc inner2 csr
        cS = sing-coh (Sup r1 r2) (Sup c1 c2) csr csc nbc
        cbig = sing-coh (Sup v1 v2) (Sup (sing r1 c1) (sing r2 c2)) csv inner2 tt
        lev = sing-le-val (Sup v1 v2) (Sup (sing r1 c1) (sing r2 c2)) (sing (Sup r1 r2) (Sup c1 c2))
                cbig cS le2
        big = FunEl (cons (mkSigma v1 (sing r1 c1)) (cons (mkSigma v2 (sing r2 c2)) nil))
        tot = LeCode-trans (sing (Sup v1 v2) (sing (Sup r1 r2) (Sup c1 c2)))
                (sing (Sup v1 v2) (Sup (sing r1 c1) (sing r2 c2))) big
                (sing-coh (Sup v1 v2) (sing (Sup r1 r2) (Sup c1 c2)) csv cS tt) cbig cpsup lev le1
    in mkSigma (Sup r1 r2)
         (mkSigma (rguard (bot-or r1) (bot-or r2))
           (Ideal.down is big _ psup (sing-coh (Sup v1 v2) (sing (Sup r1 r2) (Sup c1 c2)) csv cS tt) tot))
    where
      comp-r : Or (Eq (fst e1) Bot) (NotBot (fst e1)) -> Or (Eq (fst e2) Bot) (NotBot (fst e2)) ->
        Comp (fst e1) (fst e2)
      comp-r (left q) o = Eq-transport (\ z -> Comp z (fst e2)) (Eq-sym q) (comp-Bot-l (fst e2))
      comp-r (right n1) (left q) = Eq-transport (Comp (fst e1)) (Eq-sym q) (comp-Bot-r (fst e1))
      comp-r (right n1) (right n2) =
        comp-B (fst e1) (fst e2) v1 v2 n1 n2 cw
          (guard-elim (fst e1) n1 (fst (snd e1))) (guard-elim (fst e2) n2 (fst (snd e2)))
      csv' = Coherent-Sup v1 v2 cw cv1 cv2
      rguard : Or (Eq (fst e1) Bot) (NotBot (fst e1)) -> Or (Eq (fst e2) Bot) (NotBot (fst e2)) ->
        Guard (Sup (fst e1) (fst e2)) (RecB Pz Ps (Sup (fst e1) (fst e2)) (Sup v1 v2))
      rguard (left q) o =
        Eq-transport (\ z -> Guard (Sup z (fst e2)) (RecB Pz Ps (Sup z (fst e2)) (Sup v1 v2))) (Eq-sym q)
          (guard-map (fst e2) (\ nb b -> monw (fst e2) v2 (Sup v1 v2) csv'
                                   (LeCode-Sup-right v1 v2 cw cv1 cv2) b) (fst (snd e2)))
      rguard (right n1) (left q) =
        Eq-transport (\ z -> Guard (Sup (fst e1) z) (RecB Pz Ps (Sup (fst e1) z) (Sup v1 v2))) (Eq-sym q)
          (Eq-transport (\ z -> Guard z (RecB Pz Ps z (Sup v1 v2))) (Eq-sym (Sup-Bot-r (fst e1)))
            (guard-map (fst e1) (\ nb b -> monw (fst e1) v1 (Sup v1 v2) csv'
                                     (LeCode-Sup-left v1 v2 cw cv1 cv2) b) (fst (snd e1))))
      rguard (right n1) (right n2) =
        let crr = comp-r (right n1) (right n2) in
        guard-intro (Sup (fst e1) (fst e2)) (NotBot-Sup-l (fst e1) (fst e2) n1 crr)
          (sup-B (fst e1) (fst e2) v1 v2 n1 n2 cw cv1 cv2
             (guard-elim (fst e1) n1 (fst (snd e1))) (guard-elim (fst e2) n2 (fst (snd e2))))

  ideal-Rec : (Pk : Pred) -> Ideal Pk -> Ideal (RecS Pz Ps Pk)
  ideal-Rec Pk ik = record { coh = coh' ; bot = tt ; down = down' ; comp = comp' ; sup = sup' }
    where
      coh' : (u : FinEl) -> RecS Pz Ps Pk u -> Coherent u
      coh' u e = go (bot-or u)
        where
          go : Or (Eq u Bot) (NotBot u) -> Coherent u
          go (left refl) = tt
          go (right nb) = let b = guard-elim u nb e in coh-B u (fst b) nb (snd (snd b))
      down' : (u u' : FinEl) -> RecS Pz Ps Pk u -> Coherent u' -> LeCode u' u -> RecS Pz Ps Pk u'
      down' u u' e cu' le = go (bot-or u')
        where
          go : Or (Eq u' Bot) (NotBot u') -> RecS Pz Ps Pk u'
          go (left refl) = tt
          go (right nb') =
            let nb = NotBot-from-Le u' u nb' le
                b = guard-elim u nb e
            in guard-intro u' nb' (mkSigma (fst b) (mkSigma (fst (snd b))
                 (down-B u u' (fst b) (snd (snd b)) nb' cu' le)))
      comp' : (u v : FinEl) -> RecS Pz Ps Pk u -> RecS Pz Ps Pk v -> Comp u v
      comp' u v e1 e2 = go (bot-or u) (bot-or v)
        where
          go : Or (Eq u Bot) (NotBot u) -> Or (Eq v Bot) (NotBot v) -> Comp u v
          go (left refl) o = comp-Bot-l v
          go (right nb) (left refl) = comp-Bot-r u
          go (right nb1) (right nb2) =
            let b1 = guard-elim u nb1 e1 ; b2 = guard-elim v nb2 e2
            in comp-B u v (fst b1) (fst b2) nb1 nb2
                 (Ideal.comp ik (fst b1) (fst b2) (fst (snd b1)) (fst (snd b2))) (snd (snd b1)) (snd (snd b2))
      sup' : (u v : FinEl) -> RecS Pz Ps Pk u -> RecS Pz Ps Pk v -> RecS Pz Ps Pk (Sup u v)
      sup' u v e1 e2 = go (bot-or u) (bot-or v)
        where
          go : Or (Eq u Bot) (NotBot u) -> Or (Eq v Bot) (NotBot v) -> RecS Pz Ps Pk (Sup u v)
          go (left refl) o = e2
          go (right nb) (left refl) = Eq-transport (RecS Pz Ps Pk) (Eq-sym (Sup-Bot-r u)) e1
          go (right nb1) (right nb2) =
            let b1 = guard-elim u nb1 e1 ; b2 = guard-elim v nb2 e2
                w1 = fst b1 ; w2 = fst b2
                k1 = fst (snd b1) ; k2 = fst (snd b2)
                cw = Ideal.comp ik w1 w2 k1 k2
                cuv = comp' u v e1 e2
            in guard-intro (Sup u v) (NotBot-Sup-l u v nb1 cuv)
                 (mkSigma (Sup w1 w2) (mkSigma (Ideal.sup ik w1 w2 k1 k2)
                   (sup-B u v w1 w2 nb1 nb2 cw (Ideal.coh ik w1 k1) (Ideal.coh ik w2 k2)
                      (snd (snd b1)) (snd (snd b2)))))

------------------------------------------------------------------------
-- Rebuilding the selection clause of a Lam approximant from edgewise
-- data (B monotone in x, each B x an ideal).
------------------------------------------------------------------------

module LamEdges (B : FinEl -> Pred) (bB : BodyOK B) where

  open BodyOK bB

  from-edges : (a : FinEl) (g : FinFun) -> CoherentFunTail g -> FinMem a UCode ->
    ((p : Edge) -> EdgeIn p g ->
       Sigma FinEl (\ x -> Pair (LeCode x (fst p)) (Pair (FinMem x a) (B x (snd p))))) ->
    (u v : FinEl) -> Selection g u v ->
    Sigma FinEl (\ x -> Pair (LeCode x u) (Pair (FinMem x a) (B x v)))
  from-edges a .nil cg aU ew .Bot .Bot sel-nil =
    mkSigma Bot (mkSigma tt (mkSigma (finMem-bot-from a aU) (Ideal.bot (ideal Bot tt))))
  from-edges a (cons p g) cg aU ew u v (sel-skip sel) =
    from-edges a g (CFTcons.tail-coh cg) aU (\ q ein -> ew q (there ein)) u v sel
  from-edges a (cons p g) cg aU ew .(Sup (fst p) u) .(Sup (snd p) v) (sel-take {p} {u} {v} ck cv sel) =
    let ca  = coh-from-aU a aU
        wp  = ew p here
        xp  = fst wp ; lep = fst (snd wp) ; mp = fst (snd (snd wp)) ; bp = snd (snd (snd wp))
        wt  = from-edges a g (CFTcons.tail-coh cg) aU (\ q ein -> ew q (there ein)) u v sel
        xt  = fst wt ; let' = fst (snd wt) ; mt = fst (snd (snd wt)) ; bt = snd (snd (snd wt))
        cxp = FinMem-coh-u xp a mp ; cxt = FinMem-coh-u xt a mt
        ckp = CFTcons.key-coh cg
        cu  = Coherent-Selection sel (CFTcons.tail-coh cg)
        cxx = Comp-mono xp xt (fst p) u cxp cxt ckp cu lep let' ck
        cs  = Coherent-Sup xp xt cxx cxp cxt
        csu = Coherent-Sup (fst p) u ck ckp cu
        l1  = LeCode-trans xp (fst p) (Sup (fst p) u) cxp ckp csu lep (LeCode-Sup-left (fst p) u ck ckp cu)
        l2  = LeCode-trans xt u (Sup (fst p) u) cxt cu csu let' (LeCode-Sup-right (fst p) u ck ckp cu)
        b1  = mon xp (Sup xp xt) (snd p) cxp cs (LeCode-Sup-left xp xt cxx cxp cxt) bp
        b2  = mon xt (Sup xp xt) v cxt cs (LeCode-Sup-right xp xt cxx cxp cxt) bt
    in mkSigma (Sup xp xt) (mkSigma (LeCode-Sup-lub xp xt (Sup (fst p) u) l1 l2)
         (mkSigma (FinMem-Sup-element xp xt a cxx ca mp mt)
                  (Ideal.sup (ideal (Sup xp xt) cs) (snd p) v b1 b2)))

-- a Lam map whose body transfer may use the domain membership
LamS-map2 : (PA PA' : Pred) (B B' : FinEl -> Pred) ->
  ((u : FinEl) -> PA u -> PA' u) ->
  ((x a v : FinEl) -> FinMem x a -> PA a -> B x v -> B' x v) ->
  (u : FinEl) -> LamS PA B u -> LamS PA' B' u
LamS-map2 PA PA' B B' ha hb Bot e = tt
LamS-map2 PA PA' B B' ha hb (FunEl g) e =
  let a = fst e ; aU = fst (snd (snd e)) ; ea = fst (snd (snd (snd e))) ; body = snd (snd (snd (snd e)))
  in mkSigma a (mkSigma (fst (snd e)) (mkSigma aU (mkSigma (ha a ea)
       (\ u v sel -> let w = body u v sel ; x = fst w ; mem = fst (snd (snd w))
                     in mkSigma x (mkSigma (fst (snd w)) (mkSigma mem (hb x a v mem ea (snd (snd (snd w))))))))))
