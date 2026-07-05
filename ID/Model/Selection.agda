{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- Selection.agda
--
-- Edge, EdgeIn, Selection infrastructure, and lookup lemmas.
--
-- A Selection of a finite function f is a compatible sub-multiset.
-- u = Sup of selected keys, v = Sup of selected values.
-- sel-take carries Comp on both keys and values for coherence.
------------------------------------------------------------------------

module ID.Model.Selection where

import ID.Domain.Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ;
              fst ; snd ; Sigma ; Eq ; refl ; Eq-transport ; Eq-sym ;
              Eq-cong ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ;
              List ; nil ; cons ;
              isPos)
open import ID.Domain.Kernel using (EvalFun ; EvalFun-step ;
  leFinEl ; leFinEl-sound ;
  LeCode ; LeFunCode ; LeCode-Bot ; LeCode-Sup-lub ;
  LeCode-Sup-left ; LeCode-Sup-right ;
  LeCode-refl ; LeCode-trans ;
  Sup ; Comp ; CompStepFun ; Coherent-Sup ;
  Coherent ; CoherentFun ; CoherentFunTail ; CFTcons ; CoherentWith ;
  cft-from-cf ;
  Coherent-EvalFun ; EvalFun-mon-arg ;
  Comp-value-EvalFun ; comp-Bot-r ;
  LeCode-Comp ;
  FinMem ; FinMemFun ; FinMemAllU ; EvalFun-in-UCode ;
  finMem-bot-from ;
  FinMem-coh-u ;
  Sup-Bot-right ;
  finMem-upward ;
  FinMem-Sup-element ;
  coherentWith-to-compStepFun)

------------------------------------------------------------------------
-- Edge and EdgeIn
------------------------------------------------------------------------

Edge : Set
Edge = Pair FinEl FinEl

data EdgeIn : Edge -> FinFun -> Set where
  here  : {e : Edge} {es : FinFun} ->
          EdgeIn e (cons e es)
  there : {e e' : Edge} {es : FinFun} ->
          EdgeIn e es ->
          EdgeIn e (cons e' es)

CoherentFun-edge-key : (e : Edge) (g : FinFun) ->
  CoherentFunTail g -> EdgeIn e g -> Coherent (fst e)
CoherentFun-edge-key e (cons p ps) cf here = CFTcons.key-coh cf
CoherentFun-edge-key e (cons p nil) cf (there ())
CoherentFun-edge-key e (cons p (cons q qs)) cf (there ein) =
  CoherentFun-edge-key e (cons q qs) (CFTcons.tail-coh cf) ein

------------------------------------------------------------------------
-- TypedGraph and SatFinFun
------------------------------------------------------------------------

record TypedGraph (b : FinEl) (f : FinFun) : Set where
  field
    keyTyped :
      {a v : FinEl} ->
      EdgeIn (mkSigma a v) f ->
      FinMem a b

record SatFinFun (b : FinEl) : Set where
  field
    graph : FinFun
    typed : TypedGraph b graph
    sat   : CoherentFunTail graph

------------------------------------------------------------------------
-- Or -- sum type
------------------------------------------------------------------------

data Or (A B : Set) : Set where
  left  : A -> Or A B
  right : B -> Or A B

------------------------------------------------------------------------
-- Lookup lemmas for FinMemAllU / FinMemFun
------------------------------------------------------------------------

FinMemAllU-lookup :
  (f : FinFun) (b : FinEl) -> FinMemAllU f b ->
  (e : Edge) -> EdgeIn e f ->
  Pair (FinMem (fst e) b) (FinMem (snd e) UCode)
FinMemAllU-lookup (cons e es) b fmem .e here = fst fmem
FinMemAllU-lookup (cons e' es) b fmem e (there ein) =
  FinMemAllU-lookup es b (snd fmem) e ein

FinMemFun-lookup :
  (g : FinFun) (b : FinEl) (f : FinFun) -> FinMemFun g b f ->
  (e : Edge) -> EdgeIn e g ->
  Pair (FinMem (fst e) b) (FinMem (snd e) (EvalFun f (fst e)))
FinMemFun-lookup (cons e es) b f fmem .e here = fst fmem
FinMemFun-lookup (cons e' es) b f fmem e (there ein) =
  FinMemFun-lookup es b f (snd fmem) e ein

------------------------------------------------------------------------
-- Selection data type
------------------------------------------------------------------------

data Selection : FinFun -> FinEl -> FinEl -> Set where
  sel-nil  : Selection nil Bot Bot
  sel-skip : {p : Edge} {g : FinFun} {u v : FinEl} ->
             Selection g u v ->
             Selection (cons p g) u v
  sel-take : {p : Edge} {u v : FinEl} {g : FinFun} ->
             Comp (fst p) u ->
             Comp (snd p) v ->
             Selection g u v ->
             Selection (cons p g) (Sup (fst p) u) (Sup (snd p) v)

------------------------------------------------------------------------
-- Selection helpers
------------------------------------------------------------------------

sel-skip-all : (g : FinFun) -> Selection g Bot Bot
sel-skip-all nil         = sel-nil
sel-skip-all (cons p ps) = sel-skip (sel-skip-all ps)

singleton-selection : (e : Edge) (g : FinFun) ->
  EdgeIn e g -> Selection g (Sup (fst e) Bot) (Sup (snd e) Bot)
singleton-selection e (cons .e es) here =
  sel-take (comp-Bot-r (fst e)) (comp-Bot-r (snd e)) (sel-skip-all es)
singleton-selection e (cons p es) (there ein) =
  sel-skip (singleton-selection e es ein)

Coherent-Selection : {f : FinFun} {u v : FinEl} ->
  Selection f u v -> CoherentFunTail f -> Coherent u
Coherent-Selection sel-nil cf = tt
Coherent-Selection (sel-skip sel-nil) cf = tt
Coherent-Selection (sel-skip (sel-skip sel)) cf =
  Coherent-Selection (sel-skip sel) (CFTcons.tail-coh cf)
Coherent-Selection (sel-skip (sel-take ck cv sel)) cf =
  Coherent-Selection (sel-take ck cv sel) (CFTcons.tail-coh cf)
Coherent-Selection (sel-take {p} comp-key comp-val sel-nil) cf =
  Coherent-Sup (fst p) Bot comp-key
    (CFTcons.key-coh cf) tt
Coherent-Selection (sel-take {p} comp-key comp-val (sel-skip sel)) cf =
  Coherent-Sup (fst p) _ comp-key
    (CFTcons.key-coh cf)
    (Coherent-Selection (sel-skip sel) (CFTcons.tail-coh cf))
Coherent-Selection (sel-take {p} comp-key comp-val (sel-take ck cv sel)) cf =
  Coherent-Sup (fst p) _ comp-key
    (CFTcons.key-coh cf)
    (Coherent-Selection (sel-take ck cv sel) (CFTcons.tail-coh cf))

Coherent-Selection-val : {f : FinFun} {u v : FinEl} ->
  Selection f u v -> CoherentFunTail f -> Coherent v
Coherent-Selection-val sel-nil cf = tt
Coherent-Selection-val (sel-skip sel-nil) cf = tt
Coherent-Selection-val (sel-skip (sel-skip sel)) cf =
  Coherent-Selection-val (sel-skip sel) (CFTcons.tail-coh cf)
Coherent-Selection-val (sel-skip (sel-take ck cv sel)) cf =
  Coherent-Selection-val (sel-take ck cv sel) (CFTcons.tail-coh cf)
Coherent-Selection-val (sel-take {p} comp-key comp-val sel-nil) cf =
  Coherent-Sup (snd p) Bot comp-val
    (CFTcons.val-coh cf) tt
Coherent-Selection-val (sel-take {p} comp-key comp-val (sel-skip sel)) cf =
  Coherent-Sup (snd p) _ comp-val
    (CFTcons.val-coh cf)
    (Coherent-Selection-val (sel-skip sel) (CFTcons.tail-coh cf))
Coherent-Selection-val (sel-take {p} comp-key comp-val (sel-take ck cv sel)) cf =
  Coherent-Sup (snd p) _ comp-val
    (CFTcons.val-coh cf)
    (Coherent-Selection-val (sel-take ck cv sel) (CFTcons.tail-coh cf))

FinMem-Selection : {g : FinFun} {u v : FinEl} ->
  (b : FinEl) (f : FinFun) ->
  Selection g u v -> FinMemFun g b f -> CoherentFunTail g ->
  Coherent b -> FinMem b UCode ->
  FinMem u b
FinMem-Selection b f sel-nil fmg cg cb bU = finMem-bot-from b bU
FinMem-Selection b f (sel-skip sel-nil) fmg cg cb bU = finMem-bot-from b bU
FinMem-Selection b f (sel-skip (sel-skip sel)) fmg cg cb bU =
  FinMem-Selection b f (sel-skip sel) (snd fmg) (CFTcons.tail-coh cg) cb bU
FinMem-Selection b f (sel-skip (sel-take ck cv sel)) fmg cg cb bU =
  FinMem-Selection b f (sel-take ck cv sel) (snd fmg) (CFTcons.tail-coh cg) cb bU
FinMem-Selection b f (sel-take {p} comp-key comp-val sel-nil) fmg cg cb bU =
  FinMem-Sup-element (fst p) Bot b comp-key cb
    (fst (fst fmg))
    (finMem-bot-from b bU)
FinMem-Selection b f (sel-take {p} comp-key comp-val (sel-skip sel)) fmg cg cb bU =
  FinMem-Sup-element (fst p) _ b comp-key cb
    (fst (fst fmg))
    (FinMem-Selection b f (sel-skip sel) (snd fmg) (CFTcons.tail-coh cg) cb bU)
FinMem-Selection b f (sel-take {p} comp-key comp-val (sel-take ck cv sel)) fmg cg cb bU =
  FinMem-Sup-element (fst p) _ b comp-key cb
    (fst (fst fmg))
    (FinMem-Selection b f (sel-take ck cv sel) (snd fmg) (CFTcons.tail-coh cg) cb bU)

FinMemAllU-Selection : {f : FinFun} {u v : FinEl} ->
  (b : FinEl) ->
  Selection f u v -> FinMemAllU f b -> CoherentFunTail f ->
  Coherent b -> FinMem b UCode ->
  FinMem u b
FinMemAllU-Selection b sel-nil allU cf cb bU = finMem-bot-from b bU
FinMemAllU-Selection b (sel-skip sel-nil) allU cf cb bU = finMem-bot-from b bU
FinMemAllU-Selection b (sel-skip (sel-skip sel)) allU cf cb bU =
  FinMemAllU-Selection b (sel-skip sel) (snd allU) (CFTcons.tail-coh cf) cb bU
FinMemAllU-Selection b (sel-skip (sel-take ck cv sel)) allU cf cb bU =
  FinMemAllU-Selection b (sel-take ck cv sel) (snd allU) (CFTcons.tail-coh cf) cb bU
FinMemAllU-Selection b (sel-take {p} comp-key comp-val sel-nil) allU cf cb bU =
  FinMem-Sup-element (fst p) Bot b comp-key cb
    (fst (fst allU))
    (finMem-bot-from b bU)
FinMemAllU-Selection b (sel-take {p} comp-key comp-val (sel-skip sel)) allU cf cb bU =
  FinMem-Sup-element (fst p) _ b comp-key cb
    (fst (fst allU))
    (FinMemAllU-Selection b (sel-skip sel) (snd allU) (CFTcons.tail-coh cf) cb bU)
FinMemAllU-Selection b (sel-take {p} comp-key comp-val (sel-take ck cv sel)) allU cf cb bU =
  FinMem-Sup-element (fst p) _ b comp-key cb
    (fst (fst allU))
    (FinMemAllU-Selection b (sel-take ck cv sel) (snd allU) (CFTcons.tail-coh cf) cb bU)

FinMem-Selection-UCode : {f : FinFun} {u v : FinEl} ->
  (b : FinEl) ->
  Selection f u v -> FinMemAllU f b -> CoherentFunTail f ->
  FinMem v UCode
FinMem-Selection-UCode b sel-nil allU cf = tt
FinMem-Selection-UCode b (sel-skip sel-nil) allU cf = tt
FinMem-Selection-UCode b (sel-skip (sel-skip sel)) allU cf =
  FinMem-Selection-UCode b (sel-skip sel) (snd allU) (CFTcons.tail-coh cf)
FinMem-Selection-UCode b (sel-skip (sel-take ck cv sel)) allU cf =
  FinMem-Selection-UCode b (sel-take ck cv sel) (snd allU) (CFTcons.tail-coh cf)
FinMem-Selection-UCode b (sel-take {p} comp-key comp-val sel-nil) allU cf =
  FinMem-Sup-element (snd p) Bot UCode comp-val tt
    (snd (fst allU))
    tt
FinMem-Selection-UCode b (sel-take {p} comp-key comp-val (sel-skip sel)) allU cf =
  FinMem-Sup-element (snd p) _ UCode comp-val tt
    (snd (fst allU))
    (FinMem-Selection-UCode b (sel-skip sel) (snd allU) (CFTcons.tail-coh cf))
FinMem-Selection-UCode b (sel-take {p} comp-key comp-val (sel-take ck cv sel)) allU cf =
  FinMem-Sup-element (snd p) _ UCode comp-val tt
    (snd (fst allU))
    (FinMem-Selection-UCode b (sel-take ck cv sel) (snd allU) (CFTcons.tail-coh cf))

------------------------------------------------------------------------
-- selectionBelow
------------------------------------------------------------------------

selectionBelow-step : (n : Nat) (p : Edge) (rest : FinFun) (x : FinEl) ->
  Eq (leFinEl (fst p) x) n ->
  CoherentFunTail (cons p rest) -> Coherent x ->
  (u : FinEl) -> (v : FinEl) ->
  Selection rest u v -> LeCode u x -> Eq (EvalFun rest x) v ->
  Sigma FinEl \ u' -> Sigma FinEl \ v' ->
    Pair (Selection (cons p rest) u' v')
         (Pair (LeCode u' x) (Eq (EvalFun-step n (snd p) rest x) v'))
selectionBelow-step zero p rest x eq cf cx u v sel le eqv =
  mkSigma u (mkSigma v (mkSigma (sel-skip sel) (mkSigma le eqv)))
selectionBelow-step (suc m) p rest x eq cf cx u v sel le eqv =
  let le-k = leFinEl-sound (fst p) x (Eq-transport isPos (Eq-sym eq) tt)
      comp-ku = LeCode-Comp (fst p) u x cx le-k le
      comp-vr = Eq-transport (Comp (snd p)) eqv
                  (Comp-value-EvalFun p rest x le-k cx
                    (CFTcons.val-coh cf)
                    (CFTcons.compat cf)
                    (coherentWith-to-compStepFun p rest (CFTcons.compat cf)))
  in mkSigma (Sup (fst p) u) (mkSigma (Sup (snd p) v)
       (mkSigma (sel-take comp-ku comp-vr sel)
         (mkSigma (LeCode-Sup-lub (fst p) u x le-k le)
                  (Eq-cong (Sup (snd p)) eqv))))

selectionBelow :
  (f : FinFun) (x : FinEl) ->
  CoherentFunTail f -> Coherent x ->
  Sigma FinEl \ u ->
  Sigma FinEl \ v ->
    Pair (Selection f u v)
         (Pair (LeCode u x) (Eq (EvalFun f x) v))
selectionBelow nil x cf cx =
  mkSigma Bot (mkSigma Bot (mkSigma sel-nil (mkSigma (LeCode-Bot x) refl)))
selectionBelow (cons p nil) x cf cx =
  selectionBelow-step (leFinEl (fst p) x) p nil x refl cf cx
       Bot Bot sel-nil (LeCode-Bot x) refl
selectionBelow (cons p (cons q qs)) x cf cx =
  let ih = selectionBelow (cons q qs) x (CFTcons.tail-coh cf) cx
  in selectionBelow-step (leFinEl (fst p) x) p (cons q qs) x refl cf cx
       (fst ih) (fst (snd ih))
       (fst (snd (snd ih))) (fst (snd (snd (snd ih)))) (snd (snd (snd (snd ih))))

------------------------------------------------------------------------
-- Selection-le-EvalFun
------------------------------------------------------------------------

Selection-le-EvalFun : {f : FinFun} {u v : FinEl} ->
  (g : FinFun) ->
  Selection f u v -> LeFunCode f g ->
  CoherentFunTail f -> CoherentFunTail g -> Coherent u ->
  LeCode v (EvalFun g u)
Selection-le-EvalFun g sel-nil lf cf cg cu = LeCode-Bot (EvalFun g Bot)
Selection-le-EvalFun g (sel-skip sel-nil) lf cf cg cu = LeCode-Bot (EvalFun g Bot)
Selection-le-EvalFun g (sel-skip (sel-skip sel)) lf cf cg cu =
  Selection-le-EvalFun g (sel-skip sel) (snd lf) (CFTcons.tail-coh cf) cg cu
Selection-le-EvalFun g (sel-skip (sel-take ck cv sel)) lf cf cg cu =
  Selection-le-EvalFun g (sel-take ck cv sel) (snd lf) (CFTcons.tail-coh cf) cg cu
Selection-le-EvalFun g (sel-take {p} comp-key comp-val sel-nil) lf cf cg cu =
  let cu-inner = tt
      cv-inner = tt
      cp = CFTcons.key-coh cf
      cpv = CFTcons.val-coh cf
      le-v0 = fst lf
      ih = LeCode-Bot (EvalFun g Bot)
      cu-sup = Coherent-Sup (fst p) Bot comp-key cp tt
      c-ef-p = Coherent-EvalFun g (fst p) cg cp
      c-ef-u = Coherent-EvalFun g Bot cg tt
      c-ef-sup = Coherent-EvalFun g (Sup (fst p) Bot) cg cu-sup
      le-key-sup = LeCode-Sup-left (fst p) Bot comp-key cp tt
      le-u-sup = LeCode-Sup-right (fst p) Bot comp-key cp tt
      le-ef-p = EvalFun-mon-arg g (fst p) (Sup (fst p) Bot) le-key-sup cg cp cu-sup
      le-ef-u = EvalFun-mon-arg g Bot (Sup (fst p) Bot) le-u-sup cg tt cu-sup
      le-v0-sup = LeCode-trans (snd p) (EvalFun g (fst p)) (EvalFun g (Sup (fst p) Bot))
                    cpv c-ef-p c-ef-sup le-v0 le-ef-p
      le-v-sup = LeCode-trans Bot (EvalFun g Bot) (EvalFun g (Sup (fst p) Bot))
                   tt c-ef-u c-ef-sup ih le-ef-u
  in LeCode-Sup-lub (snd p) Bot (EvalFun g (Sup (fst p) Bot)) le-v0-sup le-v-sup
Selection-le-EvalFun g (sel-take {p} {u} {v} comp-key comp-val (sel-skip sel)) lf cf cg cu =
  let cu-inner = Coherent-Selection (sel-skip sel) (CFTcons.tail-coh cf)
      cv-inner = Coherent-Selection-val (sel-skip sel) (CFTcons.tail-coh cf)
      cp = CFTcons.key-coh cf
      cpv = CFTcons.val-coh cf
      le-v0 = fst lf
      ih = Selection-le-EvalFun g (sel-skip sel) (snd lf) (CFTcons.tail-coh cf) cg cu-inner
      cu-sup = Coherent-Sup (fst p) u comp-key cp cu-inner
      c-ef-p = Coherent-EvalFun g (fst p) cg cp
      c-ef-u = Coherent-EvalFun g u cg cu-inner
      c-ef-sup = Coherent-EvalFun g (Sup (fst p) u) cg cu-sup
      le-key-sup = LeCode-Sup-left (fst p) u comp-key cp cu-inner
      le-u-sup = LeCode-Sup-right (fst p) u comp-key cp cu-inner
      le-ef-p = EvalFun-mon-arg g (fst p) (Sup (fst p) u) le-key-sup cg cp cu-sup
      le-ef-u = EvalFun-mon-arg g u (Sup (fst p) u) le-u-sup cg cu-inner cu-sup
      le-v0-sup = LeCode-trans (snd p) (EvalFun g (fst p)) (EvalFun g (Sup (fst p) u))
                    cpv c-ef-p c-ef-sup le-v0 le-ef-p
      le-v-sup = LeCode-trans v (EvalFun g u) (EvalFun g (Sup (fst p) u))
                   cv-inner c-ef-u c-ef-sup ih le-ef-u
  in LeCode-Sup-lub (snd p) v (EvalFun g (Sup (fst p) u)) le-v0-sup le-v-sup
Selection-le-EvalFun g (sel-take {p} {u} {v} comp-key comp-val (sel-take ck cv sel)) lf cf cg cu =
  let cu-inner = Coherent-Selection (sel-take ck cv sel) (CFTcons.tail-coh cf)
      cv-inner = Coherent-Selection-val (sel-take ck cv sel) (CFTcons.tail-coh cf)
      cp = CFTcons.key-coh cf
      cpv = CFTcons.val-coh cf
      le-v0 = fst lf
      ih = Selection-le-EvalFun g (sel-take ck cv sel) (snd lf) (CFTcons.tail-coh cf) cg cu-inner
      cu-sup = Coherent-Sup (fst p) u comp-key cp cu-inner
      c-ef-p = Coherent-EvalFun g (fst p) cg cp
      c-ef-u = Coherent-EvalFun g u cg cu-inner
      c-ef-sup = Coherent-EvalFun g (Sup (fst p) u) cg cu-sup
      le-key-sup = LeCode-Sup-left (fst p) u comp-key cp cu-inner
      le-u-sup = LeCode-Sup-right (fst p) u comp-key cp cu-inner
      le-ef-p = EvalFun-mon-arg g (fst p) (Sup (fst p) u) le-key-sup cg cp cu-sup
      le-ef-u = EvalFun-mon-arg g u (Sup (fst p) u) le-u-sup cg cu-inner cu-sup
      le-v0-sup = LeCode-trans (snd p) (EvalFun g (fst p)) (EvalFun g (Sup (fst p) u))
                    cpv c-ef-p c-ef-sup le-v0 le-ef-p
      le-v-sup = LeCode-trans v (EvalFun g u) (EvalFun g (Sup (fst p) u))
                   cv-inner c-ef-u c-ef-sup ih le-ef-u
  in LeCode-Sup-lub (snd p) v (EvalFun g (Sup (fst p) u)) le-v0-sup le-v-sup

------------------------------------------------------------------------
-- FinMem-Selection-codomain
------------------------------------------------------------------------

FinMem-Selection-codomain : {g : FinFun} {u v : FinEl} ->
  (b : FinEl) (f : FinFun) ->
  Selection g u v -> FinMemFun g b f -> CoherentFunTail g ->
  CoherentFunTail f -> FinMemAllU f b ->
  FinMem v (EvalFun f u)
FinMem-Selection-codomain b f sel-nil fmg cg cf allU =
  finMem-bot-from (EvalFun f Bot) (EvalFun-in-UCode f Bot b cf tt allU)
FinMem-Selection-codomain b f (sel-skip sel-nil) fmg cg cf allU =
  finMem-bot-from (EvalFun f Bot) (EvalFun-in-UCode f Bot b cf tt allU)
FinMem-Selection-codomain b f (sel-skip (sel-skip sel)) fmg cg cf allU =
  FinMem-Selection-codomain b f (sel-skip sel) (snd fmg) (CFTcons.tail-coh cg) cf allU
FinMem-Selection-codomain b f (sel-skip (sel-take ck cv sel)) fmg cg cf allU =
  FinMem-Selection-codomain b f (sel-take ck cv sel) (snd fmg) (CFTcons.tail-coh cg) cf allU
FinMem-Selection-codomain b f
  (sel-take {p} comp-key comp-val sel-nil) fmg cg cf allU =
  let cu = tt
      cv = tt
      ck = CFTcons.key-coh cg
      cpv = CFTcons.val-coh cg
      cu-sup = Coherent-Sup (fst p) Bot comp-key ck tt
      ih = finMem-bot-from (EvalFun f Bot) (EvalFun-in-UCode f Bot b cf tt allU)
      c-efp = Coherent-EvalFun f (fst p) cf ck
      c-efu = Coherent-EvalFun f Bot cf tt
      c-efsup = Coherent-EvalFun f (Sup (fst p) Bot) cf cu-sup
      le-k-sup = LeCode-Sup-left (fst p) Bot comp-key ck tt
      le-u-sup = LeCode-Sup-right (fst p) Bot comp-key ck tt
      le-efp = EvalFun-mon-arg f (fst p) (Sup (fst p) Bot) le-k-sup cf ck cu-sup
      le-efu = EvalFun-mon-arg f Bot (Sup (fst p) Bot) le-u-sup cf tt cu-sup
      efSupU = EvalFun-in-UCode f (Sup (fst p) Bot) b cf cu-sup allU
      mem-p = finMem-upward (snd p) (EvalFun f (fst p)) (EvalFun f (Sup (fst p) Bot))
                le-efp c-efp c-efsup (snd (fst fmg)) efSupU
      mem-ih = finMem-upward Bot (EvalFun f Bot) (EvalFun f (Sup (fst p) Bot))
                le-efu c-efu c-efsup ih efSupU
  in FinMem-Sup-element (snd p) Bot (EvalFun f (Sup (fst p) Bot))
       comp-val c-efsup mem-p mem-ih
FinMem-Selection-codomain b f
  (sel-take {p} {u} {v} comp-key comp-val (sel-skip sel)) fmg cg cf allU =
  let cu = Coherent-Selection (sel-skip sel) (CFTcons.tail-coh cg)
      cv0 = Coherent-Selection-val (sel-skip sel) (CFTcons.tail-coh cg)
      ck = CFTcons.key-coh cg
      cpv = CFTcons.val-coh cg
      cu-sup = Coherent-Sup (fst p) u comp-key ck cu
      ih = FinMem-Selection-codomain b f (sel-skip sel) (snd fmg) (CFTcons.tail-coh cg) cf allU
      c-efp = Coherent-EvalFun f (fst p) cf ck
      c-efu = Coherent-EvalFun f u cf cu
      c-efsup = Coherent-EvalFun f (Sup (fst p) u) cf cu-sup
      le-k-sup = LeCode-Sup-left (fst p) u comp-key ck cu
      le-u-sup = LeCode-Sup-right (fst p) u comp-key ck cu
      le-efp = EvalFun-mon-arg f (fst p) (Sup (fst p) u) le-k-sup cf ck cu-sup
      le-efu = EvalFun-mon-arg f u (Sup (fst p) u) le-u-sup cf cu cu-sup
      efSupU = EvalFun-in-UCode f (Sup (fst p) u) b cf cu-sup allU
      mem-p = finMem-upward (snd p) (EvalFun f (fst p)) (EvalFun f (Sup (fst p) u))
                le-efp c-efp c-efsup (snd (fst fmg)) efSupU
      mem-ih = finMem-upward v (EvalFun f u) (EvalFun f (Sup (fst p) u))
                le-efu c-efu c-efsup ih efSupU
  in FinMem-Sup-element (snd p) v (EvalFun f (Sup (fst p) u))
       comp-val c-efsup mem-p mem-ih
FinMem-Selection-codomain b f
  (sel-take {p} {u} {v} comp-key comp-val (sel-take ck cv sel)) fmg cg cf allU =
  let cu = Coherent-Selection (sel-take ck cv sel) (CFTcons.tail-coh cg)
      cv' = Coherent-Selection-val (sel-take ck cv sel) (CFTcons.tail-coh cg)
      ck' = CFTcons.key-coh cg
      cpv = CFTcons.val-coh cg
      cu-sup = Coherent-Sup (fst p) u comp-key ck' cu
      ih = FinMem-Selection-codomain b f (sel-take ck cv sel) (snd fmg) (CFTcons.tail-coh cg) cf allU
      c-efp = Coherent-EvalFun f (fst p) cf ck'
      c-efu = Coherent-EvalFun f u cf cu
      c-efsup = Coherent-EvalFun f (Sup (fst p) u) cf cu-sup
      le-k-sup = LeCode-Sup-left (fst p) u comp-key ck' cu
      le-u-sup = LeCode-Sup-right (fst p) u comp-key ck' cu
      le-efp = EvalFun-mon-arg f (fst p) (Sup (fst p) u) le-k-sup cf ck' cu-sup
      le-efu = EvalFun-mon-arg f u (Sup (fst p) u) le-u-sup cf cu cu-sup
      efSupU = EvalFun-in-UCode f (Sup (fst p) u) b cf cu-sup allU
      mem-p = finMem-upward (snd p) (EvalFun f (fst p)) (EvalFun f (Sup (fst p) u))
                le-efp c-efp c-efsup (snd (fst fmg)) efSupU
      mem-ih = finMem-upward v (EvalFun f u) (EvalFun f (Sup (fst p) u))
                le-efu c-efu c-efsup ih efSupU
  in FinMem-Sup-element (snd p) v (EvalFun f (Sup (fst p) u))
       comp-val c-efsup mem-p mem-ih

------------------------------------------------------------------------
-- EvalFun-le-graph
------------------------------------------------------------------------

EvalFun-le-graph : (g' g : FinFun) (x : FinEl) ->
  LeFunCode g' g -> CoherentFunTail g' -> CoherentFunTail g -> Coherent x ->
  LeCode (EvalFun g' x) (EvalFun g x)
EvalFun-le-graph g' g x lf cg' cg cx =
  let sb = selectionBelow g' x cg' cx
      u' = fst sb
      v' = fst (snd sb)
      sel' = fst (snd (snd sb))
      le-u' = fst (snd (snd (snd sb)))
      eq-v' = snd (snd (snd (snd sb)))
      cu' = Coherent-Selection sel' cg'
      cv' = Coherent-Selection-val sel' cg'
      le-v'-gu' = Selection-le-EvalFun g sel' lf cg' cg cu'
      c-gu' = Coherent-EvalFun g u' cg cu'
      c-gx = Coherent-EvalFun g x cg cx
      le-gu'-gx = EvalFun-mon-arg g u' x le-u' cg cu' cx
      le-v'-gx = LeCode-trans v' (EvalFun g u') (EvalFun g x) cv' c-gu' c-gx le-v'-gu' le-gu'-gx
  in Eq-transport (\ z -> LeCode z (EvalFun g x)) (Eq-sym eq-v') le-v'-gx
