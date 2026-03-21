{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- FinitaryProjection.agda
--
-- Finitary projection on finite elements, corresponding to
-- Proposition 1 of Coquand & Huber (2018).
--
-- pCode a u : FinEl  with  pCode a u = u  iff  FinMem u a
--
-- Both directions proved (backward needs Coherent u and FinMem a UCode).
--
-- Note: LeCode (pCode a u) u does NOT hold in general for function
-- elements because projected keys are smaller, which can reduce
-- EvalFun at that key below the projected value.
------------------------------------------------------------------------

module FinitaryProjection where

import Basic as S
open S using (Nat ; zero ; suc ; Top ; tt ; Empty ; Sigma ; mkSigma ;
              fst ; snd ; Pair ; List ; nil ; cons ; Eq ; refl ;
              Eq-transport ; Eq-sym ; Eq-cong ;
              FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ;
              pair-eq ; cons-eq)
open import PaperSemantics using (EvalFun ; FinMem ; FinMemFun ; FinMemAllU ;
  Coherent ; CoherentFun ; CoherentFunTail ; CFTcons ; mkCFT ;
  cft-from-cf ; NotBot ;
  FinMem-a-in-U ; FinMem-coh-u ; EvalFun-in-UCode ;
  LeCode ; LeFunCode ; LeCode-refl ;
  Comp ; Comp-down ; Comp-sym ; comp-Bot-r ; LeCode-Comp)

------------------------------------------------------------------------
-- pCode: finitary projection on finite elements
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  pCode : FinEl -> FinEl -> FinEl
  pCode Bot          u            = Bot
  pCode UCode        UCode        = UCode
  pCode UCode        Bot          = Bot
  pCode UCode        (FunEl g)    = Bot
  pCode UCode        (PiCode a f) = PiCode (pCode UCode a) (projectUFun a f)
  pCode (FunEl g)    u            = Bot
  pCode (PiCode a f) Bot          = Bot
  pCode (PiCode a f) UCode        = Bot
  pCode (PiCode a f) (FunEl g)    = FunEl (projectPiFun a f g)
  pCode (PiCode a f) (PiCode b h) = Bot

  projectUFun : FinEl -> FinFun -> FinFun
  projectUFun a nil         = nil
  projectUFun a (cons p ps) =
    cons (mkSigma (pCode a (fst p)) (pCode UCode (snd p)))
         (projectUFun a ps)

  projectPiFun : FinEl -> FinFun -> FinFun -> FinFun
  projectPiFun a f nil         = nil
  projectPiFun a f (cons p ps) =
    let x' = pCode a (fst p)
    in cons (mkSigma x' (pCode (EvalFun f x') (snd p)))
            (projectPiFun a f ps)

------------------------------------------------------------------------
-- Basic helpers
------------------------------------------------------------------------

PiCode-cong : {a b : FinEl} {f g : FinFun} ->
  Eq a b -> Eq f g -> Eq (PiCode a f) (PiCode b g)
PiCode-cong refl refl = refl

pCode-Bot : (a : FinEl) -> Eq (pCode a Bot) Bot
pCode-Bot Bot          = refl
pCode-Bot UCode        = refl
pCode-Bot (FunEl g)    = refl
pCode-Bot (PiCode a f) = refl

------------------------------------------------------------------------
-- Forward: FinMem u a -> Eq (pCode a u) u
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual
  pCode-forward : (a u : FinEl) -> FinMem u a -> Eq (pCode a u) u

  pCode-forward a Bot mem = pCode-Bot a

  pCode-forward UCode UCode mem = refl
  pCode-forward Bot          UCode ()
  pCode-forward (FunEl g)    UCode ()
  pCode-forward (PiCode a f) UCode ()

  pCode-forward UCode (PiCode a' f') mem =
    let dom-eq = pCode-forward UCode a' (fst mem)
        cod-eq = projectUFun-forward a' f' (fst (snd mem))
    in PiCode-cong dom-eq cod-eq
  pCode-forward Bot          (PiCode a' f') ()
  pCode-forward (FunEl g)    (PiCode a' f') ()
  pCode-forward (PiCode b h) (PiCode a' f') ()

  pCode-forward (PiCode a f) (FunEl g) mem =
    Eq-cong FunEl (projectPiFun-forward a f g (fst mem))
  pCode-forward Bot       (FunEl g) ()
  pCode-forward UCode     (FunEl g) ()
  pCode-forward (FunEl h) (FunEl g) ()

  projectUFun-forward : (a : FinEl) (f : FinFun) ->
    FinMemAllU f a -> Eq (projectUFun a f) f
  projectUFun-forward a nil mem = refl
  projectUFun-forward a (cons p ps) mem =
    let key-eq = pCode-forward a (fst p) (fst (fst mem))
        val-eq = pCode-forward UCode (snd p) (snd (fst mem))
        tail-eq = projectUFun-forward a ps (snd mem)
    in cons-eq (pair-eq key-eq val-eq) tail-eq

  projectPiFun-forward : (a : FinEl) (f : FinFun) (g : FinFun) ->
    FinMemFun g a f -> Eq (projectPiFun a f g) g
  projectPiFun-forward a f nil mem = refl
  projectPiFun-forward a f (cons p ps) mem =
    let key-eq = pCode-forward a (fst p) (fst (fst mem))
        val-eq = Eq-transport
          (\ x -> Eq (pCode (EvalFun f x) (snd p)) (snd p))
          (Eq-sym key-eq)
          (pCode-forward (EvalFun f (fst p)) (snd p) (snd (fst mem)))
        tail-eq = projectPiFun-forward a f ps (snd mem)
    in cons-eq (pair-eq key-eq val-eq) tail-eq

------------------------------------------------------------------------
-- Backward: Coherent u -> FinMem a UCode -> Eq (pCode a u) u -> FinMem u a
------------------------------------------------------------------------

Bot-not-UCode : Eq Bot UCode -> Empty
Bot-not-UCode ()

Bot-not-FunEl : (g : FinFun) -> Eq Bot (FunEl g) -> Empty
Bot-not-FunEl g ()

Bot-not-PiCode : (a : FinEl) (f : FinFun) -> Eq Bot (PiCode a f) -> Empty
Bot-not-PiCode a f ()

cons-head : {A : Set} {x y : A} {xs ys : List A} ->
  Eq (cons x xs) (cons y ys) -> Eq x y
cons-head refl = refl

cons-tail : {A : Set} {x y : A} {xs ys : List A} ->
  Eq (cons x xs) (cons y ys) -> Eq xs ys
cons-tail refl = refl

FunEl-inj : {g h : FinFun} -> Eq (FunEl g) (FunEl h) -> Eq g h
FunEl-inj refl = refl

PiCode-inj-dom : {a b : FinEl} {f g : FinFun} ->
  Eq (PiCode a f) (PiCode b g) -> Eq a b
PiCode-inj-dom refl = refl

PiCode-inj-cod : {a b : FinEl} {f g : FinFun} ->
  Eq (PiCode a f) (PiCode b g) -> Eq f g
PiCode-inj-cod refl = refl

{-# TERMINATING #-}
mutual
  pCode-backward : (a u : FinEl) -> Coherent u -> FinMem a UCode ->
    Eq (pCode a u) u -> FinMem u a

  -- u = Bot: FinMem Bot a = FinMem a UCode, use hypothesis
  pCode-backward a Bot cu aU eq = aU

  -- a = Bot
  pCode-backward Bot UCode        cu aU eq = Bot-not-UCode eq
  pCode-backward Bot (FunEl g)    cu aU eq = Bot-not-FunEl g eq
  pCode-backward Bot (PiCode b h) cu aU eq = Bot-not-PiCode b h eq

  -- a = UCode
  pCode-backward UCode UCode        cu aU eq = tt
  pCode-backward UCode (FunEl g)    cu aU eq = Bot-not-FunEl g eq
  pCode-backward UCode (PiCode b h) cu aU eq =
    let bU = pCode-backward UCode b (fst cu) tt (PiCode-inj-dom eq)
    in mkSigma bU
         (mkSigma
           (projectUFun-backward b h (snd cu) bU (PiCode-inj-cod eq))
           (snd cu))

  -- a = FunEl g: FinMem (FunEl g) UCode = Empty
  pCode-backward (FunEl g) UCode        cu () eq
  pCode-backward (FunEl g) (FunEl h)    cu () eq
  pCode-backward (FunEl g) (PiCode b h) cu () eq

  -- a = PiCode a' f'
  pCode-backward (PiCode a' f') UCode        cu aU eq = Bot-not-UCode eq
  pCode-backward (PiCode a' f') (FunEl g)    cu aU eq =
    let mkSigma a'U (mkSigma allU cftf') = aU
    in mkSigma
         (projectPiFun-backward a' f' g cu a'U allU cftf' (FunEl-inj eq))
         (mkSigma cu aU)
  pCode-backward (PiCode a' f') (PiCode b h) cu aU eq = Bot-not-PiCode b h eq

  projectUFun-backward : (b : FinEl) (h : FinFun) ->
    CoherentFunTail h -> FinMem b UCode ->
    Eq (projectUFun b h) h -> FinMemAllU h b
  projectUFun-backward b nil cft bU eq = tt
  projectUFun-backward b (cons p ps) cft bU eq =
    let hd-eq = cons-head eq
        key-eq = Eq-cong fst hd-eq
        val-eq = Eq-cong snd hd-eq
        tail-eq = cons-tail eq
    in mkSigma
         (mkSigma (pCode-backward b (fst p) (CFTcons.key-coh cft) bU key-eq)
                  (pCode-backward UCode (snd p) (CFTcons.val-coh cft) tt val-eq))
         (projectUFun-backward b ps (CFTcons.tail-coh cft) bU tail-eq)

  projectPiFun-backward : (a : FinEl) (f : FinFun) (g : FinFun) ->
    CoherentFun g -> FinMem a UCode -> FinMemAllU f a -> CoherentFunTail f ->
    Eq (projectPiFun a f g) g -> FinMemFun g a f
  projectPiFun-backward a f nil         () aU allU cftf eq
  projectPiFun-backward a f (cons p ps) cf aU allU cftf eq =
    let hd-eq = cons-head eq
        key-eq = Eq-cong fst hd-eq
        val-eq-raw = Eq-cong snd hd-eq
        val-eq = Eq-transport
          (\ x -> Eq (pCode (EvalFun f x) (snd p)) (snd p))
          key-eq val-eq-raw
        tail-eq = cons-tail eq
        key-mem = pCode-backward a (fst p) (CFTcons.key-coh cf) aU key-eq
        efp-U   = EvalFun-in-UCode f (fst p) a cftf (CFTcons.key-coh cf) allU
    in mkSigma
         (mkSigma key-mem
                  (pCode-backward (EvalFun f (fst p)) (snd p)
                    (CFTcons.val-coh cf) efp-U val-eq))
         (projectPiFun-backward-tail a f p ps cf aU allU cftf tail-eq)

  projectPiFun-backward-tail : (a : FinEl) (f : FinFun)
    (p : Pair FinEl FinEl) (ps : FinFun) ->
    CoherentFunTail (cons p ps) -> FinMem a UCode ->
    FinMemAllU f a -> CoherentFunTail f ->
    Eq (projectPiFun a f ps) ps -> FinMemFun ps a f
  projectPiFun-backward-tail a f p nil         cft aU allU cftf eq = tt
  projectPiFun-backward-tail a f p (cons q qs) cft aU allU cftf eq =
    projectPiFun-backward a f (cons q qs)
      (CFTcons.tail-coh cft) aU allU cftf eq
