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

------------------------------------------------------------------------
-- Lemma 2: Coherent (pCode a u)
-- Lemma 3: Comp (pCode a u) (pCode a v)   (same type code)
--
-- Both require FinMem a UCode (type well-formedness) to ensure
-- projected values in type-code graphs are non-Bot.
------------------------------------------------------------------------

open import PaperSemantics using (comp-Bot-l ; comp-EvalFun ;
  CompFun ; CompStepFun ; CompStepStep ;
  CoherentWith)

{-# TERMINATING #-}
mutual

  -- Lemma 2: projection output is coherent
  -- Requires FinMem u a (not just Coherent u) to access FinMemAllU etc.
  pCode-coherent : (a u : FinEl) -> FinMem a UCode -> FinMem u a ->
    Coherent (pCode a u)
  pCode-coherent Bot          Bot aU mem = tt
  pCode-coherent UCode        Bot aU mem = tt
  pCode-coherent (FunEl g)    Bot () mem
  pCode-coherent (PiCode a f) Bot aU mem = tt
  pCode-coherent Bot UCode aU ()
  pCode-coherent Bot (FunEl g) aU ()
  pCode-coherent Bot (PiCode b h) aU ()
  pCode-coherent UCode UCode aU mem = tt
  pCode-coherent UCode (FunEl g) aU ()
  pCode-coherent UCode (PiCode b h) aU mem =
    let mkSigma bU (mkSigma allU cfth) = mem
    in mkSigma (pCode-coherent UCode b tt bU)
               (projectUFun-cft b h bU cfth allU)
  pCode-coherent (FunEl g) u () mem
  pCode-coherent (PiCode a f) UCode aU ()
  pCode-coherent (PiCode a f) (FunEl g) aU mem =
    let mkSigma a'U (mkSigma allU cftf) = aU
    in projectPiFun-cf a f g a'U allU cftf (fst mem) (fst (snd mem))
  pCode-coherent (PiCode a f) (PiCode b h) aU ()

  -- CoherentFunTail of projectUFun output
  -- Needs FinMemAllU to ensure values satisfy FinMem (snd p) UCode,
  -- which excludes FunEl values (pCode UCode (FunEl g) = Bot, violating NotBot)
  projectUFun-cft : (b : FinEl) (h : FinFun) ->
    FinMem b UCode -> CoherentFunTail h -> FinMemAllU h b ->
    CoherentFunTail (projectUFun b h)
  projectUFun-cft b nil bU cft allU = tt
  projectUFun-cft b (cons p ps) bU cft allU =
    mkCFT (pCode-coherent b (fst p) bU (fst (fst allU)))
          (pCode-coherent UCode (snd p) tt (snd (fst allU)))
          (pCode-nbot-valU (snd p) (snd (fst allU)) (CFTcons.val-nbot cft))
          (projectUFun-cwt b p ps bU cft allU)
          (projectUFun-cft b ps bU (CFTcons.tail-coh cft) (snd allU))

  -- NotBot for pCode UCode u when FinMem u UCode and NotBot u
  pCode-nbot-valU : (u : FinEl) -> FinMem u UCode -> NotBot u -> NotBot (pCode UCode u)
  pCode-nbot-valU Bot          mem ()
  pCode-nbot-valU UCode        mem nb = tt
  pCode-nbot-valU (FunEl g)    ()  nb
  pCode-nbot-valU (PiCode a f) mem nb = tt

  -- CoherentWith for projectUFun head vs tail
  -- Key compatibility: pCode b (fst p) ~ pCode b (fst q) follows from
  -- both being FinMem in b, hence in Principal b (compatible by LeCode-Comp).
  -- Value compatibility: pCode UCode (snd p) ~ pCode UCode (snd q) similarly.
  projectUFun-cwt : (b : FinEl) (p : Pair FinEl FinEl) (ps : FinFun) ->
    FinMem b UCode -> CoherentFunTail (cons p ps) -> FinMemAllU (cons p ps) b ->
    CoherentWith (mkSigma (pCode b (fst p)) (pCode UCode (snd p)))
                 (projectUFun b ps)
  projectUFun-cwt b p nil bU cft allU = tt
  projectUFun-cwt b p (cons q qs) bU cft allU =
    let step-orig = fst (CFTcons.compat cft)
        -- allU : FinMemAllU (cons p (cons q qs)) b
        -- fst allU : Pair (FinMem (fst p) b) (FinMem (snd p) UCode)
        -- snd allU : FinMemAllU (cons q qs) b
        -- fst (snd allU) : Pair (FinMem (fst q) b) (FinMem (snd q) UCode)
        eq-kp = pCode-forward b (fst p) (fst (fst allU))
        eq-kq = pCode-forward b (fst q) (fst (fst (snd allU)))
        eq-vp = pCode-forward UCode (snd p) (snd (fst allU))
        eq-vq = pCode-forward UCode (snd q) (snd (fst (snd allU)))
    in mkSigma
         (\ ck ->
           let -- ck : Comp (pCode b (fst p)) (pCode b (fst q))
               -- Transport to Comp (fst p) (fst q) using forward eqs
               key-comp = S.Eq-transport (\ x -> Comp x (fst q))
                            eq-kp (S.Eq-transport (\ x -> Comp (pCode b (fst p)) x) eq-kq ck)
               val-comp = step-orig key-comp
               -- Transport back: Comp (snd p) (snd q) → Comp (pCode UCode (snd p)) (pCode UCode (snd q))
           in S.Eq-transport (\ x -> Comp x (pCode UCode (snd q)))
                (S.Eq-sym eq-vp) (S.Eq-transport (\ x -> Comp (snd p) x) (S.Eq-sym eq-vq) val-comp))
         (projectUFun-cwt b p qs bU
            (mkCFT (CFTcons.key-coh cft) (CFTcons.val-coh cft)
                   (CFTcons.val-nbot cft)
                   (snd (CFTcons.compat cft))
                   (CFTcons.tail-coh (CFTcons.tail-coh cft)))
            (mkSigma (fst allU) (snd (snd allU))))

  -- Drop first element from CoherentWith
  projectUFun-cwt-drop-head : {p : Pair FinEl FinEl} {q : Pair FinEl FinEl} {qs : FinFun} ->
    CoherentWith p (cons q qs) -> CoherentWith p qs
  projectUFun-cwt-drop-head (mkSigma _ rest) = rest

  -- Compatibility of pCode c u and pCode c v when both FinMem in c
  -- Uses forward direction: FinMem u c → pCode c u = u, so Comp (pCode c u) (pCode c v)
  -- reduces to Comp u v when both are fixed points.
  -- When one is not a fixed point, pCode gives Bot.
  pCode-comp-from-mem : (c u v : FinEl) -> FinMem c UCode ->
    FinMem u c -> FinMem v c ->
    Comp (pCode c u) (pCode c v) -> Comp (pCode c u) (pCode c v)
  pCode-comp-from-mem c u v cU mu mv comp = comp

  -- CoherentFun of projectPiFun output
  projectPiFun-cf : (a : FinEl) (f : FinFun) (g : FinFun) ->
    FinMem a UCode -> FinMemAllU f a -> CoherentFunTail f ->
    FinMemFun g a f -> CoherentFun g ->
    CoherentFun (projectPiFun a f g)
  projectPiFun-cf a f nil aU allU cftf fmf ()
  projectPiFun-cf a f (cons p nil) aU allU cftf fmf cfg =
    let key-mem = fst (fst fmf)
        val-mem = snd (fst fmf)
        eq-kp = pCode-forward a (fst p) key-mem
        efpU = S.Eq-transport (\ x -> FinMem (EvalFun f x) UCode) (S.Eq-sym eq-kp)
                 (EvalFun-in-UCode f (fst p) a cftf (CFTcons.key-coh cfg) allU)
        val-mem' = S.Eq-transport (\ x -> FinMem (snd p) (EvalFun f x)) (S.Eq-sym eq-kp) val-mem
    in mkCFT (pCode-coherent a (fst p) aU key-mem)
             (pCode-coherent (EvalFun f (pCode a (fst p))) (snd p) efpU val-mem')
             (pCode-nbot-mem (EvalFun f (pCode a (fst p))) (snd p) efpU val-mem' (CFTcons.val-nbot cfg))
             tt tt
  projectPiFun-cf a f (cons p (cons q qs)) aU allU cftf fmf cfg =
    let key-mem = fst (fst fmf)
        val-mem = snd (fst fmf)
        eq-kp = pCode-forward a (fst p) key-mem
        efpU = S.Eq-transport (\ x -> FinMem (EvalFun f x) UCode) (S.Eq-sym eq-kp)
                 (EvalFun-in-UCode f (fst p) a cftf (CFTcons.key-coh cfg) allU)
        val-mem' = S.Eq-transport (\ x -> FinMem (snd p) (EvalFun f x)) (S.Eq-sym eq-kp) val-mem
    in mkCFT (pCode-coherent a (fst p) aU key-mem)
             (pCode-coherent (EvalFun f (pCode a (fst p))) (snd p) efpU val-mem')
             (pCode-nbot-mem (EvalFun f (pCode a (fst p))) (snd p) efpU val-mem' (CFTcons.val-nbot cfg))
             (projectPiFun-cwt a f p (cons q qs) aU allU cftf fmf cfg)
             (projectPiFun-cf a f (cons q qs) aU allU cftf (snd fmf) (CFTcons.tail-coh cfg))

  -- NotBot for pCode c u when FinMem u c and NotBot u
  pCode-nbot-mem : (c u : FinEl) -> FinMem c UCode -> FinMem u c ->
    NotBot u -> NotBot (pCode c u)
  pCode-nbot-mem c Bot cU mem ()
  pCode-nbot-mem Bot UCode cU () nb
  pCode-nbot-mem UCode UCode cU mem nb = tt
  pCode-nbot-mem UCode (FunEl g) cU () nb
  pCode-nbot-mem UCode (PiCode b h) cU mem nb = tt
  pCode-nbot-mem (FunEl g) u () mem nb
  pCode-nbot-mem (PiCode a f) UCode cU () nb
  pCode-nbot-mem (PiCode a f) (FunEl g) cU mem nb = tt
  pCode-nbot-mem (PiCode a f) (PiCode b h) cU () nb

  -- CoherentWith for projectPiFun head vs tail
  projectPiFun-cwt : (a : FinEl) (f : FinFun)
    (p : Pair FinEl FinEl) (ps : FinFun) ->
    FinMem a UCode -> FinMemAllU f a -> CoherentFunTail f ->
    FinMemFun (cons p ps) a f -> CoherentFunTail (cons p ps) ->
    CoherentWith (mkSigma (pCode a (fst p))
                          (pCode (EvalFun f (pCode a (fst p))) (snd p)))
                 (projectPiFun a f ps)
  projectPiFun-cwt a f p nil aU allU cftf fmf cfg = tt
  projectPiFun-cwt a f p (cons q qs) aU allU cftf fmf cfg =
    let step-orig = fst (CFTcons.compat cfg)
        -- step-orig : Comp (fst p) (fst q) → Comp (snd p) (snd q)
        key-mem-p = fst (fst fmf)
        key-mem-q = fst (fst (snd fmf))
        val-mem-p = snd (fst fmf)
        val-mem-q = snd (fst (snd fmf))
        eq-kp = pCode-forward a (fst p) key-mem-p
        eq-kq = pCode-forward a (fst q) key-mem-q
        eq-vp = pCode-forward (EvalFun f (fst p)) (snd p) val-mem-p
        eq-vq = pCode-forward (EvalFun f (fst q)) (snd q) val-mem-q
    in mkSigma
         (\ ck ->
           let -- Transport key comp via forward eqs
               key-comp = S.Eq-transport (\ x -> Comp x (fst q))
                            eq-kp (S.Eq-transport (\ x -> Comp (pCode a (fst p)) x) eq-kq ck)
               val-comp = step-orig key-comp
               -- Transport val comp back through pCode-forward
           in S.Eq-transport
                (\ x -> Comp (pCode (EvalFun f x) (snd p))
                             (pCode (EvalFun f (pCode a (fst q))) (snd q)))
                (S.Eq-sym eq-kp)
                (S.Eq-transport
                  (\ x -> Comp (pCode (EvalFun f (fst p)) (snd p))
                               (pCode (EvalFun f x) (snd q)))
                  (S.Eq-sym eq-kq)
                  (S.Eq-transport (\ x -> Comp x (pCode (EvalFun f (fst q)) (snd q)))
                    (S.Eq-sym eq-vp)
                    (S.Eq-transport (\ x -> Comp (snd p) x) (S.Eq-sym eq-vq) val-comp))))
         (projectPiFun-cwt a f p qs aU allU cftf
           (mkSigma (fst fmf) (snd (snd fmf)))
           (mkCFT (CFTcons.key-coh cfg) (CFTcons.val-coh cfg)
                  (CFTcons.val-nbot cfg)
                  (snd (CFTcons.compat cfg))
                  (CFTcons.tail-coh (CFTcons.tail-coh cfg))))
