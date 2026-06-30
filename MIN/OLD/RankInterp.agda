{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- RankInterp.agda  (MIN/ -- Pi + U fragment)
--
-- Rank-interpolation for the stage-stratified membership, mirroring the
-- stabilisation proof (MemStable.goodMemStab):
--
--   if  RANK x <= suc n,  RANK a <= n,  RANK u <= n,
--       MB.finMem (suc n) x a,  and  LeCode u x,
--   then there is  y  with
--       RANK y <= n,  LeCode u y,  LeCode y x,  MB.finMem n y a.
--
-- Proved by induction on n (goodInterp).  Pi+U only (no Nat noise).
--
-- STATUS (compiles, 0 postulate/pragma; 2 interaction holes remain):
--   * L1  EvalFun-sel-cong : DONE.  EvalFun f k = EvalFun f k' whenever k,k'
--     select the same keys of f -- the lemma that keeps the dependent value
--     type EvalFun f k fixed while the key drops.  (Via leiC-sound/complete.)
--   * goodInterp scaffold + ALL atom/absurd/n=0 cases : DONE.
--   * fm-below / fm-above now carry a  Coherent u / Coherent v  side-condition
--     (the standard well-formedness premise; interpolation is only ever applied
--     to coherent approximants).
--   * FUNEL-BELOW (FunEl g : PiCode b f, from below) : DONE, in the companion
--     module MIN.OLD.RankInterpFunEl (funelBelow).  Per u0-edge (j,d): take
--     the canonical selection of g at j (selectionBelow) giving uSel<=j with
--     EvalFun g j : EvalFun f uSel; interpolate uSel up to uj in [uSel,j] via
--     fm-above, and reduce EvalFun g j down to vj>=d via fm-below; retype
--     vj : EvalFun f uj by upward closure (uSel<=uj).  g' = the (uj,vj) edges;
--     selection preservation is a monotonicity squeeze (no edge-key pinning).
--   * FUNEL-ABOVE (FunEl g : PiCode b f, from above) : DONE, in companion
--     module MIN.OLD.RankInterpFunElAbove (funelAbove).  Dual of FUNEL-BELOW:
--     per g-edge (ka,ca), seed = Sup(fSel,hSel) of the f- and h-selection keys
--     at ka; ua = (fm-below) reduces ka preserving BOTH selections; then ca is
--     lifted up to va in [ca, EvalFun h ua] via fm-above at type EvalFun f ua.
--   * OPEN (2 holes, the type-code shrink PiCode b f : UCode):
--       PICODE-BELOW : from below      PICODE-ABOVE : from above
--     OBSTRUCTION (genuine, not a reuse of the FUNEL infra): the u = PiCode c k
--     case must build y' = PiCode c' k' with c <= c' <= b and k <= k' <= f, all
--     at rank m.  When RANK b = suc m (allowed by bx) the domain MUST shrink to
--     a rank-m c' (= ihb b UCode c), so fa' k' c' forces the family's sample
--     KEYS to be typed c'.  But the level-m IH cannot interpolate at type b
--     (RANK b > m), and there is no operation producing c'-typed sample points
--     from the b-typed selection keys of f (membership is not downward-closed in
--     the type).  Closing this needs a NEW "typed re-sampling over a sub-domain"
--     lemma (a typed analogue of selectionBelow / best-c'-approximant).
------------------------------------------------------------------------

module MIN.OLD.RankInterp where

open import MIN.Domain.Basic
  using ( Top ; tt ; Empty
        ; Nat ; zero ; suc ; max ; isPos
        ; Le ; Le-refl ; Le-suc ; Le-trans ; Le-max-l ; Le-max-r
        ; Pair ; mkSigma ; fst ; snd ; Sigma
        ; Eq ; refl ; Eq-sym ; Eq-transport ; Eq-cong
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode
        ; FinFun ; nil ; cons )
open import MIN.Domain.Order
  using ( RANK ; RANKFun ; EvalFun ; Sup ; Comp ; Coherent ; CoherentFunTail
        ; LeCode ; LeFunCode ; Le-max-lub ; max-mono
        ; LeCode-Bot ; LeCode-refl ; LeCode-trans
        ; LeCode-Sup-left ; LeCode-Sup-right ; LeCode-Sup-lub )
open import MIN.Domain.MemStage
open import MIN.Domain.MemStable
  using ( MemStabPack ; goodMemStab )
open import MIN.Domain.OrderStage using ( leiC ; LeqC )
open import MIN.Domain.OrderBridge
  using ( EvalFun-step ; LeCode-to-LeqC ; LeqC-to-LeCode )
open import MIN.Domain.OrderStable using ( leiC-sound ; leiC-complete )
open import MIN.Model.Selection using ( Edge ; EdgeIn ; here ; there )
open import MIN.OLD.RankInterpFunEl using ( funelBelow )
open import MIN.OLD.RankInterpFunElAbove using ( funelAbove )
open import MIN.OLD.RankInterpPiAbove using ( piAbove )
open import MIN.OLD.RankInterpPiBelow using ( piBelow )

exFalso : {A : Set} -> Empty -> A
exFalso ()

-- staged swap  (a:U)  ->  (Bot : a) ; definitional per type-constructor, but
-- needs `a` destructured to fire the fm' clause (fm' Bot a = fm' a UCode).
swapBot : (n : Nat) (a : FinEl) -> MB.finMem (suc n) a UCode -> MB.finMem (suc n) Bot a
swapBot n Bot          mem = mem
swapBot n UCode        mem = mem
swapBot n (FunEl g)    mem = mem
swapBot n (PiCode a f) mem = mem

------------------------------------------------------------------------
-- L1 : EvalFun selection-congruence.
-- EvalFun f u keys ONLY on whether each edge-key is <= u (leiC zero vs
-- suc), so if k and k' select the SAME keys of f then EvalFun f k =
-- EvalFun f k'.  Keeps the dependent value-type EvalFun f k fixed while
-- the key drops from k to a smaller k'.
------------------------------------------------------------------------

step-cong : (nk nk' : Nat) (bi : FinEl) (ps : FinFun) (k k' : FinEl) ->
  (Eq nk' zero -> Eq nk zero) -> (Eq nk zero -> Eq nk' zero) ->
  Eq (EvalFun ps k) (EvalFun ps k') ->
  Eq (EvalFun-step nk bi ps k) (EvalFun-step nk' bi ps k')
step-cong zero    zero    bi ps k k' f g ih = ih
step-cong (suc n) (suc m) bi ps k k' f g ih = Eq-cong (Sup bi) ih
step-cong zero    (suc m) bi ps k k' f g ih = exFalso (znots (g refl))
  where znots : Eq (suc m) zero -> Empty
        znots ()
step-cong (suc n) zero    bi ps k k' f g ih = exFalso (znots (f refl))
  where znots : Eq (suc n) zero -> Empty
        znots ()

EvalFun-sel-cong : (f : FinFun) (k k' : FinEl) ->
  ((p : Edge) -> EdgeIn p f ->
     Pair (LeqC (fst p) k -> LeqC (fst p) k') (LeqC (fst p) k' -> LeqC (fst p) k)) ->
  Eq (EvalFun f k) (EvalFun f k')
EvalFun-sel-cong nil         k k' h = refl
EvalFun-sel-cong (cons p ps) k k' h =
  step-cong (leiC (fst p) k) (leiC (fst p) k') (snd p) ps k k'
    sel-bwd sel-fwd
    (EvalFun-sel-cong ps k k' (\ q ein -> h q (there ein)))
  where
    sel-bwd : Eq (leiC (fst p) k') zero -> Eq (leiC (fst p) k) zero
    sel-bwd ek' = lemma (leiC (fst p) k) refl
      where
        lemma : (nk : Nat) -> Eq (leiC (fst p) k) nk -> Eq (leiC (fst p) k) zero
        lemma zero    e = e
        lemma (suc w) e =
          exFalso (Eq-transport isPos ek'
            (leiC-complete (fst p) k'
              (fst (h p here) (leiC-sound (fst p) k
                (Eq-transport (\ z -> isPos z) (Eq-sym e) tt)))))
    sel-fwd : Eq (leiC (fst p) k) zero -> Eq (leiC (fst p) k') zero
    sel-fwd ek = lemma (leiC (fst p) k') refl
      where
        lemma : (nk' : Nat) -> Eq (leiC (fst p) k') nk' -> Eq (leiC (fst p) k') zero
        lemma zero    e = e
        lemma (suc w) e =
          exFalso (Eq-transport isPos ek
            (leiC-complete (fst p) k
              (snd (h p here) (leiC-sound (fst p) k'
                (Eq-transport (\ z -> isPos z) (Eq-sym e) tt)))))

------------------------------------------------------------------------
-- Per-stage interpolation pack.
------------------------------------------------------------------------

record InterpPack (n : Nat) : Set where
  field
    -- from below: x:a is the (rank suc n) UPPER bound; lift u up to a typed rank-n elt.
    fm-below : (x a u : FinEl) ->
      Le (RANK x) (suc n) -> Le (RANK a) n -> Le (RANK u) n ->
      Coherent u ->
      MB.finMem (suc n) x a -> LeCode u x ->
      Sigma FinEl (\ y -> Pair (Le (RANK y) n)
        (Pair (LeCode u y) (Pair (LeCode y x) (MB.finMem n y a))))
    -- from above: y:a is the (rank suc n) LOWER bound; lower v down to a typed rank-n elt.
    fm-above : (y a v : FinEl) ->
      Le (RANK y) (suc n) -> Le (RANK a) n -> Le (RANK v) n ->
      Coherent v ->
      MB.finMem (suc n) y a -> LeCode y v ->
      Sigma FinEl (\ w -> Pair (Le (RANK w) n)
        (Pair (LeCode y w) (Pair (LeCode w v) (MB.finMem n w a))))
    -- COUPLED rank+type reduction (the type-code shrink kernel): k:a is a rank-(suc n)
    -- member of the rank-(suc n) type a:U; given a point lower bound u (k<=u) and a type
    -- lower bound b (b<=a), JOINTLY reduce both to rank n:  k<=u'<=u, b<=b'<=a, b':U, u':b'.
    fm-couple : (k a u b : FinEl) ->
      Le (RANK k) (suc n) -> Le (RANK a) (suc n) -> Le (RANK u) n -> Le (RANK b) n ->
      Coherent u -> Coherent b ->
      MB.finMem (suc n) a UCode -> MB.finMem (suc n) k a ->
      LeCode k u -> LeCode b a ->
      Sigma FinEl (\ u' -> Sigma FinEl (\ b' ->
        Pair (Le (RANK u') n) (Pair (Le (RANK b') n)
        (Pair (LeCode k u') (Pair (LeCode u' u)
        (Pair (LeCode b b') (Pair (LeCode b' a)
        (Pair (MB.finMem n b' UCode) (MB.finMem n u' b')))))))))

goodInterp : (n : Nat) -> InterpPack n

goodInterp zero = record { fm-below = belowZ ; fm-above = aboveZ ; fm-couple = coupleZ }
  where
    open MemStabPack (goodMemStab zero) renaming (fm-bwd to bwd)

    coupleZ : (k a u b : FinEl) ->
      Le (RANK k) (suc zero) -> Le (RANK a) (suc zero) -> Le (RANK u) zero -> Le (RANK b) zero ->
      Coherent u -> Coherent b ->
      MB.finMem (suc zero) a UCode -> MB.finMem (suc zero) k a ->
      LeCode k u -> LeCode b a ->
      Sigma FinEl (\ u' -> Sigma FinEl (\ b' ->
        Pair (Le (RANK u') zero) (Pair (Le (RANK b') zero)
        (Pair (LeCode k u') (Pair (LeCode u' u)
        (Pair (LeCode b b') (Pair (LeCode b' a)
        (Pair (MB.finMem zero b' UCode) (MB.finMem zero u' b')))))))))
    -- a = Bot
    coupleZ Bot   Bot u b bk ba bu bb cu cb aU memk lku lba =
      mkSigma Bot (mkSigma Bot (mkSigma tt (mkSigma tt (mkSigma tt (mkSigma tt
        (mkSigma lba (mkSigma tt (mkSigma tt tt))))))))
    coupleZ UCode      Bot u b bk ba bu bb cu cb aU () lku lba
    coupleZ (FunEl g)  Bot u b bk ba bu bb cu cb aU () lku lba
    coupleZ (PiCode c k) Bot u b bk ba bu bb cu cb aU () lku lba
    -- a = UCode
    coupleZ Bot   UCode u b bk ba bu bb cu cb aU memk lku lba =
      mkSigma Bot (mkSigma UCode (mkSigma tt (mkSigma tt (mkSigma tt (mkSigma tt
        (mkSigma lba (mkSigma tt (mkSigma tt tt))))))))
    coupleZ UCode UCode u b bk ba bu bb cu cb aU memk lku lba =
      mkSigma UCode (mkSigma UCode (mkSigma tt (mkSigma tt (mkSigma tt (mkSigma lku
        (mkSigma lba (mkSigma tt (mkSigma tt tt))))))))
    coupleZ (FunEl g)  UCode u b bk ba bu bb cu cb aU () lku lba
    -- k = PiCode (a Pi-TYPE : UCode) : vacuous at level 0 (u would need rank >= 1)
    coupleZ (PiCode c k) UCode Bot          b bk ba bu bb cu cb aU memk () lba
    coupleZ (PiCode c k) UCode UCode        b bk ba bu bb cu cb aU memk () lba
    coupleZ (PiCode c k) UCode (FunEl ug)   b bk ba bu bb cu cb aU memk () lba
    coupleZ (PiCode c k) UCode (PiCode d j) b bk ba () bb cu cb aU memk lku lba
    -- a = FunEl : not a type
    coupleZ k (FunEl g) u b bk ba bu bb cu cb () memk lku lba
    -- a = PiCode
    coupleZ Bot (PiCode a0 fa) u Bot bk ba bu bb cu cb aU memk lku lba =
      mkSigma Bot (mkSigma Bot (mkSigma tt (mkSigma tt (mkSigma tt (mkSigma tt
        (mkSigma tt (mkSigma tt (mkSigma tt tt))))))))
    coupleZ Bot (PiCode a0 fa) u UCode        bk ba bu bb cu cb aU memk lku ()
    coupleZ Bot (PiCode a0 fa) u (FunEl h)    bk ba bu () cu cb aU memk lku lba
    coupleZ Bot (PiCode a0 fa) u (PiCode c k) bk ba bu () cu cb aU memk lku lba
    coupleZ UCode (PiCode a0 fa) u b bk ba bu bb cu cb aU () lku lba
    coupleZ (FunEl kg) (PiCode a0 fa) Bot          b bk ba bu bb cu cb aU memk () lba
    coupleZ (FunEl kg) (PiCode a0 fa) UCode        b bk ba bu bb cu cb aU memk () lba
    coupleZ (FunEl kg) (PiCode a0 fa) (FunEl ug)   b bk ba () bb cu cb aU memk lku lba
    coupleZ (FunEl kg) (PiCode a0 fa) (PiCode c k) b bk ba bu bb cu cb aU memk () lba
    coupleZ (PiCode c k) (PiCode a0 fa) u b bk ba bu bb cu cb aU () lku lba
    belowZ : (x a u : FinEl) ->
      Le (RANK x) (suc zero) -> Le (RANK a) zero -> Le (RANK u) zero ->
      Coherent u ->
      MB.finMem (suc zero) x a -> LeCode u x ->
      Sigma FinEl (\ y -> Pair (Le (RANK y) zero)
        (Pair (LeCode u y) (Pair (LeCode y x) (MB.finMem zero y a))))
    belowZ Bot   a u bx ba bu cu mem lux =
      mkSigma Bot   (mkSigma tt (mkSigma lux (mkSigma tt (bwd Bot   a tt ba mem))))
    belowZ UCode a u bx ba bu cu mem lux =
      mkSigma UCode (mkSigma tt (mkSigma lux (mkSigma tt (bwd UCode a tt ba mem))))
    belowZ (FunEl g) Bot          u bx ba bu cu () lux
    belowZ (FunEl g) UCode        u bx ba bu cu () lux
    belowZ (FunEl g) (FunEl h)    u bx ba bu cu () lux
    belowZ (FunEl g) (PiCode b f) u bx () bu cu mem lux
    belowZ (PiCode b f) Bot       u bx ba bu cu () lux
    belowZ (PiCode b f) UCode     Bot          bx ba bu cu mem lux =
      mkSigma Bot (mkSigma tt (mkSigma tt (mkSigma tt tt)))
    belowZ (PiCode b f) UCode     UCode        bx ba bu cu mem ()
    belowZ (PiCode b f) UCode     (FunEl h)    bx ba () cu mem lux
    belowZ (PiCode b f) UCode     (PiCode c k) bx ba () cu mem lux
    belowZ (PiCode b f) (FunEl h)    u bx ba bu cu () lux
    belowZ (PiCode b f) (PiCode c k) u bx ba bu cu () lux

    aboveZ : (y a v : FinEl) ->
      Le (RANK y) (suc zero) -> Le (RANK a) zero -> Le (RANK v) zero ->
      Coherent v ->
      MB.finMem (suc zero) y a -> LeCode y v ->
      Sigma FinEl (\ w -> Pair (Le (RANK w) zero)
        (Pair (LeCode y w) (Pair (LeCode w v) (MB.finMem zero w a))))
    aboveZ Bot   a v by ba bv cv mem lyv =
      mkSigma Bot   (mkSigma tt (mkSigma tt (mkSigma tt (bwd Bot   a tt ba mem))))
    aboveZ UCode a v by ba bv cv mem lyv =
      mkSigma UCode (mkSigma tt (mkSigma tt (mkSigma lyv (bwd UCode a tt ba mem))))
    aboveZ (FunEl g) Bot          v by ba bv cv () lyv
    aboveZ (FunEl g) UCode        v by ba bv cv () lyv
    aboveZ (FunEl g) (FunEl h)    v by ba bv cv () lyv
    aboveZ (FunEl g) (PiCode b f) v by () bv cv mem lyv
    aboveZ (PiCode b f) a Bot          by ba bv cv mem ()
    aboveZ (PiCode b f) a UCode        by ba bv cv mem ()
    aboveZ (PiCode b f) a (FunEl h)    by ba () cv mem lyv
    aboveZ (PiCode b f) a (PiCode c k) by ba () cv mem lyv

goodInterp (suc m) = record { fm-below = belowS ; fm-above = aboveS ; fm-couple = coupleS }
  where
    open MemStabPack (goodMemStab (suc m)) renaming (fm-bwd to bwd)
    open InterpPack  (goodInterp m) renaming (fm-below to ihb ; fm-above to iha ; fm-couple to ihc)
    belowS : (x a u : FinEl) ->
      Le (RANK x) (suc (suc m)) -> Le (RANK a) (suc m) -> Le (RANK u) (suc m) ->
      Coherent u ->
      MB.finMem (suc (suc m)) x a -> LeCode u x ->
      Sigma FinEl (\ y -> Pair (Le (RANK y) (suc m))
        (Pair (LeCode u y) (Pair (LeCode y x) (MB.finMem (suc m) y a))))
    belowS Bot   a u bx ba bu cu mem lux =
      mkSigma Bot   (mkSigma tt (mkSigma lux (mkSigma tt (bwd Bot   a tt ba mem))))
    belowS UCode a u bx ba bu cu mem lux =
      mkSigma UCode (mkSigma tt (mkSigma lux (mkSigma tt (bwd UCode a tt ba mem))))
    belowS (FunEl g) Bot          u bx ba bu cu () lux
    belowS (FunEl g) UCode        u bx ba bu cu () lux
    belowS (FunEl g) (FunEl h)    u bx ba bu cu () lux
    belowS (FunEl g) (PiCode b f) u bx ba bu cu mem lux =
      funelBelow m g b f iha ihb u bx ba bu cu mem lux
    belowS (PiCode b f) Bot          u bx ba bu cu () lux
    belowS (PiCode b f) UCode Bot          bx ba bu cu mem lux =
      mkSigma Bot (mkSigma tt (mkSigma tt (mkSigma tt tt)))
    belowS (PiCode b f) UCode UCode        bx ba bu cu mem ()
    belowS (PiCode b f) UCode (FunEl h)    bx ba bu cu mem ()
    belowS (PiCode b f) UCode (PiCode c k) bx ba bu cu mem lux =
      piBelow m b f iha ihb ihc c k bx bu cu mem lux
    belowS (PiCode b f) (FunEl h)    u bx ba bu cu () lux
    belowS (PiCode b f) (PiCode c k) u bx ba bu cu () lux

    aboveS : (y a v : FinEl) ->
      Le (RANK y) (suc (suc m)) -> Le (RANK a) (suc m) -> Le (RANK v) (suc m) ->
      Coherent v ->
      MB.finMem (suc (suc m)) y a -> LeCode y v ->
      Sigma FinEl (\ w -> Pair (Le (RANK w) (suc m))
        (Pair (LeCode y w) (Pair (LeCode w v) (MB.finMem (suc m) w a))))
    aboveS Bot   a v by ba bv cv mem lyv =
      mkSigma Bot   (mkSigma tt (mkSigma tt (mkSigma tt (bwd Bot   a tt ba mem))))
    aboveS UCode a v by ba bv cv mem lyv =
      mkSigma UCode (mkSigma tt (mkSigma tt (mkSigma lyv (bwd UCode a tt ba mem))))
    aboveS (FunEl g) Bot          v by ba bv cv () lyv
    aboveS (FunEl g) UCode        v by ba bv cv () lyv
    aboveS (FunEl g) (FunEl h)    v by ba bv cv () lyv
    aboveS (FunEl g) (PiCode b f) v by ba bv cv mem lyv =
      funelAbove m g b f iha ihb v by ba bv cv mem lyv
    aboveS (PiCode b f) Bot          v by ba bv cv () lyv
    aboveS (PiCode b f) UCode        v by ba bv cv mem lyv =
      piAbove m b f iha ihb v by bv cv mem lyv
    aboveS (PiCode b f) (FunEl h)    v by ba bv cv () lyv
    aboveS (PiCode b f) (PiCode c k) v by ba bv cv () lyv

    coupleS : (k a u b : FinEl) ->
      Le (RANK k) (suc (suc m)) -> Le (RANK a) (suc (suc m)) ->
      Le (RANK u) (suc m) -> Le (RANK b) (suc m) ->
      Coherent u -> Coherent b ->
      MB.finMem (suc (suc m)) a UCode -> MB.finMem (suc (suc m)) k a ->
      LeCode k u -> LeCode b a ->
      Sigma FinEl (\ u' -> Sigma FinEl (\ b' ->
        Pair (Le (RANK u') (suc m)) (Pair (Le (RANK b') (suc m))
        (Pair (LeCode k u') (Pair (LeCode u' u)
        (Pair (LeCode b b') (Pair (LeCode b' a)
        (Pair (MB.finMem (suc m) b' UCode) (MB.finMem (suc m) u' b')))))))))
    -- a = Bot
    coupleS Bot   Bot u b bk ba bu bb cu cb aU memk lku lba =
      mkSigma Bot (mkSigma Bot (mkSigma tt (mkSigma tt (mkSigma tt (mkSigma tt
        (mkSigma lba (mkSigma tt (mkSigma tt tt))))))))
    coupleS UCode      Bot u b bk ba bu bb cu cb aU () lku lba
    coupleS (FunEl g)  Bot u b bk ba bu bb cu cb aU () lku lba
    coupleS (PiCode c k) Bot u b bk ba bu bb cu cb aU () lku lba
    -- a = UCode
    coupleS Bot   UCode u b bk ba bu bb cu cb aU memk lku lba =
      mkSigma Bot (mkSigma UCode (mkSigma tt (mkSigma tt (mkSigma tt (mkSigma tt
        (mkSigma lba (mkSigma tt (mkSigma tt tt))))))))
    coupleS UCode UCode u b bk ba bu bb cu cb aU memk lku lba =
      mkSigma UCode (mkSigma UCode (mkSigma tt (mkSigma tt (mkSigma tt (mkSigma lku
        (mkSigma lba (mkSigma tt (mkSigma tt tt))))))))
    coupleS (FunEl g)  UCode u b bk ba bu bb cu cb aU () lku lba
    -- k = PiCode (a Pi-TYPE : UCode) : the type-code shrink = PICODE-ABOVE on (PiCode c k)
    coupleS (PiCode c k) UCode u b bk ba bu bb cu cb aU memk lku lba =
      let r    = aboveS (PiCode c k) UCode u bk tt bu cu memk lku
          w    = fst r
          rw   = fst (snd r)
          lkw  = fst (snd (snd r))
          lwu  = fst (snd (snd (snd r)))
          wU   = snd (snd (snd (snd r)))
      in mkSigma w (mkSigma UCode (mkSigma rw (mkSigma tt (mkSigma lkw (mkSigma lwu
           (mkSigma lba (mkSigma tt (mkSigma tt wU))))))))
    -- a = FunEl : not a type
    coupleS k (FunEl g) u b bk ba bu bb cu cb () memk lku lba
    -- a = PiCode , k = Bot : pure type shrink via belowS
    coupleS Bot (PiCode a0 fa) u b bk ba bu bb cu cb aU memk lku lba =
      let r    = belowS (PiCode a0 fa) UCode b ba tt bb cb aU lba
          b'   = fst r
          rb'  = fst (snd r)
          lbb' = fst (snd (snd r))
          lb'a = fst (snd (snd (snd r)))
          b'U  = snd (snd (snd (snd r)))
      in mkSigma Bot (mkSigma b' (mkSigma tt (mkSigma rb' (mkSigma tt (mkSigma tt
           (mkSigma lbb' (mkSigma lb'a (mkSigma b'U (swapBot m b' b'U)))))))))
    coupleS UCode (PiCode a0 fa) u b bk ba bu bb cu cb aU () lku lba
    coupleS (FunEl kg) (PiCode a0 fa) u b bk ba bu bb cu cb aU memk lku lba = {! COUPLE-FUNEL !}
    coupleS (PiCode c k) (PiCode a0 fa) u b bk ba bu bb cu cb aU () lku lba
