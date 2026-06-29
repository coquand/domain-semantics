{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- FinMemStageProps.agda  (NAT/ — Pi + U fragment)
--
-- The closure / monotonicity PROPERTIES of the collapsed membership
-- finMemC, ported from PaperTyping's block-3 mutual cycle.  The cycle is
-- genuinely non-structural for Agda's foetus checker (it recurses through
-- EvalFun-results / domain-function keys), so it is made structural here
-- by a fuel index `k` bounding the RANK of the type/element arguments:
--   * recursions descending into a PiCode domain DROP the fuel, and
--   * same-fuel recursions decrease the element / FinFun list structurally.
-- Agda accepts the resulting lex (fuel, structure), like LeqStageProps2.
-- Memberships stay at the canonical level (finMemC), destructured /
-- reconstructed by the bound-free unfolding isos of FinMemStageUnfold.
--
-- Then the public, fuel-free properties (collapse the *-k cycle at
-- fuel = the max of the relevant RANKs) + the structural extras
-- (finMem-upward, FinMemFun-append, FinMem-Sup-element, finMem-Sup-both).
--
-- NO postulates.
------------------------------------------------------------------------

module NAT.Domain.MemProps where

open import NAT.Domain.Basic
  using ( Top ; tt ; Empty
        ; Nat ; zero ; suc ; max ; isPos
        ; Le ; Le-refl ; Le-suc ; Le-trans ; Le-max-l ; Le-max-r
        ; Pair ; mkSigma ; fst ; snd
        ; Eq ; refl ; Eq-sym ; Eq-transport
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; FinFun ; nil ; cons )
open import NAT.Domain.Order
  using ( RANK ; RANKFun ; Sup ; append ; EvalFun ; EvalFun-step
        ; Comp ; CompFun ; CompStepFun ; CoherentWith ; LeCode ; LeFunCode
        ; Coherent ; CoherentFun ; CoherentFunTail ; CFTcons ; cft-from-cf
        ; leFinEl ; leFinEl-sound
        ; Comp-value-EvalFun ; Coherent-EvalFun ; comp-EvalFun ; EvalFun-append-eq
        ; EvalFun-mon ; Coherent-Sup ; CoherentFun-append
        ; CoherentFunTail-append ; coherentWith-to-compStepFun
        ; compStepFun-to-coherentWith ; compStepFun-append ; coherentWith-append
        ; Le-max-lub ; RANK-Sup ; RANK-append ; RANK-ev ; ev-bridge )
open import NAT.Domain.MemStage
open import NAT.Domain.MemUnfold

private
  max-Le-l : (a b c : Nat) -> Le (max a b) c -> Le a c
  max-Le-l a b c h = Le-trans a (max a b) c (Le-max-l a b) h

  max-Le-r : (a b c : Nat) -> Le (max a b) c -> Le b c
  max-Le-r a b c h = Le-trans b (max a b) c (Le-max-r a b) h

  b3-x : (x y z : Nat) -> Le x (max x (max y z))
  b3-x x y z = Le-max-l x (max y z)
  b3-y : (x y z : Nat) -> Le y (max x (max y z))
  b3-y x y z = Le-trans y (max y z) (max x (max y z)) (Le-max-l y z) (Le-max-r x (max y z))
  b3-z : (x y z : Nat) -> Le z (max x (max y z))
  b3-z x y z = Le-trans z (max y z) (max x (max y z)) (Le-max-r y z) (Le-max-r x (max y z))

  RANK-EvalFun : (h : FinFun) (u : FinEl) -> Le (RANK (EvalFun h u)) (RANKFun h)
  RANK-EvalFun h u =
    let M = max (RANKFun h) (RANK u)
    in Eq-transport (\ x -> Le (RANK x) (RANKFun h))
         (Eq-sym (ev-bridge M h u (Le-refl M)))
         (RANK-ev (suc M) h u)

  ev-bnd : (k : Nat) (h : FinFun) (u : FinEl) -> Le (RANKFun h) k -> Le (RANK (EvalFun h u)) k
  ev-bnd k h u bh = Le-trans (RANK (EvalFun h u)) (RANKFun h) k (RANK-EvalFun h u) bh

  app-bnd : (k : Nat) (f g : FinFun) -> Le (RANKFun f) k -> Le (RANKFun g) k -> Le (RANKFun (append f g)) k
  app-bnd k f g bf bg =
    Le-trans (RANKFun (append f g)) (max (RANKFun f) (RANKFun g)) k (RANK-append f g) (Le-max-lub (RANKFun f) (RANKFun g) k bf bg)

  rk-key : (p : Pair FinEl FinEl) (ps : FinFun) (k : Nat) -> Le (RANKFun (cons p ps)) k -> Le (RANK (fst p)) k
  rk-key p ps k b = max-Le-l (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps)) k b
  rk-val : (p : Pair FinEl FinEl) (ps : FinFun) (k : Nat) -> Le (RANKFun (cons p ps)) k -> Le (RANK (snd p)) k
  rk-val p ps k b = Le-trans (RANK (snd p)) (max (RANK (snd p)) (RANKFun ps)) k
                      (Le-max-l (RANK (snd p)) (RANKFun ps))
                      (max-Le-r (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps)) k b)
  rk-tail : (p : Pair FinEl FinEl) (ps : FinFun) (k : Nat) -> Le (RANKFun (cons p ps)) k -> Le (RANKFun ps) k
  rk-tail p ps k b = Le-trans (RANKFun ps) (max (RANK (snd p)) (RANKFun ps)) k
                       (Le-max-r (RANK (snd p)) (RANKFun ps))
                       (max-Le-r (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps)) k b)

------------------------------------------------------------------------
-- The fuel-indexed closure cycle.
------------------------------------------------------------------------

mutual
  finMemUCode-Sup-k : (k : Nat) (a c : FinEl) -> Le (RANK a) k -> Le (RANK c) k ->
    Comp a c -> finMemC a UCode -> finMemC c UCode -> finMemC (Sup a c) UCode
  finMemUCode-Sup-k k Bot          c ba bc comp aU cU = cU
  finMemUCode-Sup-k k UCode        Bot          ba bc comp aU cU = aU
  finMemUCode-Sup-k k UCode        UCode        ba bc comp aU cU = aU
  finMemUCode-Sup-k k UCode        (FunEl h)    ba bc () aU cU
  finMemUCode-Sup-k k UCode        (PiCode c h) ba bc () aU cU
  finMemUCode-Sup-k k (FunEl g)    c ba bc comp () cU
  finMemUCode-Sup-k k (PiCode a f) Bot          ba bc comp aU cU = aU
  finMemUCode-Sup-k k (PiCode a f) UCode        ba bc () aU cU
  finMemUCode-Sup-k k (PiCode a f) (FunEl h)    ba bc () aU cU
  finMemUCode-Sup-k zero    (PiCode a f) (PiCode c h) () bc comp aU cU
  finMemUCode-Sup-k k NatCode Bot          ba bc comp aU cU = aU
  finMemUCode-Sup-k k NatCode UCode        ba bc () aU cU
  finMemUCode-Sup-k k NatCode (FunEl h)    ba bc () aU cU
  finMemUCode-Sup-k k NatCode (PiCode c h) ba bc () aU cU
  finMemUCode-Sup-k k NatCode NatCode      ba bc comp aU cU = aU
  finMemUCode-Sup-k k NatCode ZeroEl       ba bc () aU cU
  finMemUCode-Sup-k k NatCode (SucEl c)    ba bc () aU cU
  finMemUCode-Sup-k (suc k) (PiCode a f) (PiCode c h) ba bc comp aU cU =
    let bda = max-Le-l (RANK a) (RANKFun f) k ba
        bfa = max-Le-r (RANK a) (RANKFun f) k ba
        bdc = max-Le-l (RANK c) (RANKFun h) k bc
        bfc = max-Le-r (RANK c) (RANKFun h) k bc
        aDom = finMemC-piU-dom a f aU ; aAll = finMemC-piU-allU a f aU ; aCft = finMemC-piU-cft a f aU
        cDom = finMemC-piU-dom c h cU ; cAll = finMemC-piU-allU c h cU ; cCft = finMemC-piU-cft c h cU
    in finMemC-piU-mk (Sup a c) (append f h)
         (finMemUCode-Sup-k k a c bda bdc (fst comp) aDom cDom)
         (FinMemAllU-append-Sup-k k a c f h bda bdc bfa bfc
            (fst comp) (coh-from-aU a aDom) (coh-from-aU c cDom) aDom cDom aCft cCft aAll cAll)
         (CoherentFunTail-append f h aCft cCft (snd comp))

  FinMemAllU-append-Sup-k : (k : Nat) (d c : FinEl) (f h : FinFun) ->
    Le (RANK d) k -> Le (RANK c) k -> Le (RANKFun f) k -> Le (RANKFun h) k ->
    Comp d c -> Coherent d -> Coherent c ->
    finMemC d UCode -> finMemC c UCode ->
    CoherentFunTail f -> CoherentFunTail h ->
    finMemAllUC f d -> finMemAllUC h c ->
    finMemAllUC (append f h) (Sup d c)
  FinMemAllU-append-Sup-k k d c nil h bd bc bf bh cd cohd cohc dU cU cohf cohh memf memh =
    FinMemAllU-Sup-right-k k d c h bd bc bh cd dU cohc cohh memh
  FinMemAllU-append-Sup-k k d c (cons p ps) h bd bc bf bh cd cohd cohc dU cU cohf cohh memf memh =
    finMemAllUC-mk p (append ps h) (Sup d c)
      (finMem-Sup-left-k k d c (fst p) bd bc (rk-key p ps k bf) cd cohd cohc cU
         (CFTcons.key-coh cohf) (finMemAllUC-hd-key p ps d memf))
      (finMemAllUC-hd-val p ps d memf)
      (FinMemAllU-append-Sup-k k d c ps h bd bc (rk-tail p ps k bf) bh cd cohd cohc dU cU
         (CFTcons.tail-coh cohf) cohh (finMemAllUC-tl p ps d memf) memh)

  FinMemAllU-Sup-right-k : (k : Nat) (d c : FinEl) (h : FinFun) ->
    Le (RANK d) k -> Le (RANK c) k -> Le (RANKFun h) k ->
    Comp d c -> finMemC d UCode -> Coherent c -> CoherentFunTail h ->
    finMemAllUC h c -> finMemAllUC h (Sup d c)
  FinMemAllU-Sup-right-k k d c nil bd bc bh cd dU cohc cohh memh = tt
  FinMemAllU-Sup-right-k k d c (cons p ps) bd bc bh cd dU cohc cohh memh =
    finMemAllUC-mk p ps (Sup d c)
      (finMem-Sup-right-k k d c (fst p) bd bc (rk-key p ps k bh) cd dU
         (CFTcons.key-coh cohh) (finMemAllUC-hd-key p ps c memh))
      (finMemAllUC-hd-val p ps c memh)
      (FinMemAllU-Sup-right-k k d c ps bd bc (rk-tail p ps k bh) cd dU cohc
         (CFTcons.tail-coh cohh) (finMemAllUC-tl p ps c memh))

  EvalFun-in-UCode-k : (k : Nat) (f : FinFun) (x d : FinEl) ->
    Le (RANKFun f) k ->
    CoherentFunTail f -> Coherent x -> finMemAllUC f d -> finMemC (EvalFun f x) UCode
  EvalFun-in-UCode-k k nil x d bf cohf cx allU = tt
  EvalFun-in-UCode-k k (cons q rest) x d bf cohf cx allU =
    EvalFun-in-UCode-step-k k (leFinEl (fst q) x) q rest x d bf refl cohf cx allU

  EvalFun-in-UCode-step-k : (k : Nat) (n : Nat) (q : Pair FinEl FinEl) (rest : FinFun)
    (x d : FinEl) -> Le (RANKFun (cons q rest)) k ->
    Eq n (leFinEl (fst q) x) ->
    CoherentFunTail (cons q rest) -> Coherent x -> finMemAllUC (cons q rest) d ->
    finMemC (EvalFun-step n (snd q) rest x) UCode
  EvalFun-in-UCode-step-k k zero q rest x d bf eq cohf cx allU =
    EvalFun-in-UCode-k k rest x d (rk-tail q rest k bf)
      (CFTcons.tail-coh cohf) cx (finMemAllUC-tl q rest d allU)
  EvalFun-in-UCode-step-k k (suc _) q rest x d bf eq cohf cx allU =
    let vU = finMemAllUC-hd-val q rest d allU
        restU = EvalFun-in-UCode-k k rest x d (rk-tail q rest k bf) (CFTcons.tail-coh cohf) cx (finMemAllUC-tl q rest d allU)
        comp-vr = Comp-value-EvalFun q rest x
                    (leFinEl-sound (fst q) x (Eq-transport isPos eq tt))
                    cx (CFTcons.val-coh cohf) (CFTcons.compat cohf)
                    (coherentWith-to-compStepFun q rest (CFTcons.compat cohf))
    in finMemUCode-Sup-k k (snd q) (EvalFun rest x)
         (rk-val q rest k bf) (ev-bnd k rest x (rk-tail q rest k bf)) comp-vr vU restU

  finMem-Sup-right-k : (k : Nat) (a b u : FinEl) -> Le (RANK a) k -> Le (RANK b) k -> Le (RANK u) k ->
    Comp a b -> finMemC a UCode -> Coherent u -> finMemC u b -> finMemC u (Sup a b)
  finMem-Sup-right-k k a b Bot ba bb bu comp aU cohu mem =
    finMemC-bot-from (Sup a b) (finMemUCode-Sup-k k a b ba bb comp aU (finMemC-bot-to b mem))
  finMem-Sup-right-k k Bot          UCode UCode ba bb bu comp aU cohu mem = mem
  finMem-Sup-right-k k UCode        UCode UCode ba bb bu comp aU cohu mem = mem
  finMem-Sup-right-k k (FunEl g)    UCode UCode ba bb bu comp aU cohu mem = aU
  finMem-Sup-right-k k (PiCode d kk) UCode UCode ba bb bu () aU cohu mem
  finMem-Sup-right-k k a Bot          UCode ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a (FunEl h)    UCode ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a (PiCode c h) UCode ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a UCode (PiCode b' h') ba bb bu comp aU cohu mem =
    finMem-Sup-right-PiCode-k k a UCode b' h' ba bb comp aU mem
  finMem-Sup-right-k k a Bot          (PiCode b' h') ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a (FunEl g)    (PiCode b' h') ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a (PiCode c h) (PiCode b' h') ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a (PiCode c h) (FunEl g) ba bb bu comp aU cohu mem =
    finMem-Sup-right-FunEl-k k a c h g ba bb bu comp aU cohu mem
  finMem-Sup-right-k k a Bot       (FunEl g) ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a UCode     (FunEl g) ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a (FunEl h) (FunEl g) ba bb bu comp aU cohu ()
  -- u = ZeroEl : forces b = NatCode, a in {Bot, NatCode}, Sup a NatCode = NatCode
  finMem-Sup-right-k k Bot           NatCode ZeroEl ba bb bu comp aU cohu mem = mem
  finMem-Sup-right-k k NatCode       NatCode ZeroEl ba bb bu comp aU cohu mem = mem
  finMem-Sup-right-k k UCode         NatCode ZeroEl ba bb bu () aU cohu mem
  finMem-Sup-right-k k (FunEl g)     NatCode ZeroEl ba bb bu () aU cohu mem
  finMem-Sup-right-k k (PiCode d kk) NatCode ZeroEl ba bb bu () aU cohu mem
  finMem-Sup-right-k k ZeroEl        NatCode ZeroEl ba bb bu () aU cohu mem
  finMem-Sup-right-k k (SucEl d)     NatCode ZeroEl ba bb bu () aU cohu mem
  finMem-Sup-right-k k a Bot          ZeroEl ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a UCode        ZeroEl ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a (FunEl h)    ZeroEl ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a (PiCode c h) ZeroEl ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a ZeroEl       ZeroEl ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a (SucEl c)    ZeroEl ba bb bu comp aU cohu ()
  -- u = NatCode (as element) : forces b = UCode, a in {Bot, UCode}, Sup a UCode = UCode
  finMem-Sup-right-k k Bot           UCode NatCode ba bb bu comp aU cohu mem = mem
  finMem-Sup-right-k k UCode         UCode NatCode ba bb bu comp aU cohu mem = mem
  finMem-Sup-right-k k (FunEl g)     UCode NatCode ba bb bu comp () cohu mem
  finMem-Sup-right-k k (PiCode d kk) UCode NatCode ba bb bu () aU cohu mem
  finMem-Sup-right-k k NatCode       UCode NatCode ba bb bu () aU cohu mem
  finMem-Sup-right-k k ZeroEl        UCode NatCode ba bb bu () aU cohu mem
  finMem-Sup-right-k k (SucEl d)     UCode NatCode ba bb bu () aU cohu mem
  finMem-Sup-right-k k a Bot          NatCode ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a (FunEl h)    NatCode ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a (PiCode c h) NatCode ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a NatCode      NatCode ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a ZeroEl       NatCode ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a (SucEl c)    NatCode ba bb bu comp aU cohu ()
  -- u = SucEl d : forces b = NatCode, a in {Bot, NatCode}, Sup a NatCode = NatCode
  finMem-Sup-right-k k Bot           NatCode (SucEl d) ba bb bu comp aU cohu mem = mem
  finMem-Sup-right-k k NatCode       NatCode (SucEl d) ba bb bu comp aU cohu mem = mem
  finMem-Sup-right-k k UCode         NatCode (SucEl d) ba bb bu () aU cohu mem
  finMem-Sup-right-k k (FunEl g)     NatCode (SucEl d) ba bb bu () aU cohu mem
  finMem-Sup-right-k k (PiCode c kk) NatCode (SucEl d) ba bb bu () aU cohu mem
  finMem-Sup-right-k k ZeroEl        NatCode (SucEl d) ba bb bu () aU cohu mem
  finMem-Sup-right-k k (SucEl e)     NatCode (SucEl d) ba bb bu () aU cohu mem
  finMem-Sup-right-k k a Bot          (SucEl d) ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a UCode        (SucEl d) ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a (FunEl h)    (SucEl d) ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a (PiCode c h) (SucEl d) ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a ZeroEl       (SucEl d) ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a (SucEl e)    (SucEl d) ba bb bu comp aU cohu ()

  finMem-Sup-right-PiCode-k : (k : Nat) (a b : FinEl) (b' : FinEl) (h' : FinFun) ->
    Le (RANK a) k -> Le (RANK b) k ->
    Comp a b -> finMemC a UCode ->
    finMemC (PiCode b' h') b -> finMemC (PiCode b' h') (Sup a b)
  finMem-Sup-right-PiCode-k k Bot   UCode b' h' ba bb comp aU mem = mem
  finMem-Sup-right-PiCode-k k UCode UCode b' h' ba bb comp aU mem = mem
  finMem-Sup-right-PiCode-k k (FunEl g) UCode b' h' ba bb comp () mem
  finMem-Sup-right-PiCode-k k (PiCode d kk) UCode b' h' ba bb () aU mem

  finMem-Sup-right-FunEl-k : (k : Nat) (a : FinEl) (c : FinEl) (h : FinFun) (g : FinFun) ->
    Le (RANK a) k -> Le (RANK (PiCode c h)) k -> Le (RANK (FunEl g)) k ->
    Comp a (PiCode c h) -> finMemC a UCode -> Coherent (FunEl g) ->
    finMemC (FunEl g) (PiCode c h) -> finMemC (FunEl g) (Sup a (PiCode c h))
  finMem-Sup-right-FunEl-k k Bot c h g ba bb bu comp aU cohg mem = mem
  finMem-Sup-right-FunEl-k k UCode c h g ba bb bu () aU cohg mem
  finMem-Sup-right-FunEl-k k (FunEl j) c h g ba bb bu comp () cohg mem
  finMem-Sup-right-FunEl-k zero    (PiCode d kk) c h g () bb bu comp aU cohg mem
  finMem-Sup-right-FunEl-k (suc k) (PiCode d kk) c h g ba bb bu comp aU cohg mem =
    let bdd = max-Le-l (RANK d) (RANKFun kk) k ba ; bkk = max-Le-r (RANK d) (RANKFun kk) k ba
        bc  = max-Le-l (RANK c) (RANKFun h) k bb  ; bh  = max-Le-r (RANK c) (RANKFun h) k bb
        piU = finMemC-funel-wf g c h mem
        dU = finMemC-piU-dom d kk aU ; allUk = finMemC-piU-allU d kk aU ; cohk = finMemC-piU-cft d kk aU
        cU = finMemC-piU-dom c h piU ; allUh = finMemC-piU-allU c h piU ; cohh = finMemC-piU-cft c h piU
        cohd = coh-from-aU d dU ; cohc = coh-from-aU c cU
        supU = finMemUCode-Sup-k k d c bdd bc (fst comp) dU cU
        allUkh = FinMemAllU-append-Sup-k k d c kk h bdd bc bkk bh (fst comp) cohd cohc dU cU cohk cohh allUk allUh
        cohkh = CoherentFunTail-append kk h cohk cohh (snd comp)
    in finMemC-funel-mk g (Sup d c) (append kk h)
         (finMemFun-Sup-right-k k d c kk h g bdd bc bkk bh bu (fst comp) (snd comp) dU allUk cohk (cft-from-cf g cohg) (finMemC-funel-fun g c h mem))
         (finMemC-funel-coh g c h mem)
         (finMemC-piU-mk (Sup d c) (append kk h) supU allUkh cohkh)

  finMemFun-Sup-right-k : (k : Nat) (d c : FinEl) (kk h : FinFun) (g : FinFun) ->
    Le (RANK d) k -> Le (RANK c) k -> Le (RANKFun kk) k -> Le (RANKFun h) k -> Le (RANKFun g) k ->
    Comp d c -> CompFun kk h -> finMemC d UCode -> finMemAllUC kk d -> CoherentFunTail kk ->
    CoherentFunTail g -> finMemFunC g c h -> finMemFunC g (Sup d c) (append kk h)
  finMemFun-Sup-right-k k d c kk h nil bd bc bkk bh bg cd ckh dU allUk cohk cohg mem = tt
  finMemFun-Sup-right-k k d c kk h (cons p ps) bd bc bkk bh bg cd ckh dU allUk cohk cohg mem =
    finMemFunC-mk p ps (Sup d c) (append kk h)
      (finMem-Sup-right-k k d c (fst p) bd bc (rk-key p ps k bg) cd dU (CFTcons.key-coh cohg) (finMemFunC-hd-key p ps c h mem))
      (finMem-EvalFun-append-k k d kk h (fst p) (snd p) bkk bh (rk-val p ps k bg) ckh cohk (CFTcons.key-coh cohg) (CFTcons.val-coh cohg) allUk (finMemFunC-hd-val p ps c h mem))
      (finMemFun-Sup-right-k k d c kk h ps bd bc bkk bh (rk-tail p ps k bg) cd ckh dU allUk cohk (CFTcons.tail-coh cohg) (finMemFunC-tl p ps c h mem))

  finMem-EvalFun-append-k : (k : Nat) (d : FinEl) (kk h : FinFun) (xi yi : FinEl) ->
    Le (RANKFun kk) k -> Le (RANKFun h) k -> Le (RANK yi) k ->
    CompFun kk h -> CoherentFunTail kk -> Coherent xi -> Coherent yi ->
    finMemAllUC kk d ->
    finMemC yi (EvalFun h xi) -> finMemC yi (EvalFun (append kk h) xi)
  finMem-EvalFun-append-k k d nil h xi yi bkk bh byi ckh cohk cxi cohyi allU mem = mem
  finMem-EvalFun-append-k k d (cons q qs) h xi yi bkk bh byi ckh cohk cxi cohyi allU mem =
    let ih = finMem-EvalFun-append-k k d qs h xi yi (rk-tail q qs k bkk) bh byi (snd ckh) (CFTcons.tail-coh cohk) cxi cohyi (finMemAllUC-tl q qs d allU) mem
        csf = compStepFun-append q qs h (coherentWith-to-compStepFun q qs (CFTcons.compat cohk)) (fst ckh)
        cw  = coherentWith-append q qs h (CFTcons.compat cohk) (compStepFun-to-coherentWith q h (fst ckh))
        vU  = finMemAllUC-hd-val q qs d allU
    in finMem-EvalFun-prepend-k k (leFinEl (fst q) xi) q (append qs h) xi yi
         (rk-val q qs k bkk) (app-bnd k qs h (rk-tail q qs k bkk) bh) byi
         refl cxi (CFTcons.val-coh cohk) vU cw csf cohyi ih

  finMem-EvalFun-prepend-k : (k : Nat) (n : Nat) (q : Pair FinEl FinEl) (rest : FinFun)
    (xi yi : FinEl) -> Le (RANK (snd q)) k -> Le (RANKFun rest) k -> Le (RANK yi) k ->
    Eq n (leFinEl (fst q) xi) ->
    Coherent xi -> Coherent (snd q) -> finMemC (snd q) UCode ->
    CoherentWith q rest -> CompStepFun q rest ->
    Coherent yi ->
    finMemC yi (EvalFun rest xi) ->
    finMemC yi (EvalFun-step n (snd q) rest xi)
  finMem-EvalFun-prepend-k k zero    q rest xi yi bvq brest byi eq cxi cohv vU cw csf cohyi ih = ih
  finMem-EvalFun-prepend-k k (suc _) q rest xi yi bvq brest byi eq cxi cohv vU cw csf cohyi ih =
    finMem-Sup-right-k k (snd q) (EvalFun rest xi) yi
      bvq (ev-bnd k rest xi brest) byi
      (Comp-value-EvalFun q rest xi
        (leFinEl-sound (fst q) xi (Eq-transport isPos eq tt))
        cxi cohv cw csf)
      vU cohyi ih

  finMem-Sup-left-k : (k : Nat) (a b u : FinEl) -> Le (RANK a) k -> Le (RANK b) k -> Le (RANK u) k ->
    Comp a b -> Coherent a -> Coherent b ->
    finMemC b UCode -> Coherent u -> finMemC u a -> finMemC u (Sup a b)
  finMem-Sup-left-k k a b Bot ba bb bu comp coha cohb bU cohu mem =
    finMemC-bot-from (Sup a b) (finMemUCode-Sup-k k a b ba bb comp (finMemC-bot-to a mem) bU)
  finMem-Sup-left-k k Bot          b UCode ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k UCode        Bot          UCode ba bb bu comp coha cohb bU cohu mem = mem
  finMem-Sup-left-k k UCode        UCode        UCode ba bb bu comp coha cohb bU cohu mem = mem
  finMem-Sup-left-k k UCode        (FunEl h)    UCode ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k UCode        (PiCode c h) UCode ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k (FunEl g)    b UCode ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k (PiCode a f) b UCode ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k Bot          b (PiCode b' h') ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k UCode        Bot          (PiCode b' h') ba bb bu comp coha cohb bU cohu mem = mem
  finMem-Sup-left-k k UCode        UCode        (PiCode b' h') ba bb bu comp coha cohb bU cohu mem = mem
  finMem-Sup-left-k k UCode        (FunEl h)    (PiCode b' h') ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k UCode        (PiCode c h) (PiCode b' h') ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k (FunEl g)    b (PiCode b' h') ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k (PiCode a f) b (PiCode b' h') ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k Bot          b (FunEl g) ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k UCode        b (FunEl g) ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k (FunEl j)    b (FunEl g) ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k (PiCode d kk) Bot          (FunEl g) ba bb bu comp coha cohb bU cohu mem = mem
  finMem-Sup-left-k k (PiCode d kk) UCode        (FunEl g) ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k (PiCode d kk) (FunEl h)    (FunEl g) ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k zero    (PiCode d kk) (PiCode c h) (FunEl g) () bb bu comp coha cohb bU cohu mem
  finMem-Sup-left-k (suc k) (PiCode d kk) (PiCode c h) (FunEl g) ba bb bu comp coha cohb bU cohu mem =
    let bdd = max-Le-l (RANK d) (RANKFun kk) k ba ; bkk = max-Le-r (RANK d) (RANKFun kk) k ba
        bc  = max-Le-l (RANK c) (RANKFun h) k bb  ; bh  = max-Le-r (RANK c) (RANKFun h) k bb
        cohd = fst coha ; cohc = fst cohb
        piU = finMemC-funel-wf g d kk mem
        dU = finMemC-piU-dom d kk piU ; allUk = finMemC-piU-allU d kk piU
        cU = finMemC-piU-dom c h bU ; allUh = finMemC-piU-allU c h bU
        cohk = snd coha ; cohh = snd cohb
        cohg = cft-from-cf g (finMemC-funel-coh g d kk mem)
        supU = finMemUCode-Sup-k k d c bdd bc (fst comp) dU cU
        allUkh = FinMemAllU-append-Sup-k k d c kk h bdd bc bkk bh (fst comp) cohd cohc dU cU cohk cohh allUk allUh
        cohkh = CoherentFunTail-append kk h cohk cohh (snd comp)
    in finMemC-funel-mk g (Sup d c) (append kk h)
         (finMemFun-Sup-left-k k d c kk h g bdd bc bkk bh bu (fst comp) (snd comp) cohd cohc cU allUh cohk cohh cohg (finMemC-funel-fun g d kk mem))
         (finMemC-funel-coh g d kk mem)
         (finMemC-piU-mk (Sup d c) (append kk h) supU allUkh cohkh)
  -- u = ZeroEl : forces a = NatCode, b in {Bot, NatCode}, Sup NatCode b = NatCode
  finMem-Sup-left-k k NatCode Bot       ZeroEl ba bb bu comp coha cohb bU cohu mem = mem
  finMem-Sup-left-k k NatCode NatCode   ZeroEl ba bb bu comp coha cohb bU cohu mem = mem
  finMem-Sup-left-k k NatCode UCode     ZeroEl ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k NatCode (FunEl h) ZeroEl ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k NatCode (PiCode c h) ZeroEl ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k NatCode ZeroEl    ZeroEl ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k NatCode (SucEl c) ZeroEl ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k Bot          b ZeroEl ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k UCode        b ZeroEl ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k (FunEl g)    b ZeroEl ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k (PiCode c h) b ZeroEl ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k ZeroEl       b ZeroEl ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k (SucEl c)    b ZeroEl ba bb bu comp coha cohb bU cohu ()
  -- u = NatCode (as element) : forces a = UCode, b in {Bot, UCode}, Sup UCode b = UCode
  finMem-Sup-left-k k UCode Bot     NatCode ba bb bu comp coha cohb bU cohu mem = mem
  finMem-Sup-left-k k UCode UCode   NatCode ba bb bu comp coha cohb bU cohu mem = mem
  finMem-Sup-left-k k UCode (FunEl h) NatCode ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k UCode (PiCode c h) NatCode ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k UCode NatCode NatCode ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k UCode ZeroEl  NatCode ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k UCode (SucEl c) NatCode ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k Bot          b NatCode ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k (FunEl g)    b NatCode ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k (PiCode c h) b NatCode ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k NatCode      b NatCode ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k ZeroEl       b NatCode ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k (SucEl c)    b NatCode ba bb bu comp coha cohb bU cohu ()
  -- u = SucEl d : forces a = NatCode, b in {Bot, NatCode}, Sup NatCode b = NatCode
  finMem-Sup-left-k k NatCode Bot       (SucEl d) ba bb bu comp coha cohb bU cohu mem = mem
  finMem-Sup-left-k k NatCode NatCode   (SucEl d) ba bb bu comp coha cohb bU cohu mem = mem
  finMem-Sup-left-k k NatCode UCode     (SucEl d) ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k NatCode (FunEl h) (SucEl d) ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k NatCode (PiCode c h) (SucEl d) ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k NatCode ZeroEl    (SucEl d) ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k NatCode (SucEl c) (SucEl d) ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k Bot          b (SucEl d) ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k UCode        b (SucEl d) ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k (FunEl g)    b (SucEl d) ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k (PiCode c h) b (SucEl d) ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k ZeroEl       b (SucEl d) ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k (SucEl c)    b (SucEl d) ba bb bu comp coha cohb bU cohu ()

  finMemFun-Sup-left-k : (k : Nat) (d c : FinEl) (kk h : FinFun) (g : FinFun) ->
    Le (RANK d) k -> Le (RANK c) k -> Le (RANKFun kk) k -> Le (RANKFun h) k -> Le (RANKFun g) k ->
    Comp d c -> CompFun kk h ->
    Coherent d -> Coherent c -> finMemC c UCode -> finMemAllUC h c ->
    CoherentFunTail kk -> CoherentFunTail h ->
    CoherentFunTail g ->
    finMemFunC g d kk -> finMemFunC g (Sup d c) (append kk h)
  finMemFun-Sup-left-k k d c kk h nil bd bc bkk bh bg cd ckh cohd cohc cU allUh cohk cohh cohg mem = tt
  finMemFun-Sup-left-k k d c kk h (cons p ps) bd bc bkk bh bg cd ckh cohd cohc cU allUh cohk cohh cohg mem =
    let key-mem = finMem-Sup-left-k k d c (fst p) bd bc (rk-key p ps k bg) cd cohd cohc cU (CFTcons.key-coh cohg) (finMemFunC-hd-key p ps d kk mem)
        eval-eq = EvalFun-append-eq kk h (fst p) ckh cohk (CFTcons.key-coh cohg)
        comp-eval = comp-EvalFun kk h (fst p) ckh cohk (CFTcons.key-coh cohg)
        coh-eval-k = Coherent-EvalFun kk (fst p) cohk (CFTcons.key-coh cohg)
        coh-eval-h = Coherent-EvalFun h (fst p) cohh (CFTcons.key-coh cohg)
        evalh-U = EvalFun-in-UCode-k k h (fst p) c bh cohh (CFTcons.key-coh cohg) allUh
        val-left = finMem-Sup-left-k k (EvalFun kk (fst p)) (EvalFun h (fst p)) (snd p)
                     (ev-bnd k kk (fst p) bkk) (ev-bnd k h (fst p) bh) (rk-val p ps k bg)
                     comp-eval coh-eval-k coh-eval-h evalh-U
                     (CFTcons.val-coh cohg) (finMemFunC-hd-val p ps d kk mem)
        val-mem = Eq-transport (\ x -> finMemC (snd p) x) (Eq-sym eval-eq) val-left
        tail-mem = finMemFun-Sup-left-k k d c kk h ps bd bc bkk bh (rk-tail p ps k bg) cd ckh cohd cohc cU allUh cohk cohh (CFTcons.tail-coh cohg) (finMemFunC-tl p ps d kk mem)
    in finMemFunC-mk p ps (Sup d c) (append kk h) key-mem val-mem tail-mem

------------------------------------------------------------------------
-- Public, fuel-free properties (collapse the cycle at fuel = max RANK).
------------------------------------------------------------------------

finMemUCode-Sup : (a c : FinEl) -> Comp a c -> finMemC a UCode -> finMemC c UCode -> finMemC (Sup a c) UCode
finMemUCode-Sup a c = finMemUCode-Sup-k (max (RANK a) (RANK c)) a c (Le-max-l (RANK a) (RANK c)) (Le-max-r (RANK a) (RANK c))

FinMemAllU-append-Sup : (d c : FinEl) (f h : FinFun) ->
  Comp d c -> Coherent d -> Coherent c -> finMemC d UCode -> finMemC c UCode ->
  CoherentFunTail f -> CoherentFunTail h -> finMemAllUC f d -> finMemAllUC h c ->
  finMemAllUC (append f h) (Sup d c)
FinMemAllU-append-Sup d c f h =
  let k = max (max (RANK d) (RANK c)) (max (RANKFun f) (RANKFun h))
  in FinMemAllU-append-Sup-k k d c f h
       (Le-trans (RANK d) (max (RANK d) (RANK c)) k (Le-max-l (RANK d) (RANK c)) (Le-max-l (max (RANK d) (RANK c)) (max (RANKFun f) (RANKFun h))))
       (Le-trans (RANK c) (max (RANK d) (RANK c)) k (Le-max-r (RANK d) (RANK c)) (Le-max-l (max (RANK d) (RANK c)) (max (RANKFun f) (RANKFun h))))
       (Le-trans (RANKFun f) (max (RANKFun f) (RANKFun h)) k (Le-max-l (RANKFun f) (RANKFun h)) (Le-max-r (max (RANK d) (RANK c)) (max (RANKFun f) (RANKFun h))))
       (Le-trans (RANKFun h) (max (RANKFun f) (RANKFun h)) k (Le-max-r (RANKFun f) (RANKFun h)) (Le-max-r (max (RANK d) (RANK c)) (max (RANKFun f) (RANKFun h))))

EvalFun-in-UCode : (f : FinFun) (x d : FinEl) ->
  CoherentFunTail f -> Coherent x -> finMemAllUC f d -> finMemC (EvalFun f x) UCode
EvalFun-in-UCode f x d = EvalFun-in-UCode-k (RANKFun f) f x d (Le-refl (RANKFun f))

finMem-Sup-right : (a b u : FinEl) -> Comp a b -> finMemC a UCode -> Coherent u ->
  finMemC u b -> finMemC u (Sup a b)
finMem-Sup-right a b u =
  finMem-Sup-right-k (max (RANK a) (max (RANK b) (RANK u))) a b u
    (b3-x (RANK a) (RANK b) (RANK u)) (b3-y (RANK a) (RANK b) (RANK u)) (b3-z (RANK a) (RANK b) (RANK u))

finMem-Sup-left : (a b u : FinEl) -> Comp a b -> Coherent a -> Coherent b ->
  finMemC b UCode -> Coherent u -> finMemC u a -> finMemC u (Sup a b)
finMem-Sup-left a b u =
  finMem-Sup-left-k (max (RANK a) (max (RANK b) (RANK u))) a b u
    (b3-x (RANK a) (RANK b) (RANK u)) (b3-y (RANK a) (RANK b) (RANK u)) (b3-z (RANK a) (RANK b) (RANK u))

------------------------------------------------------------------------
-- Monotonicity:  u : a  and  a <= b  and  b : U  ->  u : b.
------------------------------------------------------------------------

mutual
  finMem-upward : (v a b : FinEl) -> LeCode a b -> Coherent a -> Coherent b ->
    finMemC v a -> finMemC b UCode -> finMemC v b
  finMem-upward Bot          a            b            le ca cb mem bU = finMemC-bot-from b bU
  finMem-upward UCode        UCode        UCode        le ca cb mem bU = mem
  finMem-upward UCode        UCode        Bot          ()
  finMem-upward UCode        UCode        (FunEl h)    ()
  finMem-upward UCode        UCode        (PiCode c h) ()
  finMem-upward UCode        Bot          b            le ca cb ()
  finMem-upward UCode        (FunEl g)    b            le ca cb ()
  finMem-upward UCode        (PiCode c h) b            le ca cb ()
  finMem-upward (FunEl g)    (PiCode a f) (PiCode b h) le ca cb mem bU =
    finMemC-funel-mk g b h
      (finMemFun-upward g a b f h (fst le) (fst ca) (coh-from-aU b (finMemC-piU-dom b h bU))
        (snd ca) (finMemC-piU-cft b h bU) (snd le) (finMemC-funel-fun g a f mem)
        (finMemC-piU-dom b h bU) (finMemC-piU-allU b h bU))
      (finMemC-funel-coh g a f mem)
      bU
  finMem-upward (FunEl g)    (PiCode a f) Bot          ()
  finMem-upward (FunEl g)    (PiCode a f) UCode        ()
  finMem-upward (FunEl g)    (PiCode a f) (FunEl h)    ()
  finMem-upward (FunEl g)    Bot          b            le ca cb ()
  finMem-upward (FunEl g)    UCode        b            le ca cb ()
  finMem-upward (FunEl g)    (FunEl h)    b            le ca cb ()
  finMem-upward (PiCode a f) UCode        UCode        le ca cb mem bU = mem
  finMem-upward (PiCode a f) UCode        Bot          ()
  finMem-upward (PiCode a f) UCode        (FunEl h)    ()
  finMem-upward (PiCode a f) UCode        (PiCode c h) ()
  finMem-upward (PiCode a f) Bot          b            le ca cb ()
  finMem-upward (PiCode a f) (FunEl g)    b            le ca cb ()
  finMem-upward (PiCode a f) (PiCode c h) b            le ca cb ()
  -- v = ZeroEl : a = NatCode, b = NatCode (LeCode NatCode b forces b = NatCode)
  finMem-upward ZeroEl Bot          b le ca cb ()
  finMem-upward ZeroEl UCode        b le ca cb ()
  finMem-upward ZeroEl (FunEl g)    b le ca cb ()
  finMem-upward ZeroEl (PiCode c h) b le ca cb ()
  finMem-upward ZeroEl NatCode      Bot          ()
  finMem-upward ZeroEl NatCode      UCode        ()
  finMem-upward ZeroEl NatCode      (FunEl h)    ()
  finMem-upward ZeroEl NatCode      (PiCode c h) ()
  finMem-upward ZeroEl NatCode      NatCode      le ca cb mem bU = mem
  finMem-upward ZeroEl NatCode      ZeroEl       ()
  finMem-upward ZeroEl NatCode      (SucEl h)    ()
  finMem-upward ZeroEl ZeroEl       b le ca cb ()
  finMem-upward ZeroEl (SucEl d)    b le ca cb ()
  -- v = NatCode (as element) : a = UCode, b = UCode
  finMem-upward NatCode Bot          b le ca cb ()
  finMem-upward NatCode (FunEl g)    b le ca cb ()
  finMem-upward NatCode (PiCode c h) b le ca cb ()
  finMem-upward NatCode NatCode      b le ca cb ()
  finMem-upward NatCode ZeroEl       b le ca cb ()
  finMem-upward NatCode (SucEl d)    b le ca cb ()
  finMem-upward NatCode UCode        UCode        le ca cb mem bU = mem
  finMem-upward NatCode UCode        Bot          ()
  finMem-upward NatCode UCode        (FunEl h)    ()
  finMem-upward NatCode UCode        (PiCode c h) ()
  finMem-upward NatCode UCode        NatCode      ()
  finMem-upward NatCode UCode        ZeroEl       ()
  finMem-upward NatCode UCode        (SucEl h)    ()
  -- v = SucEl d : a = NatCode, b = NatCode
  finMem-upward (SucEl d) Bot          b le ca cb ()
  finMem-upward (SucEl d) UCode        b le ca cb ()
  finMem-upward (SucEl d) (FunEl g)    b le ca cb ()
  finMem-upward (SucEl d) (PiCode c h) b le ca cb ()
  finMem-upward (SucEl d) NatCode      Bot          ()
  finMem-upward (SucEl d) NatCode      UCode        ()
  finMem-upward (SucEl d) NatCode      (FunEl h)    ()
  finMem-upward (SucEl d) NatCode      (PiCode c h) ()
  finMem-upward (SucEl d) NatCode      NatCode      le ca cb mem bU = mem
  finMem-upward (SucEl d) NatCode      ZeroEl       ()
  finMem-upward (SucEl d) NatCode      (SucEl h)    ()
  finMem-upward (SucEl d) ZeroEl       b le ca cb ()
  finMem-upward (SucEl d) (SucEl e)    b le ca cb ()

  finMemFun-upward : (g : FinFun) (a b : FinEl) (f h : FinFun) ->
    LeCode a b -> Coherent a -> Coherent b ->
    CoherentFunTail f -> CoherentFunTail h -> LeFunCode f h ->
    finMemFunC g a f -> finMemC b UCode -> finMemAllUC h b -> finMemFunC g b h
  finMemFun-upward nil         a b f h le-a ca cb cf ch lfh mem bU allUh = tt
  finMemFun-upward (cons p ps) a b f h le-a ca cb cf ch lfh mem bU allUh =
    let kmem = finMemFunC-hd-key p ps a f mem
        vmem = finMemFunC-hd-val p ps a f mem
        cp   = FinMem-coh-u (fst p) a kmem
        le-fh = EvalFun-mon f h (fst p) cf ch cp lfh
        c-ef  = Coherent-EvalFun f (fst p) cf cp
        c-eh  = Coherent-EvalFun h (fst p) ch cp
        efhU  = EvalFun-in-UCode h (fst p) b ch cp allUh
    in finMemFunC-mk p ps b h
         (finMem-upward (fst p) a b le-a ca cb kmem bU)
         (finMem-upward (snd p) (EvalFun f (fst p)) (EvalFun h (fst p)) le-fh c-ef c-eh vmem efhU)
         (finMemFun-upward ps a b f h le-a ca cb cf ch lfh (finMemFunC-tl p ps a f mem) bU allUh)

------------------------------------------------------------------------
-- FinMemFun-append, FinMem-Sup-element, finMem-Sup-both.
------------------------------------------------------------------------

FinMemFun-append : (g h : FinFun) (b : FinEl) (f : FinFun) ->
  finMemFunC g b f -> finMemFunC h b f -> finMemFunC (append g h) b f
FinMemFun-append nil         h b f mg mh = mh
FinMemFun-append (cons p ps) h b f mg mh =
  finMemFunC-mk p (append ps h) b f
    (finMemFunC-hd-key p ps b f mg) (finMemFunC-hd-val p ps b f mg)
    (FinMemFun-append ps h b f (finMemFunC-tl p ps b f mg) mh)

-- finMemC (SucEl x) NatCode reduces definitionally to MB.finMem (suc (RANK x)) x NatCode;
-- bridge it to/from the canonical-level finMemC x NatCode.
sucNat-to : (x : FinEl) -> finMemC (SucEl x) NatCode -> finMemC x NatCode
sucNat-to x m =
  finMemC-from (suc (RANK x)) x NatCode (Le-suc (RANK x) (RANK x) (Le-refl (RANK x))) tt m

sucNat-from : (x : FinEl) -> finMemC x NatCode -> finMemC (SucEl x) NatCode
sucNat-from x m =
  finMemC-to (suc (RANK x)) x NatCode (Le-suc (RANK x) (RANK x) (Le-refl (RANK x))) tt m

FinMem-Sup-element : (u v a : FinEl) -> Comp u v -> Coherent a ->
  finMemC u a -> finMemC v a -> finMemC (Sup u v) a
FinMem-Sup-element Bot          v a comp ca mu mv = mv
FinMem-Sup-element UCode        Bot a comp ca mu mv = mu
FinMem-Sup-element (FunEl g)    Bot a comp ca mu mv = mu
FinMem-Sup-element (PiCode a1 f1) Bot a comp ca mu mv = mu
FinMem-Sup-element UCode        UCode UCode comp ca mu mv = mu
FinMem-Sup-element UCode        UCode Bot comp ca () mv
FinMem-Sup-element UCode        UCode (FunEl h) comp ca () mv
FinMem-Sup-element UCode        UCode (PiCode b f) comp ca () mv
FinMem-Sup-element UCode        (FunEl h) a () ca mu mv
FinMem-Sup-element UCode        (PiCode b f) a () ca mu mv
FinMem-Sup-element (FunEl g)    UCode a () ca mu mv
FinMem-Sup-element (FunEl g)    (PiCode b f) a () ca mu mv
FinMem-Sup-element (FunEl g)    (FunEl h) Bot comp ca () mv
FinMem-Sup-element (FunEl g)    (FunEl h) UCode comp ca () mv
FinMem-Sup-element (FunEl g)    (FunEl h) (FunEl k) comp ca () mv
FinMem-Sup-element (FunEl g)    (FunEl h) (PiCode b f) comp ca mu mv =
  finMemC-funel-mk (append g h) b f
    (FinMemFun-append g h b f (finMemC-funel-fun g b f mu) (finMemC-funel-fun h b f mv))
    (CoherentFun-append g h (finMemC-funel-coh g b f mu) (finMemC-funel-coh h b f mv) comp)
    (finMemC-funel-wf g b f mu)
FinMem-Sup-element (PiCode a1 f1) UCode a () ca mu mv
FinMem-Sup-element (PiCode a1 f1) (FunEl h) a () ca mu mv
FinMem-Sup-element (PiCode a1 f1) (PiCode a2 f2) Bot comp ca () mv
FinMem-Sup-element (PiCode a1 f1) (PiCode a2 f2) UCode comp ca mu mv =
  finMemUCode-Sup (PiCode a1 f1) (PiCode a2 f2) comp mu mv
FinMem-Sup-element (PiCode a1 f1) (PiCode a2 f2) (FunEl h) comp ca () mv
FinMem-Sup-element (PiCode a1 f1) (PiCode a2 f2) (PiCode b f) comp ca () mv
-- u = ZeroEl : a = NatCode, v in {Bot, ZeroEl}, Sup ZeroEl v = ZeroEl
FinMem-Sup-element ZeroEl Bot          NatCode comp ca mu mv = mu
FinMem-Sup-element ZeroEl ZeroEl       NatCode comp ca mu mv = mu
FinMem-Sup-element ZeroEl UCode        NatCode () ca mu mv
FinMem-Sup-element ZeroEl (FunEl h)    NatCode () ca mu mv
FinMem-Sup-element ZeroEl (PiCode b f) NatCode () ca mu mv
FinMem-Sup-element ZeroEl NatCode      NatCode () ca mu mv
FinMem-Sup-element ZeroEl (SucEl d)    NatCode () ca mu mv
FinMem-Sup-element ZeroEl v Bot          comp ca () mv
FinMem-Sup-element ZeroEl v UCode        comp ca () mv
FinMem-Sup-element ZeroEl v (FunEl h)    comp ca () mv
FinMem-Sup-element ZeroEl v (PiCode b f) comp ca () mv
FinMem-Sup-element ZeroEl v ZeroEl       comp ca () mv
FinMem-Sup-element ZeroEl v (SucEl d)    comp ca () mv
-- u = NatCode (as element) : a = UCode, v in {Bot, NatCode}, Sup NatCode v = NatCode
FinMem-Sup-element NatCode Bot          UCode comp ca mu mv = mu
FinMem-Sup-element NatCode NatCode      UCode comp ca mu mv = mu
FinMem-Sup-element NatCode UCode        UCode () ca mu mv
FinMem-Sup-element NatCode (FunEl h)    UCode () ca mu mv
FinMem-Sup-element NatCode (PiCode b f) UCode () ca mu mv
FinMem-Sup-element NatCode ZeroEl       UCode () ca mu mv
FinMem-Sup-element NatCode (SucEl d)    UCode () ca mu mv
FinMem-Sup-element NatCode v Bot          comp ca () mv
FinMem-Sup-element NatCode v (FunEl h)    comp ca () mv
FinMem-Sup-element NatCode v (PiCode b f) comp ca () mv
FinMem-Sup-element NatCode v NatCode      comp ca () mv
FinMem-Sup-element NatCode v ZeroEl       comp ca () mv
FinMem-Sup-element NatCode v (SucEl d)    comp ca () mv
-- u = SucEl d : a = NatCode, v in {Bot, SucEl e}; Sup (SucEl d)(SucEl e) = SucEl (Sup d e)
FinMem-Sup-element (SucEl d) Bot          NatCode comp ca mu mv = mu
FinMem-Sup-element (SucEl d) UCode        NatCode () ca mu mv
FinMem-Sup-element (SucEl d) (FunEl h)    NatCode () ca mu mv
FinMem-Sup-element (SucEl d) (PiCode b f) NatCode () ca mu mv
FinMem-Sup-element (SucEl d) NatCode      NatCode () ca mu mv
FinMem-Sup-element (SucEl d) ZeroEl       NatCode () ca mu mv
FinMem-Sup-element (SucEl d) (SucEl e)    NatCode comp ca mu mv =
  sucNat-from (Sup d e) (FinMem-Sup-element d e NatCode comp tt (sucNat-to d mu) (sucNat-to e mv))
FinMem-Sup-element (SucEl d) v Bot          comp ca () mv
FinMem-Sup-element (SucEl d) v UCode        comp ca () mv
FinMem-Sup-element (SucEl d) v (FunEl h)    comp ca () mv
FinMem-Sup-element (SucEl d) v (PiCode b f) comp ca () mv
FinMem-Sup-element (SucEl d) v ZeroEl       comp ca () mv
FinMem-Sup-element (SucEl d) v (SucEl e)    comp ca () mv

finMem-Sup-both : (a1 a2 u1 u2 : FinEl) ->
  finMemC a1 u1 -> finMemC a2 u2 -> Comp u1 u2 -> Comp a1 a2 ->
  finMemC (Sup a1 a2) (Sup u1 u2)
finMem-Sup-both a1 a2 u1 u2 m1 m2 comp-u comp-a =
  let u1U = FinMem-a-in-U a1 u1 m1
      u2U = FinMem-a-in-U a2 u2 m2
      cu1 = coh-from-aU u1 u1U
      cu2 = coh-from-aU u2 u2U
      ca1 = FinMem-coh-u a1 u1 m1
      ca2 = FinMem-coh-u a2 u2 m2
      c-sup = Coherent-Sup u1 u2 comp-u cu1 cu2
      m1' = finMem-Sup-left u1 u2 a1 comp-u cu1 cu2 u2U ca1 m1
      m2' = finMem-Sup-right u1 u2 a2 comp-u u1U ca2 m2
  in FinMem-Sup-element a1 a2 (Sup u1 u2) comp-a c-sup m1' m2'
