{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- FinMemStageProps.agda  (MIN/ — Pi + U fragment)
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

module ID.Domain.MemProps where

open import ID.Domain.Basic
  using ( Top ; tt ; Empty
        ; Nat ; zero ; suc ; max ; isPos
        ; Le ; Le-refl ; Le-suc ; Le-trans ; Le-max-l ; Le-max-r
        ; Pair ; mkSigma ; fst ; snd
        ; Eq ; refl ; Eq-sym ; Eq-transport
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; IdCode ; RefEl ; FinFun ; nil ; cons )
open import ID.Domain.Order
  using ( RANK ; RANKFun ; Sup ; append ; EvalFun ; EvalFun-step
        ; Comp ; CompFun ; CompStepFun ; CoherentWith ; LeCode ; LeFunCode
        ; Coherent ; CoherentFun ; CoherentFunTail ; CFTcons ; cft-from-cf
        ; leFinEl ; leFinEl-sound
        ; Comp-value-EvalFun ; Coherent-EvalFun ; comp-EvalFun ; EvalFun-append-eq
        ; EvalFun-mon ; Coherent-Sup ; CoherentFun-append
        ; CoherentFunTail-append ; coherentWith-to-compStepFun
        ; compStepFun-to-coherentWith ; compStepFun-append ; coherentWith-append
        ; Le-max-lub ; RANK-Sup ; RANK-append ; RANK-ev ; ev-bridge
        ; LeCode-Sup-left ; LeCode-Sup-right ; LeCode-Sup-lub
        ; LeCode-trans ; LeCode-refl ; Comp-sym )
open import ID.Domain.MemStage
open import ID.Domain.MemUnfold

private
  max-Le-l : (a b c : Nat) -> Le (max a b) c -> Le a c
  max-Le-l a b c h = Le-trans a (max a b) c (Le-max-l a b) h

  max-Le-r : (a b c : Nat) -> Le (max a b) c -> Le b c
  max-Le-r a b c h = Le-trans b (max a b) c (Le-max-r a b) h

  bRefW : (w : FinEl) -> Le (RANK w) (RANK (RefEl w))
  bRefW w = Le-suc (RANK w) (RANK w) (Le-refl (RANK w))

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
-- FinMemFun-append (fuel-free, structural on g): needed by the
-- element-level Sup inside the mutual, so it is defined up here.
------------------------------------------------------------------------

FinMemFun-append : (g h : FinFun) (b : FinEl) (f : FinFun) ->
  finMemFunC g b f -> finMemFunC h b f -> finMemFunC (append g h) b f
FinMemFun-append nil         h b f mg mh = mh
FinMemFun-append (cons p ps) h b f mg mh =
  finMemFunC-mk p (append ps h) b f
    (finMemFunC-hd-key p ps b f mg) (finMemFunC-hd-val p ps b f mg)
    (FinMemFun-append ps h b f (finMemFunC-tl p ps b f mg) mh)

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
  -- Id fragment.  RefEl is never a type-code (finMemC (RefEl _) UCode = Empty).
  finMemUCode-Sup-k k (RefEl w)    c ba bc comp () cU
  finMemUCode-Sup-k k UCode        (IdCode _ _ _) ba bc () aU cU
  finMemUCode-Sup-k k UCode        (RefEl _)      ba bc () aU cU
  finMemUCode-Sup-k k (PiCode a f) (IdCode _ _ _) ba bc () aU cU
  finMemUCode-Sup-k k (PiCode a f) (RefEl _)      ba bc () aU cU
  finMemUCode-Sup-k zero    (IdCode t u v) c            () bc comp aU cU
  finMemUCode-Sup-k (suc k) (IdCode t u v) Bot          ba bc comp aU cU = aU
  finMemUCode-Sup-k (suc k) (IdCode t u v) UCode        ba bc () aU cU
  finMemUCode-Sup-k (suc k) (IdCode t u v) (FunEl h)    ba bc () aU cU
  finMemUCode-Sup-k (suc k) (IdCode t u v) (PiCode b g) ba bc () aU cU
  finMemUCode-Sup-k (suc k) (IdCode t u v) (RefEl w)    ba bc () aU cU
  finMemUCode-Sup-k (suc k) (IdCode t u v) (IdCode t' u' v') ba bc comp aU cU =
    let bt   = max-Le-l (RANK t) (max (RANK u) (RANK v)) k ba
        buv  = max-Le-r (RANK t) (max (RANK u) (RANK v)) k ba
        bu   = max-Le-l (RANK u) (RANK v) k buv
        bv   = max-Le-r (RANK u) (RANK v) k buv
        bt'  = max-Le-l (RANK t') (max (RANK u') (RANK v')) k bc
        buv' = max-Le-r (RANK t') (max (RANK u') (RANK v')) k bc
        bu'  = max-Le-l (RANK u') (RANK v') k buv'
        bv'  = max-Le-r (RANK u') (RANK v') k buv'
        comp-t = fst comp ; comp-u = fst (snd comp) ; comp-v = snd (snd comp)
        tU  = finMemC-idU-dom t u v aU ; uT  = finMemC-idU-lhs t u v aU ; vT  = finMemC-idU-rhs t u v aU
        t'U = finMemC-idU-dom t' u' v' cU ; u'T = finMemC-idU-lhs t' u' v' cU ; v'T = finMemC-idU-rhs t' u' v' cU
        supT = finMemUCode-Sup-k k t t' bt bt' comp-t tU t'U
        supU = finMem-Sup-both-k k u u' t t' bu bu' bt bt' uT u'T comp-t comp-u
        supV = finMem-Sup-both-k k v v' t t' bv bv' bt bt' vT v'T comp-t comp-v
    in finMemC-idU-mk (Sup t t') (Sup u u') (Sup v v') supT supU supV

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
  -- Id fragment: member u = IdCode (a type-code, only in UCode)
  finMem-Sup-right-k k a Bot          (IdCode t' u' v') ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a (FunEl h)    (IdCode t' u' v') ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a (PiCode c h) (IdCode t' u' v') ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a (IdCode _ _ _) (IdCode t' u' v') ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a (RefEl _)    (IdCode t' u' v') ba bb bu comp aU cohu ()
  finMem-Sup-right-k k Bot          UCode (IdCode t' u' v') ba bb bu comp aU cohu mem = mem
  finMem-Sup-right-k k UCode        UCode (IdCode t' u' v') ba bb bu comp aU cohu mem = mem
  finMem-Sup-right-k k (FunEl g)    UCode (IdCode t' u' v') ba bb bu comp () cohu mem
  finMem-Sup-right-k k (PiCode d q) UCode (IdCode t' u' v') ba bb bu () aU cohu mem
  finMem-Sup-right-k k (IdCode _ _ _) UCode (IdCode t' u' v') ba bb bu () aU cohu mem
  finMem-Sup-right-k k (RefEl _)    UCode (IdCode t' u' v') ba bb bu () aU cohu mem
  -- Id fragment: member u = RefEl (a proof, only in an IdCode type)
  finMem-Sup-right-k k a Bot          (RefEl w) ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a UCode        (RefEl w) ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a (FunEl h)    (RefEl w) ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a (PiCode c h) (RefEl w) ba bb bu comp aU cohu ()
  finMem-Sup-right-k k a (RefEl _)    (RefEl w) ba bb bu comp aU cohu ()
  finMem-Sup-right-k k Bot          (IdCode t' u' v') (RefEl w) ba bb bu comp aU cohu mem = mem
  finMem-Sup-right-k k UCode        (IdCode t' u' v') (RefEl w) ba bb bu () aU cohu mem
  finMem-Sup-right-k k (FunEl g)    (IdCode t' u' v') (RefEl w) ba bb bu () aU cohu mem
  finMem-Sup-right-k k (PiCode d q) (IdCode t' u' v') (RefEl w) ba bb bu () aU cohu mem
  finMem-Sup-right-k k (RefEl _)    (IdCode t' u' v') (RefEl w) ba bb bu () aU cohu mem
  finMem-Sup-right-k k (IdCode t'' u'' v'') (IdCode t' u' v') (RefEl w) ba bb bu comp aU cohu mem =
    let bt''  = Le-trans (RANK t'') (RANK (IdCode t'' u'' v'')) k (bTId t'' u'' v'') ba
        bu''  = Le-trans (RANK u'') (RANK (IdCode t'' u'' v'')) k (bUId t'' u'' v'') ba
        bv''  = Le-trans (RANK v'') (RANK (IdCode t'' u'' v'')) k (bVId t'' u'' v'') ba
        bt'   = Le-trans (RANK t') (RANK (IdCode t' u' v')) k (bTId t' u' v') bb
        bu'   = Le-trans (RANK u') (RANK (IdCode t' u' v')) k (bUId t' u' v') bb
        bv'   = Le-trans (RANK v') (RANK (IdCode t' u' v')) k (bVId t' u' v') bb
        bw    = Le-trans (RANK w) (RANK (RefEl w)) k (bRefW w) bu
        ct = fst comp ; cu = fst (snd comp) ; cv = snd (snd comp)
        cw   = finMemC-ref-coh w t' u' v' mem
        wt'  = finMemC-ref-wit w t' u' v' mem
        leWu' = finMemC-ref-le1 w t' u' v' mem
        leWv' = finMemC-ref-le2 w t' u' v' mem
        t'U = finMemC-ref-tU w t' u' v' mem ; u'T = finMemC-ref-uT w t' u' v' mem ; v'T = finMemC-ref-vT w t' u' v' mem
        t''U = finMemC-idU-dom t'' u'' v'' aU ; u''T = finMemC-idU-lhs t'' u'' v'' aU ; v''T = finMemC-idU-rhs t'' u'' v'' aU
        coht' = coh-from-aU t' t'U
        cohu'' = FinMem-coh-u u'' t'' u''T ; cohu' = FinMem-coh-u u' t' u'T
        cohv'' = FinMem-coh-u v'' t'' v''T ; cohv' = FinMem-coh-u v' t' v'T
        cohSupU = Coherent-Sup u'' u' cu cohu'' cohu'
        cohSupV = Coherent-Sup v'' v' cv cohv'' cohv'
        w-in-SupT = finMem-Sup-right-k k t'' t' w bt'' bt' bw ct t''U cw wt'
        leW-SupU = LeCode-trans w u' (Sup u'' u') cw cohu' cohSupU leWu' (LeCode-Sup-right u'' u' cu cohu'' cohu')
        leW-SupV = LeCode-trans w v' (Sup v'' v') cw cohv' cohSupV leWv' (LeCode-Sup-right v'' v' cv cohv'' cohv')
        supT = finMemUCode-Sup-k k t'' t' bt'' bt' ct t''U t'U
        supU = finMem-Sup-both-k k u'' u' t'' t' bu'' bu' bt'' bt' u''T u'T ct cu
        supV = finMem-Sup-both-k k v'' v' t'' t' bv'' bv' bt'' bt' v''T v'T ct cv
    in finMemC-ref-mk w (Sup t'' t') (Sup u'' u') (Sup v'' v')
         cw w-in-SupT leW-SupU leW-SupV supT supU supV

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
  -- Id fragment: member u = IdCode (a type-code, only in UCode)
  finMem-Sup-left-k k Bot          b (IdCode t' u' v') ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k (FunEl g)    b (IdCode t' u' v') ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k (PiCode d q) b (IdCode t' u' v') ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k (IdCode _ _ _) b (IdCode t' u' v') ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k (RefEl _)    b (IdCode t' u' v') ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k UCode Bot          (IdCode t' u' v') ba bb bu comp coha cohb bU cohu mem = mem
  finMem-Sup-left-k k UCode UCode        (IdCode t' u' v') ba bb bu comp coha cohb bU cohu mem = mem
  finMem-Sup-left-k k UCode (FunEl h)    (IdCode t' u' v') ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k UCode (PiCode c h) (IdCode t' u' v') ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k UCode (IdCode _ _ _) (IdCode t' u' v') ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k UCode (RefEl _)    (IdCode t' u' v') ba bb bu () coha cohb bU cohu mem
  -- Id fragment: member u = RefEl (a proof, only in an IdCode type)
  finMem-Sup-left-k k Bot          b (RefEl w) ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k UCode        b (RefEl w) ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k (FunEl g)    b (RefEl w) ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k (PiCode d q) b (RefEl w) ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k (RefEl _)    b (RefEl w) ba bb bu comp coha cohb bU cohu ()
  finMem-Sup-left-k k (IdCode t' u' v') Bot          (RefEl w) ba bb bu comp coha cohb bU cohu mem = mem
  finMem-Sup-left-k k (IdCode t' u' v') UCode        (RefEl w) ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k (IdCode t' u' v') (FunEl h)    (RefEl w) ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k (IdCode t' u' v') (PiCode c h) (RefEl w) ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k (IdCode t' u' v') (RefEl _)    (RefEl w) ba bb bu () coha cohb bU cohu mem
  finMem-Sup-left-k k (IdCode t' u' v') (IdCode t'' u'' v'') (RefEl w) ba bb bu comp coha cohb bU cohu mem =
    let bt'   = Le-trans (RANK t') (RANK (IdCode t' u' v')) k (bTId t' u' v') ba
        bu'   = Le-trans (RANK u') (RANK (IdCode t' u' v')) k (bUId t' u' v') ba
        bv'   = Le-trans (RANK v') (RANK (IdCode t' u' v')) k (bVId t' u' v') ba
        bt''  = Le-trans (RANK t'') (RANK (IdCode t'' u'' v'')) k (bTId t'' u'' v'') bb
        bu''  = Le-trans (RANK u'') (RANK (IdCode t'' u'' v'')) k (bUId t'' u'' v'') bb
        bv''  = Le-trans (RANK v'') (RANK (IdCode t'' u'' v'')) k (bVId t'' u'' v'') bb
        bw    = Le-trans (RANK w) (RANK (RefEl w)) k (bRefW w) bu
        ct = fst comp ; cu = fst (snd comp) ; cv = snd (snd comp)
        coht' = fst coha ; cohu' = fst (snd coha) ; cohv' = snd (snd coha)
        coht'' = fst cohb ; cohu'' = fst (snd cohb) ; cohv'' = snd (snd cohb)
        cw   = finMemC-ref-coh w t' u' v' mem
        wt'  = finMemC-ref-wit w t' u' v' mem
        leWu' = finMemC-ref-le1 w t' u' v' mem
        leWv' = finMemC-ref-le2 w t' u' v' mem
        t'U = finMemC-ref-tU w t' u' v' mem ; u'T = finMemC-ref-uT w t' u' v' mem ; v'T = finMemC-ref-vT w t' u' v' mem
        t''U = finMemC-idU-dom t'' u'' v'' bU ; u''T = finMemC-idU-lhs t'' u'' v'' bU ; v''T = finMemC-idU-rhs t'' u'' v'' bU
        cohSupU = Coherent-Sup u' u'' cu cohu' cohu''
        cohSupV = Coherent-Sup v' v'' cv cohv' cohv''
        w-in-SupT = finMem-Sup-left-k k t' t'' w bt' bt'' bw ct coht' coht'' t''U cw wt'
        leW-SupU = LeCode-trans w u' (Sup u' u'') cw cohu' cohSupU leWu' (LeCode-Sup-left u' u'' cu cohu' cohu'')
        leW-SupV = LeCode-trans w v' (Sup v' v'') cw cohv' cohSupV leWv' (LeCode-Sup-left v' v'' cv cohv' cohv'')
        supT = finMemUCode-Sup-k k t' t'' bt' bt'' ct t'U t''U
        supU = finMem-Sup-both-k k u' u'' t' t'' bu' bu'' bt' bt'' u'T u''T ct cu
        supV = finMem-Sup-both-k k v' v'' t' t'' bv' bv'' bt' bt'' v'T v''T ct cv
    in finMemC-ref-mk w (Sup t' t'') (Sup u' u'') (Sup v' v'')
         cw w-in-SupT leW-SupU leW-SupV supT supU supV

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

  -- Element-level Sup at a FIXED type a (fuel-indexed; the IdCode / PiCode
  -- type-code cases route through finMemUCode-Sup-k, and the RefEl proof
  -- case recurses structurally into the witness component).
  FinMem-Sup-element-k : (k : Nat) (u v a : FinEl) ->
    Le (RANK u) k -> Le (RANK v) k -> Le (RANK a) k ->
    Comp u v -> Coherent a -> finMemC u a -> finMemC v a -> finMemC (Sup u v) a
  FinMem-Sup-element-k k Bot            v            a              bu bv ba comp ca mu mv = mv
  FinMem-Sup-element-k k UCode          Bot          a              bu bv ba comp ca mu mv = mu
  FinMem-Sup-element-k k (FunEl g)      Bot          a              bu bv ba comp ca mu mv = mu
  FinMem-Sup-element-k k (PiCode a1 f1) Bot          a              bu bv ba comp ca mu mv = mu
  FinMem-Sup-element-k k (IdCode t u v) Bot          a              bu bv ba comp ca mu mv = mu
  FinMem-Sup-element-k k (RefEl w)      Bot          a              bu bv ba comp ca mu mv = mu
  FinMem-Sup-element-k k UCode          UCode        UCode          bu bv ba comp ca mu mv = mu
  FinMem-Sup-element-k k UCode          UCode        Bot            bu bv ba comp ca () mv
  FinMem-Sup-element-k k UCode          UCode        (FunEl h)      bu bv ba comp ca () mv
  FinMem-Sup-element-k k UCode          UCode        (PiCode b f)   bu bv ba comp ca () mv
  FinMem-Sup-element-k k UCode          UCode        (IdCode _ _ _) bu bv ba comp ca () mv
  FinMem-Sup-element-k k UCode          UCode        (RefEl _)      bu bv ba comp ca () mv
  FinMem-Sup-element-k k UCode          (FunEl h)    a              bu bv ba () ca mu mv
  FinMem-Sup-element-k k UCode          (PiCode b f) a              bu bv ba () ca mu mv
  FinMem-Sup-element-k k UCode          (IdCode _ _ _) a            bu bv ba () ca mu mv
  FinMem-Sup-element-k k UCode          (RefEl _)    a              bu bv ba () ca mu mv
  FinMem-Sup-element-k k (FunEl g)      UCode        a              bu bv ba () ca mu mv
  FinMem-Sup-element-k k (FunEl g)      (PiCode b f) a              bu bv ba () ca mu mv
  FinMem-Sup-element-k k (FunEl g)      (IdCode _ _ _) a            bu bv ba () ca mu mv
  FinMem-Sup-element-k k (FunEl g)      (RefEl _)    a              bu bv ba () ca mu mv
  FinMem-Sup-element-k k (FunEl g)      (FunEl h)    Bot            bu bv ba comp ca () mv
  FinMem-Sup-element-k k (FunEl g)      (FunEl h)    UCode          bu bv ba comp ca () mv
  FinMem-Sup-element-k k (FunEl g)      (FunEl h)    (FunEl kk)     bu bv ba comp ca () mv
  FinMem-Sup-element-k k (FunEl g)      (FunEl h)    (PiCode b f)   bu bv ba comp ca mu mv =
    finMemC-funel-mk (append g h) b f
      (FinMemFun-append g h b f (finMemC-funel-fun g b f mu) (finMemC-funel-fun h b f mv))
      (CoherentFun-append g h (finMemC-funel-coh g b f mu) (finMemC-funel-coh h b f mv) comp)
      (finMemC-funel-wf g b f mu)
  FinMem-Sup-element-k k (FunEl g)      (FunEl h)    (IdCode _ _ _) bu bv ba comp ca () mv
  FinMem-Sup-element-k k (FunEl g)      (FunEl h)    (RefEl _)      bu bv ba comp ca () mv
  FinMem-Sup-element-k k (PiCode a1 f1) UCode        a              bu bv ba () ca mu mv
  FinMem-Sup-element-k k (PiCode a1 f1) (FunEl h)    a              bu bv ba () ca mu mv
  FinMem-Sup-element-k k (PiCode a1 f1) (IdCode _ _ _) a            bu bv ba () ca mu mv
  FinMem-Sup-element-k k (PiCode a1 f1) (RefEl _)    a              bu bv ba () ca mu mv
  FinMem-Sup-element-k k (PiCode a1 f1) (PiCode a2 f2) Bot          bu bv ba comp ca () mv
  FinMem-Sup-element-k k (PiCode a1 f1) (PiCode a2 f2) UCode        bu bv ba comp ca mu mv =
    finMemUCode-Sup-k k (PiCode a1 f1) (PiCode a2 f2) bu bv comp mu mv
  FinMem-Sup-element-k k (PiCode a1 f1) (PiCode a2 f2) (FunEl h)    bu bv ba comp ca () mv
  FinMem-Sup-element-k k (PiCode a1 f1) (PiCode a2 f2) (PiCode b f) bu bv ba comp ca () mv
  FinMem-Sup-element-k k (PiCode a1 f1) (PiCode a2 f2) (IdCode _ _ _) bu bv ba comp ca () mv
  FinMem-Sup-element-k k (PiCode a1 f1) (PiCode a2 f2) (RefEl _)    bu bv ba comp ca () mv
  FinMem-Sup-element-k k (IdCode t u v) UCode        a              bu bv ba () ca mu mv
  FinMem-Sup-element-k k (IdCode t u v) (FunEl h)    a              bu bv ba () ca mu mv
  FinMem-Sup-element-k k (IdCode t u v) (PiCode b f) a              bu bv ba () ca mu mv
  FinMem-Sup-element-k k (IdCode t u v) (RefEl _)    a              bu bv ba () ca mu mv
  FinMem-Sup-element-k k (IdCode t u v) (IdCode t' u' v') Bot       bu bv ba comp ca () mv
  FinMem-Sup-element-k k (IdCode t u v) (IdCode t' u' v') UCode     bu bv ba comp ca mu mv =
    finMemUCode-Sup-k k (IdCode t u v) (IdCode t' u' v') bu bv comp mu mv
  FinMem-Sup-element-k k (IdCode t u v) (IdCode t' u' v') (FunEl h) bu bv ba comp ca () mv
  FinMem-Sup-element-k k (IdCode t u v) (IdCode t' u' v') (PiCode b f) bu bv ba comp ca () mv
  FinMem-Sup-element-k k (IdCode t u v) (IdCode t' u' v') (IdCode _ _ _) bu bv ba comp ca () mv
  FinMem-Sup-element-k k (IdCode t u v) (IdCode t' u' v') (RefEl _) bu bv ba comp ca () mv
  FinMem-Sup-element-k k (RefEl w)      UCode        a              bu bv ba () ca mu mv
  FinMem-Sup-element-k k (RefEl w)      (FunEl h)    a              bu bv ba () ca mu mv
  FinMem-Sup-element-k k (RefEl w)      (PiCode b f) a              bu bv ba () ca mu mv
  FinMem-Sup-element-k k (RefEl w)      (IdCode _ _ _) a            bu bv ba () ca mu mv
  FinMem-Sup-element-k k (RefEl w1)     (RefEl w2)   Bot            bu bv ba comp ca () mv
  FinMem-Sup-element-k k (RefEl w1)     (RefEl w2)   UCode          bu bv ba comp ca () mv
  FinMem-Sup-element-k k (RefEl w1)     (RefEl w2)   (FunEl h)      bu bv ba comp ca () mv
  FinMem-Sup-element-k k (RefEl w1)     (RefEl w2)   (PiCode b f)   bu bv ba comp ca () mv
  FinMem-Sup-element-k k (RefEl w1)     (RefEl w2)   (RefEl _)      bu bv ba comp ca () mv
  FinMem-Sup-element-k k (RefEl w1)     (RefEl w2)   (IdCode t u v) bu bv ba comp ca mu mv =
    let bw1 = Le-trans (RANK w1) (RANK (RefEl w1)) k (bRefW w1) bu
        bw2 = Le-trans (RANK w2) (RANK (RefEl w2)) k (bRefW w2) bv
        bt  = Le-trans (RANK t) (RANK (IdCode t u v)) k (bTId t u v) ba
        cw1 = finMemC-ref-coh w1 t u v mu ; cw2 = finMemC-ref-coh w2 t u v mv
        w1t = finMemC-ref-wit w1 t u v mu ; w2t = finMemC-ref-wit w2 t u v mv
        le1u = finMemC-ref-le1 w1 t u v mu ; le1v = finMemC-ref-le2 w1 t u v mu
        le2u = finMemC-ref-le1 w2 t u v mv ; le2v = finMemC-ref-le2 w2 t u v mv
        tU = finMemC-ref-tU w1 t u v mu ; uT = finMemC-ref-uT w1 t u v mu ; vT = finMemC-ref-vT w1 t u v mu
        cohT = coh-from-aU t tU
        cSup = Coherent-Sup w1 w2 comp cw1 cw2
        wSup-t = FinMem-Sup-element-k k w1 w2 t bw1 bw2 bt comp cohT w1t w2t
        leSupU = LeCode-Sup-lub w1 w2 u le1u le2u
        leSupV = LeCode-Sup-lub w1 w2 v le1v le2v
    in finMemC-ref-mk (Sup w1 w2) t u v cSup wSup-t leSupU leSupV tU uT vT

  finMem-Sup-both-k : (k : Nat) (a1 a2 u1 u2 : FinEl) ->
    Le (RANK a1) k -> Le (RANK a2) k -> Le (RANK u1) k -> Le (RANK u2) k ->
    finMemC a1 u1 -> finMemC a2 u2 -> Comp u1 u2 -> Comp a1 a2 ->
    finMemC (Sup a1 a2) (Sup u1 u2)
  finMem-Sup-both-k k a1 a2 u1 u2 ba1 ba2 bu1 bu2 m1 m2 comp-u comp-a =
    let u1U = FinMem-a-in-U a1 u1 m1
        u2U = FinMem-a-in-U a2 u2 m2
        cu1 = coh-from-aU u1 u1U ; cu2 = coh-from-aU u2 u2U
        ca1 = FinMem-coh-u a1 u1 m1 ; ca2 = FinMem-coh-u a2 u2 m2
        c-sup = Coherent-Sup u1 u2 comp-u cu1 cu2
        m1' = finMem-Sup-left-k  k u1 u2 a1 bu1 bu2 ba1 comp-u cu1 cu2 u2U ca1 m1
        m2' = finMem-Sup-right-k k u1 u2 a2 bu1 bu2 ba2 comp-u u1U ca2 m2
        bSup = Le-trans (RANK (Sup u1 u2)) (max (RANK u1) (RANK u2)) k
                 (RANK-Sup u1 u2) (Le-max-lub (RANK u1) (RANK u2) k bu1 bu2)
    in FinMem-Sup-element-k k a1 a2 (Sup u1 u2) ba1 ba2 bSup comp-a c-sup m1' m2'

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
  -- Id fragment: member v = IdCode (a type-code, only lives in UCode)
  finMem-upward (IdCode t' u' v') UCode        UCode        le ca cb mem bU = mem
  finMem-upward (IdCode t' u' v') UCode        Bot          ()
  finMem-upward (IdCode t' u' v') UCode        (FunEl h)    ()
  finMem-upward (IdCode t' u' v') UCode        (PiCode c h) ()
  finMem-upward (IdCode t' u' v') UCode        (IdCode _ _ _) ()
  finMem-upward (IdCode t' u' v') UCode        (RefEl _)    ()
  finMem-upward (IdCode t' u' v') Bot          b            le ca cb ()
  finMem-upward (IdCode t' u' v') (FunEl g)    b            le ca cb ()
  finMem-upward (IdCode t' u' v') (PiCode c h) b            le ca cb ()
  finMem-upward (IdCode t' u' v') (IdCode _ _ _) b          le ca cb ()
  finMem-upward (IdCode t' u' v') (RefEl _)    b            le ca cb ()
  -- Id fragment: member v = RefEl (a proof, only lives in an IdCode type)
  finMem-upward (RefEl w) Bot          b            le ca cb ()
  finMem-upward (RefEl w) UCode        b            le ca cb ()
  finMem-upward (RefEl w) (FunEl g)    b            le ca cb ()
  finMem-upward (RefEl w) (PiCode c h) b            le ca cb ()
  finMem-upward (RefEl w) (RefEl _)    b            le ca cb ()
  finMem-upward (RefEl w) (IdCode t' u' v') Bot          () ca cb mem bU
  finMem-upward (RefEl w) (IdCode t' u' v') UCode        () ca cb mem bU
  finMem-upward (RefEl w) (IdCode t' u' v') (FunEl h)    () ca cb mem bU
  finMem-upward (RefEl w) (IdCode t' u' v') (PiCode c h) () ca cb mem bU
  finMem-upward (RefEl w) (IdCode t' u' v') (RefEl _)    () ca cb mem bU
  finMem-upward (RefEl w) (IdCode t' u' v') (IdCode t'' u'' v'') le ca cb mem bU =
    let coht' = fst ca ; cohu' = fst (snd ca) ; cohv' = snd (snd ca)
        coht'' = fst cb ; cohu'' = fst (snd cb) ; cohv'' = snd (snd cb)
        leT = fst le ; leU = fst (snd le) ; leV = snd (snd le)
        cw = finMemC-ref-coh w t' u' v' mem
        wt' = finMemC-ref-wit w t' u' v' mem
        leWu' = finMemC-ref-le1 w t' u' v' mem
        leWv' = finMemC-ref-le2 w t' u' v' mem
        t''U = finMemC-idU-dom t'' u'' v'' bU ; u''T = finMemC-idU-lhs t'' u'' v'' bU ; v''T = finMemC-idU-rhs t'' u'' v'' bU
        w-t'' = finMem-upward w t' t'' leT coht' coht'' wt' t''U
        leWu'' = LeCode-trans w u' u'' cw cohu' cohu'' leWu' leU
        leWv'' = LeCode-trans w v' v'' cw cohv' cohv'' leWv' leV
    in finMemC-ref-mk w t'' u'' v'' cw w-t'' leWu'' leWv'' t''U u''T v''T

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

FinMem-Sup-element : (u v a : FinEl) -> Comp u v -> Coherent a ->
  finMemC u a -> finMemC v a -> finMemC (Sup u v) a
FinMem-Sup-element u v a =
  FinMem-Sup-element-k (max (RANK u) (max (RANK v) (RANK a))) u v a
    (b3-x (RANK u) (RANK v) (RANK a)) (b3-y (RANK u) (RANK v) (RANK a)) (b3-z (RANK u) (RANK v) (RANK a))

finMem-Sup-both : (a1 a2 u1 u2 : FinEl) ->
  finMemC a1 u1 -> finMemC a2 u2 -> Comp u1 u2 -> Comp a1 a2 ->
  finMemC (Sup a1 a2) (Sup u1 u2)
finMem-Sup-both a1 a2 u1 u2 =
  let k = max (max (RANK a1) (RANK a2)) (max (RANK u1) (RANK u2))
  in finMem-Sup-both-k k a1 a2 u1 u2
       (Le-trans (RANK a1) (max (RANK a1) (RANK a2)) k (Le-max-l (RANK a1) (RANK a2)) (Le-max-l (max (RANK a1) (RANK a2)) (max (RANK u1) (RANK u2))))
       (Le-trans (RANK a2) (max (RANK a1) (RANK a2)) k (Le-max-r (RANK a1) (RANK a2)) (Le-max-l (max (RANK a1) (RANK a2)) (max (RANK u1) (RANK u2))))
       (Le-trans (RANK u1) (max (RANK u1) (RANK u2)) k (Le-max-l (RANK u1) (RANK u2)) (Le-max-r (max (RANK a1) (RANK a2)) (max (RANK u1) (RANK u2))))
       (Le-trans (RANK u2) (max (RANK u1) (RANK u2)) k (Le-max-r (RANK u1) (RANK u2)) (Le-max-r (max (RANK a1) (RANK a2)) (max (RANK u1) (RANK u2))))
