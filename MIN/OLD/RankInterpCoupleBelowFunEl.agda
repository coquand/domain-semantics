{-# OPTIONS --without-K --exact-split #-}
------------------------------------------------------------------------
-- RankInterpCoupleBelowFunEl.agda  (MIN/ -- Pi + U fragment)
--
-- CASE 4 per-edge core : couple-BELOW on a FUNCTION element.
--   reduce  FunEl kg : PiCode a0 fa  DOWN to  FunEl kg' : PiCode a0' fa'
--   with  ug <= kg' <= kg  (ug = the lower bound u),  b <= b' <= a.
--
-- funelBelow with a TYPE-DOWNCAST: iterate the lower bound ug's edges,
-- select on the TYPED member kg (so the selection key kgSel : a0 is typed,
-- no coordination gap), then per ug-edge (j,d):
--   * key  : couple-ABOVE kgSel up to uj' in [kgSel,j], type a0 -> bEdge (downcast),
--            threading the accumulating domain a0'_acc.
--   * value: couple-BELOW the member value vSel(=EvalFun kg j : EvalFun fa kgSel)
--            DOWN to vj' in [d,vSel], type EvalFun fa kgSel -> tvEdge (downcast)
--            -- ONE call yields both the kg'-value vj' AND the fa'-value tvEdge
--            (= the type of vj'), so kg' and the codomain family fa' are built TOGETHER.
--
-- This file validates the per-edge STATEMENT (the heart of case 4): the
-- builder assembly is the buildBelow/buildKU domain-threading pattern.
------------------------------------------------------------------------
module MIN.OLD.RankInterpCoupleBelowFunEl where

open import MIN.Domain.Basic
open import MIN.Domain.Order
open import MIN.Domain.MemStage
open import MIN.Domain.MemProps using ( finMem-upward ; EvalFun-in-UCode )
open import MIN.Domain.MemUnfold using ( FinMem-coh-u ; coh-from-aU )
open import MIN.Domain.Membership using ( fun-from ; allU-from )
open import MIN.Model.Selection
  using ( Selection ; selectionBelow ; FinMem-Selection ; FinMem-Selection-codomain
        ; Selection-le-EvalFun ; Coherent-Selection ; Coherent-Selection-val
        ; Edge ; EdgeIn ; here ; there )
open import MIN.OLD.RankInterpFunEl
  using ( ihaT ; ihbT ; toStage ; fromStage ; efRank ; LeCode-NotBot
        ; Selection-RANK-u' ; Selection-RANK-v'
        ; edge-le ; GraphInv ; mkCoherentWith ; mkLeFunCode-u0 )
open import MIN.OLD.RankInterpPiBelow using ( BelowOut ; buildBelow )
open import MIN.Domain.MemShift using ( finMemAllU-shift ; finMemFun-shift )

-- couple-ABOVE at predecessor level m (the user's fm-couple).
ihcAboveT : Nat -> Set
ihcAboveT m = (k a u b : FinEl) ->
  Le (RANK k) (suc m) -> Le (RANK a) (suc m) -> Le (RANK u) m -> Le (RANK b) m ->
  Coherent u -> Coherent b ->
  MB.finMem (suc m) a UCode -> MB.finMem (suc m) k a ->
  LeCode k u -> LeCode b a ->
  Sigma FinEl (\ u' -> Sigma FinEl (\ b' ->
    Pair (Le (RANK u') m) (Pair (Le (RANK b') m)
    (Pair (LeCode k u') (Pair (LeCode u' u)
    (Pair (LeCode b b') (Pair (LeCode b' a)
    (Pair (MB.finMem m b' UCode) (MB.finMem m u' b')))))))))

-- couple-BELOW at predecessor level m (the DUAL: u <= k, produce u <= u' <= k).
ihcBelowT : Nat -> Set
ihcBelowT m = (k a u b : FinEl) ->
  Le (RANK k) (suc m) -> Le (RANK a) (suc m) -> Le (RANK u) m -> Le (RANK b) m ->
  Coherent u -> Coherent b ->
  MB.finMem (suc m) a UCode -> MB.finMem (suc m) k a ->
  LeCode u k -> LeCode b a ->
  Sigma FinEl (\ u' -> Sigma FinEl (\ b' ->
    Pair (Le (RANK u') m) (Pair (Le (RANK b') m)
    (Pair (LeCode u u') (Pair (LeCode u' k)
    (Pair (LeCode b b') (Pair (LeCode b' a)
    (Pair (MB.finMem m b' UCode) (MB.finMem m u' b')))))))))

------------------------------------------------------------------------
-- per-edge result.  domEdge is the (grown) domain typing this edge's key;
-- tval is the codomain-family value (the type of kval).
------------------------------------------------------------------------

record EdgeBelow (m : Nat) (a0 : FinEl) (fa kg : FinFun) (domAcc j d : FinEl) : Set where
  field
    ekey kval tval domEdge : FinEl
    rkey   : Le (RANK ekey) m
    rkval  : Le (RANK kval) m
    rtval  : Le (RANK tval) m
    rdomE  : Le (RANK domEdge) m
    keyT   : MB.finMem m ekey domEdge        -- uj' : bEdge
    valT   : MB.finMem m kval tval           -- vj' : tvEdge
    tvalU  : MB.finMem m tval UCode          -- tvEdge : U
    domEU  : MB.finMem m domEdge UCode       -- bEdge : U
    acc-le-domE : LeCode domAcc domEdge      -- domAcc <= bEdge
    dom-le-a0 : LeCode domEdge a0            -- bEdge <= a0
    key-le-j  : LeCode ekey j
    d-le-kval : LeCode d kval
    kval-le-kg : LeCode kval (EvalFun kg ekey)   -- vj' <= EvalFun kg uj'
    tval-le-fa : LeCode tval (EvalFun fa ekey)   -- tvEdge <= EvalFun fa uj'
    cdomE  : Coherent domEdge
    ckey   : Coherent ekey
    ckval  : Coherent kval
    ctval  : Coherent tval
    nbkval : NotBot kval

interpEdgeBelow : (m : Nat) (a0 : FinEl) (fa kg : FinFun) ->
  ihcAboveT m -> ihcBelowT m ->
  CoherentFunTail fa -> CoherentFunTail kg ->
  Coherent a0 -> MB.finMem (suc m) a0 UCode -> finMemC a0 UCode ->
  finMemFunC kg a0 fa -> finMemAllUC fa a0 ->
  Le (RANK a0) (suc m) -> Le (RANKFun fa) (suc m) -> Le (RANKFun kg) (suc m) ->
  (domAcc : FinEl) -> Coherent domAcc -> MB.finMem m domAcc UCode ->
  Le (RANK domAcc) m -> LeCode domAcc a0 ->
  (j d : FinEl) -> Coherent j -> Coherent d -> NotBot d ->
  Le (RANK j) m -> Le (RANK d) m -> LeCode d (EvalFun kg j) ->
  EdgeBelow m a0 fa kg domAcc j d
interpEdgeBelow m a0 fa kg ihcA ihcB ctfa ctkg ca0 a0Um a0UC fmkg faU
                ra0 rfa rkg domAcc cdomAcc domAccUm rdomAcc ldomAcca0
                j d cj cd nbd rj rd led =
  record
    { ekey = uj' ; kval = vj' ; tval = tvEdge ; domEdge = bEdge
    ; rkey = ruj' ; rkval = rvj' ; rtval = rtvEdge ; rdomE = rbEdge
    ; keyT = uj'bEdge ; valT = vj'tv ; tvalU = tvU
    ; domEU = bEdgeUm ; acc-le-domE = ldomAcc-bEdge
    ; dom-le-a0 = lbEdge-a0 ; key-le-j = luj'j ; d-le-kval = ld-vj'
    ; kval-le-kg = vj'-le-kguj' ; tval-le-fa = tv-le-fauj'
    ; cdomE = cbEdge ; ckey = cuj' ; ckval = cvj' ; ctval = ctvEdge
    ; nbkval = LeCode-NotBot d vj' nbd ld-vj' }
  where
    ra0S : Le (RANK a0) (suc m)
    ra0S = ra0
    -- selection of the TYPED member kg at j
    sb    = selectionBelow kg j ctkg cj
    kgSel = fst sb
    vSel  = fst (snd sb)
    sel   = fst (snd (snd sb))
    kgSel-le-j = fst (snd (snd (snd sb)))         -- LeCode kgSel j
    eqV   = snd (snd (snd (snd sb)))              -- Eq (EvalFun kg j) vSel
    ckgSel = Coherent-Selection sel ctkg
    cvSel  = Coherent-Selection-val sel ctkg
    rkgSel = Le-trans (RANK kgSel) (RANKFun kg) (suc m) (Selection-RANK-u' sel) rkg
    -- kgSel : a0   and   vSel : EvalFun fa kgSel
    kgSelb-c : finMemC kgSel a0
    kgSelb-c = FinMem-Selection a0 fa sel (fun-from kg a0 fa fmkg) ctkg ca0 a0UC
    kgSelb : MB.finMem (suc m) kgSel a0
    kgSelb = toStage (suc m) kgSel a0 rkgSel ra0S kgSelb-c
    r-fa-kgSel : Le (RANK (EvalFun fa kgSel)) (suc m)
    r-fa-kgSel = efRank fa kgSel (suc m) rfa
    vSelEf-c : finMemC vSel (EvalFun fa kgSel)
    vSelEf-c = FinMem-Selection-codomain a0 fa sel (fun-from kg a0 fa fmkg) ctkg ctfa
                 (allU-from fa a0 faU)
    -- d <= vSel  (since EvalFun kg j = vSel)
    d-le-vSel : LeCode d vSel
    d-le-vSel = Eq-transport (LeCode d) eqV led
    -- KEY: couple-above kgSel up to uj' in [kgSel,j], domain a0 -> bEdge (>= domAcc)
    cpA = ihcA kgSel a0 j domAcc rkgSel ra0 rj rdomAcc cj cdomAcc a0Um kgSelb kgSel-le-j ldomAcca0
    uj'    = fst cpA
    bEdge  = fst (snd cpA)
    ruj'   = fst (snd (snd cpA))
    rbEdge = fst (snd (snd (snd cpA)))
    lkgSel-uj' = fst (snd (snd (snd (snd cpA))))             -- LeCode kgSel uj'
    luj'j      = fst (snd (snd (snd (snd (snd cpA)))))       -- LeCode uj' j
    ldomAcc-bEdge = fst (snd (snd (snd (snd (snd (snd cpA))))))      -- LeCode domAcc bEdge
    lbEdge-a0  = fst (snd (snd (snd (snd (snd (snd (snd cpA)))))))   -- LeCode bEdge a0
    bEdgeUm    = fst (snd (snd (snd (snd (snd (snd (snd (snd cpA))))))))
    uj'bEdge   = snd (snd (snd (snd (snd (snd (snd (snd (snd cpA))))))))  -- MB.finMem m uj' bEdge
    cbEdge = coh-from-aU bEdge (fromStage m bEdge UCode rbEdge tt bEdgeUm)
    cuj'   = FinMem-coh-u uj' bEdge (fromStage m uj' bEdge ruj' rbEdge uj'bEdge)
    -- VALUE: couple-below vSel (: EvalFun fa kgSel) down to vj' in [d,vSel], type -> tvEdge
    fakgSelUm : MB.finMem (suc m) (EvalFun fa kgSel) UCode
    fakgSelUm = toStage (suc m) (EvalFun fa kgSel) UCode r-fa-kgSel tt
                  (EvalFun-in-UCode fa kgSel a0 ctfa ckgSel faU)
    rvSel : Le (RANK vSel) (suc m)
    rvSel = Le-trans (RANK vSel) (RANKFun kg) (suc m) (Selection-RANK-v' sel) rkg
    vSelEf : MB.finMem (suc m) vSel (EvalFun fa kgSel)
    vSelEf = toStage (suc m) vSel (EvalFun fa kgSel) rvSel r-fa-kgSel vSelEf-c
    cpB = ihcB vSel (EvalFun fa kgSel) d Bot
            rvSel r-fa-kgSel rd tt cd tt fakgSelUm vSelEf d-le-vSel (LeCode-Bot (EvalFun fa kgSel))
    vj'    = fst cpB
    tvEdge = fst (snd cpB)
    rvj'   = fst (snd (snd cpB))
    rtvEdge = fst (snd (snd (snd cpB)))
    ld-vj'   = fst (snd (snd (snd (snd cpB))))            -- LeCode d vj'
    lvj'-vSel = fst (snd (snd (snd (snd (snd cpB)))))     -- LeCode vj' vSel
    ltv-fakgSel = fst (snd (snd (snd (snd (snd (snd (snd cpB)))))))  -- LeCode tvEdge (EvalFun fa kgSel)
    tvU      = fst (snd (snd (snd (snd (snd (snd (snd (snd cpB))))))))  -- MB.finMem m tvEdge UCode
    vj'tv    = snd (snd (snd (snd (snd (snd (snd (snd (snd cpB))))))))  -- MB.finMem m vj' tvEdge
    cvj'   = FinMem-coh-u vj' tvEdge (fromStage m vj' tvEdge rvj' rtvEdge vj'tv)
    ctvEdge = coh-from-aU tvEdge (fromStage m tvEdge UCode rtvEdge tt tvU)
    -- vj' <= EvalFun kg uj'  (kgSel <= uj' preserves the kg-value)
    c-kg-kgSel = Coherent-EvalFun kg kgSel ctkg ckgSel
    c-kg-uj'   = Coherent-EvalFun kg uj' ctkg cuj'
    vSel-le-kgkgSel : LeCode vSel (EvalFun kg kgSel)
    vSel-le-kgkgSel = Selection-le-EvalFun kg sel (LeFunCode-refl kg ctkg) ctkg ctkg ckgSel
    kgkgSel-le-kguj' = EvalFun-mon-arg kg kgSel uj' lkgSel-uj' ctkg ckgSel cuj'
    vSel-le-kguj' = LeCode-trans vSel (EvalFun kg kgSel) (EvalFun kg uj')
                      cvSel c-kg-kgSel c-kg-uj' vSel-le-kgkgSel kgkgSel-le-kguj'
    vj'-le-kguj' : LeCode vj' (EvalFun kg uj')
    vj'-le-kguj' = LeCode-trans vj' vSel (EvalFun kg uj') cvj' cvSel c-kg-uj' lvj'-vSel vSel-le-kguj'
    -- tvEdge <= EvalFun fa uj'  (tvEdge <= EvalFun fa kgSel <= EvalFun fa uj')
    c-fa-kgSel = Coherent-EvalFun fa kgSel ctfa ckgSel
    c-fa-uj'   = Coherent-EvalFun fa uj' ctfa cuj'
    fakgSel-le-fauj' = EvalFun-mon-arg fa kgSel uj' lkgSel-uj' ctfa ckgSel cuj'
    tv-le-fauj' : LeCode tvEdge (EvalFun fa uj')
    tv-le-fauj' = LeCode-trans tvEdge (EvalFun fa kgSel) (EvalFun fa uj')
                    ctvEdge c-fa-kgSel c-fa-uj' ltv-fakgSel fakgSel-le-fauj'

------------------------------------------------------------------------
-- Step A : the case-4 BUILDER around interpEdgeBelow.
--   build  FunEl kgg : PiCode dom fam  with  ug <= kgg <= kg,
--   PiCode b0 fb <= PiCode dom fam <= PiCode a0 fa,  all at rank suc m.
------------------------------------------------------------------------

-- a value's type is NotBot when the value is NotBot.  (Stated on finMemC,
-- whose canonical level is suc _, so finMemC v Bot reduces to Empty.)
notbot-type : (v t : FinEl) -> NotBot v -> finMemC v t -> NotBot t
notbot-type v            UCode        nb mem = tt
notbot-type v            (FunEl h)    nb mem = tt
notbot-type v            (PiCode c h) nb mem = tt
notbot-type Bot          Bot          () mem
notbot-type UCode        Bot          nb ()
notbot-type (FunEl g)    Bot          nb ()
notbot-type (PiCode a f) Bot          nb ()

-- per-kgg-edge typing witness against the (built) family fam.
KgFamWit : (m : Nat) (dom : FinEl) (kgg fam : FinFun) -> Set
KgFamWit m dom nil         fam = Top
KgFamWit m dom (cons p ps) fam =
  Pair (Pair (MB.finMem m (fst p) dom) (Coherent (fst p)))
       (Pair (Le (RANK (snd p)) m)
         (Pair (Sigma FinEl (\ tv ->
                  Pair (Coherent tv) (Pair (Le (RANK tv) m)
                    (Pair (EdgeIn (mkSigma (fst p) tv) fam) (MB.finMem m (snd p) tv)))))
               (KgFamWit m dom ps fam)))

-- lift the witness through a fam-cons (every EdgeIn gets one `there`).
kgwit-mono : (m : Nat) (dom : FinEl) (q : Edge) (kgg fam : FinFun) ->
  KgFamWit m dom kgg fam -> KgFamWit m dom kgg (cons q fam)
kgwit-mono m dom q nil         fam w = tt
kgwit-mono m dom q (cons p ps) fam w =
  mkSigma (fst w)
    (mkSigma (fst (snd w))
      (mkSigma
        (mkSigma (fst tvw)
          (mkSigma (fst (snd tvw))
            (mkSigma (fst (snd (snd tvw)))
              (mkSigma (there (fst (snd (snd (snd tvw)))))
                       (snd (snd (snd (snd tvw))))))))
        (kgwit-mono m dom q ps fam (snd (snd (snd w))))))
  where
    tvw = fst (snd (snd w))

-- assemble the finMemFun against the final fam, one pass via edge-le.
mkFinMemFun : (m : Nat) (dom : FinEl) (kgg fam : FinFun) ->
  CoherentFunTail fam -> Coherent dom -> finMemAllUC fam dom ->
  Le (RANKFun fam) m -> Le (RANK dom) m ->
  KgFamWit m dom kgg fam ->
  MB.finMemFun (suc m) kgg dom fam
mkFinMemFun m dom nil         fam cff cdom faUC rfam rdom w = tt
mkFinMemFun m dom (cons p ps) fam cff cdom faUC rfam rdom w =
  mkSigma (mkSigma keyTy valTy)
    (mkFinMemFun m dom ps fam cff cdom faUC rfam rdom (snd (snd (snd w))))
  where
    keyTy = fst (fst w)
    ckey  = snd (fst w)
    rval  = fst (snd w)
    tvw   = fst (snd (snd w))
    tv    = fst tvw
    ctv   = fst (snd tvw)
    rtv   = fst (snd (snd tvw))
    ein   = fst (snd (snd (snd tvw)))
    valtv = snd (snd (snd (snd tvw)))
    tv-le : LeCode tv (EvalFun fam (fst p))
    tv-le = edge-le (mkSigma (fst p) tv) fam (fst p) cff ein ckey ctv (LeCode-refl (fst p) ckey)
    efU : finMemC (EvalFun fam (fst p)) UCode
    efU = EvalFun-in-UCode fam (fst p) dom cff ckey faUC
    c-ef = Coherent-EvalFun fam (fst p) cff ckey
    val-c = finMem-upward (snd p) tv (EvalFun fam (fst p)) tv-le ctv c-ef
              (fromStage m (snd p) tv rval rtv valtv) efU
    valTy = toStage m (snd p) (EvalFun fam (fst p)) rval (efRank fam (fst p) m rfam) val-c

exFalso : {A : Set} -> Empty -> A
exFalso ()

-- the fused builder output: the function graph kgg AND its Pi-type
-- PiCode dom fam, built together over ug's edges (kgg) with an fb-seed
-- (the tail of fam) supplying the  fb <= fam  domination.
record CBOut (m : Nat) (a0 : FinEl) (fa kg fb : FinFun) (cacc : FinEl) (ugs : FinFun) : Set where
  field
    dom         : FinEl
    rdom        : Le (RANK dom) m
    domUm       : MB.finMem m dom UCode
    cdom        : Coherent dom
    cacc-le-dom : LeCode cacc dom
    dom-le-a0   : LeCode dom a0
    fam         : FinFun
    rfam        : Le (RANKFun fam) m
    famU        : MB.finMemAllU (suc m) fam dom
    cftfam      : CoherentFunTail fam
    lf-fam-fa   : LeFunCode fam fa
    ginvFa      : GraphInv fa fam
    alignFb     : (e : Edge) -> EdgeIn e fb ->
                    Sigma Edge (\ e' -> Pair (EdgeIn e' fam)
                      (Pair (LeCode (fst e') (fst e))
                        (Pair (LeCode (snd e) (snd e')) (Coherent (snd e')))))
    kgg         : FinFun
    rkgg        : Le (RANKFun kgg) m
    cftkgg      : CoherentFunTail kgg
    lf-kgg-kg   : LeFunCode kgg kg
    ginvKg      : GraphInv kg kgg
    kgWit       : KgFamWit m dom kgg fam
    alignUg     : (e : Edge) -> EdgeIn e ugs ->
                    Sigma Edge (\ e' -> Pair (EdgeIn e' kgg)
                      (Pair (LeCode (fst e') (fst e))
                        (Pair (LeCode (snd e) (snd e')) (Coherent (snd e')))))

buildCB : (m : Nat) (a0 : FinEl) (fa kg fb : FinFun) ->
  ihaT m -> ihbT m -> ihcAboveT m -> ihcBelowT m ->
  CoherentFunTail fa -> CoherentFunTail kg -> Coherent a0 ->
  MB.finMem (suc m) a0 UCode -> finMemC a0 UCode ->
  finMemFunC kg a0 fa -> finMemAllUC fa a0 ->
  Le (RANK a0) (suc m) -> Le (RANKFun fa) (suc m) -> Le (RANKFun kg) (suc m) ->
  CoherentFunTail fb -> LeFunCode fb fa -> Le (RANKFun fb) m ->
  (cacc : FinEl) -> Coherent cacc -> MB.finMem m cacc UCode ->
  Le (RANK cacc) m -> LeCode cacc a0 ->
  (ugs : FinFun) -> CoherentFunTail ugs -> LeFunCode ugs kg -> Le (RANKFun ugs) m ->
  CBOut m a0 fa kg fb cacc ugs
buildCB m a0 fa kg fb iha ihb ihcA ihcB ctfa ctkg ca0 a0Um a0UC fmkg faU ra0 rfa rkg
        ctfb lffbfa rfb cacc ccacc caccUm rcacc lcacca0 nil ctugs lfugskg rugs =
  record
    { dom = BelowOut.dom bo ; rdom = BelowOut.rdom bo ; domUm = BelowOut.domUm bo
    ; cdom = BelowOut.cdom bo ; cacc-le-dom = BelowOut.cacc-le-dom bo
    ; dom-le-a0 = BelowOut.dom-le-b bo
    ; fam = BelowOut.fam bo ; rfam = BelowOut.rfam bo ; famU = BelowOut.famU bo
    ; cftfam = BelowOut.cftfam bo ; lf-fam-fa = BelowOut.lf-fam-f bo ; ginvFa = BelowOut.ginvF bo
    ; alignFb = BelowOut.alignK bo
    ; kgg = nil ; rkgg = tt ; cftkgg = tt ; lf-kgg-kg = tt ; ginvKg = \ { q () }
    ; kgWit = tt ; alignUg = \ { e () } }
  where
    bo = buildBelow m a0 fa iha ihb ihcA ctfa ca0 a0UC a0Um faU ra0 rfa
           cacc ccacc caccUm rcacc lcacca0 fb ctfb lffbfa rfb
buildCB m a0 fa kg fb iha ihb ihcA ihcB ctfa ctkg ca0 a0Um a0UC fmkg faU ra0 rfa rkg
        ctfb lffbfa rfb cacc ccacc caccUm rcacc lcacca0 (cons p ps) ctugs lfugskg rugs =
  record
    { dom = dom ; rdom = CBOut.rdom ih ; domUm = CBOut.domUm ih ; cdom = cdom
    ; cacc-le-dom = LeCode-trans cacc bEdge dom ccacc cbEdge cdom
                      (EdgeBelow.acc-le-domE eo) (CBOut.cacc-le-dom ih)
    ; dom-le-a0 = CBOut.dom-le-a0 ih
    ; fam = cons (mkSigma uj' tvEdge) (CBOut.fam ih)
    ; rfam = Le-max-lub (RANK uj') (max (RANK tvEdge) (RANKFun (CBOut.fam ih))) m
               (EdgeBelow.rkey eo)
               (Le-max-lub (RANK tvEdge) (RANKFun (CBOut.fam ih)) m (EdgeBelow.rtval eo) (CBOut.rfam ih))
    ; famU = mkSigma (mkSigma uj'-dom (EdgeBelow.tvalU eo)) (CBOut.famU ih)
    ; cftfam = record
        { key-coh = EdgeBelow.ckey eo ; val-coh = EdgeBelow.ctval eo
        ; val-nbot = notbot-type vj' tvEdge (EdgeBelow.nbkval eo)
                       (fromStage m vj' tvEdge (EdgeBelow.rkval eo) (EdgeBelow.rtval eo) (EdgeBelow.valT eo))
        ; compat = mkCoherentWith fa (mkSigma uj' tvEdge) (CBOut.fam ih) ctfa
                     (EdgeBelow.ckey eo) (EdgeBelow.tval-le-fa eo) (CBOut.ginvFa ih)
        ; tail-coh = CBOut.cftfam ih }
    ; lf-fam-fa = mkSigma (EdgeBelow.tval-le-fa eo) (CBOut.lf-fam-fa ih)
    ; ginvFa = \ { q here -> mkSigma (EdgeBelow.ckey eo) (EdgeBelow.tval-le-fa eo)
                 ; q (there e) -> CBOut.ginvFa ih q e }
    ; alignFb = \ e ein -> let r = CBOut.alignFb ih e ein
                           in mkSigma (fst r) (mkSigma (there (fst (snd r))) (snd (snd r)))
    ; kgg = cons (mkSigma uj' vj') (CBOut.kgg ih)
    ; rkgg = Le-max-lub (RANK uj') (max (RANK vj') (RANKFun (CBOut.kgg ih))) m
               (EdgeBelow.rkey eo)
               (Le-max-lub (RANK vj') (RANKFun (CBOut.kgg ih)) m (EdgeBelow.rkval eo) (CBOut.rkgg ih))
    ; cftkgg = record
        { key-coh = EdgeBelow.ckey eo ; val-coh = EdgeBelow.ckval eo ; val-nbot = EdgeBelow.nbkval eo
        ; compat = mkCoherentWith kg (mkSigma uj' vj') (CBOut.kgg ih) ctkg
                     (EdgeBelow.ckey eo) (EdgeBelow.kval-le-kg eo) (CBOut.ginvKg ih)
        ; tail-coh = CBOut.cftkgg ih }
    ; lf-kgg-kg = mkSigma (EdgeBelow.kval-le-kg eo) (CBOut.lf-kgg-kg ih)
    ; ginvKg = \ { q here -> mkSigma (EdgeBelow.ckey eo) (EdgeBelow.kval-le-kg eo)
                 ; q (there e) -> CBOut.ginvKg ih q e }
    ; kgWit = mkSigma (mkSigma uj'-dom (EdgeBelow.ckey eo))
                (mkSigma (EdgeBelow.rkval eo)
                  (mkSigma (mkSigma tvEdge (mkSigma (EdgeBelow.ctval eo)
                              (mkSigma (EdgeBelow.rtval eo) (mkSigma here (EdgeBelow.valT eo)))))
                    (kgwit-mono m dom (mkSigma uj' tvEdge) (CBOut.kgg ih) (CBOut.fam ih) (CBOut.kgWit ih))))
    ; alignUg = \ { e here ->
                      mkSigma (mkSigma uj' vj')
                        (mkSigma here (mkSigma (EdgeBelow.key-le-j eo)
                          (mkSigma (EdgeBelow.d-le-kval eo) (EdgeBelow.ckval eo))))
                  ; e (there e') -> let r = CBOut.alignUg ih e e'
                                    in mkSigma (fst r) (mkSigma (there (fst (snd r))) (snd (snd r))) } }
  where
    j = fst p ; d = snd p
    cj = CFTcons.key-coh ctugs ; cd = CFTcons.val-coh ctugs ; nbd = CFTcons.val-nbot ctugs
    led = fst lfugskg
    rj = Le-trans (RANK j) (RANKFun (cons p ps)) m
           (Le-max-l (RANK j) (max (RANK d) (RANKFun ps))) rugs
    rd = Le-trans (RANK d) (RANKFun (cons p ps)) m
           (Le-trans (RANK d) (max (RANK d) (RANKFun ps)) (RANKFun (cons p ps))
             (Le-max-l (RANK d) (RANKFun ps))
             (Le-max-r (RANK j) (max (RANK d) (RANKFun ps)))) rugs
    rps = Le-trans (RANKFun ps) (RANKFun (cons p ps)) m
            (Le-trans (RANKFun ps) (max (RANK d) (RANKFun ps)) (RANKFun (cons p ps))
              (Le-max-r (RANK d) (RANKFun ps))
              (Le-max-r (RANK j) (max (RANK d) (RANKFun ps)))) rugs
    eo = interpEdgeBelow m a0 fa kg ihcA ihcB ctfa ctkg ca0 a0Um a0UC fmkg faU ra0 rfa rkg
           cacc ccacc caccUm rcacc lcacca0 j d cj cd nbd rj rd led
    uj' = EdgeBelow.ekey eo ; vj' = EdgeBelow.kval eo
    tvEdge = EdgeBelow.tval eo ; bEdge = EdgeBelow.domEdge eo
    cbEdge = EdgeBelow.cdomE eo
    ih = buildCB m a0 fa kg fb iha ihb ihcA ihcB ctfa ctkg ca0 a0Um a0UC fmkg faU ra0 rfa rkg
           ctfb lffbfa rfb bEdge cbEdge (EdgeBelow.domEU eo) (EdgeBelow.rdomE eo) (EdgeBelow.dom-le-a0 eo)
           ps (CFTcons.tail-coh ctugs) (snd lfugskg) rps
    dom = CBOut.dom ih
    cdom = CBOut.cdom ih
    uj'-dom : MB.finMem m uj' dom
    uj'-dom = toStage m uj' dom (EdgeBelow.rkey eo) (CBOut.rdom ih)
                (finMem-upward uj' bEdge dom (CBOut.cacc-le-dom ih) cbEdge cdom
                  (fromStage m uj' bEdge (EdgeBelow.rkey eo) (EdgeBelow.rdomE eo) (EdgeBelow.keyT eo))
                  (fromStage m dom UCode (CBOut.rdom ih) tt (CBOut.domUm ih)))

------------------------------------------------------------------------
-- Top-level : the couple-BELOW FunEl case (u = FunEl ug, ug nonempty).
------------------------------------------------------------------------

coupleBelowFunEl : (m : Nat) (kg : FinFun) (a0 : FinEl) (fa : FinFun) ->
  ihaT m -> ihbT m -> ihcAboveT m -> ihcBelowT m ->
  (ug : FinFun) (b : FinEl) ->
  Le (RANK (FunEl ug)) (suc m) -> Le (RANK b) (suc m) ->
  CoherentFun ug -> Coherent b ->
  Le (RANK (FunEl kg)) (suc (suc m)) -> Le (RANK (PiCode a0 fa)) (suc (suc m)) ->
  MB.finMem (suc (suc m)) (FunEl kg) (PiCode a0 fa) ->
  LeFunCode ug kg -> LeCode b (PiCode a0 fa) ->
  Sigma FinEl (\ u' -> Sigma FinEl (\ b' ->
    Pair (Le (RANK u') (suc m)) (Pair (Le (RANK b') (suc m))
    (Pair (LeCode (FunEl ug) u') (Pair (LeCode u' (FunEl kg))
    (Pair (LeCode b b') (Pair (LeCode b' (PiCode a0 fa))
    (Pair (MB.finMem (suc m) b' UCode) (MB.finMem (suc m) u' b')))))))))
coupleBelowFunEl m kg a0 fa iha ihb ihcA ihcB nil b bu bb cug cb bk ba memk lfugkg lba =
  exFalso cug
coupleBelowFunEl m kg a0 fa iha ihb ihcA ihcB (cons up ups) b bu bb cug cb bk ba memk lfugkg lba =
  goB b bb cb lba
  where
    ug = cons up ups
    ff_kg    = fst memk
    cohkg    = fst (snd memk)
    a0U-Sm   = fst (snd (snd memk))
    faAU-SSm = fst (snd (snd (snd memk)))
    ctfa     = snd (snd (snd (snd memk)))
    ctkg     = cft-from-cf kg cohkg
    rkg : Le (RANKFun kg) (suc m)
    rkg = bk
    ra0 : Le (RANK a0) (suc m)
    ra0 = Le-trans (RANK a0) (max (RANK a0) (RANKFun fa)) (suc m) (Le-max-l (RANK a0) (RANKFun fa)) ba
    rfa : Le (RANKFun fa) (suc m)
    rfa = Le-trans (RANKFun fa) (max (RANK a0) (RANKFun fa)) (suc m) (Le-max-r (RANK a0) (RANKFun fa)) ba
    a0Um : MB.finMem (suc m) a0 UCode
    a0Um = a0U-Sm
    a0UC : finMemC a0 UCode
    a0UC = fromStage (suc m) a0 UCode ra0 tt a0U-Sm
    ca0 : Coherent a0
    ca0 = coh-from-aU a0 a0UC
    faU : finMemAllUC fa a0
    faU = finMemAllU-shift (suc (suc m)) (suc (max (RANKFun fa) (RANK a0))) fa a0
            (Le-max-lub (RANKFun fa) (RANK a0) (suc m) rfa ra0)
            (Le-refl (suc (max (RANKFun fa) (RANK a0)))) faAU-SSm
    fmkg : finMemFunC kg a0 fa
    fmkg = finMemFun-shift (suc (suc m)) (suc (max (RANKFun kg) (max (RANK a0) (RANKFun fa)))) kg a0 fa
             (Le-max-lub (RANKFun kg) (max (RANK a0) (RANKFun fa)) (suc m) rkg
               (Le-max-lub (RANK a0) (RANKFun fa) (suc m) ra0 rfa))
             (Le-refl (suc (max (RANKFun kg) (max (RANK a0) (RANKFun fa))))) ff_kg
    rug : Le (RANKFun ug) m
    rug = bu

    out-type : (b'' : FinEl) -> Set
    out-type b'' =
      Sigma FinEl (\ u' -> Sigma FinEl (\ b' ->
        Pair (Le (RANK u') (suc m)) (Pair (Le (RANK b') (suc m))
        (Pair (LeCode (FunEl ug) u') (Pair (LeCode u' (FunEl kg))
        (Pair (LeCode b'' b') (Pair (LeCode b' (PiCode a0 fa))
        (Pair (MB.finMem (suc m) b' UCode) (MB.finMem (suc m) u' b')))))))))

    run : (b'' : FinEl) (fbL : FinFun) ->
      CoherentFunTail fbL -> LeFunCode fbL fa -> Le (RANKFun fbL) m ->
      (cacc : FinEl) -> Coherent cacc -> MB.finMem m cacc UCode -> Le (RANK cacc) m -> LeCode cacc a0 ->
      ((co : CBOut m a0 fa kg fbL cacc ug) -> LeCode b'' (PiCode (CBOut.dom co) (CBOut.fam co))) ->
      out-type b''
    run b'' fbL ctfbL lffbLfa rfbL cacc ccacc caccUm rcacc lcacca0 mkBB =
      mkSigma (FunEl (CBOut.kgg co))
       (mkSigma (PiCode (CBOut.dom co) (CBOut.fam co))
        (mkSigma (CBOut.rkgg co)
         (mkSigma (Le-max-lub (RANK (CBOut.dom co)) (RANKFun (CBOut.fam co)) m (CBOut.rdom co) (CBOut.rfam co))
          (mkSigma (mkLeFunCode-u0 kg ug (CBOut.kgg co) (CBOut.cftkgg co) cug (CBOut.alignUg co))
           (mkSigma (CBOut.lf-kgg-kg co)
            (mkSigma (mkBB co)
             (mkSigma (mkSigma (CBOut.dom-le-a0 co) (CBOut.lf-fam-fa co))
              (mkSigma (mkSigma (CBOut.domUm co) (mkSigma (CBOut.famU co) (CBOut.cftfam co)))
               (mkSigma ffkgg
                (mkSigma (CBOut.cftkgg co)
                 (mkSigma (CBOut.domUm co) (mkSigma (CBOut.famU co) (CBOut.cftfam co)))))))))))))
      where
        co = buildCB m a0 fa kg fbL iha ihb ihcA ihcB ctfa ctkg ca0 a0Um a0UC fmkg faU ra0 rfa rkg
               ctfbL lffbLfa rfbL cacc ccacc caccUm rcacc lcacca0 ug cug lfugkg rug
        famUC : finMemAllUC (CBOut.fam co) (CBOut.dom co)
        famUC = finMemAllU-shift (suc m) (suc (max (RANKFun (CBOut.fam co)) (RANK (CBOut.dom co))))
                  (CBOut.fam co) (CBOut.dom co)
                  (Le-max-lub (RANKFun (CBOut.fam co)) (RANK (CBOut.dom co)) m (CBOut.rfam co) (CBOut.rdom co))
                  (Le-refl (suc (max (RANKFun (CBOut.fam co)) (RANK (CBOut.dom co))))) (CBOut.famU co)
        ffkgg : MB.finMemFun (suc m) (CBOut.kgg co) (CBOut.dom co) (CBOut.fam co)
        ffkgg = mkFinMemFun m (CBOut.dom co) (CBOut.kgg co) (CBOut.fam co) (CBOut.cftfam co) (CBOut.cdom co)
                  famUC (CBOut.rfam co) (CBOut.rdom co) (CBOut.kgWit co)

    goB : (b'' : FinEl) -> Le (RANK b'') (suc m) -> Coherent b'' -> LeCode b'' (PiCode a0 fa) -> out-type b''
    goB Bot          rb'' cb' lba' =
      run Bot nil tt tt tt Bot tt (toStage m Bot UCode tt tt tt) tt tt (\ co -> tt)
    goB UCode        rb'' cb' ()
    goB (FunEl h)    rb'' cb' ()
    goB (PiCode b0 fb) rb'' cb' lba' =
      run (PiCode b0 fb) fb ctfb lffbfa rfb c'0 cc'0 c'0Um rc'0 lc'0a0
        (\ co -> mkSigma
                   (LeCode-trans b0 c'0 (CBOut.dom co) cb0 cc'0 (CBOut.cdom co) lc-b0c'0 (CBOut.cacc-le-dom co))
                   (mkLeFunCode-u0 fa fb (CBOut.fam co) (CBOut.cftfam co) ctfb (CBOut.alignFb co)))
      where
        cb0    = fst cb'
        ctfb   = snd cb'
        lb0a0  = fst lba'
        lffbfa = snd lba'
        rb0 : Le (RANK b0) m
        rb0 = Le-trans (RANK b0) (max (RANK b0) (RANKFun fb)) m (Le-max-l (RANK b0) (RANKFun fb)) rb''
        rfb : Le (RANKFun fb) m
        rfb = Le-trans (RANKFun fb) (max (RANK b0) (RANKFun fb)) m (Le-max-r (RANK b0) (RANKFun fb)) rb''
        ihbR  = ihb a0 UCode b0 ra0 tt rb0 cb0 a0Um lb0a0
        c'0   = fst ihbR
        rc'0  = fst (snd ihbR)
        lc-b0c'0 = fst (snd (snd ihbR))
        lc'0a0   = fst (snd (snd (snd ihbR)))
        c'0Um    = snd (snd (snd (snd ihbR)))
        cc'0  = coh-from-aU c'0 (fromStage m c'0 UCode rc'0 tt c'0Um)
