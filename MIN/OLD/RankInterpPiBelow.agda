{-# OPTIONS --without-K --exact-split #-}
------------------------------------------------------------------------
-- RankInterpPiBelow.agda  (MIN/ -- Pi + U fragment)
--
-- PICODE-BELOW : the type-code  PiCode b f : UCode  shrink FROM BELOW.
--   x = PiCode b f : U is the rank-(suc(suc m)) UPPER bound; lift a lower
--   bound u = PiCode c k up to a typed rank-(suc m) code y = PiCode c' k'.
--
-- The domain SHRINKS (c <= c' <= b), so the family's sample keys must be
-- DOWNCAST b -> c' : this genuinely needs `fm-couple` (the 3rd InterpPack
-- field, here `ihc`).  Coordination of the single domain c' across all
-- sample keys is solved by THREADING the accumulating domain through
-- couple's own b'-output: couple(.., b_lower := cacc) returns bEdge >= cacc,
-- so the chain  c <= c'0 <= ... <= c'  is monotone and the final c' types
-- every (upcast) key -- NO Sup/join, NO compatibility lemmas.
------------------------------------------------------------------------
module MIN.OLD.RankInterpPiBelow where

open import MIN.Domain.Basic
open import MIN.Domain.Order
open import MIN.Domain.MemStage
open import MIN.Domain.MemShift using ( finMemAllU-shift )
open import MIN.Domain.MemProps using ( finMem-upward ; EvalFun-in-UCode )
open import MIN.Domain.MemUnfold using ( FinMem-coh-u ; coh-from-aU )
open import MIN.Domain.Membership using ( allU-from )
open import MIN.Model.Selection
  using ( Selection ; selectionBelow ; FinMemAllU-Selection ; Coherent-Selection
        ; Edge ; EdgeIn ; here ; there )
open import MIN.OLD.RankInterpFunEl
  using ( ihaT ; ihbT ; toStage ; fromStage ; efRank ; LeCode-NotBot
        ; Selection-RANK-u' ; edge-le ; GraphInv ; mkCoherentWith ; mkLeFunCode-u0 )
open import MIN.OLD.RankInterpFunElAbove using ( sel-preserve )

-- couple at the predecessor level m (the fm-couple field).
ihcT : Nat -> Set
ihcT m = (k a u b : FinEl) ->
  Le (RANK k) (suc m) -> Le (RANK a) (suc m) -> Le (RANK u) m -> Le (RANK b) m ->
  Coherent u -> Coherent b ->
  MB.finMem (suc m) a UCode -> MB.finMem (suc m) k a ->
  LeCode k u -> LeCode b a ->
  Sigma FinEl (\ u' -> Sigma FinEl (\ b' ->
    Pair (Le (RANK u') m) (Pair (Le (RANK b') m)
    (Pair (LeCode k u') (Pair (LeCode u' u)
    (Pair (LeCode b b') (Pair (LeCode b' a)
    (Pair (MB.finMem m b' UCode) (MB.finMem m u' b')))))))))

------------------------------------------------------------------------
-- the family builder over k (the lower bound), threading the domain.
------------------------------------------------------------------------

record BelowOut (m : Nat) (b : FinEl) (f : FinFun) (cacc : FinEl) (ks : FinFun) : Set where
  field
    dom         : FinEl
    rdom        : Le (RANK dom) m
    domUm       : MB.finMem m dom UCode
    cacc-le-dom : LeCode cacc dom
    dom-le-b    : LeCode dom b
    cdom        : Coherent dom
    fam         : FinFun
    rfam        : Le (RANKFun fam) m
    famU        : MB.finMemAllU (suc m) fam dom
    cftfam      : CoherentFunTail fam
    lf-fam-f    : LeFunCode fam f
    ginvF       : GraphInv f fam
    alignK      : (e : Edge) -> EdgeIn e ks ->
                    Sigma Edge (\ e' -> Pair (EdgeIn e' fam)
                      (Pair (LeCode (fst e') (fst e))
                        (Pair (LeCode (snd e) (snd e')) (Coherent (snd e')))))

buildBelow : (m : Nat) (b : FinEl) (f : FinFun) ->
  ihaT m -> ihbT m -> ihcT m ->
  CoherentFunTail f -> Coherent b -> finMemC b UCode -> MB.finMem (suc m) b UCode ->
  finMemAllUC f b -> Le (RANK b) (suc m) -> Le (RANKFun f) (suc m) ->
  (cacc : FinEl) -> Coherent cacc -> MB.finMem m cacc UCode ->
  Le (RANK cacc) m -> LeCode cacc b ->
  (ks : FinFun) -> CoherentFunTail ks -> LeFunCode ks f -> Le (RANKFun ks) m ->
  BelowOut m b f cacc ks
buildBelow m b f iha ihb ihc ctf cb bUC bUm fab rb rf cacc ccacc caccUm rcacc lcaccb
           nil ctks lf rks =
  record { dom = cacc ; rdom = rcacc ; domUm = caccUm
         ; cacc-le-dom = LeCode-refl cacc ccacc ; dom-le-b = lcaccb ; cdom = ccacc
         ; fam = nil ; rfam = tt ; famU = tt ; cftfam = tt
         ; lf-fam-f = tt ; ginvF = \ { q () } ; alignK = \ { e () } }
buildBelow m b f iha ihb ihc ctf cb bUC bUm fab rb rf cacc ccacc caccUm rcacc lcaccb
           (cons p ps) ctks lf rks =
  record
    { dom = dom ; rdom = BelowOut.rdom ih ; domUm = BelowOut.domUm ih
    ; cacc-le-dom = LeCode-trans cacc bEdge dom ccacc cbEdge cdom lcaccbEdge bEdge-le-dom
    ; dom-le-b = BelowOut.dom-le-b ih ; cdom = cdom
    ; fam = cons (mkSigma q' e') fam
    ; rfam = Le-max-lub (RANK q') (max (RANK e') (RANKFun fam)) m rq'
               (Le-max-lub (RANK e') (RANKFun fam) m re' (BelowOut.rfam ih))
    ; famU = mkSigma (mkSigma q'-dom e'U) (BelowOut.famU ih)
    ; cftfam = record
        { key-coh  = cq' ; val-coh = ce' ; val-nbot = LeCode-NotBot e e' nbe le-e-e'
        ; compat   = mkCoherentWith f (mkSigma q' e') fam ctf cq' le-e'-fq' (BelowOut.ginvF ih)
        ; tail-coh = BelowOut.cftfam ih }
    ; lf-fam-f = mkSigma le-e'-fq' (BelowOut.lf-fam-f ih)
    ; ginvF = \ { q here        -> mkSigma cq' le-e'-fq'
                ; q (there ein') -> BelowOut.ginvF ih q ein' }
    ; alignK = \ { e0 here ->
                     mkSigma (mkSigma q' e')
                       (mkSigma here (mkSigma le-q'-qk (mkSigma le-e-e' ce')))
                 ; e0 (there ein') ->
                     let r = BelowOut.alignK ih e0 ein'
                     in mkSigma (fst r) (mkSigma (there (fst (snd r))) (snd (snd r))) } }
  where
    qk  = fst p
    e   = snd p
    cqk = CFTcons.key-coh ctks
    ce  = CFTcons.val-coh ctks
    nbe = CFTcons.val-nbot ctks
    le-e-fqk = fst lf                              -- LeCode e (EvalFun f qk)
    rqk = Le-trans (RANK qk) (RANKFun (cons p ps)) m
            (Le-max-l (RANK qk) (max (RANK e) (RANKFun ps))) rks
    re  = Le-trans (RANK e) (RANKFun (cons p ps)) m
            (Le-trans (RANK e) (max (RANK e) (RANKFun ps)) (RANKFun (cons p ps))
              (Le-max-l (RANK e) (RANKFun ps))
              (Le-max-r (RANK qk) (max (RANK e) (RANKFun ps)))) rks
    rps = Le-trans (RANKFun ps) (RANKFun (cons p ps)) m
            (Le-trans (RANKFun ps) (max (RANK e) (RANKFun ps)) (RANKFun (cons p ps))
              (Le-max-r (RANK e) (RANKFun ps))
              (Le-max-r (RANK qk) (max (RANK e) (RANKFun ps)))) rks
    -- selection of f at qk
    sb    = selectionBelow f qk ctf cqk
    fSel  = fst sb
    vSel  = fst (snd sb)
    sel   = fst (snd (snd sb))
    fSel-le-qk = fst (snd (snd (snd sb)))          -- LeCode fSel qk
    eqV   = snd (snd (snd (snd sb)))               -- Eq (EvalFun f qk) vSel
    cfSel = Coherent-Selection sel ctf
    rfSel = Le-trans (RANK fSel) (RANKFun f) (suc m) (Selection-RANK-u' sel) rf
    fSelb-c : finMemC fSel b
    fSelb-c = FinMemAllU-Selection b sel (allU-from f b fab) ctf cb bUC
    fSelb : MB.finMem (suc m) fSel b
    fSelb = toStage (suc m) fSel b rfSel rb fSelb-c
    -- couple : downcast fSel : b  to  q' : bEdge   (cacc <= bEdge <= b),  fSel <= q' <= qk
    cpR = ihc fSel b qk cacc rfSel rb rqk rcacc cqk ccacc bUm fSelb fSel-le-qk lcaccb
    q'    = fst cpR
    bEdge = fst (snd cpR)
    rq'   = fst (snd (snd cpR))
    rbEdge = fst (snd (snd (snd cpR)))
    le-fSel-q' = fst (snd (snd (snd (snd cpR))))      -- LeCode fSel q'
    le-q'-qk   = fst (snd (snd (snd (snd (snd cpR)))))  -- LeCode q' qk
    lcaccbEdge = fst (snd (snd (snd (snd (snd (snd cpR))))))       -- LeCode cacc bEdge
    lbEdgeb    = fst (snd (snd (snd (snd (snd (snd (snd cpR)))))))  -- LeCode bEdge b
    bEdgeUm    = fst (snd (snd (snd (snd (snd (snd (snd (snd cpR))))))))  -- MB.finMem m bEdge UCode
    q'bEdge    = snd (snd (snd (snd (snd (snd (snd (snd (snd cpR))))))))  -- MB.finMem m q' bEdge
    cbEdge = coh-from-aU bEdge (fromStage m bEdge UCode rbEdge tt bEdgeUm)
    cq'    = FinMem-coh-u q' bEdge (fromStage m q' bEdge rq' rbEdge q'bEdge)
    -- recurse on ps with the grown domain bEdge
    ih  = buildBelow m b f iha ihb ihc ctf cb bUC bUm fab rb rf
            bEdge cbEdge bEdgeUm rbEdge lbEdgeb
            ps (CFTcons.tail-coh ctks) (snd lf) rps
    dom  = BelowOut.dom ih
    cdom = BelowOut.cdom ih
    bEdge-le-dom = BelowOut.cacc-le-dom ih          -- LeCode bEdge dom
    fam  = BelowOut.fam ih
    -- upcast q' : bEdge  ->  q' : dom
    q'-dom-c : finMemC q' dom
    q'-dom-c = finMem-upward q' bEdge dom bEdge-le-dom cbEdge cdom
                 (fromStage m q' bEdge rq' rbEdge q'bEdge)
                 (fromStage m dom UCode (BelowOut.rdom ih) tt (BelowOut.domUm ih))
    q'-dom : MB.finMem m q' dom
    q'-dom = toStage m q' dom rq' (BelowOut.rdom ih) q'-dom-c
    -- value : reduce EvalFun f q' (rank suc m) down to e' >= e at UCode
    r-fq' : Le (RANK (EvalFun f q')) (suc m)
    r-fq' = efRank f q' (suc m) rf
    c-fqk = Coherent-EvalFun f qk ctf cqk
    c-fq' = Coherent-EvalFun f q' ctf cq'
    fq'-le : LeCode (EvalFun f qk) (EvalFun f q')
    fq'-le = sel-preserve f qk q' fSel vSel ctf cfSel cq' sel eqV le-fSel-q'
    le-e-fq' : LeCode e (EvalFun f q')
    le-e-fq' = LeCode-trans e (EvalFun f qk) (EvalFun f q') ce c-fqk c-fq' le-e-fqk fq'-le
    fq'U-c = EvalFun-in-UCode f q' b ctf cq' fab
    fq'Um : MB.finMem (suc m) (EvalFun f q') UCode
    fq'Um = toStage (suc m) (EvalFun f q') UCode r-fq' tt fq'U-c
    ihbR = ihb (EvalFun f q') UCode e r-fq' tt re ce fq'Um le-e-fq'
    e'   = fst ihbR
    re'  = fst (snd ihbR)
    le-e-e'   = fst (snd (snd ihbR))               -- LeCode e e'
    le-e'-fq' = fst (snd (snd (snd ihbR)))         -- LeCode e' (EvalFun f q')
    e'Um = snd (snd (snd (snd ihbR)))              -- MB.finMem m e' UCode
    e'U  = e'Um
    ce'  = FinMem-coh-u e' UCode (fromStage m e' UCode re' tt e'Um)

------------------------------------------------------------------------
-- top-level : the belowS (PiCode b f) UCode (PiCode c k) clause.
------------------------------------------------------------------------

piBelow : (m : Nat) (b : FinEl) (f : FinFun) -> ihaT m -> ihbT m -> ihcT m ->
  (c : FinEl) (k : FinFun) ->
  Le (RANK (PiCode b f)) (suc (suc m)) -> Le (RANK (PiCode c k)) (suc m) ->
  Coherent (PiCode c k) ->
  MB.finMem (suc (suc m)) (PiCode b f) UCode -> LeCode (PiCode c k) (PiCode b f) ->
  Sigma FinEl (\ y -> Pair (Le (RANK y) (suc m))
    (Pair (LeCode (PiCode c k) y)
      (Pair (LeCode y (PiCode b f)) (MB.finMem (suc m) y UCode))))
piBelow m b f iha ihb ihc c k bx bu cu mem lux =
  mkSigma (PiCode dom fam)
    (mkSigma (Le-max-lub (RANK dom) (RANKFun fam) m (BelowOut.rdom bo) (BelowOut.rfam bo))
      (mkSigma (mkSigma lc-dom
                  (mkLeFunCode-u0 f k fam (BelowOut.cftfam bo) ctk (BelowOut.alignK bo)))
        (mkSigma (mkSigma (BelowOut.dom-le-b bo) (BelowOut.lf-fam-f bo))
          (mkSigma (BelowOut.domUm bo)
            (mkSigma (BelowOut.famU bo) (BelowOut.cftfam bo))))))
  where
    bUm  = fst mem                                 -- MB.finMem (suc m) b UCode
    fSS  = fst (snd mem)                           -- MB.finMemAllU (suc(suc m)) f b
    ctf  = snd (snd mem)
    cc   = fst cu                                  -- Coherent c
    ctk  = snd cu                                  -- CoherentFunTail k
    rb : Le (RANK b) (suc m)
    rb = Le-trans (RANK b) (max (RANK b) (RANKFun f)) (suc m) (Le-max-l (RANK b) (RANKFun f)) bx
    rf : Le (RANKFun f) (suc m)
    rf = Le-trans (RANKFun f) (max (RANK b) (RANKFun f)) (suc m) (Le-max-r (RANK b) (RANKFun f)) bx
    rc : Le (RANK c) m
    rc = Le-trans (RANK c) (max (RANK c) (RANKFun k)) m (Le-max-l (RANK c) (RANKFun k)) bu
    rkf : Le (RANKFun k) m
    rkf = Le-trans (RANKFun k) (max (RANK c) (RANKFun k)) m (Le-max-r (RANK c) (RANKFun k)) bu
    lcb  = fst lux                                 -- LeCode c b
    lkf  = snd lux                                 -- LeFunCode k f
    bUC : finMemC b UCode
    bUC = fromStage (suc m) b UCode rb tt bUm
    cb : Coherent b
    cb = coh-from-aU b bUC
    bAU-SS : Le (suc (max (RANKFun f) (RANK b))) (suc (suc m))
    bAU-SS = Le-max-lub (RANKFun f) (RANK b) (suc m) rf rb
    fab : finMemAllUC f b
    fab = finMemAllU-shift (suc (suc m)) (suc (max (RANKFun f) (RANK b))) f b
            bAU-SS (Le-refl (suc (max (RANKFun f) (RANK b)))) fSS
    -- seed domain  c'0 = lift c up toward b  (c <= c'0 <= b)
    ihbR  = ihb b UCode c rb tt rc cc bUm lcb
    c'0   = fst ihbR
    rc'0  = fst (snd ihbR)
    lcc'0 = fst (snd (snd ihbR))                   -- LeCode c c'0
    lc'0b = fst (snd (snd (snd ihbR)))             -- LeCode c'0 b
    c'0Um = snd (snd (snd (snd ihbR)))             -- MB.finMem m c'0 UCode
    cc'0  = coh-from-aU c'0 (fromStage m c'0 UCode rc'0 tt c'0Um)
    bo  = buildBelow m b f iha ihb ihc ctf cb bUC bUm fab rb rf
            c'0 cc'0 c'0Um rc'0 lc'0b k ctk lkf rkf
    dom = BelowOut.dom bo
    fam = BelowOut.fam bo
    lc-dom : LeCode c dom
    lc-dom = LeCode-trans c c'0 dom cc cc'0 (BelowOut.cdom bo) lcc'0 (BelowOut.cacc-le-dom bo)
