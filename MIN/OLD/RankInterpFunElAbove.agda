{-# OPTIONS --without-K --exact-split #-}
module MIN.OLD.RankInterpFunElAbove where

open import MIN.Domain.Basic
open import MIN.Domain.Order
open import MIN.Domain.MemStage
open import MIN.Domain.MemProps using ( finMem-upward ; EvalFun-in-UCode )
open import MIN.Domain.MemUnfold using ( FinMem-coh-u )
open import MIN.Model.Selection
  using ( Selection ; selectionBelow ; Selection-le-EvalFun ; Coherent-Selection
        ; Coherent-Selection-val ; EvalFun-le-graph ; Edge ; EdgeIn )
open import MIN.OLD.RankInterpFunEl
  using ( EdgeOut ; ihaT ; ihbT ; toStage ; fromStage ; efRank ; LeCode-NotBot
        ; Selection-RANK-u' ; edge-le )

-- EvalFun f x <= EvalFun f y  via a selection key wSel <= x with EvalFun f x = EvalFun f wSel,
-- when wSel <= y.  Returns LeCode (EvalFun fn x) (EvalFun fn y).
sel-preserve : (fn : FinFun) (x y wSel vSel : FinEl) ->
  CoherentFunTail fn -> Coherent wSel -> Coherent y ->
  Selection fn wSel vSel -> Eq (EvalFun fn x) vSel -> LeCode wSel y ->
  LeCode (EvalFun fn x) (EvalFun fn y)
sel-preserve fn x y wSel vSel cfn cw cy sel eqv lewy =
  let le1 : LeCode vSel (EvalFun fn wSel)
      le1 = Selection-le-EvalFun fn sel (LeFunCode-refl fn cfn) cfn cfn cw
      cvSel = Coherent-Selection-val sel cfn
      cefw  = Coherent-EvalFun fn wSel cfn cw
      cefy  = Coherent-EvalFun fn y cfn cy
      le2 : LeCode (EvalFun fn wSel) (EvalFun fn y)
      le2 = EvalFun-mon-arg fn wSel y lewy cfn cw cy
      le1' : LeCode (EvalFun fn x) (EvalFun fn wSel)
      le1' = Eq-transport (\ z -> LeCode z (EvalFun fn wSel)) (Eq-sym eqv) le1
  in LeCode-trans (EvalFun fn x) (EvalFun fn wSel) (EvalFun fn y)
       (Eq-transport Coherent (Eq-sym eqv) cvSel) cefw cefy le1' le2

interpEdgeAbove : (m : Nat) (g : FinFun) (b : FinEl) (f : FinFun) (h : FinFun) ->
  ihaT m -> ihbT m ->
  CoherentFunTail g -> CoherentFunTail f -> CoherentFunTail h ->
  finMemAllUC f b -> LeFunCode g h ->
  Le (RANK b) m -> Le (RANKFun f) m -> Le (RANKFun h) m ->
  (ka ca : FinEl) -> EdgeIn (mkSigma ka ca) g ->
  MB.finMem (suc m) ka b -> MB.finMem (suc m) ca (EvalFun f ka) ->
  Coherent ka -> Coherent ca -> NotBot ca ->
  Le (RANK ka) (suc m) -> Le (RANK ca) (suc m) ->
  EdgeOut m h b f ka ca
interpEdgeAbove m g b f h iha ihb ctg ctf cth fab lgh rb rf rh
                ka ca einKC kab caEf cka cca nbca rka rca =
  record
    { ekey = ua ; eval = va ; rkey = rua ; rval = rva
    ; keyb = uab ; valef = vaEfua-s ; key-le-j = ua-le-ka
    ; d-le-val = ca-le-va ; val-le-g = va-le-Hua
    ; ckey = cua ; cval = cva ; nbval = LeCode-NotBot ca va nbca ca-le-va }
  where
    rbS : Le (RANK b) (suc m)
    rbS = Le-trans (RANK b) m (suc m) rb (Le-suc m m (Le-refl m))
    -- f / h selections at ka
    sbf = selectionBelow f ka ctf cka
    fSel = fst sbf ; vSelf = fst (snd sbf)
    selF = fst (snd (snd sbf)) ; fSel-le-ka = fst (snd (snd (snd sbf)))
    eqF = snd (snd (snd (snd sbf)))            -- Eq (EvalFun f ka) vSelf
    cfSel = Coherent-Selection selF ctf
    sbh = selectionBelow h ka cth cka
    hSel = fst sbh ; vSelh = fst (snd sbh)
    selH = fst (snd (snd sbh)) ; hSel-le-ka = fst (snd (snd (snd sbh)))
    eqH = snd (snd (snd (snd sbh)))            -- Eq (EvalFun h ka) vSelh
    chSel = Coherent-Selection selH cth
    -- seed = Sup fSel hSel
    comp-seed = LeCode-Comp fSel hSel ka cka fSel-le-ka hSel-le-ka
    seed = Sup fSel hSel
    cseed = Coherent-Sup fSel hSel comp-seed cfSel chSel
    seed-le-ka = LeCode-Sup-lub fSel hSel ka fSel-le-ka hSel-le-ka
    rfSel = Le-trans (RANK fSel) (RANKFun f) m (Selection-RANK-u' selF) rf
    rhSel = Le-trans (RANK hSel) (RANKFun h) m (Selection-RANK-u' selH) rh
    rseed = Le-trans (RANK seed) (max (RANK fSel) (RANK hSel)) m
              (RANK-Sup fSel hSel) (Le-max-lub (RANK fSel) (RANK hSel) m rfSel rhSel)
    -- ua = ihb ka b seed : reduce key, preserve both selections
    ihbR = ihb ka b seed rka rb rseed cseed kab seed-le-ka
    ua = fst ihbR
    rua = fst (snd ihbR)
    seed-le-ua = fst (snd (snd ihbR))          -- LeCode seed ua
    ua-le-ka = fst (snd (snd (snd ihbR)))      -- LeCode ua ka
    uab = snd (snd (snd (snd ihbR)))           -- MB.finMem m ua b
    cua = FinMem-coh-u ua b (fromStage m ua b rua rb uab)
    fSel-le-ua = LeCode-trans fSel seed ua cfSel cseed cua
                   (LeCode-Sup-left fSel hSel comp-seed cfSel chSel) seed-le-ua
    hSel-le-ua = LeCode-trans hSel seed ua chSel cseed cua
                   (LeCode-Sup-right fSel hSel comp-seed cfSel chSel) seed-le-ua
    -- EvalFun f ka <= EvalFun f ua  (f-selection preserved)
    ef-ka-le-ua = sel-preserve f ka ua fSel vSelf ctf cfSel cua selF eqF fSel-le-ua
    -- ca : EvalFun f ua  (upward, type grows)
    r-ef-ua = efRank f ua m rf
    efU-ua = EvalFun-in-UCode f ua b ctf cua fab
    caEf-c = fromStage (suc m) ca (EvalFun f ka) rca
               (Le-trans (RANK (EvalFun f ka)) m (suc m) (efRank f ka m rf) (Le-suc m m (Le-refl m)))
               caEf
    caEfua-c = finMem-upward ca (EvalFun f ka) (EvalFun f ua) ef-ka-le-ua
                 (Coherent-EvalFun f ka ctf cka) (Coherent-EvalFun f ua ctf cua) caEf-c efU-ua
    -- ca <= EvalFun h ua
    ca-le-Gka = edge-le (mkSigma ka ca) g ka ctg einKC cka cca (LeCode-refl ka cka)
    Gka-le-Hka = EvalFun-le-graph g h ka lgh ctg cth cka
    Hka-le-Hua = sel-preserve h ka ua hSel vSelh cth chSel cua selH eqH hSel-le-ua
    c-Gka = Coherent-EvalFun g ka ctg cka
    c-Hka = Coherent-EvalFun h ka cth cka
    c-Hua = Coherent-EvalFun h ua cth cua
    ca-le-Hka = LeCode-trans ca (EvalFun g ka) (EvalFun h ka) cca c-Gka c-Hka ca-le-Gka Gka-le-Hka
    ca-le-Hua = LeCode-trans ca (EvalFun h ka) (EvalFun h ua) cca c-Hka c-Hua ca-le-Hka Hka-le-Hua
    -- va = iha ca (EvalFun f ua) (EvalFun h ua) : lift ca up, typed EvalFun f ua
    caEfua-s = toStage (suc m) ca (EvalFun f ua) rca
                 (Le-suc (RANK (EvalFun f ua)) m r-ef-ua) caEfua-c
    r-eh-ua = efRank h ua m rh
    ihaR = iha ca (EvalFun f ua) (EvalFun h ua) rca r-ef-ua r-eh-ua c-Hua caEfua-s ca-le-Hua
    va = fst ihaR
    rva = fst (snd ihaR)
    ca-le-va = fst (snd (snd ihaR))            -- LeCode ca va
    va-le-Hua = fst (snd (snd (snd ihaR)))     -- LeCode va (EvalFun h ua)
    vaEfua-s = snd (snd (snd (snd ihaR)))      -- MB.finMem m va (EvalFun f ua)
    cva = FinMem-coh-u va (EvalFun f ua) (fromStage m va (EvalFun f ua) rva r-ef-ua vaEfua-s)

------------------------------------------------------------------------
-- The g''-builder over g (the typed lower bound), upper bound h.
------------------------------------------------------------------------

open import MIN.OLD.RankInterpFunEl
  using ( BuildOut ; mkCoherentWith ; mkLeFunCode-u0 ; funelBelow )
open import MIN.Domain.MemShift using ( finMemFun-shift ; finMemAllU-shift ; finMem-shift )
open import MIN.Domain.MemUnfold using ( coh-from-aU )
open import MIN.Model.Selection using ( here ; there )

buildG''A : (m : Nat) (g : FinFun) (b : FinEl) (f : FinFun) (h : FinFun) ->
  ihaT m -> ihbT m -> CoherentFunTail g -> CoherentFunTail f -> CoherentFunTail h ->
  finMemAllUC f b -> Le (RANK b) m -> Le (RANKFun f) m -> Le (RANKFun h) m ->
  LeFunCode g h ->
  (gs : FinFun) -> CoherentFunTail gs -> MB.finMemFun (suc (suc m)) gs b f ->
  Le (RANKFun gs) (suc m) -> ((e : Edge) -> EdgeIn e gs -> EdgeIn e g) ->
  BuildOut m h b f gs
buildG''A m g b f h iha ihb ctg ctf cth fab rb rf rh lgh nil ctgs fmgs rgs wk =
  record { gp = nil ; rkgp = tt ; ffgp = tt ; lfgpg = tt ; cftgp = tt
         ; ginv = \ { q () } ; align = \ { e () } }
buildG''A m g b f h iha ihb ctg ctf cth fab rb rf rh lgh (cons p ps) ctgs fmgs rgs wk =
  record
    { gp    = cons (mkSigma uj vj) gpp
    ; rkgp  = Le-max-lub (RANK uj) (max (RANK vj) (RANKFun gpp)) m
                (EdgeOut.rkey eo)
                (Le-max-lub (RANK vj) (RANKFun gpp) m (EdgeOut.rval eo) (BuildOut.rkgp ih))
    ; ffgp  = mkSigma (mkSigma (EdgeOut.keyb eo) (EdgeOut.valef eo)) (BuildOut.ffgp ih)
    ; lfgpg = mkSigma (EdgeOut.val-le-g eo) (BuildOut.lfgpg ih)
    ; cftgp = record
        { key-coh  = EdgeOut.ckey eo
        ; val-coh  = EdgeOut.cval eo
        ; val-nbot = EdgeOut.nbval eo
        ; compat   = mkCoherentWith h (mkSigma uj vj) gpp cth
                       (EdgeOut.ckey eo) (EdgeOut.val-le-g eo) (BuildOut.ginv ih)
        ; tail-coh = BuildOut.cftgp ih }
    ; ginv  = \ { q here        -> mkSigma (EdgeOut.ckey eo) (EdgeOut.val-le-g eo)
                ; q (there ein') -> BuildOut.ginv ih q ein' }
    ; align = \ { e here ->
                    mkSigma (mkSigma uj vj)
                      (mkSigma here (mkSigma (EdgeOut.key-le-j eo)
                        (mkSigma (EdgeOut.d-le-val eo) (EdgeOut.cval eo))))
                ; e (there ein') ->
                    let r = BuildOut.align ih e ein'
                    in mkSigma (fst r) (mkSigma (there (fst (snd r))) (snd (snd r))) } }
  where
    rka = Le-trans (RANK (fst p)) (RANKFun (cons p ps)) (suc m)
            (Le-max-l (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps))) rgs
    rca = Le-trans (RANK (snd p)) (RANKFun (cons p ps)) (suc m)
            (Le-trans (RANK (snd p)) (max (RANK (snd p)) (RANKFun ps)) (RANKFun (cons p ps))
              (Le-max-l (RANK (snd p)) (RANKFun ps))
              (Le-max-r (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps)))) rgs
    rps = Le-trans (RANKFun ps) (RANKFun (cons p ps)) (suc m)
            (Le-trans (RANKFun ps) (max (RANK (snd p)) (RANKFun ps)) (RANKFun (cons p ps))
              (Le-max-r (RANK (snd p)) (RANKFun ps))
              (Le-max-r (RANK (fst p)) (max (RANK (snd p)) (RANKFun ps)))) rgs
    eo  = interpEdgeAbove m g b f h iha ihb ctg ctf cth fab lgh rb rf rh
            (fst p) (snd p) (wk (mkSigma (fst p) (snd p)) here)
            (fst (fst fmgs)) (snd (fst fmgs))
            (CFTcons.key-coh ctgs) (CFTcons.val-coh ctgs) (CFTcons.val-nbot ctgs) rka rca
    uj  = EdgeOut.ekey eo
    vj  = EdgeOut.eval eo
    ih  = buildG''A m g b f h iha ihb ctg ctf cth fab rb rf rh lgh
            ps (CFTcons.tail-coh ctgs) (snd fmgs) rps (\ e ein -> wk e (there ein))
    gpp = BuildOut.gp ih

------------------------------------------------------------------------
-- Top-level entry: exactly the aboveS (FunEl g)(PiCode b f) clause type.
------------------------------------------------------------------------

exF : {A : Set} -> Empty -> A
exF ()

funelAbove : (m : Nat) (g : FinFun) (b : FinEl) (f : FinFun) -> ihaT m -> ihbT m ->
  (v : FinEl) ->
  Le (RANK (FunEl g)) (suc (suc m)) -> Le (RANK (PiCode b f)) (suc m) ->
  Le (RANK v) (suc m) -> Coherent v ->
  MB.finMem (suc (suc m)) (FunEl g) (PiCode b f) -> LeCode (FunEl g) v ->
  Sigma FinEl (\ w -> Pair (Le (RANK w) (suc m))
    (Pair (LeCode (FunEl g) w) (Pair (LeCode w v) (MB.finMem (suc m) w (PiCode b f)))))
funelAbove m nil b f iha ihb v by ba bv cv mem lyv = exF (fst (snd mem))
funelAbove m (cons gp0 gps) b f iha ihb v by ba bv cv mem lyv = dispatch v bv cv lyv
  where
    gg = cons gp0 gps
    ff_g  = fst mem
    cohg  = fst (snd mem)
    piDom = fst (snd (snd mem))
    faSS  = fst (snd (snd (snd mem)))
    ctf   = snd (snd (snd (snd mem)))
    ctg   = cohg
    rg : Le (RANKFun gg) (suc m)
    rg = by
    rb : Le (RANK b) m
    rb = Le-trans (RANK b) (max (RANK b) (RANKFun f)) m (Le-max-l (RANK b) (RANKFun f)) ba
    rf : Le (RANKFun f) m
    rf = Le-trans (RANKFun f) (max (RANK b) (RANKFun f)) m (Le-max-r (RANK b) (RANKFun f)) ba
    bU : finMemC b UCode
    bU = fromStage (suc m) b UCode (Le-suc (RANK b) m rb) tt piDom
    bUm : MB.finMem m b UCode
    bUm = toStage m b UCode rb tt bU
    bAU-S : Le (suc (max (RANKFun f) (RANK b))) (suc m)
    bAU-S = Le-max-lub (RANKFun f) (RANK b) m rf rb
    bAU-SS : Le (suc (max (RANKFun f) (RANK b))) (suc (suc m))
    bAU-SS = Le-suc (suc (max (RANKFun f) (RANK b))) (suc m) bAU-S
    faSm : MB.finMemAllU (suc m) f b
    faSm = finMemAllU-shift (suc (suc m)) (suc m) f b bAU-SS bAU-S faSS
    fab : finMemAllUC f b
    fab = finMemAllU-shift (suc (suc m)) (suc (max (RANKFun f) (RANK b))) f b bAU-SS
            (Le-refl (suc (max (RANKFun f) (RANK b)))) faSS

    dispatch : (v' : FinEl) -> Le (RANK v') (suc m) -> Coherent v' -> LeCode (FunEl gg) v' ->
      Sigma FinEl (\ w -> Pair (Le (RANK w) (suc m))
        (Pair (LeCode (FunEl gg) w) (Pair (LeCode w v') (MB.finMem (suc m) w (PiCode b f)))))
    dispatch Bot          bv' cv' ()
    dispatch UCode        bv' cv' ()
    dispatch (FunEl h)    bv' cv' lyv' =
      let cth = cft-from-cf h cv'
          bo  = buildG''A m gg b f h iha ihb ctg ctf cth fab rb rf bv' lyv'
                  gg ctg ff_g rg (\ e ein -> ein)
          gp  = BuildOut.gp bo
      in mkSigma (FunEl gp)
           (mkSigma (BuildOut.rkgp bo)
             (mkSigma (mkLeFunCode-u0 gg gg gp (BuildOut.cftgp bo) ctg (BuildOut.align bo))
               (mkSigma (BuildOut.lfgpg bo)
                 (mkSigma (BuildOut.ffgp bo)
                   (mkSigma (BuildOut.cftgp bo)
                     (mkSigma bUm (mkSigma faSm ctf)))))))
    dispatch (PiCode c k) bv' cv' ()
