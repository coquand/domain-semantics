{-# OPTIONS --without-K --exact-split #-}
------------------------------------------------------------------------
-- RankInterpPiAbove.agda  (MIN/ -- Pi + U fragment)
--
-- PICODE-ABOVE : the type-code  PiCode b f : UCode  shrink FROM ABOVE.
--   y = PiCode b f : U is the rank-(suc(suc m)) LOWER bound; lower an
--   upper bound v = PiCode vd vf down to a typed rank-(suc m) code w.
--
-- The domain GROWS (b <= b'' <= vd), so the family's sample keys are
-- upcast b -> b'' for FREE via finMem-upward (a c0-member of a smaller
-- type is a member of the larger b''); NO recursive couple needed here.
-- This is the EASY type-code direction (the dual, PICODE-BELOW, shrinks
-- the domain and genuinely needs couple).
--
-- Structurally a funelAbove for a TYPE-FAMILY (finMemAllU, values : U)
-- instead of a function (finMemFun, values : EvalFun-typed).
------------------------------------------------------------------------
module MIN.OLD.RankInterpPiAbove where

open import MIN.Domain.Basic
open import MIN.Domain.Order
open import MIN.Domain.MemStage
open import MIN.Domain.MemProps using ( finMem-upward )
open import MIN.Domain.MemUnfold using ( FinMem-coh-u ; coh-from-aU )
open import MIN.Model.Selection
  using ( Selection ; selectionBelow ; Selection-le-EvalFun ; Coherent-Selection
        ; Coherent-Selection-val ; Edge ; EdgeIn ; here ; there )
open import MIN.OLD.RankInterpFunEl
  using ( ihaT ; ihbT ; toStage ; fromStage ; LeCode-NotBot ; efRank
        ; Selection-RANK-u' ; edge-le ; GraphInv ; mkCoherentWith )
open import MIN.OLD.RankInterpFunElAbove using ( sel-preserve )

------------------------------------------------------------------------
-- per-edge interpolation result (key typed by the GROWN domain b'',
-- value typed by UCode).
------------------------------------------------------------------------

record EdgeU (m : Nat) (b'' : FinEl) (vf : FinFun) (ka va : FinEl) : Set where
  field
    ekey eval : FinEl
    rkey      : Le (RANK ekey) m
    rval      : Le (RANK eval) m
    keyT      : MB.finMem m ekey b''               -- ekey : b''
    valU      : MB.finMem m eval UCode             -- eval : U
    key-le-ka : LeCode ekey ka
    va-le-val : LeCode va eval
    val-le-vf : LeCode eval (EvalFun vf ekey)
    ckey      : Coherent ekey
    cval      : Coherent eval
    nbval     : NotBot eval

-- the per-edge construction:  reduce the key ka (already upcast to b'')
-- DOWN to ekey, preserving the vf-selection so the value can be lifted.
interpEdgeU : (m : Nat) (b'' : FinEl) (vf : FinFun) ->
  ihaT m -> ihbT m ->
  CoherentFunTail vf -> Coherent b'' -> MB.finMem m b'' UCode ->
  Le (RANK b'') m -> Le (RANKFun vf) m ->
  (ka va : FinEl) -> Coherent ka -> Coherent va -> NotBot va ->
  Le (RANK ka) (suc m) -> Le (RANK va) (suc m) ->
  MB.finMem (suc m) ka b'' ->                       -- ka : b''  (already upcast)
  MB.finMem (suc m) va UCode ->                     -- va : U
  LeCode va (EvalFun vf ka) ->
  EdgeU m b'' vf ka va
interpEdgeU m b'' vf iha ihb ctvf cb'' b''U rb'' rvf ka va cka cva nbva rka rva kab vaU le-va-vf =
  record
    { ekey = ka' ; eval = va' ; rkey = rka' ; rval = rva'
    ; keyT = ka'b'' ; valU = va'U ; key-le-ka = ka'-le-ka
    ; va-le-val = va-le-va' ; val-le-vf = va'-le-vfka'
    ; ckey = cka' ; cval = cva' ; nbval = LeCode-NotBot va va' nbva va-le-va' }
  where
    rb''S : Le (RANK b'') (suc m)
    rb''S = Le-trans (RANK b'') m (suc m) rb'' (Le-suc m m (Le-refl m))
    -- selection of vf at ka
    sb    = selectionBelow vf ka ctvf cka
    vfSel = fst sb
    vSel  = fst (snd sb)
    sel   = fst (snd (snd sb))
    vfSel-le-ka = fst (snd (snd (snd sb)))         -- LeCode vfSel ka
    eqV   = snd (snd (snd (snd sb)))               -- Eq (EvalFun vf ka) vSel
    cvfSel = Coherent-Selection sel ctvf
    rvfSel = Le-trans (RANK vfSel) (RANKFun vf) m (Selection-RANK-u' sel) rvf
    -- ka' = reduce ka DOWN, keeping >= vfSel (preserves the vf value)
    ihbR  = ihb ka b'' vfSel rka rb'' rvfSel cvfSel kab vfSel-le-ka
    ka'   = fst ihbR
    rka'  = fst (snd ihbR)
    vfSel-le-ka' = fst (snd (snd ihbR))            -- LeCode vfSel ka'
    ka'-le-ka    = fst (snd (snd (snd ihbR)))      -- LeCode ka' ka
    ka'b''       = snd (snd (snd (snd ihbR)))      -- MB.finMem m ka' b''
    cka'  = FinMem-coh-u ka' b'' (fromStage m ka' b'' rka' rb'' ka'b'')
    -- EvalFun vf ka <= EvalFun vf ka'  (vf-selection preserved, vfSel <= ka')
    vf-ka-le-ka' = sel-preserve vf ka ka' vfSel vSel ctvf cvfSel cka' sel eqV vfSel-le-ka'
    c-vf-ka  = Coherent-EvalFun vf ka  ctvf cka
    c-vf-ka' = Coherent-EvalFun vf ka' ctvf cka'
    le-va-vfka' : LeCode va (EvalFun vf ka')
    le-va-vfka' = LeCode-trans va (EvalFun vf ka) (EvalFun vf ka') cva c-vf-ka c-vf-ka'
                    le-va-vf vf-ka-le-ka'
    r-vf-ka' : Le (RANK (EvalFun vf ka')) m
    r-vf-ka' = efRank vf ka' m rvf
    -- va' = lift va UP to [va, EvalFun vf ka'] at type UCode
    ihaR  = iha va UCode (EvalFun vf ka') rva tt r-vf-ka' c-vf-ka' vaU le-va-vfka'
    va'   = fst ihaR
    rva'  = fst (snd ihaR)
    va-le-va'    = fst (snd (snd ihaR))            -- LeCode va va'
    va'-le-vfka' = fst (snd (snd (snd ihaR)))      -- LeCode va' (EvalFun vf ka')
    va'U  = snd (snd (snd (snd ihaR)))             -- MB.finMem m va' UCode
    cva'  = FinMem-coh-u va' UCode (fromStage m va' UCode rva' tt va'U)

------------------------------------------------------------------------
-- the family builder over f  (producing f'' : finMemAllU b'').
------------------------------------------------------------------------

record BuildU (m : Nat) (b'' : FinEl) (vf : FinFun) (fs : FinFun) : Set where
  field
    fpp    : FinFun
    rkfpp  : Le (RANKFun fpp) m
    faU    : MB.finMemAllU (suc m) fpp b''
    cftU   : CoherentFunTail fpp
    ginvU  : GraphInv vf fpp
    alignU : (e : Edge) -> EdgeIn e fs ->
               Sigma Edge (\ e' -> Pair (EdgeIn e' fpp)
                 (Pair (LeCode (fst e') (fst e))
                   (Pair (LeCode (snd e) (snd e')) (Coherent (snd e')))))

buildKU : (m : Nat) (b b'' : FinEl) (vf : FinFun) ->
  ihaT m -> ihbT m ->
  CoherentFunTail vf -> Coherent b'' -> MB.finMem m b'' UCode -> finMemC b'' UCode ->
  Le (RANK b'') m -> Le (RANKFun vf) m ->
  Coherent b -> finMemC b UCode -> LeCode b b'' -> Le (RANK b) (suc m) ->
  (fs : FinFun) -> CoherentFunTail fs ->
  MB.finMemAllU (suc (suc m)) fs b -> LeFunCode fs vf -> Le (RANKFun fs) (suc m) ->
  BuildU m b'' vf fs
buildKU m b b'' vf iha ihb ctvf cb'' b''Um b''U rb'' rvf cb bU lbb'' rbS nil ctfs fam lf rfs =
  record { fpp = nil ; rkfpp = tt ; faU = tt ; cftU = tt
         ; ginvU = \ { q () } ; alignU = \ { e () } }
buildKU m b b'' vf iha ihb ctvf cb'' b''Um b''U rb'' rvf cb bU lbb'' rbS (cons p ps) ctfs fam lf rfs =
  record
    { fpp   = cons (mkSigma ka' va') fpp
    ; rkfpp = Le-max-lub (RANK ka') (max (RANK va') (RANKFun fpp)) m
                (EdgeU.rkey eo)
                (Le-max-lub (RANK va') (RANKFun fpp) m (EdgeU.rval eo) (BuildU.rkfpp ih))
    ; faU   = mkSigma (mkSigma (EdgeU.keyT eo) (EdgeU.valU eo)) (BuildU.faU ih)
    ; cftU  = record
        { key-coh  = EdgeU.ckey eo
        ; val-coh  = EdgeU.cval eo
        ; val-nbot = EdgeU.nbval eo
        ; compat   = mkCoherentWith vf (mkSigma ka' va') fpp ctvf
                       (EdgeU.ckey eo) (EdgeU.val-le-vf eo) (BuildU.ginvU ih)
        ; tail-coh = BuildU.cftU ih }
    ; ginvU = \ { q here        -> mkSigma (EdgeU.ckey eo) (EdgeU.val-le-vf eo)
                ; q (there ein') -> BuildU.ginvU ih q ein' }
    ; alignU = \ { e here ->
                     mkSigma (mkSigma ka' va')
                       (mkSigma here (mkSigma (EdgeU.key-le-ka eo)
                         (mkSigma (EdgeU.va-le-val eo) (EdgeU.cval eo))))
                 ; e (there ein') ->
                     let r = BuildU.alignU ih e ein'
                     in mkSigma (fst r) (mkSigma (there (fst (snd r))) (snd (snd r))) } }
  where
    ka  = fst p
    va  = snd p
    rka = Le-trans (RANK ka) (RANKFun (cons p ps)) (suc m)
            (Le-max-l (RANK ka) (max (RANK va) (RANKFun ps))) rfs
    rva = Le-trans (RANK va) (RANKFun (cons p ps)) (suc m)
            (Le-trans (RANK va) (max (RANK va) (RANKFun ps)) (RANKFun (cons p ps))
              (Le-max-l (RANK va) (RANKFun ps))
              (Le-max-r (RANK ka) (max (RANK va) (RANKFun ps)))) rfs
    rps = Le-trans (RANKFun ps) (RANKFun (cons p ps)) (suc m)
            (Le-trans (RANKFun ps) (max (RANK va) (RANKFun ps)) (RANKFun (cons p ps))
              (Le-max-r (RANK va) (RANKFun ps))
              (Le-max-r (RANK ka) (max (RANK va) (RANKFun ps)))) rfs
    kab  = fst (fst fam)                            -- MB.finMem (suc m) ka b
    vaU  = snd (fst fam)                            -- MB.finMem (suc m) va UCode
    cka  = CFTcons.key-coh ctfs
    cva  = CFTcons.val-coh ctfs
    nbva = CFTcons.val-nbot ctfs
    le-va-vf = fst lf                               -- LeCode va (EvalFun vf ka)
    -- upcast ka : b  ->  b''
    kab''-c : finMemC ka b''
    kab''-c = finMem-upward ka b b'' lbb'' cb cb''
                (fromStage (suc m) ka b rka rbS kab) b''U
    kab'' : MB.finMem (suc m) ka b''
    kab'' = toStage (suc m) ka b'' rka
              (Le-trans (RANK b'') m (suc m) rb'' (Le-suc m m (Le-refl m))) kab''-c
    eo  = interpEdgeU m b'' vf iha ihb ctvf cb'' b''Um rb'' rvf
            ka va cka cva nbva rka rva kab'' vaU le-va-vf
    ka' = EdgeU.ekey eo
    va' = EdgeU.eval eo
    ih  = buildKU m b b'' vf iha ihb ctvf cb'' b''Um b''U rb'' rvf cb bU lbb'' rbS
            ps (CFTcons.tail-coh ctfs) (snd fam) (snd lf) rps
    fpp = BuildU.fpp ih

------------------------------------------------------------------------
-- assemble : the aboveS (PiCode b f) UCode v clause.
------------------------------------------------------------------------

open import MIN.OLD.RankInterpFunEl using ( mkLeFunCode-u0 )

piAbove : (m : Nat) (b : FinEl) (f : FinFun) -> ihaT m -> ihbT m ->
  (v : FinEl) ->
  Le (RANK (PiCode b f)) (suc (suc m)) -> Le (RANK v) (suc m) -> Coherent v ->
  MB.finMem (suc (suc m)) (PiCode b f) UCode -> LeCode (PiCode b f) v ->
  Sigma FinEl (\ w -> Pair (Le (RANK w) (suc m))
    (Pair (LeCode (PiCode b f) w)
      (Pair (LeCode w v) (MB.finMem (suc m) w UCode))))
piAbove m b f iha ihb v by ba cv mem lyv = dispatch v ba cv lyv
  where
    bU     = fst mem                                -- MB.finMem (suc m) b UCode
    fam    = fst (snd mem)                          -- MB.finMemAllU (suc(suc m)) f b
    ctf    = snd (snd mem)                          -- CoherentFunTail f
    rb : Le (RANK b) (suc m)
    rb = Le-trans (RANK b) (max (RANK b) (RANKFun f)) (suc m) (Le-max-l (RANK b) (RANKFun f)) by
    rf : Le (RANKFun f) (suc m)
    rf = Le-trans (RANKFun f) (max (RANK b) (RANKFun f)) (suc m) (Le-max-r (RANK b) (RANKFun f)) by
    bUC : finMemC b UCode
    bUC = fromStage (suc m) b UCode rb tt bU
    cb : Coherent b
    cb = coh-from-aU b bUC

    dispatch : (v' : FinEl) -> Le (RANK v') (suc m) -> Coherent v' -> LeCode (PiCode b f) v' ->
      Sigma FinEl (\ w -> Pair (Le (RANK w) (suc m))
        (Pair (LeCode (PiCode b f) w)
          (Pair (LeCode w v') (MB.finMem (suc m) w UCode))))
    dispatch Bot          bv' cv' ()
    dispatch UCode        bv' cv' ()
    dispatch (FunEl h)    bv' cv' ()
    dispatch (PiCode vd vf) bv' cv' lyv' = mkSigma (PiCode b'' fpp)
      (mkSigma rw (mkSigma lkw (mkSigma lwv memw)))
      where
        cvd  = fst cv'
        ctvf = snd cv'
        bvd  = Le-trans (RANK vd) (max (RANK vd) (RANKFun vf)) m (Le-max-l (RANK vd) (RANKFun vf)) bv'
        rvf  = Le-trans (RANKFun vf) (max (RANK vd) (RANKFun vf)) m (Le-max-r (RANK vd) (RANKFun vf)) bv'
        lbvd = fst lyv'                              -- LeCode b vd
        lffvf = snd lyv'                             -- LeFunCode f vf
        -- b'' = lift b up toward vd
        ihaR = iha b UCode vd rb tt bvd cvd bU lbvd
        b''  = fst ihaR
        rb'' = fst (snd ihaR)
        lbb'' = fst (snd (snd ihaR))                 -- LeCode b b''
        lb''vd = fst (snd (snd (snd ihaR)))          -- LeCode b'' vd
        b''Um = snd (snd (snd (snd ihaR)))           -- MB.finMem m b'' UCode
        b''U : finMemC b'' UCode
        b''U = fromStage m b'' UCode rb'' tt b''Um
        cb'' = coh-from-aU b'' b''U
        bo   = buildKU m b b'' vf iha ihb ctvf cb'' b''Um b''U rb'' rvf cb bUC lbb'' rb
                 f ctf fam lffvf rf
        fpp  = BuildU.fpp bo
        rw : Le (RANK (PiCode b'' fpp)) (suc m)
        rw = Le-max-lub (RANK b'') (RANKFun fpp) m rb'' (BuildU.rkfpp bo)
        lkw : LeCode (PiCode b f) (PiCode b'' fpp)
        lkw = mkSigma lbb''
                (mkLeFunCode-u0 vf f fpp (BuildU.cftU bo) ctf (BuildU.alignU bo))
        lwv : LeCode (PiCode b'' fpp) (PiCode vd vf)
        lwv = mkSigma lb''vd (lf-fpp-vf fpp (BuildU.cftU bo) (BuildU.ginvU bo))
          where
            lf-fpp-vf : (gs : FinFun) -> CoherentFunTail gs -> GraphInv vf gs -> LeFunCode gs vf
            lf-fpp-vf nil         cg gi = tt
            lf-fpp-vf (cons q qs) cg gi =
              mkSigma (snd (gi q here))
                (lf-fpp-vf qs (CFTcons.tail-coh cg) (\ e ein -> gi e (there ein)))
        memw : MB.finMem (suc m) (PiCode b'' fpp) UCode
        memw = mkSigma b''Um (mkSigma (BuildU.faU bo) (BuildU.cftU bo))
