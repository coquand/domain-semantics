{-# OPTIONS --without-K --exact-split #-}
------------------------------------------------------------------------
-- RankSandwichFam.agda  (MIN/ -- Pi + U fragment)
--
-- Compatibility of the assembled reduced family: two type-families both
-- below a coherent cap bf are CompFun-compatible.  This is what makes
-- the multi-edge reduced family CoherentFunTail (hence FamToU, hence a
-- valid type code) -- the last conceptual ingredient of typeShrink.
------------------------------------------------------------------------
module MIN.Domain.RankSandwichFam where

open import MIN.Domain.Basic
  using ( FinEl ; FinFun ; nil ; cons ; Pair ; Sigma ; mkSigma ; fst ; snd ; Top ; tt )
open import MIN.Domain.Order
  using ( Coherent ; CoherentFunTail ; EvalFun ; LeCode ; LeFunCode ; Sup
        ; Comp ; CompFun ; CompStepFun ; CFTcons
        ; Coherent-Sup ; Coherent-EvalFun ; EvalFun-mon-arg
        ; LeCode-Sup-left ; LeCode-Sup-right ; LeCode-Comp
        ; Comp-down ; Comp-sym )

------------------------------------------------------------------------
-- Comp of arguments gives Comp of EvalFun values (cap coherent).
------------------------------------------------------------------------
argComp-EvalFun : (bf : FinFun) (u v : FinEl) -> CoherentFunTail bf ->
  Coherent u -> Coherent v -> Comp u v ->
  Comp (EvalFun bf u) (EvalFun bf v)
argComp-EvalFun bf u v cbf cu cv cuv =
  LeCode-Comp (EvalFun bf u) (EvalFun bf v) (EvalFun bf w) cEbw bu-bw bv-bw
  where
    w    = Sup u v
    cw   = Coherent-Sup u v cuv cu cv
    u-w  = LeCode-Sup-left u v cuv cu cv
    v-w  = LeCode-Sup-right u v cuv cu cv
    cEbw = Coherent-EvalFun bf w cbf cw
    bu-bw = EvalFun-mon-arg bf u w u-w cbf cu cw
    bv-bw = EvalFun-mon-arg bf v w v-w cbf cv cw

------------------------------------------------------------------------
-- The new edge (u2,v2) [v2 <= EvalFun bf u2] is CompStepFun-compatible
-- with any family frest that is below the cap bf.
------------------------------------------------------------------------
compStep-cap : (u2 v2 : FinEl) (frest bf : FinFun) ->
  CoherentFunTail bf -> Coherent u2 -> Coherent v2 -> LeCode v2 (EvalFun bf u2) ->
  CoherentFunTail frest -> LeFunCode frest bf ->
  CompStepFun (mkSigma u2 v2) frest
compStep-cap u2 v2 nil bf cbf cu2 cv2 v2bf cfr lfr = tt
compStep-cap u2 v2 (cons t g) bf cbf cu2 cv2 v2bf cfr lfr =
  mkSigma stepStep
          (compStep-cap u2 v2 g bf cbf cu2 cv2 v2bf (CFTcons.tail-coh cfr) (snd lfr))
  where
    ck : Coherent (fst t)
    ck = CFTcons.key-coh cfr
    cT : Coherent (snd t)
    cT = CFTcons.val-coh cfr
    T-bf : LeCode (snd t) (EvalFun bf (fst t))
    T-bf = fst lfr
    stepStep : Comp u2 (fst t) -> Comp v2 (snd t)
    stepStep cu2k =
      Comp-sym (snd t) v2
        (Comp-down (snd t) (EvalFun bf (fst t)) v2 T-bf
          (Comp-sym v2 (EvalFun bf (fst t))
            (Comp-down v2 (EvalFun bf u2) (EvalFun bf (fst t)) v2bf
              (argComp-EvalFun bf u2 (fst t) cbf cu2 ck cu2k))))

------------------------------------------------------------------------
-- Hence CompFun {(u2,v2)} frest.
------------------------------------------------------------------------
compFun-cap : (u2 v2 : FinEl) (frest bf : FinFun) ->
  CoherentFunTail bf -> Coherent u2 -> Coherent v2 -> LeCode v2 (EvalFun bf u2) ->
  CoherentFunTail frest -> LeFunCode frest bf ->
  CompFun (cons (mkSigma u2 v2) nil) frest
compFun-cap u2 v2 frest bf cbf cu2 cv2 v2bf cfr lfr =
  mkSigma (compStep-cap u2 v2 frest bf cbf cu2 cv2 v2bf cfr lfr) tt

------------------------------------------------------------------------
-- Retype a type-family's keys to a larger domain (upward closure).
------------------------------------------------------------------------
open import MIN.Domain.MemStage using ( finMemC )
open import MIN.Domain.Membership using ( FinMemAllU )
open import MIN.Domain.MemProps using ( finMem-upward )
open import MIN.Domain.Basic using ( UCode )

finMemAllU-up : (g : FinFun) (d d' : FinEl) ->
  LeCode d d' -> Coherent d -> Coherent d' -> finMemC d' UCode ->
  FinMemAllU g d -> FinMemAllU g d'
finMemAllU-up nil d d' le cd cd' d'U mem = tt
finMemAllU-up (cons p ps) d d' le cd cd' d'U mem =
  mkSigma (mkSigma (finMem-upward (fst p) d d' le cd cd' (fst (fst mem)) d'U)
                   (snd (fst mem)))
          (finMemAllU-up ps d d' le cd cd' d'U (snd mem))

------------------------------------------------------------------------
-- append-monotonicity of LeFunCode (under a common cap / Sup).
------------------------------------------------------------------------
open import MIN.Domain.Basic using ( Eq ; Eq-sym ; Eq-transport )
open import MIN.Domain.Order
  using ( LeCode-trans ; comp-EvalFun ; EvalFun-append-eq ; append )

-- xf' = append xfr fe is below bf when both parts are.
lefun-append-bf : (g h bf : FinFun) ->
  LeFunCode g bf -> LeFunCode h bf -> LeFunCode (append g h) bf
lefun-append-bf nil        h bf lg lh = lh
lefun-append-bf (cons p ps) h bf lg lh =
  mkSigma (fst lg) (lefun-append-bf ps h bf (snd lg) lh)

-- g <= xfr  implies  g <= append xfr fe.
lefun-append-mono-L : (g xfr fe : FinFun) ->
  CoherentFunTail (append xfr fe) -> CompFun xfr fe ->
  CoherentFunTail xfr -> CoherentFunTail fe -> CoherentFunTail g ->
  LeFunCode g xfr -> LeFunCode g (append xfr fe)
lefun-append-mono-L nil xfr fe capp cxf cxfr cfe cg lg = tt
lefun-append-mono-L (cons p ps) xfr fe capp cxf cxfr cfe cg lg =
  mkSigma edge (lefun-append-mono-L ps xfr fe capp cxf cxfr cfe (CFTcons.tail-coh cg) (snd lg))
  where
    k = fst p
    ck = CFTcons.key-coh cg
    cExfr = Coherent-EvalFun xfr k cxfr ck
    cEfe  = Coherent-EvalFun fe  k cfe  ck
    cEapp = Coherent-EvalFun (append xfr fe) k capp ck
    xfr-app : LeCode (EvalFun xfr k) (EvalFun (append xfr fe) k)
    xfr-app = Eq-transport (\ z -> LeCode (EvalFun xfr k) z)
                (Eq-sym (EvalFun-append-eq xfr fe k cxf cxfr ck))
                (LeCode-Sup-left (EvalFun xfr k) (EvalFun fe k)
                  (comp-EvalFun xfr fe k cxf cxfr ck) cExfr cEfe)
    edge : LeCode (snd p) (EvalFun (append xfr fe) k)
    edge = LeCode-trans (snd p) (EvalFun xfr k) (EvalFun (append xfr fe) k)
             (CFTcons.val-coh cg) cExfr cEapp (fst lg) xfr-app

-- g <= fe  implies  g <= append xfr fe.
lefun-append-mono-R : (g xfr fe : FinFun) ->
  CoherentFunTail (append xfr fe) -> CompFun xfr fe ->
  CoherentFunTail xfr -> CoherentFunTail fe -> CoherentFunTail g ->
  LeFunCode g fe -> LeFunCode g (append xfr fe)
lefun-append-mono-R nil xfr fe capp cxf cxfr cfe cg lg = tt
lefun-append-mono-R (cons p ps) xfr fe capp cxf cxfr cfe cg lg =
  mkSigma edge (lefun-append-mono-R ps xfr fe capp cxf cxfr cfe (CFTcons.tail-coh cg) (snd lg))
  where
    k = fst p
    ck = CFTcons.key-coh cg
    cExfr = Coherent-EvalFun xfr k cxfr ck
    cEfe  = Coherent-EvalFun fe  k cfe  ck
    cEapp = Coherent-EvalFun (append xfr fe) k capp ck
    fe-app : LeCode (EvalFun fe k) (EvalFun (append xfr fe) k)
    fe-app = Eq-transport (\ z -> LeCode (EvalFun fe k) z)
               (Eq-sym (EvalFun-append-eq xfr fe k cxf cxfr ck))
               (LeCode-Sup-right (EvalFun xfr k) (EvalFun fe k)
                 (comp-EvalFun xfr fe k cxf cxfr ck) cExfr cEfe)
    edge : LeCode (snd p) (EvalFun (append xfr fe) k)
    edge = LeCode-trans (snd p) (EvalFun fe k) (EvalFun (append xfr fe) k)
             (CFTcons.val-coh cg) cEfe cEapp (fst lg) fe-app

------------------------------------------------------------------------
-- Multi-edge family builder: reduce the whole lower family af.
------------------------------------------------------------------------
open import MIN.Domain.Basic
  using ( Nat ; zero ; suc ; max ; Le ; Le-trans ; Le-max-l ; Le-max-r ; Bot )
open import MIN.Domain.Order
  using ( RANK ; RANKFun ; LeCode-refl ; LeCode-Sup-lub ; RANK-Sup ; RANK-append
        ; Le-max-lub ; CompFun-sym ; CoherentFunTail-append ; mkCFT )
open import MIN.Domain.MemProps using ( FinMem-Sup-element ; FinMemAllU-append-Sup )
open import MIN.Domain.MemUnfold using ( FinMem-coh-u ; FinMem-coh-a )
open import MIN.Domain.Membership using ( allU-to ; allU-from )
open import MIN.Domain.RankSandwichCore using ( SStmt ; SOut ; edgeCore ; EdgeOut )
open import MIN.Domain.FamU using ( FamToU ; build-h2 ; piU-intro )

record FamOut (m : Nat) (a0 b0 : FinEl) (bf : FinFun) (af : FinFun) : Set where
  constructor mkFamOut
  field
    fX0' : FinEl
    fXf' : FinFun
    f-cohx0' : Coherent fX0'
    f-x0'U   : finMemC fX0' UCode
    f-rkx0'  : Le (RANK fX0') m
    f-a0x0'  : LeCode a0 fX0'
    f-x0'b0  : LeCode fX0' b0
    f-keys   : FinMemAllU fXf' fX0'
    f-cohf   : CoherentFunTail fXf'
    f-rkf    : Le (RANKFun fXf') m
    f-af     : LeFunCode af fXf'
    f-bf     : LeFunCode fXf' bf

famBuild : (m : Nat) (ih : SStmt m)
  (x0 a0 b0 : FinEl) (xf bf : FinFun) ->
  Coherent x0 -> finMemC x0 UCode -> Le (RANK x0) (suc m) ->
  Coherent a0 -> Le (RANK a0) m -> LeCode a0 x0 ->
  Coherent b0 -> Le (RANK b0) m -> LeCode x0 b0 ->
  CoherentFunTail xf -> FinMemAllU xf x0 -> Le (RANKFun xf) (suc m) ->
  CoherentFunTail bf -> Le (RANKFun bf) m -> LeFunCode xf bf ->
  (af : FinFun) -> CoherentFunTail af -> Le (RANKFun af) m -> LeFunCode af xf ->
  FamOut m a0 b0 bf af
famBuild m ih x0 a0 b0 xf bf cx0 x0U rx0 ca0 ra0 a0x0 cb0 rb0 x0b0
         cxf allUxf rxf cbf rbf xfbf nil caf rraf afxf =
  mkFamOut x0* nil cohx0* x0*U rk-x0* a0-x0* x0*-b0 tt tt tt tt tt
  where
    dr    = ih a0 b0 Bot UCode x0 UCode ra0 rb0 tt tt rx0 tt
               ca0 cb0 tt tt cx0 tt a0x0 x0b0 tt tt x0U
    x0*   = fst dr
    z'    = fst (snd dr)
    drest = snd (snd dr)
    rk-x0* : Le (RANK x0*) m
    rk-x0* = fst drest
    a0-x0* : LeCode a0 x0*
    a0-x0* = fst (snd (snd drest))
    x0*-b0 : LeCode x0* b0
    x0*-b0 = fst (snd (snd (snd drest)))
    z'-U : LeCode z' UCode
    z'-U = fst (snd (snd (snd (snd (snd drest)))))
    x0*z' : finMemC x0* z'
    x0*z' = snd (snd (snd (snd (snd (snd drest)))))
    cz' : Coherent z'
    cz' = FinMem-coh-a x0* z' x0*z'
    x0*U : finMemC x0* UCode
    x0*U = finMem-upward x0* z' UCode z'-U cz' tt x0*z' tt
    cohx0* : Coherent x0*
    cohx0* = FinMem-coh-u x0* z' x0*z'
famBuild m ih x0 a0 b0 xf bf cx0 x0U rx0 ca0 ra0 a0x0 cb0 rb0 x0b0
         cxf allUxf rxf cbf rbf xfbf (cons uv rest) caf rraf afxf =
  mkFamOut x0' xf' cohx0' x0'U rk-x0' a0-x0' x0'-b0 keys cohf rkf af-xf' xf'-bf
  where
    u = fst uv ; v = snd uv
    cu = CFTcons.key-coh caf ; cv = CFTcons.val-coh caf ; nbv = CFTcons.val-nbot caf
    cohrest = CFTcons.tail-coh caf
    lev : LeCode v (EvalFun xf u)
    lev = fst afxf
    ru : Le (RANK u) m
    ru = Le-trans (RANK u) (RANKFun (cons uv rest)) m
           (Le-max-l (RANK u) (max (RANK v) (RANKFun rest))) rraf
    rv : Le (RANK v) m
    rv = Le-trans (RANK v) (RANKFun (cons uv rest)) m
           (Le-trans (RANK v) (max (RANK v) (RANKFun rest)) (RANKFun (cons uv rest))
             (Le-max-l (RANK v) (RANKFun rest))
             (Le-max-r (RANK u) (max (RANK v) (RANKFun rest)))) rraf
    rrest : Le (RANKFun rest) m
    rrest = Le-trans (RANKFun rest) (RANKFun (cons uv rest)) m
              (Le-trans (RANKFun rest) (max (RANK v) (RANKFun rest)) (RANKFun (cons uv rest))
                (Le-max-r (RANK v) (RANKFun rest))
                (Le-max-r (RANK u) (max (RANK v) (RANKFun rest)))) rraf
    rec = famBuild m ih x0 a0 b0 xf bf cx0 x0U rx0 ca0 ra0 a0x0 cb0 rb0 x0b0
                   cxf allUxf rxf cbf rbf xfbf rest cohrest rrest (snd afxf)
    x0'r = FamOut.fX0' rec ; xfr = FamOut.fXf' rec
    cohx0r = FamOut.f-cohx0' rec ; x0rU = FamOut.f-x0'U rec
    eo = edgeCore m ih x0 a0 b0 xf bf u v cx0 x0U rx0 ca0 ra0 a0x0 cb0 rb0 x0b0
                  cxf allUxf rxf cbf rbf xfbf cu ru cv rv nbv lev
    x0'e = EdgeOut.eX0' eo ; u2 = EdgeOut.eU2 eo ; v2 = EdgeOut.eV2 eo
    cohx0'e : Coherent x0'e
    cohx0'e = FinMem-coh-u x0'e UCode (EdgeOut.e-x0'U eo)
    bh = build-h2 x0'e u2 v2 u v bf
           (EdgeOut.e-u2x0' eo) (EdgeOut.e-v2U eo)
           (EdgeOut.e-cu2 eo) (EdgeOut.e-cv2 eo) (EdgeOut.e-nb-v2 eo)
           cu cv (EdgeOut.e-u2u eo) (EdgeOut.e-v-v2 eo) (EdgeOut.e-v2-bf eo)
    fe = cons (mkSigma u2 v2) nil
    famE : FamToU x0'e fe
    famE = fst bh
    cohfe : CoherentFunTail fe
    cohfe = FamToU.cohFam famE
    -- domain join
    comp-re = LeCode-Comp x0'r x0'e b0 cb0 (FamOut.f-x0'b0 rec) (EdgeOut.e-x0'-b0 eo)
    x0' = Sup x0'r x0'e
    cohx0' : Coherent x0'
    cohx0' = Coherent-Sup x0'r x0'e comp-re cohx0r cohx0'e
    x0'U : finMemC x0' UCode
    x0'U = FinMem-Sup-element x0'r x0'e UCode comp-re tt x0rU (EdgeOut.e-x0'U eo)
    rk-x0' : Le (RANK x0') m
    rk-x0' = Le-trans (RANK x0') (max (RANK x0'r) (RANK x0'e)) m (RANK-Sup x0'r x0'e)
               (Le-max-lub (RANK x0'r) (RANK x0'e) m (FamOut.f-rkx0' rec) (EdgeOut.e-rk-x0' eo))
    a0-x0' : LeCode a0 x0'
    a0-x0' = LeCode-trans a0 x0'r x0' ca0 cohx0r cohx0' (FamOut.f-a0x0' rec)
               (LeCode-Sup-left x0'r x0'e comp-re cohx0r cohx0'e)
    x0'-b0 : LeCode x0' b0
    x0'-b0 = LeCode-Sup-lub x0'r x0'e b0 (FamOut.f-x0'b0 rec) (EdgeOut.e-x0'-b0 eo)
    -- family join: xf' = append xfr fe
    xf' = append xfr fe
    compxffe : CompFun xfr fe
    compxffe = CompFun-sym fe xfr
                 (compFun-cap u2 v2 xfr bf cbf (EdgeOut.e-cu2 eo) (EdgeOut.e-cv2 eo)
                   (EdgeOut.e-v2-bf eo) (FamOut.f-cohf rec) (FamOut.f-bf rec))
    cohf : CoherentFunTail xf'
    cohf = CoherentFunTail-append xfr fe (FamOut.f-cohf rec) cohfe compxffe
    keys : FinMemAllU xf' x0'
    keys = allU-from xf' x0'
             (FinMemAllU-append-Sup x0'r x0'e xfr fe comp-re cohx0r cohx0'e x0rU
               (EdgeOut.e-x0'U eo) (FamOut.f-cohf rec) cohfe
               (allU-to xfr x0'r (FamOut.f-keys rec))
               (allU-to fe x0'e (FamToU.keysInA famE)))
    rk-fe : Le (RANKFun fe) m
    rk-fe = Le-max-lub (RANK u2) (max (RANK v2) zero) m (EdgeOut.e-rk-u2 eo)
              (Le-max-lub (RANK v2) zero m (EdgeOut.e-rk-v2 eo) tt)
    rkf : Le (RANKFun xf') m
    rkf = Le-trans (RANKFun xf') (max (RANKFun xfr) (RANKFun fe)) m (RANK-append xfr fe)
            (Le-max-lub (RANKFun xfr) (RANKFun fe) m (FamOut.f-rkf rec) rk-fe)
    coh-uvnil : CoherentFunTail (cons uv nil)
    coh-uvnil = mkCFT cu cv nbv tt tt
    af-xf' : LeFunCode (cons uv rest) xf'
    af-xf' = mkSigma
               (fst (lefun-append-mono-R (cons uv nil) xfr fe cohf compxffe
                       (FamOut.f-cohf rec) cohfe coh-uvnil (fst (snd bh))))
               (lefun-append-mono-L rest xfr fe cohf compxffe
                  (FamOut.f-cohf rec) cohfe cohrest (FamOut.f-af rec))
    xf'-bf : LeFunCode xf' bf
    xf'-bf = lefun-append-bf xfr fe bf (FamOut.f-bf rec) (snd (snd bh))

------------------------------------------------------------------------
-- General type-code shrink: x = PiCode x0 xf : U in [PiCode a0 af, PiCode b0 bf]
-- reduces to x' = PiCode x0' xf' : U, rank <= suc m.
------------------------------------------------------------------------
open import MIN.Domain.FamU using ( mkFamToU )
open import MIN.Domain.Basic using ( PiCode )

typeShrink : (m : Nat) (ih : SStmt m)
  (x0 a0 b0 : FinEl) (xf bf af : FinFun) ->
  Coherent x0 -> finMemC x0 UCode -> Le (RANK x0) (suc m) ->
  Coherent a0 -> Le (RANK a0) m -> LeCode a0 x0 ->
  Coherent b0 -> Le (RANK b0) m -> LeCode x0 b0 ->
  CoherentFunTail xf -> FinMemAllU xf x0 -> Le (RANKFun xf) (suc m) ->
  CoherentFunTail bf -> Le (RANKFun bf) m -> LeFunCode xf bf ->
  CoherentFunTail af -> Le (RANKFun af) m -> LeFunCode af xf ->
  Sigma FinEl (\ x' ->
    Pair (finMemC x' UCode)
    (Pair (Le (RANK x') (suc m))
    (Pair (LeCode (PiCode a0 af) x') (LeCode x' (PiCode b0 bf)))))
typeShrink m ih x0 a0 b0 xf bf af
  cx0 x0U rx0 ca0 ra0 a0x0 cb0 rb0 x0b0 cxf allUxf rxf cbf rbf xfbf caf rraf afxf =
  mkSigma (PiCode x0' xf')
    (mkSigma x'U (mkSigma rk-x' (mkSigma a-x' x'-b)))
  where
    fo = famBuild m ih x0 a0 b0 xf bf cx0 x0U rx0 ca0 ra0 a0x0 cb0 rb0 x0b0
                  cxf allUxf rxf cbf rbf xfbf af caf rraf afxf
    x0' = FamOut.fX0' fo ; xf' = FamOut.fXf' fo
    x'U : finMemC (PiCode x0' xf') UCode
    x'U = piU-intro x0' xf' (FamOut.f-x0'U fo)
            (mkFamToU (FamOut.f-keys fo) (FamOut.f-cohf fo))
    rk-x' : Le (RANK (PiCode x0' xf')) (suc m)
    rk-x' = Le-max-lub (RANK x0') (RANKFun xf') m (FamOut.f-rkx0' fo) (FamOut.f-rkf fo)
    a-x' : LeCode (PiCode a0 af) (PiCode x0' xf')
    a-x' = mkSigma (FamOut.f-a0x0' fo) (FamOut.f-af fo)
    x'-b : LeCode (PiCode x0' xf') (PiCode b0 bf)
    x'-b = mkSigma (FamOut.f-x0'b0 fo) (FamOut.f-bf fo)
