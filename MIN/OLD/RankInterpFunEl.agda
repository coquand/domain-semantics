{-# OPTIONS --without-K --exact-split #-}
module MIN.OLD.RankInterpFunEl where

open import MIN.Domain.Basic
open import MIN.Domain.Order
open import MIN.Domain.MemStage
open import MIN.Domain.MemShift using ( finMem-shift ; finMemFun-shift ; finMemAllU-shift )
open import MIN.Domain.MemProps using ( finMem-upward ; EvalFun-in-UCode )
open import MIN.Domain.MemUnfold using ( FinMem-coh-u ; coh-from-aU )
open import MIN.Domain.Membership using ( fun-from ; allU-from )
open import MIN.Model.Selection
  using ( Selection ; selectionBelow ; FinMem-Selection ; FinMem-Selection-codomain
        ; Selection-le-EvalFun ; Coherent-Selection ; Coherent-Selection-val
        ; singleton-selection ; CoherentFun-edge-key
        ; Edge ; EdgeIn ; here ; there )
open import MIN.Model.SelectionRank using ( Selection-RANK-u ; Selection-RANK-v )
import MIN.Domain.Rank as RankM

-- bridge between the (definitionally identical) Rank.RANK and Order.RANK
maxEq : {x x' y y' : Nat} -> Eq x x' -> Eq y y' -> Eq (max x y) (max x' y')
maxEq refl refl = refl

mutual
  rkEq : (x : FinEl) -> Eq (RankM.RANK x) (RANK x)
  rkEq Bot          = refl
  rkEq UCode        = refl
  rkEq (FunEl g)    = Eq-cong suc (rkFunEq g)
  rkEq (PiCode a f) = Eq-cong suc (maxEq (rkEq a) (rkFunEq f))

  rkFunEq : (g : FinFun) -> Eq (RankM.RANKFun g) (RANKFun g)
  rkFunEq nil         = refl
  rkFunEq (cons p ps) = maxEq (rkEq (fst p)) (maxEq (rkEq (snd p)) (rkFunEq ps))

Selection-RANK-u' : {g : FinFun} {u v : FinEl} ->
  Selection g u v -> Le (RANK u) (RANKFun g)
Selection-RANK-u' {g} {u} sel =
  Eq-transport (\ x -> Le x (RANKFun g)) (rkEq u)
    (Eq-transport (\ y -> Le (RankM.RANK u) y) (rkFunEq g) (Selection-RANK-u sel))

Selection-RANK-v' : {g : FinFun} {u v : FinEl} ->
  Selection g u v -> Le (RANK v) (RANKFun g)
Selection-RANK-v' {g} {u} {v} sel =
  Eq-transport (\ x -> Le x (RANKFun g)) (rkEq v)
    (Eq-transport (\ y -> Le (RankM.RANK v) y) (rkFunEq g) (Selection-RANK-v sel))

-- finMemC <-> staged shift wrappers (finMemC u a = MB.finMem (suc (max ..)) u a)
toStage : (k : Nat) (u a : FinEl) -> Le (RANK u) k -> Le (RANK a) k ->
  finMemC u a -> MB.finMem k u a
toStage k u a bu ba mem =
  finMem-shift (suc (max (RANK u) (RANK a))) k u a
    (Le-suc (RANK u) (max (RANK u) (RANK a)) (Le-max-l (RANK u) (RANK a)))
    (Le-suc (RANK a) (max (RANK u) (RANK a)) (Le-max-r (RANK u) (RANK a)))
    bu ba mem

fromStage : (k : Nat) (u a : FinEl) -> Le (RANK u) k -> Le (RANK a) k ->
  MB.finMem k u a -> finMemC u a
fromStage k u a bu ba mem =
  finMem-shift k (suc (max (RANK u) (RANK a))) u a bu ba
    (Le-suc (RANK u) (max (RANK u) (RANK a)) (Le-max-l (RANK u) (RANK a)))
    (Le-suc (RANK a) (max (RANK u) (RANK a)) (Le-max-r (RANK u) (RANK a)))
    mem

-- NotBot is upward closed under LeCode
LeCode-NotBot : (d v : FinEl) -> NotBot d -> LeCode d v -> NotBot v
LeCode-NotBot Bot          v            () le
LeCode-NotBot UCode        Bot          nb ()
LeCode-NotBot UCode        UCode        nb le = tt
LeCode-NotBot UCode        (FunEl h)    nb ()
LeCode-NotBot UCode        (PiCode b g) nb ()
LeCode-NotBot (FunEl g)    Bot          nb ()
LeCode-NotBot (FunEl g)    UCode        nb ()
LeCode-NotBot (FunEl g)    (FunEl h)    nb le = tt
LeCode-NotBot (FunEl g)    (PiCode b h) nb ()
LeCode-NotBot (PiCode a f) Bot          nb ()
LeCode-NotBot (PiCode a f) UCode        nb ()
LeCode-NotBot (PiCode a f) (FunEl h)    nb ()
LeCode-NotBot (PiCode a f) (PiCode b h) nb le = tt

-- RANK (EvalFun f w) <= m  (given RANKFun f <= m)
efRank : (f : FinFun) (w : FinEl) (m : Nat) -> Le (RANKFun f) m -> Le (RANK (EvalFun f w)) m
efRank f w m rf =
  let n = max (RANKFun f) (RANK w)
  in Le-trans (RANK (EvalFun f w)) (RANKFun f) m
       (Eq-transport (\ x -> Le (RANK x) (RANKFun f))
         (Eq-sym (ev-bridge n f w (Le-refl n))) (RANK-ev (suc n) f w))
       rf

------------------------------------------------------------------------
-- Per-edge interpolation result.
------------------------------------------------------------------------

record EdgeOut (m : Nat) (g : FinFun) (b : FinEl) (f : FinFun) (j d : FinEl) : Set where
  field
    ekey eval : FinEl
    rkey      : Le (RANK ekey) m
    rval      : Le (RANK eval) m
    keyb      : MB.finMem m ekey b
    valef     : MB.finMem m eval (EvalFun f ekey)
    key-le-j  : LeCode ekey j
    d-le-val  : LeCode d eval
    val-le-g  : LeCode eval (EvalFun g ekey)
    ckey      : Coherent ekey
    cval      : Coherent eval
    nbval     : NotBot eval

ihaT : Nat -> Set
ihaT m = (y a v : FinEl) ->
  Le (RANK y) (suc m) -> Le (RANK a) m -> Le (RANK v) m -> Coherent v ->
  MB.finMem (suc m) y a -> LeCode y v ->
  Sigma FinEl (\ w -> Pair (Le (RANK w) m)
    (Pair (LeCode y w) (Pair (LeCode w v) (MB.finMem m w a))))

ihbT : Nat -> Set
ihbT m = (x a u : FinEl) ->
  Le (RANK x) (suc m) -> Le (RANK a) m -> Le (RANK u) m -> Coherent u ->
  MB.finMem (suc m) x a -> LeCode u x ->
  Sigma FinEl (\ y -> Pair (Le (RANK y) m)
    (Pair (LeCode u y) (Pair (LeCode y x) (MB.finMem m y a))))

interpEdge : (m : Nat) (g : FinFun) (b : FinEl) (f : FinFun) ->
  ihaT m -> ihbT m ->
  CoherentFunTail g -> CoherentFunTail f ->
  finMemFunC g b f -> finMemAllUC f b ->
  Coherent b -> finMemC b UCode ->
  Le (RANKFun g) (suc m) -> Le (RANK b) m -> Le (RANKFun f) m ->
  (j d : FinEl) -> Coherent j -> Coherent d -> NotBot d ->
  Le (RANK j) m -> Le (RANK d) m -> LeCode d (EvalFun g j) ->
  EdgeOut m g b f j d
interpEdge m g b f iha ihb ctg ctf fmg fab cb bU rg rb rf j d cj cd nbd rj rd led =
  record
    { ekey = uj ; eval = vj ; rkey = ruj ; rval = rvj
    ; keyb = ujb ; valef = vjEfuj ; key-le-j = lujj
    ; d-le-val = le-d-vj ; val-le-g = vj-le-Guj
    ; ckey = cuj ; cval = cvj ; nbval = LeCode-NotBot d vj nbd le-d-vj }
  where
    rbS : Le (RANK b) (suc m)
    rbS = Le-trans (RANK b) m (suc m) rb (Le-suc m m (Le-refl m))
    -- canonical selection at j
    sb     = selectionBelow g j ctg cj
    uSel   = fst sb
    vSel   = fst (snd sb)
    sel    = fst (snd (snd sb))
    luSj   = fst (snd (snd (snd sb)))           -- LeCode uSel j
    eqEv   = snd (snd (snd (snd sb)))           -- Eq (EvalFun g j) vSel
    cuSel  = Coherent-Selection sel ctg
    cvSel  = Coherent-Selection-val sel ctg
    ruS    = Le-trans (RANK uSel) (RANKFun g) (suc m) (Selection-RANK-u' sel) rg
    rvS    = Le-trans (RANK vSel) (RANKFun g) (suc m) (Selection-RANK-v' sel) rg
    uSelb  = FinMem-Selection b f sel (fun-from g b f fmg) ctg cb bU
    vSelEf = FinMem-Selection-codomain b f sel (fun-from g b f fmg) ctg ctf (allU-from f b fab)
    r-ef-uSel : Le (RANK (EvalFun f uSel)) m
    r-ef-uSel = efRank f uSel m rf
    -- interpolate uSel up toward j  =>  uj  with  uSel <= uj <= j,  uj : b
    ihaR   = iha uSel b j ruS rb rj cj (toStage (suc m) uSel b ruS rbS uSelb) luSj
    uj     = fst ihaR
    ruj    = fst (snd ihaR)
    leSuj  = fst (snd (snd ihaR))               -- LeCode uSel uj
    lujj   = fst (snd (snd (snd ihaR)))         -- LeCode uj j
    ujb    = snd (snd (snd (snd ihaR)))         -- MB.finMem m uj b
    cuj    = FinMem-coh-u uj b (fromStage m uj b ruj rb ujb)
    r-ef-uj : Le (RANK (EvalFun f uj)) m
    r-ef-uj = efRank f uj m rf
    -- d <= vSel  (since EvalFun g j = vSel)
    d-le-vSel : LeCode d vSel
    d-le-vSel = Eq-transport (LeCode d) eqEv led
    -- reduce vSel down toward d  =>  vj : EvalFun f uSel,  d <= vj <= vSel
    ihbR   = ihb vSel (EvalFun f uSel) d rvS r-ef-uSel rd cd
               (toStage (suc m) vSel (EvalFun f uSel) rvS
                  (Le-trans (RANK (EvalFun f uSel)) m (suc m) r-ef-uSel (Le-suc m m (Le-refl m)))
                  vSelEf)
               d-le-vSel
    vj      = fst ihbR
    rvj     = fst (snd ihbR)
    le-d-vj = fst (snd (snd ihbR))              -- LeCode d vj
    le-vj-vSel = fst (snd (snd (snd ihbR)))     -- LeCode vj vSel
    vjEfuSel-s = snd (snd (snd (snd ihbR)))     -- MB.finMem m vj (EvalFun f uSel)
    cvj    = FinMem-coh-u vj (EvalFun f uSel) (fromStage m vj (EvalFun f uSel) rvj r-ef-uSel vjEfuSel-s)
    -- retype vj : EvalFun f uSel  ->  EvalFun f uj   (uSel <= uj)
    c-ef-uSel = Coherent-EvalFun f uSel ctf cuSel
    c-ef-uj   = Coherent-EvalFun f uj   ctf cuj
    ef-mono   = EvalFun-mon-arg f uSel uj leSuj ctf cuSel cuj    -- LeCode (EvalFun f uSel)(EvalFun f uj)
    efU-uj    = EvalFun-in-UCode f uj b ctf cuj fab
    vjEfuj-c  = finMem-upward vj (EvalFun f uSel) (EvalFun f uj) ef-mono c-ef-uSel c-ef-uj
                  (fromStage m vj (EvalFun f uSel) rvj r-ef-uSel vjEfuSel-s) efU-uj
    vjEfuj    = toStage m vj (EvalFun f uj) rvj r-ef-uj vjEfuj-c
    -- val-le-g :  vj <= EvalFun g uj
    cGuSel = Coherent-EvalFun g uSel ctg cuSel
    cGuj   = Coherent-EvalFun g uj   ctg cuj
    vSel-le-GuSel = Selection-le-EvalFun g sel (LeFunCode-refl g ctg) ctg ctg cuSel
                                                       -- LeCode vSel (EvalFun g uSel)
    GuSel-le-Guj  = EvalFun-mon-arg g uSel uj leSuj ctg cuSel cuj
    vSel-le-Guj   = LeCode-trans vSel (EvalFun g uSel) (EvalFun g uj)
                      cvSel cGuSel cGuj vSel-le-GuSel GuSel-le-Guj
    vj-le-Guj : LeCode vj (EvalFun g uj)
    vj-le-Guj = LeCode-trans vj vSel (EvalFun g uj) cvj cvSel cGuj le-vj-vSel vSel-le-Guj

------------------------------------------------------------------------
-- Helpers for the g'-builder.
------------------------------------------------------------------------

-- Comp p q  ->  Comp (EvalFun g p) (EvalFun g q)
Comp-EvalFun-arg : (g : FinFun) (p q : FinEl) ->
  CoherentFunTail g -> Coherent p -> Coherent q -> Comp p q ->
  Comp (EvalFun g p) (EvalFun g q)
Comp-EvalFun-arg g p q cg cp cq cpq =
  let cs  = Coherent-Sup p q cpq cp cq
      lp  = LeCode-Sup-left p q cpq cp cq
      lq  = LeCode-Sup-right p q cpq cp cq
      mep = EvalFun-mon-arg g p (Sup p q) lp cg cp cs
      meq = EvalFun-mon-arg g q (Sup p q) lq cg cq cs
      cgs = Coherent-EvalFun g (Sup p q) cg cs
  in LeCode-Comp (EvalFun g p) (EvalFun g q) (EvalFun g (Sup p q)) cgs mep meq

-- GraphInv g gp : every edge of gp has coherent key and value <= EvalFun g key.
GraphInv : FinFun -> FinFun -> Set
GraphInv g gp = (q : Edge) -> EdgeIn q gp ->
  Pair (Coherent (fst q)) (LeCode (snd q) (EvalFun g (fst q)))

-- build CoherentWith from GraphInv of the rest
mkCoherentWith : (g : FinFun) (e : Edge) (rest : FinFun) ->
  CoherentFunTail g -> Coherent (fst e) -> LeCode (snd e) (EvalFun g (fst e)) ->
  GraphInv g rest -> CoherentWith e rest
mkCoherentWith g e nil         cg ce le ginv = tt
mkCoherentWith g e (cons q qs) cg ce le ginv =
  mkSigma
    (\ comp-keys ->
       let cq     = fst (ginv q here)
           leq    = snd (ginv q here)
           cearg  = Comp-EvalFun-arg g (fst e) (fst q) cg ce cq comp-keys
           c1     = Comp-down (snd e) (EvalFun g (fst e)) (EvalFun g (fst q)) le cearg
           c2     = Comp-down (snd q) (EvalFun g (fst q)) (snd e) leq (Comp-sym (snd e) (EvalFun g (fst q)) c1)
       in Comp-sym (snd q) (snd e) c2)
    (mkCoherentWith g e qs cg ce le (\ q' ein -> ginv q' (there ein)))

------------------------------------------------------------------------
-- The g'-builder over u0.
------------------------------------------------------------------------

record BuildOut (m : Nat) (g : FinFun) (b : FinEl) (f : FinFun) (u0' : FinFun) : Set where
  field
    gp    : FinFun
    rkgp  : Le (RANKFun gp) m
    ffgp  : MB.finMemFun (suc m) gp b f
    lfgpg : LeFunCode gp g
    cftgp : CoherentFunTail gp
    ginv  : GraphInv g gp
    align : (e : Edge) -> EdgeIn e u0' ->
              Sigma Edge (\ e' -> Pair (EdgeIn e' gp)
                (Pair (LeCode (fst e') (fst e))
                  (Pair (LeCode (snd e) (snd e')) (Coherent (snd e')))))

buildG' : (m : Nat) (g : FinFun) (b : FinEl) (f : FinFun) ->
  ihaT m -> ihbT m -> CoherentFunTail g -> CoherentFunTail f ->
  finMemFunC g b f -> finMemAllUC f b -> Coherent b -> finMemC b UCode ->
  Le (RANKFun g) (suc m) -> Le (RANK b) m -> Le (RANKFun f) m ->
  (u0' : FinFun) -> CoherentFunTail u0' -> LeFunCode u0' g -> Le (RANKFun u0') m ->
  BuildOut m g b f u0'
buildG' m g b f iha ihb ctg ctf fmg fab cb bU rg rb rf nil ctu0 lfu0g ru0 =
  record { gp = nil ; rkgp = tt ; ffgp = tt ; lfgpg = tt ; cftgp = tt
         ; ginv = \ { q () } ; align = \ { e () } }
buildG' m g b f iha ihb ctg ctf fmg fab cb bU rg rb rf (cons p ps) ctu0 lfu0g ru0 =
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
        ; compat   = mkCoherentWith g (mkSigma uj vj) gpp ctg
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
    j  = fst p
    d  = snd p
    cj = CFTcons.key-coh ctu0
    cd = CFTcons.val-coh ctu0
    nbd = CFTcons.val-nbot ctu0
    led = fst lfu0g
    rj = Le-trans (RANK j) (RANKFun (cons p ps)) m
           (Le-max-l (RANK j) (max (RANK d) (RANKFun ps))) ru0
    rd = Le-trans (RANK d) (RANKFun (cons p ps)) m
           (Le-trans (RANK d) (max (RANK d) (RANKFun ps)) (RANKFun (cons p ps))
             (Le-max-l (RANK d) (RANKFun ps))
             (Le-max-r (RANK j) (max (RANK d) (RANKFun ps)))) ru0
    rps = Le-trans (RANKFun ps) (RANKFun (cons p ps)) m
            (Le-trans (RANKFun ps) (max (RANK d) (RANKFun ps)) (RANKFun (cons p ps))
              (Le-max-r (RANK d) (RANKFun ps))
              (Le-max-r (RANK j) (max (RANK d) (RANKFun ps)))) ru0
    eo  = interpEdge m g b f iha ihb ctg ctf fmg fab cb bU rg rb rf
            j d cj cd nbd rj rd led
    uj  = EdgeOut.ekey eo
    vj  = EdgeOut.eval eo
    ih  = buildG' m g b f iha ihb ctg ctf fmg fab cb bU rg rb rf
            ps (CFTcons.tail-coh ctu0) (snd lfu0g) rps
    gpp = BuildOut.gp ih

-- an edge's value is <= EvalFun gp x  whenever its key <= x
edge-le : (e' : Edge) (gp : FinFun) (x : FinEl) ->
  CoherentFunTail gp -> EdgeIn e' gp -> Coherent x -> Coherent (snd e') ->
  LeCode (fst e') x -> LeCode (snd e') (EvalFun gp x)
edge-le e' gp x cgp ein cx cv' lekx =
  let sel0 = singleton-selection e' gp ein
      sel  = Eq-transport (\ u -> Selection gp u (snd e')) (Sup-Bot-right (fst e'))
               (Eq-transport (\ v -> Selection gp (Sup (fst e') Bot) v)
                 (Sup-Bot-right (snd e')) sel0)
      ck   = CoherentFun-edge-key e' gp cgp ein
      le1  = Selection-le-EvalFun gp sel (LeFunCode-refl gp cgp) cgp cgp ck
      cefk = Coherent-EvalFun gp (fst e') cgp ck
      cefx = Coherent-EvalFun gp x cgp cx
      mon  = EvalFun-mon-arg gp (fst e') x lekx cgp ck cx
  in LeCode-trans (snd e') (EvalFun gp (fst e')) (EvalFun gp x) cv' cefk cefx le1 mon

mkLeFunCode-u0 : (g u0' gp : FinFun) -> CoherentFunTail gp -> CoherentFunTail u0' ->
  ((e : Edge) -> EdgeIn e u0' ->
     Sigma Edge (\ e' -> Pair (EdgeIn e' gp)
       (Pair (LeCode (fst e') (fst e))
         (Pair (LeCode (snd e) (snd e')) (Coherent (snd e')))))) ->
  LeFunCode u0' gp
mkLeFunCode-u0 g nil         gp cgp cu0 align = tt
mkLeFunCode-u0 g (cons p ps) gp cgp cu0 align =
  mkSigma
    (let r     = align p here
         e'    = fst r
         ein'  = fst (snd r)
         lekey = fst (snd (snd r))
         led'  = fst (snd (snd (snd r)))
         cohv' = snd (snd (snd (snd r)))
         cj    = CFTcons.key-coh cu0
     in LeCode-trans (snd p) (snd e') (EvalFun gp (fst p))
          (CFTcons.val-coh cu0) cohv' (Coherent-EvalFun gp (fst p) cgp cj)
          led' (edge-le e' gp (fst p) cgp ein' cj cohv' lekey))
    (mkLeFunCode-u0 g ps gp cgp (CFTcons.tail-coh cu0) (\ e ein -> align e (there ein)))

------------------------------------------------------------------------
-- FUNEL-BELOW, the u = FunEl u0 case, assembled into the goal.
------------------------------------------------------------------------

funBelowFunEl : (m : Nat) (g : FinFun) (b : FinEl) (f : FinFun) ->
  ihaT m -> ihbT m -> CoherentFunTail g -> CoherentFunTail f ->
  finMemFunC g b f -> finMemAllUC f b -> Coherent b -> finMemC b UCode ->
  Le (RANKFun g) (suc m) -> Le (RANK b) m -> Le (RANKFun f) m ->
  MB.finMem m b UCode -> MB.finMemAllU (suc m) f b ->
  (u0 : FinFun) -> CoherentFun u0 -> LeFunCode u0 g -> Le (RANKFun u0) m ->
  Sigma FinEl (\ y -> Pair (Le (RANK y) (suc m))
    (Pair (LeCode (FunEl u0) y)
      (Pair (LeCode y (FunEl g)) (MB.finMem (suc m) y (PiCode b f)))))
funBelowFunEl m g b f iha ihb ctg ctf fmg fab cb bU rg rb rf bUm faSm nil () lfu0g ru0
funBelowFunEl m g b f iha ihb ctg ctf fmg fab cb bU rg rb rf bUm faSm (cons p ps) cu0 lfu0g ru0 =
  let bo = buildG' m g b f iha ihb ctg ctf fmg fab cb bU rg rb rf (cons p ps) cu0 lfu0g ru0
      gp = BuildOut.gp bo
  in mkSigma (FunEl gp)
       (mkSigma (BuildOut.rkgp bo)
         (mkSigma (mkLeFunCode-u0 g (cons p ps) gp (BuildOut.cftgp bo) cu0 (BuildOut.align bo))
           (mkSigma (BuildOut.lfgpg bo)
             (mkSigma (BuildOut.ffgp bo)
               (mkSigma (BuildOut.cftgp bo)
                 (mkSigma bUm (mkSigma faSm ctf)))))))

------------------------------------------------------------------------
-- Top-level entry: exactly the belowS (FunEl g)(PiCode b f) clause type.
------------------------------------------------------------------------

funelBelow : (m : Nat) (g : FinFun) (b : FinEl) (f : FinFun) -> ihaT m -> ihbT m ->
  (u : FinEl) ->
  Le (RANK (FunEl g)) (suc (suc m)) -> Le (RANK (PiCode b f)) (suc m) ->
  Le (RANK u) (suc m) -> Coherent u ->
  MB.finMem (suc (suc m)) (FunEl g) (PiCode b f) -> LeCode u (FunEl g) ->
  Sigma FinEl (\ y -> Pair (Le (RANK y) (suc m))
    (Pair (LeCode u y) (Pair (LeCode y (FunEl g)) (MB.finMem (suc m) y (PiCode b f)))))
funelBelow m g b f iha ihb u bx ba bu cu mem lux = dispatch u bu cu lux
  where
    ff_g  = fst mem
    cohg  = fst (snd mem)
    piDom = fst (snd (snd mem))
    faSS  = fst (snd (snd (snd mem)))
    ctf   = snd (snd (snd (snd mem)))
    ctg   = cft-from-cf g cohg
    rg : Le (RANKFun g) (suc m)
    rg = bx
    rb : Le (RANK b) m
    rb = Le-trans (RANK b) (max (RANK b) (RANKFun f)) m (Le-max-l (RANK b) (RANKFun f)) ba
    rf : Le (RANKFun f) m
    rf = Le-trans (RANKFun f) (max (RANK b) (RANKFun f)) m (Le-max-r (RANK b) (RANKFun f)) ba
    bU : finMemC b UCode
    bU = fromStage (suc m) b UCode (Le-suc (RANK b) m rb) tt piDom
    cb : Coherent b
    cb = coh-from-aU b bU
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
    bFun-SS : Le (suc (max (RANKFun g) (max (RANK b) (RANKFun f)))) (suc (suc m))
    bFun-SS = Le-max-lub (RANKFun g) (max (RANK b) (RANKFun f)) (suc m) rg
                (Le-suc (max (RANK b) (RANKFun f)) m ba)
    fmg : finMemFunC g b f
    fmg = finMemFun-shift (suc (suc m)) (suc (max (RANKFun g) (max (RANK b) (RANKFun f)))) g b f
            bFun-SS (Le-refl (suc (max (RANKFun g) (max (RANK b) (RANKFun f))))) ff_g

    dispatch : (u' : FinEl) -> Le (RANK u') (suc m) -> Coherent u' -> LeCode u' (FunEl g) ->
      Sigma FinEl (\ y -> Pair (Le (RANK y) (suc m))
        (Pair (LeCode u' y) (Pair (LeCode y (FunEl g)) (MB.finMem (suc m) y (PiCode b f)))))
    dispatch Bot          bu' cu' lux' =
      mkSigma Bot (mkSigma tt (mkSigma tt (mkSigma tt (mkSigma bUm (mkSigma faSm ctf)))))
    dispatch UCode        bu' cu' ()
    dispatch (FunEl u0)   bu' cu' lux' =
      funBelowFunEl m g b f iha ihb ctg ctf fmg fab cb bU rg rb rf bUm faSm u0 cu' lux' bu'
    dispatch (PiCode c k) bu' cu' ()
