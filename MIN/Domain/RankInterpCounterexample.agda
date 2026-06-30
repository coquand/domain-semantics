{-# OPTIONS --without-K --exact-split #-}
------------------------------------------------------------------------
-- RankInterpCounterexample.agda  (MIN/ -- Pi + U fragment)
--
-- Machine-checked counterexample to RANK INTERPOLATION (fm-below):
--
--   "if  RANK a <= n,  RANK x <= n+1,  x : a,  RANK u <= n,  u <= x
--    then there is y with RANK y <= n, u <= y <= x, y : a."
--
-- It is FALSE at n = 2 (type-code case a = U).  We exhibit a, x, u and
-- prove that NO such y exists.  Engine: rank is not <=-monotone
-- (kf = fun{ka->U} has rank 2 but kf <= ka of rank 1).
------------------------------------------------------------------------
module MIN.Domain.RankInterpCounterexample where

open import MIN.Domain.Basic
  using ( FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; nil ; cons
        ; mkSigma ; fst ; snd ; Nat ; zero ; suc ; Eq ; refl
        ; Le ; Top ; tt ; Empty ; Pair ; Sigma ; Eq-transport )
open import MIN.Domain.Order using ( RANK ; LeCode ; Coherent ; CoherentFunTail ; mkCFT )
open import MIN.Domain.MemStage using ( finMemC )
open import MIN.Domain.Order using ( EvalFun ; EvalFun-step ; leFinEl ; leFinEl-sound )
open import MIN.Domain.Basic using ( isPos )
open import MIN.Domain.Membership
  using ( FinMemFun ; FinMemAllU ; finMem-piU-mk ; finMem-funel-mk
        ; finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft
        ; finMem-funel-fun ; finMem-funel-coh ; finMem-funel-wf )
open import MIN.Domain.Order
  using ( EvalFun-mon ; LeCode-trans ; RANKFun ; cft-from-cf ; Coherent-EvalFun )
open import MIN.Domain.Basic using ( Le-trans ; Le-max-r ; Eq )
open import MIN.Domain.MemUnfold using ( FinMem-coh-u )
open import MIN.Model.Selection
  using ( selectionBelow ; Selection-le-EvalFun ; Coherent-Selection
        ; FinMemAllU-Selection ; FinMem-Selection ; FinMem-Selection-codomain )
open import MIN.Domain.KeyJoinLemma using ( sel-rank )

------------------------------------------------------------------------
-- The codes.
------------------------------------------------------------------------
ka : FinEl                                    -- e  = fun{ bot -> U },  rank 1
ka = FunEl (cons (mkSigma Bot UCode) nil)

kf : FinEl                                    -- e' = fun{ ka -> U },   rank 2,  kf <= ka
kf = FunEl (cons (mkSigma ka UCode) nil)

d : FinEl                                     -- Pi( U ; { bot -> U } ), rank 1
d = PiCode UCode (cons (mkSigma Bot UCode) nil)

bhat : FinEl                                  -- Pi( d ; { ka -> U } ),  rank 2
bhat = PiCode d (cons (mkSigma ka UCode) nil)

x : FinEl                                     -- Pi( bhat ; { kf -> U } ), rank 3, : U
x = PiCode bhat (cons (mkSigma kf UCode) nil)

u : FinEl                                     -- Pi( bot ; { ka -> U } ), rank 2, <= x
u = PiCode Bot (cons (mkSigma ka UCode) nil)

------------------------------------------------------------------------
-- Ranks (definitional).
------------------------------------------------------------------------
rank-x : Eq (RANK x) 3
rank-x = refl

rank-u : Eq (RANK u) 2
rank-u = refl

rank-ka : Eq (RANK ka) 1
rank-ka = refl

rank-kf : Eq (RANK kf) 2
rank-kf = refl

------------------------------------------------------------------------
-- Order facts.
------------------------------------------------------------------------
kf-le-ka : LeCode kf ka                       -- rank inversion: 2 <= 1
kf-le-ka = mkSigma tt tt

u-le-x : LeCode u x
u-le-x = mkSigma tt (mkSigma tt tt)

coh-ka : Coherent ka
coh-ka = mkCFT tt tt tt tt tt
coh-u : Coherent u
coh-u = mkSigma tt (mkCFT coh-ka tt tt tt tt)
uU : finMemC UCode UCode
uU = tt
botU : finMemC Bot UCode
botU = tt

d-mem : finMemC d UCode
d-mem = finMem-piU-mk UCode (cons (mkSigma Bot UCode) nil)
          uU (mkSigma (mkSigma botU uU) tt) (mkCFT tt tt tt tt tt)

ka-d : finMemC ka d
ka-d = finMem-funel-mk (cons (mkSigma Bot UCode) nil) UCode (cons (mkSigma Bot UCode) nil)
         (mkSigma (mkSigma botU uU) tt) (mkCFT tt tt tt tt tt) d-mem

bhat-mem : finMemC bhat UCode
bhat-mem = finMem-piU-mk d (cons (mkSigma ka UCode) nil)
             d-mem (mkSigma (mkSigma ka-d uU) tt) (mkCFT coh-ka tt tt tt tt)

kf-bhat : finMemC kf bhat
kf-bhat = finMem-funel-mk (cons (mkSigma ka UCode) nil) d (cons (mkSigma ka UCode) nil)
            (mkSigma (mkSigma ka-d uU) tt) (mkCFT coh-ka tt tt tt tt) bhat-mem

x-mem : finMemC x UCode
x-mem = finMem-piU-mk bhat (cons (mkSigma kf UCode) nil)
          bhat-mem (mkSigma (mkSigma kf-bhat uU) tt) (mkCFT coh-kf tt tt tt tt)
  where
    coh-kf = mkCFT coh-ka tt tt tt tt

------------------------------------------------------------------------
-- The rank-interpolation property at n = 2, and its refutation.
------------------------------------------------------------------------
RankInterp : Set
RankInterp =
  (a xx uu : FinEl) ->
  Le (RANK a) 2 -> Le (RANK xx) 3 -> Le (RANK uu) 2 ->
  Coherent uu -> finMemC xx a -> LeCode uu xx ->
  Sigma FinEl (\ y -> Pair (Le (RANK y) 2)
    (Pair (LeCode uu y) (Pair (LeCode y xx) (finMemC y a))))

exFalso : {A : Set} -> Empty -> A
exFalso ()

-- single-edge eval inversion: UCode <= EvalFun {(k -> U)} v  ==>  k <= v.
single-ge-key : (k v : FinEl) ->
  LeCode UCode (EvalFun (cons (mkSigma k UCode) nil) v) -> LeCode k v
single-ge-key k v le = step (leFinEl k v) refl le
  where
    step : (w : Nat) -> Eq w (leFinEl k v) ->
      LeCode UCode (EvalFun-step w UCode nil v) -> LeCode k v
    step zero    eq le = exFalso le
    step (suc n) eq le = leFinEl-sound k v (Eq-transport isPos eq tt)

-- UCode <= c  forces  c = UCode.
leU-eq : (c : FinEl) -> LeCode UCode c -> Eq c UCode
leU-eq Bot          ()
leU-eq UCode        le = refl
leU-eq (FunEl g)    ()
leU-eq (PiCode a f) ()

-- UCode : T  forces  T = UCode.
memU-eq : (T : FinEl) -> finMemC UCode T -> Eq T UCode
memU-eq Bot          ()
memU-eq UCode        m = refl
memU-eq (FunEl g)    ()
memU-eq (PiCode a f) ()

-- the deepest contradiction: a rank-0 element s with ka <= s is impossible.
level3 : (s : FinEl) -> LeCode ka s -> Le (RANK s) zero -> Empty
level3 Bot          le rk = le
level3 UCode        le rk = le
level3 (FunEl d)    le ()
level3 (PiCode a f) le rk = le

-- No rank-<=2 type code y lies in [u, x].
no-interp : (y : FinEl) -> Le (RANK y) 2 -> LeCode u y -> LeCode y x -> finMemC y UCode -> Empty
no-interp Bot          ry luy lyx my = luy
no-interp UCode        ry luy lyx my = luy
no-interp (FunEl g)    ry luy lyx my = luy
no-interp (PiCode y0 yf) ry luy lyx my = contra uSel kf-uSel uSel-ka uSel-y0 rk-uSel
  where
    ucode-eval-ka : LeCode UCode (EvalFun yf ka)
    ucode-eval-ka = fst (snd luy)
    y0-bhat : LeCode y0 bhat
    y0-bhat = fst lyx
    yf-kf' = snd lyx                                -- LeFunCode yf {(kf,U)}
    y0U : finMemC y0 UCode
    y0U = finMem-piU-dom y0 yf my
    cy0 : Coherent y0
    cy0 = FinMem-coh-u y0 UCode y0U
    allUyf : FinMemAllU yf y0
    allUyf = finMem-piU-allU y0 yf my
    cyf : CoherentFunTail yf
    cyf = finMem-piU-cft y0 yf my
    rk-yf : Le (RANKFun yf) 1
    rk-yf = Le-trans (RANKFun yf) _ 1 (Le-max-r (RANK y0) (RANKFun yf)) ry
    sb = selectionBelow yf ka cyf coh-ka
    uSel = fst sb ; vSel = fst (snd sb)
    sel = fst (snd (snd sb))
    uSel-ka : LeCode uSel ka
    uSel-ka = fst (snd (snd (snd sb)))
    eq-vSel : Eq (EvalFun yf ka) vSel
    eq-vSel = snd (snd (snd (snd sb)))
    cuSel = Coherent-Selection sel cyf
    uSel-y0 : finMemC uSel y0
    uSel-y0 = FinMemAllU-Selection y0 sel allUyf cyf cy0 y0U
    ucode-vSel : LeCode UCode vSel
    ucode-vSel = Eq-transport (\ z -> LeCode UCode z) eq-vSel ucode-eval-ka
    vSel-kf : LeCode vSel (EvalFun (cons (mkSigma kf UCode) nil) uSel)
    vSel-kf = Selection-le-EvalFun {yf} {uSel} {vSel} (cons (mkSigma kf UCode) nil)
                sel yf-kf' cyf (mkCFT coh-kf tt tt tt tt) cuSel
      where coh-kf = mkCFT coh-ka tt tt tt tt
    cvSel : Coherent vSel
    cvSel = Eq-transport Coherent eq-vSel (Coherent-EvalFun yf ka cyf coh-ka)
    ucode-kf : LeCode UCode (EvalFun (cons (mkSigma kf UCode) nil) uSel)
    ucode-kf = LeCode-trans UCode vSel _ tt cvSel
                 (Coherent-EvalFun (cons (mkSigma kf UCode) nil) uSel
                   (mkCFT (mkCFT coh-ka tt tt tt tt) tt tt tt tt) cuSel)
                 ucode-vSel vSel-kf
    kf-uSel : LeCode kf uSel
    kf-uSel = single-ge-key kf uSel ucode-kf
    rk-uSel : Le (RANK uSel) 1
    rk-uSel = Le-trans (RANK uSel) (RANKFun yf) 1 (sel-rank sel) rk-yf

    contra : (us : FinEl) -> LeCode kf us -> LeCode us ka -> finMemC us y0 -> Le (RANK us) 1 -> Empty
    contra Bot          kfus _ _ _ = kfus
    contra UCode        kfus _ _ _ = kfus
    contra (PiCode a f) kfus _ _ _ = kfus
    contra (FunEl g) kfus uska usy0 rkus = caseY0 y0 usy0 y0-bhat
      where
        ge-gka : LeCode UCode (EvalFun g ka)
        ge-gka = fst kfus
        rkg : Le (RANKFun g) zero
        rkg = rkus
        caseY0 : (y : FinEl) -> finMemC (FunEl g) y -> LeCode y bhat -> Empty
        caseY0 Bot          mem _ = mem
        caseY0 UCode        mem _ = mem
        caseY0 (FunEl h)    mem _ = mem
        caseY0 (PiCode y00 y0f) mem y0b =
          level3 (fst sb2) ka-s rk-s
          where
            fmg  = finMem-funel-fun g y00 y0f mem
            cg   = cft-from-cf g (finMem-funel-coh g y00 y0f mem)
            wfy0 = finMem-funel-wf g y00 y0f mem
            y00U = finMem-piU-dom y00 y0f wfy0
            cy00 = FinMem-coh-u y00 UCode y00U
            cy0f = finMem-piU-cft y00 y0f wfy0
            allUy0f = finMem-piU-allU y00 y0f wfy0
            y0f-ka = snd y0b
            sb2 = selectionBelow g ka cg coh-ka
            s = fst sb2 ; vSel2 = fst (snd sb2)
            sel2 = fst (snd (snd sb2))
            eq2 : Eq (EvalFun g ka) vSel2
            eq2 = snd (snd (snd (snd sb2)))
            cs = Coherent-Selection sel2 cg
            s-y00 : finMemC s y00
            s-y00 = FinMem-Selection y00 y0f sel2 fmg cg cy00 y00U
            vSel2-cod : finMemC vSel2 (EvalFun y0f s)
            vSel2-cod = FinMem-Selection-codomain y00 y0f sel2 fmg cg cy0f allUy0f
            ucode-vSel2 : LeCode UCode vSel2
            ucode-vSel2 = Eq-transport (\ z -> LeCode UCode z) eq2 ge-gka
            vSel2=U : Eq vSel2 UCode
            vSel2=U = leU-eq vSel2 ucode-vSel2
            ucode-cod : finMemC UCode (EvalFun y0f s)
            ucode-cod = Eq-transport (\ z -> finMemC z (EvalFun y0f s)) vSel2=U vSel2-cod
            cod=U : Eq (EvalFun y0f s) UCode
            cod=U = memU-eq (EvalFun y0f s) ucode-cod
            mon : LeCode (EvalFun y0f s) (EvalFun (cons (mkSigma ka UCode) nil) s)
            mon = EvalFun-mon y0f (cons (mkSigma ka UCode) nil) s cy0f
                    (mkCFT coh-ka tt tt tt tt) cs y0f-ka
            ucode-kas : LeCode UCode (EvalFun (cons (mkSigma ka UCode) nil) s)
            ucode-kas = Eq-transport (\ z -> LeCode z (EvalFun (cons (mkSigma ka UCode) nil) s)) cod=U mon
            ka-s : LeCode ka s
            ka-s = single-ge-key ka s ucode-kas
            rk-s : Le (RANK s) zero
            rk-s = Le-trans (RANK s) (RANKFun g) zero (sel-rank sel2) rkg

fm-below-false : RankInterp -> Empty
fm-below-false RI =
  let r = RI UCode x u tt tt tt coh-u x-mem u-le-x
      y  = fst r
      ry = fst (snd r)
      luy = fst (snd (snd r))
      lyx = fst (snd (snd (snd r)))
      my  = snd (snd (snd (snd r)))
  in no-interp y ry luy lyx my
