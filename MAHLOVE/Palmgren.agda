{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOVE/Palmgren.agda
--
-- Palmgren's paradox INSIDE the object theory: the Russell Mahlo theory
-- of MAHLO/Typing extended by V-elimination (MAHLOVE/Typing) derives a
-- closed term of type  Bot = Pi X:V. X.
--
-- Terms (Leibniz equality  Leib x y = Pi P:V->V. P x -> P y):
--   f0 = \a b. a,  g0 = \a b c. N,  w0 = U(f0,g0)
--   proj y  = velim(OpF; k, k, k, f; y)       (proj U(f,g) = f, else k)
--   PX y    = velim(V; N, N, N, X; y)         (X on U-codes, N otherwise)
--   Q x     = Leib x w0 -> Bot                (the motive)
--   qN, qP, qS : Leib c w0 -> Bot  by  e (\y. PX y) 0  (no-confusion)
--   qU         : from e : Leib U(f,g) w0, transport along
--                h y = proj y w0 (\_.w0)  to  Leib (f w0 b0) w0  and
--                apply the induction hypothesis at a = w0:  Bot
--   palmgren = velim(Q; qN, qP, qS, qU; w0) (refl w0) : Bot
------------------------------------------------------------------------

module MAHLOVE.Palmgren where

open import MAHLOVE.Basic using (refl)
open import MAHLOVE.Syntax
open import MAHLOVE.Typing

------------------------------------------------------------------------
-- Closed terms (generic in the scope)
------------------------------------------------------------------------

VV : {n : Num} -> Expr n
VV = Arr V V

kO : {n : Num} -> Expr n
kO = Lam V (Lam (Arr x0 V) Nat)

f0 : {n : Num} -> Expr n
f0 = Lam V (Lam (Arr x0 V) x1)

g0 : {n : Num} -> Expr n
g0 = Lam V (Lam (Arr x0 V) (Lam (App (App f0 x1) x0) Nat))

w0 : {n : Num} -> Expr n
w0 = Ucode f0 g0

b0 : {n : Num} -> Expr n
b0 = Lam w0 w0

Bot : {n : Num} -> Expr n
Bot = PiB V x0

Leib : {n : Num} -> Expr n -> Expr n -> Expr n
Leib x y = PiB VV (Arr (App x0 (wkExpr x)) (App x0 (wkExpr y)))

rfl : {n : Num} -> Expr n -> Expr n
rfl x = Lam VV (Lam (App x0 (wkExpr x)) x0)

proj : {n : Num} -> Expr n -> Expr n
proj t = VElim OpF kO kO kO x3 t

------------------------------------------------------------------------
-- Basic typings, in an arbitrary well-formed context
------------------------------------------------------------------------

module _ {n : Num} {G : Ctx n} where

  isArrV : {A : Expr n} -> HasType G A V -> IsType G (Arr A V)
  isArrV h = isty-Pi (isty-el h) (isty-V (wf-extend (isty-el h)))

  isVV : WfCtx G -> IsType G VV
  isVV w = isty-Pi (isty-V w) (isty-V (wf-extend (isty-V w)))

  isBot : WfCtx G -> IsType G Bot
  isBot w = isty-Pi (isty-V w) (isty-el (ty-var (wf-extend (isty-V w))))

isOpBody : {n : Num} {G : Ctx n} -> WfCtx (extend G V) ->
           IsType (extend G V) (Arr (Arr x0 V) V)
isOpBody w = isty-Pi (isArrV (ty-var w)) (isty-V (wf-extend (isArrV (ty-var w))))

isOpF : {n : Num} {G : Ctx n} -> WfCtx G -> IsType G OpF
isOpF w = isty-Pi (isty-V w) (isOpBody (wf-extend (isty-V w)))

-- App (App F a) b : V
app2 : {n : Num} {G : Ctx n} {F a b : Expr n} -> WfCtx G ->
       HasType G F OpF -> HasType G a V -> HasType G b (Arr a V) ->
       HasType G (App (App F a) b) V
app2 w hF ha hb =
  ty-App (isArrV ha) (isty-V (wf-extend (isArrV ha)))
    (ty-App (isty-V w) (isOpBody (wf-extend (isty-V w))) hF ha) hb

-- closed terms: typable in every well-formed context

wfV : {n : Num} {G : Ctx n} -> WfCtx G -> WfCtx (extend G V)
wfV w = wf-extend (isty-V w)

wfVA : {n : Num} {G : Ctx n} -> WfCtx G -> WfCtx (extend (extend G V) (Arr x0 V))
wfVA w = wf-extend (isArrV (ty-var (wfV w)))

hasK : {n : Num} {G : Ctx n} -> WfCtx G -> HasType G kO OpF
hasK w = ty-Lam (isty-V w) (isOpBody (wfV w))
           (ty-Lam (isArrV (ty-var (wfV w))) (isty-V (wfVA w)) (ty-Nat-V (wfVA w)))

hasF0 : {n : Num} {G : Ctx n} -> WfCtx G -> HasType G f0 OpF
hasF0 w = ty-Lam (isty-V w) (isOpBody (wfV w))
            (ty-Lam (isArrV (ty-var (wfV w))) (isty-V (wfVA w)) (ty-var (wfVA w)))

-- OpG F is a type, given  wk wk F : OpF  under  a : V, b : a -> V
isOpG : {n : Num} {G : Ctx n} {F : Expr n} -> WfCtx G ->
        HasType (extend (extend G V) (Arr x0 V)) (wkExpr (wkExpr F)) OpF ->
        IsType G (OpG F)
isOpG w hF = isty-Pi (isty-V w) (isty-Pi (isArrV (ty-var (wfV w)))
               (isArrV (app2 (wfVA w) hF (ty-var (wfVA w)) (ty-var (wfVA w)))))

hasG0 : {n : Num} {G : Ctx n} -> WfCtx G -> HasType G g0 (OpG f0)
hasG0 w =
  ty-Lam (isty-V w)
    (isty-Pi (isArrV (ty-var (wfV w))) (isArrV fab))
    (ty-Lam (isArrV (ty-var (wfV w))) (isArrV fab)
      (ty-Lam (isty-el fab) (isty-V (wf-extend (isty-el fab)))
        (ty-Nat-V (wf-extend (isty-el fab)))))
  where
    fab = app2 (wfVA w) (hasF0 (wfVA w)) (ty-var (wfVA w)) (ty-var (wfVA w))

hasW0 : {n : Num} {G : Ctx n} -> WfCtx G -> HasType G w0 V
hasW0 w = ty-Ucode (hasF0 w) (hasG0 w)

hasB0 : {n : Num} {G : Ctx n} -> WfCtx G -> HasType G b0 (Arr w0 V)
hasB0 w = ty-Lam (isty-el (hasW0 w)) (isty-V (wf-extend (isty-el (hasW0 w))))
            (hasW0 (wf-extend (isty-el (hasW0 w))))

------------------------------------------------------------------------
-- Case contexts for the constant motives OpF and V
------------------------------------------------------------------------

wfUpre : {n : Num} {G : Ctx n} -> WfCtx G -> WfCtx (extend (extend G OpF) (OpG x0))
wfUpre w = wf-extend (isOpG (wf-extend (isOpF w)) (ty-var (wfVA (wf-extend (isOpF w)))))

-- the type  Pi a:V. Pi b:a->V. M  for a constant type M
isIHf : {n : Num} {G : Ctx n} {M : Expr (suc (suc n))} -> WfCtx G ->
        IsType (extend (extend G V) (Arr x0 V)) M -> IsType G (PiB V (PiB (Arr x0 V) M))
isIHf w hM = isty-Pi (isty-V w) (isty-Pi (isArrV (ty-var (wfV w))) hM)

-- motive OpF
wfPSop : {n : Num} {G : Ctx n} -> WfCtx G -> WfCtx (ctxPS G OpF)
wfPSop w = wf-extend (isty-Pi (isty-el (ty-var ww3)) (isOpF (wf-extend (isty-el (ty-var ww3)))))
  where ww3 = wf-extend (isOpF (wfVA w))

wfUop : {n : Num} {G : Ctx n} -> WfCtx G -> WfCtx (ctxU G OpF)
wfUop w = wf-extend (isIHf ww3 (isty-Pi (isty-el fab) (isOpF (wf-extend (isty-el fab)))))
  where
    ww3 = wf-extend (isIHf (wfUpre w) (isOpF (wfVA (wfUpre w))))
    fab = app2 (wfVA ww3) (ty-var (wfVA ww3)) (ty-var (wfVA ww3)) (ty-var (wfVA ww3))

-- motive V
wfPSv : {n : Num} {G : Ctx n} -> WfCtx G -> WfCtx (ctxPS G V)
wfPSv w = wf-extend (isty-Pi (isty-el (ty-var ww3)) (isty-V (wf-extend (isty-el (ty-var ww3)))))
  where ww3 = wf-extend (isty-V (wfVA w))

wfUv : {n : Num} {G : Ctx n} -> WfCtx G -> WfCtx (ctxU G V)
wfUv w = wf-extend (isIHf ww3 (isty-Pi (isty-el fab) (isty-V (wf-extend (isty-el fab)))))
  where
    ww3 = wf-extend (isIHf (wfUpre w) (isty-V (wfVA (wfUpre w))))
    fab = app2 (wfVA ww3) (ty-var (wfVA ww3)) (ty-var (wfVA ww3)) (ty-var (wfVA ww3))

------------------------------------------------------------------------
-- proj : V -> OpF,   proj U(f,g) = f
------------------------------------------------------------------------

module _ {n : Num} {G : Ctx n} (w : WfCtx G) where

  hasProj : {t : Expr n} -> HasType G t V -> HasType G (proj t) OpF
  hasProj ht = ty-VElim (isOpF (wfV w)) (hasK w) (hasK (wfPSop w)) (hasK (wfPSop w))
                 (ty-var (wfUop w)) ht

  projU : {f g : Expr n} -> HasType G f OpF -> HasType G g (OpG f) ->
          ConvTm G (proj (Ucode f g)) f OpF
  projU hf hg = conv-VElim-U (isOpF (wfV w)) (hasK w) (hasK (wfPSop w)) (hasK (wfPSop w))
                  (ty-var (wfUop w)) hf hg

------------------------------------------------------------------------
-- The discriminator  dsc X t = velim(V; N, N, N, X; t)
-- (X in the scope of the U case, i.e. weakened by 4)
------------------------------------------------------------------------

dsc : {n : Num} -> Expr (suc (suc (suc (suc n)))) -> Expr n -> Expr n
dsc X t = VElim V Nat Nat Nat X t

module _ {n : Num} {G : Ctx n} (w : WfCtx G)
         {X : Expr (suc (suc (suc (suc n))))} (hX : HasType (ctxU G V) X V) where

  hasDsc : {t : Expr n} -> HasType G t V -> HasType G (dsc X t) V
  hasDsc ht = ty-VElim (isty-V (wfV w)) (ty-Nat-V w) (ty-Nat-V (wfPSv w)) (ty-Nat-V (wfPSv w)) hX ht

  dscNat : ConvTm G (dsc X Nat) Nat V
  dscNat = conv-VElim-Nat (isty-V (wfV w)) (ty-Nat-V w) (ty-Nat-V (wfPSv w)) (ty-Nat-V (wfPSv w)) hX

  dscPi : {A : Expr n} {B : Expr (suc n)} -> HasType G A V -> HasType (extend G A) B V ->
          ConvTm G (dsc X (PiB A B)) Nat V
  dscPi hA hB = conv-VElim-Pi (isty-V (wfV w)) (ty-Nat-V w) (ty-Nat-V (wfPSv w)) (ty-Nat-V (wfPSv w)) hX hA hB

  dscSig : {A : Expr n} {B : Expr (suc n)} -> HasType G A V -> HasType (extend G A) B V ->
           ConvTm G (dsc X (SigmaB A B)) Nat V
  dscSig hA hB = conv-VElim-Sigma (isty-V (wfV w)) (ty-Nat-V w) (ty-Nat-V (wfPSv w)) (ty-Nat-V (wfPSv w)) hX hA hB

  dscU : {f g : Expr n} -> HasType G f OpF -> HasType G g (OpG f) ->
         ConvTm G (dsc X (Ucode f g))
                  (substExpr (sub4 f g
                     (Lam V (Lam (Arr x0 V) (velimR w2 V Nat Nat Nat X (App (App (renExpr w2 f) x1) x0))))
                     (Lam V (Lam (Arr x0 V) (Lam (App (App (renExpr w2 f) x1) x0)
                        (velimR w3 V Nat Nat Nat X (App (App (App (renExpr w3 g) x2) x1) x0)))))) X)
                  V
  dscU hf hg = conv-VElim-U (isty-V (wfV w)) (ty-Nat-V w) (ty-Nat-V (wfPSv w)) (ty-Nat-V (wfPSv w)) hX hf hg

------------------------------------------------------------------------
-- Leibniz equality and the motive Q
------------------------------------------------------------------------

appV : {n : Num} {G : Ctx n} {A F a : Expr n} ->
       HasType G A V -> HasType G F (Arr A V) -> HasType G a A -> HasType G (App F a) V
appV hA hF ha = ty-App (isty-el hA) (isty-V (wf-extend (isty-el hA))) hF ha

-- P t : V  for  P : V -> V
appP : {n : Num} {G : Ctx n} {P t : Expr n} -> WfCtx G ->
       HasType G P VV -> HasType G t V -> HasType G (App P t) V
appP w hP ht = ty-App (isty-V w) (isty-V (wfV w)) hP ht

isLeib : {n : Num} {G : Ctx n} {t : Expr n} -> WfCtx G ->
         HasType (extend G VV) (wkExpr t) V -> IsType G (Leib t w0)
isLeib w ht = isty-Pi (isVV w) (isty-Pi (isty-el hPt) (isty-el (appP wz (ty-var wz) (hasW0 wz))))
  where
    wv = wf-extend (isVV w)
    hPt = appP wv (ty-var wv) ht
    wz = wf-extend (isty-el hPt)

isQ : {n : Num} {G : Ctx n} {t : Expr n} -> WfCtx G ->
      HasType (extend G VV) (wkExpr t) V -> IsType G (Arr (Leib t w0) Bot)
isQ w ht = isty-Pi (isLeib w ht) (isBot (wf-extend (isLeib w ht)))

Q : {n : Num} -> Expr (suc n)
Q = Arr (Leib x0 w0) Bot

wfPSq : {n : Num} {G : Ctx n} -> WfCtx G -> WfCtx (ctxPS G Q)
wfPSq w = wf-extend (isty-Pi (isty-el (ty-var wq3))
            (isQ wy (appV (ty-var wyP) (ty-var wyP) (ty-var wyP))))
  where
    wq3 = wf-extend (isQ (wfVA w) (ty-var (wf-extend (isVV (wfVA w)))))
    wy  = wf-extend (isty-el (ty-var wq3))
    wyP = wf-extend (isVV wy)

wfUq : {n : Num} {G : Ctx n} -> WfCtx G -> WfCtx (ctxU G Q)
wfUq w = wf-extend (isIHf wu3 (isty-Pi (isty-el fab) (isQ wc hgabc)))
  where
    wp  = wfUpre w
    wpP = wf-extend (isVV (wfVA wp))
    wu3 = wf-extend (isIHf wp (isQ (wfVA wp)
            (app2 wpP (ty-var wpP) (ty-var wpP) (ty-var wpP))))
    fab = app2 (wfVA wu3) (ty-var (wfVA wu3)) (ty-var (wfVA wu3)) (ty-var (wfVA wu3))
    wc  = wf-extend (isty-el fab)
    wcP = wf-extend (isVV wc)
    -- g a b c,  g : OpG f
    hgabc = ty-App (isty-el fab') (isty-V (wf-extend (isty-el fab')))
              (ty-App (isArrV (ty-var wcP)) (isArrV (app2 wcb (ty-var wcb) (ty-var wcb) (ty-var wcb)))
                (ty-App (isty-V wcP)
                   (isty-Pi (isArrV (ty-var wcPa))
                      (isArrV (app2 wcPab (ty-var wcPab) (ty-var wcPab) (ty-var wcPab))))
                   (ty-var wcP) (ty-var wcP))
                (ty-var wcP))
              (ty-var wcP)
      where
        fab'  = app2 wcP (ty-var wcP) (ty-var wcP) (ty-var wcP)
        wcb   = wf-extend (isArrV (ty-var wcP))
        wcPa  = wfV wcP
        wcPab = wfVA wcP

tyNat : {n : Num} {G : Ctx n} -> WfCtx G -> HasType G Nat V
tyNat w = ty-Nat-V w

------------------------------------------------------------------------
-- No-confusion:  the discriminator  PX = \y. velim(V; N,N,N,X; y)
------------------------------------------------------------------------

PXv : {n : Num} -> Expr (suc n)
PXv = Lam V (dsc (Var (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) x0)

hasLamDsc : {n : Num} {G : Ctx n} {Xu : Expr (suc (suc (suc (suc (suc n)))))} -> WfCtx G ->
            HasType (ctxU (extend G V) V) Xu V -> HasType G (Lam V (dsc Xu x0)) VV
hasLamDsc w hX = ty-Lam (isty-V w) (isty-V (wfV w)) (hasDsc (wfV w) hX (ty-var (wfV w)))

-- PX w0 = X
pxW : {n : Num} {G : Ctx n} -> WfCtx (extend G V) -> ConvTm (extend G V) (App PXv w0) x0 V
pxW w = conv-trans
          (conv-beta (isty-V w) (isty-V (wfV w)) (hasDsc (wfV w) (ty-var (wfUv (wfV w))) (ty-var (wfV w)))
             (hasW0 w))
          (dscU w (ty-var (wfUv w)) (hasF0 w) (hasG0 w))

-- the no-confusion case  \e. \X. e PX 0 : Leib c w0 -> Bot
qcase : {n : Num} -> Expr n -> Expr n
qcase c = Lam (Leib c w0) (Lam V (App (App x1 PXv) Zero))

qN-ok : {n : Num} {G : Ctx n} -> WfCtx G -> HasType G (qcase Nat) (subst1 Q Nat)
qN-ok w0' = ty-Lam hL (isBot wL) (ty-Lam (isty-V wL) (isty-el (ty-var wX)) body)
  where
    w   = w0'
    wP  = wf-extend (isVV w)
    hL  = isLeib w (tyNat wP)
    wL  = wf-extend hL
    wX  = wfV wL
    hPc = appP wX (hasLamDsc wX (ty-var (wfUv (wfV wX)))) (tyNat wX)
    wX1 = wf-extend (isty-el hPc)
    wXP = wf-extend (isVV wX)
    wXPz = wf-extend (isty-el (appP wXP (ty-var wXP) (tyNat wXP)))
    cvN = conv-trans
            (conv-beta (isty-V wX) (isty-V (wfV wX))
               (hasDsc (wfV wX) (ty-var (wfUv (wfV wX))) (ty-var (wfV wX))) (tyNat wX))
            (dscNat wX (ty-var (wfUv wX)))
    body = ty-conv
             (ty-App (isty-el hPc)
                (isty-el (appP wX1 (hasLamDsc wX1 (ty-var (wfUv (wfV wX1)))) (hasW0 wX1)))
                (ty-App (isVV wX)
                   (isty-Pi (isty-el (appP wXP (ty-var wXP) (tyNat wXP)))
                            (isty-el (appP wXPz (ty-var wXPz) (hasW0 wXPz))))
                   (ty-var wX) (hasLamDsc wX (ty-var (wfUv (wfV wX)))))
                (ty-conv (ty-Zero wX) (tyeq-el (conv-sym cvN))))
             (tyeq-el (pxW wX))

qP-ok : {n : Num} {G : Ctx n} -> WfCtx G -> HasType (ctxPS G Q) (qcase (PiB x3 (App x3 x0))) (resPi Q)
qP-ok w0' = ty-Lam hL (isBot wL) (ty-Lam (isty-V wL) (isty-el (ty-var wX)) body)
  where
    w   = wfPSq w0'
    wP  = wf-extend (isVV w)
    hL  = isLeib w (ty-Pi (univ-V refl) (ty-var wP) (appV (ty-var (wf-extend (isty-el (ty-var wP)))) (ty-var (wf-extend (isty-el (ty-var wP)))) (ty-var (wf-extend (isty-el (ty-var wP))))))
    wL  = wf-extend hL
    wX  = wfV wL
    wXA = wf-extend (isty-el (ty-var wX))
    hPc = appP wX (hasLamDsc wX (ty-var (wfUv (wfV wX)))) (ty-Pi (univ-V refl) (ty-var wX) (appV (ty-var (wf-extend (isty-el (ty-var wX)))) (ty-var (wf-extend (isty-el (ty-var wX)))) (ty-var (wf-extend (isty-el (ty-var wX))))))
    wX1 = wf-extend (isty-el hPc)
    wXP = wf-extend (isVV wX)
    wXPz = wf-extend (isty-el (appP wXP (ty-var wXP) (ty-Pi (univ-V refl) (ty-var wXP) (appV (ty-var (wf-extend (isty-el (ty-var wXP)))) (ty-var (wf-extend (isty-el (ty-var wXP)))) (ty-var (wf-extend (isty-el (ty-var wXP))))))))
    cvN = conv-trans
            (conv-beta (isty-V wX) (isty-V (wfV wX))
               (hasDsc (wfV wX) (ty-var (wfUv (wfV wX))) (ty-var (wfV wX))) (ty-Pi (univ-V refl) (ty-var wX) (appV (ty-var (wf-extend (isty-el (ty-var wX)))) (ty-var (wf-extend (isty-el (ty-var wX)))) (ty-var (wf-extend (isty-el (ty-var wX)))))))
            (dscPi wX (ty-var (wfUv wX)) (ty-var wX) (appV (ty-var wXA) (ty-var wXA) (ty-var wXA)))
    body = ty-conv
             (ty-App (isty-el hPc)
                (isty-el (appP wX1 (hasLamDsc wX1 (ty-var (wfUv (wfV wX1)))) (hasW0 wX1)))
                (ty-App (isVV wX)
                   (isty-Pi (isty-el (appP wXP (ty-var wXP) (ty-Pi (univ-V refl) (ty-var wXP) (appV (ty-var (wf-extend (isty-el (ty-var wXP)))) (ty-var (wf-extend (isty-el (ty-var wXP)))) (ty-var (wf-extend (isty-el (ty-var wXP))))))))
                            (isty-el (appP wXPz (ty-var wXPz) (hasW0 wXPz))))
                   (ty-var wX) (hasLamDsc wX (ty-var (wfUv (wfV wX)))))
                (ty-conv (ty-Zero wX) (tyeq-el (conv-sym cvN))))
             (tyeq-el (pxW wX))

qS-ok : {n : Num} {G : Ctx n} -> WfCtx G -> HasType (ctxPS G Q) (qcase (SigmaB x3 (App x3 x0))) (resSig Q)
qS-ok w0' = ty-Lam hL (isBot wL) (ty-Lam (isty-V wL) (isty-el (ty-var wX)) body)
  where
    w   = wfPSq w0'
    wP  = wf-extend (isVV w)
    hL  = isLeib w (ty-Sigma (univ-V refl) (ty-var wP) (appV (ty-var (wf-extend (isty-el (ty-var wP)))) (ty-var (wf-extend (isty-el (ty-var wP)))) (ty-var (wf-extend (isty-el (ty-var wP))))))
    wL  = wf-extend hL
    wX  = wfV wL
    wXA = wf-extend (isty-el (ty-var wX))
    hPc = appP wX (hasLamDsc wX (ty-var (wfUv (wfV wX)))) (ty-Sigma (univ-V refl) (ty-var wX) (appV (ty-var (wf-extend (isty-el (ty-var wX)))) (ty-var (wf-extend (isty-el (ty-var wX)))) (ty-var (wf-extend (isty-el (ty-var wX))))))
    wX1 = wf-extend (isty-el hPc)
    wXP = wf-extend (isVV wX)
    wXPz = wf-extend (isty-el (appP wXP (ty-var wXP) (ty-Sigma (univ-V refl) (ty-var wXP) (appV (ty-var (wf-extend (isty-el (ty-var wXP)))) (ty-var (wf-extend (isty-el (ty-var wXP)))) (ty-var (wf-extend (isty-el (ty-var wXP))))))))
    cvN = conv-trans
            (conv-beta (isty-V wX) (isty-V (wfV wX))
               (hasDsc (wfV wX) (ty-var (wfUv (wfV wX))) (ty-var (wfV wX))) (ty-Sigma (univ-V refl) (ty-var wX) (appV (ty-var (wf-extend (isty-el (ty-var wX)))) (ty-var (wf-extend (isty-el (ty-var wX)))) (ty-var (wf-extend (isty-el (ty-var wX)))))))
            (dscSig wX (ty-var (wfUv wX)) (ty-var wX) (appV (ty-var wXA) (ty-var wXA) (ty-var wXA)))
    body = ty-conv
             (ty-App (isty-el hPc)
                (isty-el (appP wX1 (hasLamDsc wX1 (ty-var (wfUv (wfV wX1)))) (hasW0 wX1)))
                (ty-App (isVV wX)
                   (isty-Pi (isty-el (appP wXP (ty-var wXP) (ty-Sigma (univ-V refl) (ty-var wXP) (appV (ty-var (wf-extend (isty-el (ty-var wXP)))) (ty-var (wf-extend (isty-el (ty-var wXP)))) (ty-var (wf-extend (isty-el (ty-var wXP))))))))
                            (isty-el (appP wXPz (ty-var wXPz) (hasW0 wXPz))))
                   (ty-var wX) (hasLamDsc wX (ty-var (wfUv (wfV wX)))))
                (ty-conv (ty-Zero wX) (tyeq-el (conv-sym cvN))))
             (tyeq-el (pxW wX))

------------------------------------------------------------------------
-- The U case
------------------------------------------------------------------------

-- f0 w0 b0 = w0
f0ww : {n : Num} {G : Ctx n} -> WfCtx G -> ConvTm G (App (App f0 w0) b0) w0 V
f0ww w =
  conv-trans
    (conv-App (isArrV (hasW0 w)) (isty-V (wf-extend (isArrV (hasW0 w))))
       (conv-beta (isty-V w) (isOpBody (wfV w))
          (ty-Lam (isArrV (ty-var (wfV w))) (isty-V (wfVA w)) (ty-var (wfVA w))) (hasW0 w))
       (conv-refl (hasB0 w)))
    (conv-beta (isArrV (hasW0 w)) (isty-V (wf-extend (isArrV (hasW0 w))))
       (hasW0 (wf-extend (isArrV (hasW0 w)))) (hasB0 w))

-- h y = proj y w0 b0,   HP = \y. P (h y)
HP : {n : Num} -> Expr (suc (suc n))
HP = Lam V (App x2 (App (App (proj x0) w0) b0))

-- the e' of the U case:  from e : Leib U(f,g) w0  get  Leib (f w0 b0) w0
e' : {n : Num} -> Expr (suc (suc (suc (suc (suc n)))))
e' = Lam VV (Lam (App x0 (App (App x5' w0) b0)) (App (App x2 HP) x0))
  where x5' = Var (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))

qU : {n : Num} -> Expr (suc (suc (suc (suc n))))
qU = Lam (Leib (Ucode x3 x2) w0) (App (App (App x2 w0) b0) e')

qU-ok : {n : Num} {G : Ctx n} -> WfCtx G -> HasType (ctxU G Q) qU (resU Q)
qU-ok w = ty-Lam hL (isBot wL5) body5
  where
    wK   = wfUq w
    wKP  = wf-extend (isVV wK)
    hL   = isLeib wK (ty-Ucode (ty-var wKP) (ty-var wKP))
    wL5  = wf-extend hL
    wL6  = wf-extend (isVV wL5)
    hz   = appP wL6 (ty-var wL6) (app2 wL6 (ty-var wL6) (hasW0 wL6) (hasB0 wL6))
    wL7  = wf-extend (isty-el hz)
    hU   = ty-Ucode (ty-var wL7) (ty-var wL7)
    hHP  = (ty-Lam (isty-V wL7) (isty-V (wfV wL7)) (appP (wfV wL7) (ty-var (wfV wL7)) (app2 (wfV wL7) (hasProj (wfV wL7) (ty-var (wfV wL7))) (hasW0 (wfV wL7)) (hasB0 (wfV wL7)))))
    hHPU = appP wL7 hHP hU
    wL8  = wf-extend (isty-el hHPU)
    hHPw = appP wL8 (ty-Lam (isty-V wL8) (isty-V (wfV wL8)) (appP (wfV wL8) (ty-var (wfV wL8)) (app2 (wfV wL8) (hasProj (wfV wL8) (ty-var (wfV wL8))) (hasW0 (wfV wL8)) (hasB0 (wfV wL8))))) (hasW0 wL8)
    wL7P = wf-extend (isVV wL7)
    wL7Pz = wf-extend (isty-el (appP wL7P (ty-var wL7P) (ty-Ucode (ty-var wL7P) (ty-var wL7P))))
    -- HP U(f,g) = P (f w0 b0)
    cvA  = conv-trans
             (conv-beta (isty-V wL7) (isty-V (wfV wL7)) (appP (wfV wL7) (ty-var (wfV wL7)) (app2 (wfV wL7) (hasProj (wfV wL7) (ty-var (wfV wL7))) (hasW0 (wfV wL7)) (hasB0 (wfV wL7)))) hU)
             (conv-App (isty-V wL7) (isty-V (wfV wL7)) (conv-refl (ty-var wL7))
                (conv-App (isArrV (hasW0 wL7)) (isty-V (wf-extend (isArrV (hasW0 wL7))))
                   (conv-App (isty-V wL7) (isOpBody (wfV wL7))
                      (projU wL7 (ty-var wL7) (ty-var wL7)) (conv-refl (hasW0 wL7)))
                   (conv-refl (hasB0 wL7))))
    -- HP w0 = P w0
    cvB  = conv-trans
             (conv-beta (isty-V wL7) (isty-V (wfV wL7)) (appP (wfV wL7) (ty-var (wfV wL7)) (app2 (wfV wL7) (hasProj (wfV wL7) (ty-var (wfV wL7))) (hasW0 (wfV wL7)) (hasB0 (wfV wL7)))) (hasW0 wL7))
             (conv-App (isty-V wL7) (isty-V (wfV wL7)) (conv-refl (ty-var wL7))
                (conv-trans
                   (conv-App (isArrV (hasW0 wL7)) (isty-V (wf-extend (isArrV (hasW0 wL7))))
                      (conv-App (isty-V wL7) (isOpBody (wfV wL7))
                         (projU wL7 (hasF0 wL7) (hasG0 wL7)) (conv-refl (hasW0 wL7)))
                      (conv-refl (hasB0 wL7)))
                   (f0ww wL7)))
    body7 = ty-conv
              (ty-App (isty-el hHPU) (isty-el hHPw)
                 (ty-App (isVV wL7)
                    (isty-Pi (isty-el (appP wL7P (ty-var wL7P) (ty-Ucode (ty-var wL7P) (ty-var wL7P))))
                             (isty-el (appP wL7Pz (ty-var wL7Pz) (hasW0 wL7Pz))))
                    (ty-var wL7) hHP)
                 (ty-conv (ty-var wL7) (tyeq-el (conv-sym cvA))))
              (tyeq-el cvB)
    hPw7 = appP wL7 (ty-var wL7) (hasW0 wL7)
    he'  = ty-Lam (isVV wL5) (isty-Pi (isty-el hz) (isty-el hPw7))
             (ty-Lam (isty-el hz) (isty-el hPw7) body7)
    -- the induction hypothesis at a = w0, b = b0
    wa   = wfVA wL5
    waP  = wf-extend (isVV wa)
    hI1  = ty-App (isty-V wL5)
             (isty-Pi (isArrV (ty-var (wfV wL5))) (isQ wa (app2 waP (ty-var waP) (ty-var waP) (ty-var waP))))
             (ty-var wL5) (hasW0 wL5)
    wb   = wf-extend (isArrV (hasW0 wL5))
    wbP  = wf-extend (isVV wb)
    hI2  = ty-App (isArrV (hasW0 wL5)) (isQ wb (app2 wbP (ty-var wbP) (hasW0 wbP) (ty-var wbP)))
             hI1 (hasB0 wL5)
    wL5P = wf-extend (isVV wL5)
    hT   = app2 wL5P (ty-var wL5P) (hasW0 wL5P) (hasB0 wL5P)
    body5 = ty-App (isLeib wL5 hT) (isBot (wf-extend (isLeib wL5 hT))) hI2 he'

------------------------------------------------------------------------
-- The paradox
------------------------------------------------------------------------

palm : Expr zero
palm = App (VElim Q (qcase Nat) (qcase (PiB x3 (App x3 x0))) (qcase (SigmaB x3 (App x3 x0))) qU w0)
           (rfl w0)

-- a closed inhabitant of  Pi X:V. X
palmgren : HasType empty palm Bot
palmgren =
  ty-App (isLeib wf-empty (hasW0 wv)) (isBot (wf-extend (isLeib wf-empty (hasW0 wv))))
    (ty-VElim (isQ (wfV wf-empty) (ty-var (wf-extend (isVV (wfV wf-empty)))))
       (qN-ok wf-empty) (qP-ok wf-empty) (qS-ok wf-empty) (qU-ok wf-empty) (hasW0 wf-empty))
    (ty-Lam (isVV wf-empty) (isty-Pi (isty-el hPw) (isty-el hPw'))
       (ty-Lam (isty-el hPw) (isty-el hPw') (ty-var wz)))
  where
    wv   = wf-extend (isVV wf-empty)
    hPw  = appP wv (ty-var wv) (hasW0 wv)
    wz   = wf-extend (isty-el hPw)
    hPw' = appP wz (ty-var wz) (hasW0 wz)
