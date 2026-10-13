{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Valid/Step.agda  (Tarski port of MAHLOINJ/Valid/Step)
--
-- Assembling the property pack at stage (suc k) from the pack at k,
-- by dispatch on the codes; hence  props : (k : Lev) -> Props k.
------------------------------------------------------------------------

module MAHLORT.Valid.Step where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; PairEl ; SigmaCode
             ; FinFun ; nil ; cons) renaming (fst to dfst ; snd to dsnd)
open D using () renaming (suc to nsuc ; zero to nzero ; Nat to Lev)
open import MAHLOINJ.Domain.Kernel
  using (EvalFun ; LeCode ; FinMem ; Comp ; Sup ; append ; coh-from-aU ; finMem-funel-fun ; finMem-funel-coh
        ; cft-from-cf ; FinMem-Sup-element ; finMemUCode-Sup ; sucNat-to ; finMemC-pair-fst ; finMemC-pair-snd)
open import MAHLORT.Syntax.Presup using (pTE)
open import MAHLORT.Valid.HeadRed
open import MAHLORT.Valid.Stage
open import MAHLORT.Valid.Props

module Step (k : Lev) (ih : Props k) where

  module CP = CodeT k ih PiB PiOK
  module CS = CodeT k ih SigmaB SigOK
  module PM = PiM k ih
  module SM = SigM k ih
  module NM = NatM k ih

  RT1 = St.RT (nsuc k)
  RM1 = St.RM (nsuc k)

  funU : (g : FinFun) (b : FinEl) (f : FinFun) -> FinMem (FunEl g) (PiCode b f) -> PM.FunU g b f
  funU g b f m = PM.mkFunU (finMem-funel-fun g b f m) (cft-from-cf g (finMem-funel-coh g b f m))

  pairU : (x1 x2 b : FinEl) (f : FinFun) -> FinMem (PairEl x1 x2) (SigmaCode b f) -> SM.PairU x1 x2 b f
  pairU x1 x2 b f m = SM.mkPairU (finMemC-pair-fst x1 x2 b f m) (finMemC-pair-snd x1 x2 b f m)

  -- the decoding along a reduction / a conversion of the element
  decHR : {n : Num} {G : Ctx n} {M M1 T : Expr n} (w : UnivR G T) -> AR M M1 -> AR (decR w M) (decR w M1)
  decHR (u , (rs , (univ-V e , te))) hr = ar-ElV hr
  decHR (u , (rs , (univ-U f g e , te))) hr = ar-ElV (ar-That hr)

  rigidU : {n : Num} {u : Expr n} -> Univ u -> Rigid u
  rigidU (univ-V refl) = rigid-V
  rigidU (univ-U f g refl) = rigid-TyU

  decTE : {n : Num} {G : Ctx n} {M M1 T : Expr n} (w : UnivR G T) -> ConvTm G M M1 T -> TyEq G (decR w M) (decR w M1)
  decTE (u , (rs , (univ-V refl , te))) q = tyeq-ElV (conv-conv q te)
  decTE (u , (rs , (univ-U f g refl , te))) q = tyeq-ElV (conv-That (conv-conv q te))

  expU : {n : Num} {G : Ctx n} {T T1 : Expr n} -> AR T T1 -> TyEq G T T1 -> UnivR G T1 -> UnivR G T
  expU hr q (u , (rs , (un , te))) = u , (ar-to hr rs (rigidU un) , (un , tyeq-trans q te))

  expN : {n : Num} {G : Ctx n} {T T1 : Expr n} -> AR T T1 -> TyEq G T T1 -> NatR G T1 -> NatR G T
  expN hr q (rs , te) = ar-to hr rs rigid-Nat , tyeq-trans q te

  expZ : {n : Num} {G : Ctx n} {M M1 : Expr n} -> AR M M1 -> ConvTm G M M1 Nat -> ZeroR G M1 -> ZeroR G M
  expZ hr q (rs , c) = ar-to hr rs rigid-Zero , conv-trans q c

  iNat : {n : Num} {G : Ctx n} {T : Expr n} -> TyEq G T Nat -> IsType G Nat
  iNat q = snd (pTE q)


  symT1 : {n : Num} {G : Ctx n} {T T' : Expr n} (a : FinEl) -> FinMem a UCode -> RT1 G T T' a -> RT1 G T' T a
  symT1 Bot aU r = tt
  symT1 UCode aU r = univR2 (UnivR2.wr r) (UnivR2.wl r) (sk-sym (UnivR2.sk r))
  symT1 NatCode aU r = snd r , fst r
  symT1 (PiCode b f) aU r = CP.symC b f (piU b f aU) r
  symT1 (SigmaCode b f) aU r = CS.symC b f (sigU b f aU) r

  transT1 : {n : Num} {G : Ctx n} {T1 T2 T3 : Expr n} (a : FinEl) -> FinMem a UCode ->
    RT1 G T1 T2 a -> RT1 G T2 T3 a -> RT1 G T1 T3 a
  transT1 Bot aU r1 r2 = tt
  transT1 UCode aU r1 r2 = univR2 (UnivR2.wl r1) (UnivR2.wr r2)
    (sk-trans (UnivR2.sk r1) (sk-trans (kind-det (UnivR2.wr r1) (UnivR2.wl r2)) (UnivR2.sk r2)))
  transT1 NatCode aU r1 r2 = fst r1 , snd r2
  transT1 (PiCode b f) aU r1 r2 = CP.transC b f (piU b f aU) r1 r2
  transT1 (SigmaCode b f) aU r1 r2 = CS.transC b f (sigU b f aU) r1 r2

  downT1 : {n : Num} {G : Ctx n} {T T' : Expr n} (a0 a1 : FinEl) -> LeCode a0 a1 ->
    FinMem a0 UCode -> FinMem a1 UCode -> RT1 G T T' a1 -> RT1 G T T' a0
  downT1 Bot a1 le a0U a1U r = tt
  downT1 UCode UCode le a0U a1U r = r
  downT1 NatCode NatCode le a0U a1U r = r
  downT1 (PiCode b0 f0) (PiCode b1 f1) le a0U a1U r =
    CP.downC b0 f0 b1 f1 (dfst le) (dsnd le) (piU b0 f0 a0U) (piU b1 f1 a1U) r
  downT1 (SigmaCode b0 f0) (SigmaCode b1 f1) le a0U a1U r =
    CS.downC b0 f0 b1 f1 (dfst le) (dsnd le) (sigU b0 f0 a0U) (sigU b1 f1 a1U) r

  joinT1 : {n : Num} {G : Ctx n} {T T' : Expr n} (a1 a2 : FinEl) -> Comp a1 a2 ->
    FinMem a1 UCode -> FinMem a2 UCode -> RT1 G T T' a1 -> RT1 G T T' a2 -> RT1 G T T' (Sup a1 a2)
  joinT1 Bot a2 c a1U a2U r1 r2 = r2
  joinT1 UCode Bot c a1U a2U r1 r2 = r1
  joinT1 NatCode Bot c a1U a2U r1 r2 = r1
  joinT1 (PiCode b f) Bot c a1U a2U r1 r2 = r1
  joinT1 (SigmaCode b f) Bot c a1U a2U r1 r2 = r1
  joinT1 UCode UCode c a1U a2U r1 r2 = r1
  joinT1 NatCode NatCode c a1U a2U r1 r2 = r1
  joinT1 (PiCode b1 f1) (PiCode b2 f2) c a1U a2U r1 r2 =
    CP.joinC b1 f1 b2 f2 (dfst c) (dsnd c) (piU b1 f1 a1U) (piU b2 f2 a2U)
      (piU (Sup b1 b2) (append f1 f2) (finMemUCode-Sup (PiCode b1 f1) (PiCode b2 f2) c a1U a2U)) r1 r2
  joinT1 (SigmaCode b1 f1) (SigmaCode b2 f2) c a1U a2U r1 r2 =
    CS.joinC b1 f1 b2 f2 (dfst c) (dsnd c) (sigU b1 f1 a1U) (sigU b2 f2 a2U)
      (sigU (Sup b1 b2) (append f1 f2) (finMemUCode-Sup (SigmaCode b1 f1) (SigmaCode b2 f2) c a1U a2U)) r1 r2

  expT1 : {n : Num} {G : Ctx n} {T T1 T' : Expr n} (a : FinEl) -> AR T T1 -> TyEq G T T1 ->
    RT1 G T1 T' a -> RT1 G T T' a
  expT1 Bot hr q r = tt
  expT1 UCode hr q r = univR2 (expU hr q (UnivR2.wl r)) (UnivR2.wr r) (UnivR2.sk r)
  expT1 NatCode hr q r = expN hr q (fst r) , snd r
  expT1 (PiCode b f) hr q r = CP.expC b f hr q r
  expT1 (SigmaCode b f) hr q r = CS.expC b f hr q r

  expT1' : {n : Num} {G : Ctx n} {T T' T1' : Expr n} (a : FinEl) -> AR T' T1' -> TyEq G T' T1' ->
    RT1 G T T1' a -> RT1 G T T' a
  expT1' Bot hr q r = tt
  expT1' UCode hr q r = univR2 (UnivR2.wl r) (expU hr q (UnivR2.wr r)) (UnivR2.sk r)
  expT1' NatCode hr q r = fst r , expN hr q (snd r)
  expT1' (PiCode b f) hr q r = CP.expC' b f hr q r
  expT1' (SigmaCode b f) hr q r = CS.expC' b f hr q r

  symM1 : {n : Num} {G : Ctx n} {M M' T : Expr n} (u a : FinEl) -> FinMem u a -> FinMem a UCode -> RT1 G T T a ->
    RM1 G M M' T u a -> RM1 G M' M T u a
  symM1 Bot a um aU vt r = tt
  symM1 UCode Bot um aU vt r = tt
  symM1 {G = G} UCode UCode um aU vt r = fst r , symT1 {G = G} UCode um (snd r)
  symM1 UCode (FunEl _) um aU vt r = tt
  symM1 UCode ZeroEl um aU vt r = tt
  symM1 UCode (SucEl _) um aU vt r = tt
  symM1 UCode (PairEl _ _) um aU vt r = tt
  symM1 (FunEl _) Bot um aU vt r = tt
  symM1 (FunEl g) UCode um aU vt r = Empty-elim (snd r)
  symM1 (FunEl _) (FunEl _) um aU vt r = tt
  symM1 (FunEl g) (PiCode b f) um aU vt r = PM.symPi (piU b f aU) (funU g b f um) vt r
  symM1 (FunEl _) ZeroEl um aU vt r = tt
  symM1 (FunEl _) (SucEl _) um aU vt r = tt
  symM1 (FunEl _) (PairEl _ _) um aU vt r = tt
  symM1 (PiCode _ _) Bot um aU vt r = tt
  symM1 {G = G} (PiCode pb pf) UCode um aU vt r = fst r , symT1 {G = G} (PiCode pb pf) um (snd r)
  symM1 (PiCode _ _) (FunEl _) um aU vt r = tt
  symM1 (PiCode _ _) ZeroEl um aU vt r = tt
  symM1 (PiCode _ _) (SucEl _) um aU vt r = tt
  symM1 (PiCode _ _) (PairEl _ _) um aU vt r = tt
  symM1 NatCode Bot um aU vt r = tt
  symM1 {G = G} NatCode UCode um aU vt r = fst r , symT1 {G = G} NatCode um (snd r)
  symM1 NatCode (FunEl _) um aU vt r = tt
  symM1 NatCode ZeroEl um aU vt r = tt
  symM1 NatCode (SucEl _) um aU vt r = tt
  symM1 NatCode (PairEl _ _) um aU vt r = tt
  symM1 ZeroEl Bot um aU vt r = tt
  symM1 ZeroEl UCode um aU vt r = Empty-elim (snd r)
  symM1 ZeroEl (FunEl _) um aU vt r = tt
  symM1 ZeroEl NatCode um aU vt r = fst r , (snd (snd r) , fst (snd r))
  symM1 ZeroEl ZeroEl um aU vt r = tt
  symM1 ZeroEl (SucEl _) um aU vt r = tt
  symM1 ZeroEl (PairEl _ _) um aU vt r = tt
  symM1 (SucEl _) Bot um aU vt r = tt
  symM1 (SucEl v) UCode um aU vt r = Empty-elim (snd r)
  symM1 (SucEl _) (FunEl _) um aU vt r = tt
  symM1 (SucEl v) NatCode um aU vt r = fst r , NM.symS (sucNat-to v um) (iNat (fst r)) (snd r)
  symM1 (SucEl _) ZeroEl um aU vt r = tt
  symM1 (SucEl _) (SucEl _) um aU vt r = tt
  symM1 (SucEl _) (PairEl _ _) um aU vt r = tt
  symM1 (PairEl _ _) Bot um aU vt r = tt
  symM1 (PairEl x1 x2) UCode um aU vt r = Empty-elim (snd r)
  symM1 (PairEl _ _) (FunEl _) um aU vt r = tt
  symM1 (PairEl _ _) ZeroEl um aU vt r = tt
  symM1 (PairEl _ _) (SucEl _) um aU vt r = tt
  symM1 (PairEl _ _) (PairEl _ _) um aU vt r = tt
  symM1 (PairEl x1 x2) (SigmaCode b f) um aU vt r = SM.symSig (sigU b f aU) (pairU x1 x2 b f um) vt r
  symM1 (SigmaCode _ _) Bot um aU vt r = tt
  symM1 {G = G} (SigmaCode sb sf) UCode um aU vt r = fst r , symT1 {G = G} (SigmaCode sb sf) um (snd r)
  symM1 (SigmaCode _ _) (FunEl _) um aU vt r = tt
  symM1 (SigmaCode _ _) ZeroEl um aU vt r = tt
  symM1 (SigmaCode _ _) (SucEl _) um aU vt r = tt
  symM1 (SigmaCode _ _) (PairEl _ _) um aU vt r = tt

  transM1 : {n : Num} {G : Ctx n} {M1 M2 M3 T : Expr n} (u a : FinEl) -> FinMem u a -> FinMem a UCode -> RT1 G T T a ->
    RM1 G M1 M2 T u a -> RM1 G M2 M3 T u a -> RM1 G M1 M3 T u a
  transM1 Bot a um aU vt r1 r2 = tt
  transM1 UCode Bot um aU vt r1 r2 = tt
  transM1 {G = G} UCode UCode um aU vt r1 r2 = fst r1 , transT1 {G = G} UCode um (snd r1) (realignU (\ X Y -> RT1 _ X Y UCode) (fst r2) (fst r1) (snd r2))
  transM1 UCode (FunEl _) um aU vt r1 r2 = tt
  transM1 UCode ZeroEl um aU vt r1 r2 = tt
  transM1 UCode (SucEl _) um aU vt r1 r2 = tt
  transM1 UCode (PairEl _ _) um aU vt r1 r2 = tt
  transM1 (FunEl _) Bot um aU vt r1 r2 = tt
  transM1 (FunEl g) UCode um aU vt r1 r2 = Empty-elim (snd r1)
  transM1 (FunEl _) (FunEl _) um aU vt r1 r2 = tt
  transM1 (FunEl g) (PiCode b f) um aU vt r1 r2 = PM.transPi (piU b f aU) (funU g b f um) vt r1 r2
  transM1 (FunEl _) ZeroEl um aU vt r1 r2 = tt
  transM1 (FunEl _) (SucEl _) um aU vt r1 r2 = tt
  transM1 (FunEl _) (PairEl _ _) um aU vt r1 r2 = tt
  transM1 (PiCode _ _) Bot um aU vt r1 r2 = tt
  transM1 {G = G} (PiCode pb pf) UCode um aU vt r1 r2 = fst r1 , transT1 {G = G} (PiCode pb pf) um (snd r1) (realignU (\ X Y -> RT1 _ X Y (PiCode pb pf)) (fst r2) (fst r1) (snd r2))
  transM1 (PiCode _ _) (FunEl _) um aU vt r1 r2 = tt
  transM1 (PiCode _ _) ZeroEl um aU vt r1 r2 = tt
  transM1 (PiCode _ _) (SucEl _) um aU vt r1 r2 = tt
  transM1 (PiCode _ _) (PairEl _ _) um aU vt r1 r2 = tt
  transM1 NatCode Bot um aU vt r1 r2 = tt
  transM1 {G = G} NatCode UCode um aU vt r1 r2 = fst r1 , transT1 {G = G} NatCode um (snd r1) (realignU (\ X Y -> RT1 _ X Y NatCode) (fst r2) (fst r1) (snd r2))
  transM1 NatCode (FunEl _) um aU vt r1 r2 = tt
  transM1 NatCode ZeroEl um aU vt r1 r2 = tt
  transM1 NatCode (SucEl _) um aU vt r1 r2 = tt
  transM1 NatCode (PairEl _ _) um aU vt r1 r2 = tt
  transM1 ZeroEl Bot um aU vt r1 r2 = tt
  transM1 ZeroEl UCode um aU vt r1 r2 = Empty-elim (snd r1)
  transM1 ZeroEl (FunEl _) um aU vt r1 r2 = tt
  transM1 ZeroEl NatCode um aU vt r1 r2 = fst r1 , (fst (snd r1) , snd (snd r2))
  transM1 ZeroEl ZeroEl um aU vt r1 r2 = tt
  transM1 ZeroEl (SucEl _) um aU vt r1 r2 = tt
  transM1 ZeroEl (PairEl _ _) um aU vt r1 r2 = tt
  transM1 (SucEl _) Bot um aU vt r1 r2 = tt
  transM1 (SucEl v) UCode um aU vt r1 r2 = Empty-elim (snd r1)
  transM1 (SucEl _) (FunEl _) um aU vt r1 r2 = tt
  transM1 (SucEl v) NatCode um aU vt r1 r2 = fst r1 , NM.transS (sucNat-to v um) (iNat (fst r1)) (snd r1) (snd r2)
  transM1 (SucEl _) ZeroEl um aU vt r1 r2 = tt
  transM1 (SucEl _) (SucEl _) um aU vt r1 r2 = tt
  transM1 (SucEl _) (PairEl _ _) um aU vt r1 r2 = tt
  transM1 (PairEl _ _) Bot um aU vt r1 r2 = tt
  transM1 (PairEl x1 x2) UCode um aU vt r1 r2 = Empty-elim (snd r1)
  transM1 (PairEl _ _) (FunEl _) um aU vt r1 r2 = tt
  transM1 (PairEl _ _) ZeroEl um aU vt r1 r2 = tt
  transM1 (PairEl _ _) (SucEl _) um aU vt r1 r2 = tt
  transM1 (PairEl _ _) (PairEl _ _) um aU vt r1 r2 = tt
  transM1 (PairEl x1 x2) (SigmaCode b f) um aU vt r1 r2 = SM.transSig (sigU b f aU) (pairU x1 x2 b f um) vt r1 r2
  transM1 (SigmaCode _ _) Bot um aU vt r1 r2 = tt
  transM1 {G = G} (SigmaCode sb sf) UCode um aU vt r1 r2 = fst r1 , transT1 {G = G} (SigmaCode sb sf) um (snd r1) (realignU (\ X Y -> RT1 _ X Y (SigmaCode sb sf)) (fst r2) (fst r1) (snd r2))
  transM1 (SigmaCode _ _) (FunEl _) um aU vt r1 r2 = tt
  transM1 (SigmaCode _ _) ZeroEl um aU vt r1 r2 = tt
  transM1 (SigmaCode _ _) (SucEl _) um aU vt r1 r2 = tt
  transM1 (SigmaCode _ _) (PairEl _ _) um aU vt r1 r2 = tt

  convM1 : {n : Num} {G : Ctx n} {M M' T T' : Expr n} (u a : FinEl) -> FinMem u a -> FinMem a UCode -> RT1 G T T' a ->
    RM1 G M M' T u a -> RM1 G M M' T' u a
  convM1 Bot a um aU vt r = tt
  convM1 UCode Bot um aU vt r = tt
  convM1 UCode UCode um aU vt r = UnivR2.wr vt , convU (\ X Y -> RT1 _ X Y UCode) vt (fst r) (snd r)
  convM1 UCode (FunEl _) um aU vt r = tt
  convM1 UCode ZeroEl um aU vt r = tt
  convM1 UCode (SucEl _) um aU vt r = tt
  convM1 UCode (PairEl _ _) um aU vt r = tt
  convM1 (FunEl _) Bot um aU vt r = tt
  convM1 (FunEl g) UCode um aU vt r = Empty-elim (snd r)
  convM1 (FunEl _) (FunEl _) um aU vt r = tt
  convM1 (FunEl g) (PiCode b f) um aU vt r = PM.convPi (piU b f aU) (funU g b f um) vt r
  convM1 (FunEl _) ZeroEl um aU vt r = tt
  convM1 (FunEl _) (SucEl _) um aU vt r = tt
  convM1 (FunEl _) (PairEl _ _) um aU vt r = tt
  convM1 (PiCode _ _) Bot um aU vt r = tt
  convM1 (PiCode pb pf) UCode um aU vt r = UnivR2.wr vt , convU (\ X Y -> RT1 _ X Y (PiCode pb pf)) vt (fst r) (snd r)
  convM1 (PiCode _ _) (FunEl _) um aU vt r = tt
  convM1 (PiCode _ _) ZeroEl um aU vt r = tt
  convM1 (PiCode _ _) (SucEl _) um aU vt r = tt
  convM1 (PiCode _ _) (PairEl _ _) um aU vt r = tt
  convM1 NatCode Bot um aU vt r = tt
  convM1 NatCode UCode um aU vt r = UnivR2.wr vt , convU (\ X Y -> RT1 _ X Y NatCode) vt (fst r) (snd r)
  convM1 NatCode (FunEl _) um aU vt r = tt
  convM1 NatCode ZeroEl um aU vt r = tt
  convM1 NatCode (SucEl _) um aU vt r = tt
  convM1 NatCode (PairEl _ _) um aU vt r = tt
  convM1 ZeroEl Bot um aU vt r = tt
  convM1 ZeroEl UCode um aU vt r = Empty-elim (snd r)
  convM1 ZeroEl (FunEl _) um aU vt r = tt
  convM1 ZeroEl NatCode um aU vt r = snd (snd vt) , snd r
  convM1 ZeroEl ZeroEl um aU vt r = tt
  convM1 ZeroEl (SucEl _) um aU vt r = tt
  convM1 ZeroEl (PairEl _ _) um aU vt r = tt
  convM1 (SucEl _) Bot um aU vt r = tt
  convM1 (SucEl v) UCode um aU vt r = Empty-elim (snd r)
  convM1 (SucEl _) (FunEl _) um aU vt r = tt
  convM1 (SucEl v) NatCode um aU vt r = snd (snd vt) , snd r
  convM1 (SucEl _) ZeroEl um aU vt r = tt
  convM1 (SucEl _) (SucEl _) um aU vt r = tt
  convM1 (SucEl _) (PairEl _ _) um aU vt r = tt
  convM1 (PairEl _ _) Bot um aU vt r = tt
  convM1 (PairEl x1 x2) UCode um aU vt r = Empty-elim (snd r)
  convM1 (PairEl _ _) (FunEl _) um aU vt r = tt
  convM1 (PairEl _ _) ZeroEl um aU vt r = tt
  convM1 (PairEl _ _) (SucEl _) um aU vt r = tt
  convM1 (PairEl _ _) (PairEl _ _) um aU vt r = tt
  convM1 (PairEl x1 x2) (SigmaCode b f) um aU vt r = SM.convSig (sigU b f aU) (pairU x1 x2 b f um) vt r
  convM1 (SigmaCode _ _) Bot um aU vt r = tt
  convM1 (SigmaCode sb sf) UCode um aU vt r = UnivR2.wr vt , convU (\ X Y -> RT1 _ X Y (SigmaCode sb sf)) vt (fst r) (snd r)
  convM1 (SigmaCode _ _) (FunEl _) um aU vt r = tt
  convM1 (SigmaCode _ _) ZeroEl um aU vt r = tt
  convM1 (SigmaCode _ _) (SucEl _) um aU vt r = tt
  convM1 (SigmaCode _ _) (PairEl _ _) um aU vt r = tt

  expM1 : {n : Num} {G : Ctx n} {M M1 M' T : Expr n} (u a : FinEl) -> FinMem u a -> FinMem a UCode ->
    AR M M1 -> ConvTm G M M1 T -> RT1 G T T a -> RM1 G M1 M' T u a -> RM1 G M M' T u a
  expM1 Bot a um aU hr q vt r = tt
  expM1 UCode Bot um aU hr q vt r = tt
  expM1 {G = G} UCode UCode um aU hr q vt r = fst r , expT1 {G = G} UCode (decHR (fst r) hr) (decTE (fst r) q) (snd r)
  expM1 UCode (FunEl _) um aU hr q vt r = tt
  expM1 UCode ZeroEl um aU hr q vt r = tt
  expM1 UCode (SucEl _) um aU hr q vt r = tt
  expM1 UCode (PairEl _ _) um aU hr q vt r = tt
  expM1 (FunEl _) Bot um aU hr q vt r = tt
  expM1 (FunEl g) UCode um aU hr q vt r = Empty-elim (snd r)
  expM1 (FunEl _) (FunEl _) um aU hr q vt r = tt
  expM1 (FunEl g) (PiCode b f) um aU hr q vt r = PM.expPi (piU b f aU) (funU g b f um) vt hr q r
  expM1 (FunEl _) ZeroEl um aU hr q vt r = tt
  expM1 (FunEl _) (SucEl _) um aU hr q vt r = tt
  expM1 (FunEl _) (PairEl _ _) um aU hr q vt r = tt
  expM1 (PiCode _ _) Bot um aU hr q vt r = tt
  expM1 {G = G} (PiCode pb pf) UCode um aU hr q vt r = fst r , expT1 {G = G} (PiCode pb pf) (decHR (fst r) hr) (decTE (fst r) q) (snd r)
  expM1 (PiCode _ _) (FunEl _) um aU hr q vt r = tt
  expM1 (PiCode _ _) ZeroEl um aU hr q vt r = tt
  expM1 (PiCode _ _) (SucEl _) um aU hr q vt r = tt
  expM1 (PiCode _ _) (PairEl _ _) um aU hr q vt r = tt
  expM1 NatCode Bot um aU hr q vt r = tt
  expM1 {G = G} NatCode UCode um aU hr q vt r = fst r , expT1 {G = G} NatCode (decHR (fst r) hr) (decTE (fst r) q) (snd r)
  expM1 NatCode (FunEl _) um aU hr q vt r = tt
  expM1 NatCode ZeroEl um aU hr q vt r = tt
  expM1 NatCode (SucEl _) um aU hr q vt r = tt
  expM1 NatCode (PairEl _ _) um aU hr q vt r = tt
  expM1 ZeroEl Bot um aU hr q vt r = tt
  expM1 ZeroEl UCode um aU hr q vt r = Empty-elim (snd r)
  expM1 ZeroEl (FunEl _) um aU hr q vt r = tt
  expM1 ZeroEl NatCode um aU hr q vt r = fst r , (expZ hr (conv-conv q (fst r)) (fst (snd r)) , snd (snd r))
  expM1 ZeroEl ZeroEl um aU hr q vt r = tt
  expM1 ZeroEl (SucEl _) um aU hr q vt r = tt
  expM1 ZeroEl (PairEl _ _) um aU hr q vt r = tt
  expM1 (SucEl _) Bot um aU hr q vt r = tt
  expM1 (SucEl v) UCode um aU hr q vt r = Empty-elim (snd r)
  expM1 (SucEl _) (FunEl _) um aU hr q vt r = tt
  expM1 (SucEl v) NatCode um aU hr q vt r = fst r , NM.expS hr (conv-conv q (fst r)) (snd r)
  expM1 (SucEl _) ZeroEl um aU hr q vt r = tt
  expM1 (SucEl _) (SucEl _) um aU hr q vt r = tt
  expM1 (SucEl _) (PairEl _ _) um aU hr q vt r = tt
  expM1 (PairEl _ _) Bot um aU hr q vt r = tt
  expM1 (PairEl x1 x2) UCode um aU hr q vt r = Empty-elim (snd r)
  expM1 (PairEl _ _) (FunEl _) um aU hr q vt r = tt
  expM1 (PairEl _ _) ZeroEl um aU hr q vt r = tt
  expM1 (PairEl _ _) (SucEl _) um aU hr q vt r = tt
  expM1 (PairEl _ _) (PairEl _ _) um aU hr q vt r = tt
  expM1 (PairEl x1 x2) (SigmaCode b f) um aU hr q vt r = SM.expSig (sigU b f aU) (pairU x1 x2 b f um) vt hr q r
  expM1 (SigmaCode _ _) Bot um aU hr q vt r = tt
  expM1 {G = G} (SigmaCode sb sf) UCode um aU hr q vt r = fst r , expT1 {G = G} (SigmaCode sb sf) (decHR (fst r) hr) (decTE (fst r) q) (snd r)
  expM1 (SigmaCode _ _) (FunEl _) um aU hr q vt r = tt
  expM1 (SigmaCode _ _) ZeroEl um aU hr q vt r = tt
  expM1 (SigmaCode _ _) (SucEl _) um aU hr q vt r = tt
  expM1 (SigmaCode _ _) (PairEl _ _) um aU hr q vt r = tt

  expM1' : {n : Num} {G : Ctx n} {M M' M1' T : Expr n} (u a : FinEl) -> FinMem u a -> FinMem a UCode ->
    AR M' M1' -> ConvTm G M' M1' T -> RT1 G T T a -> RM1 G M M1' T u a -> RM1 G M M' T u a
  expM1' Bot a um aU hr q vt r = tt
  expM1' UCode Bot um aU hr q vt r = tt
  expM1' {G = G} UCode UCode um aU hr q vt r = fst r , expT1' {G = G} UCode (decHR (fst r) hr) (decTE (fst r) q) (snd r)
  expM1' UCode (FunEl _) um aU hr q vt r = tt
  expM1' UCode ZeroEl um aU hr q vt r = tt
  expM1' UCode (SucEl _) um aU hr q vt r = tt
  expM1' UCode (PairEl _ _) um aU hr q vt r = tt
  expM1' (FunEl _) Bot um aU hr q vt r = tt
  expM1' (FunEl g) UCode um aU hr q vt r = Empty-elim (snd r)
  expM1' (FunEl _) (FunEl _) um aU hr q vt r = tt
  expM1' (FunEl g) (PiCode b f) um aU hr q vt r = PM.expPi' (piU b f aU) (funU g b f um) vt hr q r
  expM1' (FunEl _) ZeroEl um aU hr q vt r = tt
  expM1' (FunEl _) (SucEl _) um aU hr q vt r = tt
  expM1' (FunEl _) (PairEl _ _) um aU hr q vt r = tt
  expM1' (PiCode _ _) Bot um aU hr q vt r = tt
  expM1' {G = G} (PiCode pb pf) UCode um aU hr q vt r = fst r , expT1' {G = G} (PiCode pb pf) (decHR (fst r) hr) (decTE (fst r) q) (snd r)
  expM1' (PiCode _ _) (FunEl _) um aU hr q vt r = tt
  expM1' (PiCode _ _) ZeroEl um aU hr q vt r = tt
  expM1' (PiCode _ _) (SucEl _) um aU hr q vt r = tt
  expM1' (PiCode _ _) (PairEl _ _) um aU hr q vt r = tt
  expM1' NatCode Bot um aU hr q vt r = tt
  expM1' {G = G} NatCode UCode um aU hr q vt r = fst r , expT1' {G = G} NatCode (decHR (fst r) hr) (decTE (fst r) q) (snd r)
  expM1' NatCode (FunEl _) um aU hr q vt r = tt
  expM1' NatCode ZeroEl um aU hr q vt r = tt
  expM1' NatCode (SucEl _) um aU hr q vt r = tt
  expM1' NatCode (PairEl _ _) um aU hr q vt r = tt
  expM1' ZeroEl Bot um aU hr q vt r = tt
  expM1' ZeroEl UCode um aU hr q vt r = Empty-elim (snd r)
  expM1' ZeroEl (FunEl _) um aU hr q vt r = tt
  expM1' ZeroEl NatCode um aU hr q vt r = fst r , (fst (snd r) , expZ hr (conv-conv q (fst r)) (snd (snd r)))
  expM1' ZeroEl ZeroEl um aU hr q vt r = tt
  expM1' ZeroEl (SucEl _) um aU hr q vt r = tt
  expM1' ZeroEl (PairEl _ _) um aU hr q vt r = tt
  expM1' (SucEl _) Bot um aU hr q vt r = tt
  expM1' (SucEl v) UCode um aU hr q vt r = Empty-elim (snd r)
  expM1' (SucEl _) (FunEl _) um aU hr q vt r = tt
  expM1' (SucEl v) NatCode um aU hr q vt r = fst r , NM.expS' hr (conv-conv q (fst r)) (snd r)
  expM1' (SucEl _) ZeroEl um aU hr q vt r = tt
  expM1' (SucEl _) (SucEl _) um aU hr q vt r = tt
  expM1' (SucEl _) (PairEl _ _) um aU hr q vt r = tt
  expM1' (PairEl _ _) Bot um aU hr q vt r = tt
  expM1' (PairEl x1 x2) UCode um aU hr q vt r = Empty-elim (snd r)
  expM1' (PairEl _ _) (FunEl _) um aU hr q vt r = tt
  expM1' (PairEl _ _) ZeroEl um aU hr q vt r = tt
  expM1' (PairEl _ _) (SucEl _) um aU hr q vt r = tt
  expM1' (PairEl _ _) (PairEl _ _) um aU hr q vt r = tt
  expM1' (PairEl x1 x2) (SigmaCode b f) um aU hr q vt r = SM.expSig' (sigU b f aU) (pairU x1 x2 b f um) vt hr q r
  expM1' (SigmaCode _ _) Bot um aU hr q vt r = tt
  expM1' {G = G} (SigmaCode sb sf) UCode um aU hr q vt r = fst r , expT1' {G = G} (SigmaCode sb sf) (decHR (fst r) hr) (decTE (fst r) q) (snd r)
  expM1' (SigmaCode _ _) (FunEl _) um aU hr q vt r = tt
  expM1' (SigmaCode _ _) ZeroEl um aU hr q vt r = tt
  expM1' (SigmaCode _ _) (SucEl _) um aU hr q vt r = tt
  expM1' (SigmaCode _ _) (PairEl _ _) um aU hr q vt r = tt

  restrM1 : {n : Num} {G : Ctx n} {M M' T : Expr n} (u u' a : FinEl) -> LeCode u' u ->
    FinMem u' a -> FinMem u a -> FinMem a UCode -> RT1 G T T a -> RM1 G M M' T u a -> RM1 G M M' T u' a
  restrM1 u Bot a le u'm um aU vt r = tt
  restrM1 u UCode Bot le u'm um aU vt r = tt
  restrM1 u UCode (FunEl _) le u'm um aU vt r = tt
  restrM1 u UCode ZeroEl le u'm um aU vt r = tt
  restrM1 u UCode (SucEl _) le u'm um aU vt r = tt
  restrM1 u UCode (PairEl _ _) le u'm um aU vt r = tt
  restrM1 {G = G} UCode UCode UCode le u'm um aU vt r = fst r , downT1 {G = G} UCode UCode le u'm um (snd r)
  restrM1 u (FunEl _) Bot le u'm um aU vt r = tt
  restrM1 u (FunEl _) (FunEl _) le u'm um aU vt r = tt
  restrM1 u (FunEl _) ZeroEl le u'm um aU vt r = tt
  restrM1 u (FunEl _) (SucEl _) le u'm um aU vt r = tt
  restrM1 u (FunEl _) (PairEl _ _) le u'm um aU vt r = tt
  restrM1 (FunEl g) (FunEl g') (PiCode b f) le u'm um aU vt r = PM.restrPi le (piU b f aU) (funU g b f um) (funU g' b f u'm) vt r
  restrM1 u (PiCode _ _) Bot le u'm um aU vt r = tt
  restrM1 u (PiCode _ _) (FunEl _) le u'm um aU vt r = tt
  restrM1 u (PiCode _ _) ZeroEl le u'm um aU vt r = tt
  restrM1 u (PiCode _ _) (SucEl _) le u'm um aU vt r = tt
  restrM1 u (PiCode _ _) (PairEl _ _) le u'm um aU vt r = tt
  restrM1 {G = G} (PiCode pb pf) (PiCode qb qf) UCode le u'm um aU vt r = fst r , downT1 {G = G} (PiCode qb qf) (PiCode pb pf) le u'm um (snd r)
  restrM1 u NatCode Bot le u'm um aU vt r = tt
  restrM1 u NatCode (FunEl _) le u'm um aU vt r = tt
  restrM1 u NatCode ZeroEl le u'm um aU vt r = tt
  restrM1 u NatCode (SucEl _) le u'm um aU vt r = tt
  restrM1 u NatCode (PairEl _ _) le u'm um aU vt r = tt
  restrM1 {G = G} NatCode NatCode UCode le u'm um aU vt r = fst r , downT1 {G = G} NatCode NatCode le u'm um (snd r)
  restrM1 u ZeroEl Bot le u'm um aU vt r = tt
  restrM1 u ZeroEl (FunEl _) le u'm um aU vt r = tt
  restrM1 u ZeroEl ZeroEl le u'm um aU vt r = tt
  restrM1 u ZeroEl (SucEl _) le u'm um aU vt r = tt
  restrM1 u ZeroEl (PairEl _ _) le u'm um aU vt r = tt
  restrM1 ZeroEl ZeroEl NatCode le u'm um aU vt r = r
  restrM1 u (SucEl _) Bot le u'm um aU vt r = tt
  restrM1 u (SucEl _) (FunEl _) le u'm um aU vt r = tt
  restrM1 u (SucEl _) ZeroEl le u'm um aU vt r = tt
  restrM1 u (SucEl _) (SucEl _) le u'm um aU vt r = tt
  restrM1 u (SucEl _) (PairEl _ _) le u'm um aU vt r = tt
  restrM1 (SucEl v) (SucEl v') NatCode le u'm um aU vt r = fst r , NM.restrS le (sucNat-to v' u'm) (sucNat-to v um) (iNat (fst r)) (snd r)
  restrM1 u (PairEl _ _) Bot le u'm um aU vt r = tt
  restrM1 u (PairEl _ _) (FunEl _) le u'm um aU vt r = tt
  restrM1 u (PairEl _ _) ZeroEl le u'm um aU vt r = tt
  restrM1 u (PairEl _ _) (SucEl _) le u'm um aU vt r = tt
  restrM1 u (PairEl _ _) (PairEl _ _) le u'm um aU vt r = tt
  restrM1 (PairEl x1 x2) (PairEl y1 y2) (SigmaCode b f) le u'm um aU vt r =
    SM.restrSig (dfst le) (dsnd le) (sigU b f aU) (pairU x1 x2 b f um) (pairU y1 y2 b f u'm) vt r
  restrM1 u (SigmaCode _ _) Bot le u'm um aU vt r = tt
  restrM1 u (SigmaCode _ _) (FunEl _) le u'm um aU vt r = tt
  restrM1 u (SigmaCode _ _) ZeroEl le u'm um aU vt r = tt
  restrM1 u (SigmaCode _ _) (SucEl _) le u'm um aU vt r = tt
  restrM1 u (SigmaCode _ _) (PairEl _ _) le u'm um aU vt r = tt
  restrM1 {G = G} (SigmaCode sb sf) (SigmaCode tb tf) UCode le u'm um aU vt r = fst r , downT1 {G = G} (SigmaCode tb tf) (SigmaCode sb sf) le u'm um (snd r)

  downM1 : {n : Num} {G : Ctx n} {M M' T : Expr n} (u a0 a1 : FinEl) -> LeCode a0 a1 ->
    FinMem u a0 -> FinMem a0 UCode -> FinMem a1 UCode -> RT1 G T T a1 -> RM1 G M M' T u a1 -> RM1 G M M' T u a0
  downM1 Bot a0 a1 le um a0U a1U vt r = tt
  downM1 UCode Bot a1 le um a0U a1U vt r = tt
  downM1 UCode (FunEl _) a1 le um a0U a1U vt r = tt
  downM1 UCode ZeroEl a1 le um a0U a1U vt r = tt
  downM1 UCode (SucEl _) a1 le um a0U a1U vt r = tt
  downM1 UCode (PairEl _ _) a1 le um a0U a1U vt r = tt
  downM1 UCode UCode UCode le um a0U a1U vt r = r
  downM1 UCode NatCode NatCode le um a0U a1U vt r = r
  downM1 (FunEl _) Bot a1 le um a0U a1U vt r = tt
  downM1 (FunEl _) (FunEl _) a1 le um a0U a1U vt r = tt
  downM1 (FunEl _) ZeroEl a1 le um a0U a1U vt r = tt
  downM1 (FunEl _) (SucEl _) a1 le um a0U a1U vt r = tt
  downM1 (FunEl _) (PairEl _ _) a1 le um a0U a1U vt r = tt
  downM1 (FunEl _) UCode UCode le um a0U a1U vt r = r
  downM1 (FunEl _) NatCode NatCode le um a0U a1U vt r = r
  downM1 (PiCode _ _) Bot a1 le um a0U a1U vt r = tt
  downM1 (PiCode _ _) (FunEl _) a1 le um a0U a1U vt r = tt
  downM1 (PiCode _ _) ZeroEl a1 le um a0U a1U vt r = tt
  downM1 (PiCode _ _) (SucEl _) a1 le um a0U a1U vt r = tt
  downM1 (PiCode _ _) (PairEl _ _) a1 le um a0U a1U vt r = tt
  downM1 (PiCode _ _) UCode UCode le um a0U a1U vt r = r
  downM1 (PiCode _ _) NatCode NatCode le um a0U a1U vt r = r
  downM1 NatCode Bot a1 le um a0U a1U vt r = tt
  downM1 NatCode (FunEl _) a1 le um a0U a1U vt r = tt
  downM1 NatCode ZeroEl a1 le um a0U a1U vt r = tt
  downM1 NatCode (SucEl _) a1 le um a0U a1U vt r = tt
  downM1 NatCode (PairEl _ _) a1 le um a0U a1U vt r = tt
  downM1 NatCode UCode UCode le um a0U a1U vt r = r
  downM1 NatCode NatCode NatCode le um a0U a1U vt r = r
  downM1 ZeroEl Bot a1 le um a0U a1U vt r = tt
  downM1 ZeroEl (FunEl _) a1 le um a0U a1U vt r = tt
  downM1 ZeroEl ZeroEl a1 le um a0U a1U vt r = tt
  downM1 ZeroEl (SucEl _) a1 le um a0U a1U vt r = tt
  downM1 ZeroEl (PairEl _ _) a1 le um a0U a1U vt r = tt
  downM1 ZeroEl UCode UCode le um a0U a1U vt r = r
  downM1 ZeroEl NatCode NatCode le um a0U a1U vt r = r
  downM1 (SucEl _) Bot a1 le um a0U a1U vt r = tt
  downM1 (SucEl _) (FunEl _) a1 le um a0U a1U vt r = tt
  downM1 (SucEl _) ZeroEl a1 le um a0U a1U vt r = tt
  downM1 (SucEl _) (SucEl _) a1 le um a0U a1U vt r = tt
  downM1 (SucEl _) (PairEl _ _) a1 le um a0U a1U vt r = tt
  downM1 (SucEl _) UCode UCode le um a0U a1U vt r = r
  downM1 (SucEl _) NatCode NatCode le um a0U a1U vt r = r
  downM1 (PairEl _ _) Bot a1 le um a0U a1U vt r = tt
  downM1 (PairEl _ _) (FunEl _) a1 le um a0U a1U vt r = tt
  downM1 (PairEl _ _) ZeroEl a1 le um a0U a1U vt r = tt
  downM1 (PairEl _ _) (SucEl _) a1 le um a0U a1U vt r = tt
  downM1 (PairEl _ _) (PairEl _ _) a1 le um a0U a1U vt r = tt
  downM1 (PairEl _ _) UCode UCode le um a0U a1U vt r = r
  downM1 (PairEl _ _) NatCode NatCode le um a0U a1U vt r = r
  downM1 (SigmaCode _ _) Bot a1 le um a0U a1U vt r = tt
  downM1 (SigmaCode _ _) (FunEl _) a1 le um a0U a1U vt r = tt
  downM1 (SigmaCode _ _) ZeroEl a1 le um a0U a1U vt r = tt
  downM1 (SigmaCode _ _) (SucEl _) a1 le um a0U a1U vt r = tt
  downM1 (SigmaCode _ _) (PairEl _ _) a1 le um a0U a1U vt r = tt
  downM1 (SigmaCode _ _) UCode UCode le um a0U a1U vt r = r
  downM1 (SigmaCode _ _) NatCode NatCode le um a0U a1U vt r = r
  downM1 (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le um a0U a1U vt r =
    PM.downPi (dfst le) (dsnd le) (piU b0 f0 a0U) (piU b1 f1 a1U) (funU g b0 f0 um) vt r
  downM1 (PairEl x1 x2) (SigmaCode b0 f0) (SigmaCode b1 f1) le um a0U a1U vt r =
    SM.downSig (dfst le) (dsnd le) (sigU b0 f0 a0U) (sigU b1 f1 a1U) (pairU x1 x2 b0 f0 um) vt r

  upM1 : {n : Num} {G : Ctx n} {M M' T : Expr n} (u a0 a1 : FinEl) -> LeCode a0 a1 ->
    FinMem u a0 -> FinMem a0 UCode -> FinMem a1 UCode -> RT1 G T T a1 -> RM1 G M M' T u a0 -> RM1 G M M' T u a1
  upM1 Bot a0 a1 le um a0U a1U vt r = tt
  upM1 UCode a0 Bot le um a0U a1U vt r = tt
  upM1 UCode a0 (FunEl _) le um a0U a1U vt r = tt
  upM1 UCode a0 ZeroEl le um a0U a1U vt r = tt
  upM1 UCode a0 (SucEl _) le um a0U a1U vt r = tt
  upM1 UCode a0 (PairEl _ _) le um a0U a1U vt r = tt
  upM1 UCode UCode UCode le um a0U a1U vt r = r
  upM1 UCode NatCode NatCode le um a0U a1U vt r = r
  upM1 (FunEl _) a0 Bot le um a0U a1U vt r = tt
  upM1 (FunEl _) a0 (FunEl _) le um a0U a1U vt r = tt
  upM1 (FunEl _) a0 ZeroEl le um a0U a1U vt r = tt
  upM1 (FunEl _) a0 (SucEl _) le um a0U a1U vt r = tt
  upM1 (FunEl _) a0 (PairEl _ _) le um a0U a1U vt r = tt
  upM1 (FunEl _) UCode UCode le um a0U a1U vt r = r
  upM1 (FunEl _) NatCode NatCode le um a0U a1U vt r = r
  upM1 (PiCode _ _) a0 Bot le um a0U a1U vt r = tt
  upM1 (PiCode _ _) a0 (FunEl _) le um a0U a1U vt r = tt
  upM1 (PiCode _ _) a0 ZeroEl le um a0U a1U vt r = tt
  upM1 (PiCode _ _) a0 (SucEl _) le um a0U a1U vt r = tt
  upM1 (PiCode _ _) a0 (PairEl _ _) le um a0U a1U vt r = tt
  upM1 (PiCode _ _) UCode UCode le um a0U a1U vt r = r
  upM1 (PiCode _ _) NatCode NatCode le um a0U a1U vt r = r
  upM1 NatCode a0 Bot le um a0U a1U vt r = tt
  upM1 NatCode a0 (FunEl _) le um a0U a1U vt r = tt
  upM1 NatCode a0 ZeroEl le um a0U a1U vt r = tt
  upM1 NatCode a0 (SucEl _) le um a0U a1U vt r = tt
  upM1 NatCode a0 (PairEl _ _) le um a0U a1U vt r = tt
  upM1 NatCode UCode UCode le um a0U a1U vt r = r
  upM1 NatCode NatCode NatCode le um a0U a1U vt r = r
  upM1 ZeroEl a0 Bot le um a0U a1U vt r = tt
  upM1 ZeroEl a0 (FunEl _) le um a0U a1U vt r = tt
  upM1 ZeroEl a0 ZeroEl le um a0U a1U vt r = tt
  upM1 ZeroEl a0 (SucEl _) le um a0U a1U vt r = tt
  upM1 ZeroEl a0 (PairEl _ _) le um a0U a1U vt r = tt
  upM1 ZeroEl UCode UCode le um a0U a1U vt r = r
  upM1 ZeroEl NatCode NatCode le um a0U a1U vt r = r
  upM1 (SucEl _) a0 Bot le um a0U a1U vt r = tt
  upM1 (SucEl _) a0 (FunEl _) le um a0U a1U vt r = tt
  upM1 (SucEl _) a0 ZeroEl le um a0U a1U vt r = tt
  upM1 (SucEl _) a0 (SucEl _) le um a0U a1U vt r = tt
  upM1 (SucEl _) a0 (PairEl _ _) le um a0U a1U vt r = tt
  upM1 (SucEl _) UCode UCode le um a0U a1U vt r = r
  upM1 (SucEl _) NatCode NatCode le um a0U a1U vt r = r
  upM1 (PairEl _ _) a0 Bot le um a0U a1U vt r = tt
  upM1 (PairEl _ _) a0 (FunEl _) le um a0U a1U vt r = tt
  upM1 (PairEl _ _) a0 ZeroEl le um a0U a1U vt r = tt
  upM1 (PairEl _ _) a0 (SucEl _) le um a0U a1U vt r = tt
  upM1 (PairEl _ _) a0 (PairEl _ _) le um a0U a1U vt r = tt
  upM1 (PairEl _ _) UCode UCode le um a0U a1U vt r = r
  upM1 (PairEl _ _) NatCode NatCode le um a0U a1U vt r = r
  upM1 (SigmaCode _ _) a0 Bot le um a0U a1U vt r = tt
  upM1 (SigmaCode _ _) a0 (FunEl _) le um a0U a1U vt r = tt
  upM1 (SigmaCode _ _) a0 ZeroEl le um a0U a1U vt r = tt
  upM1 (SigmaCode _ _) a0 (SucEl _) le um a0U a1U vt r = tt
  upM1 (SigmaCode _ _) a0 (PairEl _ _) le um a0U a1U vt r = tt
  upM1 (SigmaCode _ _) UCode UCode le um a0U a1U vt r = r
  upM1 (SigmaCode _ _) NatCode NatCode le um a0U a1U vt r = r
  upM1 UCode Bot UCode le () a0U a1U vt r
  upM1 UCode Bot NatCode le () a0U a1U vt r
  upM1 UCode Bot (PiCode _ _) le () a0U a1U vt r
  upM1 UCode Bot (SigmaCode _ _) le () a0U a1U vt r
  upM1 UCode (PiCode _ _) (PiCode _ _) le () a0U a1U vt r
  upM1 UCode (SigmaCode _ _) (SigmaCode _ _) le () a0U a1U vt r
  upM1 (FunEl _) Bot UCode le () a0U a1U vt r
  upM1 (FunEl _) Bot NatCode le () a0U a1U vt r
  upM1 (FunEl _) Bot (PiCode _ _) le () a0U a1U vt r
  upM1 (FunEl _) Bot (SigmaCode _ _) le () a0U a1U vt r
  upM1 (FunEl _) (SigmaCode _ _) (SigmaCode _ _) le () a0U a1U vt r
  upM1 (PiCode _ _) Bot UCode le () a0U a1U vt r
  upM1 (PiCode _ _) Bot NatCode le () a0U a1U vt r
  upM1 (PiCode _ _) Bot (PiCode _ _) le () a0U a1U vt r
  upM1 (PiCode _ _) Bot (SigmaCode _ _) le () a0U a1U vt r
  upM1 (PiCode _ _) (PiCode _ _) (PiCode _ _) le () a0U a1U vt r
  upM1 (PiCode _ _) (SigmaCode _ _) (SigmaCode _ _) le () a0U a1U vt r
  upM1 NatCode Bot UCode le () a0U a1U vt r
  upM1 NatCode Bot NatCode le () a0U a1U vt r
  upM1 NatCode Bot (PiCode _ _) le () a0U a1U vt r
  upM1 NatCode Bot (SigmaCode _ _) le () a0U a1U vt r
  upM1 NatCode (PiCode _ _) (PiCode _ _) le () a0U a1U vt r
  upM1 NatCode (SigmaCode _ _) (SigmaCode _ _) le () a0U a1U vt r
  upM1 ZeroEl Bot UCode le () a0U a1U vt r
  upM1 ZeroEl Bot NatCode le () a0U a1U vt r
  upM1 ZeroEl Bot (PiCode _ _) le () a0U a1U vt r
  upM1 ZeroEl Bot (SigmaCode _ _) le () a0U a1U vt r
  upM1 ZeroEl (PiCode _ _) (PiCode _ _) le () a0U a1U vt r
  upM1 ZeroEl (SigmaCode _ _) (SigmaCode _ _) le () a0U a1U vt r
  upM1 (SucEl _) Bot UCode le () a0U a1U vt r
  upM1 (SucEl _) Bot NatCode le () a0U a1U vt r
  upM1 (SucEl _) Bot (PiCode _ _) le () a0U a1U vt r
  upM1 (SucEl _) Bot (SigmaCode _ _) le () a0U a1U vt r
  upM1 (SucEl _) (PiCode _ _) (PiCode _ _) le () a0U a1U vt r
  upM1 (SucEl _) (SigmaCode _ _) (SigmaCode _ _) le () a0U a1U vt r
  upM1 (PairEl _ _) Bot UCode le () a0U a1U vt r
  upM1 (PairEl _ _) Bot NatCode le () a0U a1U vt r
  upM1 (PairEl _ _) Bot (PiCode _ _) le () a0U a1U vt r
  upM1 (PairEl _ _) Bot (SigmaCode _ _) le () a0U a1U vt r
  upM1 (PairEl _ _) (PiCode _ _) (PiCode _ _) le () a0U a1U vt r
  upM1 (SigmaCode _ _) Bot UCode le () a0U a1U vt r
  upM1 (SigmaCode _ _) Bot NatCode le () a0U a1U vt r
  upM1 (SigmaCode _ _) Bot (PiCode _ _) le () a0U a1U vt r
  upM1 (SigmaCode _ _) Bot (SigmaCode _ _) le () a0U a1U vt r
  upM1 (SigmaCode _ _) (PiCode _ _) (PiCode _ _) le () a0U a1U vt r
  upM1 (SigmaCode _ _) (SigmaCode _ _) (SigmaCode _ _) le () a0U a1U vt r
  upM1 (FunEl g) (PiCode b0 f0) (PiCode b1 f1) le um a0U a1U vt r =
    PM.upPi (dfst le) (dsnd le) (piU b0 f0 a0U) (piU b1 f1 a1U) (funU g b0 f0 um) vt r
  upM1 (PairEl x1 x2) (SigmaCode b0 f0) (SigmaCode b1 f1) le um a0U a1U vt r =
    SM.upSig (dfst le) (dsnd le) (sigU b0 f0 a0U) (sigU b1 f1 a1U) (pairU x1 x2 b0 f0 um) vt r

  joinM1 : {n : Num} {G : Ctx n} {M M' T : Expr n} (u1 u2 a : FinEl) -> Comp u1 u2 ->
    FinMem u1 a -> FinMem u2 a -> FinMem a UCode -> RT1 G T T a ->
    RM1 G M M' T u1 a -> RM1 G M M' T u2 a -> RM1 G M M' T (Sup u1 u2) a
  joinM1 Bot u2 a c m1 m2 aU vt r1 r2 = r2
  joinM1 UCode Bot a c m1 m2 aU vt r1 r2 = r1
  joinM1 (FunEl _) Bot a c m1 m2 aU vt r1 r2 = r1
  joinM1 (PiCode _ _) Bot a c m1 m2 aU vt r1 r2 = r1
  joinM1 NatCode Bot a c m1 m2 aU vt r1 r2 = r1
  joinM1 ZeroEl Bot a c m1 m2 aU vt r1 r2 = r1
  joinM1 (SucEl _) Bot a c m1 m2 aU vt r1 r2 = r1
  joinM1 (PairEl _ _) Bot a c m1 m2 aU vt r1 r2 = r1
  joinM1 (SigmaCode _ _) Bot a c m1 m2 aU vt r1 r2 = r1
  joinM1 UCode UCode Bot c m1 m2 aU vt r1 r2 = tt
  joinM1 UCode UCode (FunEl _) c m1 m2 aU vt r1 r2 = tt
  joinM1 UCode UCode ZeroEl c m1 m2 aU vt r1 r2 = tt
  joinM1 UCode UCode (SucEl _) c m1 m2 aU vt r1 r2 = tt
  joinM1 UCode UCode (PairEl _ _) c m1 m2 aU vt r1 r2 = tt
  joinM1 {G = G} UCode UCode UCode c m1 m2 aU vt r1 r2 = fst r1 , joinT1 {G = G} UCode UCode c m1 m2 (snd r1) (realignU (\ X Y -> RT1 _ X Y UCode) (fst r2) (fst r1) (snd r2))
  joinM1 (FunEl g1) (FunEl g2) Bot c m1 m2 aU vt r1 r2 = tt
  joinM1 (FunEl g1) (FunEl g2) (FunEl _) c m1 m2 aU vt r1 r2 = tt
  joinM1 (FunEl g1) (FunEl g2) ZeroEl c m1 m2 aU vt r1 r2 = tt
  joinM1 (FunEl g1) (FunEl g2) (SucEl _) c m1 m2 aU vt r1 r2 = tt
  joinM1 (FunEl g1) (FunEl g2) (PairEl _ _) c m1 m2 aU vt r1 r2 = tt
  joinM1 (FunEl g1) (FunEl g2) UCode c m1 m2 aU vt r1 r2 = Empty-elim (snd r1)
  joinM1 (PiCode pb1 pf1) (PiCode pb2 pf2) Bot c m1 m2 aU vt r1 r2 = tt
  joinM1 (PiCode pb1 pf1) (PiCode pb2 pf2) (FunEl _) c m1 m2 aU vt r1 r2 = tt
  joinM1 (PiCode pb1 pf1) (PiCode pb2 pf2) ZeroEl c m1 m2 aU vt r1 r2 = tt
  joinM1 (PiCode pb1 pf1) (PiCode pb2 pf2) (SucEl _) c m1 m2 aU vt r1 r2 = tt
  joinM1 (PiCode pb1 pf1) (PiCode pb2 pf2) (PairEl _ _) c m1 m2 aU vt r1 r2 = tt
  joinM1 {G = G} (PiCode pb1 pf1) (PiCode pb2 pf2) UCode c m1 m2 aU vt r1 r2 = fst r1 , joinT1 {G = G} (PiCode pb1 pf1) (PiCode pb2 pf2) c m1 m2 (snd r1) (realignU (\ X Y -> RT1 _ X Y (PiCode pb2 pf2)) (fst r2) (fst r1) (snd r2))
  joinM1 NatCode NatCode Bot c m1 m2 aU vt r1 r2 = tt
  joinM1 NatCode NatCode (FunEl _) c m1 m2 aU vt r1 r2 = tt
  joinM1 NatCode NatCode ZeroEl c m1 m2 aU vt r1 r2 = tt
  joinM1 NatCode NatCode (SucEl _) c m1 m2 aU vt r1 r2 = tt
  joinM1 NatCode NatCode (PairEl _ _) c m1 m2 aU vt r1 r2 = tt
  joinM1 {G = G} NatCode NatCode UCode c m1 m2 aU vt r1 r2 = fst r1 , joinT1 {G = G} NatCode NatCode c m1 m2 (snd r1) (realignU (\ X Y -> RT1 _ X Y NatCode) (fst r2) (fst r1) (snd r2))
  joinM1 ZeroEl ZeroEl Bot c m1 m2 aU vt r1 r2 = tt
  joinM1 ZeroEl ZeroEl (FunEl _) c m1 m2 aU vt r1 r2 = tt
  joinM1 ZeroEl ZeroEl ZeroEl c m1 m2 aU vt r1 r2 = tt
  joinM1 ZeroEl ZeroEl (SucEl _) c m1 m2 aU vt r1 r2 = tt
  joinM1 ZeroEl ZeroEl (PairEl _ _) c m1 m2 aU vt r1 r2 = tt
  joinM1 ZeroEl ZeroEl UCode c m1 m2 aU vt r1 r2 = Empty-elim (snd r1)
  joinM1 (SucEl v1) (SucEl v2) Bot c m1 m2 aU vt r1 r2 = tt
  joinM1 (SucEl v1) (SucEl v2) (FunEl _) c m1 m2 aU vt r1 r2 = tt
  joinM1 (SucEl v1) (SucEl v2) ZeroEl c m1 m2 aU vt r1 r2 = tt
  joinM1 (SucEl v1) (SucEl v2) (SucEl _) c m1 m2 aU vt r1 r2 = tt
  joinM1 (SucEl v1) (SucEl v2) (PairEl _ _) c m1 m2 aU vt r1 r2 = tt
  joinM1 (SucEl v1) (SucEl v2) UCode c m1 m2 aU vt r1 r2 = Empty-elim (snd r1)
  joinM1 (PairEl x1 x2) (PairEl y1 y2) Bot c m1 m2 aU vt r1 r2 = tt
  joinM1 (PairEl x1 x2) (PairEl y1 y2) (FunEl _) c m1 m2 aU vt r1 r2 = tt
  joinM1 (PairEl x1 x2) (PairEl y1 y2) ZeroEl c m1 m2 aU vt r1 r2 = tt
  joinM1 (PairEl x1 x2) (PairEl y1 y2) (SucEl _) c m1 m2 aU vt r1 r2 = tt
  joinM1 (PairEl x1 x2) (PairEl y1 y2) (PairEl _ _) c m1 m2 aU vt r1 r2 = tt
  joinM1 (PairEl x1 x2) (PairEl y1 y2) UCode c m1 m2 aU vt r1 r2 = Empty-elim (snd r1)
  joinM1 (SigmaCode sb1 sf1) (SigmaCode sb2 sf2) Bot c m1 m2 aU vt r1 r2 = tt
  joinM1 (SigmaCode sb1 sf1) (SigmaCode sb2 sf2) (FunEl _) c m1 m2 aU vt r1 r2 = tt
  joinM1 (SigmaCode sb1 sf1) (SigmaCode sb2 sf2) ZeroEl c m1 m2 aU vt r1 r2 = tt
  joinM1 (SigmaCode sb1 sf1) (SigmaCode sb2 sf2) (SucEl _) c m1 m2 aU vt r1 r2 = tt
  joinM1 (SigmaCode sb1 sf1) (SigmaCode sb2 sf2) (PairEl _ _) c m1 m2 aU vt r1 r2 = tt
  joinM1 {G = G} (SigmaCode sb1 sf1) (SigmaCode sb2 sf2) UCode c m1 m2 aU vt r1 r2 = fst r1 , joinT1 {G = G} (SigmaCode sb1 sf1) (SigmaCode sb2 sf2) c m1 m2 (snd r1) (realignU (\ X Y -> RT1 _ X Y (SigmaCode sb2 sf2)) (fst r2) (fst r1) (snd r2))
  joinM1 ZeroEl ZeroEl NatCode c m1 m2 aU vt r1 r2 = r1
  joinM1 (SucEl v1) (SucEl v2) NatCode c m1 m2 aU vt r1 r2 = fst r1 , NM.joinS c (sucNat-to v1 m1) (sucNat-to v2 m2) (iNat (fst r1)) (snd r1) (snd r2)
  joinM1 (FunEl g1) (FunEl g2) (PiCode b f) c m1 m2 aU vt r1 r2 =
    PM.joinPi c (piU b f aU) (funU g1 b f m1) (funU g2 b f m2)
      (funU (append g1 g2) b f (FinMem-Sup-element (FunEl g1) (FunEl g2) (PiCode b f) c (coh-from-aU (PiCode b f) aU) m1 m2)) vt r1 r2
  joinM1 (PairEl x1 x2) (PairEl y1 y2) (SigmaCode b f) c m1 m2 aU vt r1 r2 =
    SM.joinSig (dfst c) (dsnd c) (sigU b f aU) (pairU x1 x2 b f m1) (pairU y1 y2 b f m2)
      (pairU (Sup x1 y1) (Sup x2 y2) b f (FinMem-Sup-element (PairEl x1 x2) (PairEl y1 y2) (SigmaCode b f) c (coh-from-aU (SigmaCode b f) aU) m1 m2)) vt r1 r2

  result : Props (nsuc k)
  result = record
    { natV = \ iN -> (hrs-refl , tyeq-refl iN) , (hrs-refl , tyeq-refl iN) ; symT = symT1 ; transT = transT1 ; downT = downT1 ; joinT = joinT1
    ; expT = expT1 ; expT' = expT1' ; symM = symM1 ; transM = transM1 ; convM = convM1
    ; restrM = restrM1 ; downM = downM1 ; upM = upM1 ; joinM = joinM1 ; expM = expM1 ; expM' = expM1' }

props : (k : Lev) -> Props k
props nzero    = props0
props (nsuc k) = Step.result k (props k)
