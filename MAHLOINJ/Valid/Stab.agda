{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Valid/Stab.agda
--
-- Stage stability: for codes (and elements) of RANK below j, the
-- relations at stages j and (suc j) are equivalent.  Proved by
-- induction on j with generic "map" lemmas for the clause records.
------------------------------------------------------------------------

module MAHLOINJ.Valid.Stab where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Typing
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; PairEl ; SigmaCode
             ; FinFun ; nil ; cons ; Le ; max ; Le-trans ; Le-max-l ; Le-max-r) renaming (fst to dfst ; snd to dsnd)
open D using () renaming (suc to nsuc ; zero to nzero ; Nat to Lev)
open import MAHLOINJ.Domain.Kernel using (EvalFun ; RANK ; RANKFun)
open import MAHLOINJ.Domain.Rank using (RANK-EvalFun)
open import MAHLOINJ.Model.Selection using (Selection)
open import MAHLOINJ.Model.SelectionRank using (Selection-RANK-u ; Selection-RANK-v)
open import MAHLOINJ.Valid.HeadRed
open import MAHLOINJ.Valid.Stage

------------------------------------------------------------------------
-- generic maps of the clause records
------------------------------------------------------------------------

mapCT : {S : Shape} {RTa RTb : RTyT} {RMa RMb : RTmT} {n : Num} {G : Ctx n} {T T' : Expr n} {b : FinEl} {f : FinFun} ->
  ({X Y : Expr n} -> RTa G X Y b -> RTb G X Y b) ->
  ((w c : FinEl) -> Selection f w c -> {N N' A : Expr n} -> RMb G N N' A w b -> RMa G N N' A w b) ->
  ((w c : FinEl) -> Selection f w c -> {X Y : Expr n} -> RTa G X Y c -> RTb G X Y c) ->
  CodeTy S RTa RMa G T T' b f -> CodeTy S RTb RMb G T T' b f
mapCT hd hm ht r = record
  { A = A ; A' = A' ; B = B ; B' = B' ; rT = rT ; rT' = rT' ; tT = tT ; tT' = tT'
  ; iA = iA ; iB = iB ; iA' = iA' ; iB' = iB' ; eA = eA ; eB = eB
  ; dom = hd dom
  ; cod = \ w c sel N N' cv rm -> ht w c sel (cod w c sel N N' cv (hm w c sel rm)) }
  where open CodeTy r

mapPi : {RMa RMb : RTmT} {n : Num} {G : Ctx n} {M M' T : Expr n} {g : FinFun} {b : FinEl} {f : FinFun} ->
  ((w v : FinEl) -> Selection g w v -> {N N' A : Expr n} -> RMb G N N' A w b -> RMa G N N' A w b) ->
  ((w v : FinEl) -> Selection g w v -> {X X' Y : Expr n} -> RMa G X X' Y v (EvalFun f w) -> RMb G X X' Y v (EvalFun f w)) ->
  PiTm RMa G M M' T g b f -> PiTm RMb G M M' T g b f
mapPi h1 h2 p = record { A = A ; B = B ; rT = rT ; tT = tT ; iA = iA ; iB = iB
                       ; app = \ w v sel N N' cv rm -> h2 w v sel (app w v sel N N' cv (h1 w v sel rm)) }
  where open PiTm p

mapSig : {RMa RMb : RTmT} {n : Num} {G : Ctx n} {M M' T : Expr n} {u1 u2 b : FinEl} {f : FinFun} ->
  ({X X' Y : Expr n} -> RMa G X X' Y u1 b -> RMb G X X' Y u1 b) ->
  ({X X' Y : Expr n} -> RMa G X X' Y u2 (EvalFun f u1) -> RMb G X X' Y u2 (EvalFun f u1)) ->
  SigTm RMa G M M' T u1 u2 b f -> SigTm RMb G M M' T u1 u2 b f
mapSig h1 h2 p = record { A = A ; B = B ; rT = rT ; tT = tT ; iA = iA ; iB = iB ; cF = cF
                        ; fstR = h1 fstR ; sndR = h2 sndR }
  where open SigTm p

mapSuc : {RMa RMb : RTmT} {n : Num} {G : Ctx n} {M M' : Expr n} {v : FinEl} ->
  ({X X' : Expr n} -> RMa G X X' Nat v NatCode -> RMb G X X' Nat v NatCode) ->
  SucTm RMa G M M' v -> SucTm RMb G M M' v
mapSuc h p = record { P = P ; P' = P' ; rM = rM ; rM' = rM' ; cM = cM ; cM' = cM' ; cP = cP ; pred = h pred }
  where open SucTm p

------------------------------------------------------------------------
-- rank bounds
------------------------------------------------------------------------

Bd : FinEl -> Lev -> Set
Bd x j = Le (nsuc (RANK x)) j

private
  bdl : (x y j : Lev) -> Le (nsuc (max x y)) j -> Le (nsuc x) j
  bdl x y nzero ()
  bdl x y (nsuc j) h = Le-trans x (max x y) j (Le-max-l x y) h

  bdr : (x y j : Lev) -> Le (nsuc (max x y)) j -> Le (nsuc y) j
  bdr x y nzero ()
  bdr x y (nsuc j) h = Le-trans y (max x y) j (Le-max-r x y) h

  bdle : (x y j : Lev) -> Le x y -> Le (nsuc y) j -> Le (nsuc x) j
  bdle x y nzero le ()
  bdle x y (nsuc j) le h = Le-trans x y j le h

-- components of codes of bounded rank (bound at  suc j  on the code, j on parts)
bdPiDom : (b : FinEl) (f : FinFun) (j : Lev) -> Bd (PiCode b f) (nsuc j) -> Bd b j
bdPiDom b f j h = bdl (RANK b) (RANKFun f) j h

bdPiFun : (b : FinEl) (f : FinFun) (j : Lev) -> Bd (PiCode b f) (nsuc j) -> Le (nsuc (RANKFun f)) j
bdPiFun b f j h = bdr (RANK b) (RANKFun f) j h

bdSel-u : {f : FinFun} {w c : FinEl} (j : Lev) -> Le (nsuc (RANKFun f)) j -> Selection f w c -> Bd w j
bdSel-u {f} {w} j h sel = bdle (RANK w) (RANKFun f) j (Selection-RANK-u sel) h

bdSel-v : {f : FinFun} {w c : FinEl} (j : Lev) -> Le (nsuc (RANKFun f)) j -> Selection f w c -> Bd c j
bdSel-v {f} {c = c} j h sel = bdle (RANK c) (RANKFun f) j (Selection-RANK-v sel) h

bdEv : (f : FinFun) (w : FinEl) (j : Lev) -> Le (nsuc (RANKFun f)) j -> Bd (EvalFun f w) j
bdEv f w j h = bdle (RANK (EvalFun f w)) (RANKFun f) j (RANK-EvalFun f w) h

bdFun : (g : FinFun) (j : Lev) -> Bd (FunEl g) (nsuc j) -> Le (nsuc (RANKFun g)) j
bdFun g j h = h

bdPair1 : (u1 u2 : FinEl) (j : Lev) -> Bd (PairEl u1 u2) (nsuc j) -> Bd u1 j
bdPair1 u1 u2 j h = bdl (RANK u1) (RANK u2) j h

bdPair2 : (u1 u2 : FinEl) (j : Lev) -> Bd (PairEl u1 u2) (nsuc j) -> Bd u2 j
bdPair2 u1 u2 j h = bdr (RANK u1) (RANK u2) j h

bdSuc : (v : FinEl) (j : Lev) -> Bd (SucEl v) (nsuc j) -> Bd v j
bdSuc v j h = h

bdle0 : (x j : Lev) -> Le (nsuc x) j -> Le (nsuc nzero) j
bdle0 x nzero ()
bdle0 x (nsuc j) h = tt

------------------------------------------------------------------------
-- the stability pack
------------------------------------------------------------------------

record Stab (j : Lev) : Set where
  field
    tUp : {n : Num} {G : Ctx n} {T T' : Expr n} (a : FinEl) -> Bd a j ->
          St.RT j G T T' a -> St.RT (nsuc j) G T T' a
    tDn : {n : Num} {G : Ctx n} {T T' : Expr n} (a : FinEl) -> Bd a j ->
          St.RT (nsuc j) G T T' a -> St.RT j G T T' a
    mUp : {n : Num} {G : Ctx n} {M M' T : Expr n} (u a : FinEl) -> Bd u j -> Bd a j ->
          St.RM j G M M' T u a -> St.RM (nsuc j) G M M' T u a
    mDn : {n : Num} {G : Ctx n} {M M' T : Expr n} (u a : FinEl) -> Bd u j -> Bd a j ->
          St.RM (nsuc j) G M M' T u a -> St.RM j G M M' T u a

stab0 : Stab nzero
stab0 = record { tUp = \ a () ; tDn = \ a () ; mUp = \ u a () ; mDn = \ u a () }

module StabStep (j : Lev) (ih : Stab j) where
  open Stab ih

  RTa = St.RT (nsuc j) ; RTb = St.RT (nsuc (nsuc j))
  RMa = St.RM (nsuc j) ; RMb = St.RM (nsuc (nsuc j))

  codeUp : {S : Shape} {n : Num} {G : Ctx n} {T T' : Expr n} (b : FinEl) (f : FinFun) -> Bd (PiCode b f) (nsuc j) ->
    CodeTy S (St.RT j) (St.RM j) G T T' b f -> CodeTy S (St.RT (nsuc j)) (St.RM (nsuc j)) G T T' b f
  codeUp b f h = mapCT (tUp b (bdPiDom b f j h))
    (\ w c sel -> mDn w b (bdSel-u j (bdPiFun b f j h) sel) (bdPiDom b f j h))
    (\ w c sel -> tUp c (bdSel-v j (bdPiFun b f j h) sel))

  codeDn : {S : Shape} {n : Num} {G : Ctx n} {T T' : Expr n} (b : FinEl) (f : FinFun) -> Bd (PiCode b f) (nsuc j) ->
    CodeTy S (St.RT (nsuc j)) (St.RM (nsuc j)) G T T' b f -> CodeTy S (St.RT j) (St.RM j) G T T' b f
  codeDn b f h = mapCT (tDn b (bdPiDom b f j h))
    (\ w c sel -> mUp w b (bdSel-u j (bdPiFun b f j h) sel) (bdPiDom b f j h))
    (\ w c sel -> tDn c (bdSel-v j (bdPiFun b f j h) sel))

  tUp1 : {n : Num} {G : Ctx n} {T T' : Expr n} (a : FinEl) -> Bd a (nsuc j) -> RTa G T T' a -> RTb G T T' a
  tUp1 Bot h r = tt
  tUp1 UCode h r = r
  tUp1 NatCode h r = r
  tUp1 (PiCode b f) h r = codeUp b f h r
  tUp1 (SigmaCode b f) h r = codeUp b f h r

  tDn1 : {n : Num} {G : Ctx n} {T T' : Expr n} (a : FinEl) -> Bd a (nsuc j) -> RTb G T T' a -> RTa G T T' a
  tDn1 Bot h r = tt
  tDn1 UCode h r = r
  tDn1 NatCode h r = r
  tDn1 (PiCode b f) h r = codeDn b f h r
  tDn1 (SigmaCode b f) h r = codeDn b f h r

  mUp1 : {n : Num} {G : Ctx n} {M M' T : Expr n} (u a : FinEl) -> Bd u (nsuc j) -> Bd a (nsuc j) ->
    RMa G M M' T u a -> RMb G M M' T u a
  mUp1 Bot a hu ha r = tt
  mUp1 UCode Bot hu ha r = tt
  mUp1 {G = G} UCode UCode hu ha r = fst r , tUp1 {G = G} UCode hu (snd r)
  mUp1 UCode (FunEl _) hu ha r = tt
  mUp1 UCode ZeroEl hu ha r = tt
  mUp1 UCode (SucEl _) hu ha r = tt
  mUp1 UCode (PairEl _ _) hu ha r = tt
  mUp1 (FunEl _) Bot hu ha r = tt
  mUp1 (FunEl g) UCode hu ha r = Empty-elim (snd r)
  mUp1 (FunEl _) (FunEl _) hu ha r = tt
  mUp1 (FunEl g) (PiCode b f) hu ha r =
    mapPi (\ w v sel -> mDn w b (bdSel-u j (bdFun g j hu) sel) (bdPiDom b f j ha))
          (\ w v sel -> mUp v (EvalFun f w) (bdSel-v j (bdFun g j hu) sel) (bdEv f w j (bdPiFun b f j ha))) r
  mUp1 (FunEl _) ZeroEl hu ha r = tt
  mUp1 (FunEl _) (SucEl _) hu ha r = tt
  mUp1 (FunEl _) (PairEl _ _) hu ha r = tt
  mUp1 (PiCode _ _) Bot hu ha r = tt
  mUp1 {G = G} (PiCode pb pf) UCode hu ha r = fst r , tUp1 {G = G} (PiCode pb pf) hu (snd r)
  mUp1 (PiCode _ _) (FunEl _) hu ha r = tt
  mUp1 (PiCode _ _) ZeroEl hu ha r = tt
  mUp1 (PiCode _ _) (SucEl _) hu ha r = tt
  mUp1 (PiCode _ _) (PairEl _ _) hu ha r = tt
  mUp1 NatCode Bot hu ha r = tt
  mUp1 {G = G} NatCode UCode hu ha r = fst r , tUp1 {G = G} NatCode hu (snd r)
  mUp1 NatCode (FunEl _) hu ha r = tt
  mUp1 NatCode ZeroEl hu ha r = tt
  mUp1 NatCode (SucEl _) hu ha r = tt
  mUp1 NatCode (PairEl _ _) hu ha r = tt
  mUp1 ZeroEl Bot hu ha r = tt
  mUp1 ZeroEl UCode hu ha r = Empty-elim (snd r)
  mUp1 ZeroEl (FunEl _) hu ha r = tt
  mUp1 ZeroEl NatCode hu ha r = r
  mUp1 ZeroEl ZeroEl hu ha r = tt
  mUp1 ZeroEl (SucEl _) hu ha r = tt
  mUp1 ZeroEl (PairEl _ _) hu ha r = tt
  mUp1 (SucEl _) Bot hu ha r = tt
  mUp1 (SucEl v) UCode hu ha r = Empty-elim (snd r)
  mUp1 (SucEl _) (FunEl _) hu ha r = tt
  mUp1 (SucEl v) NatCode hu ha r = fst r , mapSuc (mUp v NatCode (bdSuc v j hu) (bdle0 (RANK v) j hu)) (snd r)
  mUp1 (SucEl _) ZeroEl hu ha r = tt
  mUp1 (SucEl _) (SucEl _) hu ha r = tt
  mUp1 (SucEl _) (PairEl _ _) hu ha r = tt
  mUp1 (PairEl _ _) Bot hu ha r = tt
  mUp1 (PairEl x1 x2) UCode hu ha r = Empty-elim (snd r)
  mUp1 (PairEl _ _) (FunEl _) hu ha r = tt
  mUp1 (PairEl _ _) ZeroEl hu ha r = tt
  mUp1 (PairEl _ _) (SucEl _) hu ha r = tt
  mUp1 (PairEl _ _) (PairEl _ _) hu ha r = tt
  mUp1 (PairEl x1 x2) (SigmaCode b f) hu ha r =
    mapSig (mUp x1 b (bdPair1 x1 x2 j hu) (bdPiDom b f j ha))
           (mUp x2 (EvalFun f x1) (bdPair2 x1 x2 j hu) (bdEv f x1 j (bdPiFun b f j ha))) r
  mUp1 (SigmaCode _ _) Bot hu ha r = tt
  mUp1 {G = G} (SigmaCode sb sf) UCode hu ha r = fst r , tUp1 {G = G} (SigmaCode sb sf) hu (snd r)
  mUp1 (SigmaCode _ _) (FunEl _) hu ha r = tt
  mUp1 (SigmaCode _ _) ZeroEl hu ha r = tt
  mUp1 (SigmaCode _ _) (SucEl _) hu ha r = tt
  mUp1 (SigmaCode _ _) (PairEl _ _) hu ha r = tt

  mDn1 : {n : Num} {G : Ctx n} {M M' T : Expr n} (u a : FinEl) -> Bd u (nsuc j) -> Bd a (nsuc j) ->
    RMb G M M' T u a -> RMa G M M' T u a
  mDn1 Bot a hu ha r = tt
  mDn1 UCode Bot hu ha r = tt
  mDn1 {G = G} UCode UCode hu ha r = fst r , tDn1 {G = G} UCode hu (snd r)
  mDn1 UCode (FunEl _) hu ha r = tt
  mDn1 UCode ZeroEl hu ha r = tt
  mDn1 UCode (SucEl _) hu ha r = tt
  mDn1 UCode (PairEl _ _) hu ha r = tt
  mDn1 (FunEl _) Bot hu ha r = tt
  mDn1 (FunEl g) UCode hu ha r = Empty-elim (snd r)
  mDn1 (FunEl _) (FunEl _) hu ha r = tt
  mDn1 (FunEl g) (PiCode b f) hu ha r =
    mapPi (\ w v sel -> mUp w b (bdSel-u j (bdFun g j hu) sel) (bdPiDom b f j ha))
          (\ w v sel -> mDn v (EvalFun f w) (bdSel-v j (bdFun g j hu) sel) (bdEv f w j (bdPiFun b f j ha))) r
  mDn1 (FunEl _) ZeroEl hu ha r = tt
  mDn1 (FunEl _) (SucEl _) hu ha r = tt
  mDn1 (FunEl _) (PairEl _ _) hu ha r = tt
  mDn1 (PiCode _ _) Bot hu ha r = tt
  mDn1 {G = G} (PiCode pb pf) UCode hu ha r = fst r , tDn1 {G = G} (PiCode pb pf) hu (snd r)
  mDn1 (PiCode _ _) (FunEl _) hu ha r = tt
  mDn1 (PiCode _ _) ZeroEl hu ha r = tt
  mDn1 (PiCode _ _) (SucEl _) hu ha r = tt
  mDn1 (PiCode _ _) (PairEl _ _) hu ha r = tt
  mDn1 NatCode Bot hu ha r = tt
  mDn1 {G = G} NatCode UCode hu ha r = fst r , tDn1 {G = G} NatCode hu (snd r)
  mDn1 NatCode (FunEl _) hu ha r = tt
  mDn1 NatCode ZeroEl hu ha r = tt
  mDn1 NatCode (SucEl _) hu ha r = tt
  mDn1 NatCode (PairEl _ _) hu ha r = tt
  mDn1 ZeroEl Bot hu ha r = tt
  mDn1 ZeroEl UCode hu ha r = Empty-elim (snd r)
  mDn1 ZeroEl (FunEl _) hu ha r = tt
  mDn1 ZeroEl NatCode hu ha r = r
  mDn1 ZeroEl ZeroEl hu ha r = tt
  mDn1 ZeroEl (SucEl _) hu ha r = tt
  mDn1 ZeroEl (PairEl _ _) hu ha r = tt
  mDn1 (SucEl _) Bot hu ha r = tt
  mDn1 (SucEl v) UCode hu ha r = Empty-elim (snd r)
  mDn1 (SucEl _) (FunEl _) hu ha r = tt
  mDn1 (SucEl v) NatCode hu ha r = fst r , mapSuc (mDn v NatCode (bdSuc v j hu) (bdle0 (RANK v) j hu)) (snd r)
  mDn1 (SucEl _) ZeroEl hu ha r = tt
  mDn1 (SucEl _) (SucEl _) hu ha r = tt
  mDn1 (SucEl _) (PairEl _ _) hu ha r = tt
  mDn1 (PairEl _ _) Bot hu ha r = tt
  mDn1 (PairEl x1 x2) UCode hu ha r = Empty-elim (snd r)
  mDn1 (PairEl _ _) (FunEl _) hu ha r = tt
  mDn1 (PairEl _ _) ZeroEl hu ha r = tt
  mDn1 (PairEl _ _) (SucEl _) hu ha r = tt
  mDn1 (PairEl _ _) (PairEl _ _) hu ha r = tt
  mDn1 (PairEl x1 x2) (SigmaCode b f) hu ha r =
    mapSig (mDn x1 b (bdPair1 x1 x2 j hu) (bdPiDom b f j ha))
           (mDn x2 (EvalFun f x1) (bdPair2 x1 x2 j hu) (bdEv f x1 j (bdPiFun b f j ha))) r
  mDn1 (SigmaCode _ _) Bot hu ha r = tt
  mDn1 {G = G} (SigmaCode sb sf) UCode hu ha r = fst r , tDn1 {G = G} (SigmaCode sb sf) hu (snd r)
  mDn1 (SigmaCode _ _) (FunEl _) hu ha r = tt
  mDn1 (SigmaCode _ _) ZeroEl hu ha r = tt
  mDn1 (SigmaCode _ _) (SucEl _) hu ha r = tt
  mDn1 (SigmaCode _ _) (PairEl _ _) hu ha r = tt

  result : Stab (nsuc j)
  result = record { tUp = tUp1 ; tDn = tDn1 ; mUp = mUp1 ; mDn = mDn1 }

stab : (j : Lev) -> Stab j
stab nzero    = stab0
stab (nsuc j) = StabStep.result j (stab j)
