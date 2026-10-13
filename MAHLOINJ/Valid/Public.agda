{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Valid/Public.agda
--
-- Level shifting (from stability) and the properties of the PUBLIC
-- relations RTy / RTm (canonical levels).
------------------------------------------------------------------------

module MAHLOINJ.Valid.Public where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Typing
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; PairEl ; SigmaCode
             ; FinFun ; Le ; max ; Le-trans ; Le-max-l ; Le-max-r ; Le-refl ; Le-suc)
open D using () renaming (suc to nsuc ; zero to nzero ; Nat to Lev)
open import MAHLOINJ.Domain.Kernel using (RANK ; LeCode ; FinMem ; Comp ; Sup)
import MAHLOINJ.Domain.Kernel as K
open import MAHLOINJ.Valid.HeadRed
open import MAHLOINJ.Valid.Stage
open import MAHLOINJ.Valid.Props
open import MAHLOINJ.Valid.Step
open import MAHLOINJ.Valid.Stab

------------------------------------------------------------------------
-- shifting
------------------------------------------------------------------------

plus : Lev -> Lev -> Lev
plus nzero    a = a
plus (nsuc d) a = nsuc (plus d a)

private
  Le-plus : (d a : Lev) -> Le a (plus d a)
  Le-plus nzero    a = Le-refl a
  Le-plus (nsuc d) a = Le-suc a (plus d a) (Le-plus d a)

  bd-plus : (x : FinEl) (d j : Lev) -> Bd x j -> Bd x (plus d j)
  bd-plus x d j h = Le-trans (nsuc (RANK x)) j (plus d j) h (Le-plus d j)

  gap : (a b : Lev) -> Le a b -> Sg Lev (\ d -> Eq b (plus d a))
  gap nzero    b       h = b , plus0 b
    where
      plus0 : (b : Lev) -> Eq b (plus b nzero)
      plus0 nzero    = refl
      plus0 (nsuc b) = Eq-cong nsuc (plus0 b)
  gap (nsuc a) nzero   ()
  gap (nsuc a) (nsuc b) h =
    let r = gap a b h in fst r , Eq-trans (Eq-cong nsuc (snd r)) (plus-suc (fst r) a)
    where
      plus-suc : (d a : Lev) -> Eq (nsuc (plus d a)) (plus d (nsuc a))
      plus-suc nzero    a = refl
      plus-suc (nsuc d) a = Eq-cong nsuc (plus-suc d a)

upT : {n : Num} {G : Ctx n} {T T' : Expr n} (a : FinEl) (d j : Lev) -> Bd a j ->
  St.RT j G T T' a -> St.RT (plus d j) G T T' a
upT a nzero    j h r = r
upT a (nsuc d) j h r = Stab.tUp (stab (plus d j)) a (bd-plus a d j h) (upT a d j h r)

dnT : {n : Num} {G : Ctx n} {T T' : Expr n} (a : FinEl) (d j : Lev) -> Bd a j ->
  St.RT (plus d j) G T T' a -> St.RT j G T T' a
dnT a nzero    j h r = r
dnT a (nsuc d) j h r = dnT a d j h (Stab.tDn (stab (plus d j)) a (bd-plus a d j h) r)

upM' : {n : Num} {G : Ctx n} {M M' T : Expr n} (u a : FinEl) (d j : Lev) -> Bd u j -> Bd a j ->
  St.RM j G M M' T u a -> St.RM (plus d j) G M M' T u a
upM' u a nzero    j hu ha r = r
upM' u a (nsuc d) j hu ha r = Stab.mUp (stab (plus d j)) u a (bd-plus u d j hu) (bd-plus a d j ha) (upM' u a d j hu ha r)

dnM' : {n : Num} {G : Ctx n} {M M' T : Expr n} (u a : FinEl) (d j : Lev) -> Bd u j -> Bd a j ->
  St.RM (plus d j) G M M' T u a -> St.RM j G M M' T u a
dnM' u a nzero    j hu ha r = r
dnM' u a (nsuc d) j hu ha r = dnM' u a d j hu ha (Stab.mDn (stab (plus d j)) u a (bd-plus u d j hu) (bd-plus a d j ha) r)

-- any two levels above the rank
shiftT : {n : Num} {G : Ctx n} {T T' : Expr n} (a : FinEl) (j k : Lev) -> Bd a j -> Bd a k ->
  St.RT j G T T' a -> St.RT k G T T' a
shiftT {G = G} {T} {T'} a j k hj hk r =
  let c = nsuc (RANK a) ; cc = Le-refl (RANK a)
      gj = gap c j hj ; gk = gap c k hk
      r0 = dnT a (fst gj) c cc (transport (\ x -> St.RT x G T T' a) (snd gj) r)
  in transport (\ x -> St.RT x G T T' a) (Eq-sym (snd gk)) (upT a (fst gk) c cc r0)

shiftM : {n : Num} {G : Ctx n} {M M' T : Expr n} (u a : FinEl) (j k : Lev) ->
  Bd u j -> Bd a j -> Bd u k -> Bd a k -> St.RM j G M M' T u a -> St.RM k G M M' T u a
shiftM {G = G} {M} {M'} {T} u a j k huj haj huk hak r =
  let c = nsuc (max (RANK u) (RANK a))
      cu = Le-max-l (RANK u) (RANK a) ; ca = Le-max-r (RANK u) (RANK a)
      hc = Le-max-lub' (RANK u) (RANK a) j huj haj
      hc' = Le-max-lub' (RANK u) (RANK a) k huk hak
      gj = gap c j hc ; gk = gap c k hc'
      r0 = dnM' u a (fst gj) c cu ca (transport (\ x -> St.RM x G M M' T u a) (snd gj) r)
  in transport (\ x -> St.RM x G M M' T u a) (Eq-sym (snd gk)) (upM' u a (fst gk) c cu ca r0)
  where
    Le-max-lub' : (x y j : Lev) -> Le (nsuc x) j -> Le (nsuc y) j -> Le (nsuc (max x y)) j
    Le-max-lub' x y nzero () hy
    Le-max-lub' x y (nsuc j) hx hy = K.Le-max-lub x y j hx hy

------------------------------------------------------------------------
-- bounds at maxima
------------------------------------------------------------------------

L1 : FinEl -> Lev
L1 x = nsuc (RANK x)

L2 : FinEl -> FinEl -> Lev
L2 x y = nsuc (max (RANK x) (RANK y))

L3 : FinEl -> FinEl -> FinEl -> Lev
L3 x y z = nsuc (max (RANK x) (max (RANK y) (RANK z)))

bd1 : (x : FinEl) -> Bd x (L1 x)
bd1 x = Le-refl (RANK x)

bd2l : (x y : FinEl) -> Bd x (L2 x y)
bd2l x y = Le-max-l (RANK x) (RANK y)
bd2r : (x y : FinEl) -> Bd y (L2 x y)
bd2r x y = Le-max-r (RANK x) (RANK y)

bd3a : (x y z : FinEl) -> Bd x (L3 x y z)
bd3a x y z = Le-max-l (RANK x) (max (RANK y) (RANK z))
bd3b : (x y z : FinEl) -> Bd y (L3 x y z)
bd3b x y z = Le-trans (RANK y) (max (RANK y) (RANK z)) (max (RANK x) (max (RANK y) (RANK z)))
               (Le-max-l (RANK y) (RANK z)) (Le-max-r (RANK x) (max (RANK y) (RANK z)))
bd3c : (x y z : FinEl) -> Bd z (L3 x y z)
bd3c x y z = Le-trans (RANK z) (max (RANK y) (RANK z)) (max (RANK x) (max (RANK y) (RANK z)))
               (Le-max-r (RANK y) (RANK z)) (Le-max-r (RANK x) (max (RANK y) (RANK z)))

-- moving public relations to / from a level
tyTo : {n : Num} {G : Ctx n} {T T' : Expr n} (a : FinEl) (L : Lev) -> Bd a L -> RTy G T T' a -> St.RT L G T T' a
tyTo a L h r = shiftT a (L1 a) L (bd1 a) h r

tyFr : {n : Num} {G : Ctx n} {T T' : Expr n} (a : FinEl) (L : Lev) -> Bd a L -> St.RT L G T T' a -> RTy G T T' a
tyFr a L h r = shiftT a L (L1 a) h (bd1 a) r

tmTo : {n : Num} {G : Ctx n} {M M' T : Expr n} (u a : FinEl) (L : Lev) -> Bd u L -> Bd a L ->
  RTm G M M' T u a -> St.RM L G M M' T u a
tmTo u a L hu ha r = shiftM u a (L2 u a) L (bd2l u a) (bd2r u a) hu ha r

tmFr : {n : Num} {G : Ctx n} {M M' T : Expr n} (u a : FinEl) (L : Lev) -> Bd u L -> Bd a L ->
  St.RM L G M M' T u a -> RTm G M M' T u a
tmFr u a L hu ha r = shiftM u a L (L2 u a) hu ha (bd2l u a) (bd2r u a) r

------------------------------------------------------------------------
-- public properties
------------------------------------------------------------------------

module P (L : Lev) = Props (props L)

pSymT : {n : Num} {G : Ctx n} {T T' : Expr n} (a : FinEl) -> FinMem a UCode -> RTy G T T' a -> RTy G T' T a
pSymT a aU r = P.symT (L1 a) a aU r

pTransT : {n : Num} {G : Ctx n} {T1 T2 T3 : Expr n} (a : FinEl) -> FinMem a UCode ->
  RTy G T1 T2 a -> RTy G T2 T3 a -> RTy G T1 T3 a
pTransT a aU r1 r2 = P.transT (L1 a) a aU r1 r2

pDownT : {n : Num} {G : Ctx n} {T T' : Expr n} (a0 a1 : FinEl) -> LeCode a0 a1 ->
  FinMem a0 UCode -> FinMem a1 UCode -> RTy G T T' a1 -> RTy G T T' a0
pDownT a0 a1 le h0 h1 r =
  tyFr a0 (L2 a0 a1) (bd2l a0 a1) (P.downT (L2 a0 a1) a0 a1 le h0 h1 (tyTo a1 (L2 a0 a1) (bd2r a0 a1) r))

pJoinT : {n : Num} {G : Ctx n} {T T' : Expr n} (a1 a2 : FinEl) -> Comp a1 a2 ->
  FinMem a1 UCode -> FinMem a2 UCode -> RTy G T T' a1 -> RTy G T T' a2 -> RTy G T T' (Sup a1 a2)
pJoinT a1 a2 c h1 h2 r1 r2 =
  tyFr (Sup a1 a2) L (bd3a (Sup a1 a2) a1 a2)
    (P.joinT L a1 a2 c h1 h2 (tyTo a1 L (bd3b (Sup a1 a2) a1 a2) r1) (tyTo a2 L (bd3c (Sup a1 a2) a1 a2) r2))
  where L = L3 (Sup a1 a2) a1 a2

pExpT : {n : Num} {G : Ctx n} {T T1 T' : Expr n} (a : FinEl) -> HRs T T1 -> TyEq G T T1 ->
  RTy G T1 T' a -> RTy G T T' a
pExpT a hr q r = P.expT (L1 a) a hr q r

pExpT' : {n : Num} {G : Ctx n} {T T' T1' : Expr n} (a : FinEl) -> HRs T' T1' -> TyEq G T' T1' ->
  RTy G T T1' a -> RTy G T T' a
pExpT' a hr q r = P.expT' (L1 a) a hr q r

pSymM : {n : Num} {G : Ctx n} {M M' T : Expr n} (u a : FinEl) -> FinMem u a -> FinMem a UCode ->
  RTy G T T a -> RTm G M M' T u a -> RTm G M' M T u a
pSymM u a um aU v r = P.symM (L2 u a) u a um aU (tyTo a (L2 u a) (bd2r u a) v) r

pTransM : {n : Num} {G : Ctx n} {M1 M2 M3 T : Expr n} (u a : FinEl) -> FinMem u a -> FinMem a UCode ->
  RTy G T T a -> RTm G M1 M2 T u a -> RTm G M2 M3 T u a -> RTm G M1 M3 T u a
pTransM u a um aU v r1 r2 = P.transM (L2 u a) u a um aU (tyTo a (L2 u a) (bd2r u a) v) r1 r2

pConvM : {n : Num} {G : Ctx n} {M M' T T' : Expr n} (u a : FinEl) -> FinMem u a -> FinMem a UCode ->
  RTy G T T' a -> RTm G M M' T u a -> RTm G M M' T' u a
pConvM u a um aU v r = P.convM (L2 u a) u a um aU (tyTo a (L2 u a) (bd2r u a) v) r

pRestrM : {n : Num} {G : Ctx n} {M M' T : Expr n} (u u' a : FinEl) -> LeCode u' u ->
  FinMem u' a -> FinMem u a -> FinMem a UCode -> RTy G T T a -> RTm G M M' T u a -> RTm G M M' T u' a
pRestrM u u' a le m' m aU v r =
  tmFr u' a L (bd3b u u' a) (bd3c u u' a)
    (P.restrM L u u' a le m' m aU (tyTo a L (bd3c u u' a) v) (tmTo u a L (bd3a u u' a) (bd3c u u' a) r))
  where L = L3 u u' a

pDownM : {n : Num} {G : Ctx n} {M M' T : Expr n} (u a0 a1 : FinEl) -> LeCode a0 a1 ->
  FinMem u a0 -> FinMem a0 UCode -> FinMem a1 UCode -> RTy G T T a1 -> RTm G M M' T u a1 -> RTm G M M' T u a0
pDownM u a0 a1 le m h0 h1 v r =
  tmFr u a0 L (bd3a u a0 a1) (bd3b u a0 a1)
    (P.downM L u a0 a1 le m h0 h1 (tyTo a1 L (bd3c u a0 a1) v) (tmTo u a1 L (bd3a u a0 a1) (bd3c u a0 a1) r))
  where L = L3 u a0 a1

pUpM : {n : Num} {G : Ctx n} {M M' T : Expr n} (u a0 a1 : FinEl) -> LeCode a0 a1 ->
  FinMem u a0 -> FinMem a0 UCode -> FinMem a1 UCode -> RTy G T T a1 -> RTm G M M' T u a0 -> RTm G M M' T u a1
pUpM u a0 a1 le m h0 h1 v r =
  tmFr u a1 L (bd3a u a0 a1) (bd3c u a0 a1)
    (P.upM L u a0 a1 le m h0 h1 (tyTo a1 L (bd3c u a0 a1) v) (tmTo u a0 L (bd3a u a0 a1) (bd3b u a0 a1) r))
  where L = L3 u a0 a1

pJoinM : {n : Num} {G : Ctx n} {M M' T : Expr n} (u1 u2 a : FinEl) -> Comp u1 u2 ->
  FinMem u1 a -> FinMem u2 a -> FinMem a UCode -> RTy G T T a ->
  RTm G M M' T u1 a -> RTm G M M' T u2 a -> RTm G M M' T (Sup u1 u2) a
pJoinM u1 u2 a c m1 m2 aU v r1 r2 =
  tmFr (Sup u1 u2) a L (bdS) (bdA)
    (P.joinM L u1 u2 a c m1 m2 aU (tyTo a L bdA v)
       (tmTo u1 a L (bdU1) bdA r1) (tmTo u2 a L bdU2 bdA r2))
  where
    L = nsuc (max (RANK (Sup u1 u2)) (max (RANK u1) (max (RANK u2) (RANK a))))
    bdS = Le-max-l (RANK (Sup u1 u2)) (max (RANK u1) (max (RANK u2) (RANK a)))
    rest = max (RANK u1) (max (RANK u2) (RANK a))
    top = max (RANK (Sup u1 u2)) rest
    up : (x : Lev) -> Le x rest -> Le x top
    up x h = Le-trans x rest top h (Le-max-r (RANK (Sup u1 u2)) rest)
    bdU1 = up (RANK u1) (Le-max-l (RANK u1) (max (RANK u2) (RANK a)))
    bdU2 = up (RANK u2) (Le-trans (RANK u2) (max (RANK u2) (RANK a)) rest (Le-max-l (RANK u2) (RANK a))
                           (Le-max-r (RANK u1) (max (RANK u2) (RANK a))))
    bdA = up (RANK a) (Le-trans (RANK a) (max (RANK u2) (RANK a)) rest (Le-max-r (RANK u2) (RANK a))
                         (Le-max-r (RANK u1) (max (RANK u2) (RANK a))))

pExpM : {n : Num} {G : Ctx n} {M M1 M' T : Expr n} (u a : FinEl) -> FinMem u a -> FinMem a UCode ->
  HRs M M1 -> ConvTm G M M1 T -> RTy G T T a -> RTm G M1 M' T u a -> RTm G M M' T u a
pExpM u a um aU hr q v r = P.expM (L2 u a) u a um aU hr q (tyTo a (L2 u a) (bd2r u a) v) r

pExpM' : {n : Num} {G : Ctx n} {M M' M1' T : Expr n} (u a : FinEl) -> FinMem u a -> FinMem a UCode ->
  HRs M' M1' -> ConvTm G M' M1' T -> RTy G T T a -> RTm G M M1' T u a -> RTm G M M' T u a
pExpM' u a um aU hr q v r = P.expM' (L2 u a) u a um aU hr q (tyTo a (L2 u a) (bd2r u a) v) r
