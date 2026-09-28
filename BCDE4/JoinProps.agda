{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.JoinProps
--
-- Properties of joins used by the normalisation-free Lemma 4.18:
--
--  * Join-diag: on the diagonal (Γ ⊢ T0 = T1) the coercions are
--    injective.  By η for Π, for level products and for constraint
--    products (conv-GLam-eta), and by Π-/[α]-/[ψ]-/U-injectivity.
--    Loops are decided first: in a loopy context everything is ∅.
--
--  * normTop: a join whose left type is known not to be a guard with an
--    invalid constraint (i.e. is convertible to U / Π / [α], so that
--    any guard on top must be valid, BCDE4.GrdNoConf) is replaced by one
--    without a guard join on top: a valid guard is dropped (relevel from
--    Γ,ψ to Γ, guard β).
--
--  * JRes and the transport of results along SubTy (ERT.StripUniqNF).
------------------------------------------------------------------------

module BCDE4.JoinProps where

open import BCDE4.Basic
open import BCDE4.Levels
open import BCDE4.RussellSyntax
open import BCDE4.RussellTyping
open import BCDE4.RussellMeta
open import BCDE4.RussellRelevel using (Skel ; CEnt ; sk-empty ; sk-extend ; ent-valid ; relev-IsType)
open import BCDE4.RussellInversion
open import BCDE4.Coerce
open import BCDE4.Main using (UInj ; PiInj ; LPiInj)
open import BCDE4.LC.Decide using (ldecAll)
open import BCDE4.GrdNoConf ldecAll using (grd-inj1 ; noconf-Pi-U ; noconf-LPi-U ; noconf-Pi-LPi)
open import BCDE4.LC.Loop using (decLoop)

------------------------------------------------------------------------
-- Small facts
------------------------------------------------------------------------

U-conv : {n : Nat} {G : Ctx n} {l l' : LExpr} -> WfCtx G -> Valid (lctx G) l l' -> ConvTy G (U l) (U l')
U-conv {l = l} wf v = conv-Ty-from-U (conv-U-lvl wf v (lt-next l))

-- p = k ∨ m and k = m  ⇒  p = k
private
  join-self : {Th : LCtx} {k m p : LExpr} -> Valid Th p (lsup k m) -> Valid Th k m -> Valid Th p k
  join-self v km = v-trans v (v-trans (v-sup v-refl (v-sym km)) v-idem)

skel-unC : {n : Nat} (G : Ctx n) (c : Constr) -> Skel (addC G c) G
skel-unC (empty Th)   c = sk-empty
skel-unC (extend G A) c = sk-extend (skel-unC G c)

------------------------------------------------------------------------
-- The diagonal
------------------------------------------------------------------------

mutual

  Join-diag : {n : Nat} {G : Ctx n} {T0 T1 L t0 t1 : Expr n} {k0 k1 : Co n}
    -> Join G T0 T1 L k0 k1 -> ConvTy G T0 T1
    -> HasType G t0 T0 -> HasType G t1 T1
    -> ConvTm G (coe k0 t0) (coe k1 t1) L -> ConvTm G t0 t1 T0
  Join-diag {G = G} j cT d0 d1 e = diag (decLoop (lctx G)) j cT d0 d1 e

  diag : {n : Nat} {G : Ctx n} {T0 T1 L t0 t1 : Expr n} {k0 k1 : Co n}
    -> Either (Loop (lctx G)) (LoopFree (lctx G))
    -> Join G T0 T1 L k0 k1 -> ConvTy G T0 T1
    -> HasType G t0 T0 -> HasType G t1 T1
    -> ConvTm G (coe k0 t0) (coe k1 t1) L -> ConvTm G t0 t1 T0
  diag (inl lp) j cT d0 d1 e =
    let dT0 = typing-IsType d0
    in conv-trans (conv-collapse lp dT0 d0) (conv-sym (conv-collapse lp dT0 (ty-conv d1 (conv-Ty-sym cT))))
  diag (inr lf) (jconv c0 c1) cT d0 d1 e = conv-conv e (conv-Ty-sym c0)
  diag (inr lf) (juniv k m p v c0 c1) cT d0 d1 e =
    let vkm = UInj lf (conv-Ty-trans (conv-Ty-sym c0) (conv-Ty-trans cT c1))
    in conv-conv (conv-conv e (U-conv (typing-WfCtx d0) (join-self v vkm))) (conv-Ty-sym c0)
  diag (inr lf) (jpi dA dB0 dB1 cv0 cv1 j) cT d0 d1 e =
    let cB  = snd (PiInj lf (conv-Ty-trans (conv-Ty-sym cv0) (conv-Ty-trans cT cv1)))
        t0' = ty-conv d0 cv0
        t1' = ty-conv d1 cv1
        h0  = appv0-ty dA dB0 t0'
        h1  = appv0-ty dA dB1 t1'
        dL  = join-L j
        hb0 = coe-ty j h0
        hb1 = coe-ty (Join-sym j) h1
        eb  = conv-trans (conv-sym (lam-beta-v0 dA dL hb0))
                (conv-trans (appv0-cong dA dL e) (lam-beta-v0 dA dL hb1))
        ih  = Join-diag j cB h0 h1 eb
        s1  = conv-eta dA dB0 t0'
        s2  = conv-cong-Lam-body dA dB0 h0 ih
        s3  = conv-cong-Lam-Ty dA dB0 (conv-Ty-refl dA) cB (ty-conv h1 (conv-Ty-sym cB))
        s4  = conv-conv (conv-sym (conv-eta dA dB1 t1'))
                (conv-Ty-Pi dA dB1 (conv-Ty-refl dA) (conv-Ty-sym cB))
    in conv-conv (conv-trans s1 (conv-trans s2 (conv-trans s3 s4))) (conv-Ty-sym cv0)
  diag (inr lf) (jlpi wf dB0 dB1 cv0 cv1 j) cT d0 d1 e =
    let cB  = LPiInj lf (conv-Ty-trans (conv-Ty-sym cv0) (conv-Ty-trans cT cv1))
        t0' = ty-conv d0 cv0
        t1' = ty-conv d1 cv1
        h0  = lappv0-ty dB0 t0'
        h1  = lappv0-ty dB1 t1'
        dL  = join-L j
        hb0 = coe-ty j h0
        hb1 = coe-ty (Join-sym j) h1
        eb  = conv-trans (conv-sym (llam-beta-v0 dL hb0))
                (conv-trans (lappv0-cong dL e) (llam-beta-v0 dL hb1))
        ih  = Join-diag j cB h0 h1 eb
        s1  = conv-LApp-eta dB0 t0'
        s2  = conv-cong-LLam wf dB0 h0 ih
        s3  = conv-cong-LLam-Ty wf dB0 cB (ty-conv h1 (conv-Ty-sym cB))
        s4  = conv-conv (conv-sym (conv-LApp-eta dB1 t1')) (conv-Ty-LPi wf dB1 (conv-Ty-sym cB))
    in conv-conv (conv-trans s1 (conv-trans s2 (conv-trans s3 s4))) (conv-Ty-sym cv0)
  diag {G = G} (inr lf) (jgrd {c = c} wf dB0 dB1 cv0 cv1 j) cT d0 d1 e =
    let cB  = grd-inj1 (conv-Ty-trans (conv-Ty-sym cv0) (conv-Ty-trans cT cv1))
        t0' = ty-conv d0 cv0
        t1' = ty-conv d1 cv1
        h0  = unguard-HasType dB0 t0'
        h1  = unguard-HasType dB1 t1'
        dL  = join-L j
        hb0 = coe-ty j h0
        hb1 = coe-ty (Join-sym j) h1
        vc  = valid-addC G c
        eb  = conv-trans (conv-sym (conv-GLam-beta vc dL hb0))
                (conv-trans (unguard-ConvTm dL e) (conv-GLam-beta vc dL hb1))
        ih  = Join-diag j cB h0 h1 eb
        s1  = conv-GLam-eta wf dB0 t0' h0
        s2  = conv-cong-GLam wf dB0 h0 ih
        s3  = conv-cong-GLam-Ty wf dB0 cB (ty-conv h1 (conv-Ty-sym cB))
        s4  = conv-conv (conv-sym (conv-GLam-eta wf dB1 t1' h1)) (conv-Ty-Grd wf dB1 (conv-Ty-sym cB))
    in conv-conv (conv-trans s1 (conv-trans s2 (conv-trans s3 s4))) (conv-Ty-sym cv0)

------------------------------------------------------------------------
-- Results of the main lemma
------------------------------------------------------------------------

record JRes {n : Nat} (G : Ctx n) (u0 u1 T0 T1 : Expr n) : Set where
  constructor mkJRes
  field
    L    : Expr n
    k0   : Co n
    k1   : Co n
    join : Join G T0 T1 L k0 k1
    eq   : ConvTm G (coe k0 u0) (coe k1 u1) L

swapRes : {n : Nat} {G : Ctx n} {u0 u1 T0 T1 : Expr n} -> JRes G u1 u0 T1 T0 -> JRes G u0 u1 T0 T1
swapRes (mkJRes L k0 k1 j e) = mkJRes L k1 k0 (Join-sym j) (conv-sym e)

-- in a loopy context: everything is ∅
collapseRes : {n : Nat} {G : Ctx n} {u0 u1 T0 T1 : Expr n} -> Loop (lctx G) ->
  HasType G u0 T0 -> HasType G u1 T1 -> JRes G u0 u1 T0 T1
collapseRes lp d0 d1 =
  let dT0 = typing-IsType d0 ; dT1 = typing-IsType d1
      c0  = conv-Ty-collapse lp dT0 ; c1 = conv-Ty-collapse lp dT1
  in mkJRes Emp idC idC (jconv c0 c1)
       (conv-trans (conv-conv (conv-collapse lp dT0 d0) c0) (conv-sym (conv-conv (conv-collapse lp dT1 d1) c1)))

------------------------------------------------------------------------
-- Removing valid guards on top of a join
------------------------------------------------------------------------

NotGrd : {n : Nat} {G : Ctx n} {T0 T1 L : Expr n} {k0 k1 : Co n} -> Join G T0 T1 L k0 k1 -> Set
NotGrd (jconv _ _)           = Top
NotGrd (juniv _ _ _ _ _ _)   = Top
NotGrd (jpi _ _ _ _ _ _)     = Top
NotGrd (jlpi _ _ _ _ _ _)    = Top
NotGrd (jgrd _ _ _ _ _ _)    = Empty

gdepth : {n : Nat} {G : Ctx n} {T0 T1 L : Expr n} {k0 k1 : Co n} -> Join G T0 T1 L k0 k1 -> Nat
gdepth (jconv _ _)          = zero
gdepth (juniv _ _ _ _ _ _)  = zero
gdepth (jpi _ _ _ _ _ _)    = zero
gdepth (jlpi _ _ _ _ _ _)   = zero
gdepth (jgrd _ _ _ _ _ j)   = suc (gdepth j)

gdepth-retarget : {n : Nat} {G : Ctx n} {T0 T1 T0' T1' L : Expr n} {k0 k1 : Co n}
  (e0 : ConvTy G T0' T0) (e1 : ConvTy G T1' T1) (j : Join G T0 T1 L k0 k1) ->
  Eq (gdepth (retarget e0 e1 j)) (gdepth j)
gdepth-retarget e0 e1 (jconv _ _)          = refl
gdepth-retarget e0 e1 (juniv _ _ _ _ _ _)  = refl
gdepth-retarget e0 e1 (jpi _ _ _ _ _ _)    = refl
gdepth-retarget e0 e1 (jlpi _ _ _ _ _ _)   = refl
gdepth-retarget e0 e1 (jgrd _ _ _ _ _ _)   = refl

gdepth-relev : {n : Nat} {G H : Ctx n} {T0 T1 L : Expr n} {k0 k1 : Co n}
  (s : Skel G H) (e : CEnt H G) (j : Join G T0 T1 L k0 k1) -> Eq (gdepth (Join-relev s e j)) (gdepth j)
gdepth-relev s e (jconv _ _)          = refl
gdepth-relev s e (juniv _ _ _ _ _ _)  = refl
gdepth-relev s e (jpi _ _ _ _ _ _)    = refl
gdepth-relev s e (jlpi _ _ _ _ _ _)   = refl
gdepth-relev s e (jgrd _ _ _ _ _ j)   = Eq-cong suc (gdepth-relev _ _ j)

record JResN {n : Nat} (G : Ctx n) (u0 u1 T0 T1 : Expr n) : Set where
  constructor mkJResN
  field
    L    : Expr n
    k0   : Co n
    k1   : Co n
    join : Join G T0 T1 L k0 k1
    eq   : ConvTm G (coe k0 u0) (coe k1 u1) L
    ng   : NotGrd join

-- the hypothesis: any guard T0 is convertible to is valid
GrdOK : {n : Nat} -> Ctx n -> Expr n -> Set
GrdOK {n} G T = (c : Constr) (B : Expr n) -> ConvTy G T (Grd c B) -> ValidC (lctx G) c

private
  suc-inj : {a b : Nat} -> Eq (suc a) (suc b) -> Eq a b
  suc-inj refl = refl

normTop' : {n : Nat} {G : Ctx n} {u0 u1 T0 T1 L : Expr n} {k0 k1 : Co n} ->
  GrdOK G T0 -> (f : Nat) -> (j : Join G T0 T1 L k0 k1) -> Eq (gdepth j) f ->
  ConvTm G (coe k0 u0) (coe k1 u1) L -> HasType G u0 T0 -> HasType G u1 T1 -> JResN G u0 u1 T0 T1
normTop' vf f j@(jconv _ _)         ef e d0 d1 = mkJResN _ _ _ j e tt
normTop' vf f j@(juniv _ _ _ _ _ _) ef e d0 d1 = mkJResN _ _ _ j e tt
normTop' vf f j@(jpi _ _ _ _ _ _)   ef e d0 d1 = mkJResN _ _ _ j e tt
normTop' vf f j@(jlpi _ _ _ _ _ _)  ef e d0 d1 = mkJResN _ _ _ j e tt
normTop' vf zero (jgrd _ _ _ _ _ _) () e d0 d1
normTop' {G = G} vf (suc f) (jgrd {c = c} {B0 = B0} wf dB0 dB1 cv0 cv1 j) ef e d0 d1 =
  let v    = vf c B0 cv0
      s    = skel-unC G c
      en   = ent-valid G c v
      j'   = Join-relev s en j
      r0   = conv-Ty-trans cv0 (conv-Ty-Grd-beta v (relev-IsType s en dB0))
      r1   = conv-Ty-trans cv1 (conv-Ty-Grd-beta v (relev-IsType s en dB1))
      j''  = retarget r0 r1 j'
      dL   = join-L j''
      e'   = conv-trans (conv-sym (conv-GLam-beta v dL (coe-ty j'' d0)))
               (conv-trans (conv-conv e (conv-Ty-Grd-beta v dL)) (conv-GLam-beta v dL (coe-ty (Join-sym j'') d1)))
      ef'  = Eq-trans (gdepth-retarget r0 r1 j') (Eq-trans (gdepth-relev s en j) (suc-inj ef))
  in normTop' vf f j'' ef' e' d0 d1

normTop : {n : Nat} {G : Ctx n} {u0 u1 T0 T1 : Expr n} ->
  GrdOK G T0 -> HasType G u0 T0 -> HasType G u1 T1 -> JRes G u0 u1 T0 T1 -> JResN G u0 u1 T0 T1
normTop vf d0 d1 (mkJRes L k0 k1 j e) = normTop' vf (gdepth j) j refl e d0 d1

------------------------------------------------------------------------
-- Universe joins
------------------------------------------------------------------------

-- a join one of whose sides is a universe is a universe join
joinU-l : {n : Nat} {G : Ctx n} {P0 P1 : Expr n} {k : LExpr} (x y : Expr n) -> LoopFree (lctx G)
  -> JRes G x y P0 P1 -> HasType G x P0 -> HasType G y P1 -> ConvTy G P0 (U k)
  -> Sigma LExpr (\ p1 -> Pair (ConvTy G P1 (U p1)) (ConvTm G x y (U (lsup k p1))))
joinU-l {G = G} {k = k} x y lf r d0 d1 cP =
  go (normTop (\ c B cv -> grd-valid-U' (conv-Ty-trans (conv-Ty-sym cP) cv)) d0 d1 r)
  where
    grd-valid-U' : {c : Constr} {B : Expr _} -> ConvTy G (U k) (Grd c B) -> ValidC (lctx G) c
    grd-valid-U' cv = GU.grd-valid-U lf cv
      where import BCDE4.GrdNoConf ldecAll as GU
    go : JResN G x y _ _ -> Sigma LExpr (\ p1 -> Pair (ConvTy G _ (U p1)) (ConvTm G x y (U (lsup k p1))))
    go (mkJResN L _ _ (jconv c0 c1) e _) =
      let cLU = conv-Ty-trans (conv-Ty-sym c0) cP
      in mkSigma k (mkSigma (conv-Ty-trans c1 cLU) (conv-cum (conv-conv e cLU) (leL-supl k k)))
    go (mkJResN _ _ _ (juniv k' m' p v c0 c1) e _) =
      let ek = UInj lf (conv-Ty-trans (conv-Ty-sym c0) cP)          -- k' = k
      in mkSigma m' (mkSigma c1 (U-resp-Tm (v-trans v (v-sup ek v-refl)) e))
    go (mkJResN _ _ _ (jpi _ _ _ cv0 _ _) e _)  = absurd (noconf-Pi-U lf (conv-Ty-trans (conv-Ty-sym cv0) cP))
    go (mkJResN _ _ _ (jlpi _ _ _ cv0 _ _) e _) = absurd (noconf-LPi-U lf (conv-Ty-trans (conv-Ty-sym cv0) cP))
    go (mkJResN _ _ _ (jgrd _ _ _ _ _ _) e ())

joinU-both : {n : Nat} {G : Ctx n} {l0 l1 : LExpr} (x y : Expr n) -> LoopFree (lctx G)
  -> JRes G x y (U l0) (U l1) -> HasType G x (U l0) -> HasType G y (U l1) -> ConvTm G x y (U (lsup l0 l1))
joinU-both {l0 = l0} x y lf r d0 d1 =
  let s  = joinU-l x y lf r d0 d1 (conv-Ty-refl (isType-U (typing-WfCtx d0)))
      el = UInj lf (conv-Ty-sym (fst (snd s)))                     -- p1 = l1
  in U-resp-Tm (v-sup v-refl el) (snd (snd s))

aboveU : {n : Nat} {G : Ctx n} {P T : Expr n} {p : LExpr} -> LoopFree (lctx G)
  -> SubTy G P T -> ConvTy G P (U p) -> Sigma LExpr (\ m -> Pair (LeL (lctx G) p m) (ConvTy G T (U m)))
aboveU {p = p} lf (sub-conv c) cP = mkSigma p (mkSigma (leL-self p) (conv-Ty-trans (conv-Ty-sym c) cP))
aboveU {p = p} lf (sub-cum k m le cP' cT) cP =
  let ek = UInj lf (conv-Ty-trans (conv-Ty-sym cP) cP')            -- p = k
  in mkSigma m (mkSigma (leL-trans (leL-refl ek) le) cT)

cumL : {n : Nat} {G : Ctx n} {P0 P1 T0 T1 : Expr n} (x y : Expr n) -> LoopFree (lctx G)
  -> JRes G x y P0 P1 -> HasType G x P0 -> HasType G y P1
  -> (k m : LExpr) -> LeL (lctx G) k m -> ConvTy G P0 (U k) -> ConvTy G T0 (U m)
  -> SubTy G P1 T1 -> JRes G x y T0 T1
cumL x y lf r d0 d1 k m le cP cT s1 =
  let s  = joinU-l x y lf r d0 d1 cP
      p1 = fst s
      a  = aboveU lf s1 (fst (snd s))
      m1 = fst a
  in mkJRes (U (lsup m m1)) idC idC (juniv m m1 (lsup m m1) v-refl cT (snd (snd a)))
       (conv-cum (snd (snd s)) (leL-sup-mono le (fst (snd a))))

-- from the principal types to the actual ones
Join-sub : {n : Nat} {G : Ctx n} {P0 P1 T0 T1 t0 t1 : Expr n} -> LoopFree (lctx G)
  -> JRes G t0 t1 P0 P1 -> HasType G t0 P0 -> HasType G t1 P1
  -> SubTy G P0 T0 -> SubTy G P1 T1 -> JRes G t0 t1 T0 T1
Join-sub lf (mkJRes L k0 k1 j e) d0 d1 (sub-conv c0) (sub-conv c1) =
  mkJRes L k0 k1 (retarget (conv-Ty-sym c0) (conv-Ty-sym c1) j) e
Join-sub {t0 = t0} {t1 = t1} lf r d0 d1 (sub-cum k m le cP cT) s1 = cumL t0 t1 lf r d0 d1 k m le cP cT s1
Join-sub {t0 = t0} {t1 = t1} lf r d0 d1 (sub-conv c0) (sub-cum k m le cP cT) =
  swapRes (cumL t1 t0 lf (swapRes r) d1 d0 k m le cP cT (sub-conv c0))
