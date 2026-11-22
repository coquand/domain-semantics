{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.GAT.Sound
--
-- sterbac4 Theorem 16: the erasure sends every GAT derivation to a
-- derivation of ERT's T_T.  Port of UNIT/GSound.seg.
------------------------------------------------------------------------

module ERT.GAT.Sound where

open import ERT.Basic
open import ERT.TarskiSyntax
open import ERT.TarskiTyping
open import ERT.TarskiMeta
open import ERT.TarskiMetaCong using (ConvTmSub ; liftSub-ConvTmSub ; subst-cong-IsType ; subst-cong-HasType ;
                                      subst1-cong-Ty)
open import ERT.GAT.Syntax
open import ERT.GAT.Rules
open import ERT.GAT.TLib

SM : {n m : Nat} -> GC n -> GS n m -> GC m -> Set
SM D s G = Pair (WfCtx (eC D)) (Pair (WfCtx (eC G)) (WtS (eC D) (eC G) (eS s)))

QS : {n m : Nat} -> GC n -> GS n m -> GS n m -> GC m -> Set
QS D s t G = Pair (SM D s G) (Pair (WtS (eC D) (eC G) (eS t)) (CTS (eC D) (eC G) (eS s) (eS t)))

SoundJ : GJ -> Set
SoundJ (gjwf G)          = WfCtx (eC G)
SoundJ (gjty G A)        = IsType (eC G) (eT A)
SoundJ (gjtm G a A)      = HasType (eC G) (eT a) (eT A)
SoundJ (gjsub D s G)     = SM D s G
SoundJ (gjeqcx G D)      = CxEq (eC G) (eC D)
SoundJ (gjeqty G A B)    = ConvTy (eC G) (eT A) (eT B)
SoundJ (gjeqtm G a b A)  = ConvTm (eC G) (eT a) (eT b) (eT A)
SoundJ (gjeqsub D s t G) = QS D s t G

------------------------------------------------------------------------
-- helpers

dom-WtSub : {h g : Nat} (H H' : Ctx h) {G : Ctx g} {s : Sub h g}
  -> CxEq H H' -> WfCtx H' -> WtS H G s -> WtS H' G s
dom-WtSub H H' {s = s} e wf ws =
  ptS (\ i -> substExpr-id (s i)) (compS (cxS H H' e wf) wf ws)

cod-WtSub : {h g : Nat} {H : Ctx h} {G G' : Ctx g} {s : Sub h g}
  -> WfCtx H -> WfCtx G -> WfCtx G' -> CxEq G G' -> WtS H G s -> WtS H G' s
cod-WtSub {G = G} {G'} wfH wfG wfG' e ws = compS ws wfH (cxS G' G (cx-sym G G' wfG' e) wfG)


lift-id-pt : {n : Nat} -> PtEq (liftSub (idSub {n})) (\ i -> Var i)
lift-id-pt fzero    = refl
lift-id-pt (fsuc i) = refl

lift-comp-pt : {h k g : Nat} (s : Sub k g) (d : Sub h k) -> PtEq (liftSub (cmpS s d)) (cmpS (liftSub s) (liftSub d))
lift-comp-pt s d fzero    = refl
lift-comp-pt s d (fsuc i) = Eq-sym (subst-wk-comm d (s i))

sec-comp-pt : {h g : Nat} (s : Sub h g) (a : Expr g)
  -> PtEq (cmpS (subst1Sub a) s) (cmpS (liftSub s) (subst1Sub (substExpr s a)))
sec-comp-pt s a fzero    = refl
sec-comp-pt s a (fsuc i) = Eq-sym (subst1-wk (s i) (substExpr s a))

lpsq-pt : {n : Nat} -> PtEq (cmpS (liftSub (wkS {n})) (subst1Sub (Var fzero))) (\ i -> Var i)
lpsq-pt fzero    = refl
lpsq-pt (fsuc i) = refl

wkl-pt : {n : Nat} -> PtEq (\ i -> Var (liftRen (wkRen {n}) i)) (liftSub wkS)
wkl-pt fzero    = refl
wkl-pt (fsuc i) = refl

eta-eq : {n : Nat} (A : Expr n) (B : Expr (suc n)) (f : Expr n)
  -> Eq (Lam A B (App (wkExpr A) (renExpr (liftRen wkRen) B) (wkExpr f) (Var fzero)))
        (Lam A B (App (substExpr wkS A) (substExpr (liftSub wkS) B) (substExpr wkS f) (Var fzero)))
eta-eq A B f =
  Eq-cong (\ X -> Lam A B X)
    (Eq-cong4 App (ren-as-subst wkRen A)
       (Eq-trans (ren-as-subst (liftRen wkRen) B) (substExpr-ext _ _ wkl-pt B))
       (ren-as-subst wkRen f) refl)

------------------------------------------------------------------------
-- Theorem 16

sound : {J : GJ} -> GDer J -> SoundJ J
sound g-nil = wf-empty
sound (g-ext h) = wf-extend (sound h)
sound gc-nil = tt
sound (gc-refl {G = G} h) = cx-refl (eC G) (sound h)
sound (gc-ext h1 h2) = mkSigma (sound h1) (sound h2)
sound (gs-id h) = mkSigma (sound h) (mkSigma (sound h) (idS (sound h)))
sound (gs-comp h1 h2) =
  let r1 = sound h1 ; r2 = sound h2
  in mkSigma (fst r2) (mkSigma (fst (snd r1)) (compS (snd (snd r2)) (fst r2) (snd (snd r1))))
sound (gs-eps h) = mkSigma (sound h) (mkSigma wf-empty (epsS fin0))
sound (gs-p h) = mkSigma (wf-extend (sound h)) (mkSigma (isType-WfCtx (sound h)) (pS (sound h)))
sound (gs-lift h1 h2) =
  let r1 = sound h1 ; r2 = sound h2
  in mkSigma (wf-extend (sTy (snd (snd r1)) (fst r1) r2))
       (mkSigma (wf-extend r2) (liftS (snd (snd r1)) (fst r1) r2))
sound (gs-sec h1 h2) =
  let r1 = sound h1 ; r2 = sound h2
  in mkSigma (isType-WfCtx r1) (mkSigma (wf-extend r1) (secS r1 r2))
sound (gs-cx {D' = D'} {D = D} h0 h0' h1 h2 h) =
  let r0 = sound h0 ; r0' = sound h0' ; r1 = sound h1 ; r2 = sound h2 ; r = sound h
  in mkSigma r0 (mkSigma r0' (dom-WtSub (eC D) (eC D') r1 r0 (cod-WtSub (fst r) (fst (snd r)) r0' r2 (snd (snd r)))))
sound (gt-pi h1 h2) = is-Ty-Pi (sound h1) (sound h2)
sound (gt-uu h) = is-Ty-U (sound h)
sound (gt-el h) = is-Ty-El (sound h)
sound (gt-sb h1 h2) = sTy (snd (snd (sound h2))) (fst (sound h2)) (sound h1)
sound (gt-cx h0 h1 h2) = cx-IsType (sound h1) (sound h0) (sound h2)
sound (gm-lam h1 h2 h3) = ty-Lam (sound h1) (sound h2) (sound h3)
sound (gm-app h1 h2 h3 h4) = ty-App (sound h1) (sound h2) (sound h3) (sound h4)
sound (gm-pic h1 h2) = ty-PiCode (sound h1) (sound h2)
sound (gm-uc h lt) = ty-UCode (sound h) lt
sound (gm-lf lt h) = ty-Lift lt (sound h)
sound (gm-q {G = G} {A = A} h) =
  Eq-transport (\ X -> HasType (extend (eC G) (eT A)) (Var fzero) X) (ren-as-subst wkRen (eT A))
    (ty-var (wf-extend (sound h)))
sound (gm-sb hA h1 h2) = sTm (snd (snd (sound h2))) (fst (sound h2)) (sound h1)
sound (gm-conv h1 h2) = ty-conv (sound h1) (sound h2)
sound (gm-cx h0 h1 h2) = cx-HasType (sound h1) (sound h0) (sound h2)
sound (ge-refl h) = conv-Ty-refl (sound h)
sound (ge-sym h) = conv-Ty-sym (sound h)
sound (ge-trans h1 h2) = conv-Ty-trans (sound h1) (sound h2)
sound (ge-pi h0 h1 h2) = conv-Ty-Pi (sound h0) (sound h1) (sound h2)
sound (ge-el h) = conv-Ty-El (sound h)
sound (ge-sb h0 h1 h2 h3 h4) =
  let r2 = sound h2 ; r3 = sound h3 ; r4 = sound h4
  in conv-Ty-trans (congTy (snd (snd r4)) (fst r2) (sound h0)) (sCTy (snd (snd r3)) (fst r2) (sound h1))
sound (ge-el-lf lt h) = conv-Ty-El-Lift lt (sound h)
sound (ge-el-pic h1 h2) = conv-Ty-El-PiCode (sound h1) (sound h2)
sound (ge-el-uc h lt) = conv-Ty-El-UCode (sound h) lt
sound (ge-sb-id {G = G} {A = A} h) =
  Eq-transport (\ X -> ConvTy (eC G) X (eT A)) (Eq-sym (substExpr-id (eT A))) (conv-Ty-refl (sound h))
sound (ge-sb-comp {A = A} {s = s} {T = T} {d = d} h0 h1 h2) =
  Eq-transport (\ X -> ConvTy (eC T) (substExpr (eS d) (substExpr (eS s) (eT A))) X) (subst-subst (eS d) (eS s) (eT A))
    (conv-Ty-refl (sTy (snd (snd (sound h2))) (fst (sound h2)) (sTy (snd (snd (sound h1))) (fst (sound h1)) (sound h0))))
sound (ge-pi-sb h1 h2 h3) = conv-Ty-refl (sTy (snd (snd (sound h3))) (fst (sound h3)) (is-Ty-Pi (sound h1) (sound h2)))
sound (ge-uu-sb h) = conv-Ty-refl (is-Ty-U (fst (sound h)))
sound (ge-el-sb h1 h2) = conv-Ty-refl (is-Ty-El (sTm (snd (snd (sound h2))) (fst (sound h2)) (sound h1)))
sound (ge-cx h0 h1 h2) = cx-ConvTy (sound h1) (sound h0) (sound h2)
sound (gm-refl h) = conv-refl (sound h)
sound (gm-sym hA h) = conv-sym (sound h)
sound (gm-trans h1 h2) = conv-trans (sound h1) (sound h2)
sound (gm-eqconv h1 h2) = conv-conv (sound h1) (sound h2)
sound (gm-elam h0 h1 h2 h3) =
  let r0 = sound h0 ; r2 = sound h2 ; r3 = sound h3
  in conv-trans (conv-cong-Lam-body r0 (presup-l-ConvTy r2) r3)
       (conv-cong-Lam-Ty r0 (sound h1) r2 (presup-r-ConvTm r3))
sound (gm-eapp h0 hB ha h1 h2 h3 h4) =
  let r0 = sound h0 ; rB = sound hB ; ra = sound ha ; r3 = sound h3 ; r4 = sound h4
      cr = subst1-cong-Ty r4 r0 rB
  in conv-trans (conv-cong-App-fun r0 rB r3 ra)
       (conv-trans (conv-cong-App-arg r0 rB (presup-r-ConvTm r3) r4 cr)
          (conv-conv (conv-cong-App-Ty r0 (sound h1) (sound h2) (presup-r-ConvTm r3) (presup-r-ConvTm r4))
             (conv-Ty-sym cr)))
sound (gm-epic h0 h1 h2) = conv-cong-PiCode (sound h0) (sound h1) (sound h2)
sound (gm-elf lt h) = conv-cong-Lift lt (sound h)
sound (gm-esb hA h0 h1 h2 h3 h4) =
  let r2 = sound h2 ; r3 = sound h3 ; r4 = sound h4
  in conv-trans (congTm (snd (snd r4)) (fst r2) (sound h0))
       (conv-conv (sCTm (snd (snd r3)) (fst r2) (sound h1))
          (conv-Ty-sym (congTy (snd (snd r4)) (fst r2) (sound hA))))
sound (gm-beta hA hB h1 h2) = conv-beta (sound hA) (sound hB) (sound h1) (sound h2)
sound (gm-eta {G = G} {A = A} {B = B} {f = f} hA hB h) =
  Eq-transport (\ X -> ConvTm (eC G) (eT f) X (Pi (eT A) (eT B))) (eta-eq (eT A) (eT B) (eT f))
    (conv-eta (sound hA) (sound hB) (sound h))
sound (gm-lf-pic lt h1 h2) = conv-Lift-PiCode lt (sound h1) (sound h2)
sound (gm-lf-uc h lt1 lt2) = conv-Lift-UCode (sound h) lt1 lt2
sound (gm-lf-lf lt1 lt2 h) = conv-Lift-Lift lt1 lt2 (sound h)
sound (gm-sb-id {G = G} {a = a} {A = A} h) =
  Eq-transport (\ X -> ConvTm (eC G) X (eT a) (eT A)) (Eq-sym (substExpr-id (eT a))) (conv-refl (sound h))
sound (gm-sb-comp {a = a} {A = A} {s = s} {T = T} {d = d} h0 h1 h2) =
  Eq-transport (\ X -> ConvTm (eC T) (substExpr (eS d) (substExpr (eS s) (eT a))) (substExpr (cmpS (eS s) (eS d)) (eT a)) X)
    (subst-subst (eS d) (eS s) (eT A))
    (Eq-transport (\ X -> ConvTm (eC T) (substExpr (eS d) (substExpr (eS s) (eT a))) X (substExpr (eS d) (substExpr (eS s) (eT A))))
       (subst-subst (eS d) (eS s) (eT a))
       (conv-refl (sTm (snd (snd (sound h2))) (fst (sound h2)) (sTm (snd (snd (sound h1))) (fst (sound h1)) (sound h0)))))
sound (gm-lam-sb h1 h2 h3 h4) =
  conv-refl (sTm (snd (snd (sound h4))) (fst (sound h4)) (ty-Lam (sound h1) (sound h2) (sound h3)))
sound (gm-app-sb {A = A} {B = B} {c = c} {a = a} {D = D} {s = s} h1 h2 h3 h4 h5) =
  Eq-transport (\ X -> ConvTm (eC D) (substExpr (eS s) (App (eT A) (eT B) (eT c) (eT a))) (substExpr (eS s) (App (eT A) (eT B) (eT c) (eT a))) X)
    (subst-subst1 (eS s) (eT B) (eT a))
    (conv-refl (sTm (snd (snd (sound h5))) (fst (sound h5)) (ty-App (sound h1) (sound h2) (sound h3) (sound h4))))
sound (gm-pic-sb h1 h2 h3) = conv-refl (sTm (snd (snd (sound h3))) (fst (sound h3)) (ty-PiCode (sound h1) (sound h2)))
sound (gm-uc-sb h lt) = conv-refl (ty-UCode (fst (sound h)) lt)
sound (gm-lf-sb lt h1 h2) = conv-refl (sTm (snd (snd (sound h2))) (fst (sound h2)) (ty-Lift lt (sound h1)))
sound (gm-q-lift {A = A} {D = D} {s = s} h1 h2) =
  let dA = sTy (snd (snd (sound h2))) (fst (sound h2)) (sound h1)
  in conv-refl (Eq-transport (\ X -> HasType (extend (eC D) (substExpr (eS s) (eT A))) (Var fzero) X)
                 (ren-as-subst wkRen (substExpr (eS s) (eT A))) (ty-var (wf-extend dA)))
sound (gm-q-sec h1 h2) = conv-refl (sound h2)
sound (gm-ecx h0 h1 h2) = cx-ConvTm (sound h1) (sound h0) (sound h2)
sound (gq-refl h) = mkSigma (sound h) (mkSigma (snd (snd (sound h))) (ctsR (snd (snd (sound h)))))
sound (gq-sym h) =
  let r = sound h
  in mkSigma (mkSigma (fst (fst r)) (mkSigma (fst (snd (fst r))) (fst (snd r))))
       (mkSigma (snd (snd (fst r))) (ctsS (fst (fst r)) (fst (snd (fst r))) (snd (snd r))))
sound (gq-trans h1 h2) =
  let r1 = sound h1 ; r2 = sound h2
  in mkSigma (fst r1) (mkSigma (fst (snd r2)) (ctsT (fst (fst r1)) (fst (snd (fst r1))) (snd (snd r1)) (snd (snd r2))))
sound (gq-comp h1 h2) =
  let r1 = sound h1 ; r2 = sound h2
      wT = fst (fst r2) ; wD = fst (fst r1) ; wG = fst (snd (fst r1))
  in mkSigma (mkSigma wT (mkSigma wG (compS (snd (snd (fst r2))) wT (snd (snd (fst r1))))))
       (mkSigma (compS (fst (snd r2)) wT (fst (snd r1)))
          (ctsC wT wD wG (snd (snd (fst r2))) (snd (snd r2)) (fst (snd r1)) (snd (snd r1))))
sound (gq-lift {A = A} {D = D} {s = s} {s' = s'} h0 h1 h2 h3) =
  let r0 = sound h0 ; r2 = sound h2 ; r3 = sound h3
      wD = fst r2
      dAs = sTy (snd (snd r2)) wD r0
      dAs' = sTy (fst (snd r3)) wD r0
      e : CxEq (extend (eC D) (substExpr (eS s') (eT A))) (extend (eC D) (substExpr (eS s) (eT A)))
      e = mkSigma (cx-refl (eC D) wD) (conv-Ty-sym (congTy (snd (snd r3)) wD r0))
  in mkSigma (mkSigma (wf-extend dAs) (mkSigma (wf-extend r0) (liftS (snd (snd r2)) wD r0)))
       (mkSigma (dom-WtSub _ _ e (wf-extend dAs) (liftS (fst (snd r3)) wD r0))
          (ctsL (snd (snd r3)) wD r0))
sound (gq-sec hA ha ha' h1 h2) =
  let rA = sound hA
  in mkSigma (mkSigma (isType-WfCtx rA) (mkSigma (wf-extend rA) (secS rA (sound ha))))
       (mkSigma (secS rA (sound ha')) (ctsSec (isType-WfCtx rA) (sound h2)))
sound (gq-idl h) = mkSigma (sound h) (mkSigma (snd (snd (sound h))) (ctsR (snd (snd (sound h)))))
sound (gq-idr {s = s} h) =
  let r = sound h
      w = ptS (\ i -> Eq-sym (substExpr-id (eS s i))) (snd (snd r))
  in mkSigma (mkSigma (fst r) (mkSigma (fst (snd r)) w)) (mkSigma (snd (snd r)) (ctsP w (\ i -> substExpr-id (eS s i))))
sound (gq-assoc {s = s} {d = d} {e = e} h1 h2 h3) =
  let r1 = sound h1 ; r2 = sound h2 ; r3 = sound h3
      w = compS (snd (snd r3)) (fst r3) (compS (snd (snd r2)) (fst r2) (snd (snd r1)))
  in mkSigma (mkSigma (fst r3) (mkSigma (fst (snd r1)) w))
       (mkSigma (compS (compS (snd (snd r3)) (fst r3) (snd (snd r2))) (fst r3) (snd (snd r1)))
          (ctsP w (\ i -> subst-subst (eS e) (eS d) (eS s i))))
sound (gq-eps {s = s} h) =
  mkSigma (mkSigma (fst (sound h)) (mkSigma wf-empty (epsS (eS s)))) (mkSigma (epsS fin0) (ctsE (eS s) fin0))
sound (gq-lift-id {G = G} {A = A} h) =
  let r = sound h ; wG = isType-WfCtx r
      w = liftS (idS wG) wG r
  in mkSigma (mkSigma (wf-extend (sTy (idS wG) wG r)) (mkSigma (wf-extend r) w))
       (mkSigma (ptS lift-id-pt w) (ctsP w lift-id-pt))
sound (gq-lift-comp {s = s} {d = d} h0 h1 h2) =
  let r0 = sound h0 ; r1 = sound h1 ; r2 = sound h2
      wsd = compS (snd (snd r2)) (fst r2) (snd (snd r1))
      w = liftS wsd (fst r2) r0
  in mkSigma (mkSigma (wf-extend (sTy wsd (fst r2) r0)) (mkSigma (wf-extend r0) w))
       (mkSigma (ptS (lift-comp-pt (eS s) (eS d)) w) (ctsP w (lift-comp-pt (eS s) (eS d))))
sound (gq-p-lift {s = s} h1 h2) =
  let r1 = sound h1 ; r2 = sound h2
      dAs = sTy (snd (snd r2)) (fst r2) r1
      w = compS (pS dAs) (wf-extend dAs) (snd (snd r2))
      pt = \ i -> Eq-sym (ren-as-subst wkRen (eS s i))
  in mkSigma (mkSigma (wf-extend dAs) (mkSigma (fst (snd r2)) (ptS pt w)))
       (mkSigma w (ctsP (ptS pt w) (\ i -> ren-as-subst wkRen (eS s i))))
sound (gq-p-sec h1 h2) =
  let wG = isType-WfCtx (sound h1)
  in mkSigma (mkSigma wG (mkSigma wG (idS wG))) (mkSigma (idS wG) (ctsR (idS wG)))
sound (gq-sec-comp {G = G} {A = A} {a = a} {s = s} h1 h2 h3) =
  let r1 = sound h1 ; r2 = sound h2 ; r3 = sound h3
      w = compS (snd (snd r3)) (fst r3) (secS r1 r2)
  in mkSigma (mkSigma (fst r3) (mkSigma (wf-extend r1) w))
       (mkSigma (ptS (sec-comp-pt (eS s) (eT a)) w) (ctsP w (sec-comp-pt (eS s) (eT a))))
sound (gq-lift-p-sec-q {G = G} {A = A} h) =
  let r = sound h ; wGA = wf-extend r
      w = ptS (\ i -> Eq-sym (lpsq-pt i)) (idS wGA)
  in mkSigma (mkSigma wGA (mkSigma wGA w)) (mkSigma (idS wGA) (ctsP w lpsq-pt))
