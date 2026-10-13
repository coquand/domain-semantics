{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLOINJ/Adq/View.agda
--
-- Views of the PUBLIC relations at concrete codes: the clause records
-- with public relations inside (all stage bookkeeping hidden here).
------------------------------------------------------------------------

module MAHLOINJ.Adq.View where

open import MAHLO.Basic renaming (Sigma to Sg)
open import MAHLO.Syntax
open import MAHLO.Typing
import MAHLOINJ.Domain.Basic as D
open D using (Top ; tt ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; NatCode ; ZeroEl ; SucEl ; PairEl ; SigmaCode
             ; FinFun ; Le ; max ; Le-trans ; Le-max-l ; Le-max-r ; Le-refl)
open D using () renaming (suc to nsuc ; zero to nzero ; Nat to Lev)
open import MAHLOINJ.Domain.Kernel using (EvalFun ; RANK ; RANKFun)
open import MAHLOINJ.Model.Selection using (Selection)
open import MAHLOINJ.Domain.Kernel using (NotBot)
open import MAHLOINJ.Valid.HeadRed
open import MAHLOINJ.Valid.Stage
open import MAHLOINJ.Valid.Stab
open import MAHLOINJ.Valid.Public
open import MAHLOINJ.Valid.Props using (ShapeOK)

------------------------------------------------------------------------
-- generic: clause records at a stage j  <->  with public relations
------------------------------------------------------------------------

module _ {n : Num} {G : Ctx n} where

  codeToPub : {S : Shape} {T T' : Expr n} (b : FinEl) (f : FinFun) (j : Lev) -> Bd (PiCode b f) (nsuc j) ->
    CodeTy S (St.RT j) (St.RM j) G T T' b f -> CodeTy S RTy RTm G T T' b f
  codeToPub b f j h = mapCT (tyFr b j hb)
    (\ w c sel -> tmTo w b j (bdSel-u j hf sel) hb)
    (\ w c sel -> tyFr c j (bdSel-v j hf sel))
    where hb = bdPiDom b f j h ; hf = bdPiFun b f j h

  codeFromPub : {S : Shape} {T T' : Expr n} (b : FinEl) (f : FinFun) (j : Lev) -> Bd (PiCode b f) (nsuc j) ->
    CodeTy S RTy RTm G T T' b f -> CodeTy S (St.RT j) (St.RM j) G T T' b f
  codeFromPub b f j h = mapCT (tyTo b j hb)
    (\ w c sel -> tmFr w b j (bdSel-u j hf sel) hb)
    (\ w c sel -> tyTo c j (bdSel-v j hf sel))
    where hb = bdPiDom b f j h ; hf = bdPiFun b f j h

  piToPub : {M M' T : Expr n} (g : FinFun) (b : FinEl) (f : FinFun) (j : Lev) ->
    Bd (FunEl g) (nsuc j) -> Bd (PiCode b f) (nsuc j) ->
    PiTm (St.RM j) G M M' T g b f -> PiTm RTm G M M' T g b f
  piToPub g b f j hg hp = mapPi
    (\ w v sel -> tmTo w b j (bdSel-u j (bdFun g j hg) sel) (bdPiDom b f j hp))
    (\ w v sel -> tmFr v (EvalFun f w) j (bdSel-v j (bdFun g j hg) sel) (bdEv f w j (bdPiFun b f j hp)))

  piFromPub : {M M' T : Expr n} (g : FinFun) (b : FinEl) (f : FinFun) (j : Lev) ->
    Bd (FunEl g) (nsuc j) -> Bd (PiCode b f) (nsuc j) ->
    PiTm RTm G M M' T g b f -> PiTm (St.RM j) G M M' T g b f
  piFromPub g b f j hg hp = mapPi
    (\ w v sel -> tmFr w b j (bdSel-u j (bdFun g j hg) sel) (bdPiDom b f j hp))
    (\ w v sel -> tmTo v (EvalFun f w) j (bdSel-v j (bdFun g j hg) sel) (bdEv f w j (bdPiFun b f j hp)))

  sigToPub : {M M' T : Expr n} (u1 u2 b : FinEl) (f : FinFun) (j : Lev) ->
    Bd (PairEl u1 u2) (nsuc j) -> Bd (SigmaCode b f) (nsuc j) ->
    SigTm (St.RM j) G M M' T u1 u2 b f -> SigTm RTm G M M' T u1 u2 b f
  sigToPub u1 u2 b f j hu hp = mapSig
    (tmFr u1 b j (bdPair1 u1 u2 j hu) (bdPiDom b f j hp))
    (tmFr u2 (EvalFun f u1) j (bdPair2 u1 u2 j hu) (bdEv f u1 j (bdPiFun b f j hp)))

  sigFromPub : {M M' T : Expr n} (u1 u2 b : FinEl) (f : FinFun) (j : Lev) ->
    Bd (PairEl u1 u2) (nsuc j) -> Bd (SigmaCode b f) (nsuc j) ->
    SigTm RTm G M M' T u1 u2 b f -> SigTm (St.RM j) G M M' T u1 u2 b f
  sigFromPub u1 u2 b f j hu hp = mapSig
    (tmTo u1 b j (bdPair1 u1 u2 j hu) (bdPiDom b f j hp))
    (tmTo u2 (EvalFun f u1) j (bdPair2 u1 u2 j hu) (bdEv f u1 j (bdPiFun b f j hp)))

  sucToPub : {M M' : Expr n} (v : FinEl) (j : Lev) -> Bd (SucEl v) (nsuc j) ->
    SucTm (St.RM j) G M M' v -> SucTm RTm G M M' v
  sucToPub v j h = mapSuc (tmFr v NatCode j (bdSuc v j h) (bdle0 (RANK v) j (bdSuc v j h)))

  sucFromPub : {M M' : Expr n} (v : FinEl) (j : Lev) -> Bd (SucEl v) (nsuc j) ->
    SucTm RTm G M M' v -> SucTm (St.RM j) G M M' v
  sucFromPub v j h = mapSuc (tmTo v NatCode j (bdSuc v j h) (bdle0 (RANK v) j (bdSuc v j h)))

------------------------------------------------------------------------
-- public views
------------------------------------------------------------------------

K2 : FinEl -> FinEl -> Lev
K2 x y = max (RANK x) (RANK y)

private
  hl : (x y : FinEl) -> Bd x (nsuc (max (RANK x) (RANK y)))
  hl x y = Le-max-l (RANK x) (RANK y)
  hr : (x y : FinEl) -> Bd y (nsuc (max (RANK x) (RANK y)))
  hr x y = Le-max-r (RANK x) (RANK y)

module _ {n : Num} {G : Ctx n} where

  piTyV : {T T' : Expr n} {b : FinEl} {f : FinFun} -> RTy G T T' (PiCode b f) -> CodeTy PiB RTy RTm G T T' b f
  piTyV {b = b} {f} r = codeToPub b f (RANK (PiCode b f)) (Le-refl (RANK (PiCode b f))) r

  piTyM : {T T' : Expr n} {b : FinEl} {f : FinFun} -> CodeTy PiB RTy RTm G T T' b f -> RTy G T T' (PiCode b f)
  piTyM {b = b} {f} r = codeFromPub b f (RANK (PiCode b f)) (Le-refl (RANK (PiCode b f))) r

  sigTyV : {T T' : Expr n} {b : FinEl} {f : FinFun} -> RTy G T T' (SigmaCode b f) -> CodeTy SigmaB RTy RTm G T T' b f
  sigTyV {b = b} {f} r = codeToPub b f (RANK (PiCode b f)) (Le-refl (RANK (PiCode b f))) r

  sigTyM : {T T' : Expr n} {b : FinEl} {f : FinFun} -> CodeTy SigmaB RTy RTm G T T' b f -> RTy G T T' (SigmaCode b f)
  sigTyM {b = b} {f} r = codeFromPub b f (RANK (PiCode b f)) (Le-refl (RANK (PiCode b f))) r

  lamV : {M M' T : Expr n} {g : FinFun} {b : FinEl} {f : FinFun} ->
    RTm G M M' T (FunEl g) (PiCode b f) -> PiTm RTm G M M' T g b f
  lamV {g = g} {b} {f} r = piToPub g b f (K2 (FunEl g) (PiCode b f)) (hl (FunEl g) (PiCode b f)) (hr (FunEl g) (PiCode b f)) r

  lamM : {M M' T : Expr n} {g : FinFun} {b : FinEl} {f : FinFun} ->
    PiTm RTm G M M' T g b f -> RTm G M M' T (FunEl g) (PiCode b f)
  lamM {g = g} {b} {f} r = piFromPub g b f (K2 (FunEl g) (PiCode b f)) (hl (FunEl g) (PiCode b f)) (hr (FunEl g) (PiCode b f)) r

  pairV : {M M' T : Expr n} {u1 u2 b : FinEl} {f : FinFun} ->
    RTm G M M' T (PairEl u1 u2) (SigmaCode b f) -> SigTm RTm G M M' T u1 u2 b f
  pairV {u1 = u1} {u2} {b} {f} r = sigToPub u1 u2 b f (K2 (PairEl u1 u2) (SigmaCode b f)) (hl (PairEl u1 u2) (SigmaCode b f)) (hr (PairEl u1 u2) (SigmaCode b f)) r

  pairM : {M M' T : Expr n} {u1 u2 b : FinEl} {f : FinFun} ->
    SigTm RTm G M M' T u1 u2 b f -> RTm G M M' T (PairEl u1 u2) (SigmaCode b f)
  pairM {u1 = u1} {u2} {b} {f} r = sigFromPub u1 u2 b f (K2 (PairEl u1 u2) (SigmaCode b f)) (hl (PairEl u1 u2) (SigmaCode b f)) (hr (PairEl u1 u2) (SigmaCode b f)) r

  sucV : {M M' T : Expr n} {v : FinEl} -> RTm G M M' T (SucEl v) NatCode -> TyEq G T Nat * SucTm RTm G M M' v
  sucV {v = v} r = fst r , sucToPub v (K2 (SucEl v) NatCode) (hl (SucEl v) NatCode) (snd r)

  sucM : {M M' T : Expr n} {v : FinEl} -> TyEq G T Nat -> SucTm RTm G M M' v -> RTm G M M' T (SucEl v) NatCode
  sucM {v = v} q r = q , sucFromPub v (K2 (SucEl v) NatCode) (hl (SucEl v) NatCode) r

  -- elements of the universe
  elV : {M M' T : Expr n} (u : FinEl) -> NotBot u -> RTm G M M' T u UCode -> UnivR G T * RTy G M M' u
  elV UCode nb r = fst r , tyFr UCode (L2 UCode UCode) (hl UCode UCode) (snd r)
  elV (FunEl g) nb r = Empty-elim (snd r)
  elV (PiCode b f) nb r = fst r , tyFr (PiCode b f) (L2 (PiCode b f) UCode) (hl (PiCode b f) UCode) (snd r)
  elV NatCode nb r = fst r , tyFr NatCode (L2 NatCode UCode) (hl NatCode UCode) (snd r)
  elV ZeroEl nb r = Empty-elim (snd r)
  elV (SucEl v) nb r = Empty-elim (snd r)
  elV (PairEl u1 u2) nb r = Empty-elim (snd r)
  elV (SigmaCode b f) nb r = fst r , tyFr (SigmaCode b f) (L2 (SigmaCode b f) UCode) (hl (SigmaCode b f) UCode) (snd r)

  elM : {M M' T : Expr n} (u : FinEl) -> UnivR G T -> RTy G M M' u -> RTm G M M' T u UCode
  elM Bot q r = tt
  elM UCode q r = q , tyTo UCode (L2 UCode UCode) (hl UCode UCode) r
  elM (FunEl g) q ()
  elM (PiCode b f) q r = q , tyTo (PiCode b f) (L2 (PiCode b f) UCode) (hl (PiCode b f) UCode) r
  elM NatCode q r = q , tyTo NatCode (L2 NatCode UCode) (hl NatCode UCode) r
  elM ZeroEl q ()
  elM (SucEl v) q ()
  elM (PairEl u1 u2) q ()
  elM (SigmaCode b f) q r = q , tyTo (SigmaCode b f) (L2 (SigmaCode b f) UCode) (hl (SigmaCode b f) UCode) r

------------------------------------------------------------------------
-- normalising the record fields when the type is literally a shape
------------------------------------------------------------------------

module _ {RM : RTmT} {n : Num} {G : Ctx n} {M M' : Expr n} {As : Expr n} {Bs : Expr (suc n)} where

  piApp : {g : FinFun} {b : FinEl} {f : FinFun} -> PiTm RM G M M' (PiB As Bs) g b f ->
    (w v : FinEl) -> Selection g w v -> (N N' : Expr n) -> ConvTm G N N' As ->
    RM G N N' As w b -> RM G (App M N) (App M' N') (subst1 Bs N) v (EvalFun f w)
  piApp {g} {b} {f} p = go (PiB-inj (HRs-det (PiTm.rT p) hrs-refl nored-Pi nored-Pi))
    where
      go : Eq (PiTm.A p) As * Eq (PiTm.B p) Bs -> (w v : FinEl) -> Selection g w v -> (N N' : Expr n) -> ConvTm G N N' As ->
           RM G N N' As w b -> RM G (App M N) (App M' N') (subst1 Bs N) v (EvalFun f w)
      go (eA , eB) = transport2 (\ X Y -> (w v : FinEl) -> Selection g w v -> (N N' : Expr n) -> ConvTm G N N' X ->
                                   RM G N N' X w b -> RM G (App M N) (App M' N') (subst1 Y N) v (EvalFun f w))
                       eA eB (PiTm.app p)

  sigFst : {u1 u2 b : FinEl} {f : FinFun} -> SigTm RM G M M' (SigmaB As Bs) u1 u2 b f ->
    RM G (Fst M) (Fst M') As u1 b
  sigFst {u1} {u2} {b} {f} p = go (SigmaB-inj (HRs-det (SigTm.rT p) hrs-refl nored-Sigma nored-Sigma))
    where
      go : Eq (SigTm.A p) As * Eq (SigTm.B p) Bs -> RM G (Fst M) (Fst M') As u1 b
      go (eA , eB) = transport (\ X -> RM G (Fst M) (Fst M') X u1 b) eA (SigTm.fstR p)

  sigSnd : {u1 u2 b : FinEl} {f : FinFun} -> SigTm RM G M M' (SigmaB As Bs) u1 u2 b f ->
    RM G (Snd M) (Snd M') (subst1 Bs (Fst M)) u2 (EvalFun f u1)
  sigSnd {u1} {u2} {b} {f} p = go (SigmaB-inj (HRs-det (SigTm.rT p) hrs-refl nored-Sigma nored-Sigma))
    where
      go : Eq (SigTm.A p) As * Eq (SigTm.B p) Bs -> RM G (Snd M) (Snd M') (subst1 Bs (Fst M)) u2 (EvalFun f u1)
      go (eA , eB) = transport (\ Y -> RM G (Snd M) (Snd M') (subst1 Y (Fst M)) u2 (EvalFun f u1)) eB (SigTm.sndR p)

-- the codomain of a literal shape, with the shape's own components
module _ {RT : RTyT} {RM : RTmT} {n : Num} {G : Ctx n} {Al Ar : Expr n} {Bl Br : Expr (suc n)} where

  codeCodN : {S : Shape} -> ShapeOK S -> {b : FinEl} {f : FinFun} -> CodeTy S RT RM G (S Al Bl) (S Ar Br) b f ->
    (w c : FinEl) -> Selection f w c -> (N N' : Expr n) -> ConvTm G N N' Al ->
    RM G N N' Al w b -> RT G (subst1 Bl N) (subst1 Br N') c
  codeCodN {S} sok {b} {f} r = go (ShapeOK.inj sok (HRs-det (CodeTy.rT r) hrs-refl (ShapeOK.nored sok) (ShapeOK.nored sok)))
                                  (ShapeOK.inj sok (HRs-det (CodeTy.rT' r) hrs-refl (ShapeOK.nored sok) (ShapeOK.nored sok)))
    where
      go : Eq (CodeTy.A r) Al * Eq (CodeTy.B r) Bl -> Eq (CodeTy.A' r) Ar * Eq (CodeTy.B' r) Br ->
           (w c : FinEl) -> Selection f w c -> (N N' : Expr n) -> ConvTm G N N' Al ->
           RM G N N' Al w b -> RT G (subst1 Bl N) (subst1 Br N') c
      go (eA , eB) (eA' , eB') =
        transport2 (\ X Y -> (w c : FinEl) -> Selection f w c -> (N N' : Expr n) -> ConvTm G N N' X ->
                              RM G N N' X w b -> RT G (subst1 Y N) (subst1 Br N') c)
          eA eB (transport (\ Z -> (w c : FinEl) -> Selection f w c -> (N N' : Expr n) -> ConvTm G N N' (CodeTy.A r) ->
                              RM G N N' (CodeTy.A r) w b -> RT G (subst1 (CodeTy.B r) N) (subst1 Z N') c) eB' (CodeTy.cod r))
