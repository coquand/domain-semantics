{-# OPTIONS --without-K #-}
------------------------------------------------------------------------
-- AdequacyRecords.agda  (MIN/ — Pi + U fragment)
--
-- The §3 public record (un)builders for the adequacy stack.
--
-- The stratified public relations Val2/EqVal2/ValTy2/EqValTy2 are
-- *informative*: at a Pi/FunEl code they reduce definitionally to the
-- OpenRecords records at the code's rank-determined stage.  But the edge
-- fields of those records live at that rank-determined stage, NOT at the
-- canonical public level of the component codes.  Adequacy wants to read
-- and build records whose fields are public-level.
--
-- This module defines public-level record types (RValTyPiP / REqValTyPiP
-- / RValPiP / REqValPiP) with their edges phrased on the public relations,
-- and (un)builders that bridge to the stratified records by `shift*`-ing
-- each edge between the record's stage and the components' canonical level.
-- Every record field sits at a stage >= its canonical level (by the RANK
-- structural inequalities + SelectionRank), so the shifts always validate.
--
-- Adequacy then manipulates Pi records only through these, never seeing a
-- stage.  No postulates.
------------------------------------------------------------------------

open import BCDE4.Levels using (LDecAll)
module BCDE4.Valid.Records (D : LDecAll) where

open import BCDE4.Levels using (LExpr ; Valid)

open import BCDE4.Dom.Basic using (U0 ; EqL ; eqL ; EqL-refl ; EqL-sym ; EqL-trans ; EqL-Eq ; eqL-EqL ; EqL-eqL ; eqL-refl)
open import BCDE4.Valid.Core using (U-tr)

open import BCDE4.Dom.Basic
  using (Nat ; zero ; suc ; Top ; tt ; Pair ; mkSigma ; fst ; snd ;
         Le ; Le-refl ; Le-trans ; Le-suc ; max ; Le-max-l ; Le-max-r ;
         FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; Eq ; refl ;
         LevTy ; LevEl ; LPiCode ;
         Eq-transport ; Eq-sym)
open import BCDE4.RussellSyntax using (Expr ; Pi ; U ; App ; subst1 ; LPi ; LApp ; lsub1)
open import BCDE4.RussellTyping
open import BCDE4.Dom.Kernel
  using (EvalFun ; CoherentFun ; CoherentFunTail ; FinMemFun ; FinMemAllU ; LeCode)
open import BCDE4.Model.Selection using (Selection)
open import BCDE4.Dom.Rank
  using (RANK ; RANKFun ; RANK-dom ; RANK-cod ; RANK-fun ; RANK-EvalFun ; RANK-Lcod)
open import BCDE4.Model.SelectionRank using (Selection-RANK-u ; Selection-RANK-v)
open import BCDE4.Valid.Stratified D
open import BCDE4.Valid.Levels D using (shiftVTy ; shiftEVTy ; shiftVl ; shiftEVl)

-- Stratified records at a given stage (same as ValidityMono.SR).
module SR (k : Nat) = OpenRecords
  (Bundle.val (Stage k)) (Bundle.eqval (Stage k))
  (Bundle.valty (Stage k)) (Bundle.eqvalty (Stage k))

------------------------------------------------------------------------
-- Bound helpers
------------------------------------------------------------------------

-- The canonical levels of the component codes are all <= the record's
-- edge stage.  For a Pi-type record the stage is RANK (PiCode b f); for a
-- term record at (FunEl g, PiCode b f) the stage is max (RANK (FunEl g))
-- (RANK (PiCode b f)).  These helpers package the bounds used by shift*.

private
  -- domain b is below the Pi code stage
  le-b-Pi : (b : FinEl) (f : FinFun) -> Le (suc (RANK b)) (RANK (PiCode b f))
  le-b-Pi = RANK-dom

  -- a selected key u (Selection f u v) is below the Pi code stage
  le-u-Pi : {u v : FinEl} (b : FinEl) (f : FinFun) ->
    Selection f u v -> Le (suc (RANK u)) (RANK (PiCode b f))
  le-u-Pi {u} {v} b f sel =
    Le-trans (suc (RANK u)) (suc (RANKFun f)) (RANK (PiCode b f))
      (Selection-RANK-u sel) (RANK-cod b f)

  -- a selected value v (Selection f u v) is below the Pi code stage
  le-v-Pi : {u v : FinEl} (b : FinEl) (f : FinFun) ->
    Selection f u v -> Le (suc (RANK v)) (RANK (PiCode b f))
  le-v-Pi {u} {v} b f sel =
    Le-trans (suc (RANK v)) (suc (RANKFun f)) (RANK (PiCode b f))
      (Selection-RANK-v sel) (RANK-cod b f)

  -- 2-way max bounds (canonical val/eqval level)
  m2l : (x y : FinEl) -> Le (suc (RANK x)) (suc (max (RANK x) (RANK y)))
  m2l x y = Le-max-l (RANK x) (RANK y)
  m2r : (x y : FinEl) -> Le (suc (RANK y)) (suc (max (RANK x) (RANK y)))
  m2r x y = Le-max-r (RANK x) (RANK y)

  -- The term-record stage at (FunEl g, PiCode b f) is
  --   s = max (RANK (FunEl g)) (RANK (PiCode b f))
  -- with the inner valty component sitting one level up (suc s).
  le-Pi-FP : (g : FinFun) (b : FinEl) (f : FinFun) ->
    Le (suc (RANK (PiCode b f))) (suc (max (RANK (FunEl g)) (RANK (PiCode b f))))
  le-Pi-FP g b f = Le-max-r (RANK (FunEl g)) (RANK (PiCode b f))

  le-b-FP : (g : FinFun) (b : FinEl) (f : FinFun) ->
    Le (suc (RANK b)) (max (RANK (FunEl g)) (RANK (PiCode b f)))
  le-b-FP g b f =
    Le-trans (suc (RANK b)) (RANK (PiCode b f)) (max (RANK (FunEl g)) (RANK (PiCode b f)))
      (RANK-dom b f) (Le-max-r (RANK (FunEl g)) (RANK (PiCode b f)))

  le-u-FP : (g : FinFun) (b : FinEl) (f : FinFun) {u v : FinEl} ->
    Selection g u v -> Le (suc (RANK u)) (max (RANK (FunEl g)) (RANK (PiCode b f)))
  le-u-FP g b f {u} {v} sel =
    Le-trans (suc (RANK u)) (RANK (FunEl g)) (max (RANK (FunEl g)) (RANK (PiCode b f)))
      (Selection-RANK-u sel) (Le-max-l (RANK (FunEl g)) (RANK (PiCode b f)))

  le-v-FP : (g : FinFun) (b : FinEl) (f : FinFun) {u v : FinEl} ->
    Selection g u v -> Le (suc (RANK v)) (max (RANK (FunEl g)) (RANK (PiCode b f)))
  le-v-FP g b f {u} {v} sel =
    Le-trans (suc (RANK v)) (RANK (FunEl g)) (max (RANK (FunEl g)) (RANK (PiCode b f)))
      (Selection-RANK-v sel) (Le-max-l (RANK (FunEl g)) (RANK (PiCode b f)))

  le-ef-FP : (g : FinFun) (b : FinEl) (f : FinFun) (u : FinEl) ->
    Le (suc (RANK (EvalFun f u))) (max (RANK (FunEl g)) (RANK (PiCode b f)))
  le-ef-FP g b f u =
    Le-trans (suc (RANK (EvalFun f u))) (RANK (PiCode b f)) (max (RANK (FunEl g)) (RANK (PiCode b f)))
      (Le-trans (suc (RANK (EvalFun f u))) (suc (RANKFun f)) (RANK (PiCode b f))
        (RANK-EvalFun f u) (RANK-cod b f))
      (Le-max-r (RANK (FunEl g)) (RANK (PiCode b f)))

------------------------------------------------------------------------
-- Public-level edge types (phrased on the public relations)
------------------------------------------------------------------------

PiEdgeVal2P : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> Set
PiEdgeVal2P {n} G A B b f =
  (u v : FinEl) -> Selection f u v ->
  (N : Expr n) -> HasType G N A -> Val2 G N A u b ->
  ValTy2 G (subst1 B N) v

PiEdgeEq2P : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> Set
PiEdgeEq2P {n} G A B b f =
  (u v : FinEl) -> Selection f u v ->
  (N1 N2 : Expr n) -> HasType G N1 A -> HasType G N2 A ->
  ConvTm G N1 N2 A -> EqVal2 G N1 N2 A u b ->
  EqValTy2 G (subst1 B N1) (subst1 B N2) v

PiEdgeEqTy2P : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> Expr (suc n) -> FinEl -> FinFun -> Set
PiEdgeEqTy2P {n} G A B B' b f =
  (u v : FinEl) -> Selection f u v ->
  (P : Expr n) -> HasType G P A -> Val2 G P A u b ->
  EqValTy2 G (subst1 B P) (subst1 B' P) v

PiAppVal2P : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> FinFun -> Set
PiAppVal2P {n} G M A0 B0 b f g =
  (u v : FinEl) -> Selection g u v ->
  {A1 : Expr n} {B1 : Expr (suc n)} -> Ann G A0 B0 A1 B1 ->
  (N : Expr n) -> HasType G N A0 -> Val2 G N A0 u b ->
  Val2 G (App A1 B1 M N) (subst1 B0 N) v (EvalFun f u)

PiAppEq2P : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> FinFun -> Set
PiAppEq2P {n} G M A0 B0 b f g =
  (u v : FinEl) -> Selection g u v ->
  {A1 A2 : Expr n} {B1 B2 : Expr (suc n)} ->
  Ann G A0 B0 A1 B1 -> Ann G A0 B0 A2 B2 ->
  (N1 N2 : Expr n) -> HasType G N1 A0 -> HasType G N2 A0 ->
  ConvTm G N1 N2 A0 -> EqVal2 G N1 N2 A0 u b ->
  EqVal2 G (App A1 B1 M N1) (App A2 B2 M N2) (subst1 B0 N1) v (EvalFun f u)

PiAppEqVal2P : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> FinFun -> Set
PiAppEqVal2P {n} G M N A0 B0 b f g =
  (u v : FinEl) -> Selection g u v ->
  {A1 A2 : Expr n} {B1 B2 : Expr (suc n)} ->
  Ann G A0 B0 A1 B1 -> Ann G A0 B0 A2 B2 ->
  (P : Expr n) -> HasType G P A0 -> Val2 G P A0 u b ->
  EqVal2 G (App A1 B1 M P) (App A2 B2 N P) (subst1 B0 P) v (EvalFun f u)

------------------------------------------------------------------------
-- Public-level records
------------------------------------------------------------------------

record RValTyPiP {n : Nat} (G : Ctx n) (M : Expr n) (b : FinEl) (f : FinFun) : Set where
  constructor mkRValTyPiP
  field
    domA   : Expr n
    codB   : Expr (suc n)
    red    : Red3 G M (Pi domA codB)
    cohF   : CoherentFunTail f
    fmAllU : FinMemAllU f b
    htA    : IsType G domA
    htB    : IsType (extend G domA) codB
    valA   : ValTy2 G domA b
    edgeV  : PiEdgeVal2P G domA codB b f
    edgeE  : PiEdgeEq2P G domA codB b f

record REqValTyPiP {n : Nat} (G : Ctx n) (M N : Expr n) (b : FinEl) (f : FinFun) : Set where
  constructor mkREqValTyPiP
  field
    domA   : Expr n
    codB   : Expr (suc n)
    domA'  : Expr n
    codB'  : Expr (suc n)
    redM   : Red3 G M (Pi domA codB)
    redN   : Red3 G N (Pi domA' codB')
    cohF   : CoherentFunTail f
    fmAllU : FinMemAllU f b
    convA  : ConvTy G domA domA'
    convB  : ConvTy (extend G domA) codB codB'
    eqA    : EqValTy2 G domA domA' b
    edgeET : PiEdgeEqTy2P G domA codB codB' b f

record RValPiP {n : Nat} (G : Ctx n) (M A : Expr n) (g : FinFun) (b : FinEl) (f : FinFun) : Set where
  constructor mkRValPiP
  field
    domA0  : Expr n
    codB0  : Expr (suc n)
    red    : Red3 G A (Pi domA0 codB0)
    cohG   : CoherentFun g
    fmG    : FinMemFun g b f
    appV   : PiAppVal2P G M domA0 codB0 b f g
    appE   : PiAppEq2P G M domA0 codB0 b f g

record REqValPiP {n : Nat} (G : Ctx n) (M N A : Expr n) (g : FinFun) (b : FinEl) (f : FinFun) : Set where
  constructor mkREqValPiP
  field
    domA0  : Expr n
    codB0  : Expr (suc n)
    red    : Red3 G A (Pi domA0 codB0)
    cohG   : CoherentFun g
    fmG    : FinMemFun g b f
    appEV  : PiAppEqVal2P G M N domA0 codB0 b f g

------------------------------------------------------------------------
-- ValTyPi : ValTy2 G M (PiCode b f)  <->  RValTyPiP G M b f
--   record stage  t = RANK (PiCode b f)
------------------------------------------------------------------------

un-ValTyPi : {n : Nat} {G : Ctx n} {M : Expr n} {b : FinEl} {f : FinFun} ->
  ValTy2 G M (PiCode b f) -> RValTyPiP G M b f
un-ValTyPi {n} {G} {M} {b} {f} vt = record
  { domA   = A
  ; codB   = B
  ; red    = RValTyPi.red vt
  ; cohF   = RValTyPi.cohF vt
  ; fmAllU = RValTyPi.fmAllU vt
  ; htA    = RValTyPi.htA vt
  ; htB    = RValTyPi.htB vt
  ; valA   = shiftVTy t (suc (RANK b)) G A b (le-b-Pi b f) (Le-refl (suc (RANK b)))
               (RValTyPi.valA vt)
  ; edgeV  = \ u v sel N htN valN ->
      let valN-t = shiftVl (suc (max (RANK u) (RANK b))) t G N A u b
                     (m2l u b) (m2r u b) (le-u-Pi b f sel) (le-b-Pi b f) valN
      in shiftVTy t (suc (RANK v)) G (subst1 B N) v
           (le-v-Pi b f sel) (Le-refl (suc (RANK v)))
           (RValTyPi.edgeV vt u v sel N htN valN-t)
  ; edgeE  = \ u v sel N1 N2 htN1 htN2 cvN eqN ->
      let eqN-t = shiftEVl (suc (max (RANK u) (RANK b))) t G N1 N2 A u b
                    (m2l u b) (m2r u b) (le-u-Pi b f sel) (le-b-Pi b f) eqN
      in shiftEVTy t (suc (RANK v)) G (subst1 B N1) (subst1 B N2) v
           (le-v-Pi b f sel) (Le-refl (suc (RANK v)))
           (RValTyPi.edgeE vt u v sel N1 N2 htN1 htN2 cvN eqN-t)
  }
  where
    open SR (RANK (PiCode b f))
    t = RANK (PiCode b f)
    A = RValTyPi.domA vt
    B = RValTyPi.codB vt

mk-ValTyPi : {n : Nat} {G : Ctx n} {M : Expr n} {b : FinEl} {f : FinFun} ->
  RValTyPiP G M b f -> ValTy2 G M (PiCode b f)
mk-ValTyPi {n} {G} {M} {b} {f} r = record
  { domA   = A
  ; codB   = B
  ; red    = RValTyPiP.red r
  ; cohF   = RValTyPiP.cohF r
  ; fmAllU = RValTyPiP.fmAllU r
  ; htA    = RValTyPiP.htA r
  ; htB    = RValTyPiP.htB r
  ; valA   = shiftVTy (suc (RANK b)) t G A b (Le-refl (suc (RANK b))) (le-b-Pi b f)
               (RValTyPiP.valA r)
  ; edgeV  = \ u v sel N htN valN-t ->
      let valN = shiftVl t (suc (max (RANK u) (RANK b))) G N A u b
                   (le-u-Pi b f sel) (le-b-Pi b f) (m2l u b) (m2r u b) valN-t
      in shiftVTy (suc (RANK v)) t G (subst1 B N) v
           (Le-refl (suc (RANK v))) (le-v-Pi b f sel)
           (RValTyPiP.edgeV r u v sel N htN valN)
  ; edgeE  = \ u v sel N1 N2 htN1 htN2 cvN eqN-t ->
      let eqN = shiftEVl t (suc (max (RANK u) (RANK b))) G N1 N2 A u b
                  (le-u-Pi b f sel) (le-b-Pi b f) (m2l u b) (m2r u b) eqN-t
      in shiftEVTy (suc (RANK v)) t G (subst1 B N1) (subst1 B N2) v
           (Le-refl (suc (RANK v))) (le-v-Pi b f sel)
           (RValTyPiP.edgeE r u v sel N1 N2 htN1 htN2 cvN eqN)
  }
  where
    open SR (RANK (PiCode b f))
    t = RANK (PiCode b f)
    A = RValTyPiP.domA r
    B = RValTyPiP.codB r

------------------------------------------------------------------------
-- EqValTyPi : EqValTy2 G M N (PiCode b f)
--   reduces to  Pair (ValTy2 G M (PiCode b f))
--                    (Pair (ValTy2 G N (PiCode b f)) (REqValTyPi t G M N b f))
-- The two ValTy2 components are already at the canonical level; only the
-- REqValTyPi core needs edge shifting.
------------------------------------------------------------------------

eqvalTyPi-fst : {n : Nat} {G : Ctx n} {M N : Expr n} {b : FinEl} {f : FinFun} ->
  EqValTy2 G M N (PiCode b f) -> ValTy2 G M (PiCode b f)
eqvalTyPi-fst {G = G} {M} {N} {b} {f} eqvt = fst eqvt

eqvalTyPi-snd : {n : Nat} {G : Ctx n} {M N : Expr n} {b : FinEl} {f : FinFun} ->
  EqValTy2 G M N (PiCode b f) -> ValTy2 G N (PiCode b f)
eqvalTyPi-snd {G = G} {M} {N} {b} {f} eqvt = fst (snd eqvt)

un-REqValTyPi : {n : Nat} {G : Ctx n} {M N : Expr n} {b : FinEl} {f : FinFun} ->
  EqValTy2 G M N (PiCode b f) -> REqValTyPiP G M N b f
un-REqValTyPi {n} {G} {M} {N} {b} {f} eqvt = record
  { domA   = A   ; codB  = B
  ; domA'  = A'  ; codB' = B'
  ; redM   = REqValTyPi.redM core
  ; redN   = REqValTyPi.redN core
  ; cohF   = REqValTyPi.cohF core
  ; fmAllU = REqValTyPi.fmAllU core
  ; convA  = REqValTyPi.convA core
  ; convB  = REqValTyPi.convB core
  ; eqA    = shiftEVTy t (suc (RANK b)) G A A' b (le-b-Pi b f) (Le-refl (suc (RANK b)))
               (REqValTyPi.eqA core)
  ; edgeET = \ u v sel P htP valP ->
      let valP-t = shiftVl (suc (max (RANK u) (RANK b))) t G P A u b
                     (m2l u b) (m2r u b) (le-u-Pi b f sel) (le-b-Pi b f) valP
      in shiftEVTy t (suc (RANK v)) G (subst1 B P) (subst1 B' P) v
           (le-v-Pi b f sel) (Le-refl (suc (RANK v)))
           (REqValTyPi.edgeET core u v sel P htP valP-t)
  }
  where
    open SR (RANK (PiCode b f))
    t = RANK (PiCode b f)
    core = snd (snd eqvt)
    A  = REqValTyPi.domA core   ; B  = REqValTyPi.codB core
    A' = REqValTyPi.domA' core  ; B' = REqValTyPi.codB' core

mk-EqValTyPi : {n : Nat} {G : Ctx n} {M N : Expr n} {b : FinEl} {f : FinFun} ->
  ValTy2 G M (PiCode b f) -> ValTy2 G N (PiCode b f) ->
  REqValTyPiP G M N b f -> EqValTy2 G M N (PiCode b f)
mk-EqValTyPi {n} {G} {M} {N} {b} {f} vtM vtN r =
  mkSigma vtM (mkSigma vtN (record
    { domA   = A   ; codB  = B
    ; domA'  = A'  ; codB' = B'
    ; redM   = REqValTyPiP.redM r
    ; redN   = REqValTyPiP.redN r
    ; cohF   = REqValTyPiP.cohF r
    ; fmAllU = REqValTyPiP.fmAllU r
    ; convA  = REqValTyPiP.convA r
    ; convB  = REqValTyPiP.convB r
    ; eqA    = shiftEVTy (suc (RANK b)) t G A A' b (Le-refl (suc (RANK b))) (le-b-Pi b f)
                 (REqValTyPiP.eqA r)
    ; edgeET = \ u v sel P htP valP-t ->
        let valP = shiftVl t (suc (max (RANK u) (RANK b))) G P A u b
                     (le-u-Pi b f sel) (le-b-Pi b f) (m2l u b) (m2r u b) valP-t
        in shiftEVTy (suc (RANK v)) t G (subst1 B P) (subst1 B' P) v
             (Le-refl (suc (RANK v))) (le-v-Pi b f sel)
             (REqValTyPiP.edgeET r u v sel P htP valP)
    }))
  where
    open SR (RANK (PiCode b f))
    t = RANK (PiCode b f)
    A  = REqValTyPiP.domA r   ; B  = REqValTyPiP.codB r
    A' = REqValTyPiP.domA' r  ; B' = REqValTyPiP.codB' r

------------------------------------------------------------------------
-- ValPi : Val2 G M A (FunEl g) (PiCode b f)
--   reduces to  Pair (ValTy2 G A (PiCode b f) @ stage suc s)
--                    (RValPi s G M A g b f)
--   with s = max (RANK (FunEl g)) (RANK (PiCode b f)).
------------------------------------------------------------------------

valPi-ty : {n : Nat} {G : Ctx n} {M A : Expr n} {g : FinFun} {b : FinEl} {f : FinFun} ->
  Val2 G M A (FunEl g) (PiCode b f) -> ValTy2 G A (PiCode b f)
valPi-ty {n} {G} {M} {A} {g} {b} {f} val =
  shiftVTy (suc (max (RANK (FunEl g)) (RANK (PiCode b f)))) (suc (RANK (PiCode b f)))
    G A (PiCode b f) (le-Pi-FP g b f) (Le-refl (suc (RANK (PiCode b f)))) (fst val)

un-ValPi : {n : Nat} {G : Ctx n} {M A : Expr n} {g : FinFun} {b : FinEl} {f : FinFun} ->
  Val2 G M A (FunEl g) (PiCode b f) -> RValPiP G M A g b f
un-ValPi {n} {G} {M} {A} {g} {b} {f} val = record
  { domA0 = A0 ; codB0 = B0
  ; red   = RValPi.red vpi
  ; cohG  = RValPi.cohG vpi
  ; fmG   = RValPi.fmG vpi
  ; appV  = \ u v sel {A1} {B1} an N htN valN ->
      let valN-s = shiftVl (suc (max (RANK u) (RANK b))) s G N A0 u b
                     (m2l u b) (m2r u b) (le-u-FP g b f sel) (le-b-FP g b f) valN
      in shiftVl s (suc (max (RANK v) (RANK (EvalFun f u))))
           G (App A1 B1 M N) (subst1 B0 N) v (EvalFun f u)
           (le-v-FP g b f sel) (le-ef-FP g b f u)
           (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
           (RValPi.appV vpi u v sel an N htN valN-s)
  ; appE  = \ u v sel {A1} {A2} {B1} {B2} an1 an2 N1 N2 htN1 htN2 cvN eqN ->
      let eqN-s = shiftEVl (suc (max (RANK u) (RANK b))) s G N1 N2 A0 u b
                    (m2l u b) (m2r u b) (le-u-FP g b f sel) (le-b-FP g b f) eqN
      in shiftEVl s (suc (max (RANK v) (RANK (EvalFun f u))))
           G (App A1 B1 M N1) (App A2 B2 M N2) (subst1 B0 N1) v (EvalFun f u)
           (le-v-FP g b f sel) (le-ef-FP g b f u)
           (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
           (RValPi.appE vpi u v sel an1 an2 N1 N2 htN1 htN2 cvN eqN-s)
  }
  where
    open SR (max (RANK (FunEl g)) (RANK (PiCode b f)))
    s = max (RANK (FunEl g)) (RANK (PiCode b f))
    vpi = snd val
    A0 = RValPi.domA0 vpi
    B0 = RValPi.codB0 vpi

mk-ValPi : {n : Nat} {G : Ctx n} {M A : Expr n} {g : FinFun} {b : FinEl} {f : FinFun} ->
  ValTy2 G A (PiCode b f) -> RValPiP G M A g b f -> Val2 G M A (FunEl g) (PiCode b f)
mk-ValPi {n} {G} {M} {A} {g} {b} {f} vtA r =
  mkSigma
    (shiftVTy (suc (RANK (PiCode b f))) (suc (max (RANK (FunEl g)) (RANK (PiCode b f))))
      G A (PiCode b f) (Le-refl (suc (RANK (PiCode b f)))) (le-Pi-FP g b f) vtA)
    (record
      { domA0 = A0 ; codB0 = B0
      ; red   = RValPiP.red r
      ; cohG  = RValPiP.cohG r
      ; fmG   = RValPiP.fmG r
      ; appV  = \ u v sel {A1} {B1} an N htN valN-s ->
          let valN = shiftVl s (suc (max (RANK u) (RANK b))) G N A0 u b
                       (le-u-FP g b f sel) (le-b-FP g b f) (m2l u b) (m2r u b) valN-s
          in shiftVl (suc (max (RANK v) (RANK (EvalFun f u)))) s
               G (App A1 B1 M N) (subst1 B0 N) v (EvalFun f u)
               (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
               (le-v-FP g b f sel) (le-ef-FP g b f u)
               (RValPiP.appV r u v sel an N htN valN)
      ; appE  = \ u v sel {A1} {A2} {B1} {B2} an1 an2 N1 N2 htN1 htN2 cvN eqN-s ->
          let eqN = shiftEVl s (suc (max (RANK u) (RANK b))) G N1 N2 A0 u b
                      (le-u-FP g b f sel) (le-b-FP g b f) (m2l u b) (m2r u b) eqN-s
          in shiftEVl (suc (max (RANK v) (RANK (EvalFun f u)))) s
               G (App A1 B1 M N1) (App A2 B2 M N2) (subst1 B0 N1) v (EvalFun f u)
               (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
               (le-v-FP g b f sel) (le-ef-FP g b f u)
               (RValPiP.appE r u v sel an1 an2 N1 N2 htN1 htN2 cvN eqN)
      })
  where
    open SR (max (RANK (FunEl g)) (RANK (PiCode b f)))
    s = max (RANK (FunEl g)) (RANK (PiCode b f))
    A0 = RValPiP.domA0 r
    B0 = RValPiP.codB0 r

------------------------------------------------------------------------
-- EqValPi : EqVal2 G M N A (FunEl g) (PiCode b f)
--   reduces to  Pair (ValTy2 G A (PiCode b f))
--                    (Pair (RValPi s G M A g b f)
--                          (Pair (RValPi s G N A g b f)
--                                (REqValPi s G M N A g b f)))
------------------------------------------------------------------------

eqvalPi-ty : {n : Nat} {G : Ctx n} {M N A : Expr n} {g : FinFun} {b : FinEl} {f : FinFun} ->
  EqVal2 G M N A (FunEl g) (PiCode b f) -> ValTy2 G A (PiCode b f)
eqvalPi-ty {n} {G} {M} {N} {A} {g} {b} {f} ev =
  shiftVTy (suc (max (RANK (FunEl g)) (RANK (PiCode b f)))) (suc (RANK (PiCode b f)))
    G A (PiCode b f) (le-Pi-FP g b f) (Le-refl (suc (RANK (PiCode b f)))) (fst ev)

private
  -- shared RValPi -> RValPiP conversion at stage s (used for both M and N legs)
  conv-RValPi : {n : Nat} (G : Ctx n) (Mx A : Expr n) (g : FinFun) (b : FinEl) (f : FinFun) ->
    SR.RValPi (max (RANK (FunEl g)) (RANK (PiCode b f))) G Mx A g b f ->
    RValPiP G Mx A g b f
  conv-RValPi {n} G Mx A g b f vpi = record
    { domA0 = A0 ; codB0 = B0
    ; red   = RValPi.red vpi
    ; cohG  = RValPi.cohG vpi
    ; fmG   = RValPi.fmG vpi
    ; appV  = \ u v sel {A1} {B1} an N htN valN ->
        let valN-s = shiftVl (suc (max (RANK u) (RANK b))) s G N A0 u b
                       (m2l u b) (m2r u b) (le-u-FP g b f sel) (le-b-FP g b f) valN
        in shiftVl s (suc (max (RANK v) (RANK (EvalFun f u))))
             G (App A1 B1 Mx N) (subst1 B0 N) v (EvalFun f u)
             (le-v-FP g b f sel) (le-ef-FP g b f u)
             (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
             (RValPi.appV vpi u v sel an N htN valN-s)
    ; appE  = \ u v sel {A1} {A2} {B1} {B2} an1 an2 N1 N2 htN1 htN2 cvN eqN ->
        let eqN-s = shiftEVl (suc (max (RANK u) (RANK b))) s G N1 N2 A0 u b
                      (m2l u b) (m2r u b) (le-u-FP g b f sel) (le-b-FP g b f) eqN
        in shiftEVl s (suc (max (RANK v) (RANK (EvalFun f u))))
             G (App A1 B1 Mx N1) (App A2 B2 Mx N2) (subst1 B0 N1) v (EvalFun f u)
             (le-v-FP g b f sel) (le-ef-FP g b f u)
             (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
             (RValPi.appE vpi u v sel an1 an2 N1 N2 htN1 htN2 cvN eqN-s)
    }
    where
      open SR (max (RANK (FunEl g)) (RANK (PiCode b f)))
      s = max (RANK (FunEl g)) (RANK (PiCode b f))
      A0 = RValPi.domA0 vpi
      B0 = RValPi.codB0 vpi

eqvalPi-fst : {n : Nat} {G : Ctx n} {M N A : Expr n} {g : FinFun} {b : FinEl} {f : FinFun} ->
  EqVal2 G M N A (FunEl g) (PiCode b f) -> RValPiP G M A g b f
eqvalPi-fst {n} {G} {M} {N} {A} {g} {b} {f} ev = conv-RValPi G M A g b f (fst (snd ev))

eqvalPi-snd : {n : Nat} {G : Ctx n} {M N A : Expr n} {g : FinFun} {b : FinEl} {f : FinFun} ->
  EqVal2 G M N A (FunEl g) (PiCode b f) -> RValPiP G N A g b f
eqvalPi-snd {n} {G} {M} {N} {A} {g} {b} {f} ev = conv-RValPi G N A g b f (fst (snd (snd ev)))

un-REqValPi : {n : Nat} {G : Ctx n} {M N A : Expr n} {g : FinFun} {b : FinEl} {f : FinFun} ->
  EqVal2 G M N A (FunEl g) (PiCode b f) -> REqValPiP G M N A g b f
un-REqValPi {n} {G} {M} {N} {A} {g} {b} {f} ev = record
  { domA0 = A0 ; codB0 = B0
  ; red   = REqValPi.red core
  ; cohG  = REqValPi.cohG core
  ; fmG   = REqValPi.fmG core
  ; appEV = \ u v sel {A1} {A2} {B1} {B2} an1 an2 P htP valP ->
      let valP-s = shiftVl (suc (max (RANK u) (RANK b))) s G P A0 u b
                     (m2l u b) (m2r u b) (le-u-FP g b f sel) (le-b-FP g b f) valP
      in shiftEVl s (suc (max (RANK v) (RANK (EvalFun f u))))
           G (App A1 B1 M P) (App A2 B2 N P) (subst1 B0 P) v (EvalFun f u)
           (le-v-FP g b f sel) (le-ef-FP g b f u)
           (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
           (REqValPi.appEV core u v sel an1 an2 P htP valP-s)
  }
  where
    open SR (max (RANK (FunEl g)) (RANK (PiCode b f)))
    s = max (RANK (FunEl g)) (RANK (PiCode b f))
    core = snd (snd (snd ev))
    A0 = REqValPi.domA0 core
    B0 = REqValPi.codB0 core

mk-EqValPi : {n : Nat} {G : Ctx n} {M N A : Expr n} {g : FinFun} {b : FinEl} {f : FinFun} ->
  ValTy2 G A (PiCode b f) -> RValPiP G M A g b f -> RValPiP G N A g b f ->
  REqValPiP G M N A g b f -> EqVal2 G M N A (FunEl g) (PiCode b f)
mk-EqValPi {n} {G} {M} {N} {A} {g} {b} {f} vtA rM rN rE =
  mkSigma vtA-up (mkSigma vpiM (mkSigma vpiN core))
  where
    s = max (RANK (FunEl g)) (RANK (PiCode b f))
    vtA-up : Bundle.valty (Stage (suc s)) G A (PiCode b f)
    vtA-up = shiftVTy (suc (RANK (PiCode b f))) (suc s) G A (PiCode b f)
               (Le-refl (suc (RANK (PiCode b f)))) (le-Pi-FP g b f) vtA
    mkPi : (Mx : Expr n) -> RValPiP G Mx A g b f -> SR.RValPi s G Mx A g b f
    mkPi Mx r = record
      { domA0 = RValPiP.domA0 r ; codB0 = RValPiP.codB0 r
      ; red   = RValPiP.red r
      ; cohG  = RValPiP.cohG r
      ; fmG   = RValPiP.fmG r
      ; appV  = \ u v sel {A1} {B1} an N htN valN-s ->
          let valN = shiftVl s (suc (max (RANK u) (RANK b))) G N (RValPiP.domA0 r) u b
                       (le-u-FP g b f sel) (le-b-FP g b f) (m2l u b) (m2r u b) valN-s
          in shiftVl (suc (max (RANK v) (RANK (EvalFun f u)))) s
               G (App A1 B1 Mx N) (subst1 (RValPiP.codB0 r) N) v (EvalFun f u)
               (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
               (le-v-FP g b f sel) (le-ef-FP g b f u)
               (RValPiP.appV r u v sel an N htN valN)
      ; appE  = \ u v sel {A1} {A2} {B1} {B2} an1 an2 N1 N2 htN1 htN2 cvN eqN-s ->
          let eqN = shiftEVl s (suc (max (RANK u) (RANK b))) G N1 N2 (RValPiP.domA0 r) u b
                      (le-u-FP g b f sel) (le-b-FP g b f) (m2l u b) (m2r u b) eqN-s
          in shiftEVl (suc (max (RANK v) (RANK (EvalFun f u)))) s
               G (App A1 B1 Mx N1) (App A2 B2 Mx N2) (subst1 (RValPiP.codB0 r) N1) v (EvalFun f u)
               (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
               (le-v-FP g b f sel) (le-ef-FP g b f u)
               (RValPiP.appE r u v sel an1 an2 N1 N2 htN1 htN2 cvN eqN)
      }
    vpiM = mkPi M rM
    vpiN = mkPi N rN
    core : SR.REqValPi s G M N A g b f
    core = record
      { domA0 = REqValPiP.domA0 rE ; codB0 = REqValPiP.codB0 rE
      ; red   = REqValPiP.red rE
      ; cohG  = REqValPiP.cohG rE
      ; fmG   = REqValPiP.fmG rE
      ; appEV = \ u v sel {A1} {A2} {B1} {B2} an1 an2 P htP valP-s ->
          let valP = shiftVl s (suc (max (RANK u) (RANK b))) G P (REqValPiP.domA0 rE) u b
                       (le-u-FP g b f sel) (le-b-FP g b f) (m2l u b) (m2r u b) valP-s
          in shiftEVl (suc (max (RANK v) (RANK (EvalFun f u)))) s
               G (App A1 B1 M P) (App A2 B2 N P) (subst1 (REqValPiP.codB0 rE) P) v (EvalFun f u)
               (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
               (le-v-FP g b f sel) (le-ef-FP g b f u)
               (REqValPiP.appEV rE u v sel an1 an2 P htP valP)
      }

------------------------------------------------------------------------
-- Level products [alpha]A, at the code LPiCode f.
--
-- Same shape as the Pi records, with the domain replaced by the flat set
-- of level tokens: an argument is a level l admissible for the selected
-- key (LeCode u (LevEl (codeL G l))), a fact that does not depend on the
-- stage, so only the codomain / result relations are shifted.
------------------------------------------------------------------------

private
  -- a selected value v (Selection f u v) is below the LPi code stage
  le-v-LPi : {u v : FinEl} (f : FinFun) ->
    Selection f u v -> Le (suc (RANK v)) (RANK (LPiCode f))
  le-v-LPi {u} {v} f sel =
    Le-trans (suc (RANK v)) (suc (RANKFun f)) (RANK (LPiCode f))
      (Selection-RANK-v sel) (RANK-Lcod f)

  -- term-record stage  s = max (RANK (FunEl g)) (RANK (LPiCode f))
  le-LPi-FL : (g : FinFun) (f : FinFun) ->
    Le (suc (RANK (LPiCode f))) (suc (max (RANK (FunEl g)) (RANK (LPiCode f))))
  le-LPi-FL g f = Le-max-r (RANK (FunEl g)) (RANK (LPiCode f))

  le-v-FL : (g : FinFun) (f : FinFun) {u v : FinEl} ->
    Selection g u v -> Le (suc (RANK v)) (max (RANK (FunEl g)) (RANK (LPiCode f)))
  le-v-FL g f {u} {v} sel =
    Le-trans (suc (RANK v)) (RANK (FunEl g)) (max (RANK (FunEl g)) (RANK (LPiCode f)))
      (Selection-RANK-v sel) (Le-max-l (RANK (FunEl g)) (RANK (LPiCode f)))

  le-ef-FL : (g : FinFun) (f : FinFun) (u : FinEl) ->
    Le (suc (RANK (EvalFun f u))) (max (RANK (FunEl g)) (RANK (LPiCode f)))
  le-ef-FL g f u =
    Le-trans (suc (RANK (EvalFun f u))) (RANK (LPiCode f)) (max (RANK (FunEl g)) (RANK (LPiCode f)))
      (Le-trans (suc (RANK (EvalFun f u))) (suc (RANKFun f)) (RANK (LPiCode f))
        (RANK-EvalFun f u) (RANK-Lcod f))
      (Le-max-r (RANK (FunEl g)) (RANK (LPiCode f)))

------------------------------------------------------------------------
-- Public-level edge / application types for level products
------------------------------------------------------------------------

LEdgeVal2P : {n : Nat} -> Ctx n -> Expr n -> FinFun -> Set
LEdgeVal2P {n} G A f =
  (u v : FinEl) -> Selection f u v ->
  (l : LExpr) -> LeCode u (LevEl (codeL G l)) ->
  ValTy2 G (lsub1 A l) v

LEdgeEqTy2P : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinFun -> Set
LEdgeEqTy2P {n} G A A' f =
  (u v : FinEl) -> Selection f u v ->
  (l : LExpr) -> LeCode u (LevEl (codeL G l)) ->
  EqValTy2 G (lsub1 A l) (lsub1 A' l) v

LAppVal2P : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinFun -> FinFun -> Set
LAppVal2P {n} G M A0 f g =
  (u v : FinEl) -> Selection g u v ->
  {A1 : Expr n} -> LAnn G A0 A1 ->
  (l : LExpr) -> LeCode u (LevEl (codeL G l)) ->
  Val2 G (LApp A1 M l) (lsub1 A0 l) v (EvalFun f u)

LAppEqVal2P : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> FinFun -> FinFun -> Set
LAppEqVal2P {n} G M N A0 f g =
  (u v : FinEl) -> Selection g u v ->
  {A1 A2 : Expr n} -> LAnn G A0 A1 -> LAnn G A0 A2 ->
  (l : LExpr) -> LeCode u (LevEl (codeL G l)) ->
  EqVal2 G (LApp A1 M l) (LApp A2 N l) (lsub1 A0 l) v (EvalFun f u)

LEdgeLvl2P : {n : Nat} -> Ctx n -> Expr n -> FinFun -> Set
LEdgeLvl2P {n} G A f =
  (u v : FinEl) -> Selection f u v ->
  (l l' : LExpr) -> Valid (lctx G) l l' -> LeCode u (LevEl (codeL G l)) ->
  EqValTy2 G (lsub1 A l) (lsub1 A l') v

LAppLvl2P : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinFun -> FinFun -> Set
LAppLvl2P {n} G M A0 f g =
  (u v : FinEl) -> Selection g u v ->
  {A1 A2 : Expr n} -> LAnn G A0 A1 -> LAnn G A0 A2 ->
  (l l' : LExpr) -> Valid (lctx G) l l' -> LeCode u (LevEl (codeL G l)) ->
  EqVal2 G (LApp A1 M l) (LApp A2 M l') (lsub1 A0 l) v (EvalFun f u)

------------------------------------------------------------------------
-- Public-level records for level products
------------------------------------------------------------------------

record RValTyLPiP {n : Nat} (G : Ctx n) (M : Expr n) (f : FinFun) : Set where
  constructor mkRValTyLPiP
  field
    domA   : Expr n
    red    : Red3 G M (LPi domA)
    cohF   : CoherentFunTail f
    fmAllU : FinMemAllU f LevTy
    htA    : IsType (addL G) domA
    edgeV  : LEdgeVal2P G domA f
    edgeLE : LEdgeLvl2P G domA f

record REqValTyLPiP {n : Nat} (G : Ctx n) (M N : Expr n) (f : FinFun) : Set where
  constructor mkREqValTyLPiP
  field
    domA   : Expr n
    domA'  : Expr n
    redM   : Red3 G M (LPi domA)
    redN   : Red3 G N (LPi domA')
    cohF   : CoherentFunTail f
    fmAllU : FinMemAllU f LevTy
    convA  : ConvTy (addL G) domA domA'
    edgeET : LEdgeEqTy2P G domA domA' f

record RValLPiP {n : Nat} (G : Ctx n) (M A : Expr n) (g : FinFun) (f : FinFun) : Set where
  constructor mkRValLPiP
  field
    domA0  : Expr n
    red    : Red3 G A (LPi domA0)
    cohG   : CoherentFun g
    fmG    : FinMemFun g LevTy f
    appV   : LAppVal2P G M domA0 f g
    appLE  : LAppLvl2P G M domA0 f g

record REqValLPiP {n : Nat} (G : Ctx n) (M N A : Expr n) (g : FinFun) (f : FinFun) : Set where
  constructor mkREqValLPiP
  field
    domA0  : Expr n
    red    : Red3 G A (LPi domA0)
    cohG   : CoherentFun g
    fmG    : FinMemFun g LevTy f
    appEV  : LAppEqVal2P G M N domA0 f g

------------------------------------------------------------------------
-- ValTyLPi : ValTy2 G M (LPiCode f)  <->  RValTyLPiP G M f
--   record stage  t = RANK (LPiCode f)
------------------------------------------------------------------------

un-ValTyLPi : {n : Nat} {G : Ctx n} {M : Expr n} {f : FinFun} ->
  ValTy2 G M (LPiCode f) -> RValTyLPiP G M f
un-ValTyLPi {n} {G} {M} {f} vt = record
  { domA   = A
  ; red    = RValTyLPi.red vt
  ; cohF   = RValTyLPi.cohF vt
  ; fmAllU = RValTyLPi.fmAllU vt
  ; htA    = RValTyLPi.htA vt
  ; edgeV  = \ u v sel l lel ->
      shiftVTy t (suc (RANK v)) G (lsub1 A l) v (le-v-LPi f sel) (Le-refl (suc (RANK v)))
        (RValTyLPi.edgeV vt u v sel l lel)
  ; edgeLE = \ u v sel l l' e lel ->
      shiftEVTy t (suc (RANK v)) G (lsub1 A l) (lsub1 A l') v (le-v-LPi f sel) (Le-refl (suc (RANK v)))
        (RValTyLPi.edgeLE vt u v sel l l' e lel)
  }
  where
    open SR (RANK (LPiCode f))
    t = RANK (LPiCode f)
    A = RValTyLPi.domA vt

mk-ValTyLPi : {n : Nat} {G : Ctx n} {M : Expr n} {f : FinFun} ->
  RValTyLPiP G M f -> ValTy2 G M (LPiCode f)
mk-ValTyLPi {n} {G} {M} {f} r = record
  { domA   = A
  ; red    = RValTyLPiP.red r
  ; cohF   = RValTyLPiP.cohF r
  ; fmAllU = RValTyLPiP.fmAllU r
  ; htA    = RValTyLPiP.htA r
  ; edgeV  = \ u v sel l lel ->
      shiftVTy (suc (RANK v)) t G (lsub1 A l) v (Le-refl (suc (RANK v))) (le-v-LPi f sel)
        (RValTyLPiP.edgeV r u v sel l lel)
  ; edgeLE = \ u v sel l l' e lel ->
      shiftEVTy (suc (RANK v)) t G (lsub1 A l) (lsub1 A l') v (Le-refl (suc (RANK v))) (le-v-LPi f sel)
        (RValTyLPiP.edgeLE r u v sel l l' e lel)
  }
  where
    open SR (RANK (LPiCode f))
    t = RANK (LPiCode f)
    A = RValTyLPiP.domA r

------------------------------------------------------------------------
-- EqValTyLPi : EqValTy2 G M N (LPiCode f)
--   reduces to  Pair (ValTy2 G M (LPiCode f))
--                    (Pair (ValTy2 G N (LPiCode f)) (REqValTyLPi t G M N f))
------------------------------------------------------------------------

eqvalTyLPi-fst : {n : Nat} {G : Ctx n} {M N : Expr n} {f : FinFun} ->
  EqValTy2 G M N (LPiCode f) -> ValTy2 G M (LPiCode f)
eqvalTyLPi-fst eqvt = fst eqvt

eqvalTyLPi-snd : {n : Nat} {G : Ctx n} {M N : Expr n} {f : FinFun} ->
  EqValTy2 G M N (LPiCode f) -> ValTy2 G N (LPiCode f)
eqvalTyLPi-snd eqvt = fst (snd eqvt)

un-REqValTyLPi : {n : Nat} {G : Ctx n} {M N : Expr n} {f : FinFun} ->
  EqValTy2 G M N (LPiCode f) -> REqValTyLPiP G M N f
un-REqValTyLPi {n} {G} {M} {N} {f} eqvt = record
  { domA   = A
  ; domA'  = A'
  ; redM   = REqValTyLPi.redM core
  ; redN   = REqValTyLPi.redN core
  ; cohF   = REqValTyLPi.cohF core
  ; fmAllU = REqValTyLPi.fmAllU core
  ; convA  = REqValTyLPi.convA core
  ; edgeET = \ u v sel l lel ->
      shiftEVTy t (suc (RANK v)) G (lsub1 A l) (lsub1 A' l) v (le-v-LPi f sel) (Le-refl (suc (RANK v)))
        (REqValTyLPi.edgeET core u v sel l lel)
  }
  where
    open SR (RANK (LPiCode f))
    t = RANK (LPiCode f)
    core = snd (snd eqvt)
    A  = REqValTyLPi.domA core
    A' = REqValTyLPi.domA' core

mk-EqValTyLPi : {n : Nat} {G : Ctx n} {M N : Expr n} {f : FinFun} ->
  ValTy2 G M (LPiCode f) -> ValTy2 G N (LPiCode f) ->
  REqValTyLPiP G M N f -> EqValTy2 G M N (LPiCode f)
mk-EqValTyLPi {n} {G} {M} {N} {f} vtM vtN r =
  mkSigma vtM (mkSigma vtN (record
    { domA   = A
    ; domA'  = A'
    ; redM   = REqValTyLPiP.redM r
    ; redN   = REqValTyLPiP.redN r
    ; cohF   = REqValTyLPiP.cohF r
    ; fmAllU = REqValTyLPiP.fmAllU r
    ; convA  = REqValTyLPiP.convA r
    ; edgeET = \ u v sel l lel ->
        shiftEVTy (suc (RANK v)) t G (lsub1 A l) (lsub1 A' l) v (Le-refl (suc (RANK v))) (le-v-LPi f sel)
          (REqValTyLPiP.edgeET r u v sel l lel)
    }))
  where
    open SR (RANK (LPiCode f))
    t = RANK (LPiCode f)
    A  = REqValTyLPiP.domA r
    A' = REqValTyLPiP.domA' r

------------------------------------------------------------------------
-- ValLPi : Val2 G M A (FunEl g) (LPiCode f)
--   reduces to  Pair (ValTy2 G A (LPiCode f) @ stage suc s)
--                    (RValLPi s G M A g f)
--   with s = max (RANK (FunEl g)) (RANK (LPiCode f)).
------------------------------------------------------------------------

valLPi-ty : {n : Nat} {G : Ctx n} {M A : Expr n} {g : FinFun} {f : FinFun} ->
  Val2 G M A (FunEl g) (LPiCode f) -> ValTy2 G A (LPiCode f)
valLPi-ty {n} {G} {M} {A} {g} {f} val =
  shiftVTy (suc (max (RANK (FunEl g)) (RANK (LPiCode f)))) (suc (RANK (LPiCode f)))
    G A (LPiCode f) (le-LPi-FL g f) (Le-refl (suc (RANK (LPiCode f)))) (fst val)

private
  -- shared RValLPi -> RValLPiP conversion at stage s
  conv-RValLPi : {n : Nat} (G : Ctx n) (Mx A : Expr n) (g : FinFun) (f : FinFun) ->
    SR.RValLPi (max (RANK (FunEl g)) (RANK (LPiCode f))) G Mx A g f ->
    RValLPiP G Mx A g f
  conv-RValLPi {n} G Mx A g f vpi = record
    { domA0 = A0
    ; red   = RValLPi.red vpi
    ; cohG  = RValLPi.cohG vpi
    ; fmG   = RValLPi.fmG vpi
    ; appV  = \ u v sel {A1} an l lel ->
        shiftVl s (suc (max (RANK v) (RANK (EvalFun f u))))
          G (LApp A1 Mx l) (lsub1 A0 l) v (EvalFun f u)
          (le-v-FL g f sel) (le-ef-FL g f u)
          (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
          (RValLPi.appV vpi u v sel an l lel)
    ; appLE = \ u v sel {A1} {A2} an1 an2 l l' e lel ->
        shiftEVl s (suc (max (RANK v) (RANK (EvalFun f u))))
          G (LApp A1 Mx l) (LApp A2 Mx l') (lsub1 A0 l) v (EvalFun f u)
          (le-v-FL g f sel) (le-ef-FL g f u)
          (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
          (RValLPi.appLE vpi u v sel an1 an2 l l' e lel)
    }
    where
      open SR (max (RANK (FunEl g)) (RANK (LPiCode f)))
      s = max (RANK (FunEl g)) (RANK (LPiCode f))
      A0 = RValLPi.domA0 vpi

  -- shared RValLPiP -> RValLPi conversion at stage s
  unconv-RValLPi : {n : Nat} (G : Ctx n) (Mx A : Expr n) (g : FinFun) (f : FinFun) ->
    RValLPiP G Mx A g f ->
    SR.RValLPi (max (RANK (FunEl g)) (RANK (LPiCode f))) G Mx A g f
  unconv-RValLPi {n} G Mx A g f r = record
    { domA0 = A0
    ; red   = RValLPiP.red r
    ; cohG  = RValLPiP.cohG r
    ; fmG   = RValLPiP.fmG r
    ; appV  = \ u v sel {A1} an l lel ->
        shiftVl (suc (max (RANK v) (RANK (EvalFun f u)))) s
          G (LApp A1 Mx l) (lsub1 A0 l) v (EvalFun f u)
          (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
          (le-v-FL g f sel) (le-ef-FL g f u)
          (RValLPiP.appV r u v sel an l lel)
    ; appLE = \ u v sel {A1} {A2} an1 an2 l l' e lel ->
        shiftEVl (suc (max (RANK v) (RANK (EvalFun f u)))) s
          G (LApp A1 Mx l) (LApp A2 Mx l') (lsub1 A0 l) v (EvalFun f u)
          (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
          (le-v-FL g f sel) (le-ef-FL g f u)
          (RValLPiP.appLE r u v sel an1 an2 l l' e lel)
    }
    where
      open SR (max (RANK (FunEl g)) (RANK (LPiCode f)))
      s = max (RANK (FunEl g)) (RANK (LPiCode f))
      A0 = RValLPiP.domA0 r

un-ValLPi : {n : Nat} {G : Ctx n} {M A : Expr n} {g : FinFun} {f : FinFun} ->
  Val2 G M A (FunEl g) (LPiCode f) -> RValLPiP G M A g f
un-ValLPi {n} {G} {M} {A} {g} {f} val = conv-RValLPi G M A g f (snd val)

mk-ValLPi : {n : Nat} {G : Ctx n} {M A : Expr n} {g : FinFun} {f : FinFun} ->
  ValTy2 G A (LPiCode f) -> RValLPiP G M A g f -> Val2 G M A (FunEl g) (LPiCode f)
mk-ValLPi {n} {G} {M} {A} {g} {f} vtA r =
  mkSigma
    (shiftVTy (suc (RANK (LPiCode f))) (suc (max (RANK (FunEl g)) (RANK (LPiCode f))))
      G A (LPiCode f) (Le-refl (suc (RANK (LPiCode f)))) (le-LPi-FL g f) vtA)
    (unconv-RValLPi G M A g f r)

------------------------------------------------------------------------
-- EqValLPi : EqVal2 G M N A (FunEl g) (LPiCode f)
--   reduces to  Pair (ValTy2 G A (LPiCode f))
--                    (Pair (RValLPi s G M A g f)
--                          (Pair (RValLPi s G N A g f)
--                                (REqValLPi s G M N A g f)))
------------------------------------------------------------------------

eqvalLPi-ty : {n : Nat} {G : Ctx n} {M N A : Expr n} {g : FinFun} {f : FinFun} ->
  EqVal2 G M N A (FunEl g) (LPiCode f) -> ValTy2 G A (LPiCode f)
eqvalLPi-ty {n} {G} {M} {N} {A} {g} {f} ev =
  shiftVTy (suc (max (RANK (FunEl g)) (RANK (LPiCode f)))) (suc (RANK (LPiCode f)))
    G A (LPiCode f) (le-LPi-FL g f) (Le-refl (suc (RANK (LPiCode f)))) (fst ev)

eqvalLPi-fst : {n : Nat} {G : Ctx n} {M N A : Expr n} {g : FinFun} {f : FinFun} ->
  EqVal2 G M N A (FunEl g) (LPiCode f) -> RValLPiP G M A g f
eqvalLPi-fst {n} {G} {M} {N} {A} {g} {f} ev = conv-RValLPi G M A g f (fst (snd ev))

eqvalLPi-snd : {n : Nat} {G : Ctx n} {M N A : Expr n} {g : FinFun} {f : FinFun} ->
  EqVal2 G M N A (FunEl g) (LPiCode f) -> RValLPiP G N A g f
eqvalLPi-snd {n} {G} {M} {N} {A} {g} {f} ev = conv-RValLPi G N A g f (fst (snd (snd ev)))

un-REqValLPi : {n : Nat} {G : Ctx n} {M N A : Expr n} {g : FinFun} {f : FinFun} ->
  EqVal2 G M N A (FunEl g) (LPiCode f) -> REqValLPiP G M N A g f
un-REqValLPi {n} {G} {M} {N} {A} {g} {f} ev = record
  { domA0 = A0
  ; red   = REqValLPi.red core
  ; cohG  = REqValLPi.cohG core
  ; fmG   = REqValLPi.fmG core
  ; appEV = \ u v sel {A1} {A2} an1 an2 l lel ->
      shiftEVl s (suc (max (RANK v) (RANK (EvalFun f u))))
        G (LApp A1 M l) (LApp A2 N l) (lsub1 A0 l) v (EvalFun f u)
        (le-v-FL g f sel) (le-ef-FL g f u)
        (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
        (REqValLPi.appEV core u v sel an1 an2 l lel)
  }
  where
    open SR (max (RANK (FunEl g)) (RANK (LPiCode f)))
    s = max (RANK (FunEl g)) (RANK (LPiCode f))
    core = snd (snd (snd ev))
    A0 = REqValLPi.domA0 core

mk-EqValLPi : {n : Nat} {G : Ctx n} {M N A : Expr n} {g : FinFun} {f : FinFun} ->
  ValTy2 G A (LPiCode f) -> RValLPiP G M A g f -> RValLPiP G N A g f ->
  REqValLPiP G M N A g f -> EqVal2 G M N A (FunEl g) (LPiCode f)
mk-EqValLPi {n} {G} {M} {N} {A} {g} {f} vtA rM rN rE =
  mkSigma vtA-up (mkSigma (unconv-RValLPi G M A g f rM) (mkSigma (unconv-RValLPi G N A g f rN) core))
  where
    s = max (RANK (FunEl g)) (RANK (LPiCode f))
    vtA-up : Bundle.valty (Stage (suc s)) G A (LPiCode f)
    vtA-up = shiftVTy (suc (RANK (LPiCode f))) (suc s) G A (LPiCode f)
               (Le-refl (suc (RANK (LPiCode f)))) (le-LPi-FL g f) vtA
    core : SR.REqValLPi s G M N A g f
    core = record
      { domA0 = REqValLPiP.domA0 rE
      ; red   = REqValLPiP.red rE
      ; cohG  = REqValLPiP.cohG rE
      ; fmG   = REqValLPiP.fmG rE
      ; appEV = \ u v sel {A1} {A2} an1 an2 l lel ->
          shiftEVl (suc (max (RANK v) (RANK (EvalFun f u)))) s
            G (LApp A1 M l) (LApp A2 N l) (lsub1 (REqValLPiP.domA0 rE) l) v (EvalFun f u)
            (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
            (le-v-FL g f sel) (le-ef-FL g f u)
            (REqValLPiP.appEV rE u v sel an1 an2 l lel)
      }
