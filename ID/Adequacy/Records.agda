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

module ID.Adequacy.Records where

open import ID.Domain.Basic
  using (Nat ; zero ; suc ; Top ; tt ; Pair ; mkSigma ; fst ; snd ;
         Le ; Le-refl ; Le-trans ; Le-suc ; max ; Le-max-l ; Le-max-r ;
         FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; Eq ; refl ;
         Eq-transport ; Eq-sym)
open import ID.Domain.Basic using (IdCode ; RefEl)
open import ID.Syntax.Raw using (Expr ; Pi ; U ; App ; subst1 ; Id ; Ref ; J)
open import ID.Syntax.Typing using (Ctx ; extend ; HasType ; ConvTm)
open import ID.Domain.Kernel
  using (EvalFun ; CoherentFun ; CoherentFunTail ; FinMemFun ; FinMemAllU ; FinMem)
open import ID.Model.Selection using (Selection)
open import ID.Domain.Rank
  using (RANK ; RANKFun ; RANK-dom ; RANK-cod ; RANK-fun ; RANK-EvalFun)
open import ID.Model.SelectionRank using (Selection-RANK-u ; Selection-RANK-v)
open import ID.Validity.Stratified
open import ID.Validity.Levels using (shiftVTy ; shiftEVTy ; shiftVl ; shiftEVl)

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
  (N : Expr n) -> HasType G N A0 -> Val2 G N A0 u b ->
  Val2 G (App M N) (subst1 B0 N) v (EvalFun f u)

PiAppEq2P : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> FinFun -> Set
PiAppEq2P {n} G M A0 B0 b f g =
  (u v : FinEl) -> Selection g u v ->
  (N1 N2 : Expr n) -> HasType G N1 A0 -> HasType G N2 A0 ->
  ConvTm G N1 N2 A0 -> EqVal2 G N1 N2 A0 u b ->
  EqVal2 G (App M N1) (App M N2) (subst1 B0 N1) v (EvalFun f u)

PiAppEqVal2P : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> FinFun -> Set
PiAppEqVal2P {n} G M N A0 B0 b f g =
  (u v : FinEl) -> Selection g u v ->
  (P : Expr n) -> HasType G P A0 -> Val2 G P A0 u b ->
  EqVal2 G (App M P) (App N P) (subst1 B0 P) v (EvalFun f u)

------------------------------------------------------------------------
-- Public-level records
------------------------------------------------------------------------

record RValTyPiP {n : Nat} (G : Ctx n) (M : Expr n) (b : FinEl) (f : FinFun) : Set where
  constructor mkRValTyPiP
  field
    domA   : Expr n
    codB   : Expr (suc n)
    red    : Red3 G M (Pi domA codB) U
    cohF   : CoherentFunTail f
    fmAllU : FinMemAllU f b
    htA    : HasType G domA U
    htB    : HasType (extend G domA) codB U
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
    redM   : Red3 G M (Pi domA codB) U
    redN   : Red3 G N (Pi domA' codB') U
    cohF   : CoherentFunTail f
    fmAllU : FinMemAllU f b
    convA  : ConvTm G domA domA' U
    convB  : ConvTm (extend G domA) codB codB' U
    eqA    : EqValTy2 G domA domA' b
    edgeET : PiEdgeEqTy2P G domA codB codB' b f

record RValPiP {n : Nat} (G : Ctx n) (M A : Expr n) (g : FinFun) (b : FinEl) (f : FinFun) : Set where
  constructor mkRValPiP
  field
    domA0  : Expr n
    codB0  : Expr (suc n)
    red    : Red3 G A (Pi domA0 codB0) U
    cohG   : CoherentFun g
    fmG    : FinMemFun g b f
    appV   : PiAppVal2P G M domA0 codB0 b f g
    appE   : PiAppEq2P G M domA0 codB0 b f g

record REqValPiP {n : Nat} (G : Ctx n) (M N A : Expr n) (g : FinFun) (b : FinEl) (f : FinFun) : Set where
  constructor mkREqValPiP
  field
    domA0  : Expr n
    codB0  : Expr (suc n)
    red    : Red3 G A (Pi domA0 codB0) U
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
  ; appV  = \ u v sel N htN valN ->
      let valN-s = shiftVl (suc (max (RANK u) (RANK b))) s G N A0 u b
                     (m2l u b) (m2r u b) (le-u-FP g b f sel) (le-b-FP g b f) valN
      in shiftVl s (suc (max (RANK v) (RANK (EvalFun f u))))
           G (App M N) (subst1 B0 N) v (EvalFun f u)
           (le-v-FP g b f sel) (le-ef-FP g b f u)
           (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
           (RValPi.appV vpi u v sel N htN valN-s)
  ; appE  = \ u v sel N1 N2 htN1 htN2 cvN eqN ->
      let eqN-s = shiftEVl (suc (max (RANK u) (RANK b))) s G N1 N2 A0 u b
                    (m2l u b) (m2r u b) (le-u-FP g b f sel) (le-b-FP g b f) eqN
      in shiftEVl s (suc (max (RANK v) (RANK (EvalFun f u))))
           G (App M N1) (App M N2) (subst1 B0 N1) v (EvalFun f u)
           (le-v-FP g b f sel) (le-ef-FP g b f u)
           (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
           (RValPi.appE vpi u v sel N1 N2 htN1 htN2 cvN eqN-s)
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
      ; appV  = \ u v sel N htN valN-s ->
          let valN = shiftVl s (suc (max (RANK u) (RANK b))) G N A0 u b
                       (le-u-FP g b f sel) (le-b-FP g b f) (m2l u b) (m2r u b) valN-s
          in shiftVl (suc (max (RANK v) (RANK (EvalFun f u)))) s
               G (App M N) (subst1 B0 N) v (EvalFun f u)
               (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
               (le-v-FP g b f sel) (le-ef-FP g b f u)
               (RValPiP.appV r u v sel N htN valN)
      ; appE  = \ u v sel N1 N2 htN1 htN2 cvN eqN-s ->
          let eqN = shiftEVl s (suc (max (RANK u) (RANK b))) G N1 N2 A0 u b
                      (le-u-FP g b f sel) (le-b-FP g b f) (m2l u b) (m2r u b) eqN-s
          in shiftEVl (suc (max (RANK v) (RANK (EvalFun f u)))) s
               G (App M N1) (App M N2) (subst1 B0 N1) v (EvalFun f u)
               (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
               (le-v-FP g b f sel) (le-ef-FP g b f u)
               (RValPiP.appE r u v sel N1 N2 htN1 htN2 cvN eqN)
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
    ; appV  = \ u v sel N htN valN ->
        let valN-s = shiftVl (suc (max (RANK u) (RANK b))) s G N A0 u b
                       (m2l u b) (m2r u b) (le-u-FP g b f sel) (le-b-FP g b f) valN
        in shiftVl s (suc (max (RANK v) (RANK (EvalFun f u))))
             G (App Mx N) (subst1 B0 N) v (EvalFun f u)
             (le-v-FP g b f sel) (le-ef-FP g b f u)
             (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
             (RValPi.appV vpi u v sel N htN valN-s)
    ; appE  = \ u v sel N1 N2 htN1 htN2 cvN eqN ->
        let eqN-s = shiftEVl (suc (max (RANK u) (RANK b))) s G N1 N2 A0 u b
                      (m2l u b) (m2r u b) (le-u-FP g b f sel) (le-b-FP g b f) eqN
        in shiftEVl s (suc (max (RANK v) (RANK (EvalFun f u))))
             G (App Mx N1) (App Mx N2) (subst1 B0 N1) v (EvalFun f u)
             (le-v-FP g b f sel) (le-ef-FP g b f u)
             (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
             (RValPi.appE vpi u v sel N1 N2 htN1 htN2 cvN eqN-s)
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
  ; appEV = \ u v sel P htP valP ->
      let valP-s = shiftVl (suc (max (RANK u) (RANK b))) s G P A0 u b
                     (m2l u b) (m2r u b) (le-u-FP g b f sel) (le-b-FP g b f) valP
      in shiftEVl s (suc (max (RANK v) (RANK (EvalFun f u))))
           G (App M P) (App N P) (subst1 B0 P) v (EvalFun f u)
           (le-v-FP g b f sel) (le-ef-FP g b f u)
           (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
           (REqValPi.appEV core u v sel P htP valP-s)
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
      ; appV  = \ u v sel N htN valN-s ->
          let valN = shiftVl s (suc (max (RANK u) (RANK b))) G N (RValPiP.domA0 r) u b
                       (le-u-FP g b f sel) (le-b-FP g b f) (m2l u b) (m2r u b) valN-s
          in shiftVl (suc (max (RANK v) (RANK (EvalFun f u)))) s
               G (App Mx N) (subst1 (RValPiP.codB0 r) N) v (EvalFun f u)
               (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
               (le-v-FP g b f sel) (le-ef-FP g b f u)
               (RValPiP.appV r u v sel N htN valN)
      ; appE  = \ u v sel N1 N2 htN1 htN2 cvN eqN-s ->
          let eqN = shiftEVl s (suc (max (RANK u) (RANK b))) G N1 N2 (RValPiP.domA0 r) u b
                      (le-u-FP g b f sel) (le-b-FP g b f) (m2l u b) (m2r u b) eqN-s
          in shiftEVl (suc (max (RANK v) (RANK (EvalFun f u)))) s
               G (App Mx N1) (App Mx N2) (subst1 (RValPiP.codB0 r) N1) v (EvalFun f u)
               (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
               (le-v-FP g b f sel) (le-ef-FP g b f u)
               (RValPiP.appE r u v sel N1 N2 htN1 htN2 cvN eqN)
      }
    vpiM = mkPi M rM
    vpiN = mkPi N rN
    core : SR.REqValPi s G M N A g b f
    core = record
      { domA0 = REqValPiP.domA0 rE ; codB0 = REqValPiP.codB0 rE
      ; red   = REqValPiP.red rE
      ; cohG  = REqValPiP.cohG rE
      ; fmG   = REqValPiP.fmG rE
      ; appEV = \ u v sel P htP valP-s ->
          let valP = shiftVl s (suc (max (RANK u) (RANK b))) G P (REqValPiP.domA0 rE) u b
                       (le-u-FP g b f sel) (le-b-FP g b f) (m2l u b) (m2r u b) valP-s
          in shiftEVl (suc (max (RANK v) (RANK (EvalFun f u)))) s
               G (App M P) (App N P) (subst1 (REqValPiP.codB0 rE) P) v (EvalFun f u)
               (m2l v (EvalFun f u)) (m2r v (EvalFun f u))
               (le-v-FP g b f sel) (le-ef-FP g b f u)
               (REqValPiP.appEV rE u v sel P htP valP)
      }

------------------------------------------------------------------------
-- Id records (public level).  The Id-type record has NO Selection edges
-- (unlike Pi): just the domain type validity `valA` plus the two endpoints
-- carried at the membership level (`FinMem`, stage-independent).  The proof
-- (Ref) value records RValId/REqValId are stage-independent already (defined
-- top-level in Stratified), so they need no shifting; only the type-part of a
-- Ref value must be bridged between stages.
------------------------------------------------------------------------

private
  -- the type-code component t sits below the Id code stage
  le-t-Id : (t u v : FinEl) -> Le (suc (RANK t)) (RANK (IdCode t u v))
  le-t-Id t u v = Le-max-l (RANK t) (max (RANK u) (RANK v))

  le-u-Id : (t u v : FinEl) -> Le (suc (RANK u)) (RANK (IdCode t u v))
  le-u-Id t u v = Le-trans (RANK u) (max (RANK u) (RANK v)) (max (RANK t) (max (RANK u) (RANK v)))
                    (Le-max-l (RANK u) (RANK v)) (Le-max-r (RANK t) (max (RANK u) (RANK v)))

  le-v-Id : (t u v : FinEl) -> Le (suc (RANK v)) (RANK (IdCode t u v))
  le-v-Id t u v = Le-trans (RANK v) (max (RANK u) (RANK v)) (max (RANK t) (max (RANK u) (RANK v)))
                    (Le-max-r (RANK u) (RANK v)) (Le-max-r (RANK t) (max (RANK u) (RANK v)))

  -- the Id code stage sits below the (RefEl,IdCode) value stage
  le-Id-RI : (w t u v : FinEl) ->
    Le (suc (RANK (IdCode t u v))) (suc (max (RANK (RefEl w)) (RANK (IdCode t u v))))
  le-Id-RI w t u v = Le-max-r (RANK (RefEl w)) (RANK (IdCode t u v))

record RValTyIdP {n : Nat} (G : Ctx n) (M : Expr n) (t u v : FinEl) : Set where
  constructor mkRValTyIdP
  field
    domA : Expr n
    lhs  : Expr n
    rhs  : Expr n
    red  : Red3 G M (Id domA lhs rhs) U
    htA  : HasType G domA U
    htL  : HasType G lhs domA
    htR  : HasType G rhs domA
    valA : ValTy2 G domA t
    valL : FinMem u t
    valR : FinMem v t
    valLlog : Val2 G lhs domA u t
    valRlog : Val2 G rhs domA v t

record REqValTyIdP {n : Nat} (G : Ctx n) (M N : Expr n) (t u v : FinEl) : Set where
  constructor mkREqValTyIdP
  field
    domA  : Expr n
    lhs   : Expr n
    rhs   : Expr n
    domA' : Expr n
    lhs'  : Expr n
    rhs'  : Expr n
    redM  : Red3 G M (Id domA lhs rhs) U
    redN  : Red3 G N (Id domA' lhs' rhs') U
    convA : ConvTm G domA domA' U
    convL : ConvTm G lhs lhs' domA
    convR : ConvTm G rhs rhs' domA
    eqA   : EqValTy2 G domA domA' t
    eqL   : EqVal2 G lhs lhs' domA u t
    eqR   : EqVal2 G rhs rhs' domA v t

------------------------------------------------------------------------
-- ValTyId : ValTy2 G M (IdCode t u v)  <->  RValTyIdP G M t u v
--   record stage  s = RANK (IdCode t u v)
------------------------------------------------------------------------

un-ValTyId : {n : Nat} {G : Ctx n} {M : Expr n} {t u v : FinEl} ->
  ValTy2 G M (IdCode t u v) -> RValTyIdP G M t u v
un-ValTyId {n} {G} {M} {t} {u} {v} vt = record
  { domA = RValTyId.domA vt
  ; lhs  = RValTyId.lhs vt
  ; rhs  = RValTyId.rhs vt
  ; red  = RValTyId.red vt
  ; htA  = RValTyId.htA vt
  ; htL  = RValTyId.htL vt
  ; htR  = RValTyId.htR vt
  ; valA = shiftVTy s (suc (RANK t)) G (RValTyId.domA vt) t (le-t-Id t u v) (Le-refl (suc (RANK t)))
             (RValTyId.valA vt)
  ; valL = RValTyId.valL vt
  ; valR = RValTyId.valR vt
  ; valLlog = shiftVl s (suc (max (RANK u) (RANK t))) G (RValTyId.lhs vt) (RValTyId.domA vt) u t
                (le-u-Id t u v) (le-t-Id t u v) (Le-max-l (RANK u) (RANK t)) (Le-max-r (RANK u) (RANK t)) (RValTyId.valLlog vt)
  ; valRlog = shiftVl s (suc (max (RANK v) (RANK t))) G (RValTyId.rhs vt) (RValTyId.domA vt) v t
                (le-v-Id t u v) (le-t-Id t u v) (Le-max-l (RANK v) (RANK t)) (Le-max-r (RANK v) (RANK t)) (RValTyId.valRlog vt)
  }
  where
    open SR (RANK (IdCode t u v))
    s = RANK (IdCode t u v)

mk-ValTyId : {n : Nat} {G : Ctx n} {M : Expr n} {t u v : FinEl} ->
  RValTyIdP G M t u v -> ValTy2 G M (IdCode t u v)
mk-ValTyId {n} {G} {M} {t} {u} {v} r = record
  { domA = RValTyIdP.domA r
  ; lhs  = RValTyIdP.lhs r
  ; rhs  = RValTyIdP.rhs r
  ; red  = RValTyIdP.red r
  ; htA  = RValTyIdP.htA r
  ; htL  = RValTyIdP.htL r
  ; htR  = RValTyIdP.htR r
  ; valA = shiftVTy (suc (RANK t)) s G (RValTyIdP.domA r) t (Le-refl (suc (RANK t))) (le-t-Id t u v)
             (RValTyIdP.valA r)
  ; valL = RValTyIdP.valL r
  ; valR = RValTyIdP.valR r
  ; valLlog = shiftVl (suc (max (RANK u) (RANK t))) s G (RValTyIdP.lhs r) (RValTyIdP.domA r) u t
                (Le-max-l (RANK u) (RANK t)) (Le-max-r (RANK u) (RANK t)) (le-u-Id t u v) (le-t-Id t u v) (RValTyIdP.valLlog r)
  ; valRlog = shiftVl (suc (max (RANK v) (RANK t))) s G (RValTyIdP.rhs r) (RValTyIdP.domA r) v t
                (Le-max-l (RANK v) (RANK t)) (Le-max-r (RANK v) (RANK t)) (le-v-Id t u v) (le-t-Id t u v) (RValTyIdP.valRlog r)
  }
  where
    open SR (RANK (IdCode t u v))
    s = RANK (IdCode t u v)

------------------------------------------------------------------------
-- EqValTyId : EqValTy2 G M N (IdCode t u v)
--   reduces to  Pair (ValTy2 G M (IdCode..)) (Pair (ValTy2 G N (IdCode..))
--                    (REqValTyId s G M N t u v))
------------------------------------------------------------------------

eqvalTyId-fst : {n : Nat} {G : Ctx n} {M N : Expr n} {t u v : FinEl} ->
  EqValTy2 G M N (IdCode t u v) -> ValTy2 G M (IdCode t u v)
eqvalTyId-fst eqvt = fst eqvt

eqvalTyId-snd : {n : Nat} {G : Ctx n} {M N : Expr n} {t u v : FinEl} ->
  EqValTy2 G M N (IdCode t u v) -> ValTy2 G N (IdCode t u v)
eqvalTyId-snd eqvt = fst (snd eqvt)

un-REqValTyId : {n : Nat} {G : Ctx n} {M N : Expr n} {t u v : FinEl} ->
  EqValTy2 G M N (IdCode t u v) -> REqValTyIdP G M N t u v
un-REqValTyId {n} {G} {M} {N} {t} {u} {v} eqvt = record
  { domA  = REqValTyId.domA core   ; lhs  = REqValTyId.lhs core   ; rhs  = REqValTyId.rhs core
  ; domA' = REqValTyId.domA' core  ; lhs' = REqValTyId.lhs' core  ; rhs' = REqValTyId.rhs' core
  ; redM  = REqValTyId.redM core
  ; redN  = REqValTyId.redN core
  ; convA = REqValTyId.convA core
  ; convL = REqValTyId.convL core
  ; convR = REqValTyId.convR core
  ; eqA   = shiftEVTy s (suc (RANK t)) G (REqValTyId.domA core) (REqValTyId.domA' core) t
              (le-t-Id t u v) (Le-refl (suc (RANK t))) (REqValTyId.eqA core)
  ; eqL   = shiftEVl s (suc (max (RANK u) (RANK t))) G (REqValTyId.lhs core) (REqValTyId.lhs' core) (REqValTyId.domA core) u t
              (le-u-Id t u v) (le-t-Id t u v) (Le-max-l (RANK u) (RANK t)) (Le-max-r (RANK u) (RANK t)) (REqValTyId.eqL core)
  ; eqR   = shiftEVl s (suc (max (RANK v) (RANK t))) G (REqValTyId.rhs core) (REqValTyId.rhs' core) (REqValTyId.domA core) v t
              (le-v-Id t u v) (le-t-Id t u v) (Le-max-l (RANK v) (RANK t)) (Le-max-r (RANK v) (RANK t)) (REqValTyId.eqR core)
  }
  where
    open SR (RANK (IdCode t u v))
    s = RANK (IdCode t u v)
    core = snd (snd eqvt)

mk-EqValTyId : {n : Nat} {G : Ctx n} {M N : Expr n} {t u v : FinEl} ->
  ValTy2 G M (IdCode t u v) -> ValTy2 G N (IdCode t u v) ->
  REqValTyIdP G M N t u v -> EqValTy2 G M N (IdCode t u v)
mk-EqValTyId {n} {G} {M} {N} {t} {u} {v} vtM vtN r =
  mkSigma vtM (mkSigma vtN (record
    { domA  = REqValTyIdP.domA r   ; lhs  = REqValTyIdP.lhs r   ; rhs  = REqValTyIdP.rhs r
    ; domA' = REqValTyIdP.domA' r  ; lhs' = REqValTyIdP.lhs' r  ; rhs' = REqValTyIdP.rhs' r
    ; redM  = REqValTyIdP.redM r
    ; redN  = REqValTyIdP.redN r
    ; convA = REqValTyIdP.convA r
    ; convL = REqValTyIdP.convL r
    ; convR = REqValTyIdP.convR r
    ; eqA   = shiftEVTy (suc (RANK t)) s G (REqValTyIdP.domA r) (REqValTyIdP.domA' r) t
                (Le-refl (suc (RANK t))) (le-t-Id t u v) (REqValTyIdP.eqA r)
    ; eqL   = shiftEVl (suc (max (RANK u) (RANK t))) s G (REqValTyIdP.lhs r) (REqValTyIdP.lhs' r) (REqValTyIdP.domA r) u t
                (Le-max-l (RANK u) (RANK t)) (Le-max-r (RANK u) (RANK t)) (le-u-Id t u v) (le-t-Id t u v) (REqValTyIdP.eqL r)
    ; eqR   = shiftEVl (suc (max (RANK v) (RANK t))) s G (REqValTyIdP.rhs r) (REqValTyIdP.rhs' r) (REqValTyIdP.domA r) v t
                (Le-max-l (RANK v) (RANK t)) (Le-max-r (RANK v) (RANK t)) (le-v-Id t u v) (le-t-Id t u v) (REqValTyIdP.eqR r)
    }))
  where
    open SR (RANK (IdCode t u v))
    s = RANK (IdCode t u v)

------------------------------------------------------------------------
-- ValId / EqValId : the Ref proof VALUE at type IdCode.  RValId/REqValId are
-- now STAGE-DEPENDENT (they carry the semantic endEq, referencing EV2), so the
-- public alias is the OpenRecords record at the (RefEl,IdCode) value stage.
-- Consumers that need endEq at the canonical public level shift it themselves.
------------------------------------------------------------------------

-- Public mirror records for the Ref proof value: endEq at the canonical
-- public EqVal2 level.  The (un)builders shift endEq between that level and the
-- (RefEl,IdCode) value stage `pred = max (RANK (RefEl w)) (RANK (IdCode t u v))`.
record RValIdP {n : Nat} (G : Ctx n) (M A : Expr n) (w t u v : FinEl) : Set where
  constructor mkRValIdP
  field
    domA0 : Expr n
    lhs0  : Expr n
    rhs0  : Expr n
    red   : Red3 G A (Id domA0 lhs0 rhs0) U
    wit0  : Expr n
    redTm : Red3 G M (Ref wit0) A
    refConvL : ConvTm G wit0 lhs0 domA0
    refConvR : ConvTm G wit0 rhs0 domA0
    refMem : FinMem (RefEl w) (IdCode t u v)
    endEqL : EqVal2 G wit0 lhs0 domA0 w t
    endEqR : EqVal2 G wit0 rhs0 domA0 w t

record REqValIdP {n : Nat} (G : Ctx n) (M N A : Expr n) (w t u v : FinEl) : Set where
  constructor mkREqValIdP
  field
    domA0 : Expr n
    lhs0  : Expr n
    rhs0  : Expr n
    red   : Red3 G A (Id domA0 lhs0 rhs0) U
    wit0M : Expr n
    wit0N : Expr n
    redTmM : Red3 G M (Ref wit0M) A
    redTmN : Red3 G N (Ref wit0N) A
    refMem : FinMem (RefEl w) (IdCode t u v)
    endEqLM : EqVal2 G wit0M lhs0 domA0 w t
    endEqRM : EqVal2 G wit0M rhs0 domA0 w t
    endEqLN : EqVal2 G wit0N lhs0 domA0 w t
    endEqRN : EqVal2 G wit0N rhs0 domA0 w t

private
  -- bounds for shifting endEq (value-code w, type-code t) between the value
  -- stage `pred` and the canonical public level suc (max (RANK w) (RANK t)).
  eBw : (w t u v : FinEl) -> Le (suc (RANK w)) (max (RANK (RefEl w)) (RANK (IdCode t u v)))
  eBw w t u v = Le-max-l (RANK (RefEl w)) (RANK (IdCode t u v))
  eBt : (w t u v : FinEl) -> Le (suc (RANK t)) (max (RANK (RefEl w)) (RANK (IdCode t u v)))
  eBt w t u v = Le-trans (suc (RANK t)) (RANK (IdCode t u v)) (max (RANK (RefEl w)) (RANK (IdCode t u v)))
                  (le-t-Id t u v) (Le-max-r (RANK (RefEl w)) (RANK (IdCode t u v)))

un-ValId : {n : Nat} {G : Ctx n} {M A : Expr n} {w t u v : FinEl} ->
  Val2 G M A (RefEl w) (IdCode t u v) -> RValIdP G M A w t u v
un-ValId {n} {G} {M} {A} {w} {t} {u} {v} val = record
  { domA0 = R.domA0 rid ; lhs0 = R.lhs0 rid ; rhs0 = R.rhs0 rid ; red = R.red rid
  ; wit0 = R.wit0 rid ; redTm = R.redTm rid ; refConvL = R.refConvL rid ; refConvR = R.refConvR rid
  ; refMem = R.refMem rid
  ; endEqL = shiftEVl s (suc (max (RANK w) (RANK t))) G (R.wit0 rid) (R.lhs0 rid) (R.domA0 rid) w t
               (eBw w t u v) (eBt w t u v) (Le-max-l (RANK w) (RANK t)) (Le-max-r (RANK w) (RANK t)) (R.endEqL rid)
  ; endEqR = shiftEVl s (suc (max (RANK w) (RANK t))) G (R.wit0 rid) (R.rhs0 rid) (R.domA0 rid) w t
               (eBw w t u v) (eBt w t u v) (Le-max-l (RANK w) (RANK t)) (Le-max-r (RANK w) (RANK t)) (R.endEqR rid) }
  where
    s = max (RANK (RefEl w)) (RANK (IdCode t u v))
    module R = SR.RValId s
    rid = snd val

valId-ty : {n : Nat} {G : Ctx n} {M A : Expr n} {w t u v : FinEl} ->
  Val2 G M A (RefEl w) (IdCode t u v) -> ValTy2 G A (IdCode t u v)
valId-ty {n} {G} {M} {A} {w} {t} {u} {v} val =
  shiftVTy (suc (max (RANK (RefEl w)) (RANK (IdCode t u v)))) (suc (RANK (IdCode t u v)))
    G A (IdCode t u v) (le-Id-RI w t u v) (Le-refl (suc (RANK (IdCode t u v)))) (fst val)

mk-ValId : {n : Nat} {G : Ctx n} {M A : Expr n} {w t u v : FinEl} ->
  ValTy2 G A (IdCode t u v) -> RValIdP G M A w t u v ->
  Val2 G M A (RefEl w) (IdCode t u v)
mk-ValId {n} {G} {M} {A} {w} {t} {u} {v} vtA r =
  mkSigma (shiftVTy (suc (RANK (IdCode t u v))) (suc (max (RANK (RefEl w)) (RANK (IdCode t u v))))
             G A (IdCode t u v) (Le-refl (suc (RANK (IdCode t u v)))) (le-Id-RI w t u v) vtA)
    (record
      { domA0 = RValIdP.domA0 r ; lhs0 = RValIdP.lhs0 r ; rhs0 = RValIdP.rhs0 r ; red = RValIdP.red r
      ; wit0 = RValIdP.wit0 r ; redTm = RValIdP.redTm r ; refConvL = RValIdP.refConvL r ; refConvR = RValIdP.refConvR r
      ; refMem = RValIdP.refMem r
      ; endEqL = shiftEVl (suc (max (RANK w) (RANK t))) s G (RValIdP.wit0 r) (RValIdP.lhs0 r) (RValIdP.domA0 r) w t
                   (Le-max-l (RANK w) (RANK t)) (Le-max-r (RANK w) (RANK t)) (eBw w t u v) (eBt w t u v) (RValIdP.endEqL r)
      ; endEqR = shiftEVl (suc (max (RANK w) (RANK t))) s G (RValIdP.wit0 r) (RValIdP.rhs0 r) (RValIdP.domA0 r) w t
                   (Le-max-l (RANK w) (RANK t)) (Le-max-r (RANK w) (RANK t)) (eBw w t u v) (eBt w t u v) (RValIdP.endEqR r) })
  where
    s = max (RANK (RefEl w)) (RANK (IdCode t u v))

un-EqValId : {n : Nat} {G : Ctx n} {M N A : Expr n} {w t u v : FinEl} ->
  EqVal2 G M N A (RefEl w) (IdCode t u v) -> REqValIdP G M N A w t u v
un-EqValId {n} {G} {M} {N} {A} {w} {t} {u} {v} ev = record
  { domA0 = R.domA0 reid ; lhs0 = R.lhs0 reid ; rhs0 = R.rhs0 reid ; red = R.red reid
  ; wit0M = R.wit0M reid ; wit0N = R.wit0N reid ; redTmM = R.redTmM reid ; redTmN = R.redTmN reid
  ; refMem = R.refMem reid
  ; endEqLM = sh (R.wit0M reid) (R.lhs0 reid) (R.domA0 reid) (R.endEqLM reid)
  ; endEqRM = sh (R.wit0M reid) (R.rhs0 reid) (R.domA0 reid) (R.endEqRM reid)
  ; endEqLN = sh (R.wit0N reid) (R.lhs0 reid) (R.domA0 reid) (R.endEqLN reid)
  ; endEqRN = sh (R.wit0N reid) (R.rhs0 reid) (R.domA0 reid) (R.endEqRN reid) }
  where
    s = max (RANK (RefEl w)) (RANK (IdCode t u v))
    module R = SR.REqValId s
    reid = snd (snd (snd ev))
    sh : (X Y Z : Expr n) -> Bundle.eqval (Stage s) G X Y Z w t -> EqVal2 G X Y Z w t
    sh X Y Z e = shiftEVl s (suc (max (RANK w) (RANK t))) G X Y Z w t
                   (eBw w t u v) (eBt w t u v) (Le-max-l (RANK w) (RANK t)) (Le-max-r (RANK w) (RANK t)) e

mk-EqValId : {n : Nat} {G : Ctx n} {M N A : Expr n} {w t u v : FinEl} ->
  ValTy2 G A (IdCode t u v) ->
  RValIdP G M A w t u v -> RValIdP G N A w t u v -> REqValIdP G M N A w t u v ->
  EqVal2 G M N A (RefEl w) (IdCode t u v)
mk-EqValId {n} {G} {M} {N} {A} {w} {t} {u} {v} vtA rM rN rE =
  mkSigma (shiftVTy (suc (RANK (IdCode t u v))) (suc (max (RANK (RefEl w)) (RANK (IdCode t u v))))
             G A (IdCode t u v) (Le-refl (suc (RANK (IdCode t u v)))) (le-Id-RI w t u v) vtA)
    (mkSigma (idP->id rM) (mkSigma (idP->id rN) (eqP->eq rE)))
  where
    s = max (RANK (RefEl w)) (RANK (IdCode t u v))
    shD : (X Y Z : Expr n) -> EqVal2 G X Y Z w t -> Bundle.eqval (Stage s) G X Y Z w t
    shD X Y Z e = shiftEVl (suc (max (RANK w) (RANK t))) s G X Y Z w t
                    (Le-max-l (RANK w) (RANK t)) (Le-max-r (RANK w) (RANK t)) (eBw w t u v) (eBt w t u v) e
    idP->id : {M0 : Expr n} -> RValIdP G M0 A w t u v -> SR.RValId s G M0 A w t u v
    idP->id r = record
      { domA0 = RValIdP.domA0 r ; lhs0 = RValIdP.lhs0 r ; rhs0 = RValIdP.rhs0 r ; red = RValIdP.red r
      ; wit0 = RValIdP.wit0 r ; redTm = RValIdP.redTm r ; refConvL = RValIdP.refConvL r ; refConvR = RValIdP.refConvR r
      ; refMem = RValIdP.refMem r
      ; endEqL = shD (RValIdP.wit0 r) (RValIdP.lhs0 r) (RValIdP.domA0 r) (RValIdP.endEqL r)
      ; endEqR = shD (RValIdP.wit0 r) (RValIdP.rhs0 r) (RValIdP.domA0 r) (RValIdP.endEqR r) }
    eqP->eq : REqValIdP G M N A w t u v -> SR.REqValId s G M N A w t u v
    eqP->eq r = record
      { domA0 = REqValIdP.domA0 r ; lhs0 = REqValIdP.lhs0 r ; rhs0 = REqValIdP.rhs0 r ; red = REqValIdP.red r
      ; wit0M = REqValIdP.wit0M r ; wit0N = REqValIdP.wit0N r ; redTmM = REqValIdP.redTmM r ; redTmN = REqValIdP.redTmN r
      ; refMem = REqValIdP.refMem r
      ; endEqLM = shD (REqValIdP.wit0M r) (REqValIdP.lhs0 r) (REqValIdP.domA0 r) (REqValIdP.endEqLM r)
      ; endEqRM = shD (REqValIdP.wit0M r) (REqValIdP.rhs0 r) (REqValIdP.domA0 r) (REqValIdP.endEqRM r)
      ; endEqLN = shD (REqValIdP.wit0N r) (REqValIdP.lhs0 r) (REqValIdP.domA0 r) (REqValIdP.endEqLN r)
      ; endEqRN = shD (REqValIdP.wit0N r) (REqValIdP.rhs0 r) (REqValIdP.domA0 r) (REqValIdP.endEqRN r) }
