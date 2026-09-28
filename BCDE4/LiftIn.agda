{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.LiftIn
--
-- The statements of the section of erasure (the Lift* records, as in
-- ERT.Equivalence) and the placement of a lift in a chosen Tarski
-- context: a lifted judgement is moved (BCDE4.LiftBack) to any
-- well-formed Tarski context with the right erasure, and a lifted term
-- is retyped at any Tarski type with the right erasure.  Each rule of
-- BCDE4.Equivalence picks one base context and places all its premises
-- there.
------------------------------------------------------------------------

module BCDE4.LiftIn where

open import BCDE4.Basic
open import BCDE4.Levels
import BCDE4.RussellSyntax  as R
import BCDE4.RussellTyping  as RT
import BCDE4.TarskiSyntax   as T
import BCDE4.TarskiTyping   as TT
import BCDE4.Erasure        as E
import BCDE4.TarskiMeta     as TM
open import BCDE4.EraseDeriv using (eraseCtx ; eraseCtx-addC ; eraseCtx-addL)
open import BCDE4.LiftBack

------------------------------------------------------------------------
-- The lifts: a Tarski context, Tarski expressions with the prescribed
-- erasures, and a Tarski derivation
------------------------------------------------------------------------

record LiftWfCtx {n : Nat} (G : RT.Ctx n) : Set where
  constructor mkLiftWfCtx
  field
    G' : TT.Ctx n
    G≡ : Eq (eraseCtx G') G
    wf : TT.WfCtx G'

record LiftIsType {n : Nat} (G : RT.Ctx n) (A : R.Expr n) : Set where
  constructor mkLiftIsType
  field
    G' : TT.Ctx n
    A' : T.Expr n
    G≡ : Eq (eraseCtx G') G
    A≡ : Eq (E.erase A') A
    der : TT.IsType G' A'

record LiftHasType {n : Nat} (G : RT.Ctx n) (M A : R.Expr n) : Set where
  constructor mkLiftHasType
  field
    G' : TT.Ctx n
    M' : T.Expr n
    A' : T.Expr n
    G≡ : Eq (eraseCtx G') G
    M≡ : Eq (E.erase M') M
    A≡ : Eq (E.erase A') A
    der : TT.HasType G' M' A'

record LiftConvTy {n : Nat} (G : RT.Ctx n) (A B : R.Expr n) : Set where
  constructor mkLiftConvTy
  field
    G' : TT.Ctx n
    A' : T.Expr n
    B' : T.Expr n
    G≡ : Eq (eraseCtx G') G
    A≡ : Eq (E.erase A') A
    B≡ : Eq (E.erase B') B
    der : TT.ConvTy G' A' B'

record LiftConvTm {n : Nat} (G : RT.Ctx n) (M N A : R.Expr n) : Set where
  constructor mkLiftConvTm
  field
    G' : TT.Ctx n
    M' : T.Expr n
    N' : T.Expr n
    A' : T.Expr n
    G≡ : Eq (eraseCtx G') G
    M≡ : Eq (E.erase M') M
    N≡ : Eq (E.erase N') N
    A≡ : Eq (E.erase A') A
    der : TT.ConvTm G' M' N' A'

------------------------------------------------------------------------
-- A base context: a well-formed Tarski preimage of G
------------------------------------------------------------------------

record Base {n : Nat} (G : RT.Ctx n) : Set where
  constructor mkBase
  field
    H  : TT.Ctx n
    H≡ : Eq (eraseCtx H) G
    wf : TT.WfCtx H

bW : {n : Nat} {G : RT.Ctx n} -> LiftWfCtx G -> Base G
bW (mkLiftWfCtx H e wf) = mkBase H e wf

bI : {n : Nat} {G : RT.Ctx n} {A : R.Expr n} -> LiftIsType G A -> Base G
bI (mkLiftIsType H _ e _ d) = mkBase H e (TM.isType-WfCtx d)

bH : {n : Nat} {G : RT.Ctx n} {M A : R.Expr n} -> LiftHasType G M A -> Base G
bH (mkLiftHasType H _ _ e _ _ d) = mkBase H e (TM.typing-WfCtx d)

bCm : {n : Nat} {G : RT.Ctx n} {M N A : R.Expr n} -> LiftConvTm G M N A -> Base G
bCm (mkLiftConvTm H _ _ _ e _ _ _ d) = mkBase H e (TM.typing-WfCtx (TM.presup-l-ConvTm d))

-- the base contexts under a constraint / a level binder
eC : {n : Nat} {G : RT.Ctx n} (H : TT.Ctx n) (c : Constr) -> Eq (eraseCtx H) G ->
  Eq (eraseCtx (TT.addC H c)) (RT.addC G c)
eC H c e = Eq-trans (eraseCtx-addC H c) (Eq-cong (\ X -> RT.addC X c) e)

eL : {n : Nat} {G : RT.Ctx n} (H : TT.Ctx n) -> Eq (eraseCtx H) G ->
  Eq (eraseCtx (TT.addL H)) (RT.addL G)
eL H e = Eq-trans (eraseCtx-addL H) (Eq-cong RT.addL e)

------------------------------------------------------------------------
-- Lifts placed in a given Tarski context
------------------------------------------------------------------------

record TyIn {n : Nat} (H : TT.Ctx n) (A : R.Expr n) : Set where
  constructor mkTyIn
  field
    ty  : T.Expr n
    ty≡ : Eq (E.erase ty) A
    dty : TT.IsType H ty

record TmIn {n : Nat} (H : TT.Ctx n) (M : R.Expr n) (B : T.Expr n) : Set where
  constructor mkTmIn
  field
    tm  : T.Expr n
    tm≡ : Eq (E.erase tm) M
    dtm : TT.HasType H tm B

record CTyIn {n : Nat} (H : TT.Ctx n) (A B : R.Expr n) : Set where
  constructor mkCTyIn
  field
    tyL  : T.Expr n
    tyR  : T.Expr n
    tyL≡ : Eq (E.erase tyL) A
    tyR≡ : Eq (E.erase tyR) B
    dcty : TT.ConvTy H tyL tyR

record CTmIn {n : Nat} (H : TT.Ctx n) (M N : R.Expr n) (B : T.Expr n) : Set where
  constructor mkCTmIn
  field
    tmL  : T.Expr n
    tmR  : T.Expr n
    tmL≡ : Eq (E.erase tmL) M
    tmR≡ : Eq (E.erase tmR) N
    dctm : TT.ConvTm H tmL tmR B

tyIn : {n : Nat} {G : RT.Ctx n} {A : R.Expr n} -> LiftIsType G A ->
  {H : TT.Ctx n} -> TT.WfCtx H -> Eq (eraseCtx H) G -> TyIn H A
tyIn (mkLiftIsType G' A' G≡ A≡ d) {H} wf e =
  mkTyIn A' A≡ (move-IsType G' H wf (Eq-trans G≡ (Eq-sym e)) d)

tmIn : {n : Nat} {G : RT.Ctx n} {M A : R.Expr n} -> LiftHasType G M A ->
  {H : TT.Ctx n} -> TT.WfCtx H -> Eq (eraseCtx H) G ->
  {B : T.Expr n} -> TT.IsType H B -> Eq (E.erase B) A -> TmIn H M B
tmIn (mkLiftHasType G' M' A' G≡ M≡ A≡ d) {H} wf e dB eB =
  mkTmIn M' M≡ (coerce-HasType-to (move-HasType G' H wf (Eq-trans G≡ (Eq-sym e)) d) dB (Eq-trans A≡ (Eq-sym eB)))

ctyIn : {n : Nat} {G : RT.Ctx n} {A B : R.Expr n} -> LiftConvTy G A B ->
  {H : TT.Ctx n} -> TT.WfCtx H -> Eq (eraseCtx H) G -> CTyIn H A B
ctyIn (mkLiftConvTy G' A' B' G≡ A≡ B≡ d) {H} wf e =
  mkCTyIn A' B' A≡ B≡ (move-ConvTy G' H wf (Eq-trans G≡ (Eq-sym e)) d)

ctmIn : {n : Nat} {G : RT.Ctx n} {M N A : R.Expr n} -> LiftConvTm G M N A ->
  {H : TT.Ctx n} -> TT.WfCtx H -> Eq (eraseCtx H) G ->
  {B : T.Expr n} -> TT.IsType H B -> Eq (E.erase B) A -> CTmIn H M N B
ctmIn (mkLiftConvTm G' M' N' A' G≡ M≡ N≡ A≡ d) {H} wf e dB eB =
  mkCTmIn M' N' M≡ N≡ (coerce-ConvTm-to (move-ConvTm G' H wf (Eq-trans G≡ (Eq-sym e)) d) dB (Eq-trans A≡ (Eq-sym eB)))

-- at a universe
tmU : {n : Nat} {G : RT.Ctx n} {M : R.Expr n} {l : LExpr} -> LiftHasType G M (R.U l) ->
  {H : TT.Ctx n} -> TT.WfCtx H -> Eq (eraseCtx H) G -> TmIn H M (T.U l)
tmU L wf e = tmIn L wf e (TT.is-U wf) refl

ctmU : {n : Nat} {G : RT.Ctx n} {M N : R.Expr n} {l : LExpr} -> LiftConvTm G M N (R.U l) ->
  {H : TT.Ctx n} -> TT.WfCtx H -> Eq (eraseCtx H) G -> CTmIn H M N (T.U l)
ctmU L wf e = ctmIn L wf e (TT.is-U wf) refl

------------------------------------------------------------------------
-- The domain and codomain of a Π, lifted into a common context
------------------------------------------------------------------------

record PiIn {n : Nat} (G : RT.Ctx n) (A : R.Expr n) (B : R.Expr (suc n)) : Set where
  constructor mkPiIn
  field
    H   : TT.Ctx n
    H≡  : Eq (eraseCtx H) G
    A'  : T.Expr n
    A≡  : Eq (E.erase A') A
    dA  : TT.IsType H A'
    B'  : T.Expr (suc n)
    B≡  : Eq (E.erase B') B
    dB  : TT.IsType (TT.extend H A') B'

piIn : {n : Nat} {G : RT.Ctx n} {A : R.Expr n} {B : R.Expr (suc n)} ->
  LiftIsType G A -> LiftIsType (RT.extend G A) B -> PiIn G A B
piIn (mkLiftIsType H A' e eA dA) LB =
  let mkTyIn B' eB dB = tyIn LB (TT.wf-extend dA) (Eq-cong2 RT.extend e eA)
  in mkPiIn H e A' eA dA B' eB dB

record PiCIn {n : Nat} (G : RT.Ctx n) (A A₁ : R.Expr n) (B B₁ : R.Expr (suc n)) : Set where
  constructor mkPiCIn
  field
    H   : TT.Ctx n
    H≡  : Eq (eraseCtx H) G
    AL  : T.Expr n
    AR  : T.Expr n
    AL≡ : Eq (E.erase AL) A
    AR≡ : Eq (E.erase AR) A₁
    cA  : TT.ConvTy H AL AR
    BL  : T.Expr (suc n)
    BR  : T.Expr (suc n)
    BL≡ : Eq (E.erase BL) B
    BR≡ : Eq (E.erase BR) B₁
    cB  : TT.ConvTy (TT.extend H AL) BL BR

piCIn : {n : Nat} {G : RT.Ctx n} {A A₁ : R.Expr n} {B B₁ : R.Expr (suc n)} ->
  LiftConvTy G A A₁ -> LiftConvTy (RT.extend G A) B B₁ -> PiCIn G A A₁ B B₁
piCIn (mkLiftConvTy H AL AR e eAL eAR cA) LB =
  let mkCTyIn BL BR eBL eBR cB = ctyIn LB (TT.wf-extend (TM.presup-l-ConvTy cA)) (Eq-cong2 RT.extend e eAL)
  in mkPiCIn H e AL AR eAL eAR cA BL BR eBL eBR cB
