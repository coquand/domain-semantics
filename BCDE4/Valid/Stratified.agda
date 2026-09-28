{-# OPTIONS --without-K #-}

------------------------------------------------------------------------
-- BCDE4.Valid.Stratified  (port of MIN/Validity/Stratified.agda to T_R)
--
-- Rank-stratified replacement for the mutual block in
-- ValidityCore.agda.  Instead of defining Val2/EqVal2/ValTy2/EqValTy2
-- by recursion through FinEl codes (which Agda cannot see terminates),
-- we define a `Stage : Nat -> Bundle` family by *structural recursion
-- on the step index n*.  Stage (suc n) builds the level-(suc n)
-- relations from the level-n bundle: the type-level relations recurse
-- into level n on strictly-smaller-RANK codes (domain b, edge value
-- EvalFun f u), so one Stage step strips one rank level.
--
-- The public relations are recovered at the canonical level
--   suc (max (RANK u) (RANK a))   -- enough levels for the codes present.
--
-- No postulates.
------------------------------------------------------------------------

open import BCDE4.Levels using (LDecAll)
module BCDE4.Valid.Stratified (D : LDecAll) where
-- (module parameter: canonical codes of levels, see BCDE4.Levels.LDec)

open import BCDE4.Dom.Basic
  using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ;
         Sigma ; Eq ; refl ; max ; Le ; EqL ;
         FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; List ; nil ; cons ;
         LevTy ; LevEl ; LPiCode)
open import BCDE4.Levels using (LExpr ; Valid ; LDec)
open import BCDE4.RussellSyntax using (Expr ; U ; Pi ; App ; subst1 ; LPi ; LApp ; lsub1)
open import BCDE4.RussellTyping using (Ctx ; extend ; HasType ; ConvTm ; IsType ; ConvTy ; conv-Ty-sym ; conv-Ty-trans ; lctx ; addL)
open import BCDE4.RussellReduction using (HeadRed)
open import BCDE4.RussellMeta using (ctx-conv-ConvTy ; presup-l-ConvTy ; presup-r-ConvTy)
open import BCDE4.Dom.Kernel
  using (EvalFun ; CoherentFun ; CoherentFunTail ; FinMemFun ; FinMemAllU ; LeCode)
open import BCDE4.Model.Selection using (Selection)
open import BCDE4.Dom.Rank using (RANK)

------------------------------------------------------------------------
-- Red3: head reduction of a TYPE, bundled with its type conversion.
-- (In T_R types are converted by ConvTy, which carries no level.)
------------------------------------------------------------------------

record Red3 {n : Nat} (G : Ctx n) (M N : Expr n) : Set where
  constructor mkRed3
  field
    hr : HeadRed M N
    ct : ConvTy G M N

------------------------------------------------------------------------
-- The canonical code of a level in the constraints of a context
------------------------------------------------------------------------

codeL : {n : Nat} -> Ctx n -> LExpr -> Nat
codeL G l = LDec.lcode (D (lctx G)) l

------------------------------------------------------------------------
-- The universe clause: M reduces to a universe U_l whose level has the
-- code k.  Remembering the level gives U-injectivity.
------------------------------------------------------------------------

record RValU {n : Nat} (G : Ctx n) (M : Expr n) (k : Nat) : Set where
  constructor mkRValU
  field
    ulv   : LExpr
    ured  : Red3 G M (U ulv)
    ucode : EqL (codeL G ulv) k
open RValU public

------------------------------------------------------------------------
-- Ann: application annotations (A1, B1) convertible to (A0, B0)
------------------------------------------------------------------------

record Ann {n : Nat} (G : Ctx n) (A0 : Expr n) (B0 : Expr (suc n))
           (A1 : Expr n) (B1 : Expr (suc n)) : Set where
  constructor mkAnn
  field
    annA : ConvTy G A1 A0
    annB : ConvTy (extend G A0) B1 B0

-- Annotations convertible to (A0', B0') are convertible to any (A0, B0)
-- convertible to (A0', B0').
Ann-back : {n : Nat} {G : Ctx n} {A0 A0' A1 : Expr n} {B0 B0' B1 : Expr (suc n)}
  -> Ann G A0' B0' A1 B1 -> ConvTy G A0 A0' -> ConvTy (extend G A0) B0 B0'
  -> Ann G A0 B0 A1 B1
Ann-back (mkAnn aA aB) cA cB =
  mkAnn (conv-Ty-trans aA (conv-Ty-sym cA))
        (conv-Ty-trans (ctx-conv-ConvTy (presup-r-ConvTy cA) (presup-l-ConvTy cA)
                                        (conv-Ty-sym cA) aB)
                       (conv-Ty-sym cB))

-- LAnn: level-application annotations A1 (bound by the level variable)
-- convertible to the record's own A0; the analogue of Ann for LApp.
LAnn : {n : Nat} (G : Ctx n) (A0 A1 : Expr n) -> Set
LAnn G A0 A1 = ConvTy (addL G) A1 A0

LAnn-back : {n : Nat} {G : Ctx n} {A0 A0' A1 : Expr n}
  -> LAnn G A0' A1 -> ConvTy (addL G) A0 A0' -> LAnn G A0 A1
LAnn-back aA cA = conv-Ty-trans aA (conv-Ty-sym cA)

------------------------------------------------------------------------
-- OpenRecords: edge types + records parameterized by abstract relations.
-- (Same as ValidityCore; the relations are supplied by the *previous*
-- Stage level, so there is no cycle.)
------------------------------------------------------------------------

module OpenRecords
  (V2   : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> FinEl -> Set)
  (EV2  : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> FinEl -> FinEl -> Set)
  (VT2  : {n : Nat} -> Ctx n -> Expr n -> FinEl -> Set)
  (EVT2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> Set)
  where

  -- The edge `forall (u v), Selection f u v -> ...` is already rank-bounded:
  -- Selection forces RANK u <= RANKFun f < RANK (PiCode b f) (SelectionRank),
  -- so no explicit level/bound parameter is needed and the relation is
  -- level-independent above the code's rank.

  PiEdgeVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> Set
  PiEdgeVal2 {n} G A B b f =
    (u v : FinEl) -> Selection f u v ->
    (N : Expr n) -> HasType G N A -> V2 G N A u b ->
    VT2 G (subst1 B N) v

  PiEdgeEq2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> Set
  PiEdgeEq2 {n} G A B b f =
    (u v : FinEl) -> Selection f u v ->
    (N1 N2 : Expr n) -> HasType G N1 A -> HasType G N2 A ->
    ConvTm G N1 N2 A -> EV2 G N1 N2 A u b ->
    EVT2 G (subst1 B N1) (subst1 B N2) v

  PiEdgeEqTy2 : {n : Nat} -> Ctx n -> Expr n -> Expr (suc n) -> Expr (suc n) -> FinEl -> FinFun -> Set
  PiEdgeEqTy2 {n} G A B B' b f =
    (u v : FinEl) -> Selection f u v ->
    (P : Expr n) -> HasType G P A -> V2 G P A u b ->
    EVT2 G (subst1 B P) (subst1 B' P) v

  -- The application clauses quantify over annotations convertible to the
  -- record's own (A0, B0): T_R applications carry their annotations, and
  -- this keeps the clauses stable under conversion of the type.
  PiAppVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> FinFun -> Set
  PiAppVal2 {n} G M A0 B0 b f g =
    (u v : FinEl) -> Selection g u v ->
    {A1 : Expr n} {B1 : Expr (suc n)} -> Ann G A0 B0 A1 B1 ->
    (N : Expr n) -> HasType G N A0 -> V2 G N A0 u b ->
    V2 G (App A1 B1 M N) (subst1 B0 N) v (EvalFun f u)

  PiAppEq2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> FinFun -> Set
  PiAppEq2 {n} G M A0 B0 b f g =
    (u v : FinEl) -> Selection g u v ->
    {A1 A2 : Expr n} {B1 B2 : Expr (suc n)} ->
    Ann G A0 B0 A1 B1 -> Ann G A0 B0 A2 B2 ->
    (N1 N2 : Expr n) -> HasType G N1 A0 -> HasType G N2 A0 ->
    ConvTm G N1 N2 A0 -> EV2 G N1 N2 A0 u b ->
    EV2 G (App A1 B1 M N1) (App A2 B2 M N2) (subst1 B0 N1) v (EvalFun f u)

  PiAppEqVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Expr (suc n) -> FinEl -> FinFun -> FinFun -> Set
  PiAppEqVal2 {n} G M N A0 B0 b f g =
    (u v : FinEl) -> Selection g u v ->
    {A1 A2 : Expr n} {B1 B2 : Expr (suc n)} ->
    Ann G A0 B0 A1 B1 -> Ann G A0 B0 A2 B2 ->
    (P : Expr n) -> HasType G P A0 -> V2 G P A0 u b ->
    EV2 G (App A1 B1 M P) (App A2 B2 N P) (subst1 B0 P) v (EvalFun f u)

  record RValTyPi {n : Nat} (G : Ctx n) (M : Expr n) (b : FinEl) (f : FinFun) : Set where
    inductive
    field
      domA   : Expr n
      codB   : Expr (suc n)
      red    : Red3 G M (Pi domA codB)
      cohF   : CoherentFunTail f
      fmAllU : FinMemAllU f b
      htA    : IsType G domA
      htB    : IsType (extend G domA) codB
      valA   : VT2 G domA b
      edgeV  : PiEdgeVal2 G domA codB b f
      edgeE  : PiEdgeEq2 G domA codB b f

  record REqValTyPi {n : Nat} (G : Ctx n) (M N : Expr n) (b : FinEl) (f : FinFun) : Set where
    inductive
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
      eqA    : EVT2 G domA domA' b
      edgeET : PiEdgeEqTy2 G domA codB codB' b f

  record RValPi {n : Nat} (G : Ctx n) (M A : Expr n) (g : FinFun) (b : FinEl) (f : FinFun) : Set where
    inductive
    field
      domA0  : Expr n
      codB0  : Expr (suc n)
      red    : Red3 G A (Pi domA0 codB0)
      cohG   : CoherentFun g
      fmG    : FinMemFun g b f
      appV   : PiAppVal2 G M domA0 codB0 b f g
      appE   : PiAppEq2 G M domA0 codB0 b f g

  record REqValPi {n : Nat} (G : Ctx n) (M N A : Expr n) (g : FinFun) (b : FinEl) (f : FinFun) : Set where
    inductive
    field
      domA0  : Expr n
      codB0  : Expr (suc n)
      red    : Red3 G A (Pi domA0 codB0)
      cohG   : CoherentFun g
      fmG    : FinMemFun g b f
      appEV  : PiAppEqVal2 G M N domA0 codB0 b f g

  ----------------------------------------------------------------------
  -- Level products [α]A, at the code LPiCode f.  The argument of a level
  -- application is a level l of the context; it is admissible for a
  -- selected key u when u ≤ LevEl (code of l).  As for PiAppVal2, the
  -- application clauses quantify over annotations convertible to A0.
  ----------------------------------------------------------------------

  LEdgeVal2 : {n : Nat} -> Ctx n -> Expr n -> FinFun -> Set
  LEdgeVal2 {n} G A f =
    (u v : FinEl) -> Selection f u v ->
    (l : LExpr) -> LeCode u (LevEl (codeL G l)) ->
    VT2 G (lsub1 A l) v

  LEdgeEqTy2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinFun -> Set
  LEdgeEqTy2 {n} G A A' f =
    (u v : FinEl) -> Selection f u v ->
    (l : LExpr) -> LeCode u (LevEl (codeL G l)) ->
    EVT2 G (lsub1 A l) (lsub1 A' l) v

  -- level variation (the analogue of PiEdgeEq2 / PiAppEq2): instances at
  -- levels equal in the constraints of the context are related
  LEdgeLvl2 : {n : Nat} -> Ctx n -> Expr n -> FinFun -> Set
  LEdgeLvl2 {n} G A f =
    (u v : FinEl) -> Selection f u v ->
    (l l' : LExpr) -> Valid (lctx G) l l' -> LeCode u (LevEl (codeL G l)) ->
    EVT2 G (lsub1 A l) (lsub1 A l') v

  LAppLvl2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinFun -> FinFun -> Set
  LAppLvl2 {n} G M A0 f g =
    (u v : FinEl) -> Selection g u v ->
    {A1 A2 : Expr n} -> LAnn G A0 A1 -> LAnn G A0 A2 ->
    (l l' : LExpr) -> Valid (lctx G) l l' -> LeCode u (LevEl (codeL G l)) ->
    EV2 G (LApp A1 M l) (LApp A2 M l') (lsub1 A0 l) v (EvalFun f u)

  LAppVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinFun -> FinFun -> Set
  LAppVal2 {n} G M A0 f g =
    (u v : FinEl) -> Selection g u v ->
    {A1 : Expr n} -> LAnn G A0 A1 ->
    (l : LExpr) -> LeCode u (LevEl (codeL G l)) ->
    V2 G (LApp A1 M l) (lsub1 A0 l) v (EvalFun f u)

  LAppEqVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> FinFun -> FinFun -> Set
  LAppEqVal2 {n} G M N A0 f g =
    (u v : FinEl) -> Selection g u v ->
    {A1 A2 : Expr n} -> LAnn G A0 A1 -> LAnn G A0 A2 ->
    (l : LExpr) -> LeCode u (LevEl (codeL G l)) ->
    EV2 G (LApp A1 M l) (LApp A2 N l) (lsub1 A0 l) v (EvalFun f u)

  record RValTyLPi {n : Nat} (G : Ctx n) (M : Expr n) (f : FinFun) : Set where
    inductive
    field
      domA   : Expr n
      red    : Red3 G M (LPi domA)
      cohF   : CoherentFunTail f
      fmAllU : FinMemAllU f LevTy
      htA    : IsType (addL G) domA
      edgeV  : LEdgeVal2 G domA f
      edgeLE : LEdgeLvl2 G domA f

  record REqValTyLPi {n : Nat} (G : Ctx n) (M N : Expr n) (f : FinFun) : Set where
    inductive
    field
      domA   : Expr n
      domA'  : Expr n
      redM   : Red3 G M (LPi domA)
      redN   : Red3 G N (LPi domA')
      cohF   : CoherentFunTail f
      fmAllU : FinMemAllU f LevTy
      convA  : ConvTy (addL G) domA domA'
      edgeET : LEdgeEqTy2 G domA domA' f

  record RValLPi {n : Nat} (G : Ctx n) (M A : Expr n) (g : FinFun) (f : FinFun) : Set where
    inductive
    field
      domA0  : Expr n
      red    : Red3 G A (LPi domA0)
      cohG   : CoherentFun g
      fmG    : FinMemFun g LevTy f
      appV   : LAppVal2 G M domA0 f g
      appLE  : LAppLvl2 G M domA0 f g

  record REqValLPi {n : Nat} (G : Ctx n) (M N A : Expr n) (g : FinFun) (f : FinFun) : Set where
    inductive
    field
      domA0  : Expr n
      red    : Red3 G A (LPi domA0)
      cohG   : CoherentFun g
      fmG    : FinMemFun g LevTy f
      appEV  : LAppEqVal2 G M N domA0 f g

------------------------------------------------------------------------
-- Bundle of the four relations at one stage level
------------------------------------------------------------------------

record Bundle : Set1 where
  field
    val     : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
    eqval   : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
    valty   : {n : Nat} -> Ctx n -> Expr n -> FinEl -> Set
    eqvalty : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> Set

-- Base: everything trivial. Only ever consulted at codes whose RANK
-- exceeds the available levels (never at the canonical level of a real
-- code), so the trivial value is harmless.
trivBundle : Bundle
trivBundle = record
  { val     = \ _ _ _ _ _   -> Top
  ; eqval   = \ _ _ _ _ _ _ -> Top
  ; valty   = \ _ _ _       -> Top
  ; eqvalty = \ _ _ _ _     -> Top
  }

-- One stage step: build level-(suc n) relations from the level-n bundle B.
buildStage : Bundle -> Bundle
buildStage B = record { val = vl ; eqval = evl ; valty = vty ; eqvalty = evty }
  where
    open Bundle B renaming (val to V ; eqval to EV ; valty to VT ; eqvalty to EVT)
    open OpenRecords V EV VT EVT

    vty : {n : Nat} -> Ctx n -> Expr n -> FinEl -> Set
    vty G M Bot          = Top
    vty G M (UCode k)    = RValU G M k
    vty G M (FunEl g)    = Top
    vty G M (PiCode b f) = RValTyPi G M b f
    vty G M (LPiCode f)  = RValTyLPi G M f
    vty G M LevTy        = Top
    vty G M (LevEl k)    = Top

    evty : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> Set
    evty G M N Bot          = Top
    evty G M N (UCode k)    = Pair (RValU G M k) (RValU G N k)
    evty G M N (FunEl g)    = Top
    evty G M N (PiCode b f) =
      Pair (RValTyPi G M b f)
           (Pair (RValTyPi G N b f) (REqValTyPi G M N b f))
    evty G M N (LPiCode f) =
      Pair (RValTyLPi G M f)
           (Pair (RValTyLPi G N f) (REqValTyLPi G M N f))
    evty G M N LevTy        = Top
    evty G M N (LevEl k)    = Top

    -- NO-LAG form: val/eqval's direct type-components use the SAME-stage
    -- locally-built vty/evty (not the predecessor VT/EVT).  This makes val
    -- and valty strip rank levels identically => uniform canonical level,
    -- so the property package re-indexes by n without cross-level +-1
    -- bookkeeping.  The records (RValPi/REqValPi) still reference the
    -- predecessor via OpenRecords (that is the rank-stripping recursion).
    -- vty/evty never call vl/evl, so the vl -> vty dependency is acyclic
    -- and buildStage stays structural recursion on n.
    vl : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
    vl G M A u Bot                  = Top
    vl G M A (UCode j) (UCode k)      = Pair (vty G A (UCode k)) (vty G M (UCode j))
    vl G M A (PiCode a' f') (UCode k) = Pair (vty G A (UCode k)) (vty G M (PiCode a' f'))
    vl G M A (LPiCode f') (UCode k)   = Pair (vty G A (UCode k)) (vty G M (LPiCode f'))
    vl G M A u (UCode k)              = Top
    vl G M A u (FunEl h)            = Top
    vl G M A (FunEl g) (PiCode b f) = Pair (vty G A (PiCode b f)) (RValPi G M A g b f)
    vl G M A u (PiCode b f)         = Top
    vl G M A (FunEl g) (LPiCode f)  = Pair (vty G A (LPiCode f)) (RValLPi G M A g f)
    vl G M A u (LPiCode f)          = Top
    vl G M A u LevTy                = Top
    vl G M A u (LevEl k)            = Top

    evl : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
    evl G M N A u Bot                  = Top
    evl G M N A (UCode j) (UCode k)      =
      Pair (vty G A (UCode k))
           (Pair (vty G M (UCode j)) (Pair (vty G N (UCode j)) (evty G M N (UCode j))))
    evl G M N A (PiCode a' f') (UCode k) =
      Pair (vty G A (UCode k))
           (Pair (vty G M (PiCode a' f'))
                 (Pair (vty G N (PiCode a' f')) (evty G M N (PiCode a' f'))))
    evl G M N A (LPiCode f') (UCode k) =
      Pair (vty G A (UCode k))
           (Pair (vty G M (LPiCode f'))
                 (Pair (vty G N (LPiCode f')) (evty G M N (LPiCode f'))))
    evl G M N A u (UCode k)              = Top
    evl G M N A u (FunEl h)            = Top
    evl G M N A (FunEl g) (PiCode b f) =
      Pair (vty G A (PiCode b f))
           (Pair (RValPi G M A g b f)
                 (Pair (RValPi G N A g b f) (REqValPi G M N A g b f)))
    evl G M N A u (PiCode b f)         = Top
    evl G M N A (FunEl g) (LPiCode f)  =
      Pair (vty G A (LPiCode f))
           (Pair (RValLPi G M A g f)
                 (Pair (RValLPi G N A g f) (REqValLPi G M N A g f)))
    evl G M N A u (LPiCode f)          = Top
    evl G M N A u LevTy                = Top
    evl G M N A u (LevEl k)            = Top

-- The stratified family, by structural recursion on the step index.
Stage : Nat -> Bundle
Stage zero    = trivBundle
Stage (suc n) = buildStage (Stage n)

------------------------------------------------------------------------
-- Public relations at the canonical level
------------------------------------------------------------------------

-- NO-LAG: val and valty strip levels identically, so the canonical level
-- for val/eqval is suc (max (RANK u) (RANK a)) (matching the vlU/vlD
-- stability bounds), NOT one higher.
Val2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
Val2 G M A u a = Bundle.val (Stage (suc (max (RANK u) (RANK a)))) G M A u a

EqVal2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> FinEl -> FinEl -> Set
EqVal2 G M N A u a = Bundle.eqval (Stage (suc (max (RANK u) (RANK a)))) G M N A u a

ValTy2 : {n : Nat} -> Ctx n -> Expr n -> FinEl -> Set
ValTy2 G M a = Bundle.valty (Stage (suc (RANK a))) G M a

EqValTy2 : {n : Nat} -> Ctx n -> Expr n -> Expr n -> FinEl -> Set
EqValTy2 G M N a = Bundle.eqvalty (Stage (suc (RANK a))) G M N a
