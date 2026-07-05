{-# OPTIONS --without-K #-}

------------------------------------------------------------------------
-- ValidityStability.agda  (MIN/ — Pi + U fragment)
--
-- Stage-level stability: the relations are level-independent above the
-- code's rank.  Proved as 8 transports (vty/evty/vl/evl, up & down) plus
-- the RValPi/REqValPi component transports (rvpU/rvpD/reqvpU/reqvpD),
-- mutually by structural recursion on the stage index j.
--
-- The edge realizers are rank-bounded by Selection (SelectionRank), so the
-- PiCode transports recurse only into strictly-smaller-rank codes / lower
-- stage indices.  With the NO-LAG buildStage (val and valty strip levels
-- at the SAME index), val-stability reduces to valty-stability at the same
-- index, so the rank bounds match with no +-1 offset and NO monotonicity is
-- needed.  Structural on j; no postulates.
--
-- STATUS: COMPLETE — 0 holes, 0 postulates (2026-05-20).
------------------------------------------------------------------------

module ID.Validity.Stability where

open import ID.Domain.Basic
  using (Nat ; zero ; suc ; Top ; tt ; Empty ; Pair ; mkSigma ; fst ; snd ;
         Le ; Le-trans ; Le-max-l ; Le-max-r ; max ;
         FinEl ; Bot ; UCode ; FunEl ; PiCode ; IdCode ; RefEl ; FinFun)
open import ID.Syntax.Raw using (Expr ; U ; Pi ; App ; subst1)
open import ID.Syntax.Typing using (Ctx ; extend ; HasType ; ConvTm)
open import ID.Model.Selection using (Selection)
open import ID.Domain.Kernel using (EvalFun)
open import ID.Domain.Rank using (RANK ; RANKFun ; RANK-cod ; RANK-EvalFun)
open import ID.Model.SelectionRank using (Selection-RANK-u ; Selection-RANK-v)
open import ID.Validity.Stratified

-- OpenRecords instantiated at Stage j's relations (records used by
-- Stage (suc j) at PiCode).
module R (j : Nat) = OpenRecords (Bundle.val (Stage j)) (Bundle.eqval (Stage j))
                                 (Bundle.valty (Stage j)) (Bundle.eqvalty (Stage j))

------------------------------------------------------------------------
-- The 8 stability transports, comparing Stage j and Stage (suc j).
------------------------------------------------------------------------

mutual
  vtyU : (j : Nat) {n : Nat} (G : Ctx n) (M : Expr n) (a : FinEl) ->
    Le (suc (RANK a)) j ->
    Bundle.valty (Stage j) G M a -> Bundle.valty (Stage (suc j)) G M a
  vtyD : (j : Nat) {n : Nat} (G : Ctx n) (M : Expr n) (a : FinEl) ->
    Le (suc (RANK a)) j ->
    Bundle.valty (Stage (suc j)) G M a -> Bundle.valty (Stage j) G M a

  evtyU : (j : Nat) {n : Nat} (G : Ctx n) (M N : Expr n) (a : FinEl) ->
    Le (suc (RANK a)) j ->
    Bundle.eqvalty (Stage j) G M N a -> Bundle.eqvalty (Stage (suc j)) G M N a
  evtyD : (j : Nat) {n : Nat} (G : Ctx n) (M N : Expr n) (a : FinEl) ->
    Le (suc (RANK a)) j ->
    Bundle.eqvalty (Stage (suc j)) G M N a -> Bundle.eqvalty (Stage j) G M N a

  vlU : (j : Nat) {n : Nat} (G : Ctx n) (M A : Expr n) (u a : FinEl) ->
    Le (suc (RANK u)) j -> Le (suc (RANK a)) j ->
    Bundle.val (Stage j) G M A u a -> Bundle.val (Stage (suc j)) G M A u a
  vlD : (j : Nat) {n : Nat} (G : Ctx n) (M A : Expr n) (u a : FinEl) ->
    Le (suc (RANK u)) j -> Le (suc (RANK a)) j ->
    Bundle.val (Stage (suc j)) G M A u a -> Bundle.val (Stage j) G M A u a

  evlU : (j : Nat) {n : Nat} (G : Ctx n) (M N A : Expr n) (u a : FinEl) ->
    Le (suc (RANK u)) j -> Le (suc (RANK a)) j ->
    Bundle.eqval (Stage j) G M N A u a -> Bundle.eqval (Stage (suc j)) G M N A u a
  evlD : (j : Nat) {n : Nat} (G : Ctx n) (M N A : Expr n) (u a : FinEl) ->
    Le (suc (RANK u)) j -> Le (suc (RANK a)) j ->
    Bundle.eqval (Stage (suc j)) G M N A u a -> Bundle.eqval (Stage j) G M N A u a

  -- RValPi / REqValPi transports (the FunEl/PiCode val components); the
  -- edge realizers are Selection g-bounded (rank < j), so they recurse into
  -- vlU/vlD/evlU/evlD at the SAME index j.
  rvpU : (j : Nat) {n : Nat} (G : Ctx n) (M A : Expr n) (g : FinFun) (b : FinEl) (f : FinFun) ->
    Le (suc (RANK (FunEl g))) (suc j) -> Le (suc (RANK (PiCode b f))) (suc j) ->
    R.RValPi j G M A g b f -> R.RValPi (suc j) G M A g b f
  rvpD : (j : Nat) {n : Nat} (G : Ctx n) (M A : Expr n) (g : FinFun) (b : FinEl) (f : FinFun) ->
    Le (suc (RANK (FunEl g))) (suc j) -> Le (suc (RANK (PiCode b f))) (suc j) ->
    R.RValPi (suc j) G M A g b f -> R.RValPi j G M A g b f
  reqvpU : (j : Nat) {n : Nat} (G : Ctx n) (M N A : Expr n) (g : FinFun) (b : FinEl) (f : FinFun) ->
    Le (suc (RANK (FunEl g))) (suc j) -> Le (suc (RANK (PiCode b f))) (suc j) ->
    R.REqValPi j G M N A g b f -> R.REqValPi (suc j) G M N A g b f
  reqvpD : (j : Nat) {n : Nat} (G : Ctx n) (M N A : Expr n) (g : FinFun) (b : FinEl) (f : FinFun) ->
    Le (suc (RANK (FunEl g))) (suc j) -> Le (suc (RANK (PiCode b f))) (suc j) ->
    R.REqValPi (suc j) G M N A g b f -> R.REqValPi j G M N A g b f

  -- RValId / REqValId cross-stage transports (the endEq semantic-equality
  -- fields recurse into evlU/evlD at the witness code w / dom code t).
  rvidU : (j : Nat) {n : Nat} (G : Ctx n) (M A : Expr n) (w t u v : FinEl) ->
    Le (suc (RANK (RefEl w))) (suc j) -> Le (suc (RANK (IdCode t u v))) (suc j) ->
    R.RValId j G M A w t u v -> R.RValId (suc j) G M A w t u v
  rvidD : (j : Nat) {n : Nat} (G : Ctx n) (M A : Expr n) (w t u v : FinEl) ->
    Le (suc (RANK (RefEl w))) (suc j) -> Le (suc (RANK (IdCode t u v))) (suc j) ->
    R.RValId (suc j) G M A w t u v -> R.RValId j G M A w t u v
  reqvidU : (j : Nat) {n : Nat} (G : Ctx n) (M N A : Expr n) (w t u v : FinEl) ->
    Le (suc (RANK (RefEl w))) (suc j) -> Le (suc (RANK (IdCode t u v))) (suc j) ->
    R.REqValId j G M N A w t u v -> R.REqValId (suc j) G M N A w t u v
  reqvidD : (j : Nat) {n : Nat} (G : Ctx n) (M N A : Expr n) (w t u v : FinEl) ->
    Le (suc (RANK (RefEl w))) (suc j) -> Le (suc (RANK (IdCode t u v))) (suc j) ->
    R.REqValId (suc j) G M N A w t u v -> R.REqValId j G M N A w t u v

  ------------------------------------------------------------------
  -- vtyU
  ------------------------------------------------------------------
  vtyU (suc j) G M Bot       bnd vt = vt
  vtyU (suc j) G M UCode     bnd vt = vt
  vtyU (suc j) G M (FunEl g) bnd vt = vt
  vtyU (suc j) G M (PiCode b f) bnd vt = record
    { domA   = RValTyPi.domA vt
    ; codB   = RValTyPi.codB vt
    ; red    = RValTyPi.red vt
    ; cohF   = RValTyPi.cohF vt
    ; fmAllU = RValTyPi.fmAllU vt
    ; htA    = RValTyPi.htA vt
    ; htB    = RValTyPi.htB vt
    ; valA   = vtyU j G (RValTyPi.domA vt) b lb (RValTyPi.valA vt)
    ; edgeV  = \ u v sel N htN hv ->
                 vtyU j G (subst1 (RValTyPi.codB vt) N) v (lv u v sel)
                   (RValTyPi.edgeV vt u v sel N htN
                     (vlD j G N (RValTyPi.domA vt) u b (lu u v sel) lb hv))
    ; edgeE  = \ u v sel N1 N2 ht1 ht2 cv hev ->
                 evtyU j G (subst1 (RValTyPi.codB vt) N1) (subst1 (RValTyPi.codB vt) N2) v (lv u v sel)
                   (RValTyPi.edgeE vt u v sel N1 N2 ht1 ht2 cv
                     (evlD j G N1 N2 (RValTyPi.domA vt) u b (lu u v sel) lb hev))
    }
    where
      open R j
      lb : Le (suc (RANK b)) j
      lb = Le-trans (suc (RANK b)) (suc (max (RANK b) (RANKFun f))) j
             (Le-max-l (RANK b) (RANKFun f)) bnd
      lcod : Le (suc (RANKFun f)) j
      lcod = Le-trans (suc (RANKFun f)) (suc (max (RANK b) (RANKFun f))) j
               (Le-max-r (RANK b) (RANKFun f)) bnd
      lu : (u v : FinEl) -> Selection f u v -> Le (suc (RANK u)) j
      lu u v sel = Le-trans (suc (RANK u)) (suc (RANKFun f)) j (Selection-RANK-u sel) lcod
      lv : (u v : FinEl) -> Selection f u v -> Le (suc (RANK v)) j
      lv u v sel = Le-trans (suc (RANK v)) (suc (RANKFun f)) j (Selection-RANK-v sel) lcod
  vtyU (suc j) G M (IdCode t u v) bnd vt = record
    { domA = RValTyId.domA vt ; lhs = RValTyId.lhs vt ; rhs = RValTyId.rhs vt
    ; red = RValTyId.red vt
    ; htA = RValTyId.htA vt ; htL = RValTyId.htL vt ; htR = RValTyId.htR vt
    ; valA = vtyU j G (RValTyId.domA vt) t lt (RValTyId.valA vt)
    ; valL = RValTyId.valL vt ; valR = RValTyId.valR vt
    ; valLlog = vlU j G (RValTyId.lhs vt) (RValTyId.domA vt) u t lu lt (RValTyId.valLlog vt)
    ; valRlog = vlU j G (RValTyId.rhs vt) (RValTyId.domA vt) v t lv lt (RValTyId.valRlog vt)
    }
    where
      open R j
      lt : Le (suc (RANK t)) j
      lt = Le-trans (suc (RANK t)) (suc (max (RANK t) (max (RANK u) (RANK v)))) j
             (Le-max-l (RANK t) (max (RANK u) (RANK v))) bnd
      lu : Le (suc (RANK u)) j
      lu = Le-trans (suc (RANK u)) (suc (max (RANK t) (max (RANK u) (RANK v)))) j
             (Le-trans (RANK u) (max (RANK u) (RANK v)) (max (RANK t) (max (RANK u) (RANK v)))
                (Le-max-l (RANK u) (RANK v)) (Le-max-r (RANK t) (max (RANK u) (RANK v)))) bnd
      lv : Le (suc (RANK v)) j
      lv = Le-trans (suc (RANK v)) (suc (max (RANK t) (max (RANK u) (RANK v)))) j
             (Le-trans (RANK v) (max (RANK u) (RANK v)) (max (RANK t) (max (RANK u) (RANK v)))
                (Le-max-r (RANK u) (RANK v)) (Le-max-r (RANK t) (max (RANK u) (RANK v)))) bnd
  vtyU (suc j) G M (RefEl w) bnd vt = vt

  ------------------------------------------------------------------
  -- vtyD
  ------------------------------------------------------------------
  vtyD (suc j) G M Bot       bnd vt = vt
  vtyD (suc j) G M UCode     bnd vt = vt
  vtyD (suc j) G M (FunEl g) bnd vt = vt
  vtyD (suc j) G M (PiCode b f) bnd vt = record
    { domA   = RValTyPi.domA vt
    ; codB   = RValTyPi.codB vt
    ; red    = RValTyPi.red vt
    ; cohF   = RValTyPi.cohF vt
    ; fmAllU = RValTyPi.fmAllU vt
    ; htA    = RValTyPi.htA vt
    ; htB    = RValTyPi.htB vt
    ; valA   = vtyD j G (RValTyPi.domA vt) b lb (RValTyPi.valA vt)
    ; edgeV  = \ u v sel N htN hv ->
                 vtyD j G (subst1 (RValTyPi.codB vt) N) v (lv u v sel)
                   (RValTyPi.edgeV vt u v sel N htN
                     (vlU j G N (RValTyPi.domA vt) u b (lu u v sel) lb hv))
    ; edgeE  = \ u v sel N1 N2 ht1 ht2 cv hev ->
                 evtyD j G (subst1 (RValTyPi.codB vt) N1) (subst1 (RValTyPi.codB vt) N2) v (lv u v sel)
                   (RValTyPi.edgeE vt u v sel N1 N2 ht1 ht2 cv
                     (evlU j G N1 N2 (RValTyPi.domA vt) u b (lu u v sel) lb hev))
    }
    where
      open R (suc j)
      lb : Le (suc (RANK b)) j
      lb = Le-trans (suc (RANK b)) (suc (max (RANK b) (RANKFun f))) j
             (Le-max-l (RANK b) (RANKFun f)) bnd
      lcod : Le (suc (RANKFun f)) j
      lcod = Le-trans (suc (RANKFun f)) (suc (max (RANK b) (RANKFun f))) j
               (Le-max-r (RANK b) (RANKFun f)) bnd
      lu : (u v : FinEl) -> Selection f u v -> Le (suc (RANK u)) j
      lu u v sel = Le-trans (suc (RANK u)) (suc (RANKFun f)) j (Selection-RANK-u sel) lcod
      lv : (u v : FinEl) -> Selection f u v -> Le (suc (RANK v)) j
      lv u v sel = Le-trans (suc (RANK v)) (suc (RANKFun f)) j (Selection-RANK-v sel) lcod
  vtyD (suc j) G M (IdCode t u v) bnd vt = record
    { domA = RValTyId.domA vt ; lhs = RValTyId.lhs vt ; rhs = RValTyId.rhs vt
    ; red = RValTyId.red vt
    ; htA = RValTyId.htA vt ; htL = RValTyId.htL vt ; htR = RValTyId.htR vt
    ; valA = vtyD j G (RValTyId.domA vt) t lt (RValTyId.valA vt)
    ; valL = RValTyId.valL vt ; valR = RValTyId.valR vt
    ; valLlog = vlD j G (RValTyId.lhs vt) (RValTyId.domA vt) u t lu lt (RValTyId.valLlog vt)
    ; valRlog = vlD j G (RValTyId.rhs vt) (RValTyId.domA vt) v t lv lt (RValTyId.valRlog vt)
    }
    where
      open R (suc j)
      lt : Le (suc (RANK t)) j
      lt = Le-trans (suc (RANK t)) (suc (max (RANK t) (max (RANK u) (RANK v)))) j
             (Le-max-l (RANK t) (max (RANK u) (RANK v))) bnd
      lu : Le (suc (RANK u)) j
      lu = Le-trans (suc (RANK u)) (suc (max (RANK t) (max (RANK u) (RANK v)))) j
             (Le-trans (RANK u) (max (RANK u) (RANK v)) (max (RANK t) (max (RANK u) (RANK v)))
                (Le-max-l (RANK u) (RANK v)) (Le-max-r (RANK t) (max (RANK u) (RANK v)))) bnd
      lv : Le (suc (RANK v)) j
      lv = Le-trans (suc (RANK v)) (suc (max (RANK t) (max (RANK u) (RANK v)))) j
             (Le-trans (RANK v) (max (RANK u) (RANK v)) (max (RANK t) (max (RANK u) (RANK v)))
                (Le-max-r (RANK u) (RANK v)) (Le-max-r (RANK t) (max (RANK u) (RANK v)))) bnd
  vtyD (suc j) G M (RefEl w) bnd vt = vt

  ------------------------------------------------------------------
  -- evtyU
  ------------------------------------------------------------------
  evtyU (suc j) G M N Bot       bnd vt = vt
  evtyU (suc j) G M N UCode     bnd vt = vt
  evtyU (suc j) G M N (FunEl g) bnd vt = vt
  evtyU (suc j) G M N (PiCode b f) bnd vt =
    mkSigma (vtyU (suc j) G M (PiCode b f) bnd (fst vt))
      (mkSigma (vtyU (suc j) G N (PiCode b f) bnd (fst (snd vt)))
        (record
          { domA   = REqValTyPi.domA c
          ; codB   = REqValTyPi.codB c
          ; domA'  = REqValTyPi.domA' c
          ; codB'  = REqValTyPi.codB' c
          ; redM   = REqValTyPi.redM c
          ; redN   = REqValTyPi.redN c
          ; cohF   = REqValTyPi.cohF c
          ; fmAllU = REqValTyPi.fmAllU c
          ; convA  = REqValTyPi.convA c
          ; convB  = REqValTyPi.convB c
          ; eqA    = evtyU j G (REqValTyPi.domA c) (REqValTyPi.domA' c) b lb (REqValTyPi.eqA c)
          ; edgeET = \ u v sel P htP hv ->
                       evtyU j G (subst1 (REqValTyPi.codB c) P) (subst1 (REqValTyPi.codB' c) P) v (lv u v sel)
                         (REqValTyPi.edgeET c u v sel P htP
                           (vlD j G P (REqValTyPi.domA c) u b (lu u v sel) lb hv))
          }))
    where
      open R j
      c = snd (snd vt)
      lb : Le (suc (RANK b)) j
      lb = Le-trans (suc (RANK b)) (suc (max (RANK b) (RANKFun f))) j
             (Le-max-l (RANK b) (RANKFun f)) bnd
      lcod : Le (suc (RANKFun f)) j
      lcod = Le-trans (suc (RANKFun f)) (suc (max (RANK b) (RANKFun f))) j
               (Le-max-r (RANK b) (RANKFun f)) bnd
      lu : (u v : FinEl) -> Selection f u v -> Le (suc (RANK u)) j
      lu u v sel = Le-trans (suc (RANK u)) (suc (RANKFun f)) j (Selection-RANK-u sel) lcod
      lv : (u v : FinEl) -> Selection f u v -> Le (suc (RANK v)) j
      lv u v sel = Le-trans (suc (RANK v)) (suc (RANKFun f)) j (Selection-RANK-v sel) lcod
  evtyU (suc j) G M N (IdCode t u v) bnd vt =
    mkSigma (vtyU (suc j) G M (IdCode t u v) bnd (fst vt))
      (mkSigma (vtyU (suc j) G N (IdCode t u v) bnd (fst (snd vt)))
        (record
          { domA = REqValTyId.domA c ; lhs = REqValTyId.lhs c ; rhs = REqValTyId.rhs c
          ; domA' = REqValTyId.domA' c ; lhs' = REqValTyId.lhs' c ; rhs' = REqValTyId.rhs' c
          ; redM = REqValTyId.redM c ; redN = REqValTyId.redN c
          ; convA = REqValTyId.convA c ; convL = REqValTyId.convL c ; convR = REqValTyId.convR c
          ; eqA = evtyU j G (REqValTyId.domA c) (REqValTyId.domA' c) t lt (REqValTyId.eqA c)
          ; eqL = evlU j G (REqValTyId.lhs c) (REqValTyId.lhs' c) (REqValTyId.domA c) u t lu lt (REqValTyId.eqL c)
          ; eqR = evlU j G (REqValTyId.rhs c) (REqValTyId.rhs' c) (REqValTyId.domA c) v t lv lt (REqValTyId.eqR c)
          }))
    where
      open R j
      c = snd (snd vt)
      lt : Le (suc (RANK t)) j
      lt = Le-trans (suc (RANK t)) (suc (max (RANK t) (max (RANK u) (RANK v)))) j
             (Le-max-l (RANK t) (max (RANK u) (RANK v))) bnd
      lu : Le (suc (RANK u)) j
      lu = Le-trans (suc (RANK u)) (suc (max (RANK t) (max (RANK u) (RANK v)))) j
             (Le-trans (RANK u) (max (RANK u) (RANK v)) (max (RANK t) (max (RANK u) (RANK v)))
                (Le-max-l (RANK u) (RANK v)) (Le-max-r (RANK t) (max (RANK u) (RANK v)))) bnd
      lv : Le (suc (RANK v)) j
      lv = Le-trans (suc (RANK v)) (suc (max (RANK t) (max (RANK u) (RANK v)))) j
             (Le-trans (RANK v) (max (RANK u) (RANK v)) (max (RANK t) (max (RANK u) (RANK v)))
                (Le-max-r (RANK u) (RANK v)) (Le-max-r (RANK t) (max (RANK u) (RANK v)))) bnd
  evtyU (suc j) G M N (RefEl w) bnd vt = vt

  ------------------------------------------------------------------
  -- evtyD
  ------------------------------------------------------------------
  evtyD (suc j) G M N Bot       bnd vt = vt
  evtyD (suc j) G M N UCode     bnd vt = vt
  evtyD (suc j) G M N (FunEl g) bnd vt = vt
  evtyD (suc j) G M N (PiCode b f) bnd vt =
    mkSigma (vtyD (suc j) G M (PiCode b f) bnd (fst vt))
      (mkSigma (vtyD (suc j) G N (PiCode b f) bnd (fst (snd vt)))
        (record
          { domA   = REqValTyPi.domA c
          ; codB   = REqValTyPi.codB c
          ; domA'  = REqValTyPi.domA' c
          ; codB'  = REqValTyPi.codB' c
          ; redM   = REqValTyPi.redM c
          ; redN   = REqValTyPi.redN c
          ; cohF   = REqValTyPi.cohF c
          ; fmAllU = REqValTyPi.fmAllU c
          ; convA  = REqValTyPi.convA c
          ; convB  = REqValTyPi.convB c
          ; eqA    = evtyD j G (REqValTyPi.domA c) (REqValTyPi.domA' c) b lb (REqValTyPi.eqA c)
          ; edgeET = \ u v sel P htP hv ->
                       evtyD j G (subst1 (REqValTyPi.codB c) P) (subst1 (REqValTyPi.codB' c) P) v (lv u v sel)
                         (REqValTyPi.edgeET c u v sel P htP
                           (vlU j G P (REqValTyPi.domA c) u b (lu u v sel) lb hv))
          }))
    where
      open R (suc j)
      c = snd (snd vt)
      lb : Le (suc (RANK b)) j
      lb = Le-trans (suc (RANK b)) (suc (max (RANK b) (RANKFun f))) j
             (Le-max-l (RANK b) (RANKFun f)) bnd
      lcod : Le (suc (RANKFun f)) j
      lcod = Le-trans (suc (RANKFun f)) (suc (max (RANK b) (RANKFun f))) j
               (Le-max-r (RANK b) (RANKFun f)) bnd
      lu : (u v : FinEl) -> Selection f u v -> Le (suc (RANK u)) j
      lu u v sel = Le-trans (suc (RANK u)) (suc (RANKFun f)) j (Selection-RANK-u sel) lcod
      lv : (u v : FinEl) -> Selection f u v -> Le (suc (RANK v)) j
      lv u v sel = Le-trans (suc (RANK v)) (suc (RANKFun f)) j (Selection-RANK-v sel) lcod
  evtyD (suc j) G M N (IdCode t u v) bnd vt =
    mkSigma (vtyD (suc j) G M (IdCode t u v) bnd (fst vt))
      (mkSigma (vtyD (suc j) G N (IdCode t u v) bnd (fst (snd vt)))
        (record
          { domA = REqValTyId.domA c ; lhs = REqValTyId.lhs c ; rhs = REqValTyId.rhs c
          ; domA' = REqValTyId.domA' c ; lhs' = REqValTyId.lhs' c ; rhs' = REqValTyId.rhs' c
          ; redM = REqValTyId.redM c ; redN = REqValTyId.redN c
          ; convA = REqValTyId.convA c ; convL = REqValTyId.convL c ; convR = REqValTyId.convR c
          ; eqA = evtyD j G (REqValTyId.domA c) (REqValTyId.domA' c) t lt (REqValTyId.eqA c)
          ; eqL = evlD j G (REqValTyId.lhs c) (REqValTyId.lhs' c) (REqValTyId.domA c) u t lu lt (REqValTyId.eqL c)
          ; eqR = evlD j G (REqValTyId.rhs c) (REqValTyId.rhs' c) (REqValTyId.domA c) v t lv lt (REqValTyId.eqR c)
          }))
    where
      open R (suc j)
      c = snd (snd vt)
      lt : Le (suc (RANK t)) j
      lt = Le-trans (suc (RANK t)) (suc (max (RANK t) (max (RANK u) (RANK v)))) j
             (Le-max-l (RANK t) (max (RANK u) (RANK v))) bnd
      lu : Le (suc (RANK u)) j
      lu = Le-trans (suc (RANK u)) (suc (max (RANK t) (max (RANK u) (RANK v)))) j
             (Le-trans (RANK u) (max (RANK u) (RANK v)) (max (RANK t) (max (RANK u) (RANK v)))
                (Le-max-l (RANK u) (RANK v)) (Le-max-r (RANK t) (max (RANK u) (RANK v)))) bnd
      lv : Le (suc (RANK v)) j
      lv = Le-trans (suc (RANK v)) (suc (max (RANK t) (max (RANK u) (RANK v)))) j
             (Le-trans (RANK v) (max (RANK u) (RANK v)) (max (RANK t) (max (RANK u) (RANK v)))
                (Le-max-r (RANK u) (RANK v)) (Le-max-r (RANK t) (max (RANK u) (RANK v)))) bnd
  evtyD (suc j) G M N (RefEl w) bnd vt = vt

  ------------------------------------------------------------------
  -- vlU : val (Stage j) = vl[Stage (j-1)]; transports the type-part via
  -- vtyU (lower index) and the RValPi via vlU/vlD/evlU/evlD (lower index).
  ------------------------------------------------------------------
  vlU (suc j) G M A u Bot                  bu ba vv = vv
  vlU (suc j) G M A UCode UCode            bu ba vv =
    mkSigma (vtyU (suc j) G A UCode ba (fst vv)) (vtyU (suc j) G M UCode ba (snd vv))
  vlU (suc j) G M A (PiCode a' f') UCode   bu ba vv =
    mkSigma (vtyU (suc j) G A UCode ba (fst vv)) (vtyU (suc j) G M (PiCode a' f') bu (snd vv))
  vlU (suc j) G M A Bot UCode              bu ba vv = vv
  vlU (suc j) G M A (FunEl g) UCode        bu ba vv = vv
  vlU (suc j) G M A u (FunEl h)            bu ba vv = vv
  vlU (suc j) G M A (FunEl g) (PiCode b f) bu ba vv =
    mkSigma (vtyU (suc j) G A (PiCode b f) ba (fst vv)) (rvpU j G M A g b f bu ba (snd vv))
  vlU (suc j) G M A Bot (PiCode b f)       bu ba vv = vv
  vlU (suc j) G M A UCode (PiCode b f)     bu ba vv = vv
  vlU (suc j) G M A (PiCode a' f') (PiCode b f) bu ba vv = vv
  vlU (suc j) G M A (IdCode t u v) UCode   bu ba vv =
    mkSigma (vtyU (suc j) G A UCode ba (fst vv)) (vtyU (suc j) G M (IdCode t u v) bu (snd vv))
  vlU (suc j) G M A (RefEl w) UCode        bu ba vv = vv
  vlU (suc j) G M A (IdCode t u v) (PiCode b f) bu ba vv = vv
  vlU (suc j) G M A (RefEl w) (PiCode b f) bu ba vv = vv
  vlU (suc j) G M A (RefEl w) (IdCode t' u' v') bu ba vv =
    mkSigma (vtyU (suc j) G A (IdCode t' u' v') ba (fst vv)) (rvidU j G M A w t' u' v' bu ba (snd vv))
  vlU (suc j) G M A Bot (IdCode a a1 a2)   bu ba vv = vv
  vlU (suc j) G M A UCode (IdCode a a1 a2) bu ba vv = vv
  vlU (suc j) G M A (FunEl g) (IdCode a a1 a2) bu ba vv = vv
  vlU (suc j) G M A (PiCode b f) (IdCode a a1 a2) bu ba vv = vv
  vlU (suc j) G M A (IdCode s0 s1 s2) (IdCode a a1 a2) bu ba vv = vv
  vlU (suc j) G M A u (RefEl a)            bu ba vv = vv

  ------------------------------------------------------------------
  -- vlD
  ------------------------------------------------------------------
  vlD (suc j) G M A u Bot                  bu ba vv = vv
  vlD (suc j) G M A UCode UCode            bu ba vv =
    mkSigma (vtyD (suc j) G A UCode ba (fst vv)) (vtyD (suc j) G M UCode ba (snd vv))
  vlD (suc j) G M A (PiCode a' f') UCode   bu ba vv =
    mkSigma (vtyD (suc j) G A UCode ba (fst vv)) (vtyD (suc j) G M (PiCode a' f') bu (snd vv))
  vlD (suc j) G M A Bot UCode              bu ba vv = vv
  vlD (suc j) G M A (FunEl g) UCode        bu ba vv = vv
  vlD (suc j) G M A u (FunEl h)            bu ba vv = vv
  vlD (suc j) G M A (FunEl g) (PiCode b f) bu ba vv =
    mkSigma (vtyD (suc j) G A (PiCode b f) ba (fst vv)) (rvpD j G M A g b f bu ba (snd vv))
  vlD (suc j) G M A Bot (PiCode b f)       bu ba vv = vv
  vlD (suc j) G M A UCode (PiCode b f)     bu ba vv = vv
  vlD (suc j) G M A (PiCode a' f') (PiCode b f) bu ba vv = vv
  vlD (suc j) G M A (IdCode t u v) UCode   bu ba vv =
    mkSigma (vtyD (suc j) G A UCode ba (fst vv)) (vtyD (suc j) G M (IdCode t u v) bu (snd vv))
  vlD (suc j) G M A (RefEl w) UCode        bu ba vv = vv
  vlD (suc j) G M A (IdCode t u v) (PiCode b f) bu ba vv = vv
  vlD (suc j) G M A (RefEl w) (PiCode b f) bu ba vv = vv
  vlD (suc j) G M A (RefEl w) (IdCode t' u' v') bu ba vv =
    mkSigma (vtyD (suc j) G A (IdCode t' u' v') ba (fst vv)) (rvidD j G M A w t' u' v' bu ba (snd vv))
  vlD (suc j) G M A Bot (IdCode a a1 a2)   bu ba vv = vv
  vlD (suc j) G M A UCode (IdCode a a1 a2) bu ba vv = vv
  vlD (suc j) G M A (FunEl g) (IdCode a a1 a2) bu ba vv = vv
  vlD (suc j) G M A (PiCode b f) (IdCode a a1 a2) bu ba vv = vv
  vlD (suc j) G M A (IdCode s0 s1 s2) (IdCode a a1 a2) bu ba vv = vv
  vlD (suc j) G M A u (RefEl a)            bu ba vv = vv

  ------------------------------------------------------------------
  -- evlU
  ------------------------------------------------------------------
  evlU (suc j) G M N A u Bot                  bu ba vv = vv
  evlU (suc j) G M N A UCode UCode            bu ba vv =
    mkSigma (vtyU (suc j) G A UCode ba (fst vv))
      (mkSigma (vtyU (suc j) G M UCode ba (fst (snd vv)))
        (mkSigma (vtyU (suc j) G N UCode ba (fst (snd (snd vv))))
          (evtyU (suc j) G M N UCode ba (snd (snd (snd vv))))))
  evlU (suc j) G M N A (PiCode a' f') UCode   bu ba vv =
    mkSigma (vtyU (suc j) G A UCode ba (fst vv))
      (mkSigma (vtyU (suc j) G M (PiCode a' f') bu (fst (snd vv)))
        (mkSigma (vtyU (suc j) G N (PiCode a' f') bu (fst (snd (snd vv))))
          (evtyU (suc j) G M N (PiCode a' f') bu (snd (snd (snd vv))))))
  evlU (suc j) G M N A Bot UCode              bu ba vv = vv
  evlU (suc j) G M N A (FunEl g) UCode        bu ba vv = vv
  evlU (suc j) G M N A u (FunEl h)            bu ba vv = vv
  evlU (suc j) G M N A (FunEl g) (PiCode b f) bu ba vv =
    mkSigma (vtyU (suc j) G A (PiCode b f) ba (fst vv))
      (mkSigma (rvpU j G M A g b f bu ba (fst (snd vv)))
        (mkSigma (rvpU j G N A g b f bu ba (fst (snd (snd vv))))
          (reqvpU j G M N A g b f bu ba (snd (snd (snd vv))))))
  evlU (suc j) G M N A Bot (PiCode b f)       bu ba vv = vv
  evlU (suc j) G M N A UCode (PiCode b f)     bu ba vv = vv
  evlU (suc j) G M N A (PiCode a' f') (PiCode b f) bu ba vv = vv
  evlU (suc j) G M N A (IdCode t u v) UCode   bu ba vv =
    mkSigma (vtyU (suc j) G A UCode ba (fst vv))
      (mkSigma (vtyU (suc j) G M (IdCode t u v) bu (fst (snd vv)))
        (mkSigma (vtyU (suc j) G N (IdCode t u v) bu (fst (snd (snd vv))))
          (evtyU (suc j) G M N (IdCode t u v) bu (snd (snd (snd vv))))))
  evlU (suc j) G M N A (RefEl w) UCode        bu ba vv = vv
  evlU (suc j) G M N A (IdCode t u v) (PiCode b f) bu ba vv = vv
  evlU (suc j) G M N A (RefEl w) (PiCode b f) bu ba vv = vv
  evlU (suc j) G M N A (RefEl w) (IdCode t' u' v') bu ba vv =
    mkSigma (vtyU (suc j) G A (IdCode t' u' v') ba (fst vv))
      (mkSigma (rvidU j G M A w t' u' v' bu ba (fst (snd vv)))
        (mkSigma (rvidU j G N A w t' u' v' bu ba (fst (snd (snd vv))))
          (reqvidU j G M N A w t' u' v' bu ba (snd (snd (snd vv))))))
  evlU (suc j) G M N A Bot (IdCode a a1 a2)   bu ba vv = vv
  evlU (suc j) G M N A UCode (IdCode a a1 a2) bu ba vv = vv
  evlU (suc j) G M N A (FunEl g) (IdCode a a1 a2) bu ba vv = vv
  evlU (suc j) G M N A (PiCode b f) (IdCode a a1 a2) bu ba vv = vv
  evlU (suc j) G M N A (IdCode s0 s1 s2) (IdCode a a1 a2) bu ba vv = vv
  evlU (suc j) G M N A u (RefEl a)            bu ba vv = vv

  ------------------------------------------------------------------
  -- evlD
  ------------------------------------------------------------------
  evlD (suc j) G M N A u Bot                  bu ba vv = vv
  evlD (suc j) G M N A UCode UCode            bu ba vv =
    mkSigma (vtyD (suc j) G A UCode ba (fst vv))
      (mkSigma (vtyD (suc j) G M UCode ba (fst (snd vv)))
        (mkSigma (vtyD (suc j) G N UCode ba (fst (snd (snd vv))))
          (evtyD (suc j) G M N UCode ba (snd (snd (snd vv))))))
  evlD (suc j) G M N A (PiCode a' f') UCode   bu ba vv =
    mkSigma (vtyD (suc j) G A UCode ba (fst vv))
      (mkSigma (vtyD (suc j) G M (PiCode a' f') bu (fst (snd vv)))
        (mkSigma (vtyD (suc j) G N (PiCode a' f') bu (fst (snd (snd vv))))
          (evtyD (suc j) G M N (PiCode a' f') bu (snd (snd (snd vv))))))
  evlD (suc j) G M N A Bot UCode              bu ba vv = vv
  evlD (suc j) G M N A (FunEl g) UCode        bu ba vv = vv
  evlD (suc j) G M N A u (FunEl h)            bu ba vv = vv
  evlD (suc j) G M N A (FunEl g) (PiCode b f) bu ba vv =
    mkSigma (vtyD (suc j) G A (PiCode b f) ba (fst vv))
      (mkSigma (rvpD j G M A g b f bu ba (fst (snd vv)))
        (mkSigma (rvpD j G N A g b f bu ba (fst (snd (snd vv))))
          (reqvpD j G M N A g b f bu ba (snd (snd (snd vv))))))
  evlD (suc j) G M N A Bot (PiCode b f)       bu ba vv = vv
  evlD (suc j) G M N A UCode (PiCode b f)     bu ba vv = vv
  evlD (suc j) G M N A (PiCode a' f') (PiCode b f) bu ba vv = vv
  evlD (suc j) G M N A (IdCode t u v) UCode   bu ba vv =
    mkSigma (vtyD (suc j) G A UCode ba (fst vv))
      (mkSigma (vtyD (suc j) G M (IdCode t u v) bu (fst (snd vv)))
        (mkSigma (vtyD (suc j) G N (IdCode t u v) bu (fst (snd (snd vv))))
          (evtyD (suc j) G M N (IdCode t u v) bu (snd (snd (snd vv))))))
  evlD (suc j) G M N A (RefEl w) UCode        bu ba vv = vv
  evlD (suc j) G M N A (IdCode t u v) (PiCode b f) bu ba vv = vv
  evlD (suc j) G M N A (RefEl w) (PiCode b f) bu ba vv = vv
  evlD (suc j) G M N A (RefEl w) (IdCode t' u' v') bu ba vv =
    mkSigma (vtyD (suc j) G A (IdCode t' u' v') ba (fst vv))
      (mkSigma (rvidD j G M A w t' u' v' bu ba (fst (snd vv)))
        (mkSigma (rvidD j G N A w t' u' v' bu ba (fst (snd (snd vv))))
          (reqvidD j G M N A w t' u' v' bu ba (snd (snd (snd vv))))))
  evlD (suc j) G M N A Bot (IdCode a a1 a2)   bu ba vv = vv
  evlD (suc j) G M N A UCode (IdCode a a1 a2) bu ba vv = vv
  evlD (suc j) G M N A (FunEl g) (IdCode a a1 a2) bu ba vv = vv
  evlD (suc j) G M N A (PiCode b f) (IdCode a a1 a2) bu ba vv = vv
  evlD (suc j) G M N A (IdCode s0 s1 s2) (IdCode a a1 a2) bu ba vv = vv
  evlD (suc j) G M N A u (RefEl a)            bu ba vv = vv

  ------------------------------------------------------------------
  -- RValPi / REqValPi transports
  ------------------------------------------------------------------
  rvpU j G M A g b f bu ba vp = record
    { domA0 = RValPi.domA0 vp
    ; codB0 = RValPi.codB0 vp
    ; red   = RValPi.red vp
    ; cohG  = RValPi.cohG vp
    ; fmG   = RValPi.fmG vp
    ; appV  = \ u v sel N htN hv ->
                vlU j G (App M N) (subst1 (RValPi.codB0 vp) N) v (EvalFun f u) (lv u v sel) (lef u)
                  (RValPi.appV vp u v sel N htN
                    (vlD j G N (RValPi.domA0 vp) u b (lu u v sel) lb hv))
    ; appE  = \ u v sel N1 N2 ht1 ht2 cv hev ->
                evlU j G (App M N1) (App M N2) (subst1 (RValPi.codB0 vp) N1) v (EvalFun f u) (lv u v sel) (lef u)
                  (RValPi.appE vp u v sel N1 N2 ht1 ht2 cv
                    (evlD j G N1 N2 (RValPi.domA0 vp) u b (lu u v sel) lb hev))
    }
    where
      open R j
      lb : Le (suc (RANK b)) j
      lb = Le-trans (suc (RANK b)) (suc (max (RANK b) (RANKFun f))) j (Le-max-l (RANK b) (RANKFun f)) ba
      lcf : Le (suc (RANKFun f)) j
      lcf = Le-trans (suc (RANKFun f)) (suc (max (RANK b) (RANKFun f))) j (Le-max-r (RANK b) (RANKFun f)) ba
      lu : (u v : FinEl) -> Selection g u v -> Le (suc (RANK u)) j
      lu u v sel = Le-trans (suc (RANK u)) (suc (RANKFun g)) j (Selection-RANK-u sel) bu
      lv : (u v : FinEl) -> Selection g u v -> Le (suc (RANK v)) j
      lv u v sel = Le-trans (suc (RANK v)) (suc (RANKFun g)) j (Selection-RANK-v sel) bu
      lef : (u : FinEl) -> Le (suc (RANK (EvalFun f u))) j
      lef u = Le-trans (suc (RANK (EvalFun f u))) (suc (RANKFun f)) j (RANK-EvalFun f u) lcf

  rvpD j G M A g b f bu ba vp = record
    { domA0 = RValPi.domA0 vp
    ; codB0 = RValPi.codB0 vp
    ; red   = RValPi.red vp
    ; cohG  = RValPi.cohG vp
    ; fmG   = RValPi.fmG vp
    ; appV  = \ u v sel N htN hv ->
                vlD j G (App M N) (subst1 (RValPi.codB0 vp) N) v (EvalFun f u) (lv u v sel) (lef u)
                  (RValPi.appV vp u v sel N htN
                    (vlU j G N (RValPi.domA0 vp) u b (lu u v sel) lb hv))
    ; appE  = \ u v sel N1 N2 ht1 ht2 cv hev ->
                evlD j G (App M N1) (App M N2) (subst1 (RValPi.codB0 vp) N1) v (EvalFun f u) (lv u v sel) (lef u)
                  (RValPi.appE vp u v sel N1 N2 ht1 ht2 cv
                    (evlU j G N1 N2 (RValPi.domA0 vp) u b (lu u v sel) lb hev))
    }
    where
      open R (suc j)
      lb : Le (suc (RANK b)) j
      lb = Le-trans (suc (RANK b)) (suc (max (RANK b) (RANKFun f))) j (Le-max-l (RANK b) (RANKFun f)) ba
      lcf : Le (suc (RANKFun f)) j
      lcf = Le-trans (suc (RANKFun f)) (suc (max (RANK b) (RANKFun f))) j (Le-max-r (RANK b) (RANKFun f)) ba
      lu : (u v : FinEl) -> Selection g u v -> Le (suc (RANK u)) j
      lu u v sel = Le-trans (suc (RANK u)) (suc (RANKFun g)) j (Selection-RANK-u sel) bu
      lv : (u v : FinEl) -> Selection g u v -> Le (suc (RANK v)) j
      lv u v sel = Le-trans (suc (RANK v)) (suc (RANKFun g)) j (Selection-RANK-v sel) bu
      lef : (u : FinEl) -> Le (suc (RANK (EvalFun f u))) j
      lef u = Le-trans (suc (RANK (EvalFun f u))) (suc (RANKFun f)) j (RANK-EvalFun f u) lcf

  reqvpU j G M N A g b f bu ba vp = record
    { domA0 = REqValPi.domA0 vp
    ; codB0 = REqValPi.codB0 vp
    ; red   = REqValPi.red vp
    ; cohG  = REqValPi.cohG vp
    ; fmG   = REqValPi.fmG vp
    ; appEV = \ u v sel P htP hv ->
                evlU j G (App M P) (App N P) (subst1 (REqValPi.codB0 vp) P) v (EvalFun f u) (lv u v sel) (lef u)
                  (REqValPi.appEV vp u v sel P htP
                    (vlD j G P (REqValPi.domA0 vp) u b (lu u v sel) lb hv))
    }
    where
      open R j
      lb : Le (suc (RANK b)) j
      lb = Le-trans (suc (RANK b)) (suc (max (RANK b) (RANKFun f))) j (Le-max-l (RANK b) (RANKFun f)) ba
      lcf : Le (suc (RANKFun f)) j
      lcf = Le-trans (suc (RANKFun f)) (suc (max (RANK b) (RANKFun f))) j (Le-max-r (RANK b) (RANKFun f)) ba
      lu : (u v : FinEl) -> Selection g u v -> Le (suc (RANK u)) j
      lu u v sel = Le-trans (suc (RANK u)) (suc (RANKFun g)) j (Selection-RANK-u sel) bu
      lv : (u v : FinEl) -> Selection g u v -> Le (suc (RANK v)) j
      lv u v sel = Le-trans (suc (RANK v)) (suc (RANKFun g)) j (Selection-RANK-v sel) bu
      lef : (u : FinEl) -> Le (suc (RANK (EvalFun f u))) j
      lef u = Le-trans (suc (RANK (EvalFun f u))) (suc (RANKFun f)) j (RANK-EvalFun f u) lcf

  reqvpD j G M N A g b f bu ba vp = record
    { domA0 = REqValPi.domA0 vp
    ; codB0 = REqValPi.codB0 vp
    ; red   = REqValPi.red vp
    ; cohG  = REqValPi.cohG vp
    ; fmG   = REqValPi.fmG vp
    ; appEV = \ u v sel P htP hv ->
                evlD j G (App M P) (App N P) (subst1 (REqValPi.codB0 vp) P) v (EvalFun f u) (lv u v sel) (lef u)
                  (REqValPi.appEV vp u v sel P htP
                    (vlU j G P (REqValPi.domA0 vp) u b (lu u v sel) lb hv))
    }
    where
      open R (suc j)
      lb : Le (suc (RANK b)) j
      lb = Le-trans (suc (RANK b)) (suc (max (RANK b) (RANKFun f))) j (Le-max-l (RANK b) (RANKFun f)) ba
      lcf : Le (suc (RANKFun f)) j
      lcf = Le-trans (suc (RANKFun f)) (suc (max (RANK b) (RANKFun f))) j (Le-max-r (RANK b) (RANKFun f)) ba
      lu : (u v : FinEl) -> Selection g u v -> Le (suc (RANK u)) j
      lu u v sel = Le-trans (suc (RANK u)) (suc (RANKFun g)) j (Selection-RANK-u sel) bu
      lv : (u v : FinEl) -> Selection g u v -> Le (suc (RANK v)) j
      lv u v sel = Le-trans (suc (RANK v)) (suc (RANKFun g)) j (Selection-RANK-v sel) bu
      lef : (u : FinEl) -> Le (suc (RANK (EvalFun f u))) j
      lef u = Le-trans (suc (RANK (EvalFun f u))) (suc (RANKFun f)) j (RANK-EvalFun f u) lcf

  rvidU j G M A w t u v bu ba vp = record
    { domA0 = RValId.domA0 vp ; lhs0 = RValId.lhs0 vp ; rhs0 = RValId.rhs0 vp
    ; red = RValId.red vp ; wit0 = RValId.wit0 vp ; redTm = RValId.redTm vp
    ; refConvL = RValId.refConvL vp ; refConvR = RValId.refConvR vp ; refMem = RValId.refMem vp
    ; endEqL = evlU j G (RValId.wit0 vp) (RValId.lhs0 vp) (RValId.domA0 vp) w t bu lt (RValId.endEqL vp)
    ; endEqR = evlU j G (RValId.wit0 vp) (RValId.rhs0 vp) (RValId.domA0 vp) w t bu lt (RValId.endEqR vp) }
    where
      open R j
      lt : Le (suc (RANK t)) j
      lt = Le-trans (suc (RANK t)) (suc (max (RANK t) (max (RANK u) (RANK v)))) j (Le-max-l (RANK t) (max (RANK u) (RANK v))) ba

  rvidD j G M A w t u v bu ba vp = record
    { domA0 = RValId.domA0 vp ; lhs0 = RValId.lhs0 vp ; rhs0 = RValId.rhs0 vp
    ; red = RValId.red vp ; wit0 = RValId.wit0 vp ; redTm = RValId.redTm vp
    ; refConvL = RValId.refConvL vp ; refConvR = RValId.refConvR vp ; refMem = RValId.refMem vp
    ; endEqL = evlD j G (RValId.wit0 vp) (RValId.lhs0 vp) (RValId.domA0 vp) w t bu lt (RValId.endEqL vp)
    ; endEqR = evlD j G (RValId.wit0 vp) (RValId.rhs0 vp) (RValId.domA0 vp) w t bu lt (RValId.endEqR vp) }
    where
      open R (suc j)
      lt : Le (suc (RANK t)) j
      lt = Le-trans (suc (RANK t)) (suc (max (RANK t) (max (RANK u) (RANK v)))) j (Le-max-l (RANK t) (max (RANK u) (RANK v))) ba

  reqvidU j G M N A w t u v bu ba vp = record
    { domA0 = REqValId.domA0 vp ; lhs0 = REqValId.lhs0 vp ; rhs0 = REqValId.rhs0 vp
    ; red = REqValId.red vp ; wit0M = REqValId.wit0M vp ; wit0N = REqValId.wit0N vp
    ; redTmM = REqValId.redTmM vp ; redTmN = REqValId.redTmN vp ; refMem = REqValId.refMem vp
    ; endEqLM = evlU j G (REqValId.wit0M vp) (REqValId.lhs0 vp) (REqValId.domA0 vp) w t bu lt (REqValId.endEqLM vp)
    ; endEqRM = evlU j G (REqValId.wit0M vp) (REqValId.rhs0 vp) (REqValId.domA0 vp) w t bu lt (REqValId.endEqRM vp)
    ; endEqLN = evlU j G (REqValId.wit0N vp) (REqValId.lhs0 vp) (REqValId.domA0 vp) w t bu lt (REqValId.endEqLN vp)
    ; endEqRN = evlU j G (REqValId.wit0N vp) (REqValId.rhs0 vp) (REqValId.domA0 vp) w t bu lt (REqValId.endEqRN vp) }
    where
      open R j
      lt : Le (suc (RANK t)) j
      lt = Le-trans (suc (RANK t)) (suc (max (RANK t) (max (RANK u) (RANK v)))) j (Le-max-l (RANK t) (max (RANK u) (RANK v))) ba

  reqvidD j G M N A w t u v bu ba vp = record
    { domA0 = REqValId.domA0 vp ; lhs0 = REqValId.lhs0 vp ; rhs0 = REqValId.rhs0 vp
    ; red = REqValId.red vp ; wit0M = REqValId.wit0M vp ; wit0N = REqValId.wit0N vp
    ; redTmM = REqValId.redTmM vp ; redTmN = REqValId.redTmN vp ; refMem = REqValId.refMem vp
    ; endEqLM = evlD j G (REqValId.wit0M vp) (REqValId.lhs0 vp) (REqValId.domA0 vp) w t bu lt (REqValId.endEqLM vp)
    ; endEqRM = evlD j G (REqValId.wit0M vp) (REqValId.rhs0 vp) (REqValId.domA0 vp) w t bu lt (REqValId.endEqRM vp)
    ; endEqLN = evlD j G (REqValId.wit0N vp) (REqValId.lhs0 vp) (REqValId.domA0 vp) w t bu lt (REqValId.endEqLN vp)
    ; endEqRN = evlD j G (REqValId.wit0N vp) (REqValId.rhs0 vp) (REqValId.domA0 vp) w t bu lt (REqValId.endEqRN vp) }
    where
      open R (suc j)
      lt : Le (suc (RANK t)) j
      lt = Le-trans (suc (RANK t)) (suc (max (RANK t) (max (RANK u) (RANK v)))) j (Le-max-l (RANK t) (max (RANK u) (RANK v))) ba
