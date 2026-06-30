{-# OPTIONS --without-K --exact-split #-}
------------------------------------------------------------------------
-- FamU.agda  (MIN/ -- Pi + U fragment)
--
-- The notion  "f : a → U"  for analysing  Pi a f : U, defined so that
--
--     a : U   and   f : a → U      ⟺      Pi a f : U.
--
-- Concretely  f : a → U  is the family-well-formedness data of the type:
-- every edge (x ↦ y) of the finite family f has key x : a and value
-- y : U, and f is a coherent finite graph.  (`FinMemAllU f a` packages the
-- per-edge "x : a, y : U"; `CoherentFunTail f` the coherence.)
------------------------------------------------------------------------
module MIN.Domain.FamU where

open import MIN.Domain.Basic
  using ( FinEl ; FinFun ; UCode ; PiCode ; Bot ; cons ; nil ; Pair ; mkSigma ; fst ; snd ; tt
        ; Eq-transport )
open import MIN.Domain.Order
  using ( Coherent ; CoherentFunTail ; NotBot ; EvalFun ; LeCode ; LeFunCode
        ; LeCode-trans ; Coherent-EvalFun ; EvalFun-mon-arg ; LeFunCode-refl
        ; Sup ; Sup-Bot-right )
open import MIN.Domain.OrderStage using ( mkCFT )
open import MIN.Domain.MemStage using ( finMemC )
open import MIN.Domain.Membership
  using ( FinMemAllU ; finMem-piU-dom ; finMem-piU-allU ; finMem-piU-cft
        ; finMem-piU-mk ; EvalFun-in-UCode )
open import MIN.Model.Selection
  using ( Edge ; EdgeIn ; here ; Selection ; singleton-selection
        ; Selection-le-EvalFun ; CoherentFun-edge-key )

------------------------------------------------------------------------
-- edge-le (reproved locally, type-in-type-free): an edge's value is
-- below EvalFun gp x whenever its key is below x.  (Same proof as in
-- RankInterpFunEl, but that module is --type-in-type, which we avoid.)
------------------------------------------------------------------------
edge-le : (e' : Edge) (gp : FinFun) (x : FinEl) ->
  CoherentFunTail gp -> EdgeIn e' gp -> Coherent x -> Coherent (snd e') ->
  LeCode (fst e') x -> LeCode (snd e') (EvalFun gp x)
edge-le e' gp x cgp ein cx cv' lekx =
  let sel0 = singleton-selection e' gp ein
      sel  = Eq-transport (\ uu -> Selection gp uu (snd e')) (Sup-Bot-right (fst e'))
               (Eq-transport (\ vv -> Selection gp (Sup (fst e') Bot) vv)
                 (Sup-Bot-right (snd e')) sel0)
      ck   = CoherentFun-edge-key e' gp cgp ein
      le1  = Selection-le-EvalFun gp sel (LeFunCode-refl gp cgp) cgp cgp ck
      cefk = Coherent-EvalFun gp (fst e') cgp ck
      cefx = Coherent-EvalFun gp x cgp cx
      mon  = EvalFun-mon-arg gp (fst e') x lekx cgp ck cx
  in LeCode-trans (snd e') (EvalFun gp (fst e')) (EvalFun gp x) cv' cefk cefx le1 mon

-- f : a → U
record FamToU (a : FinEl) (f : FinFun) : Set where
  constructor mkFamToU
  field
    keysInA : FinMemAllU f a      -- each edge (x ↦ y):  x : a  and  y : U
    cohFam  : CoherentFunTail f   -- f is a coherent finite graph

------------------------------------------------------------------------
-- The intended equivalence:   a : U  ∧  f : a → U   ⟺   Pi a f : U.
------------------------------------------------------------------------

-- (→)  Pi a f : U   gives   a : U   and   f : a → U.
piU-elim : (a : FinEl) (f : FinFun) ->
  finMemC (PiCode a f) UCode -> Pair (finMemC a UCode) (FamToU a f)
piU-elim a f mem =
  mkSigma (finMem-piU-dom a f mem)
          (mkFamToU (finMem-piU-allU a f mem) (finMem-piU-cft a f mem))

-- (←)  a : U   and   f : a → U   give   Pi a f : U.
piU-intro : (a : FinEl) (f : FinFun) ->
  finMemC a UCode -> FamToU a f -> finMemC (PiCode a f) UCode
piU-intro a f aU fam =
  finMem-piU-mk a f aU (FamToU.keysInA fam) (FamToU.cohFam fam)

------------------------------------------------------------------------
-- The "application" reading is now a DERIVED consequence: a family
-- f : a → U sends every coherent member of a to a type code.
------------------------------------------------------------------------

famAt : (a : FinEl) (f : FinFun) -> FamToU a f ->
  (u : FinEl) -> Coherent u -> finMemC u a -> finMemC (EvalFun f u) UCode
famAt a f fam u cu _ =
  EvalFun-in-UCode f u a (FamToU.cohFam fam) cu (FamToU.keysInA fam)

------------------------------------------------------------------------
-- Re-analysis of the interval problem (case a = b = UCode, w = Pi w0 wf)
-- THROUGH the equivalence  a : U ∧ f : a → U ⟺ Pi a f : U.
--
-- By `piU-elim`,  w : U  gives  w0 : U  and  FamToU w0 wf.  The order
-- v ≤ w ≤ u unfolds to a domain interval  v0 ≤ w0 ≤ u0  and a family
-- sandwich  vf ⊑ wf ⊑ uf.  To produce the witness w1 = Pi w1_0 w1_f : U
-- (via `piU-intro`) we need:
--    (D)  w1_0 : U of rank n-1 with v0 ≤ w1_0 ≤ u0      -- the DOMAIN
--    (F)  FamToU w1_0 w1_f of rank n-1 with vf ⊑ w1_f ⊑ uf   -- the FAMILY
--
-- (D) is the problem itself at rank n-1 (induction hypothesis): w0 : U,
--     v0 ≤ w0 ≤ u0, so a rank-(n-1) type code w1_0 in [v0,u0] exists.
--
-- (F) is the crux.  Two cases close it immediately:
--    * if u : U   -- take w1 = u  (rank n, u : U, v ≤ u ≤ u).
--    * if v : U   -- take w1 = Pi w1_0 vf  : here  vf : v0 → U  (v : U),
--      and since v0 ≤ w1_0 its keys upcast to w1_0, so FamToU w1_0 vf;
--      vf ⊑ vf and vf ⊑ uf (from vf ⊑ wf ⊑ uf) give v ≤ w1 ≤ u.
--
-- So the ONLY difficult case is:  v : U fails AND u : U fails
-- (both interval endpoints are coherent NON-types).  There the family
-- keys carrying the demands sit in w0 / u0 (or are "wild"), and must be
-- re-typed into the *reduced* domain w1_0 ≤ u0 -- the keys-in-w1_0
-- obligation that `FamToU` makes explicit and that has no free upcast.
-- That both-endpoints-non-type case is the sharp target for the next
-- step (a counterexample, or the family-reconstruction lemma).
------------------------------------------------------------------------

------------------------------------------------------------------------
-- SINGLE-EDGE family case (g = {(u,v)}), the core of the family half.
--
-- Given the reduced pieces the recursion produces -- a reduced domain d2
-- and a reduced edge (u2, v2) with  u2 : d2,  v2 : U,  u2 ≤ u,  v ≤ v2,
-- and  v2 ≤ EvalFun l u2  (the cap) -- the single-edge family
-- h2 = {(u2, v2)} satisfies everything:  h2 : d2 → U,  {(u,v)} ≤ h2,  h2 ≤ l.
------------------------------------------------------------------------
build-h2 : (d2 u2 v2 u v : FinEl) (l : FinFun) ->
  finMemC u2 d2 -> finMemC v2 UCode ->
  Coherent u2 -> Coherent v2 -> NotBot v2 -> Coherent u -> Coherent v ->
  LeCode u2 u -> LeCode v v2 -> LeCode v2 (EvalFun l u2) ->
  Pair (FamToU d2 (cons (mkSigma u2 v2) nil))
    (Pair (LeFunCode (cons (mkSigma u v) nil) (cons (mkSigma u2 v2) nil))
          (LeFunCode (cons (mkSigma u2 v2) nil) l))
build-h2 d2 u2 v2 u v l u2d2 v2U cu2 cv2 nbv2 cu cv lu2u lvv2 lv2lu2 =
  mkSigma
    (mkFamToU (mkSigma (mkSigma u2d2 v2U) tt)            -- FinMemAllU {(u2,v2)} d2
              (mkCFT cu2 cv2 nbv2 tt tt))                -- CoherentFunTail {(u2,v2)}
    (mkSigma
      (mkSigma v-le-eval tt)                             -- {(u,v)} ≤ {(u2,v2)}
      (mkSigma lv2lu2 tt))                               -- {(u2,v2)} ≤ l
  where
    h2 = cons (mkSigma u2 v2) nil
    cohh2 : CoherentFunTail h2
    cohh2 = mkCFT cu2 cv2 nbv2 tt tt
    -- v2 ≤ EvalFun h2 u   (u2 ≤ u fires the single edge)
    v2-le-eval : LeCode v2 (EvalFun h2 u)
    v2-le-eval = edge-le (mkSigma u2 v2) h2 u cohh2 here cu cv2 lu2u
    -- v ≤ EvalFun h2 u
    v-le-eval : LeCode v (EvalFun h2 u)
    v-le-eval = LeCode-trans v v2 (EvalFun h2 u) cv cv2
                  (Coherent-EvalFun h2 u cohh2 cu) lvv2 v2-le-eval
