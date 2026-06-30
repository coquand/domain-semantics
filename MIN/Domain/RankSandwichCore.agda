{-# OPTIONS --without-K --exact-split #-}
------------------------------------------------------------------------
-- RankSandwichCore.agda  (MIN/ -- Pi + U fragment)
--
-- The statement SStmt of Lemma S, and the single-edge family-reduction
-- core `edgeCore` -- the mathematical heart of the type-code shrink.
--
-- Given the IH `ih : SStmt m`, a typed member family xf : x0 -> U and a
-- cap family bf with xf <= bf, edgeCore takes one lower-family demand
-- (u , v) [v <= EvalFun xf u] and produces a reduced typed edge
-- (u2 : x0', v2 : U) of rank <= m with u2 <= u, v <= v2 <= EvalFun bf u2,
-- and a reduced domain x0' in [lo, b0].
--
-- The construction (the resolved coupling):
--   * u_x  = typedKeyJoin xf u v   : x0, u_x <= u, v <= EvalFun xf u_x.
--   * mu   = keyJoinLemma bf u_x (EvalFun xf u_x)   -- cap-support taken
--            AT u_x (so mu <= u_x automatically).
--   * (u2, x0') = ih (mu , u_x , x0)  -- couple-reduce u_x : x0 inside
--            [mu, u], keeping EvalFun bf u2 >= EvalFun xf u_x >= v.
--   * v2   = ih (v , EvalFun xf u_x , U)  -- typeShrink the typed value.
------------------------------------------------------------------------
module MIN.Domain.RankSandwichCore where

open import MIN.Domain.Basic
  using ( Nat ; zero ; suc ; max ; Le ; Le-refl ; Le-trans ; Top ; tt ; Empty
        ; Pair ; Sigma ; mkSigma ; fst ; snd
        ; FinEl ; Bot ; UCode ; FunEl ; PiCode ; FinFun ; nil ; cons
        ; Eq ; Eq-sym ; Eq-transport )
open import MIN.Domain.Order
  using ( RANK ; RANKFun ; Sup ; Coherent ; CoherentFunTail ; NotBot
        ; EvalFun ; LeCode ; LeFunCode ; LeCode-trans ; Coherent-EvalFun
        ; EvalFun-mon ; EvalFun-mon-arg ; ev-bridge ; RANK-ev )
open import MIN.Domain.MemStage using ( finMemC )
open import MIN.Domain.Membership using ( FinMemAllU ; allU-to )
open import MIN.Domain.MemProps using ( finMem-upward ; EvalFun-in-UCode )
open import MIN.Domain.MemUnfold using ( FinMem-coh-u ; FinMem-a-in-U ; FinMem-coh-a )
open import MIN.Domain.KeyJoinLemma using ( keyJoinLemma ; typedKeyJoin )
open import MIN.Domain.Order using ( Le-max-lub )
open import MIN.Domain.FamU using ( FamToU ; build-h2 ; piU-intro )

------------------------------------------------------------------------
-- The statement.
------------------------------------------------------------------------
SOut : Nat -> FinEl -> FinEl -> FinEl -> FinEl -> Set
SOut n a b c d =
  Sigma FinEl (\ x' -> Sigma FinEl (\ z' ->
    Pair (Le (RANK x') n) (Pair (Le (RANK z') n)
    (Pair (LeCode a x') (Pair (LeCode x' b)
    (Pair (LeCode c z') (Pair (LeCode z' d) (finMemC x' z'))))))))

SStmt : Nat -> Set
SStmt n =
  (a b c d x z : FinEl) ->
  Le (RANK a) n -> Le (RANK b) n -> Le (RANK c) n -> Le (RANK d) n ->
  Le (RANK x) (suc n) -> Le (RANK z) (suc n) ->
  Coherent a -> Coherent b -> Coherent c -> Coherent d ->
  Coherent x -> Coherent z ->
  LeCode a x -> LeCode x b -> LeCode c z -> LeCode z d -> finMemC x z ->
  SOut n a b c d

------------------------------------------------------------------------
-- small helpers.
------------------------------------------------------------------------

-- NotBot is upward closed under LeCode.
notbot-le : (v w : FinEl) -> LeCode v w -> NotBot v -> NotBot w
notbot-le v UCode        le nb = tt
notbot-le v (FunEl g)    le nb = tt
notbot-le v (PiCode a f) le nb = tt
notbot-le Bot          Bot le nb = nb
notbot-le UCode        Bot le nb = le
notbot-le (FunEl g)    Bot le nb = le
notbot-le (PiCode a f) Bot le nb = le

-- canonical RANK (EvalFun h u) <= RANKFun h  (exposed from ev-bridge/RANK-ev).
RANK-EvalFun : (h : FinFun) (u : FinEl) -> Le (RANK (EvalFun h u)) (RANKFun h)
RANK-EvalFun h u =
  let M = max (RANKFun h) (RANK u)
  in Eq-transport (\ x -> Le (RANK x) (RANKFun h))
       (Eq-sym (ev-bridge M h u (Le-refl M)))
       (RANK-ev (suc M) h u)

------------------------------------------------------------------------
-- The reduced-edge output.
------------------------------------------------------------------------
record EdgeOut (m : Nat) (lo b0 : FinEl) (bf : FinFun) (u v : FinEl) : Set where
  constructor mkEdgeOut
  field
    eX0' eU2 eV2 : FinEl
    e-x0'U   : finMemC eX0' UCode
    e-rk-x0' : Le (RANK eX0') m
    e-lo-x0' : LeCode lo eX0'
    e-x0'-b0 : LeCode eX0' b0
    e-u2x0'  : finMemC eU2 eX0'
    e-rk-u2  : Le (RANK eU2) m
    e-u2u    : LeCode eU2 u
    e-v2U    : finMemC eV2 UCode
    e-rk-v2  : Le (RANK eV2) m
    e-v-v2   : LeCode v eV2
    e-v2-bf  : LeCode eV2 (EvalFun bf eU2)
    e-cu2    : Coherent eU2
    e-cv2    : Coherent eV2
    e-nb-v2  : NotBot eV2

------------------------------------------------------------------------
-- edgeCore.
------------------------------------------------------------------------
edgeCore : (m : Nat) (ih : SStmt m)
  (x0 lo b0 : FinEl) (xf bf : FinFun) (u v : FinEl) ->
  Coherent x0 -> finMemC x0 UCode -> Le (RANK x0) (suc m) ->
  Coherent lo -> Le (RANK lo) m -> LeCode lo x0 ->
  Coherent b0 -> Le (RANK b0) m -> LeCode x0 b0 ->
  CoherentFunTail xf -> FinMemAllU xf x0 -> Le (RANKFun xf) (suc m) ->
  CoherentFunTail bf -> Le (RANKFun bf) m -> LeFunCode xf bf ->
  Coherent u -> Le (RANK u) m -> Coherent v -> Le (RANK v) m -> NotBot v ->
  LeCode v (EvalFun xf u) ->
  EdgeOut m lo b0 bf u v
edgeCore m ih x0 lo b0 xf bf u v
  cx0 x0U rx0 clo rlo lox0 cb0 rb0 x0b0
  cxf allU rxf cbf rbf xfbf cu ru cv rv nbv lev =
  mkEdgeOut x0' u2 v2 x0'U rk-x0' lo-x0' x0'-b0 u2x0' rk-u2 u2u
            v2U rk-v2 v-v2 v2-bfu2 cu2 cv2 nb-v2
  where
    -- typed witness u_x : x0
    tkj = typedKeyJoin xf x0 u v cxf cu cv cx0 x0U allU lev
    ux  = fst tkj
    uxu : LeCode ux u
    uxu = fst (snd tkj)
    rk-ux0 : Le (RANK ux) (RANKFun xf)
    rk-ux0 = fst (snd (snd tkj))
    v-Vx : LeCode v (EvalFun xf ux)
    v-Vx = fst (snd (snd (snd tkj)))
    uxX0 : finMemC ux x0
    uxX0 = snd (snd (snd (snd tkj)))
    cux : Coherent ux
    cux = FinMem-coh-u ux x0 uxX0
    rk-ux : Le (RANK ux) (suc m)
    rk-ux = Le-trans (RANK ux) (RANKFun xf) (suc m) rk-ux0 rxf
    -- the typed value Vx = EvalFun xf ux
    cVx : Coherent (EvalFun xf ux)
    cVx = Coherent-EvalFun xf ux cxf cux
    VxU : finMemC (EvalFun xf ux) UCode
    VxU = EvalFun-in-UCode xf ux x0 cxf cux (allU-to xf x0 allU)
    rk-Vx : Le (RANK (EvalFun xf ux)) (suc m)
    rk-Vx = Le-trans (RANK (EvalFun xf ux)) (RANKFun xf) (suc m) (RANK-EvalFun xf ux) rxf
    Vx-bfux : LeCode (EvalFun xf ux) (EvalFun bf ux)
    Vx-bfux = EvalFun-mon xf bf ux cxf cbf cux xfbf
    -- cap support mu, taken AT ux  (so mu <= ux)
    kj  = keyJoinLemma bf ux (EvalFun xf ux) cbf cux cVx Vx-bfux
    mu  = fst kj
    mu-ux : LeCode mu ux
    mu-ux = fst (snd kj)
    rk-mu0 : Le (RANK mu) (RANKFun bf)
    rk-mu0 = fst (snd (snd kj))
    Vx-bfmu : LeCode (EvalFun xf ux) (EvalFun bf mu)
    Vx-bfmu = fst (snd (snd (snd kj)))
    cmu : Coherent mu
    cmu = snd (snd (snd (snd kj)))
    rk-mu : Le (RANK mu) m
    rk-mu = Le-trans (RANK mu) (RANKFun bf) m rk-mu0 rbf
    -- couple-reduce  (ux : x0)  inside [mu, u] x [lo, b0]
    keyred = ih mu u lo b0 ux x0 rk-mu ru rlo rb0 rk-ux rx0
                cmu cu clo cb0 cux cx0 mu-ux uxu lox0 x0b0 uxX0
    u2  = fst keyred
    x0' = fst (snd keyred)
    krest = snd (snd keyred)
    rk-u2 : Le (RANK u2) m
    rk-u2 = fst krest
    rk-x0' : Le (RANK x0') m
    rk-x0' = fst (snd krest)
    mu-u2 : LeCode mu u2
    mu-u2 = fst (snd (snd krest))
    u2u : LeCode u2 u
    u2u = fst (snd (snd (snd krest)))
    lo-x0' : LeCode lo x0'
    lo-x0' = fst (snd (snd (snd (snd krest))))
    x0'-b0 : LeCode x0' b0
    x0'-b0 = fst (snd (snd (snd (snd (snd krest)))))
    u2x0' : finMemC u2 x0'
    u2x0' = snd (snd (snd (snd (snd (snd krest)))))
    cu2 : Coherent u2
    cu2 = FinMem-coh-u u2 x0' u2x0'
    x0'U : finMemC x0' UCode
    x0'U = FinMem-a-in-U u2 x0' u2x0'
    -- cap at the reduced key
    cbfu2 : Coherent (EvalFun bf u2)
    cbfu2 = Coherent-EvalFun bf u2 cbf cu2
    rk-bfu2 : Le (RANK (EvalFun bf u2)) m
    rk-bfu2 = Le-trans (RANK (EvalFun bf u2)) (RANKFun bf) m (RANK-EvalFun bf u2) rbf
    cbfmu : Coherent (EvalFun bf mu)
    cbfmu = Coherent-EvalFun bf mu cbf cmu
    Vx-bfu2 : LeCode (EvalFun xf ux) (EvalFun bf u2)
    Vx-bfu2 = LeCode-trans (EvalFun xf ux) (EvalFun bf mu) (EvalFun bf u2)
                cVx cbfmu cbfu2 Vx-bfmu
                (EvalFun-mon-arg bf mu u2 mu-u2 cbf cmu cu2)
    -- typeShrink the typed value Vx into [v, EvalFun bf u2]
    valred = ih v (EvalFun bf u2) Bot UCode (EvalFun xf ux) UCode
                rv rk-bfu2 tt tt rk-Vx tt
                cv cbfu2 tt tt cVx tt
                v-Vx Vx-bfu2 tt tt VxU
    v2  = fst valred
    z'' = fst (snd valred)
    vrest = snd (snd valred)
    rk-v2 : Le (RANK v2) m
    rk-v2 = fst vrest
    v-v2 : LeCode v v2
    v-v2 = fst (snd (snd vrest))
    v2-bfu2 : LeCode v2 (EvalFun bf u2)
    v2-bfu2 = fst (snd (snd (snd vrest)))
    z''-U : LeCode z'' UCode
    z''-U = fst (snd (snd (snd (snd (snd vrest)))))
    v2z'' : finMemC v2 z''
    v2z'' = snd (snd (snd (snd (snd (snd vrest)))))
    cz'' : Coherent z''
    cz'' = FinMem-coh-a v2 z'' v2z''
    v2U : finMemC v2 UCode
    v2U = finMem-upward v2 z'' UCode z''-U cz'' tt v2z'' tt
    cv2 : Coherent v2
    cv2 = FinMem-coh-u v2 z'' v2z''
    nb-v2 : NotBot v2
    nb-v2 = notbot-le v v2 v-v2 nbv

------------------------------------------------------------------------
-- Single-demand type-code shrink (T1 / T2 with a one-edge lower family):
--   a = PiCode a0 {(u,v)},  x = PiCode x0 xf : U,  b = PiCode b0 bf
--   ==>  x' = PiCode x0' {(u2,v2)} : U  in [a, b], rank <= suc m.
-- This is edgeCore assembled into a Pi via build-h2 + piU-intro.
------------------------------------------------------------------------
typeShrink1 : (m : Nat) (ih : SStmt m)
  (x0 a0 b0 : FinEl) (xf bf : FinFun) (u v : FinEl) ->
  Coherent x0 -> finMemC x0 UCode -> Le (RANK x0) (suc m) ->
  Coherent a0 -> Le (RANK a0) m -> LeCode a0 x0 ->
  Coherent b0 -> Le (RANK b0) m -> LeCode x0 b0 ->
  CoherentFunTail xf -> FinMemAllU xf x0 -> Le (RANKFun xf) (suc m) ->
  CoherentFunTail bf -> Le (RANKFun bf) m -> LeFunCode xf bf ->
  Coherent u -> Le (RANK u) m -> Coherent v -> Le (RANK v) m -> NotBot v ->
  LeCode v (EvalFun xf u) ->
  Sigma FinEl (\ x' ->
    Pair (finMemC x' UCode)
    (Pair (Le (RANK x') (suc m))
    (Pair (LeCode (PiCode a0 (cons (mkSigma u v) nil)) x')
          (LeCode x' (PiCode b0 bf)))))
typeShrink1 m ih x0 a0 b0 xf bf u v
  cx0 x0U rx0 ca0 ra0 a0x0 cb0 rb0 x0b0
  cxf allU rxf cbf rbf xfbf cu ru cv rv nbv lev =
  mkSigma x' (mkSigma x'U (mkSigma rk-x' (mkSigma a-x' x'-b)))
  where
    eo = edgeCore m ih x0 a0 b0 xf bf u v
           cx0 x0U rx0 ca0 ra0 a0x0 cb0 rb0 x0b0
           cxf allU rxf cbf rbf xfbf cu ru cv rv nbv lev
    x0' = EdgeOut.eX0' eo
    u2  = EdgeOut.eU2 eo
    v2  = EdgeOut.eV2 eo
    bh = build-h2 x0' u2 v2 u v bf
           (EdgeOut.e-u2x0' eo) (EdgeOut.e-v2U eo)
           (EdgeOut.e-cu2 eo) (EdgeOut.e-cv2 eo) (EdgeOut.e-nb-v2 eo)
           cu cv (EdgeOut.e-u2u eo) (EdgeOut.e-v-v2 eo) (EdgeOut.e-v2-bf eo)
    fam : FamToU x0' (cons (mkSigma u2 v2) nil)
    fam = fst bh
    x' = PiCode x0' (cons (mkSigma u2 v2) nil)
    x'U : finMemC x' UCode
    x'U = piU-intro x0' (cons (mkSigma u2 v2) nil) (EdgeOut.e-x0'U eo) fam
    rk-x' : Le (RANK x') (suc m)
    rk-x' = Le-max-lub (RANK x0') (max (RANK u2) (max (RANK v2) zero)) m
              (EdgeOut.e-rk-x0' eo)
              (Le-max-lub (RANK u2) (max (RANK v2) zero) m
                (EdgeOut.e-rk-u2 eo)
                (Le-max-lub (RANK v2) zero m (EdgeOut.e-rk-v2 eo) tt))
    a-x' : LeCode (PiCode a0 (cons (mkSigma u v) nil)) x'
    a-x' = mkSigma (EdgeOut.e-lo-x0' eo) (fst (snd bh))
    x'-b : LeCode x' (PiCode b0 bf)
    x'-b = mkSigma (EdgeOut.e-x0'-b0 eo) (snd (snd bh))
