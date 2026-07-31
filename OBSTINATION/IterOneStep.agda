{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.IterOneStep
--
-- DISCHARGING THE ONE-STEP LAW OF `IterCycleComp` FROM `uoh`.
--
-- `IterCycleComp` derives the d-step recurrence `DStep` from the one-step
-- law
--
--   ONE-STEP LAW    psi i (m+1) = phi i (psi (p i) m)        (m >= N)
--
-- which it takes as a hypothesis.  This file PROVES it, by applying the
-- case-3 universal clause of the joint verdict of H at an analysis point
--
--   P  =  appT V (embedTup Y)                  (`module At`)
--
-- to the actual iterate tuples  arg m = appF (iter m) Y.  Here V is any
-- ar-tuple of D-values -- the STRATIFICATION of `IterStrat`: a slot carries
-- `inf` while its coordinate is believed to diverge and its actual finite
-- limit once that is known.  The TOP point
--
--   Q  =  topQ ar (embedTup Y)  =  <inf,...,inf, Y>
--
-- is the all-inf instance ON THE NOSE, and is re-exported by
-- `open At (repT ar inf) (length-repT ar inf) public`, so every earlier
-- interface of this module survives unchanged.
--
-- Only THREE things ever used the top point rather than a general one, and
-- each is generalised here:
--
--   * `topQ-inf-range`  ->  `At.inf-range`, from `appT-inf-range`: the
--     parameter part is `embedTup Y`, all of whose coordinates are finite,
--     so `Eq (get j P) inf` forces j < length V = ar.  The read-graph lands
--     inside the block for free, at ANY stratification.
--   * `length-topQ`     ->  `At.length-P`, from `length-appT-embed` and
--     the hypothesis `lenV : Eq (length V) ar`.
--   * `splitBelow (repT ar inf) (embedTup Y)`  ->  `splitBelow V (embedTup Y)`;
--     `bel-recPart : Below recPart V` is used only for `length-recPart`.
--
-- THE FOUR SIDE CONDITIONS of the case-3 clause, and how they are met:
--
--   1. Eq (length X) (length A0)               -- pure bookkeeping
--        `arg-len`, from `iterVec-length` and `Below-length`.
--   2. LeN k m'   (the consulted slot has passed h's threshold)
--   4. LeFTup (del (p i) A0) (del (p i) X)     (the approximant is dominated)
--        BOTH are consequences of the single condition
--
--            Reach m  =  LeFTup A0 (arg m)
--
--        the iterate tuple dominates the approximant.  Condition 2 comes
--        out of `getF-le` at the slot, condition 4 out of `del-LeFTup`.
--        `Reach` is upward closed in m (`ReachAt-up`), so ONE stage N
--        suffices, which is exactly the shape `IterCycleComp` expects.
--   3. Eq (getF (p i) X) (fbot m')             -- the consulted slot is
--        still incomplete.  This is the hypothesis `allbot`; by
--        `IterShape.cpl-persists` a component that fails it has already
--        stabilised (and falls in the ConstFrom branch), so the height
--        analysis never has to touch it.
--
-- WHAT REMAINS (the dispatch).  Nothing here produces the stage N.  Two
-- handles are provided for that step:
--
--   * `Reach-dec` -- Reach is decidable at every stage, so the dispatch
--     can branch on it exactly as `PrecInfDispatch` branches on
--     `LeD-dec (bot k0) (uSeq rd Y k0)`;
--   * `Reach-from-rec` / `Reach-coord` -- `splitBelow` cuts A0 into its
--     recursion part (ar entries, all below the corresponding entry of V)
--     and its parameter part, and the parameter half of `Reach` holds
--     unconditionally.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.IterOneStep where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.Property
open import OBSTINATION.PropertyAt using (Case3at ; UOat ; getF-le)
open import OBSTINATION.PropertyVec using (compOf ; UOM ; UOMall)
open import OBSTINATION.Extension using (del-LeFTup)
open import OBSTINATION.Refine using (Below-length)
open import OBSTINATION.CompPull using (LeFTup-trans)
open import OBSTINATION.PhiProps using (addN)
open import OBSTINATION.IterFun
open import OBSTINATION.IterShape using (iter ; iter-le ; IsBot)
open import OBSTINATION.IterSeq using (appT)
open import OBSTINATION.IterGraph using
  (repT ; topQ ; c3-slot ; c3-thr ; c3-phi ; c3-inf)
open import OBSTINATION.IterCompose using (DStep)
open import OBSTINATION.IterCycleComp using (pIter ; Comp ; cycle-DStep)

------------------------------------------------------------------------
-- The two remaining projections out of a case-3 verdict
--
-- (`IterGraph` has slot / threshold / phi / PhiOK / inf; these two are the
-- ones the universal clause itself needs.  f, A, A0 explicit, as there.)
------------------------------------------------------------------------

module _ (f : FTup -> FEl) (A : Tup) (A0 : FTup) where

  c3-eqk : (c : Case3at f A A0) ->
    Eq (getF (c3-slot f A A0 c) A0) (fbot (c3-thr f A A0 c))
  c3-eqk c = fst (snd (snd (snd c)))

  c3-univ : (c : Case3at f A A0) (X : FTup) (m : Nat) ->
    Eq (length X) (length A0) ->
    LeN (c3-thr f A A0 c) m ->
    Eq (getF (c3-slot f A A0 c) X) (fbot m) ->
    LeFTup (del (c3-slot f A A0 c) A0) (del (c3-slot f A A0 c) X) ->
    Eq (f X) (fbot (c3-phi f A A0 c m))
  c3-univ c = snd (snd (snd (snd (snd (snd c)))))

------------------------------------------------------------------------
-- Length bookkeeping for appends
------------------------------------------------------------------------

length-appF : (A B : FTup) -> Eq (length (appF A B)) (addN (length B) (length A))
length-appF nil        B = refl
length-appF (cons a A) B = Eq-cong suc (length-appF A B)

length-appT : (A B : Tup) -> Eq (length (appT A B)) (addN (length B) (length A))
length-appT nil        B = refl
length-appT (cons a A) B = Eq-cong suc (length-appT A B)

length-repT : (r : Nat) (d : D) -> Eq (length (repT r d)) r
length-repT zero    d = refl
length-repT (suc r) d = Eq-cong suc (length-repT r d)

length-embedTup : (A : FTup) -> Eq (length (embedTup A)) (length A)
length-embedTup nil         = refl
length-embedTup (cons a A)  = Eq-cong suc (length-embedTup A)

-- the length of a general analysis point `appT V (embedTup Y)`
length-appT-embed : (V : Tup) (Y : FTup) ->
  Eq (length (appT V (embedTup Y))) (addN (length Y) (length V))
length-appT-embed V Y =
  Eq-trans (length-appT V (embedTup Y))
    (Eq-cong (\ n -> addN n (length V)) (length-embedTup Y))

length-topQ : (r : Nat) (Y : FTup) ->
  Eq (length (topQ r (embedTup Y))) (addN (length Y) r)
length-topQ r Y =
  Eq-trans (length-appT-embed (repT r inf) Y)
    (Eq-cong (addN (length Y)) (length-repT r inf))

------------------------------------------------------------------------
-- Coordinates of an append, in and out of range
------------------------------------------------------------------------

getF-appF : (j : Nat) (A B : FTup) -> LeN (suc j) (length A) ->
  Eq (getF j (appF A B)) (getF j A)
getF-appF j       nil        B ()
getF-appF zero    (cons a A) B lt = refl
getF-appF (suc j) (cons a A) B lt = getF-appF j A B lt

-- out of range, `getF` is the default S^0(bot)
getF-out : (j : Nat) (A : FTup) -> Not (LeN (suc j) (length A)) ->
  Eq (getF j A) (fbot zero)
getF-out j       nil        nlt = refl
getF-out zero    (cons a A) nlt = Empty-elim (nlt tt)
getF-out (suc j) (cons a A) nlt = getF-out j A nlt

------------------------------------------------------------------------
-- AN INFINITE COORDINATE OF AN ANALYSIS POINT IS A RECURSION SLOT
--
-- The parameter part is embedTup Y, every coordinate of which is finite;
-- only the entries coming from V can be inf.  This holds at ANY
-- stratification V, not just the top one.
------------------------------------------------------------------------

embedTup-not-inf : (j : Nat) (T : FTup) -> Eq (get j (embedTup T)) inf -> Empty
embedTup-not-inf j       nil                ()
embedTup-not-inf zero    (cons (fbot k) xs) ()
embedTup-not-inf zero    (cons (fcpl k) xs) ()
embedTup-not-inf (suc j) (cons x xs)        e = embedTup-not-inf j xs e

appT-inf-range : (V : Tup) (T : FTup) (j : Nat) ->
  Eq (get j (appT V (embedTup T))) inf -> LeN (suc j) (length V)
appT-inf-range nil        T j       e = Empty-elim (embedTup-not-inf j T e)
appT-inf-range (cons d V) T zero    e = tt
appT-inf-range (cons d V) T (suc j) e = appT-inf-range V T j e

topQ-inf-range : (r : Nat) (Y : FTup) (j : Nat) ->
  Eq (get j (topQ r (embedTup Y))) inf -> LeN (suc j) r
topQ-inf-range r Y j e =
  Eq-transport (\ n -> LeN (suc j) n) (length-repT r inf)
    (appT-inf-range (repT r inf) Y j e)

------------------------------------------------------------------------
-- Shape of an incomplete coordinate, and its height
------------------------------------------------------------------------

hgt : FEl -> Nat
hgt (fbot k) = k
hgt (fcpl k) = k

Incompl : FEl -> Set
Incompl (fbot _) = Top
Incompl (fcpl _) = Empty

-- it is `IterShape.IsBot`, only without the module parameters
Incompl-IsBot : (idt : IterData) (Y : FTup) (x : FEl) -> Incompl x -> IsBot idt Y x
Incompl-IsBot idt Y (fbot k) t  = t
Incompl-IsBot idt Y (fcpl k) ()

incompl-shape : (x : FEl) -> Incompl x -> Eq x (fbot (hgt x))
incompl-shape (fbot k) t  = refl
incompl-shape (fcpl k) ()

------------------------------------------------------------------------
-- Decidability and coordinatewise description of the tuple order
------------------------------------------------------------------------

LeTup-dec : (A B : Tup) -> Dec (LeTup A B)
LeTup-dec nil         nil         = yes tt
LeTup-dec nil         (cons _ _)  = no (\ ())
LeTup-dec (cons _ _)  nil         = no (\ ())
LeTup-dec (cons x xs) (cons y ys) = comb (LeD-dec x y) (LeTup-dec xs ys)
  where
    comb : Dec (LeD x y) -> Dec (LeTup xs ys) -> Dec (Pair (LeD x y) (LeTup xs ys))
    comb (yes a) (yes b)  = yes (mkSigma a b)
    comb (yes a) (no nb)  = no (\ q -> nb (snd q))
    comb (no na) (yes b)  = no (\ q -> na (fst q))
    comb (no na) (no nb)  = no (\ q -> na (fst q))

LeFTup-dec : (A B : FTup) -> Dec (LeFTup A B)
LeFTup-dec A B = LeTup-dec (embedTup A) (embedTup B)

LeFTup-coord : (A B : FTup) -> Eq (length A) (length B) ->
  ((j : Nat) -> LeN (suc j) (length A) -> LeF (getF j A) (getF j B)) ->
  LeFTup A B
LeFTup-coord nil        nil        e h = tt
LeFTup-coord nil        (cons _ _) () h
LeFTup-coord (cons _ _) nil        () h
LeFTup-coord (cons a A) (cons b B) e h =
  mkSigma (h zero tt) (LeFTup-coord A B (suc-inj e) (\ j lt -> h (suc j) lt))

------------------------------------------------------------------------
-- Splitting a finite approximant of an append
--
-- Below A0 (appT P T) cuts A0 into the part below P and the part below T.
------------------------------------------------------------------------

splitBelow : (P T : Tup) (A0 : FTup) -> Below A0 (appT P T) ->
  Sigma FTup (\ A1 -> Sigma FTup (\ A2 ->
    Pair (Eq A0 (appF A1 A2)) (Pair (Below A1 P) (Below A2 T))))
splitBelow nil        T A0          bel = mkSigma nil (mkSigma A0 (mkSigma refl (mkSigma tt bel)))
splitBelow (cons d P) T nil         ()
splitBelow (cons d P) T (cons a A0) bel =
  mkSigma (cons a A1) (mkSigma A2
    (mkSigma (Eq-cong (cons a) eqA)
      (mkSigma (mkSigma (fst bel) bel1) bel2)))
  where
    rec = splitBelow P T A0 (snd bel)
    A1  = fst rec
    A2  = fst (snd rec)
    eqA : Eq A0 (appF A1 A2)
    eqA = fst (snd (snd rec))
    bel1 : Below A1 P
    bel1 = fst (snd (snd (snd rec)))
    bel2 : Below A2 T
    bel2 = snd (snd (snd (snd rec)))

------------------------------------------------------------------------
-- The setting: a mutual block and its parameters.
--
-- Everything down to `psi` is INDEPENDENT of the analysis point.
------------------------------------------------------------------------

module _ (idt : IterData) (Y : FTup) where
  open IterData idt

  ----------------------------------------------------------------------
  -- The iterates, and the tuples the step function is actually applied to
  ----------------------------------------------------------------------

  it : Nat -> FTup
  it m = iter idt Y m

  arg : Nat -> FTup
  arg m = appF (it m) Y

  -- the recursion unfolds by applying H to arg (holds by refl)
  it-suc : (m : Nat) -> Eq (it (suc m)) (H (arg m))
  it-suc m = refl

  length-it : (m : Nat) -> Eq (length (it m)) ar
  length-it m = iterVec-length G H ar lenG lenH (fbot m) Y

  ----------------------------------------------------------------------
  -- Side conditions 2 and 4: ONE condition, upward closed in the stage
  --
  -- Stated at an ARBITRARY approximant.  Which one matters: the joint one
  -- couples the components -- one component's demand on a slot is imposed
  -- on all of them -- whereas each component's OWN approximant demands only
  -- what that component needs.  See `IterEach`.
  ----------------------------------------------------------------------

  ReachAt : FTup -> Nat -> Set
  ReachAt A0 m = LeFTup A0 (arg m)

  arg-le : (a b : Nat) -> LeN a b -> LeFTup (arg a) (arg b)
  arg-le a b le = appF-mono (iter-le idt Y a b le) (LeFTup-refl Y)

  ReachAt-up : (A0 : FTup) (a b : Nat) -> LeN a b -> ReachAt A0 a -> ReachAt A0 b
  ReachAt-up A0 a b le ra = LeFTup-trans ra (arg-le a b le)

  -- ANTITONE in the approximant: a smaller approximant is easier to reach.
  -- This is the formal content of the per-component refinement -- each
  -- component's own approximant is below the join that the joint witness
  -- uses, so `ReachAt (B i)` is a weaker demand than `Reach`.
  ReachAt-anti : (A0 A0' : FTup) -> LeFTup A0 A0' -> (m : Nat) ->
    ReachAt A0' m -> ReachAt A0 m
  ReachAt-anti A0 A0' le m r = LeFTup-trans le r

  ReachAt-dec : (A0 : FTup) (m : Nat) -> Dec (ReachAt A0 m)
  ReachAt-dec A0 m = LeFTup-dec A0 (arg m)

  -- the shape hypothesis, at a recursion slot of an incomplete component
  slot-shape : (j m : Nat) -> LeN (suc j) ar -> Incompl (getF j (it m)) ->
    Eq (getF j (arg m)) (fbot (hgt (getF j (it m))))
  slot-shape j m lt ib =
    Eq-trans
      (getF-appF j (it m) Y
        (Eq-transport (\ n -> LeN (suc j) n) (Eq-sym (length-it m)) lt))
      (incompl-shape (getF j (it m)) ib)

  psi : Nat -> Nat -> Nat
  psi i m = hgt (getF i (it m))

  ----------------------------------------------------------------------
  -- THE ANALYSIS POINT, stratified
  --
  --   P = appT V (embedTup Y),   length V = ar
  --
  -- V = repT ar inf is the top point, re-exported below; a general V
  -- carries the finite limits of the coordinates already settled
  -- (`IterStrat`).
  ----------------------------------------------------------------------

  module At (V : Tup) (lenV : Eq (length V) ar) where

    P : Tup
    P = appT V (embedTup Y)

    length-P : Eq (length P) (addN (length Y) ar)
    length-P =
      Eq-trans (length-appT-embed V Y) (Eq-cong (addN (length Y)) lenV)

    -- an infinite coordinate of P is a recursion slot
    inf-range : (j : Nat) -> Eq (get j P) inf -> LeN (suc j) ar
    inf-range j e =
      Eq-transport (\ n -> LeN (suc j) n) lenV (appT-inf-range V Y j e)

    uP : UOM H ar P
    uP = uoh P

    -- one approximant, ar verdicts
    P0 : FTup
    P0 = fst uP

    belP0 : Below P0 P
    belP0 = fst (snd uP)

    verdict : (i : Nat) -> LeN (suc i) ar -> UOat (compOf H i) P P0
    verdict = snd (snd uP)

    --------------------------------------------------------------------
    -- Side condition 1: lengths
    --------------------------------------------------------------------

    -- for ANY approximant below P -- the analysis is not tied to the joint one
    arg-len-at : (A0 : FTup) -> Below A0 P -> (m : Nat) ->
      Eq (length (arg m)) (length A0)
    arg-len-at A0 bel m =
      Eq-trans (Eq-trans (length-appF (it m) Y) (Eq-cong (addN (length Y)) (length-it m)))
        (Eq-sym (Eq-trans (Below-length bel) length-P))

    arg-len : (m : Nat) -> Eq (length (arg m)) (length P0)
    arg-len = arg-len-at P0 belP0

    Reach : Nat -> Set
    Reach = ReachAt P0

    Reach-up : (a b : Nat) -> LeN a b -> Reach a -> Reach b
    Reach-up = ReachAt-up P0

    Reach-dec : (m : Nat) -> Dec (Reach m)
    Reach-dec = ReachAt-dec P0

    --------------------------------------------------------------------
    -- Reach reduced to the recursion slots
    --
    -- A0 splits as <A1, A2> with A1 the ar recursion entries and A2 below
    -- the parameters; the A2 half of Reach holds unconditionally, so only
    -- the growth of the iterates past A1 is at issue.
    --------------------------------------------------------------------

    -- again at an ARBITRARY approximant below P
    module _ (A0 : FTup) (bel : Below A0 P) where

      private
        sB = splitBelow V (embedTup Y) A0 bel

      recPart : FTup
      recPart = fst sB

      parPart : FTup
      parPart = fst (snd sB)

      split-at : Eq A0 (appF recPart parPart)
      split-at = fst (snd (snd sB))

      bel-recPart : Below recPart V
      bel-recPart = fst (snd (snd (snd sB)))

      -- Below parPart (embedTup Y) IS LeFTup parPart Y
      le-parPart : LeFTup parPart Y
      le-parPart = snd (snd (snd (snd sB)))

      length-recPart : Eq (length recPart) ar
      length-recPart = Eq-trans (Below-length bel-recPart) lenV

      ReachAt-from-rec : (m : Nat) -> LeFTup recPart (it m) -> ReachAt A0 m
      ReachAt-from-rec m le =
        Eq-transport (\ Z -> LeFTup Z (arg m)) (Eq-sym split-at)
          (appF-mono le le-parPart)

      -- ... and further down to a coordinatewise (i.e. numeric) condition
      ReachAt-coord : (m : Nat) ->
        ((j : Nat) -> LeN (suc j) (length recPart) ->
          LeF (getF j recPart) (getF j (it m))) ->
        ReachAt A0 m
      ReachAt-coord m h =
        ReachAt-from-rec m
          (LeFTup-coord recPart (it m)
            (Eq-trans length-recPart (Eq-sym (length-it m))) h)

    -- the joint instances
    P1 : FTup
    P1 = recPart P0 belP0

    P2 : FTup
    P2 = parPart P0 belP0

    P0-split : Eq P0 (appF P1 P2)
    P0-split = split-at P0 belP0

    belP1 : Below P1 V
    belP1 = bel-recPart P0 belP0

    leP2 : LeFTup P2 Y
    leP2 = le-parPart P0 belP0

    length-P1 : Eq (length P1) ar
    length-P1 = length-recPart P0 belP0

    Reach-from-rec : (m : Nat) -> LeFTup P1 (it m) -> Reach m
    Reach-from-rec = ReachAt-from-rec P0 belP0

    Reach-coord : (m : Nat) ->
      ((j : Nat) -> LeN (suc j) (length P1) -> LeF (getF j P1) (getF j (it m))) ->
      Reach m
    Reach-coord = ReachAt-coord P0 belP0

    --------------------------------------------------------------------
    -- APPLYING A CASE-3 VERDICT AT AN ITERATE
    --
    -- This is the whole content: the universal clause of h_i's case-3
    -- verdict, instantiated at X = arg m, with the four side conditions
    -- discharged.
    --------------------------------------------------------------------

    -- the consulted slot is a recursion slot
    c3-slot-range-at : (A0 : FTup) (i : Nat) (c : Case3at (compOf H i) P A0) ->
      LeN (suc (c3-slot (compOf H i) P A0 c)) ar
    c3-slot-range-at A0 i c =
      inf-range (c3-slot (compOf H i) P A0 c) (c3-inf (compOf H i) P A0 c)

    c3-slot-range : (i : Nat) (c : Case3at (compOf H i) P P0) ->
      LeN (suc (c3-slot (compOf H i) P P0 c)) ar
    c3-slot-range = c3-slot-range-at P0

    onestep-c3-at : (A0 : FTup) (bel : Below A0 P)
      (i : Nat) (c : Case3at (compOf H i) P A0) (m n : Nat) ->
      ReachAt A0 m ->
      Eq (getF (c3-slot (compOf H i) P A0 c) (arg m)) (fbot n) ->
      Eq (getF i (it (suc m))) (fbot (c3-phi (compOf H i) P A0 c n))
    onestep-c3-at A0 bel i c m n rm shp =
      c3-univ (compOf H i) P A0 c (arg m) n (arg-len-at A0 bel m) thr-le shp
        (del-LeFTup (c3-slot (compOf H i) P A0 c) rm)
      where
        pi : Nat
        pi = c3-slot (compOf H i) P A0 c

        -- side condition 2: the consulted slot has passed h_i's threshold
        thr-le : LeN (c3-thr (compOf H i) P A0 c) n
        thr-le =
          Eq-transport (\ z -> LeD (embed z) (embed (fbot n)))
            (c3-eqk (compOf H i) P A0 c)
            (Eq-transport (\ z -> LeD (embed (getF pi A0)) (embed z)) shp
              (getF-le pi rm))

    onestep-c3 : (i : Nat) (c : Case3at (compOf H i) P P0) (m n : Nat) ->
      Reach m ->
      Eq (getF (c3-slot (compOf H i) P P0 c) (arg m)) (fbot n) ->
      Eq (getF i (it (suc m))) (fbot (c3-phi (compOf H i) P P0 c n))
    onestep-c3 = onestep-c3-at P0 belP0

    -- the consulted slot has passed the verdict's threshold -- side condition
    -- 2, exposed on its own because the ConstFrom analysis needs it directly
    slot-thr : (A0 : FTup) (i : Nat) (c : Case3at (compOf H i) P A0) (m : Nat) ->
      ReachAt A0 m ->
      Incompl (getF (c3-slot (compOf H i) P A0 c) (it m)) ->
      LeN (c3-thr (compOf H i) P A0 c)
          (hgt (getF (c3-slot (compOf H i) P A0 c) (it m)))
    slot-thr A0 i c m rm ib =
      Eq-transport
        (\ z -> LeD (embed z) (embed (fbot (hgt (getF pi (it m))))))
        (c3-eqk (compOf H i) P A0 c)
        (Eq-transport (\ z -> LeD (embed (getF pi A0)) (embed z))
          (slot-shape pi m (c3-slot-range-at A0 i c) ib)
          (getF-le pi rm))
      where
        pi : Nat
        pi = c3-slot (compOf H i) P A0 c

    --------------------------------------------------------------------
    -- THE ONE-STEP LAW
    --
    -- Total p, phi, psi in the shape `IterCycleComp` wants.  Off-range
    -- components are given the trivial data: `getF i (it m)` is then the
    -- default S^0(bot), so the law holds there by `getF-out`.
    --------------------------------------------------------------------

    -- Ax is a FAMILY of approximants, one per component.  Taking the constant
    -- family <P0,...,P0> recovers the joint analysis; taking each component's
    -- own approximant is strictly weaker in what `ReachAt` then demands.
    module _ (Ax : Nat -> FTup)
             (belAx : (i : Nat) -> LeN (suc i) ar -> Below (Ax i) P)
             (all3 : (i : Nat) -> LeN (suc i) ar -> Case3at (compOf H i) P (Ax i))
             where

      pOf : (i : Nat) -> Dec (LeN (suc i) ar) -> Nat
      pOf i (yes lt) = c3-slot (compOf H i) P (Ax i) (all3 i lt)
      pOf i (no _)   = zero

      p : Nat -> Nat
      p i = pOf i (LeN-dec (suc i) ar)

      phiOf : (i : Nat) -> Dec (LeN (suc i) ar) -> Nat -> Nat
      phiOf i (yes lt) = c3-phi (compOf H i) P (Ax i) (all3 i lt)
      phiOf i (no _)   = \ _ -> zero

      phi : Nat -> Nat -> Nat
      phi i = phiOf i (LeN-dec (suc i) ar)

      -- the verdict's threshold, likewise total
      thrOf : (i : Nat) -> Dec (LeN (suc i) ar) -> Nat
      thrOf i (yes lt) = c3-thr (compOf H i) P (Ax i) (all3 i lt)
      thrOf i (no _)   = zero

      thr : Nat -> Nat
      thr i = thrOf i (LeN-dec (suc i) ar)

      -- the read-graph successor really is a slot of the block
      p-range : (i : Nat) -> LeN (suc i) ar -> LeN (suc (p i)) ar
      p-range i = rng (LeN-dec (suc i) ar)
        where
          rng : (d : Dec (LeN (suc i) ar)) -> LeN (suc i) ar -> LeN (suc (pOf i d)) ar
          rng (yes lt) _   = c3-slot-range-at (Ax i) i (all3 i lt)
          rng (no nlt) lt' = Empty-elim (nlt lt')

      module _ (allbot : (j m : Nat) -> LeN (suc j) ar -> Incompl (getF j (it m)))
               (N : Nat) (rN : (i : Nat) -> LeN (suc i) ar -> ReachAt (Ax i) N) where

        one-step-d : (i : Nat) (d : Dec (LeN (suc i) ar)) (m : Nat) -> LeN N m ->
          Eq (psi i (suc m)) (phiOf i d (psi (pOf i d) m))
        one-step-d i (yes lt) m lm =
          Eq-cong hgt
            (onestep-c3-at (Ax i) (belAx i lt) i (all3 i lt) m
              (psi (c3-slot (compOf H i) P (Ax i) (all3 i lt)) m)
              (ReachAt-up (Ax i) N m lm (rN i lt))
              (slot-shape (c3-slot (compOf H i) P (Ax i) (all3 i lt)) m
                (c3-slot-range-at (Ax i) i (all3 i lt))
                (allbot (c3-slot (compOf H i) P (Ax i) (all3 i lt)) m
                  (c3-slot-range-at (Ax i) i (all3 i lt)))))
        one-step-d i (no nlt) m lm =
          Eq-cong hgt
            (getF-out i (it (suc m))
              (\ q -> nlt (Eq-transport (\ n -> LeN (suc i) n) (length-it (suc m)) q)))

        one-step : (i m : Nat) -> LeN N m -> Eq (psi i (suc m)) (phi i (psi (p i) m))
        one-step i = one-step-d i (LeN-dec (suc i) ar)

        ----------------------------------------------------------------
        -- ... and hence the d-step recurrence `IterCompose` dispatches on
        ----------------------------------------------------------------

        block-DStep : (d i : Nat) -> Eq (pIter p d i) i ->
          DStep N d (psi i) (Comp p phi i d)
        block-DStep = cycle-DStep N p phi psi one-step

  ----------------------------------------------------------------------
  -- THE TOP POINT is the all-inf stratification, ON THE NOSE
  --
  --   Q = appT (repT ar inf) (embedTup Y) = topQ ar (embedTup Y)
  --
  -- so re-exporting `At` at that instance reproduces every interface this
  -- module had before it was made generic.
  ----------------------------------------------------------------------

  open At (repT ar inf) (length-repT ar inf) public
    renaming (P to Q ; uP to uQ ; P0 to Q0 ;
              belP0 to belQ0 ; P1 to Q1 ; P2 to Q2 ; P0-split to Q0-split ;
              belP1 to belQ1 ; leP2 to leQ2 ; length-P1 to length-Q1 ;
              inf-range to Q-inf-range)
