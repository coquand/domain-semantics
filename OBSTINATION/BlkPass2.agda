{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.BlkPass2
--
-- THE HEIGHT CLAUSE (H) IS PRESERVED BY MUTUAL RECURSION, r = 2.
--
--     HPass (kv 0) -> HPass (kv 1)  ==>  HPass (\ m -> hgt m j)
--
-- (plus the (I) data of the step terms, which `MainBlk2` already needs).
-- Together with `MainBlk2.MPblock` -- the (I) half, which needs no height
-- clause at all -- this closes the recursion clause of the Main Property
--
--     MP (iv, kv) = (I) EvConstN iv  /\  (H) HPass kv
--
-- at r = 2.  Note that the analogous statement for the DECIDED verdict (G) is
-- FALSE (`BlkGrowFail`: it implies LPO), and this is where the difference
-- bites: the proof below never decides whether a height is bounded.
--
-- THE ARGUMENT.  `MainBlk2.comp-verdict` says of each component: either its
-- height and replay depth are FROZEN from a known depth on, or its replay has
-- PASSED its own threshold at a known depth.  In the second case
-- `WalkAffine.affine` turns the step term's demand walk into an affine law
--
--     hgt (m+1) j = kv j (D j + avl m (I j))            (`affine-law`)
--
-- -- past its threshold the component's height is a FIXED monotone function of
-- the height available at ONE coordinate, the one its step term ultimately
-- demands.  Then it is a finite case analysis on where that coordinate points:
--
--   * a PARAMETER, or a component that is frozen: the height is eventually
--     constant (`ev-from`, `hpass-evconst`);
--   * ITSELF: a deterministic monotone one-coordinate iteration, so (H) holds
--     with no hypothesis at all (`from-iter`, `MPPass.IterF.it-pass`) -- this
--     is exactly the configuration for which the global verdict is LPO;
--   * the OTHER component, which in turn points at ITSELF or a parameter: (H)
--     for the other one first, then `MPPass.hpass-comp2` composes the two
--     verdicts (`from-tail`);
--   * the OTHER component, which points back: a CROSS-CYCLE, so composing the
--     two affine laws around it gives a one-coordinate iteration of PERIOD 2
--     (`MPPass.double`), and `from-iter` again.
--
-- The period-2 collapse is `MutCross`'s "compose around the cycle", here at
-- the trace level and for arbitrary step terms rather than the affine case.
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.BlkPass2 where

open import OBSTINATION.Prelude
open import OBSTINATION.BlkReplay using (plus ; plus-ge-r ; plus-mono ; plus-suc-r)
open import OBSTINATION.MPPass using
  (Mono ; HPass ; MP ; plus-ge-l ; double ; double-ge ;
   hpass-cong ; hpass-sub ; hpass-evconst ; hpass-comp2 ; module IterF)
open import OBSTINATION.WalkAffine using (Dof ; affine)
open import OBSTINATION.BlkTraceR using
  (hv ; av ; nn ; cIdx ; q ; av-rec ; av-param)
open import OBSTINATION.MainBlk2 using
  (one ; two ; oth ; oth-range ; oth-uniq ;
   hgt ; avl ; stp ; hgt-mono ; stp-mono ; Verdict ; comp-verdict ; MPblock)

-- in a two-element block the other of the other is the one
oth-oth : (j : Nat) -> LeN (suc j) two -> Eq (oth (oth j)) j
oth-oth zero          lj = refl
oth-oth (suc zero)    lj = refl
oth-oth (suc (suc j)) ()

------------------------------------------------------------------------
-- THE DATA: the two step terms' traces, their (I), and their (H)
------------------------------------------------------------------------

module _ (a : Nat)
         (iv : Nat -> Nat -> Nat)
         (ivr : (j n : Nat) -> LeN (suc (iv j n)) a)
         (kv : Nat -> Nat -> Nat)
         (kv-mono : (j n n' : Nat) -> LeN n n' -> LeN (kv j n) (kv j n'))
         (Y : Nat -> Nat)
         (N I : Nat -> Nat)
         (iv-stab : (j n : Nat) -> LeN (N j) n -> Eq (iv j n) (I j))
         (hverd : (j : Nat) -> HPass (kv j))
         where

  ----------------------------------------------------------------------
  -- the block's trace and the verdicts, at r = 2
  ----------------------------------------------------------------------

  HGT : Nat -> Nat -> Nat
  HGT = hgt a iv ivr kv kv-mono Y N I iv-stab

  AVL : Nat -> Nat -> Nat
  AVL = avl a iv ivr kv kv-mono Y N I iv-stab

  STP : Nat -> Nat -> Nat
  STP = stp a iv ivr kv kv-mono Y N I iv-stab

  HGT-mono : (j : Nat) -> LeN (suc j) two -> Mono (\ m -> HGT m j)
  HGT-mono j lj = hgt-mono a iv ivr kv kv-mono Y N I iv-stab j lj

  STP-mono : (j : Nat) -> Mono (STP j)
  STP-mono j = stp-mono a iv ivr kv kv-mono Y N I iv-stab j

  Verd : Nat -> Set
  Verd = Verdict a iv ivr kv kv-mono Y N I iv-stab

  verd : (j : Nat) -> LeN (suc j) two -> Verd j
  verd = comp-verdict a iv ivr kv kv-mono Y N I iv-stab

  ----------------------------------------------------------------------
  -- THE AFFINE LAW FOR A COMPONENT PAST ITS THRESHOLD
  ----------------------------------------------------------------------

  D : Nat -> Nat
  D j = Dof a (iv j) (ivr j) (N j) (I j) (iv-stab j)

  affine-law : (j T : Nat) -> LeN (N j) (STP j T) ->
    (m : Nat) -> LeN T m -> Eq (HGT (suc m) j) (kv j (plus (D j) (AVL m (I j))))
  affine-law j T p m lm =
    Eq-cong (kv j)
      (affine a (iv j) (ivr j) (N j) (I j) (iv-stab j) (AVL m)
        (LeN-trans {N j} {STP j T} {STP j m} p (STP-mono j T m lm)))

  -- the step function a component past its threshold iterates
  phi : Nat -> Nat -> Nat
  phi j x = kv j (plus (D j) x)

  phi-mono : (j : Nat) -> Mono (phi j)
  phi-mono j x y le =
    kv-mono j (plus (D j) x) (plus (D j) y) (plus-mono (D j) (D j) x y (LeN-refl (D j)) le)

  ----------------------------------------------------------------------
  -- (H) FROM AN EVENTUALLY CONSTANT HEIGHT
  ----------------------------------------------------------------------

  ev-from : (j T : Nat) -> LeN (suc j) two ->
    ((m : Nat) -> LeN T m -> Eq (HGT (suc m) j) (HGT (suc T) j)) ->
    HPass (\ m -> HGT m j)
  ev-from j T lj h = hpass-evconst (\ m -> HGT m j) (HGT-mono j lj) (suc T) ev
    where
      ev : (n : Nat) -> LeN (suc T) n -> Eq (HGT n j) (HGT (suc T) j)
      ev zero    ()
      ev (suc m) ln = h m ln

  ----------------------------------------------------------------------
  -- (H) FROM A DETERMINISTIC ITERATION ALONG A SUBSEQUENCE
  --
  -- `u` is the component's height read along the subsequence `g` (g k = k + T
  -- for a self-reading component, k + 2k + T around a cross-cycle), and it
  -- satisfies a deterministic monotone recursion.  Then `IterF.it-pass` gives
  -- (H) for `u`, and `hpass-sub` lifts it to the whole sequence.
  ----------------------------------------------------------------------

  from-iter : (j : Nat) -> LeN (suc j) two ->
    (u g : Nat -> Nat) -> ((k : Nat) -> LeN k (g k)) ->
    ((k : Nat) -> Eq (u k) (HGT (g k) j)) ->
    (ph : Nat -> Nat) -> Mono ph ->
    ((k : Nat) -> Eq (u (suc k)) (ph (u k))) ->
    LeN (u zero) (u (suc zero)) ->
    HPass (\ m -> HGT m j)
  from-iter j lj u g gge ug ph mph rec start =
    hpass-sub (\ m -> HGT m j) (HGT-mono j lj) g gge
      (hpass-cong u (\ k -> HGT (g k) j) ug
        (hpass-cong it u (\ k -> Eq-sym (same k)) it-pass))
    where
      x0le : LeN (u zero) (ph (u zero))
      x0le = Eq-transport (\ z -> LeN (u zero) z) (rec zero) start

      open IterF ph mph (u zero) x0le

      same : (k : Nat) -> Eq (u k) (it k)
      same zero    = refl
      same (suc k) = Eq-trans (rec k) (Eq-cong ph (same k))

  ----------------------------------------------------------------------
  -- (H) FROM (H) OF THE TAIL
  --
  -- If from `T` on the component's height is `F` shifted by one, then (H) for
  -- `F` gives (H) for the height: monotony covers the finitely many earlier
  -- values without any case analysis.
  ----------------------------------------------------------------------

  from-tail : (j T : Nat) -> LeN (suc j) two -> (F : Nat -> Nat) -> Mono F ->
    ((m : Nat) -> LeN T m -> Eq (HGT (suc m) j) (F m)) -> HPass F ->
    HPass (\ m -> HGT m j)
  from-tail j T lj F mF eq hF K = route (hF K)
    where
      route :
        Or (Sigma Nat (\ s -> LeN (suc K) (F s))) ((s : Nat) -> LeN (F s) K) ->
        Or (Sigma Nat (\ s -> LeN (suc K) (HGT s j)))
           ((s : Nat) -> LeN (HGT s j) K)
      route (inl (mkSigma s big)) = inl (mkSigma (suc s') pass)
        where
          s' : Nat
          s' = maxN s T

          pass : LeN (suc K) (HGT (suc s') j)
          pass =
            Eq-transport (\ z -> LeN (suc K) z)
              (Eq-sym (eq s' (maxN-le-r s T)))
              (LeN-trans {suc K} {F s} {F s'} big (mF s s' (maxN-le-l s T)))
      route (inr bnd) = inr small
        where
          small : (n : Nat) -> LeN (HGT n j) K
          small n =
            LeN-trans {HGT n j} {HGT (suc (maxN n T)) j} {K}
              (HGT-mono j lj n (suc (maxN n T))
                (LeN-trans {n} {maxN n T} {suc (maxN n T)}
                  (maxN-le-l n T) (LeN-suc (maxN n T))))
              (Eq-transport (\ z -> LeN z K) (Eq-sym (eq (maxN n T) (maxN-le-r n T)))
                (bnd (maxN n T)))

  ----------------------------------------------------------------------
  -- WHERE A COMPONENT'S ULTIMATE DEMAND POINTS
  --
  -- `Stab j` -- the height is eventually constant, threshold known -- is the
  -- collecting case: a frozen verdict, and a component whose ultimate demand
  -- is a parameter, both give it.  `Self j` and `Cross j` are the two
  -- recursive shapes, each carrying the affine law it obeys.
  ----------------------------------------------------------------------

  Stab : Nat -> Set
  Stab j = Sigma Nat (\ T -> (m : Nat) -> LeN T m -> Eq (HGT (suc m) j) (HGT (suc T) j))

  Self : Nat -> Set
  Self j = Sigma Nat (\ T -> (m : Nat) -> LeN T m ->
             Eq (HGT (suc m) j) (phi j (HGT m j)))

  Cross : Nat -> Set
  Cross j = Sigma Nat (\ T -> (m : Nat) -> LeN T m ->
              Eq (HGT (suc m) j) (phi j (HGT m (oth j))))

  shape : (j : Nat) -> LeN (suc j) two -> Or (Stab j) (Or (Self j) (Cross j))
  shape j lj = route (verd j lj)
    where
      route : Verd j -> Or (Stab j) (Or (Self j) (Cross j))
      -- frozen: the height does not move at all
      route (inl (mkSigma T fz)) = inl (mkSigma T same)
        where
          same : (m : Nat) -> LeN T m -> Eq (HGT (suc m) j) (HGT (suc T) j)
          same m lm =
            Eq-trans (fst (fz (suc m) (LeN-trans {T} {m} {suc m} lm (LeN-suc m))))
                     (Eq-sym (fst (fz (suc T) (LeN-suc T))))
      -- past its threshold: the affine law, and then where I j points
      route (inr (mkSigma T p)) = point (LeN-dec (suc (I j)) two)
        where
          law : (m : Nat) -> LeN T m ->
            Eq (HGT (suc m) j) (kv j (plus (D j) (AVL m (I j))))
          law = affine-law j T p

          point : Dec (LeN (suc (I j)) two) -> Or (Stab j) (Or (Self j) (Cross j))
          -- a parameter: constant, so the height stops moving
          point (no nc) = inl (mkSigma T same)
            where
              same : (m : Nat) -> LeN T m -> Eq (HGT (suc m) j) (HGT (suc T) j)
              same m lm =
                Eq-trans (law m lm)
                  (Eq-trans
                    (Eq-cong (\ z -> kv j (plus (D j) z))
                      (av-param two a iv ivr kv kv-mono Y (I j) nc T m))
                    (Eq-sym (law T (LeN-refl T))))
          -- a component: itself, or the other one
          point (yes lc) = pick (EqNat-dec (I j) j)
            where
              rec : (m : Nat) -> LeN T m ->
                Eq (HGT (suc m) j) (kv j (plus (D j) (HGT m (I j))))
              rec m lm =
                Eq-trans (law m lm)
                  (Eq-cong (\ z -> kv j (plus (D j) z))
                    (av-rec two a iv ivr kv kv-mono Y (I j) lc m))

              pick : Dec (Eq (I j) j) -> Or (Stab j) (Or (Self j) (Cross j))
              pick (yes e) =
                inr (inl (mkSigma T
                  (\ m lm ->
                     Eq-transport (\ z -> Eq (HGT (suc m) j) (phi j (HGT m z))) e
                       (rec m lm))))
              pick (no ne) = other (EqNat-dec (I j) (oth j))
                where
                  other : Dec (Eq (I j) (oth j)) ->
                    Or (Stab j) (Or (Self j) (Cross j))
                  other (yes e) =
                    inr (inr (mkSigma T
                      (\ m lm ->
                         Eq-transport (\ z -> Eq (HGT (suc m) j) (phi j (HGT m z))) e
                           (rec m lm))))
                  other (no ne') = Empty-elim (ne (oth-uniq (I j) j lc lj ne'))

  ----------------------------------------------------------------------
  -- THE THREE SHAPES, ONE BY ONE
  ----------------------------------------------------------------------

  -- a frozen height
  pass-stab : (j : Nat) -> LeN (suc j) two -> Stab j -> HPass (\ m -> HGT m j)
  pass-stab j lj (mkSigma T same) = ev-from j T lj same

  -- a self-reading component: the one-coordinate iteration
  pass-self : (j : Nat) -> LeN (suc j) two -> Self j -> HPass (\ m -> HGT m j)
  pass-self j lj (mkSigma T sf) =
    from-iter j lj u g gge ug (phi j) (phi-mono j) rec start
    where
      g : Nat -> Nat
      g k = plus k T

      gge : (k : Nat) -> LeN k (g k)
      gge k = plus-ge-l k T

      u : Nat -> Nat
      u k = HGT (g k) j

      ug : (k : Nat) -> Eq (u k) (HGT (g k) j)
      ug k = refl

      rec : (k : Nat) -> Eq (u (suc k)) (phi j (u k))
      rec k = sf (plus k T) (plus-ge-r k T)

      start : LeN (u zero) (u (suc zero))
      start = HGT-mono j lj T (suc T) (LeN-suc T)

  ----------------------------------------------------------------------
  -- A CROSS-READING COMPONENT
  --
  -- Its height is `kv j (D j + w m)` past the threshold, where `w` is the
  -- OTHER component's height -- so (H) for the other one gives (H) for it
  -- (`hpass-comp2` + `from-tail`).  That is what handles a cross onto a
  -- component that is frozen or self-reading.
  ----------------------------------------------------------------------

  pass-cross-from : (j : Nat) -> LeN (suc j) two -> Cross j ->
    HPass (\ m -> HGT m (oth j)) -> HPass (\ m -> HGT m j)
  pass-cross-from j lj (mkSigma T cr) hw =
    from-tail j T lj F mF cr
      (hpass-comp2 (kv j) (\ m -> HGT m (oth j)) (kv-mono j)
        (HGT-mono (oth j) (oth-range j)) (hverd j) hw (D j))
    where
      F : Nat -> Nat
      F m = kv j (plus (D j) (HGT m (oth j)))

      mF : Mono F
      mF m m' le =
        phi-mono j (HGT m (oth j)) (HGT m' (oth j))
          (HGT-mono (oth j) (oth-range j) m m' le)

  ----------------------------------------------------------------------
  -- THE CROSS-CYCLE
  --
  -- Both components read each other for ever.  Composing the two affine laws
  -- around the cycle gives a deterministic monotone iteration of PERIOD 2 for
  -- each of them.
  ----------------------------------------------------------------------

  pass-cycle : (j : Nat) -> LeN (suc j) two -> Cross j -> Cross (oth j) ->
    HPass (\ m -> HGT m j)
  pass-cycle j lj (mkSigma T cr) (mkSigma T' cr') =
    from-iter j lj u g gge ug psi mpsi rec start
    where
      T2 : Nat
      T2 = maxN T T'

      lT : LeN T T2
      lT = maxN-le-l T T'

      lT' : LeN T' T2
      lT' = maxN-le-r T T'

      g : Nat -> Nat
      g k = plus (double k) T2

      gge : (k : Nat) -> LeN k (g k)
      gge k = LeN-trans {k} {double k} {plus (double k) T2}
                (double-ge k) (plus-ge-l (double k) T2)

      u : Nat -> Nat
      u k = HGT (g k) j

      ug : (k : Nat) -> Eq (u k) (HGT (g k) j)
      ug k = refl

      -- once around the cycle
      psi : Nat -> Nat
      psi x = phi j (phi (oth j) x)

      mpsi : Mono psi
      mpsi x y le =
        phi-mono j (phi (oth j) x) (phi (oth j) y) (phi-mono (oth j) x y le)

      rec : (k : Nat) -> Eq (u (suc k)) (psi (u k))
      rec k =
        Eq-trans (cr (suc m) (LeN-trans {T} {m} {suc m} lm (LeN-suc m)))
          (Eq-cong (phi j)
            (Eq-trans (cr' m lm')
              (Eq-cong (phi (oth j))
                (Eq-cong (\ z -> HGT m z) (oth-oth j lj)))))
        where
          m : Nat
          m = plus (double k) T2

          lm : LeN T m
          lm = LeN-trans {T} {T2} {m} lT (plus-ge-r (double k) T2)

          lm' : LeN T' m
          lm' = LeN-trans {T'} {T2} {m} lT' (plus-ge-r (double k) T2)

      start : LeN (u zero) (u (suc zero))
      start =
        HGT-mono j lj T2 (plus (double (suc zero)) T2)
          (plus-ge-r (double (suc zero)) T2)

  ----------------------------------------------------------------------
  -- (H) FOR BOTH COMPONENTS
  --
  -- One case analysis on the two shapes.  The only case needing both is the
  -- cross-cycle; a cross onto a frozen or self-reading component is settled by
  -- (H) for that component first.
  ----------------------------------------------------------------------

  hpass-blk : (j : Nat) -> LeN (suc j) two -> HPass (\ m -> HGT m j)
  hpass-blk j lj = route (shape j lj)
    where
      lc : LeN (suc (oth j)) two
      lc = oth-range j

      -- (H) for the other component, when it does not read this one
      other : Or (Stab (oth j)) (Or (Self (oth j)) (Cross (oth j))) ->
        Or (HPass (\ m -> HGT m (oth j))) (Cross (oth j))
      other (inl st)        = inl (pass-stab (oth j) lc st)
      other (inr (inl sf))  = inl (pass-self (oth j) lc sf)
      other (inr (inr crs)) = inr crs

      route : Or (Stab j) (Or (Self j) (Cross j)) -> HPass (\ m -> HGT m j)
      route (inl st)       = pass-stab j lj st
      route (inr (inl sf)) = pass-self j lj sf
      route (inr (inr cr)) = cross (other (shape (oth j) lc))
        where
          cross : Or (HPass (\ m -> HGT m (oth j))) (Cross (oth j)) ->
            HPass (\ m -> HGT m j)
          cross (inl hw)  = pass-cross-from j lj cr hw
          cross (inr crs) = pass-cycle j lj cr crs

  ----------------------------------------------------------------------
  -- THE MAIN PROPERTY OF THE BLOCK: (I) AND (H)
  --
  -- (I) is `MainBlk2.MPblock` -- the block's sequentiality index `q j` is
  -- eventually constant, needing only (I) of the step terms -- and (H) is
  -- `hpass-blk`.  Both are indexed by the block's DEPTH.
  ----------------------------------------------------------------------

  mp-blk : (j : Nat) -> LeN (suc j) two ->
    MP (q two a iv ivr kv kv-mono Y j) (\ m -> HGT m j)
  mp-blk j lj =
    mkSigma (MPblock a iv ivr kv kv-mono Y N I iv-stab j lj) (hpass-blk j lj)
