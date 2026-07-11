{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecInfSecond
--
-- The SECOND principal case of primitive recursion at the infinite first
-- argument (min1.pdf p.3-4): S^{k0}(bot) <= u_{k0}.  `f-reaches` gives a
-- region on which the recursion result reaches S^{k0}(bot); we reconcile
-- it with h's ultimate-obstination witness at Q = (S^w b, S^w b, Y) and
-- route to the appropriate region builder according to h's controlling
-- coordinate:
--
--   * h Case 1                    -> f Case 1  (prec-inf-Case1-region)
--   * h Case 2 at a Y-coordinate  -> f Case 2  (prec-inf-Case2-region)
--   * h Case 3 at coordinate 0    -> f Case 3 at coord 0 (Case3Depth)
--   * h Case 3 at coordinate 1    -> f Case 3 at coord 0 (PrecInfSub4),
--                                    or Case 1 if the base value is complete
--   * h Case 3 at a Y-coordinate  -> f Case 3 at that coord (Case3Y)
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecInfSecond where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.Meet using (joinF)
open import OBSTINATION.Mono using (evalF-mono)
open import OBSTINATION.JoinD using (getF-joinT)
open import OBSTINATION.Refine using (Below-length)
open import OBSTINATION.USeq using (uSeq)
open import OBSTINATION.PrecInf using (f-reaches ; prec-inf-Case1)
open import OBSTINATION.PrecInfReconcile
open import OBSTINATION.PrecInfExtract using (approx ; below-inf-fbot ; get-embedTup)
open import OBSTINATION.PrecInfCoord using (LeFTup-del ; LeFTup-length)
open import OBSTINATION.PrecInfSub4 using (prec-inf-Sub4)
open import OBSTINATION.PrecInfRegion
open import OBSTINATION.PrecInfRegion2 using (prec-inf-Case3Depth-region)
open import OBSTINATION.PrecFun using (RecData ; PF ; PF-mono)

------------------------------------------------------------------------
-- small helpers
------------------------------------------------------------------------

fbot-inj : {a b : Nat} -> Eq (fbot a) (fbot b) -> Eq a b
fbot-inj refl = refl

botD-inj : {a b : Nat} -> Eq (bot a) (bot b) -> Eq a b
botD-inj refl = refl

maxN-r-le : {j k : Nat} -> LeN k j -> Eq (maxN j k) j
maxN-r-le {zero}  {zero}  le = refl
maxN-r-le {suc j} {zero}  le = refl
maxN-r-le {zero}  {suc k} ()
maxN-r-le {suc j} {suc k} le = Eq-cong suc (maxN-r-le {j} {k} le)

embed-bot-inv : {x : FEl} {j : Nat} -> Eq (embed x) (bot j) -> Eq x (fbot j)
embed-bot-inv {fbot j'} e = Eq-cong fbot (botD-inj e)
embed-bot-inv {fcpl j'} ()

incfin-bot : (d : D) -> IncompleteFinite d -> Sigma Nat (\ j -> Eq d (bot j))
incfin-bot (bot j) _ = mkSigma j refl
incfin-bot (cpl j) ()
incfin-bot inf     ()

below-botD : {x : FEl} {j : Nat} -> LeD (embed x) (bot j) ->
  Sigma Nat (\ j' -> Pair (Eq x (fbot j')) (LeN j' j))
below-botD {fbot j'} {j} le = mkSigma j' (mkSigma refl le)
below-botD {fcpl j'} {j} ()

phiok-mono : (phi : Nat -> Nat) {k kc : Nat} -> LeN k kc -> PhiOK k phi -> PhiOK kc phi
phiok-mono phi {k} {kc} lk (inl cst) = inl cst'
  where cst' : ConstFrom kc phi
        cst' m lkcm = Eq-trans (cst m (LeN-trans {k} {kc} {m} lk lkcm)) (Eq-sym (cst kc lk))
phiok-mono phi {k} {kc} lk (inr sinc) = inr sinc'
  where sinc' : StrictIncFrom kc phi
        sinc' m lkcm = sinc m (LeN-trans {k} {kc} {m} lk lkcm)

module _ (rd : RecData) (Y : Tup) where
  open RecData rd

  private
    Q : Tup
    Q = cons inf (cons inf Y)

  second-principal : (uQ : UO (H) Q) (k0 : Nat)
    (eqk0 : Eq (getF (suc zero) (approx uQ)) (fbot k0))
    (le : LeD (bot k0) (uSeq rd Y k0)) ->
    UO (PF G H) (cons inf Y)
  second-principal uQ k0 eqk0 le = go uQ eqk0
    where
      fr = f-reaches rd Y k0 le
      n0r    = fst fr
      Y0r    = fst (snd fr)
      belY0r = fst (snd (snd fr))
      reachr = snd (snd (snd fr))
      lenY0r : Eq (length Y0r) (length Y)
      lenY0r = Below-length belY0r

      go : (u : UO (H) Q) -> Eq (getF (suc zero) (approx u)) (fbot k0) ->
           UO (PF G H) (cons inf Y)

      -- ================= h Case 1 =================
      go (uo1 (mkSigma nil (mkSigma bel _))) eqk = Empty-elim bel
      go (uo1 (mkSigma (cons b0 nil) (mkSigma bel _))) eqk = Empty-elim (snd bel)
      go (uo1 (mkSigma (cons b0 (cons b1 Yb)) (mkSigma bel (mkSigma m univ)))) eqk =
        prec-inf-Case1-region rd m (rN0 rec) k0 (rY0 rec) Y (rBel rec) (rReach rec) hgerm
        where
          belYb : Below Yb Y
          belYb = snd (snd bel)
          n0hE = below-inf-fbot zero (cons b0 (cons b1 Yb)) Q bel refl tt
          n0h  = fst n0hE
          eqb0 = snd n0hE
          rec = reconcile rd Y k0 n0h Yb n0r Y0r belYb belY0r reachr
          hgerm : (a r : FEl) (X : FTup) -> LeF (fbot (rN0 rec)) a -> LeD (bot k0) (embed r) ->
                  LeFTup (rY0 rec) X -> Eq (H (cons a (cons r X))) (fcpl m)
          hgerm a r X la lr lX = univ (cons a (cons r X))
            (mkSigma
              (Eq-transport (\ z -> LeD (embed z) (embed a)) (Eq-sym eqb0)
                (LeF-trans {fbot n0h} {fbot (rN0 rec)} {a} (rN0GeH rec) la))
              (mkSigma
                (Eq-transport (\ z -> LeD (embed z) (embed r)) (Eq-sym eqk) lr)
                (LeTup-trans {embedTup Yb} {embedTup (rY0 rec)} {embedTup X} (rGeH rec) lX)))

      -- ================= h Case 2 =================
      go (uo2 (mkSigma nil (mkSigma bel _))) eqk = Empty-elim bel
      go (uo2 (mkSigma (cons b0 nil) (mkSigma bel _))) eqk = Empty-elim (snd bel)
      go (uo2 (mkSigma (cons b0 (cons b1 Yb)) (mkSigma bel
        (mkSigma m (mkSigma zero (mkSigma _ (mkSigma () _))))))) eqk
      go (uo2 (mkSigma (cons b0 (cons b1 Yb)) (mkSigma bel
        (mkSigma m (mkSigma (suc zero) (mkSigma _ (mkSigma () _))))))) eqk
      go (uo2 (mkSigma (cons b0 (cons b1 Yb)) (mkSigma bel
        (mkSigma m (mkSigma (suc (suc c)) (mkSigma irange (mkSigma incompl (mkSigma eqA0i univ)))))))) eqk =
        prec-inf-Case2-region rd m (rN0 rec) k0 c (rY0 rec) Y (rBel rec)
          crange incompl cpin (rReach rec) hgerm
        where
          belYb : Below Yb Y
          belYb = snd (snd bel)
          lenYb : Eq (length Yb) (length Y)
          lenYb = Below-length belYb
          n0hE = below-inf-fbot zero (cons b0 (cons b1 Yb)) Q bel refl tt
          n0h  = fst n0hE
          eqb0 = snd n0hE
          rec = reconcile rd Y k0 n0h Yb n0r Y0r belYb belY0r reachr
          lenYb-Y0 : Eq (length Yb) (length (rY0 rec))
          lenYb-Y0 = LeFTup-length {Yb} {rY0 rec} (rGeH rec)
          lenYb-Y0r : Eq (length Yb) (length Y0r)
          lenYb-Y0r = Eq-trans lenYb (Eq-sym lenY0r)
          cYb : LeN (suc c) (length Yb)
          cYb = irange
          cY0r : LeN (suc c) (length Y0r)
          cY0r = Eq-transport (\ n -> LeN (suc c) n) lenYb-Y0r cYb
          crange : LeN (suc c) (length (rY0 rec))
          crange = Eq-transport (\ n -> LeN (suc c) n) lenYb-Y0 cYb
          jE = incfin-bot (get c Y) incompl
          j  = fst jE
          eqcY : Eq (get c Y) (bot j)
          eqcY = snd jE
          getYb-j : Eq (getF c Yb) (fbot j)
          getYb-j = embed-bot-inv (Eq-trans eqA0i eqcY)
          getY0r-le : LeD (embed (getF c Y0r)) (bot j)
          getY0r-le = Eq-transport (\ z -> LeD (embed (getF c Y0r)) z) eqcY
            (Eq-transport (\ z -> LeD z (get c Y)) (get-embedTup c Y0r cY0r)
              (LeTup-get c {embedTup Y0r} {Y} belY0r))
          getY0r-jE = below-botD {getF c Y0r} {j} getY0r-le
          j'   = fst getY0r-jE
          getY0r-j : Eq (getF c Y0r) (fbot j')
          getY0r-j = fst (snd getY0r-jE)
          j'lej : LeN j' j
          j'lej = snd (snd getY0r-jE)
          getY0-j : Eq (getF c (rY0 rec)) (fbot j)
          getY0-j =
            Eq-trans (getF-joinT c Yb Y0r lenYb-Y0r)
              (Eq-trans (Eq-cong (\ z -> joinF z (getF c Y0r)) getYb-j)
                (Eq-trans (Eq-cong (\ z -> joinF (fbot j) z) getY0r-j)
                  (Eq-cong fbot (maxN-r-le {j} {j'} j'lej))))
          cpin : Eq (embed (getF c (rY0 rec))) (get c Y)
          cpin = Eq-trans (Eq-cong embed getY0-j) (Eq-sym eqcY)
          hgerm : (a r : FEl) (X : FTup) -> LeF (fbot (rN0 rec)) a -> LeD (bot k0) (embed r) ->
                  LeFTup (rY0 rec) X -> Eq (getF c X) (getF c (rY0 rec)) ->
                  Eq (H (cons a (cons r X))) (fbot m)
          hgerm a r X la lr lX pinX =
            univ (cons a (cons r X))
              (Eq-cong (\ n -> suc (suc n)) (Eq-trans (Eq-sym (LeFTup-length {rY0 rec} {X} lX)) (Eq-sym lenYb-Y0)))
              (Eq-trans pinX (Eq-trans getY0-j (Eq-sym getYb-j)))
              (mkSigma b0a (mkSigma b1r (LeFTup-del c {Yb} {X} YbX)))
            where
              b0a = Eq-transport (\ z -> LeD (embed z) (embed a)) (Eq-sym eqb0)
                      (LeF-trans {fbot n0h} {fbot (rN0 rec)} {a} (rN0GeH rec) la)
              b1r = Eq-transport (\ z -> LeD (embed z) (embed r)) (Eq-sym eqk) lr
              YbX : LeFTup Yb X
              YbX = LeTup-trans {embedTup Yb} {embedTup (rY0 rec)} {embedTup X} (rGeH rec) lX

      -- ================= h Case 3 =================
      go (uo3 (mkSigma nil (mkSigma bel _))) eqk = Empty-elim bel
      go (uo3 (mkSigma (cons b0 nil) (mkSigma bel _))) eqk = Empty-elim (snd bel)
      -- ----- coordinate 0 : Case 3 at the recursion depth -----
      go (uo3 (mkSigma (cons b0 (cons b1 Yb)) (mkSigma bel
        (mkSigma zero (mkSigma eqinf (mkSigma k (mkSigma eqA0 (mkSigma phi (mkSigma phiok univ)))))))) ) eqk =
        prec-inf-Case3Depth-region rd phi (rN0 rec) k0 k (rY0 rec) Y (rBel rec) phiok
          (rReach rec) hgerm
        where
          belYb : Below Yb Y
          belYb = snd (snd bel)
          lenYb : Eq (length Yb) (length Y)
          lenYb = Below-length belYb
          rec = reconcile rd Y k0 k Yb n0r Y0r belYb belY0r reachr
          lenYb-Y0 : Eq (length Yb) (length (rY0 rec))
          lenYb-Y0 = LeFTup-length {Yb} {rY0 rec} (rGeH rec)
          hgerm : (n : Nat) (r : FEl) (X : FTup) -> LeN k n -> LeD (bot k0) (embed r) ->
                  LeFTup (rY0 rec) X -> Eq (H (cons (fbot n) (cons r X))) (fbot (phi n))
          hgerm n r X kn lr lX =
            univ (cons (fbot n) (cons r X)) n
              (Eq-cong (\ q -> suc (suc q)) (Eq-trans (Eq-sym (LeFTup-length {rY0 rec} {X} lX)) (Eq-sym lenYb-Y0)))
              kn refl
              (mkSigma b1r YbX)
            where
              b1r = Eq-transport (\ z -> LeD (embed z) (embed r)) (Eq-sym eqk) lr
              YbX : LeFTup Yb X
              YbX = LeTup-trans {embedTup Yb} {embedTup (rY0 rec)} {embedTup X} (rGeH rec) lX
      -- ----- coordinate 1 : Case 3 at the recursion result -----
      go (uo3 (mkSigma (cons b0 (cons b1 Yb)) (mkSigma bel
        (mkSigma (suc zero) (mkSigma eqinf (mkSigma k (mkSigma eqA0 (mkSigma phi (mkSigma phiok univ)))))))) ) eqk =
        classify (PF G H (cons (fbot (rN0 rec)) (rY0 rec))) refl (rFval rec)
        where
          belYb : Below Yb Y
          belYb = snd (snd bel)
          lenYb : Eq (length Yb) (length Y)
          lenYb = Below-length belYb
          n0hE = below-inf-fbot zero (cons b0 (cons b1 Yb)) Q bel refl tt
          n0h  = fst n0hE
          eqb0 = snd n0hE
          rec = reconcile rd Y k0 n0h Yb n0r Y0r belYb belY0r reachr
          lenYb-Y0 : Eq (length Yb) (length (rY0 rec))
          lenYb-Y0 = LeFTup-length {Yb} {rY0 rec} (rGeH rec)
          kEq : Eq k0 k
          kEq = fbot-inj (Eq-trans (Eq-sym eqk) eqA0)
          -- phi's threshold as k0
          phiokK0 : PhiOK k0 phi
          phiokK0 = Eq-transport (\ z -> PhiOK z phi) (Eq-sym kEq) phiok
          -- the germ over the reconciled region (coordinate 1 always incomplete)
          germ : (n j : Nat) (X : FTup) -> LeN (rN0 rec) n -> LeN k0 j -> LeFTup (rY0 rec) X ->
                 Eq (H (cons (fbot n) (cons (fbot j) X))) (fbot (phi j))
          germ n j X ln lj lX =
            univ (cons (fbot n) (cons (fbot j) X)) j
              (Eq-cong (\ q -> suc (suc q)) (Eq-trans (Eq-sym (LeFTup-length {rY0 rec} {X} lX)) (Eq-sym lenYb-Y0)))
              (Eq-transport (\ z -> LeN z j) kEq lj)
              refl
              (mkSigma b0a YbX)
            where
              b0a = Eq-transport (\ z -> LeD (embed z) (bot n)) (Eq-sym eqb0)
                      (LeF-trans {fbot n0h} {fbot (rN0 rec)} {fbot n} (rN0GeH rec) ln)
              YbX : LeFTup Yb X
              YbX = LeTup-trans {embedTup Yb} {embedTup (rY0 rec)} {embedTup X} (rGeH rec) lX
          classify : (v : FEl) -> Eq (PF G H (cons (fbot (rN0 rec)) (rY0 rec))) v ->
                     LeD (bot k0) (embed v) -> UO (PF G H) (cons inf Y)
          classify (fcpl p) veq vge =
            prec-inf-Case1 rd Y (rN0 rec) (rY0 rec) p (rBel rec) veq
          classify (fbot N) veq vge = decidePhi phiokK0
            where
              leKN : LeN k0 N
              leKN = vge
              decidePhi : PhiOK k0 phi -> UO (PF G H) (cons inf Y)
              decidePhi (inr sinc) =
                prec-inf-Sub4 rd (rN0 rec) k0 N phi (rY0 rec) leKN veq (inr sinc) germ Y (rBel rec)
              decidePhi (inl cst) =
                prec-inf-Sub4 rd (suc (rN0 rec)) k0 (phi N) phi (rY0 rec) leKN' Neq' (inl fixEq) germ' Y (rBel rec)
                where
                  -- f(S^{n0+1}b, Y0) = h(S^{n0}b, S^N b, Y0) = fbot (phi N)
                  Neq' : Eq (PF G H (cons (fbot (suc (rN0 rec))) (rY0 rec))) (fbot (phi N))
                  Neq' = Eq-trans
                           (Eq-cong (\ z -> H (cons (fbot (rN0 rec)) (cons z (rY0 rec)))) veq)
                           (germ (rN0 rec) N (rY0 rec) (LeN-refl (rN0 rec)) leKN (LeFTup-refl (rY0 rec)))
                  -- N <= phi N by monotonicity of f
                  leN-phiN : LeN N (phi N)
                  leN-phiN =
                    Eq-transport (\ z -> LeD (bot N) z) (Eq-cong embed Neq')
                      (Eq-transport (\ z -> LeD z (embed (PF G H (cons (fbot (suc (rN0 rec))) (rY0 rec)))))
                        (Eq-cong embed veq)
                        (PF-mono G H monoG monoH {cons (fbot (rN0 rec)) (rY0 rec)} {cons (fbot (suc (rN0 rec))) (rY0 rec)}
                          (mkSigma (LeN-suc (rN0 rec)) (LeFTup-refl (rY0 rec)))))
                  leKN' : LeN k0 (phi N)
                  leKN' = LeN-trans {k0} {N} {phi N} leKN leN-phiN
                  -- phi N is a fixpoint of phi
                  fixEq : Eq (phi N) (phi (phi N))
                  fixEq = Eq-sym (Eq-trans (cst (phi N) leKN') (Eq-sym (cst N leKN)))
                  germ' : (n j : Nat) (X : FTup) -> LeN (suc (rN0 rec)) n -> LeN k0 j -> LeFTup (rY0 rec) X ->
                          Eq (H (cons (fbot n) (cons (fbot j) X))) (fbot (phi j))
                  germ' n j X ln lj lX =
                    germ n j X (LeN-trans {rN0 rec} {suc (rN0 rec)} {n} (LeN-suc (rN0 rec)) ln) lj lX
      -- ----- coordinate >= 2 : Case 3 at a Y-coordinate -----
      go (uo3 (mkSigma (cons b0 (cons b1 Yb)) (mkSigma bel
        (mkSigma (suc (suc c)) (mkSigma eqinf (mkSigma k (mkSigma eqA0 (mkSigma phi (mkSigma phiok univ)))))))) ) eqk =
        prec-inf-Case3Y-region rd phi (rN0 rec) k0 kc c (rY0 rec) Y (rBel rec)
          eqinf getY0-kc phiokKc (rReach rec) hgerm
        where
          belYb : Below Yb Y
          belYb = snd (snd bel)
          lenYb : Eq (length Yb) (length Y)
          lenYb = Below-length belYb
          n0hE = below-inf-fbot zero (cons b0 (cons b1 Yb)) Q bel refl tt
          n0h  = fst n0hE
          eqb0 = snd n0hE
          rec = reconcile rd Y k0 n0h Yb n0r Y0r belYb belY0r reachr
          lenYb-Y0 : Eq (length Yb) (length (rY0 rec))
          lenYb-Y0 = LeFTup-length {Yb} {rY0 rec} (rGeH rec)
          lenYb-Y0r : Eq (length Yb) (length Y0r)
          lenYb-Y0r = Eq-trans lenYb (Eq-sym lenY0r)
          cYb : LeN (suc c) (length Yb)
          cYb = irange-c
            where irange-c : LeN (suc c) (length Yb)
                  irange-c = get-inf-range
                    where -- get c Y = inf, so c is in range of Y = range of Yb
                      get-inf-range : LeN (suc c) (length Yb)
                      get-inf-range = Eq-transport (\ n -> LeN (suc c) n) (Eq-sym lenYb) (rng c Y eqinf)
                        where rng : (i : Nat) (A : Tup) -> Eq (get i A) inf -> LeN (suc i) (length A)
                              rng zero    (cons _ _)  e = tt
                              rng (suc i) (cons _ xs) e = rng i xs e
                              rng i       nil         ()
          -- getF c Yb = fbot k
          getYb-k : Eq (getF c Yb) (fbot k)
          getYb-k = eqA0
          -- getF c Y0r : any fbot below inf
          cY0r : LeN (suc c) (length Y0r)
          cY0r = Eq-transport (\ n -> LeN (suc c) n) lenYb-Y0r cYb
          getY0r-le : LeD (embed (getF c Y0r)) inf
          getY0r-le = Eq-transport (\ z -> LeD z inf) (get-embedTup c Y0r cY0r)
            (Eq-transport (\ z -> LeD (get c (embedTup Y0r)) z) eqinf
              (LeTup-get c {embedTup Y0r} {Y} belY0r))
          getY0r-fE = below-inf-to-fbot (getF c Y0r) getY0r-le
            where below-inf-to-fbot : (x : FEl) -> LeD (embed x) inf -> Sigma Nat (\ q -> Eq x (fbot q))
                  below-inf-to-fbot (fbot q) _ = mkSigma q refl
                  below-inf-to-fbot (fcpl q) ()
          k'  = fst getY0r-fE
          getY0r-k' : Eq (getF c Y0r) (fbot k')
          getY0r-k' = snd getY0r-fE
          -- getF c Y0 = fbot (max k k') =: fbot kc
          kc : Nat
          kc = maxN k k'
          getY0-kc : Eq (getF c (rY0 rec)) (fbot kc)
          getY0-kc =
            Eq-trans (getF-joinT c Yb Y0r lenYb-Y0r)
              (Eq-trans (Eq-cong (\ z -> joinF z (getF c Y0r)) getYb-k)
                (Eq-cong (\ z -> joinF (fbot k) z) getY0r-k'))
          k-le-kc : LeN k kc
          k-le-kc = maxN-le-l k k'
          phiokKc : PhiOK kc phi
          phiokKc = phiok-mono phi k-le-kc phiok
          hgerm : (a r : FEl) (X : FTup) (p : Nat) -> LeF (fbot (rN0 rec)) a -> LeD (bot k0) (embed r) ->
                  LeFTup (rY0 rec) X -> LeN kc p -> Eq (getF c X) (fbot p) ->
                  Eq (H (cons a (cons r X))) (fbot (phi p))
          hgerm a r X p la lr lX kcp coordX =
            univ (cons a (cons r X)) p
              (Eq-cong (\ q -> suc (suc q)) (Eq-trans (Eq-sym (LeFTup-length {rY0 rec} {X} lX)) (Eq-sym lenYb-Y0)))
              (LeN-trans {k} {kc} {p} k-le-kc kcp)
              coordX
              (mkSigma b0a (mkSigma b1r (LeFTup-del c {Yb} {X} YbX)))
            where
              b0a = Eq-transport (\ z -> LeD (embed z) (embed a)) (Eq-sym eqb0)
                      (LeF-trans {fbot n0h} {fbot (rN0 rec)} {a} (rN0GeH rec) la)
              b1r = Eq-transport (\ z -> LeD (embed z) (embed r)) (Eq-sym eqk) lr
              YbX : LeFTup Yb X
              YbX = LeTup-trans {embedTup Yb} {embedTup (rY0 rec)} {embedTup X} (rGeH rec) lX
