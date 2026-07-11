{-# OPTIONS --safe --without-K --exact-split #-}

------------------------------------------------------------------------
-- OBSTINATION.PrecInfFirst
--
-- The FIRST principal case of primitive recursion at the infinite first
-- argument (min1.pdf p.3): NOT (S^{k0}(bot) <= u_{k0}).  The Kleene
-- sequence has a FINITE limit; `finite-stab` exhibits a stabilisation
-- point with value  embed w.
--
--   * w = S^p(0) complete  -> Case 1 (prec-inf-complete).
--   * w = S^{l0}(bot)      -> the limit is realised at a finite stage
--     (realise-limit); re-dispatch h's UO at R = (S^w b, S^{l0} b, Y),
--     with the recursion result reaching S^{l0}(bot) on the region (mono
--     + realise-limit).  Non-coordinate-1 controllers route to the same
--     region builders as the second principal case; the coordinate-1
--     controller (h Case 2 pinned to S^{l0} b) routes to
--     prec-inf-const-coord1 -- whose value equals l0 because the
--     stabilised extension value  uoValue (uoh R) = S^{l0}(bot).
--
-- No postulates, no holes, no TERMINATING pragma.
------------------------------------------------------------------------

module OBSTINATION.PrecInfFirst where

open import OBSTINATION.Prelude
open import OBSTINATION.Domain
open import OBSTINATION.Tuples
open import OBSTINATION.PR
open import OBSTINATION.Property
open import OBSTINATION.Meet using (joinF ; joinT ; join-ubT-l ; join-ubT-r)
open import OBSTINATION.Mono using (evalF-mono)
open import OBSTINATION.JoinD using (getF-joinT ; BndT-from-Below ; Below-joinT)
open import OBSTINATION.Refine using (Below-length)
open import OBSTINATION.USeq using (uSeq ; uSeq-stab)
open import OBSTINATION.PrecInf using (realise-limit ; prec-inf-complete ; f-le-uSeq)
open import OBSTINATION.PrecInfReconcile
open import OBSTINATION.PrecInfExtract using (below-inf-fbot ; get-embedTup)
open import OBSTINATION.PrecInfCoord using (LeFTup-del ; LeFTup-length)
open import OBSTINATION.PrecInfRegion
open import OBSTINATION.PrecInfRegion2 using (prec-inf-Case3Depth-region)
open import OBSTINATION.PrecInfConst1 using (prec-inf-const-coord1)
open import OBSTINATION.PrecInfSecond using
  (fbot-inj ; botD-inj ; maxN-r-le ; embed-bot-inv ; incfin-bot ; below-botD ; phiok-mono)
open import OBSTINATION.PrecFun using (RecData ; PF ; PF-mono)

module _ (rd : RecData) (Y : Tup) where
  open RecData rd

  first-principal : (k0 : Nat) -> Not (LeD (bot k0) (uSeq rd Y k0)) ->
    UO (PF G H) (cons inf Y)
  first-principal k0 nle = dispW (finiteStab k0 nle)
    where
      finiteStab : (kk : Nat) -> Not (LeD (bot kk) (uSeq rd Y kk)) ->
        Sigma Nat (\ k -> Pair (Eq (uSeq rd Y k) (uSeq rd Y (suc k)))
                               (Sigma FEl (\ w -> Eq (uSeq rd Y k) (embed w))))
      finiteStab = OBSTINATION.PrecInfExtract.finite-stab rd Y

      dispW : Sigma Nat (\ k -> Pair (Eq (uSeq rd Y k) (uSeq rd Y (suc k)))
                                     (Sigma FEl (\ w -> Eq (uSeq rd Y k) (embed w)))) ->
              UO (PF G H) (cons inf Y)
      dispW (mkSigma k (mkSigma e (mkSigma (fcpl p) ew))) =
        prec-inf-complete rd Y k e p ew
      dispW (mkSigma k (mkSigma e (mkSigma (fbot l0) ew))) = goR (uoh R) uval-R
        where
          R : Tup
          R = cons inf (cons (bot l0) Y)
          rl = realise-limit rd Y k e (fbot l0) ew
          rn     = fst rl
          Y1     = fst (snd rl)
          belY1  = fst (snd (snd rl))
          realise-eq : Eq (PF G H (cons (fbot rn) Y1)) (fbot l0)
          realise-eq = snd (snd (snd rl))

          point-eq : Eq (cons inf (cons (uSeq rd Y k) Y)) R
          point-eq = Eq-cong (\ z -> cons inf (cons z Y)) ew
          uval-R : Eq (uoValue (uoh R)) (bot l0)
          uval-R = Eq-trans (Eq-sym (Eq-cong (\ pt -> uoValue (uoh pt)) point-eq))
                     (Eq-trans (Eq-sym e) ew)

          reachAt : (kk : Nat) -> LeN kk l0 -> (a : FEl) (X : FTup) ->
                    LeF (fbot rn) a -> LeFTup Y1 X ->
                    LeD (bot kk) (embed (PF G H (cons a X)))
          reachAt kk kkl0 a X la lX =
            LeD-trans {bot kk} {bot l0} {embed (PF G H (cons a X))} kkl0
              (LeD-trans {bot l0} {embed (PF G H (cons (fbot rn) Y1))}
                         {embed (PF G H (cons a X))}
                (Eq-transport (\ z -> LeD (bot l0) z) (Eq-sym (Eq-cong embed realise-eq)) (LeN-refl l0))
                (PF-mono G H monoG monoH {cons (fbot rn) Y1} {cons a X} (mkSigma la lX)))

          bridge : (n : Nat) (X' : FTup) -> LeN k n -> Below X' Y ->
                   LeD (embed (PF G H (cons (fbot n) X'))) (bot l0)
          bridge n X' kn belX' =
            Eq-transport (\ z -> LeD (embed (PF G H (cons (fbot n) X'))) z)
              (Eq-trans (Eq-sym (uSeq-stab rd Y k e n kn)) ew)
              (f-le-uSeq rd Y n X' belX')

          goR : (u : UO (H) R) -> Eq (uoValue u) (bot l0) ->
                UO (PF G H) (cons inf Y)

          -- ============ h Case 1 ============
          goR (uo1 (mkSigma nil (mkSigma bel _))) uval = Empty-elim bel
          goR (uo1 (mkSigma (cons b0 nil) (mkSigma bel _))) uval = Empty-elim (snd bel)
          goR (uo1 (mkSigma (cons b0 (cons b1 Yb)) (mkSigma bel (mkSigma m univ)))) uval =
            prec-inf-Case1-region rd m (rN0 rec) k0R (rY0 rec) Y (rBel rec) (rReach rec) hgerm
            where
              belYb = snd (snd bel)
              n0hE = below-inf-fbot zero (cons b0 (cons b1 Yb)) R bel refl tt
              n0h = fst n0hE ; eqb0 = snd n0hE
              k0RE = below-botD {b1} {l0} (fst (snd bel))
              k0R = fst k0RE ; eqb1 = fst (snd k0RE) ; k0Rl0 = snd (snd k0RE)
              rec = reconcile rd Y k0R n0h Yb rn Y1 belYb belY1 (reachAt k0R k0Rl0)
              hgerm : (a r : FEl) (X : FTup) -> LeF (fbot (rN0 rec)) a -> LeD (bot k0R) (embed r) ->
                      LeFTup (rY0 rec) X -> Eq (H (cons a (cons r X))) (fcpl m)
              hgerm a r X la lr lX = univ (cons a (cons r X))
                (mkSigma
                  (Eq-transport (\ z -> LeD (embed z) (embed a)) (Eq-sym eqb0)
                    (LeF-trans {fbot n0h} {fbot (rN0 rec)} {a} (rN0GeH rec) la))
                  (mkSigma
                    (Eq-transport (\ z -> LeD (embed z) (embed r)) (Eq-sym eqb1) lr)
                    (LeTup-trans {embedTup Yb} {embedTup (rY0 rec)} {embedTup X} (rGeH rec) lX)))

          -- ============ h Case 2 ============
          goR (uo2 (mkSigma nil (mkSigma bel _))) uval = Empty-elim bel
          goR (uo2 (mkSigma (cons b0 nil) (mkSigma bel _))) uval = Empty-elim (snd bel)
          goR (uo2 (mkSigma (cons b0 (cons b1 Yb)) (mkSigma bel
            (mkSigma m (mkSigma zero (mkSigma _ (mkSigma () _))))))) uval
          -- coordinate 1: h pins the recursion result to S^{l0}(bot)
          goR (uo2 (mkSigma (cons b0 (cons b1 Yb)) (mkSigma bel
            (mkSigma m (mkSigma (suc zero) (mkSigma _ (mkSigma _ (mkSigma eqA0i univ)))))))) uval =
            prec-inf-const-coord1 rd n0' l0 Y0' Neq germL Y belY0'
            where
              belYb = snd (snd bel)
              lenYb = Below-length belYb
              n0hE = below-inf-fbot zero (cons b0 (cons b1 Yb)) R bel refl tt
              n0h = fst n0hE ; eqb0 = snd n0hE
              -- Case 2 at coord1 forces b1 = fbot l0, and m = l0 (stabilised value)
              b1-l0 : Eq b1 (fbot l0)
              b1-l0 = embed-bot-inv eqA0i
              m-l0 : Eq m l0
              m-l0 = botD-inj uval
              bnd = BndT-from-Below belYb belY1
              Y0' = joinT Yb Y1
              belY0' : Below Y0' Y
              belY0' = Below-joinT belYb belY1
              YbY0' : LeFTup Yb Y0'
              YbY0' = join-ubT-l bnd
              Y1Y0' : LeFTup Y1 Y0'
              Y1Y0' = join-ubT-r bnd
              lenYb-Y0' : Eq (length Yb) (length Y0')
              lenYb-Y0' = LeFTup-length {Yb} {Y0'} YbY0'
              n0' = maxN (maxN n0h rn) k
              n0h-n0' : LeN n0h n0'
              n0h-n0' = LeN-trans {n0h} {maxN n0h rn} {n0'} (maxN-le-l n0h rn) (maxN-le-l (maxN n0h rn) k)
              rn-n0' : LeN rn n0'
              rn-n0' = LeN-trans {rn} {maxN n0h rn} {n0'} (maxN-le-r n0h rn) (maxN-le-l (maxN n0h rn) k)
              k-n0' : LeN k n0'
              k-n0' = maxN-le-r (maxN n0h rn) k
              -- germL : h(S^n b, S^{l0} b, X) = S^{l0} b  on the region
              germL : (n : Nat) (X : FTup) -> LeN n0' n -> LeFTup Y0' X ->
                      Eq (H (cons (fbot n) (cons (fbot l0) X))) (fbot l0)
              germL n X n0n lX =
                Eq-transport (\ z -> Eq (H (cons (fbot n) (cons (fbot l0) X))) (fbot z)) m-l0
                  (univ (cons (fbot n) (cons (fbot l0) X))
                    (Eq-cong (\ q -> suc (suc q))
                      (Eq-trans (Eq-sym (LeFTup-length {Y0'} {X} lX)) (Eq-sym lenYb-Y0')))
                    (Eq-sym b1-l0)
                    (mkSigma b0n YbX))
                where
                  b0n = Eq-transport (\ z -> LeD (embed z) (bot n)) (Eq-sym eqb0)
                          (LeF-trans {fbot n0h} {fbot n0'} {fbot n} n0h-n0' n0n)
                  YbX : LeFTup Yb X
                  YbX = LeTup-trans {embedTup Yb} {embedTup Y0'} {embedTup X} YbY0' lX
              -- Neq : f(S^{n0'} b, Y0') = S^{l0}(bot)  (squeeze)
              lower : LeD (bot l0) (embed (PF G H (cons (fbot n0') Y0')))
              lower = reachAt l0 (LeN-refl l0) (fbot n0') Y0' rn-n0' Y1Y0'
              upper : LeD (embed (PF G H (cons (fbot n0') Y0'))) (bot l0)
              upper = bridge n0' Y0' k-n0' belY0'
              Neq : Eq (PF G H (cons (fbot n0') Y0')) (fbot l0)
              Neq = embed-bot-inv (LeD-antisym
                      {embed (PF G H (cons (fbot n0') Y0'))} {bot l0} upper lower)
          -- coordinate >= 2: pinned Y-coordinate (incomplete finite)
          goR (uo2 (mkSigma (cons b0 (cons b1 Yb)) (mkSigma bel
            (mkSigma m (mkSigma (suc (suc c)) (mkSigma irange (mkSigma incompl (mkSigma eqA0i univ)))))))) uval =
            prec-inf-Case2-region rd m (rN0 rec) k0R c (rY0 rec) Y (rBel rec)
              crange incompl cpin (rReach rec) hgerm
            where
              belYb = snd (snd bel)
              lenYb = Below-length belYb
              n0hE = below-inf-fbot zero (cons b0 (cons b1 Yb)) R bel refl tt
              n0h = fst n0hE ; eqb0 = snd n0hE
              k0RE = below-botD {b1} {l0} (fst (snd bel))
              k0R = fst k0RE ; eqb1 = fst (snd k0RE) ; k0Rl0 = snd (snd k0RE)
              rec = reconcile rd Y k0R n0h Yb rn Y1 belYb belY1 (reachAt k0R k0Rl0)
              lenYb-Y0 = LeFTup-length {Yb} {rY0 rec} (rGeH rec)
              lenYb-Y0r : Eq (length Yb) (length Y1)
              lenYb-Y0r = Eq-trans lenYb (Eq-sym (Below-length belY1))
              cYb : LeN (suc c) (length Yb)
              cYb = irange
              cY0r : LeN (suc c) (length Y1)
              cY0r = Eq-transport (\ n -> LeN (suc c) n) lenYb-Y0r cYb
              crange : LeN (suc c) (length (rY0 rec))
              crange = Eq-transport (\ n -> LeN (suc c) n) lenYb-Y0 cYb
              jE = incfin-bot (get c Y) incompl
              j = fst jE ; eqcY = snd jE
              getYb-j : Eq (getF c Yb) (fbot j)
              getYb-j = embed-bot-inv (Eq-trans eqA0i eqcY)
              getY0r-le : LeD (embed (getF c Y1)) (bot j)
              getY0r-le = Eq-transport (\ z -> LeD (embed (getF c Y1)) z) eqcY
                (Eq-transport (\ z -> LeD z (get c Y)) (get-embedTup c Y1 cY0r)
                  (LeTup-get c {embedTup Y1} {Y} belY1))
              getY0r-jE = below-botD {getF c Y1} {j} getY0r-le
              j' = fst getY0r-jE ; getY0r-j = fst (snd getY0r-jE) ; j'lej = snd (snd getY0r-jE)
              getY0-j : Eq (getF c (rY0 rec)) (fbot j)
              getY0-j =
                Eq-trans (getF-joinT c Yb Y1 lenYb-Y0r)
                  (Eq-trans (Eq-cong (\ z -> joinF z (getF c Y1)) getYb-j)
                    (Eq-trans (Eq-cong (\ z -> joinF (fbot j) z) getY0r-j)
                      (Eq-cong fbot (maxN-r-le {j} {j'} j'lej))))
              cpin : Eq (embed (getF c (rY0 rec))) (get c Y)
              cpin = Eq-trans (Eq-cong embed getY0-j) (Eq-sym eqcY)
              hgerm : (a r : FEl) (X : FTup) -> LeF (fbot (rN0 rec)) a -> LeD (bot k0R) (embed r) ->
                      LeFTup (rY0 rec) X -> Eq (getF c X) (getF c (rY0 rec)) ->
                      Eq (H (cons a (cons r X))) (fbot m)
              hgerm a r X la lr lX pinX =
                univ (cons a (cons r X))
                  (Eq-cong (\ q -> suc (suc q))
                    (Eq-trans (Eq-sym (LeFTup-length {rY0 rec} {X} lX)) (Eq-sym lenYb-Y0)))
                  (Eq-trans pinX (Eq-trans getY0-j (Eq-sym getYb-j)))
                  (mkSigma b0a (mkSigma b1r (LeFTup-del c {Yb} {X} YbX)))
                where
                  b0a = Eq-transport (\ z -> LeD (embed z) (embed a)) (Eq-sym eqb0)
                          (LeF-trans {fbot n0h} {fbot (rN0 rec)} {a} (rN0GeH rec) la)
                  b1r = Eq-transport (\ z -> LeD (embed z) (embed r)) (Eq-sym eqb1) lr
                  YbX : LeFTup Yb X
                  YbX = LeTup-trans {embedTup Yb} {embedTup (rY0 rec)} {embedTup X} (rGeH rec) lX

          -- ============ h Case 3 ============
          goR (uo3 (mkSigma nil (mkSigma bel _))) uval = Empty-elim bel
          goR (uo3 (mkSigma (cons b0 nil) (mkSigma bel _))) uval = Empty-elim (snd bel)
          -- coordinate 0: the recursion depth
          goR (uo3 (mkSigma (cons b0 (cons b1 Yb)) (mkSigma bel
            (mkSigma zero (mkSigma eqinf (mkSigma kk (mkSigma eqA0 (mkSigma phi (mkSigma phiok univ)))))))) ) uval =
            prec-inf-Case3Depth-region rd phi (rN0 rec) k0R kk (rY0 rec) Y (rBel rec) phiok
              (rReach rec) hgerm
            where
              belYb = snd (snd bel)
              lenYb = Below-length belYb
              k0RE = below-botD {b1} {l0} (fst (snd bel))
              k0R = fst k0RE ; eqb1 = fst (snd k0RE) ; k0Rl0 = snd (snd k0RE)
              rec = reconcile rd Y k0R kk Yb rn Y1 belYb belY1 (reachAt k0R k0Rl0)
              lenYb-Y0 = LeFTup-length {Yb} {rY0 rec} (rGeH rec)
              hgerm : (n : Nat) (r : FEl) (X : FTup) -> LeN kk n -> LeD (bot k0R) (embed r) ->
                      LeFTup (rY0 rec) X -> Eq (H (cons (fbot n) (cons r X))) (fbot (phi n))
              hgerm n r X kn lr lX =
                univ (cons (fbot n) (cons r X)) n
                  (Eq-cong (\ q -> suc (suc q))
                    (Eq-trans (Eq-sym (LeFTup-length {rY0 rec} {X} lX)) (Eq-sym lenYb-Y0)))
                  kn refl
                  (mkSigma b1r YbX)
                where
                  b1r = Eq-transport (\ z -> LeD (embed z) (embed r)) (Eq-sym eqb1) lr
                  YbX : LeFTup Yb X
                  YbX = LeTup-trans {embedTup Yb} {embedTup (rY0 rec)} {embedTup X} (rGeH rec) lX
          -- coordinate 1 is impossible (get 1 R = bot l0, not inf)
          goR (uo3 (mkSigma (cons b0 (cons b1 Yb)) (mkSigma bel
            (mkSigma (suc zero) (mkSigma () _))))) uval
          -- coordinate >= 2: an infinite Y-coordinate
          goR (uo3 (mkSigma (cons b0 (cons b1 Yb)) (mkSigma bel
            (mkSigma (suc (suc c)) (mkSigma eqinf (mkSigma kk (mkSigma eqA0 (mkSigma phi (mkSigma phiok univ)))))))) ) uval =
            prec-inf-Case3Y-region rd phi (rN0 rec) k0R kc c (rY0 rec) Y (rBel rec)
              eqinf getY0-kc phiokKc (rReach rec) hgerm
            where
              belYb = snd (snd bel)
              lenYb = Below-length belYb
              n0hE = below-inf-fbot zero (cons b0 (cons b1 Yb)) R bel refl tt
              n0h = fst n0hE ; eqb0 = snd n0hE
              k0RE = below-botD {b1} {l0} (fst (snd bel))
              k0R = fst k0RE ; eqb1 = fst (snd k0RE) ; k0Rl0 = snd (snd k0RE)
              rec = reconcile rd Y k0R n0h Yb rn Y1 belYb belY1 (reachAt k0R k0Rl0)
              lenYb-Y0 = LeFTup-length {Yb} {rY0 rec} (rGeH rec)
              lenYb-Y0r : Eq (length Yb) (length Y1)
              lenYb-Y0r = Eq-trans lenYb (Eq-sym (Below-length belY1))
              cYb : LeN (suc c) (length Yb)
              cYb = Eq-transport (\ n -> LeN (suc c) n) (Eq-sym lenYb) (rng c Y eqinf)
                where rng : (i : Nat) (A : Tup) -> Eq (get i A) inf -> LeN (suc i) (length A)
                      rng zero    (cons _ _)  ee = tt
                      rng (suc i) (cons _ xs) ee = rng i xs ee
                      rng i       nil         ()
              getYb-k : Eq (getF c Yb) (fbot kk)
              getYb-k = eqA0
              cY0r : LeN (suc c) (length Y1)
              cY0r = Eq-transport (\ n -> LeN (suc c) n) lenYb-Y0r cYb
              getY0r-le : LeD (embed (getF c Y1)) inf
              getY0r-le = Eq-transport (\ z -> LeD z inf) (get-embedTup c Y1 cY0r)
                (Eq-transport (\ z -> LeD (get c (embedTup Y1)) z) eqinf
                  (LeTup-get c {embedTup Y1} {Y} belY1))
              getY0r-fE = binf (getF c Y1) getY0r-le
                where binf : (x : FEl) -> LeD (embed x) inf -> Sigma Nat (\ q -> Eq x (fbot q))
                      binf (fbot q) _ = mkSigma q refl
                      binf (fcpl q) ()
              k' = fst getY0r-fE ; getY0r-k' = snd getY0r-fE
              kc = maxN kk k'
              getY0-kc : Eq (getF c (rY0 rec)) (fbot kc)
              getY0-kc =
                Eq-trans (getF-joinT c Yb Y1 lenYb-Y0r)
                  (Eq-trans (Eq-cong (\ z -> joinF z (getF c Y1)) getYb-k)
                    (Eq-cong (\ z -> joinF (fbot kk) z) getY0r-k'))
              k-le-kc : LeN kk kc
              k-le-kc = maxN-le-l kk k'
              phiokKc : PhiOK kc phi
              phiokKc = phiok-mono phi k-le-kc phiok
              hgerm : (a r : FEl) (X : FTup) (p : Nat) -> LeF (fbot (rN0 rec)) a -> LeD (bot k0R) (embed r) ->
                      LeFTup (rY0 rec) X -> LeN kc p -> Eq (getF c X) (fbot p) ->
                      Eq (H (cons a (cons r X))) (fbot (phi p))
              hgerm a r X p la lr lX kcp coordX =
                univ (cons a (cons r X)) p
                  (Eq-cong (\ q -> suc (suc q))
                    (Eq-trans (Eq-sym (LeFTup-length {rY0 rec} {X} lX)) (Eq-sym lenYb-Y0)))
                  (LeN-trans {kk} {kc} {p} k-le-kc kcp)
                  coordX
                  (mkSigma b0a (mkSigma b1r (LeFTup-del c {Yb} {X} YbX)))
                where
                  b0a = Eq-transport (\ z -> LeD (embed z) (embed a)) (Eq-sym eqb0)
                          (LeF-trans {fbot n0h} {fbot (rN0 rec)} {a} (rN0GeH rec) la)
                  b1r = Eq-transport (\ z -> LeD (embed z) (embed r)) (Eq-sym eqb1) lr
                  YbX : LeFTup Yb X
                  YbX = LeTup-trans {embedTup Yb} {embedTup (rY0 rec)} {embedTup X} (rGeH rec) lX
