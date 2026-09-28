{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.LC.Loop
--
-- Loop checking (Bezem–Coquand; bcde.pdf App. C): it is decidable
-- whether a level theory has a loop, i.e. a level l with l⁺ ≤ l.
--
--   decLoop : (Th : LCtx) -> Either (Loop Th) (LoopFree Th)
--
-- One round of the solver (BCDE4.LC.Decide) from the start function
-- that puts every variable of Th at B, the largest offset occurring in
-- the body of a clause:
--
--   * a variable reaches the cap: the gap certificate (LC.Cert.certLoop)
--     gives a set W with  W + n ⊢ W + (n+1),  i.e. the loop  l⁺ ≤ l  for
--     l = ⋁_{x ∈ W} x + n;
--   * no variable reaches the cap: the capped fixpoint c is a finite
--     model above B.  Shifted upwards by any K it is still a model (every
--     body holds at shift 0 already, all its offsets being ≤ B), so it
--     refutes every loop: from a loop l, atoms(l) ⊢ atoms(l) + N for all N,
--     which a finite model satisfying atoms(l) cannot validate.
------------------------------------------------------------------------

module BCDE4.LC.Loop where

open import BCDE4.Basic
open import BCDE4.Levels
open import BCDE4.LC.Horn
open import BCDE4.LC.Model
open import BCDE4.LC.Iter
open import BCDE4.LC.Solve
open import BCDE4.LC.Cert
open import BCDE4.LC.Equiv using (valid-from-der ; der-from-valid ; der-shift ; ShiftP ; shiftA-comp)
open import BCDE4.LC.Decide
open import BCDE4.LC.Codes using (plus-zero)

------------------------------------------------------------------------
-- Arithmetic
------------------------------------------------------------------------

private
  plus-mono : (a b c d : Nat) -> Le a b -> Le c d -> Le (a + c) (b + d)
  plus-mono = le-plus-mono

  split : (k s : Nat) -> Le k s -> Sigma Nat (\ s' -> Eq s (k + s'))
  split zero    s       p = mkSigma s refl
  split (suc k) zero    ()
  split (suc k) (suc s) p = let r = split k s p in mkSigma (fst r) (Eq-cong suc (snd r))

  cancel : (k a b : Nat) -> Le (k + a) (k + b) -> Le a b
  cancel zero    a b p = p
  cancel (suc k) a b p = cancel k a b p

  not-suc-le : (a b : Nat) -> Le (suc a + b) a -> Empty
  not-suc-le a b p = Le-antisym-suc a (Le-trans (suc a) (suc a + b) a (Le-plus-l (suc a) b) p)

------------------------------------------------------------------------
-- The offset bound B and the start
------------------------------------------------------------------------

bodyOffs : LCtx -> List Nat
bodyOffs Th = concatMap (\ c -> map snd (body c)) (clausesTh Th)

Bd : LCtx -> Nat
Bd Th = maxL (bodyOffs Th)

body-le-B : (Th : LCtx) (c : Clause) -> Mem c (clausesTh Th) -> (a : Atom) -> Mem a (body c) -> Le (snd a) (Bd Th)
body-le-B Th c mc a ma =
  maxL-ub (bodyOffs Th) (snd a) (mem-concatMap (\ c' -> map snd (body c')) (clausesTh Th) mc (mem-map snd (body c) ma))

startAtoms : LCtx -> List Atom
startAtoms Th = map (\ x -> mkSigma x (Bd Th)) (varsTh Th)

-- the start function is never ∞
private
  joinV-noinf : (j : Nat) (r : Val) -> (Eq r inf -> Empty) -> Eq (joinV (fin j) r) inf -> Empty
  joinV-noinf j none    nr ()
  joinV-noinf j (fin i) nr ()
  joinV-noinf j inf     nr e = nr refl

startOf-noinf : (as : List Atom) (x : Nat) -> Eq (startOf as x) inf -> Empty
startOf-noinf []       x ()
startOf-noinf (a ∷ as) x = go (eqN? (fst a) x)
  where
    go : (d : Either (Eq (fst a) x) (Eq (fst a) x -> Empty)) -> Eq (startStep a (startOf as x) x d) inf -> Empty
    go (inl e) = joinV-noinf (snd a) (startOf as x) (startOf-noinf as x)
    go (inr n) = startOf-noinf as x

capSel : (K : Nat) (V : List Nat) (x : Nat) -> Either (Mem x V) (Mem x V -> Empty) -> Val
capSel K V x (inl m) = fin K
capSel K V x (inr n) = none

capSel-in : (K : Nat) (V : List Nat) (x : Nat) -> Mem x V -> (d : Either (Mem x V) (Mem x V -> Empty)) ->
  Eq (capSel K V x d) (fin K)
capSel-in K V x m (inl m') = refl
capSel-in K V x m (inr n)  = absurd (n m)

------------------------------------------------------------------------
-- Levels from atoms
------------------------------------------------------------------------

atomsL-atomL : (x k : Nat) -> Eq (atomsL (atomL (mkSigma x k))) (mkSigma x k ∷ [])
atomsL-atomL x zero    = refl
atomsL-atomL x (suc k) = Eq-cong (map (shiftA (suc zero))) (atomsL-atomL x k)

-- x0 + n  ∨  ⋁_{x ∈ xs} x + n
supAt : Nat -> Nat -> List Nat -> LExpr
supAt n x0 []       = atomL (mkSigma x0 n)
supAt n x0 (x ∷ xs) = lsup (atomL (mkSigma x n)) (supAt n x0 xs)

supAt-inv : (n x0 : Nat) (xs : List Nat) (a : Atom) -> Mem a (atomsL (supAt n x0 xs)) ->
  Sigma Nat (\ x -> Pair (Either (Eq x x0) (Mem x xs)) (Eq a (mkSigma x n)))
supAt-inv n x0 [] a m = go (Eq-transport (Mem a) (atomsL-atomL x0 n) m)
  where
    go : Mem a (mkSigma x0 n ∷ []) -> Sigma Nat (\ x -> Pair (Either (Eq x x0) (Mem x [])) (Eq a (mkSigma x n)))
    go here = mkSigma x0 (mkSigma (inl refl) refl)
    go (there ())
supAt-inv n x0 (x ∷ xs) a m with mem-++-split (atomsL (atomL (mkSigma x n))) (atomsL (supAt n x0 xs)) m
... | inl h = go (Eq-transport (Mem a) (atomsL-atomL x n) h)
  where
    go : Mem a (mkSigma x n ∷ []) -> Sigma Nat (\ y -> Pair (Either (Eq y x0) (Mem y (x ∷ xs))) (Eq a (mkSigma y n)))
    go here = mkSigma x (mkSigma (inr here) refl)
    go (there ())
... | inr h = let r = supAt-inv n x0 xs a h
              in mkSigma (fst r) (mkSigma (sel (fst (snd r))) (snd (snd r)))
  where
    sel : {y : Nat} -> Either (Eq y x0) (Mem y xs) -> Either (Eq y x0) (Mem y (x ∷ xs))
    sel (inl e) = inl e
    sel (inr m') = inr (there m')

supAt-in : (n x0 : Nat) (xs : List Nat) (x : Nat) -> Mem x xs -> Mem (mkSigma x n) (atomsL (supAt n x0 xs))
supAt-in n x0 (y ∷ xs) .y here =
  mem-++-l (atomsL (atomL (mkSigma y n))) (atomsL (supAt n x0 xs))
    (Eq-transport (Mem (mkSigma y n)) (Eq-sym (atomsL-atomL y n)) here)
supAt-in n x0 (y ∷ xs) x (there m) =
  mem-++-r (atomsL (atomL (mkSigma y n))) (atomsL (supAt n x0 xs)) (supAt-in n x0 xs x m)

supAt-in0 : (n x0 : Nat) (xs : List Nat) -> Mem (mkSigma x0 n) (atomsL (supAt n x0 xs))
supAt-in0 n x0 []       = Eq-transport (Mem (mkSigma x0 n)) (Eq-sym (atomsL-atomL x0 n)) here
supAt-in0 n x0 (y ∷ xs) = mem-++-r (atomsL (atomL (mkSigma y n))) (atomsL (supAt n x0 xs)) (supAt-in0 n x0 xs)

-- every level has an atom
someAtom : (l : LExpr) -> Sigma Atom (\ a -> Mem a (atomsL l))
someAtom (lvar i)   = mkSigma (mkSigma i zero) here
someAtom (lsup l m) = let r = someAtom l in mkSigma (fst r) (mem-++-l (atomsL l) (atomsL m) (snd r))
someAtom (lnext l)  = let r = someAtom l in mkSigma (shiftA (suc zero) (fst r)) (mem-map (shiftA (suc zero)) (atomsL l) (snd r))

------------------------------------------------------------------------
-- A loop gives arbitrarily high atoms
------------------------------------------------------------------------

loop-climb : {Th : LCtx} (l : LExpr) -> Valid Th (lsup (lnext l) l) l ->
  (N : Nat) (a : Atom) -> Mem a (atomsL l) -> Der Th (InL (atomsL l)) (shiftA N a)
loop-climb {Th} l v zero    a ma = d-hyp ma
loop-climb {Th} l v (suc N) a ma =
  Eq-transport (Der Th (InL (atomsL l)))
    (Eq-trans (shiftA-comp N (suc zero) a) (Eq-cong (\ k -> shiftA k a) (plus-one N)))
    (der-cut back (der-shift N step1))
  where
    plus-one : (N : Nat) -> Eq (N + suc zero) (suc N)
    plus-one zero    = refl
    plus-one (suc N) = Eq-cong suc (plus-one N)
    step1 : Der Th (InL (atomsL l)) (shiftA (suc zero) a)
    step1 = snd (der-from-valid v) (shiftA (suc zero) a)
              (mem-++-l (atomsL (lnext l)) (atomsL l) (mem-map (shiftA (suc zero)) (atomsL l) ma))
    back : (b : Atom) -> ShiftP N (InL (atomsL l)) b -> Der Th (InL (atomsL l)) b
    back b (mkSigma a' (mkSigma ma' refl)) = loop-climb l v N a' ma'

------------------------------------------------------------------------
-- The decision
------------------------------------------------------------------------

decLoop : (Th : LCtx) -> Either (Loop Th) (LoopFree Th)
decLoop Th = go (find (\ x -> HitK K (c x)) (\ x -> hitK? K (c x)) V)
  where
    A : List Atom
    A = startAtoms Th
    open Solver Th A
    B : Nat
    B = Bd Th
    g : Fn
    g = f0
    der0 : DerAll Th P g
    der0 = startOf-der A
    m0 : Nat
    m0 = maxFin V g
    K : Nat
    K = m0 + suc (length V) * suc (MaxG Th)
    bndg : (x : Nat) -> Mem x V -> BndV K (g x)
    bndg x m = val (g x) refl
      where
        val : (v : Val) -> Eq (g x) v -> BndV K v
        val none    e = tt
        val (fin a) e = Le-trans a m0 K (maxFin-ub V g x m a e) (Le-plus-l m0 _)
        val inf     e = tt
    module CT = Cert Th P V hvV K
    out = CT.RA.run g der0 bndg
    c : Fn
    c = CT.RA.Out.res out
    ivc = CT.RA.Out.inv out
    fixc = CT.RA.Out.fix out
    offc : (x : Nat) -> (Mem x V -> Empty) -> Eq (c x) none
    offc x nm = Eq-trans (CT.RA.Inv.offV ivc x nm) (f0-off x nm)

    -- c is bounded by K on V: it is below the capped fixpoint "K on V"
    capFn : Fn
    capFn x = capSel K V x (memV? V x)
    capFn-in : (x : Nat) -> Mem x V -> Eq (capFn x) (fin K)
    capFn-in x m = capSel-in K V x m (memV? V x)
    capV-le-K : (v : Val) -> LeV (capV K v) (fin K)
    capV-le-K none    = tt
    capV-le-K (fin s) = min-r s K
    capV-le-K inf     = Le-refl K
    capFix : CT.RA.CFix capFn
    capFix cl mc = Eq-transport (LeV (capV K (fire capFn cl))) (Eq-sym (capFn-in (fst (head cl)) (hvV cl mc)))
                     (capV-le-K (fire capFn cl))
    g-le-cap : LeF g capFn
    g-le-cap x = sel (memV? V x)
      where
        sel : (d : Either (Mem x V) (Mem x V -> Empty)) -> LeV (g x) (capSel K V x d)
        sel (inl m) = val (g x) refl
          where
            val : (v : Val) -> Eq (g x) v -> LeV v (fin K)
            val none    e = tt
            val (fin a) e = Le-trans a m0 K (maxFin-ub V g x m a e) (Le-plus-l m0 _)
            val inf     e = absurd (startOf-noinf A x e)
        sel (inr n) = Eq-transport (\ v -> LeV v none) (Eq-sym (f0-off x n)) tt
    c-le-cap : LeF c capFn
    c-le-cap = CT.RA.Inv.least ivc capFn capFix g-le-cap
    c-le-K : (x : Nat) -> Mem x V -> LeV (c x) (fin K)
    c-le-K x m = Eq-transport (LeV (c x)) (capFn-in x m) (c-le-cap x)

    -- ... and above B on V
    inV-B : (x : Nat) -> Mem x V -> InV B (c x)
    inV-B x m = InV-mono B (g x) (c x) (CT.RA.Inv.ge ivc x) (startOf-sat A (mkSigma x B) (memA (mem-++-split (varsTh Th) (map fst A) m)))
      where
        memA : Either (Mem x (varsTh Th)) (Mem x (map fst A)) -> Mem (mkSigma x B) A
        memA (inl m') = mem-map (\ y -> mkSigma y B) (varsTh Th) m'
        memA (inr m') = let r = mem-map-inv fst A m'
                            r2 = mem-map-inv (\ y -> mkSigma y B) (varsTh Th) (fst (snd r))
                        in Eq-transport (\ z -> Mem (mkSigma z B) A)
                             (Eq-sym (Eq-trans (snd (snd r)) (Eq-cong fst (snd (snd r2)))))
                             (mem-map (\ y -> mkSigma y B) (varsTh Th) (fst (snd r2)))

    -- the value of c on V: a number above B
    valC : (x : Nat) -> Mem x V -> Sigma Nat (\ v -> Pair (Eq (c x) (fin v)) (Le B v))
    valC x m = go' (c x) refl (inV-B x m) (c-le-K x m)
      where
        go' : (w : Val) -> Eq (c x) w -> InV B w -> LeV w (fin K) -> Sigma Nat (\ v -> Pair (Eq (c x) (fin v)) (Le B v))
        go' none    e () le
        go' (fin v) e p  le = mkSigma v (mkSigma e p)
        go' inf     e p  ()

    -- no finite model value is infinite
    notAll : (x : Nat) -> ((i : Nat) -> InV i (c x)) -> Empty
    notAll x all = go' (memV? V x)
      where
        go' : Either (Mem x V) (Mem x V -> Empty) -> Empty
        go' (inl m) = let r = valC x m
                      in Le-antisym-suc (fst r) (Eq-transport (InV (suc (fst r))) (fst (snd r)) (all (suc (fst r))))
        go' (inr n) = Eq-transport (InV zero) (offc x n) (all zero)

    go : Find (\ x -> HitK K (c x)) V -> Either (Loop Th) (LoopFree Th)

    ----------------------------------------------------------------
    -- no variable reaches the cap: c is a finite model above B
    ----------------------------------------------------------------
    go (no nohit) = inr refute
      where
        model : Model Th c
        model cl mc = fire-SatC c cl
          (uncap K (fire c cl) (c (fst (head cl))) (fixc cl mc)
             (CT.RA.Inv.bndd ivc (fst (head cl)) (hvV cl mc))
             (\ j e le -> nohit (fst (head cl)) (hvV cl mc) (mkSigma j (mkSigma e le))))

        refute : LoopFree Th
        refute (mkSigma l v) = not-suc-le (Kl + finOr0 (c (fst a))) (snd a) climbed
          where
            Kl : Nat
            Kl = maxL (map snd (atomsL l))
            fo : Nat -> Nat
            fo x = finOr0 (c x)
            h : Fn
            h x = fin (Kl + fo x)
            -- the shifted function is still a model
            fo-val : (x : Nat) (m : Mem x V) -> Eq (fo x) (fst (valC x m))
            fo-val x m = Eq-cong finOr0 (fst (snd (valC x m)))
            hModel : Model Th h
            hModel cl mc s sb = sel (le? Kl s)
              where
                y = fst (head cl)
                vy = valC y (hvV cl mc)
                cy : Eq (c y) (fin (fst vy))
                cy = fst (snd vy)
                bodyVal : (a : Atom) -> Mem a (body cl) -> Sigma Nat (\ v -> Pair (Eq (c (fst a)) (fin v)) (Le B v))
                bodyVal a ma = valC (fst a) (body-vars ma)
                  where body-vars : Mem a (body cl) -> Mem (fst a) V
                        body-vars ma' = mem-++-l (varsTh Th) (map fst A) (body-in-vars Th cl mc a ma')
                sel : Either (Le Kl s) (Le (suc s) Kl) -> SatA h (shiftA s (head cl))
                sel (inl p) =
                  let sp = split Kl s p
                      s' = fst sp
                      sat : SatBody c s' (body cl)
                      sat a ma = let bv = bodyVal a ma
                                     q : Le (s + snd a) (Kl + fo (fst a))
                                     q = sb a ma
                                     q' : Le (Kl + (s' + snd a)) (Kl + fst bv)
                                     q' = Eq-transport (\ X -> Le X (Kl + fst bv))
                                            (Eq-trans (Eq-cong (\ Y -> Y + snd a) (snd sp)) (plus-assoc Kl s' (snd a)))
                                            (Eq-transport (\ Y -> Le (s + snd a) (Kl + Y)) (fo-val (fst a) (body-vars' a ma)) q)
                                 in Eq-transport (InV (s' + snd a)) (Eq-sym (fst (snd bv))) (cancel Kl _ _ q')
                      hd : InV (s' + snd (head cl)) (c y)
                      hd = model cl mc s' sat
                      hd' : Le (s' + snd (head cl)) (fst vy)
                      hd' = Eq-transport (InV (s' + snd (head cl))) cy hd
                  in Eq-transport (\ X -> Le X (Kl + fo y))
                       (Eq-sym (Eq-trans (Eq-cong (\ Y -> Y + snd (head cl)) (snd sp)) (plus-assoc Kl s' (snd (head cl)))))
                       (Eq-transport (\ Y -> Le (Kl + (s' + snd (head cl))) (Kl + Y)) (Eq-sym (fo-val y (hvV cl mc)))
                          (plus-mono-r Kl _ _ hd'))
                  where
                    body-vars' : (a : Atom) -> Mem a (body cl) -> Mem (fst a) V
                    body-vars' a ma = mem-++-l (varsTh Th) (map fst A) (body-in-vars Th cl mc a ma)
                sel (inr p) =
                  let sat0 : SatBody c zero (body cl)
                      sat0 a ma = let bv = bodyVal a ma
                                  in Eq-transport (InV (snd a)) (Eq-sym (fst (snd bv)))
                                       (Le-trans (snd a) B (fst bv) (body-le-B Th cl mc a ma) (snd (snd bv)))
                      hd : Le (snd (head cl)) (fst vy)
                      hd = Eq-transport (InV (snd (head cl))) cy (model cl mc zero sat0)
                  in Eq-transport (\ Y -> Le (s + snd (head cl)) (Kl + Y)) (Eq-sym (fo-val y (hvV cl mc)))
                       (plus-mono s Kl (snd (head cl)) (fst vy)
                          (Le-trans s (suc s) Kl (Le-suc s s (Le-refl s)) p) hd)
            -- the atoms of l hold in h
            hHyp : (b : Atom) -> InL (atomsL l) b -> SatA h b
            hHyp b mb = Le-trans (snd b) Kl (Kl + fo (fst b))
                          (maxL-ub (map snd (atomsL l)) (snd b) (mem-map snd (atomsL l) mb)) (Le-plus-l Kl _)
            a  = fst (someAtom l)
            ma = snd (someAtom l)
            N  = suc (Kl + fo (fst a))
            climbed : Le (N + snd a) (Kl + fo (fst a))
            climbed = sound h hModel hHyp (loop-climb l v N a ma)

    ----------------------------------------------------------------
    -- a variable reaches the cap: a loop, from the certificate
    ----------------------------------------------------------------
    go (yes xs mxs (mkSigma js (mkSigma ejs Kjs))) = inl (mkSigma lW isLoop)
      where
        module W = Window Th c V m0 offc
        gp = W.gapped
        n : Nat
        n = W.Gapped.n gp
        gle : (x : Nat) (a : Nat) -> Eq (g x) (fin a) -> Le a n
        gle x a e = sel (memV? V x)
          where
            sel : Either (Mem x V) (Mem x V -> Empty) -> Le a n
            sel (inl m)  = Le-trans a m0 n (maxFin-ub V g x m a e) (W.Gapped.m0le gp)
            sel (inr nm) = absurd (noneFin (Eq-trans (Eq-sym e) (f0-off x nm)))
              where noneFin : Eq (fin a) none -> Empty
                    noneFin ()
        hiS : Hi n (c xs)
        hiS = Eq-transport (Hi n) (Eq-sym ejs) (Le-trans (suc n) K js (W.Gapped.ltK gp) Kjs)
        Wl : List Nat
        Wl = filterD (\ x -> Hi n (c x)) (\ x -> hi? n (c x)) V
        lW : LExpr
        lW = supAt n xs Wl
        s : Fn
        s = CT.s0 n c
        loopE : (z : Nat) -> Hi n (c z) -> Der Th (SatA s) (mkSigma z (suc n))
        loopE = CT.certLoop g c n ivc fixc (W.Gapped.gap gp) gle
        inV : (x : Nat) -> Hi n (c x) -> Mem x V
        inV x hx = sel (memV? V x)
          where
            sel : Either (Mem x V) (Mem x V -> Empty) -> Mem x V
            sel (inl m) = m
            sel (inr nm) = absurd (Eq-transport (Hi n) (offc x nm) hx)
        -- the hypotheses of the certificate are atoms below lW
        toW : (b : Atom) -> SatA s b -> Der Th (InL (atomsL lW)) b
        toW b sb = sel (CT.sat-s0 n (c (fst b)) (cls n (c (fst b))) (snd b) sb)
          where
            sel : Either (Pair (Hi n (c (fst b))) (Le (snd b) n))
                         (Pair ((i : Nat) -> InV i (s (fst b))) ((i : Nat) -> InV i (c (fst b)))) ->
                  Der Th (InL (atomsL lW)) b
            sel (inl hl) = der-down (fst b) n (snd b) (snd hl)
                             (d-hyp (supAt-in n xs Wl (fst b)
                               (filterD-intro (\ x -> Hi n (c x)) (\ x -> hi? n (c x)) V (inV (fst b) (fst hl)) (fst hl))))
            sel (inr ii) = absurd (notAll (fst b) (snd ii))
        hiOf : (x : Nat) -> Either (Eq x xs) (Mem x Wl) -> Hi n (c x)
        hiOf x (inl refl) = hiS
        hiOf x (inr m)    = snd (filterD-mem (\ y -> Hi n (c y)) (\ y -> hi? n (c y)) V m)
        isLoop : Valid Th (lsup (lnext lW) lW) lW
        isLoop = valid-from-der (lsup (lnext lW) lW) lW
          (\ b mb -> d-hyp (mem-++-r (atomsL (lnext lW)) (atomsL lW) mb))
          up
          where
            up : (a : Atom) -> Mem a (atomsL (lsup (lnext lW) lW)) -> Der Th (InL (atomsL lW)) a
            up a ma with mem-++-split (atomsL (lnext lW)) (atomsL lW) ma
            ... | inr m = d-hyp m
            ... | inl m =
              let r  = mem-map-inv (shiftA (suc zero)) (atomsL lW) m
                  r2 = supAt-inv n xs Wl (fst r) (fst (snd r))
                  x  = fst r2
              in Eq-transport (Der Th (InL (atomsL lW)))
                   (Eq-sym (Eq-trans (snd (snd r)) (Eq-cong (shiftA (suc zero)) (snd (snd r2)))))
                   (der-cut toW (loopE x (hiOf x (fst (snd r2)))))
