{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Congruence.agda
--
-- Lemma 9 (congruence) and Lemma 10 (safety of the codes) of
-- mahlo-plan.tex, together with symmetry and transitivity of Op.
-- Everything here concerns a single candidate X.
------------------------------------------------------------------------

open import MAHLO.Basic
open import MAHLO.TermModel

module MAHLO.Congruence (TM : TermModel) where

open TermModel TM
open import MAHLO.Candidate TM
open import MAHLO.Pre TM

-- extensional equivalence of predicates
_<=>_ : (D -> Set) -> (D -> Set) -> Set
P <=> Q = ((a : D) -> P a -> Q a) * ((a : D) -> Q a -> P a)

module _ (X : Cand) where
  open Cand X
  private
    module R' = IsPER R-per

  ----------------------------------------------------------------------
  -- Op is antitone in the predicate, symmetric and transitive
  ----------------------------------------------------------------------

  Op-pred : {P Q : D -> Set} {f g f' g' : D} -> ((a : D) -> Q a -> P a) ->
            Op X P f g f' g' -> Op X Q f g f' g'
  Op-pred QP op A A' F F' r qA qA' e hF hF' =
    op A A' F F' r (QP A qA) (QP A' qA') e
       (\ v i -> QP _ (hF v i)) (\ v i -> QP _ (hF' v i))

  Op-sym : {P : D -> Set} {f g f' g' : D} ->
           Op X P f g f' g' -> Op X P f' g' f g
  Op-sym {P} {f} {g} {f'} {g'} op A A' F F' r pA pA' e hF hF' =
    R'.sy (fst o) , gpart
    where
      rA  = R'.rl r
      rA' = R'.rr r
      IA'A : I A' <= I A
      IA'A = snd (I-resp r)
      e' : FamEq X A' F' F
      e' v v' i =
        R'.sy (e v' v (IsPER.sy (I-per A rA) (IA'A i)))
      o = op A' A F' F (R'.sy r) pA' pA e'
             (\ v i -> hF' v (IA'A i)) (\ v i -> hF v (IA'A i))
      gpart : (c c' : D) -> I (FA f' A F) c c' ->
              R (GA g' A F c) (GA g A' F' c')
      gpart c c' i =
        let i0 = IsPER.sy (I-per (FA f' A F) (R'.rr (fst o))) i
            i1 = snd (I-resp (fst o)) i0
        in R'.sy (snd o c' c i1)

  Op-trans : {P : D -> Set} {f g f' g' f'' g'' : D} ->
             Op X P f g f' g' -> Op X P f' g' f'' g'' -> Op X P f g f'' g''
  Op-trans {P} {f} {g} {f'} {g'} {f''} {g''} op1 op2
           A A' F F' r pA pA' e hF hF' =
    R'.tr (fst o1) (fst o2) , gpart
    where
      rA  = R'.rl r
      IA'A : I A' <= I A
      IA'A = snd (I-resp r)
      e'' : FamEq X A' F' F'
      e'' v v' i = FamEq-r X rA e v v' (IA'A i)
      hF'' : FamIn X P A' F'
      hF'' v i = hF' v (IA'A i)
      o1 = op1 A A' F F' r pA pA' e hF hF'
      o2 = op2 A' A' F' F' (R'.rr r) pA' pA' e'' hF'' hF''
      gpart : (c c' : D) -> I (FA f A F) c c' ->
              R (GA g A F c) (GA g'' A' F' c')
      gpart c c' i =
        let i' = IsPER.rr (I-per (FA f A F) (R'.rl (fst o1))) i
            j  = fst (I-resp (fst o1)) i'
        in R'.tr (snd o1 c c' i) (snd o2 c' c' j)

  ----------------------------------------------------------------------
  -- Lemma 9: congruence
  ----------------------------------------------------------------------

  cong-sub : {f g f' g' : D} -> Indep X f g -> Op X (Pre X f g) f g f' g' ->
             {a : D} -> Pre X f' g' a -> Pre X f g a
  cong-sub ind op (pre-ne a n) = pre-ne a n
  cong-sub ind op (pre-nat a e) = pre-nat a e
  cong-sub ind op (pre-sat a b p r) = pre-sat a b (cong-sub ind op p) r
  cong-sub ind op (pre-pi a A F e p r h q) =
    pre-pi a A F e (cong-sub ind op p) r (\ v i -> cong-sub ind op (h v i)) q
  cong-sub ind op (pre-sig a A F e p r h q) =
    pre-sig a A F e (cong-sub ind op p) r (\ v i -> cong-sub ind op (h v i)) q
  cong-sub {f} {g} {f'} {g'} ind op (pre-f a A F e p r h q) =
    pre-sat (FA f A F) a Pf (CandCl.R-cl2 X ~~-refl (~~-sym e) eq)
    where
      pA = cong-sub ind op p
      hF : FamIn X (Pre X f g) A F
      hF v i = cong-sub ind op (h v i)
      Pf = pre-f (FA f A F) A F ~~-refl pA r hF (fst (snd (ind A F pA r hF)))
      eq = fst (op A A F F (Pre-car X pA) pA pA r hF hF)
  cong-sub {f} {g} {f'} {g'} ind op (pre-g a A F c e p r h rf i q) =
    pre-sat (GA g A F c) a Pg (CandCl.R-cl2 X ~~-refl (~~-sym e) eqg)
    where
      pA = cong-sub ind op p
      hF : FamIn X (Pre X f g) A F
      hF v i = cong-sub ind op (h v i)
      o = op A A F F (Pre-car X pA) pA pA r hF hF
      ic : I (FA f A F) c c
      ic = snd (I-resp (fst o)) i
      Pg = pre-g (GA g A F c) A F c ~~-refl pA r hF (fst (snd (ind A F pA r hF))) ic
                 (snd (snd (ind A F pA r hF)) c ic)
      eqg = snd o c c ic

  cong-sup : {f g f' g' : D} -> Indep X f' g' -> Op X (Pre X f g) f g f' g' ->
             {a : D} -> Pre X f g a -> Pre X f' g' a
  cong-sup ind op (pre-ne a n) = pre-ne a n
  cong-sup ind op (pre-nat a e) = pre-nat a e
  cong-sup ind op (pre-sat a b p r) = pre-sat a b (cong-sup ind op p) r
  cong-sup ind op (pre-pi a A F e p r h q) =
    pre-pi a A F e (cong-sup ind op p) r (\ v i -> cong-sup ind op (h v i)) q
  cong-sup ind op (pre-sig a A F e p r h q) =
    pre-sig a A F e (cong-sup ind op p) r (\ v i -> cong-sup ind op (h v i)) q
  cong-sup {f} {g} {f'} {g'} ind op (pre-f a A F e p r h q) =
    pre-sat (FA f' A F) a Pf (CandCl.R-cl2 X ~~-refl (~~-sym e) (R'.sy eq))
    where
      pA = cong-sup ind op p
      hF : FamIn X (Pre X f' g') A F
      hF v i = cong-sup ind op (h v i)
      Pf = pre-f (FA f' A F) A F ~~-refl pA r hF (fst (snd (ind A F pA r hF)))
      eq = fst (op A A F F (Pre-car X p) p p r h h)
  cong-sup {f} {g} {f'} {g'} ind op (pre-g a A F c e p r h rf i q) =
    pre-sat (GA g' A F c) a Pg (CandCl.R-cl2 X ~~-refl (~~-sym e) (R'.sy eqg))
    where
      pA = cong-sup ind op p
      hF : FamIn X (Pre X f' g') A F
      hF v i = cong-sup ind op (h v i)
      o = op A A F F (Pre-car X p) p p r h h
      ic : I (FA f' A F) c c
      ic = fst (I-resp (fst o)) i
      Pg = pre-g (GA g' A F c) A F c ~~-refl pA r hF (fst (snd (ind A F pA r hF))) ic
                 (snd (snd (ind A F pA r hF)) c ic)
      eqg = snd o c c i

  congruence : {f g f' g' : D} -> Indep X f g -> Indep X f' g' ->
               Op X (Pre X f g) f g f' g' -> Pre X f g <=> Pre X f' g'
  congruence ind ind' op =
    (\ a p -> cong-sup ind' op p) , (\ a p -> cong-sub ind op p)

  ----------------------------------------------------------------------
  -- Lemma 10: safety of the codes
  ----------------------------------------------------------------------

  -- a fresh neutral type x and a fresh neutral family y over it
  private
    yResp : {x y : D} -> N x x -> N y y -> FamResp X x y
    yResp {x} nx ny v v' i = seed-ne (ne-app ny (fst (ne-int x nx) i))

    yIn : {f g x y : D} -> N x x -> N y y -> FamIn X (Pre X f g) x y
    yIn {x = x} {y} nx ny v i = pre-ne (app y v) (ne-app ny (fst (ne-int x nx) i))

  safe-op : {f g f' g' : D} -> Op X (Pre X f g) f g f' g' -> S f f' * S g g'
  safe-op {f} {g} {f'} {g'} op = fpart , gpart
    where
      fpart : S f f'
      fpart =
        let x = fst (ext f f') ; nx = fst (snd (ext f f')) ; kx = snd (snd (ext f f'))
            y = fst (ext (app f x) (app f' x))
            ny = fst (snd (ext (app f x) (app f' x)))
            ky = snd (snd (ext (app f x) (app f' x)))
            o = op x x y y (seed-ne nx) (pre-ne x nx) (pre-ne x nx)
                   (yResp nx ny) (yIn nx ny) (yIn nx ny)
        in kx (ky (R-safe (fst o)))
      gpart : S g g'
      gpart =
        let x = fst (ext g g') ; nx = fst (snd (ext g g')) ; kx = snd (snd (ext g g'))
            y = fst (ext (app g x) (app g' x))
            ny = fst (snd (ext (app g x) (app g' x)))
            ky = snd (snd (ext (app g x) (app g' x)))
            c = fst (ext (app (app g x) y) (app (app g' x) y))
            nc = fst (snd (ext (app (app g x) y) (app (app g' x) y)))
            kc = snd (snd (ext (app (app g x) y) (app (app g' x) y)))
            o = op x x y y (seed-ne nx) (pre-ne x nx) (pre-ne x nx)
                   (yResp nx ny) (yIn nx ny) (yIn nx ny)
            ic = I-lo (FA f x y) (R'.rl (fst o)) nc
        in kx (ky (kc (R-safe (snd o c c ic))))

  safe-ind : {f g : D} -> Indep X f g -> S f f * S g g
  safe-ind {f} {g} ind = fpart , gpart
    where
      fpart : S f f
      fpart =
        let x = fst (ext f f) ; nx = fst (snd (ext f f)) ; kx = snd (snd (ext f f))
            y = fst (ext (app f x) (app f x))
            ny = fst (snd (ext (app f x) (app f x)))
            ky = snd (snd (ext (app f x) (app f x)))
            o = ind x y (pre-ne x nx) (yResp nx ny) (yIn nx ny)
        in kx (ky (R-safe (fst (snd o))))
      gpart : S g g
      gpart =
        let x = fst (ext g g) ; nx = fst (snd (ext g g)) ; kx = snd (snd (ext g g))
            y = fst (ext (app g x) (app g x))
            ny = fst (snd (ext (app g x) (app g x)))
            ky = snd (snd (ext (app g x) (app g x)))
            c = fst (ext (app (app g x) y) (app (app g x) y))
            nc = fst (snd (ext (app (app g x) y) (app (app g x) y)))
            kc = snd (snd (ext (app (app g x) y) (app (app g x) y)))
            o = ind x y (pre-ne x nx) (yResp nx ny) (yIn nx ny)
            ic = I-lo (FA f x y) (fst (snd o)) nc
        in kx (ky (kc (R-safe (snd (snd o) c ic))))
