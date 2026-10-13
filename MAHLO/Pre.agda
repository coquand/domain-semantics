{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Pre.agda
--
-- Families, pre-universes pre(f,g,X) (with Pi and Sigma), Indep and Op
-- (mahlo-plan.tex, Definitions 4--5 and the operator equality).
------------------------------------------------------------------------

open import MAHLO.Basic
open import MAHLO.TermModel

module MAHLO.Pre (TM : TermModel) where

open TermModel TM
open import MAHLO.Candidate TM

-- f A F  and  g A F c
FA : D -> D -> D -> D
FA f A F = app (app f A) F

GA : D -> D -> D -> D -> D
GA g A F c = app (app (app g A) F) c

module _ (X : Cand) where
  open Cand X

  -- F respects equality in [A]  (first half of Definition 4)
  FamResp : D -> D -> Set
  FamResp A F = (v v' : D) -> I A v v' -> R (app F v) (app F v')

  -- F, F' are equal families over A
  FamEq : D -> D -> D -> Set
  FamEq A F F' = (v v' : D) -> I A v v' -> R (app F v) (app F' v')

  -- the values of F lie in P  (second half of Definition 4)
  FamIn : (D -> Set) -> D -> D -> Set
  FamIn P A F = (v : D) -> I A v v -> P (app F v)

------------------------------------------------------------------------
-- pre(f,g,X)  (Definition 5); conclusions are stated with an equation
-- so that no index unification is ever needed.
------------------------------------------------------------------------

data Pre (X : Cand) (f g : D) : D -> Set where
  pre-ne  : (a : D) -> N a a -> Pre X f g a
  pre-nat : (a : D) -> a ~~ Nat -> Pre X f g a
  pre-sat : (a b : D) -> Pre X f g a -> Cand.R X a b -> Pre X f g b
  pre-pi  : (a A F : D) -> a ~~ Pi A F ->
            Pre X f g A -> FamResp X A F ->
            ((v : D) -> Cand.I X A v v -> Pre X f g (app F v)) ->
            Cand.R X a a -> Pre X f g a
  pre-sig : (a A F : D) -> a ~~ Sig A F ->
            Pre X f g A -> FamResp X A F ->
            ((v : D) -> Cand.I X A v v -> Pre X f g (app F v)) ->
            Cand.R X a a -> Pre X f g a
  pre-f   : (a A F : D) -> a ~~ FA f A F ->
            Pre X f g A -> FamResp X A F ->
            ((v : D) -> Cand.I X A v v -> Pre X f g (app F v)) ->
            Cand.R X a a -> Pre X f g a
  pre-g   : (a A F c : D) -> a ~~ GA g A F c ->
            Pre X f g A -> FamResp X A F ->
            ((v : D) -> Cand.I X A v v -> Pre X f g (app F v)) ->
            Cand.R X (FA f A F) (FA f A F) ->
            Cand.I X (FA f A F) c c ->
            Cand.R X a a -> Pre X f g a

module _ (X : Cand) where
  open Cand X
  private
    module R' = IsPER R-per

  Pre-car : {f g a : D} -> Pre X f g a -> R a a
  Pre-car (pre-ne a n) = seed-ne n
  Pre-car (pre-nat a e) = CandCl.R-self X seed-nat (~~-sym e)
  Pre-car (pre-sat a b p r) = R'.rr r
  Pre-car (pre-pi a A F e p r h q) = q
  Pre-car (pre-sig a A F e p r h q) = q
  Pre-car (pre-f a A F e p r h q) = q
  Pre-car (pre-g a A F c e p r h rf i q) = q

  -- X restricted to a predicate
  Res : (D -> Set) -> Rel
  Res P v v' = R v v' * (P v * P v')

  -- independence (Definition 5)
  Indep : D -> D -> Set
  Indep f g = (A F : D) -> Pre X f g A -> FamResp X A F ->
              FamIn X (Pre X f g) A F ->
              (R (Pi A F) (Pi A F) * R (Sig A F) (Sig A F)) *
              (R (FA f A F) (FA f A F) *
               ((c : D) -> I (FA f A F) c c -> R (GA g A F c) (GA g A F c)))

  -- equality of operators, tested on P
  Op : (D -> Set) -> D -> D -> D -> D -> Set
  Op P f g f' g' =
    (A A' F F' : D) -> R A A' -> P A -> P A' -> FamEq X A F F' ->
    FamIn X P A F -> FamIn X P A F' ->
    R (FA f A F) (FA f' A' F') *
    ((c c' : D) -> I (FA f A F) c c' -> R (GA g A F c) (GA g' A' F' c'))

  -- a family is equal to itself
  FamResp-Eq : {A F : D} -> FamResp X A F -> FamEq X A F F
  FamResp-Eq r = r

  -- the left family of an equal pair respects equality
  FamEq-l : {A F F' : D} -> R A A -> FamEq X A F F' -> FamResp X A F
  FamEq-l {A} rA e v v' i =
    R'.tr (e v v' i) (R'.sy (e v' v' (IsPER.rr (I-per A rA) i)))

  -- the right family of an equal pair respects equality
  FamEq-r : {A F F' : D} -> R A A -> FamEq X A F F' -> FamResp X A F'
  FamEq-r {A} rA e v v' i =
    R'.tr (R'.sy (e v v (IsPER.rl (I-per A rA) i))) (e v v' i)

------------------------------------------------------------------------
-- Everything respects the equality of D
------------------------------------------------------------------------

FA-cong : {f f' A F : D} -> f ~~ f' -> FA f A F ~~ FA f' A F
FA-cong e = app-cong (app-cong e ~~-refl) ~~-refl

GA-cong : {g g' A F c : D} -> g ~~ g' -> GA g A F c ~~ GA g' A F c
GA-cong e = app-cong (app-cong (app-cong e ~~-refl) ~~-refl) ~~-refl

module _ (X : Cand) where
  open Cand X
  open CandCl X

  Pre-cl : {f g a b : D} -> a ~~ b -> Pre X f g a -> Pre X f g b
  Pre-cl e p = pre-sat _ _ p (R-of~~ (Pre-car X p) e)

  FamEq-tr : {A A2 F F2 F' F2' : D} -> A ~~ A2 -> F ~~ F2 -> F' ~~ F2' ->
             FamEq X A F F' -> FamEq X A2 F2 F2'
  FamEq-tr eA eF eF' fe v v' i =
    R-cl2 (app-cong eF ~~-refl) (app-cong eF' ~~-refl) (fe v v' (snd (I-idx eA) i))

  FamIn-tr : {P : D -> Set} -> ({a b : D} -> a ~~ b -> P a -> P b) ->
             {A A2 F F2 : D} -> A ~~ A2 -> F ~~ F2 -> FamIn X P A F -> FamIn X P A2 F2
  FamIn-tr cl eA eF h v i = cl (app-cong eF ~~-refl) (h v (snd (I-idx eA) i))

  Pre-cong : {f g f' g' a : D} -> f ~~ f' -> g ~~ g' -> Pre X f g a -> Pre X f' g' a
  Pre-cong ef eg (pre-ne a n) = pre-ne a n
  Pre-cong ef eg (pre-nat a e) = pre-nat a e
  Pre-cong ef eg (pre-sat a b p r) = pre-sat a b (Pre-cong ef eg p) r
  Pre-cong ef eg (pre-pi a A F e p r h q) =
    pre-pi a A F e (Pre-cong ef eg p) r (\ v i -> Pre-cong ef eg (h v i)) q
  Pre-cong ef eg (pre-sig a A F e p r h q) =
    pre-sig a A F e (Pre-cong ef eg p) r (\ v i -> Pre-cong ef eg (h v i)) q
  Pre-cong ef eg (pre-f a A F e p r h q) =
    pre-f a A F (~~-trans e (FA-cong ef)) (Pre-cong ef eg p) r
          (\ v i -> Pre-cong ef eg (h v i)) q
  Pre-cong ef eg (pre-g a A F c e p r h rf i q) =
    pre-g a A F c (~~-trans e (GA-cong eg)) (Pre-cong ef eg p) r
          (\ v j -> Pre-cong ef eg (h v j))
          (R-cl2 (FA-cong ef) (FA-cong ef) rf) (fst (I-idx (FA-cong ef)) i) q

  Indep-cong : {f g f' g' : D} -> f ~~ f' -> g ~~ g' -> Indep X f g -> Indep X f' g'
  Indep-cong ef eg ind A F p r h =
    fst o ,
    (R-cl2 (FA-cong ef) (FA-cong ef) (fst (snd o)) ,
     (\ c i -> R-cl2 (GA-cong eg) (GA-cong eg)
                 (snd (snd o) c (snd (I-idx (FA-cong ef)) i))))
    where
      o = ind A F (Pre-cong (~~-sym ef) (~~-sym eg) p) r
                  (\ v i -> Pre-cong (~~-sym ef) (~~-sym eg) (h v i))

  Op-cong : {P : D -> Set} {f g f' g' f2 g2 f2' g2' : D} ->
            f ~~ f2 -> g ~~ g2 -> f' ~~ f2' -> g' ~~ g2' ->
            Op X P f g f' g' -> Op X P f2 g2 f2' g2'
  Op-cong ef eg ef' eg' op A A' F F' r pA pA' e hF hF' =
    R-cl2 (FA-cong ef) (FA-cong ef') (fst o) ,
    (\ c c' i -> R-cl2 (GA-cong eg) (GA-cong eg')
                   (snd o c c' (snd (I-idx (FA-cong ef)) i)))
    where o = op A A' F F' r pA pA' e hF hF'
