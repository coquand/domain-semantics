{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/OmegaSub.agda
--
-- Omega.ML (MAHLO/Omega.agda) for a poset of SUBSETS of a small set S,
-- ordered by a preorder _⊑_ contained in inclusion, in which bounded
-- binary unions and small inhabited directed unions are lubs.  This is
-- the setting of Principle 5.x (pr:fix) of mahlo-results.tex.
--
-- Here Omega is an ordinary inductive family Om : Sub -> Set1 (a
-- generalised inductive definition, with a limit constructor indexed by
-- small sets), and everything is predicative:
--
--   omP           Om x -> P x
--   proposition8  Om x -> x ⊑ f x
--   theorem3      Om is directed (Conf: a common bound IN Om)
--   below-pre     Om x -> x ⊑ w for every prefixed point w
--
-- The direct union argument replaces Sup x P / compatible /
-- propositions 14-16 of the ML file: at a limit, the bound of
-- U_i x_i and y is U_i (y ∪ x_i).
--
-- The ONLY impredicative step is the hypothesis Small: Om, a family of
-- elements of Pow(S), has a small cofinal subfamily.  In CC (or with
-- propositional resizing) it holds with I = Σ Sub Om.  From it:
--
--   theorem4  OM ⊑ f OM and f OM ⊑ OM, so OM and f OM have the same
--             elements, and OM is below every prefixed point of f.
------------------------------------------------------------------------

module MAHLO.OmegaSub where

open import Agda.Primitive using (Level ; _⊔_)

record Σ {a b : Level} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public
infixr 4 _,_

infixr 2 _×_
_×_ : {a b : Level} → Set a → Set b → Set (a ⊔ b)
A × B = Σ A (λ _ → B)

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B

module Setting (S : Set) (P : (S → Set) → Set) (_⊑_ : (S → Set) → (S → Set) → Set) where

  Sub : Set₁
  Sub = S → Set

  infixl 5 _∪_
  _∪_ : Sub → Sub → Sub
  (x ∪ y) s = x s ⊎ y s

  ⋃ : {I : Set} → (I → Sub) → Sub
  ⋃ {I} x s = Σ I (λ i → x i s)

  Directed : {I : Set} → (I → Sub) → Set
  Directed {I} x = (i j : I) → Σ I (λ k → x i ⊑ x k × x j ⊑ x k)

  -- x ∪ y is in P and is the lub of x and y
  record JoinOK (x y : Sub) : Set₁ where
    field
      P∪  : P (x ∪ y)
      ub1 : x ⊑ (x ∪ y)
      ub2 : y ⊑ (x ∪ y)
      lub : {w : Sub} → P w → x ⊑ w → y ⊑ w → (x ∪ y) ⊑ w

  -- ⋃ x is in P and is the lub of the family x
  record LimOK {I : Set} (x : I → Sub) : Set₁ where
    field
      P⋃  : P (⋃ x)
      ub  : (i : I) → x i ⊑ ⋃ x
      lub : {w : Sub} → P w → ((i : I) → x i ⊑ w) → ⋃ x ⊑ w

  open JoinOK
  open LimOK

  module Thm
    (⊑-refl    : (x : Sub) → x ⊑ x)
    (⊑-trans   : {x y z : Sub} → x ⊑ y → y ⊑ z → x ⊑ z)
    (⊑-⊆       : {x y : Sub} → x ⊑ y → (s : S) → x s → y s)
    (bot       : Sub)
    (P-bot     : P bot)
    (bot-least : {x : Sub} → P x → bot ⊑ x)
    (f         : Sub → Sub)
    (P-f       : {x : Sub} → P x → P (f x))
    (f-mono    : {x y : Sub} → P x → P y → x ⊑ y → f x ⊑ f y)
    (join      : {x y z : Sub} → P x → P y → P z → x ⊑ z → y ⊑ z → JoinOK x y)
    (lim       : {I : Set} (x : I → Sub) → ((i : I) → P (x i)) → I
               → Directed x → LimOK x)
    where

    data Om : Sub → Set₁ where
      obot  : Om bot
      ostep : {x : Sub} → Om x → Om (f x)
      ojoin : {x y z : Sub} → Om x → Om y → Om z → x ⊑ z → y ⊑ z → Om (x ∪ y)
      olim  : {I : Set} (x : I → Sub) → ((i : I) → Om (x i)) → I
            → Directed x → Om (⋃ x)

    omP : {x : Sub} → Om x → P x
    omP obot                 = P-bot
    omP (ostep h)            = P-f (omP h)
    omP (ojoin hx hy hz a b) = P∪ (join (omP hx) (omP hy) (omP hz) a b)
    omP (olim x hs i d)      = P⋃ (lim x (λ j → omP (hs j)) i d)

    proposition8 : {x : Sub} → Om x → x ⊑ f x
    proposition8 obot = bot-least (P-f P-bot)
    proposition8 (ostep h) = f-mono (omP h) (P-f (omP h)) (proposition8 h)
    proposition8 (ojoin hx hy hz a b) =
      lub J (P-f (P∪ J))
        (⊑-trans (proposition8 hx) (f-mono (omP hx) (P∪ J) (ub1 J)))
        (⊑-trans (proposition8 hy) (f-mono (omP hy) (P∪ J) (ub2 J)))
      where
      J = join (omP hx) (omP hy) (omP hz) a b
    proposition8 (olim x hs i d) =
      lub L (P-f (P⋃ L)) (λ j →
        ⊑-trans (proposition8 (hs j)) (f-mono (omP (hs j)) (P⋃ L) (ub L j)))
      where
      L = lim x (λ j → omP (hs j)) i d

    -- a common bound in Om
    record Conf (x y : Sub) : Set₁ where
      constructor conf
      field
        cw  : Sub
        com : Om cw
        cl  : x ⊑ cw
        cr  : y ⊑ cw
    open Conf

    proposition12 : {x y : Sub} → Om x → Conf x y → Conf (f x) y
    proposition12 hx (conf z hz a b) =
      conf (f z) (ostep hz) (f-mono (omP hx) (omP hz) a)
           (⊑-trans b (proposition8 hz))

    theorem3 : {x y : Sub} → Om x → Om y → Conf x y
    theorem3 {y = y} obot hy = conf y hy (bot-least (omP hy)) (⊑-refl y)
    theorem3 (ostep hx) hy = proposition12 hx (theorem3 hx hy)
    theorem3 {y = y} (ojoin {x1} {x2} {z} hx1 hx2 hz a b) hy = up (theorem3 hz hy)
      where
      up : Conf z y → Conf (x1 ∪ x2) y
      up (conf t ht zt yt) =
        conf t ht (lub (join (omP hx1) (omP hx2) (omP hz) a b) (omP ht)
                         (⊑-trans a zt) (⊑-trans b zt))
             yt
    theorem3 {y = y} (olim {I} x hs i0 d) hy =
      conf (⋃ g) (olim g og i0 dg) below (⊑-trans (ub1 (J i0)) (ub Lg i0))
      where
      c : (i : I) → Conf (x i) y
      c i = theorem3 (hs i) hy
      g : I → Sub
      g i = y ∪ x i
      J : (i : I) → JoinOK y (x i)
      J i = join (omP hy) (omP (hs i)) (omP (com (c i))) (cr (c i)) (cl (c i))
      og : (i : I) → Om (g i)
      og i = ojoin hy (hs i) (com (c i)) (cr (c i)) (cl (c i))
      step : (i k : I) → x i ⊑ x k → g i ⊑ g k
      step i k ik = lub (J i) (P∪ (J k)) (ub1 (J k)) (⊑-trans ik (ub2 (J k)))
      dg : Directed g
      dg i j = fst (d i j) , step i (fst (d i j)) (fst (snd (d i j)))
                           , step j (fst (d i j)) (snd (snd (d i j)))
      Lg = lim g (λ i → omP (og i)) i0 dg
      below : ⋃ x ⊑ ⋃ g
      below = lub (lim x (λ i → omP (hs i)) i0 d) (P⋃ Lg)
                (λ i → ⊑-trans (ub2 (J i)) (ub Lg i))

    below-pre : {x w : Sub} → Om x → P w → f w ⊑ w → x ⊑ w
    below-pre obot pw fw = bot-least pw
    below-pre (ostep h) pw fw = ⊑-trans (f-mono (omP h) pw (below-pre h pw fw)) fw
    below-pre (ojoin hx hy hz a b) pw fw =
      lub (join (omP hx) (omP hy) (omP hz) a b) pw
        (below-pre hx pw fw) (below-pre hy pw fw)
    below-pre (olim x hs i d) pw fw =
      lub (lim x (λ j → omP (hs j)) i d) pw (λ j → below-pre (hs j) pw fw)

    ------------------------------------------------------------------
    -- The impredicative step, as the one hypothesis
    ------------------------------------------------------------------

    record Small : Set₁ where
      field
        I    : Set
        e    : I → Sub
        e-om : (i : I) → Om (e i)
        cof  : {x : Sub} → Om x → Σ I (λ i → x ⊑ e i)

    module Fixed (sm : Small) where
      open Small sm

      e-dir : Directed e
      e-dir i j = bound (theorem3 (e-om i) (e-om j))
        where
        bound : Conf (e i) (e j) → Σ I (λ k → e i ⊑ e k × e j ⊑ e k)
        bound (conf z hz a b) =
          fst (cof hz) , ⊑-trans a (snd (cof hz)) , ⊑-trans b (snd (cof hz))

      i0 : I
      i0 = fst (cof obot)

      OM : Sub
      OM = ⋃ e

      om-OM : Om OM
      om-OM = olim e e-om i0 e-dir

      top : {x : Sub} → Om x → x ⊑ OM
      top h = ⊑-trans (snd (cof h))
                (ub (lim e (λ i → omP (e-om i)) i0 e-dir) (fst (cof h)))

      theorem4 : (OM ⊑ f OM) × (f OM ⊑ OM)
      theorem4 = proposition8 om-OM , top (ostep om-OM)

      same-elements : (s : S) → (OM s → f OM s) × (f OM s → OM s)
      same-elements s = ⊑-⊆ (fst theorem4) s , ⊑-⊆ (snd theorem4) s

      least : {w : Sub} → P w → f w ⊑ w → OM ⊑ w
      least = below-pre om-OM
