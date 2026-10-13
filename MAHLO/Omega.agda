{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Omega.agda
--
-- A transcription of Omega.ML (ffix.pdf: Coquand, proof in the Calculus
-- of Constructions, January 1987) of the fixed point theorem of fix.pdf.
--
--   A preordered by R, with a least element bottom, a total binary
--   operation sup that is a lub whenever its arguments have an upper
--   bound, and Lim : (A -> Prop) -> A, a lub of every directed predicate.
--   f monotone.  Then, with OM = Lim Omega,
--       R OM (f OM)  and  R (f OM) OM                      (theorem4)
--
-- Omega is the subset A of fix.pdf, defined impredicatively as the
-- intersection of all predicates containing bottom and closed under f,
-- under conditional sups (Clos) and under inhabited directed Lim
-- (admissible).  The proof is that of the ML file: Omega is directed
-- (theorem3), by induction on Omega with the predicate
-- [u] Omega u /\ confluent Omega u y.
--
-- The impredicativity is isolated in the record CC: a type of
-- propositions PROP : Set closed under Pi over EVERY X : Set, in
-- particular over A -> PROP.  This is the Prop of the Calculus of
-- Constructions.  Agda has no such universe, so CC is a parameter.
-- Only Pi is used: /\, the existential in confluent, and Sup are the
-- impredicative encodings, eliminated only into PROP, as in CC.
-- (CC has trivial instances, PROP = Unit; the content of the theorem is
-- for faithful instances, e.g. given propositional resizing.)
--
-- The names follow the ML file (proposition8 ... theorem4).
------------------------------------------------------------------------

module MAHLO.Omega where

record CC : Set₁ where
  field
    PROP : Set
    Prf  : PROP → Set
    Pi   : (X : Set) → (X → PROP) → PROP
    lam  : {X : Set} {B : X → PROP} → ((x : X) → Prf (B x)) → Prf (Pi X B)
    app  : {X : Set} {B : X → PROP} → Prf (Pi X B) → (x : X) → Prf (B x)

module Logic (cc : CC) where
  open CC cc public

  infixr 3 _⇒_
  infixr 4 _∧_

  _⇒_ : PROP → PROP → PROP
  p ⇒ q = Pi (Prf p) (λ _ → q)

  _∧_ : PROP → PROP → PROP
  p ∧ q = Pi PROP (λ C → (p ⇒ q ⇒ C) ⇒ C)

  ∧I : {p q : PROP} → Prf p → Prf q → Prf (p ∧ q)
  ∧I a b = lam (λ C → lam (λ k → app (app k a) b))

  ∧1 : {p q : PROP} → Prf (p ∧ q) → Prf p
  ∧1 {p} h = app (app h p) (lam (λ a → lam (λ _ → a)))

  ∧2 : {p q : PROP} → Prf (p ∧ q) → Prf q
  ∧2 {q = q} h = app (app h q) (lam (λ _ → lam (λ b → b)))

module Fix
  (cc : CC) (let open Logic cc)
  (A      : Set)
  (R      : A → A → PROP)
  (bottom : A)
  (f      : A → A)
  (sup    : A → A → A)
  (Lim    : (A → PROP) → A)
  where

  confluent : (A → PROP) → A → A → PROP
  confluent P x y = Pi PROP (λ C → Pi A (λ z → P z ⇒ R x z ⇒ R y z ⇒ C) ⇒ C)

  inclus : (A → PROP) → (A → PROP) → PROP
  inclus Q P = Pi A (λ x → Q x ⇒ P x)

  directed : (A → PROP) → PROP
  directed Q = Pi A (λ x → Pi A (λ y → Q x ⇒ Q y ⇒ confluent Q x y))

  module Axioms
    (Ref     : (x : A) → Prf (R x x))
    (Trans   : {x y z : A} → Prf (R x y) → Prf (R y z) → Prf (R x z))
    (minimum : (x : A) → Prf (R bottom x))
    (Incr    : {x y : A} → Prf (R x y) → Prf (R (f x) (f y)))
    (upperb1 : {x y z : A} → Prf (R x z) → Prf (R y z) → Prf (R x (sup x y)))
    (upperb2 : {x y z : A} → Prf (R x z) → Prf (R y z) → Prf (R y (sup x y)))
    (least   : {x y z : A} → Prf (R x z) → Prf (R y z) → Prf (R (sup x y) z))
    (Upperb  : {Q : A → PROP} {x : A} → Prf (directed Q) → Prf (Q x)
             → Prf (R x (Lim Q)))
    (Least   : {Q : A → PROP} {z : A} → Prf (directed Q)
             → ((x : A) → Prf (Q x) → Prf (R x z)) → Prf (R (Lim Q) z))
    where

    -- introduction and elimination for the encoded notions -------------

    lemme : {P : A → PROP} {x y : A} (z : A)
          → Prf (P z) → Prf (R x z) → Prf (R y z) → Prf (confluent P x y)
    lemme z pz a b = lam (λ C → lam (λ k → app (app (app (app k z) pz) a) b))

    tactic-conf : {P : A → PROP} {x y : A} {C : PROP} → Prf (confluent P x y)
                → ((z : A) → Prf (P z) → Prf (R x z) → Prf (R y z) → Prf C)
                → Prf C
    tactic-conf {C = C} h k =
      app (app h C) (lam (λ z → lam (λ pz → lam (λ a → lam (λ b → k z pz a b)))))

    inclI : {Q P : A → PROP} → ((x : A) → Prf (Q x) → Prf (P x))
          → Prf (inclus Q P)
    inclI h = lam (λ x → lam (h x))

    inclE : {Q P : A → PROP} → Prf (inclus Q P) → (x : A) → Prf (Q x)
          → Prf (P x)
    inclE h x = app (app h x)

    dirI : {Q : A → PROP}
         → ((x y : A) → Prf (Q x) → Prf (Q y) → Prf (confluent Q x y))
         → Prf (directed Q)
    dirI h = lam (λ x → lam (λ y → lam (λ qx → lam (λ qy → h x y qx qy))))

    dirE : {Q : A → PROP} → Prf (directed Q) → (x y : A) → Prf (Q x)
         → Prf (Q y) → Prf (confluent Q x y)
    dirE h x y qx qy = app (app (app (app h x) y) qx) qy

    permuter : {P : A → PROP} {x y : A} → Prf (confluent P x y)
             → Prf (confluent P y x)
    permuter c = tactic-conf c (λ z pz a b → lemme z pz b a)

    -- the closure conditions -------------------------------------------

    admissible : (A → PROP) → PROP
    admissible P = Pi (A → PROP) (λ Q → Pi A (λ x →
                     Q x ⇒ inclus Q P ⇒ directed Q ⇒ P (Lim Q)))

    admI : {P : A → PROP}
         → ((Q : A → PROP) (x : A) → Prf (Q x) → Prf (inclus Q P)
            → Prf (directed Q) → Prf (P (Lim Q)))
         → Prf (admissible P)
    admI h = lam (λ Q → lam (λ x → lam (λ qx → lam (λ i → lam (λ d →
               h Q x qx i d)))))

    admE : {P : A → PROP} → Prf (admissible P) → (Q : A → PROP) (x : A)
         → Prf (Q x) → Prf (inclus Q P) → Prf (directed Q) → Prf (P (Lim Q))
    admE h Q x qx i d = app (app (app (app (app h Q) x) qx) i) d

    Stable : (A → PROP) → PROP
    Stable P = Pi A (λ x → P x ⇒ P (f x))

    stI : {P : A → PROP} → ((x : A) → Prf (P x) → Prf (P (f x)))
        → Prf (Stable P)
    stI h = lam (λ x → lam (h x))

    stE : {P : A → PROP} → Prf (Stable P) → (x : A) → Prf (P x)
        → Prf (P (f x))
    stE h x = app (app h x)

    Clos : (A → PROP) → PROP
    Clos P = Pi A (λ x → Pi A (λ y →
               P x ⇒ P y ⇒ confluent P x y ⇒ P (sup x y)))

    closI : {P : A → PROP}
          → ((x y : A) → Prf (P x) → Prf (P y) → Prf (confluent P x y)
             → Prf (P (sup x y)))
          → Prf (Clos P)
    closI h = lam (λ x → lam (λ y → lam (λ px → lam (λ py → lam (λ c →
                h x y px py c)))))

    closE : {P : A → PROP} → Prf (Clos P) → (x y : A) → Prf (P x)
          → Prf (P y) → Prf (confluent P x y) → Prf (P (sup x y))
    closE h x y px py c = app (app (app (app (app h x) y) px) py) c

    -- Omega -------------------------------------------------------------

    Omega : A → PROP
    Omega u = Pi (A → PROP) (λ P →
                P bottom ⇒ admissible P ⇒ Stable P ⇒ Clos P ⇒ P u)

    omI : {u : A}
        → ((P : A → PROP) → Prf (P bottom) → Prf (admissible P)
           → Prf (Stable P) → Prf (Clos P) → Prf (P u))
        → Prf (Omega u)
    omI h = lam (λ P → lam (λ b → lam (λ a → lam (λ s → lam (λ c →
              h P b a s c)))))

    omE : {u : A} → Prf (Omega u) → (P : A → PROP) → Prf (P bottom)
        → Prf (admissible P) → Prf (Stable P) → Prf (Clos P) → Prf (P u)
    omE h P b a s c = app (app (app (app (app h P) b) a) s) c

    -- the propositions of Omega.ML ------------------------------------

    proposition8 : {x : A} → Prf (Omega x) → Prf (R x (f x))
    proposition8 h = omE h (λ u → R u (f u)) (minimum (f bottom)) ad st cl
      where
      ad = admI (λ Q a qa i d →
             Least d (λ y qy → Trans (inclE i y qy) (Incr (Upperb d qy))))
      st = stI (λ u h → Incr h)
      cl = closI (λ y z hy hz c → tactic-conf c (λ t _ yt zt →
             least (Trans hy (Incr (upperb1 yt zt)))
                   (Trans hz (Incr (upperb2 yt zt)))))

    proposition9 : {x : A} → Prf (Omega x) → Prf (Omega (f x))
    proposition9 {x} h = omI (λ P b a s c → stE s x (omE h P b a s c))

    proposition10 : Prf (Clos Omega)
    proposition10 = closI (λ x y hx hy c → omI (λ P b a s cl →
      closE cl x y (omE hx P b a s cl) (omE hy P b a s cl)
        (tactic-conf c (λ z hz xz yz → lemme z (omE hz P b a s cl) xz yz))))

    proposition11 : Prf (admissible Omega)
    proposition11 = admI (λ Q x qx i d → omI (λ P b a s c →
      admE a Q x qx (inclI (λ y qy → omE (inclE i y qy) P b a s c)) d))

    proposition12 : {x y : A} → Prf (confluent Omega x y)
                  → Prf (confluent Omega (f x) y)
    proposition12 c = tactic-conf c (λ z hz xz yz →
      lemme (f z) (proposition9 hz) (Incr xz) (Trans yz (proposition8 hz)))

    proposition13 : (x : A) → Prf (Clos (λ u → confluent Omega u x))
    proposition13 x = closI (λ y z hy hz c → tactic-conf c (λ t pt yt zt →
      tactic-conf pt (λ t1 ht1 tt1 xt1 →
        lemme t1 ht1 (least (Trans yt tt1) (Trans zt tt1)) xt1)))

    -- the image of P under sup x
    Sup : A → (A → PROP) → A → PROP
    Sup x P y = Pi (A → PROP) (λ Q → Pi A (λ z → P z ⇒ Q (sup x z)) ⇒ Q y)

    Sup-intro : {x : A} {P : A → PROP} {y : A} → Prf (P y)
              → Prf (Sup x P (sup x y))
    Sup-intro {y = y} py = lam (λ Q → lam (λ h → app (app h y) py))

    supE : {x : A} {P : A → PROP} {y : A} → Prf (Sup x P y) → (Q : A → PROP)
         → ((z : A) → Prf (P z) → Prf (Q (sup x z))) → Prf (Q y)
    supE h Q k = app (app h Q) (lam (λ z → lam (k z)))

    compatible : A → (A → PROP) → PROP
    compatible x P = Pi A (λ z → P z ⇒ confluent Omega z x)

    compE : {x : A} {P : A → PROP} → Prf (compatible x P) → (z : A)
          → Prf (P z) → Prf (confluent Omega z x)
    compE h z = app (app h z)

    proposition14 : {x : A} {P : A → PROP} → Prf (Omega x)
                  → Prf (inclus P Omega) → Prf (compatible x P)
                  → Prf (inclus (Sup x P) Omega)
    proposition14 {x} hx i cp = inclI (λ y hy → supE hy Omega (λ z pz →
      closE proposition10 x z hx (inclE i z pz) (permuter (compE cp z pz))))

    upp1 : {x : A} {P : A → PROP} → Prf (compatible x P) → {y : A}
         → Prf (P y) → Prf (R x (sup x y))
    upp1 cp {y} py = tactic-conf (compE cp y py) (λ z _ yz xz → upperb1 xz yz)

    upp2 : {x : A} {P : A → PROP} → Prf (compatible x P) → {y : A}
         → Prf (P y) → Prf (R y (sup x y))
    upp2 cp {y} py = tactic-conf (compE cp y py) (λ z _ yz xz → upperb2 xz yz)

    proposition15 : {x : A} {P : A → PROP} → Prf (directed P)
                  → Prf (compatible x P) → Prf (directed (Sup x P))
    proposition15 {x} {P} d cp = dirI (λ y z hy hz →
      supE hy (λ y → confluent (Sup x P) y z) (λ y1 py1 →
      supE hz (λ z → confluent (Sup x P) (sup x y1) z) (λ z1 pz1 →
      tactic-conf (dirE d y1 z1 py1 pz1) (λ t1 pt1 y1t1 z1t1 →
        lemme (sup x t1) (Sup-intro pt1)
          (least (upp1 cp pt1) (Trans y1t1 (upp2 cp pt1)))
          (least (upp1 cp pt1) (Trans z1t1 (upp2 cp pt1)))))))

    proposition16 : {x : A} → Prf (Omega x)
                  → Prf (admissible (λ u → Omega u ∧ confluent Omega u x))
    proposition16 {x} hx = admI (λ Q a qa i d →
      let iO : Prf (inclus Q Omega)
          iO = inclI (λ z qz → ∧1 (inclE i z qz))
          cp : Prf (compatible x Q)
          cp = lam (λ z → lam (λ qz → ∧2 (inclE i z qz)))
          dS = proposition15 d cp
          oL = admE proposition11 (Sup x Q) (sup x a) (Sup-intro qa)
                 (proposition14 hx iO cp) dS
      in ∧I (admE proposition11 Q a qa iO d)
            (lemme (Lim (Sup x Q)) oL
               (Least d (λ z qz → Trans (upp2 cp qz) (Upperb dS (Sup-intro qz))))
               (Trans (upp1 cp qa) (Upperb dS (Sup-intro qa)))))

    proposition17 : {P1 P2 : A → PROP} → Prf (Clos P1) → Prf (Clos P2)
                  → Prf (Clos (λ u → P1 u ∧ P2 u))
    proposition17 c1 c2 = closI (λ x y hx hy c →
      ∧I (closE c1 x y (∧1 hx) (∧1 hy)
            (tactic-conf c (λ z hz a b → lemme z (∧1 hz) a b)))
         (closE c2 x y (∧2 hx) (∧2 hy)
            (tactic-conf c (λ z hz a b → lemme z (∧2 hz) a b))))

    proposition18 : {P1 P2 : A → PROP} → Prf (Stable P1) → Prf (Stable P2)
                  → Prf (Stable (λ u → P1 u ∧ P2 u))
    proposition18 s1 s2 = stI (λ x h → ∧I (stE s1 x (∧1 h)) (stE s2 x (∧2 h)))

    fact : Prf (Omega bottom)
    fact = omI (λ P b _ _ _ → b)

    theorem3 : Prf (directed Omega)
    theorem3 = dirI (λ x y hx hy → ∧2 (omE hx (λ u → Omega u ∧ confluent Omega u y)
      (∧I fact (lemme y hy (minimum y) (Ref y)))
      (proposition16 hy)
      (proposition18 (stI (λ u h → proposition9 h)) (stI (λ u h → proposition12 h)))
      (proposition17 proposition10 (proposition13 y))))

    OM : A
    OM = Lim Omega

    theorem4 : Prf (R OM (f OM) ∧ R (f OM) OM)
    theorem4 = ∧I (Least theorem3 (λ x h →
                     Trans (proposition8 h) (Incr (Upperb theorem3 h))))
                  (Upperb theorem3 (proposition9 oOM))
      where
      oOM : Prf (Omega OM)
      oOM = admE proposition11 Omega bottom fact (inclI (λ x h → h)) theorem3
