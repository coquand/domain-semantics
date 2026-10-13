{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/TermModel.agda
--
-- The abstract term model of mahlo-plan.tex, Issue 2: a set D of
-- (beta-delta classes of) terms with application and the type
-- constructors Pi, Sig, Nat, U, the projections fst, snd, together
-- with the neutral PER N, the safe PER S and the PER NatR of natural
-- numbers.  The fields are the assumptions (A1)--(A4) used in Lemmas
-- 8--15.  Sigma is handled exactly like Pi.
--
-- D is a SETOID: elements are compared by a congruence  _~~_  (in the
-- concrete model: beta-delta conversion of terms), never by Eq.  The
-- three base relations are closed under ~~, and injectivity and
-- disjointness of the constructors are stated up to ~~.
------------------------------------------------------------------------

module MAHLO.TermModel where

open import MAHLO.Basic

record TermModel : Set1 where
  field
    D    : Set
    app  : D -> D -> D
    Pi   : D -> D -> D
    Sig  : D -> D -> D
    pr1 : D -> D
    pr2 : D -> D
    Nat  : D
    U    : D -> D -> D

    -- the equality of D: an equivalence and a congruence
    _~~_    : D -> D -> Set
    ~~-refl  : {a : D} -> a ~~ a
    ~~-sym   : {a b : D} -> a ~~ b -> b ~~ a
    ~~-trans : {a b c : D} -> a ~~ b -> b ~~ c -> a ~~ c
    app-cong : {a a' b b' : D} -> a ~~ a' -> b ~~ b' -> app a b ~~ app a' b'
    Pi-cong  : {a a' b b' : D} -> a ~~ a' -> b ~~ b' -> Pi a b ~~ Pi a' b'
    Sig-cong : {a a' b b' : D} -> a ~~ a' -> b ~~ b' -> Sig a b ~~ Sig a' b'
    U-cong   : {a a' b b' : D} -> a ~~ a' -> b ~~ b' -> U a b ~~ U a' b'
    pr1-cong : {a a' : D} -> a ~~ a' -> pr1 a ~~ pr1 a'
    pr2-cong : {a a' : D} -> a ~~ a' -> pr2 a ~~ pr2 a'

    N    : D -> D -> Set
    S    : D -> D -> Set
    NatR : D -> D -> Set

    -- the three relations are PERs
    N-sym      : {a b : D} -> N a b -> N b a
    N-trans    : {a b c : D} -> N a b -> N b c -> N a c
    S-sym      : {a b : D} -> S a b -> S b a
    S-trans    : {a b c : D} -> S a b -> S b c -> S a c
    NatR-sym   : {a b : D} -> NatR a b -> NatR b a
    NatR-trans : {a b c : D} -> NatR a b -> NatR b c -> NatR a c

    -- ... closed under the equality of D
    N-resp    : {a a' b : D} -> a ~~ a' -> N a b -> N a' b
    S-resp    : {a a' b : D} -> a ~~ a' -> S a b -> S a' b
    NatR-resp : {a a' b : D} -> a ~~ a' -> NatR a b -> NatR a' b

    -- (A2) safety range
    N-S     : {a b : D} -> N a b -> S a b
    N-NatR  : {a b : D} -> N a b -> NatR a b
    NatR-S  : {a b : D} -> NatR a b -> S a b
    ne-app  : {u u' v v' : D} -> N u u' -> S v v' -> N (app u v) (app u' v')
    ne-fst  : {u u' : D} -> N u u' -> N (pr1 u) (pr1 u')
    ne-snd  : {u u' : D} -> N u u' -> N (pr2 u) (pr2 u')

    -- (A3) extensionality with a fresh neutral (a fresh variable)
    ext : (v v' : D) -> Sigma D (\ x -> N x x * (S (app v x) (app v' x) -> S v v'))
    -- and for pairs (surjective pairing)
    ext-pair : {v v' : D} -> S (pr1 v) (pr1 v') -> S (pr2 v) (pr2 v') -> S v v'

    -- (A1) injectivity and disjointness of the constructors
    Pi-inj : {A F A' F' : D} -> Pi A F ~~ Pi A' F' -> (A ~~ A') * (F ~~ F')
    U-inj  : {f g f' g' : D} -> U f g ~~ U f' g' -> (f ~~ f') * (g ~~ g')
    Sig-inj : {A F A' F' : D} -> Sig A F ~~ Sig A' F' -> (A ~~ A') * (F ~~ F')
    Pi-Nat : {A F : D} -> Pi A F ~~ Nat -> Empty
    Sig-Pi  : {A F A' F' : D} -> Sig A F ~~ Pi A' F' -> Empty
    Sig-Nat : {A F : D} -> Sig A F ~~ Nat -> Empty
    Sig-U   : {A F f g : D} -> Sig A F ~~ U f g -> Empty
    ne-Sig  : {A F b : D} -> N (Sig A F) b -> Empty
    Pi-U   : {A F f g : D} -> Pi A F ~~ U f g -> Empty
    Nat-U  : {f g : D} -> Nat ~~ U f g -> Empty
    ne-Pi  : {A F b : D} -> N (Pi A F) b -> Empty
    ne-Nat : {b : D} -> N Nat b -> Empty
    ne-U   : {f g b : D} -> N (U f g) b -> Empty

    -- (A4) the safe PER is a congruence for the constructors
    S-Pi  : {A A' F F' : D} -> S A A' -> S F F' -> S (Pi A F) (Pi A' F')
    S-Sig : {A A' F F' : D} -> S A A' -> S F F' -> S (Sig A F) (Sig A' F')
    S-U   : {f f' g g' : D} -> S f f' -> S g g' -> S (U f g) (U f' g')
    S-Nat : S Nat Nat

  infix 4 _~~_

  -- Eq implies ~~  (so any model with ~~ := Eq is an instance)
  Eq-~~ : {a b : D} -> Eq a b -> a ~~ b
  Eq-~~ refl = ~~-refl
