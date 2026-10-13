{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/EqInstance.agda
--
-- Sanity check for the setoid refactor: the previous, Eq-based form of
-- the term model (D compared by Eq) is an instance of TermModel with
--   _~~_ := Eq.
-- Congruence and the respect fields are trivial at Eq; injectivity and
-- disjointness are the old fields.  So the generalisation loses nothing.
------------------------------------------------------------------------

module MAHLO.EqInstance where

open import MAHLO.Basic
open import MAHLO.TermModel

record EqTermModel : Set1 where
  field
    D    : Set
    app  : D -> D -> D
    Pi   : D -> D -> D
    Sig  : D -> D -> D
    pr1  : D -> D
    pr2  : D -> D
    Nat  : D
    U    : D -> D -> D
    N    : D -> D -> Set
    S    : D -> D -> Set
    NatR : D -> D -> Set
    N-sym      : {a b : D} -> N a b -> N b a
    N-trans    : {a b c : D} -> N a b -> N b c -> N a c
    S-sym      : {a b : D} -> S a b -> S b a
    S-trans    : {a b c : D} -> S a b -> S b c -> S a c
    NatR-sym   : {a b : D} -> NatR a b -> NatR b a
    NatR-trans : {a b c : D} -> NatR a b -> NatR b c -> NatR a c
    N-S     : {a b : D} -> N a b -> S a b
    N-NatR  : {a b : D} -> N a b -> NatR a b
    NatR-S  : {a b : D} -> NatR a b -> S a b
    ne-app  : {u u' v v' : D} -> N u u' -> S v v' -> N (app u v) (app u' v')
    ne-fst  : {u u' : D} -> N u u' -> N (pr1 u) (pr1 u')
    ne-snd  : {u u' : D} -> N u u' -> N (pr2 u) (pr2 u')
    ext : (v v' : D) -> Sigma D (\ x -> N x x * (S (app v x) (app v' x) -> S v v'))
    ext-pair : {v v' : D} -> S (pr1 v) (pr1 v') -> S (pr2 v) (pr2 v') -> S v v'
    Pi-inj  : {A F A' F' : D} -> Eq (Pi A F) (Pi A' F') -> Eq A A' * Eq F F'
    U-inj   : {f g f' g' : D} -> Eq (U f g) (U f' g') -> Eq f f' * Eq g g'
    Sig-inj : {A F A' F' : D} -> Eq (Sig A F) (Sig A' F') -> Eq A A' * Eq F F'
    Pi-Nat  : {A F : D} -> Eq (Pi A F) Nat -> Empty
    Sig-Pi  : {A F A' F' : D} -> Eq (Sig A F) (Pi A' F') -> Empty
    Sig-Nat : {A F : D} -> Eq (Sig A F) Nat -> Empty
    Sig-U   : {A F f g : D} -> Eq (Sig A F) (U f g) -> Empty
    ne-Sig  : {A F b : D} -> N (Sig A F) b -> Empty
    Pi-U    : {A F f g : D} -> Eq (Pi A F) (U f g) -> Empty
    Nat-U   : {f g : D} -> Eq Nat (U f g) -> Empty
    ne-Pi   : {A F b : D} -> N (Pi A F) b -> Empty
    ne-Nat  : {b : D} -> N Nat b -> Empty
    ne-U    : {f g b : D} -> N (U f g) b -> Empty
    S-Pi  : {A A' F F' : D} -> S A A' -> S F F' -> S (Pi A F) (Pi A' F')
    S-Sig : {A A' F F' : D} -> S A A' -> S F F' -> S (Sig A F) (Sig A' F')
    S-U   : {f f' g g' : D} -> S f f' -> S g g' -> S (U f g) (U f' g')
    S-Nat : S Nat Nat

private
  cong2' : {A B C : Set} (h : A -> B -> C) {a a' : A} {b b' : B} ->
           Eq a a' -> Eq b b' -> Eq (h a b) (h a' b')
  cong2' h refl refl = refl

  resp : {A : Set} (P : A -> A -> Set) {a a' b : A} -> Eq a a' -> P a b -> P a' b
  resp P refl p = p

toTermModel : EqTermModel -> TermModel
toTermModel M = record
  { D = D ; app = app ; Pi = Pi ; Sig = Sig ; pr1 = pr1 ; pr2 = pr2 ; Nat = Nat ; U = U
  ; _~~_ = Eq
  ; ~~-refl = refl ; ~~-sym = Eq-sym ; ~~-trans = Eq-trans
  ; app-cong = cong2' app ; Pi-cong = cong2' Pi ; Sig-cong = cong2' Sig ; U-cong = cong2' U
  ; pr1-cong = Eq-cong pr1 ; pr2-cong = Eq-cong pr2
  ; N = N ; S = S ; NatR = NatR
  ; N-sym = N-sym ; N-trans = N-trans ; S-sym = S-sym ; S-trans = S-trans
  ; NatR-sym = NatR-sym ; NatR-trans = NatR-trans
  ; N-resp = resp N ; S-resp = resp S ; NatR-resp = resp NatR
  ; N-S = N-S ; N-NatR = N-NatR ; NatR-S = NatR-S
  ; ne-app = ne-app ; ne-fst = ne-fst ; ne-snd = ne-snd
  ; ext = ext ; ext-pair = ext-pair
  ; Pi-inj = Pi-inj ; U-inj = U-inj ; Sig-inj = Sig-inj
  ; Pi-Nat = Pi-Nat ; Sig-Pi = Sig-Pi ; Sig-Nat = Sig-Nat ; Sig-U = Sig-U ; ne-Sig = ne-Sig
  ; Pi-U = Pi-U ; Nat-U = Nat-U ; ne-Pi = ne-Pi ; ne-Nat = ne-Nat ; ne-U = ne-U
  ; S-Pi = S-Pi ; S-Sig = S-Sig ; S-U = S-U ; S-Nat = S-Nat }
  where open EqTermModel M
