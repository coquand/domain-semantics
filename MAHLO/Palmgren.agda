{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Palmgren.agda
--
-- Palmgren's paradox: a Mahlo universe that is "closed", i.e. has an
-- elimination rule, is inconsistent.
--
-- V cannot be an Agda data type: the constructor  u f g  takes
--   f : (a : V) -> (El a -> V) -> V,
-- with V in negative position, and the positivity checker rejects it.
-- So the closed Mahlo universe is given as a record hypothesis (V, El,
-- codes, dependent eliminator, computation rules), and we derive Empty.
--
-- The argument.  The induction hypothesis at  u f g  covers  f a b  for
-- ALL a : V, in particular a = u f g itself.  Take f0 a b = a.  Then
--   f0 (u f0 g0) b = u f0 g0
-- is an immediate predecessor of  u f0 g0, and induction on V proves
-- that no code equals  u f0 g0  -- not even u f0 g0 itself.
------------------------------------------------------------------------

module MAHLO.Palmgren where

data _==_ {A : Set} (x : A) : A -> Set where
  refl : x == x

data Empty : Set where

data Bool : Set where
  tt ff : Bool

sym : {A : Set} {x y : A} -> x == y -> y == x
sym refl = refl

trans : {A : Set} {x y z : A} -> x == y -> y == z -> x == z
trans refl q = q

cong : {A B : Set} (h : A -> B) {x y : A} -> x == y -> h x == h y
cong h refl = refl

subst : {A : Set} (P : A -> Set) {x y : A} -> x == y -> P x -> P y
subst P refl p = p

tt/=ff : tt == ff -> Empty
tt/=ff ()

------------------------------------------------------------------------
-- A closed Mahlo universe: Setzer's V with  U_{f,g}  codes in V, plus
-- an elimination rule.  Only N and U_{f,g} are listed; Pi, Sigma, ...
-- would add cases to elim without changing the argument.
------------------------------------------------------------------------

record ClosedMahlo : Set1 where
  field
    V  : Set
    El : V -> Set

  OpF : Set
  OpF = (a : V) -> (El a -> V) -> V

  OpG : OpF -> Set
  OpG f = (a : V) (b : El a -> V) -> El (f a b) -> V

  field
    nat : V
    u   : (f : OpF) -> OpG f -> V

  Case-u : (V -> Set) -> Set
  Case-u P = (f : OpF) (g : OpG f) ->
             ((a : V) (b : El a -> V) -> P (f a b)) ->
             ((a : V) (b : El a -> V) (c : El (f a b)) -> P (g a b c)) ->
             P (u f g)

  field
    elim  : (P : V -> Set) -> P nat -> Case-u P -> (x : V) -> P x

    beta-nat : (P : V -> Set) (pn : P nat) (pu : Case-u P) ->
               elim P pn pu nat == pn
    beta-u   : (P : V -> Set) (pn : P nat) (pu : Case-u P) (f : OpF) (g : OpG f) ->
               elim P pn pu (u f g) ==
                 pu f g (\ a b -> elim P pn pu (f a b))
                        (\ a b c -> elim P pn pu (g a b c))

------------------------------------------------------------------------
-- The paradox
------------------------------------------------------------------------

module Paradox (M : ClosedMahlo) where
  open ClosedMahlo M

  f0 : OpF
  f0 a b = a

  g0 : OpG f0
  g0 a b c = a

  x0 : V
  x0 = u f0 g0

  -- no-confusion  nat /= u f g,  by recursion into Bool
  isU : V -> Bool
  isU = elim (\ _ -> Bool) ff (\ _ _ _ _ -> tt)

  nat/=u : {f : OpF} {g : OpG f} -> nat == u f g -> Empty
  nat/=u {f} {g} e =
    tt/=ff (trans (sym (beta-u (\ _ -> Bool) ff (\ _ _ _ _ -> tt) f g))
           (trans (cong isU (sym e)) (beta-nat (\ _ -> Bool) ff (\ _ _ _ _ -> tt))))

  -- injectivity of u in f,  by recursion into OpF (no funext needed)
  proj : V -> OpF
  proj = elim (\ _ -> OpF) f0 (\ f _ _ _ -> f)

  u-inj : {f f' : OpF} {g : OpG f} {g' : OpG f'} -> u f g == u f' g' -> f == f'
  u-inj {f} {f'} {g} {g'} e =
    trans (sym (beta-u (\ _ -> OpF) f0 (\ f _ _ _ -> f) f g))
          (trans (cong proj e) (beta-u (\ _ -> OpF) f0 (\ f _ _ _ -> f) f' g'))

  -- every code differs from x0, by the elimination rule
  Q : V -> Set
  Q x = x == x0 -> Empty

  q-nat : Q nat
  q-nat = nat/=u

  q-u : Case-u Q
  q-u f g ihf _ e =
    subst (\ h -> Q (h x0 (\ _ -> x0))) (u-inj e) (ihf x0 (\ _ -> x0)) refl

  absurd : Empty
  absurd = elim Q q-nat q-u x0 refl

palmgren : ClosedMahlo -> Empty
palmgren M = Paradox.absurd M
