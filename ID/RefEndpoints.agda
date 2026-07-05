{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ID.RefEndpoints.agda
--
-- The `Ref` endpoint-inversion lemma, the reflection-free content of the
-- identity type: a witness `Ref a0 : Id A a b` forces both endpoints to
-- be convertible to a0 (hence to each other).  This is the syntactic
-- inversion that subject reduction of the based-J reduction
--   J C d (Ref a0)  →  App d a0
-- needs, exactly as `ty-Lam-body` (via piInjectivity) powers the App/β
-- case.  Proved by induction on the typing derivation, with
-- idInjectivity as the engine:
--   * ty-Ref : the Id type is literally Id A' a0 a0; invert the
--     conversion to the target Id A a b and lift the endpoints from the
--     literal domain A' up to A via conv-conv.
--   * ty-conv : chain the conversions and recurse.
--
-- 0 postulates.
------------------------------------------------------------------------

module ID.RefEndpoints where

open import ID.Domain.Basic using ( Nat ; mkSigma ; fst ; Pair )
open import ID.Syntax.Raw using ( Expr ; U ; Id ; Ref )
open import ID.Syntax.Typing using
  ( Ctx ; HasType ; ConvTm
  ; ty-Id ; ty-Ref ; ty-conv
  ; conv-refl ; conv-sym ; conv-conv ; conv-trans )
open import ID.IdInjectivity using ( idInjectivity )

------------------------------------------------------------------------
-- Id former inversion (mirror of ty-Pi-invert).
------------------------------------------------------------------------

ty-Id-invert : {n : Nat} {G : Ctx n} {A a b T : Expr n} ->
  HasType G (Id A a b) T ->
  Pair (HasType G A U) (Pair (HasType G a A) (HasType G b A))
ty-Id-invert (ty-Id dA da db) = mkSigma dA (mkSigma da db)
ty-Id-invert (ty-conv d _ _)  = ty-Id-invert d

------------------------------------------------------------------------
-- Ref endpoint inversion.
--
-- Given HasType G (Ref a0) T and ConvTm G T (Id A a b) U (with A:U),
-- produce ConvTm G a0 a A and ConvTm G a0 b A.
------------------------------------------------------------------------

ty-Ref-endpoints : {n : Nat} {G : Ctx n}
  {a0 : Expr n} {T A a b : Expr n} ->
  HasType G (Ref a0) T ->
  ConvTm G T (Id A a b) U ->
  HasType G A U ->
  Pair (ConvTm G a0 a A) (ConvTm G a0 b A)
ty-Ref-endpoints (ty-Ref dA' da') conv dAU =
  let mkSigma convA (mkSigma ca cb) = idInjectivity conv
  in mkSigma (conv-conv ca convA dAU) (conv-conv cb convA dAU)
ty-Ref-endpoints (ty-conv d dConv _) conv dAU =
  ty-Ref-endpoints d (conv-trans dConv conv) dAU

------------------------------------------------------------------------
-- Convenience: the two endpoints of a Ref's Id type are convertible.
-- Takes the (well-formed) Id typing so the reflexive target conversion
-- and the domain typing are available.
------------------------------------------------------------------------

ty-Ref-endpoints-eq : {n : Nat} {G : Ctx n}
  {a0 : Expr n} {A a b : Expr n} ->
  HasType G (Ref a0) (Id A a b) ->
  HasType G (Id A a b) U ->
  ConvTm G a b A
ty-Ref-endpoints-eq d dId =
  let mkSigma ca cb = ty-Ref-endpoints d (conv-refl dId) (fst (ty-Id-invert dId))
  in conv-trans (conv-sym ca) cb
