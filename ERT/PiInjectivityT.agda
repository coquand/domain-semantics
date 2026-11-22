{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.PiInjectivityT
--
-- Π-injectivity for the Tarski theory T_T, transferred from T_R:
--
--   PiInj-T : Γ ⊢T Π(A,B) = Π(A',B')
--          -> (Γ ⊢T A = A')  ×  (Γ.A ⊢T B = B')
--
-- Erase (Lemma 4.6), apply PiInj-R (domain-model adequacy), lift the
-- component conversions back (Theorem 4.13), move them to Γ and Γ.A
-- (same erasure), and connect the endpoints by uniqueness of types
-- with a given erasure (Lemma 4.10, type-uniq).
--
-- No postulates, no pragmas.
------------------------------------------------------------------------

module ERT.PiInjectivityT where

open import ERT.Basic
import ERT.RussellTyping  as RT
import ERT.TarskiSyntax   as T
import ERT.TarskiTyping   as TT
import ERT.Erasure        as E
import ERT.TarskiMeta     as TM
open import ERT.EraseDeriv using (eraseCtx ; erase-ConvTy)
open import ERT.LiftBack using (move-ConvTy)
open import ERT.UniquenessTermPartial using (type-uniq)
open import ERT.Equivalence using (LiftConvTy ; mkLiftConvTy ; lift-ConvTy)
open import ERT.PiInjectivityR using (PiInj-R)

-- Π-inversion of type formation (IsType has no conversion rule)
inv-Pi-Ty : {n : Nat} {G : TT.Ctx n} {A : T.Expr n} {B : T.Expr (suc n)}
  -> TT.IsType G (T.Pi A B) -> Pair (TT.IsType G A) (TT.IsType (TT.extend G A) B)
inv-Pi-Ty (TT.is-Ty-Pi dA dB) = mkSigma dA dB

-- a Russell conversion between erasures of two Tarski types comes back
conv-back : {n : Nat} {G : TT.Ctx n} {A A' : T.Expr n}
  -> TT.IsType G A -> TT.IsType G A'
  -> RT.ConvTy (eraseCtx G) (E.erase A) (E.erase A')
  -> TT.ConvTy G A A'
conv-back {G = G} {A} {A'} dA dA' c with lift-ConvTy c
... | mkLiftConvTy G1 A1 A1' G≡ A≡ A'≡ der =
  let der' = move-ConvTy G1 G (TM.isType-WfCtx dA) G≡ der
  in TT.conv-Ty-trans
       (type-uniq dA (TM.presup-l-ConvTy der') (Eq-sym A≡))
       (TT.conv-Ty-trans der' (type-uniq (TM.presup-r-ConvTy der') dA' A'≡))

PiInj-T : {n : Nat} {G : TT.Ctx n} {A A' : T.Expr n} {B B' : T.Expr (suc n)}
  -> TT.ConvTy G (T.Pi A B) (T.Pi A' B')
  -> Pair (TT.ConvTy G A A') (TT.ConvTy (TT.extend G A) B B')
PiInj-T d =
  let l  = inv-Pi-Ty (TM.presup-l-ConvTy d)
      r  = inv-Pi-Ty (TM.presup-r-ConvTy d)
      cA = conv-back (fst l) (fst r) (fst (PiInj-R (erase-ConvTy d)))
      dB' = TM.ctx-conv-IsType (fst r) (fst l) (TT.conv-Ty-sym cA) (snd r)
  in mkSigma cA (conv-back (snd l) dB' (snd (PiInj-R (erase-ConvTy d))))
