{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Syntax/CodeCong.agda
--
-- Congruences for the codes of U_{f,g} in which f, g may change too
-- (the primitive conv-PiU, ..., conv-Ghat keep f, g fixed).  Derived
-- by REFLECTION: map both sides to V by T^, use the T^-equations and
-- the congruences of the V-codes / fApp / gApp, and reflect back.
-- These are what functionality needs: a substitution moves f, g.
------------------------------------------------------------------------

module MAHLORT.Syntax.CodeCong where

open import MAHLO.Basic hiding (Sigma)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Weaken
open import MAHLORT.Syntax.Wf
open import MAHLORT.Syntax.CtxConv
open import MAHLORT.Syntax.Ops

module _ {n : Num} {G : Ctx n} {f f' g g' a a' : Expr n} {b b' : Expr (suc n)}
         (ha : HasType G a (TyU f g)) (ha' : HasType G a' (TyU f' g'))
         (ca : ConvTm G a a' (TyU f g))
         (hb : HasType (extend G (ElU f g a)) b (wkExpr (TyU f g)))
         (hb' : HasType (extend G (ElU f' g' a')) b' (wkExpr (TyU f' g')))
         (cb : ConvTm (extend G (ElU f g a)) b b' (wkExpr (TyU f g))) where

  -- the family  \x:T_V(T^ a). T^ b  and its convertibility
  hEa : IsType G (ElV (That a))
  hEa = isty-ElV (ty-That ha)

  private
    qE : TyEq G (ElV (That a)) (ElU f g a)
    qE = tyeq-sym (tyeq-ElU-That ha)

    qE' : TyEq G (ElV (That a)) (ElU f' g' a')
    qE' = tyeq-trans (tyeq-ElV (conv-That ca)) (tyeq-sym (tyeq-ElU-That ha'))

  hTb : HasType (extend G (ElV (That a))) (That b) V
  hTb = ccTm hEa qE (ty-That hb)

  hTb' : HasType (extend G (ElV (That a))) (That b') V
  hTb' = ccTm hEa qE' (ty-That hb')

  cTb : ConvTm (extend G (ElV (That a))) (That b) (That b') V
  cTb = ccCv hEa qE (conv-That cb)

  cFam : ConvTm G (Lam (ElV (That a)) (That b)) (Lam (ElV (That a')) (That b')) (Arr (ElV (That a)) V)
  cFam = conv-Lam hEa (isty-V (wf-extend hEa)) (tyeq-ElV (conv-That ca)) cTb

  hFam : HasType G (Lam (ElV (That a)) (That b)) (Arr (ElV (That a)) V)
  hFam = ty-Lam hEa (isty-V (wf-extend hEa)) hTb

  module _ (eU : TyEq G (TyU f g) (TyU f' g')) where

    ccPiU : ConvTm G (PiU f g a (Lam (ElU f g a) b)) (PiU f' g' a' (Lam (ElU f' g' a') b')) (TyU f g)
    ccPiU =
      conv-reflect (ty-PiU ha hb) (ty-conv (ty-PiU ha' hb') (tyeq-sym eU))
        (conv-trans (conv-That-PiU ha hb)
          (conv-trans (conv-PiV (ty-That ha) hTb hTb' (conv-That ca) cTb)
                      (conv-sym (conv-That-PiU ha' hb'))))

    ccSigU : ConvTm G (SigU f g a (Lam (ElU f g a) b)) (SigU f' g' a' (Lam (ElU f' g' a') b')) (TyU f g)
    ccSigU =
      conv-reflect (ty-SigU ha hb) (ty-conv (ty-SigU ha' hb') (tyeq-sym eU))
        (conv-trans (conv-That-SigU ha hb)
          (conv-trans (conv-SigV (ty-That ha) hTb hTb' (conv-That ca) cTb)
                      (conv-sym (conv-That-SigU ha' hb'))))

    module _ (hf : HasType G f OpF) (hg : HasType G g (OpG f))
             (hf' : HasType G f' OpF) (hg' : HasType G g' (OpG f'))
             (cf : ConvTm G f f' OpF) where

      ccFhat : ConvTm G (Fhat f g a (Lam (ElU f g a) b)) (Fhat f' g' a' (Lam (ElU f' g' a') b')) (TyU f g)
      ccFhat =
        conv-reflect (ty-Fhat hf hg ha hb) (ty-conv (ty-Fhat hf' hg' ha' hb') (tyeq-sym eU))
          (conv-trans (conv-That-Fhat hf hg ha hb)
            (conv-trans (fAppCong hf (ty-That ha) cf (conv-That ca) cFam)
                        (conv-sym (conv-That-Fhat hf' hg' ha' hb'))))

      ccGhat : {c c' : Expr n} ->
               (cg : ConvTm G g g' (OpG f)) ->
               HasType G c (ElU f g (Fhat f g a (Lam (ElU f g a) b))) ->
               HasType G c' (ElU f' g' (Fhat f' g' a' (Lam (ElU f' g' a') b'))) ->
               ConvTm G c c' (ElU f g (Fhat f g a (Lam (ElU f g a) b))) ->
               ConvTm G (Ghat f g a (Lam (ElU f g a) b) c) (Ghat f' g' a' (Lam (ElU f' g' a') b') c')
                        (TyU f g)
      ccGhat cg hc hc' cc =
        conv-reflect (ty-Ghat hf hg ha hb hc) (ty-conv (ty-Ghat hf' hg' ha' hb' hc') (tyeq-sym eU))
          (conv-trans (conv-That-Ghat hf hg ha hb hc)
            (conv-trans (gAppCong hf hf' hg (ty-That ha) hFam cf cg (conv-That ca) cFam
                           (conv-conv cc (tyeq-trans (tyeq-ElU-That (ty-Fhat hf hg ha hb))
                                                     (tyeq-ElV (conv-That-Fhat hf hg ha hb)))))
                        (conv-sym (conv-That-Ghat hf' hg' ha' hb' hc'))))

ccNatU : {n : Num} {G : Ctx n} {f f' g g' : Expr n} ->
         IsType G (TyU f g) -> IsType G (TyU f' g') -> TyEq G (TyU f g) (TyU f' g') ->
         ConvTm G (NatU f g) (NatU f' g') (TyU f g)
ccNatU hU hU' eU =
  conv-reflect (ty-NatU hU) (ty-conv (ty-NatU hU') (tyeq-sym eU))
    (conv-trans (conv-That-NatU hU) (conv-sym (conv-That-NatU hU')))

-- T_U(a) = T_U'(a')  along  a = a' : U_{f,g},  a' : U_{f',g'}
elUEq : {n : Num} {G : Ctx n} {f f' g g' a a' : Expr n} ->
        HasType G a (TyU f g) -> HasType G a' (TyU f' g') -> ConvTm G a a' (TyU f g) ->
        TyEq G (ElU f g a) (ElU f' g' a')
elUEq ha ha' ca =
  tyeq-trans (tyeq-ElU-That ha) (tyeq-trans (tyeq-ElV (conv-That ca)) (tyeq-sym (tyeq-ElU-That ha')))
