{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLORT/Syntax/Ops.agda
--
-- The operator types OpF, OpG f are types; typing of  fApp f a F  and
-- gApp f g a F c;  and their congruences (fAppCong, gAppCong), which
-- let f and g change -- built from conv-App with annotation equalities,
-- using only weakening (no functionality).
------------------------------------------------------------------------

module MAHLORT.Syntax.Ops where

open import MAHLO.Basic hiding (Sigma)
open import MAHLORT.TarskiSyntax
open import MAHLORT.TarskiTyping
open import MAHLORT.Syntax.Lemmas
open import MAHLORT.Syntax.Weaken
open import MAHLORT.Syntax.Wf

------------------------------------------------------------------------
-- The operator types
------------------------------------------------------------------------

arrV : {n : Num} {G : Ctx n} {X : Expr n} -> IsType G X -> IsType G (Arr X V)
arrV hX = isty-Pi hX (isty-V (wf-extend hX))

-- T_V(x0)  in  (G, V)
elx0 : {n : Num} {G : Ctx n} -> WfCtx G -> IsType (extend G V) (ElV x0)
elx0 w = isty-ElV (ty-var (wf-extend (isty-V w)))

-- (T_V x0 -> V) -> V  in  (G, V)
bodyF : {n : Num} {G : Ctx n} -> WfCtx G -> IsType (extend G V) (Arr (Arr (ElV x0) V) V)
bodyF w = arrV (arrV (elx0 w))

opFTy : {n : Num} {G : Ctx n} -> WfCtx G -> IsType G OpF
opFTy w = isty-Pi (isty-V w) (bodyF w)

-- f a F : V
fAppTy : {n : Num} {G : Ctx n} {f a F : Expr n} ->
         HasType G f OpF -> HasType G a V -> HasType G F (Arr (ElV a) V) -> HasType G (fApp f a F) V
fAppTy hf ha hF =
  ty-App (arrV (isty-ElV ha)) (isty-V (wf-extend (arrV (isty-ElV ha))))
    (ty-App (isty-V w) (bodyF w) hf ha) hF
  where w = wfTm hf

-- the body of OpG
OpGB : {n : Num} -> Expr (suc (suc n)) -> Expr (suc n)
OpGB ff = PiB (Arr (ElV x0) V) (Arr (ElV (fApp ff x1 x0)) V)

private
  ctx2 : {n : Num} -> Ctx n -> Ctx (suc (suc n))
  ctx2 G = extend (extend G V) (Arr (ElV x0) V)

  h1 : {n : Num} {G : Ctx n} -> WfCtx G -> IsType (extend G V) (Arr (ElV x0) V)
  h1 w = arrV (elx0 w)

  w2 : {n : Num} {G : Ctx n} -> WfCtx G -> WfCtx (ctx2 G)
  w2 w = wf-extend (h1 w)

  wwf : {n : Num} {G : Ctx n} {f : Expr n} -> WfCtx G -> HasType G f OpF ->
        HasType (ctx2 G) (wkExpr (wkExpr f)) OpF
  wwf w hf = wkTm (h1 w) (wkTm (isty-V w) hf)

  fa2 : {n : Num} {G : Ctx n} {f : Expr n} -> WfCtx G -> HasType G f OpF ->
        HasType (ctx2 G) (fApp (wkExpr (wkExpr f)) x1 x0) V
  fa2 w hf = fAppTy (wwf w hf) (ty-var {i = fsuc fzero} (w2 w)) (ty-var (w2 w))

opGBody : {n : Num} {G : Ctx n} {f : Expr n} -> WfCtx G -> HasType G f OpF ->
          IsType (extend G V) (OpGB (wkExpr (wkExpr f)))
opGBody w hf = isty-Pi (h1 w) (arrV (isty-ElV (fa2 w hf)))

opGTy : {n : Num} {G : Ctx n} {f : Expr n} -> WfCtx G -> HasType G f OpF -> IsType G (OpG f)
opGTy w hf = isty-Pi (isty-V w) (opGBody w hf)

------------------------------------------------------------------------
-- gApp
------------------------------------------------------------------------

-- the type of  g a
gAE : {n : Num} (f a : Expr n) ->
      Eq (subst1 (OpGB (wkExpr (wkExpr f))) a)
         (PiB (Arr (ElV a) V) (Arr (ElV (fApp (wkExpr f) (wkExpr a) x0)) V))
gAE f a =
  Eq-cong (\ z -> PiB (Arr (ElV a) V) (Arr (ElV (fApp z (wkExpr a) x0)) V))
    (Eq-trans (subst-wk-comm (subst1Sub a) (wkExpr f)) (Eq-cong wkExpr (subst1-wk f a)))

-- the type of  g a F
gAFE : {n : Num} (f a F : Expr n) ->
       Eq (subst1 (Arr (ElV (fApp (wkExpr f) (wkExpr a) x0)) V) F) (Arr (ElV (fApp f a F)) V)
gAFE f a F = Eq-cong (\ z -> Arr (ElV z) V) (cong3 fApp (subst1-wk f F) (subst1-wk a F) refl)

private
  -- (G, a -> V) |- (f (wk a) x0) -> V
  midB : {n : Num} {G : Ctx n} {f a : Expr n} -> HasType G f OpF -> HasType G a V ->
         IsType (extend G (Arr (ElV a) V)) (Arr (ElV (fApp (wkExpr f) (wkExpr a) x0)) V)
  midB hf ha = arrV (isty-ElV (fAppTy (wkTm hA hf) (wkTm hA ha) (ty-var (wf-extend hA))))
    where hA = arrV (isty-ElV ha)

gAppTy : {n : Num} {G : Ctx n} {f g a F c : Expr n} ->
         HasType G f OpF -> HasType G g (OpG f) -> HasType G a V -> HasType G F (Arr (ElV a) V) ->
         HasType G c (ElV (fApp f a F)) -> HasType G (gApp f g a F c) V
gAppTy {f = f} {g} {a} {F} hf hg ha hF hc =
  ty-App (isty-ElV (fAppTy hf ha hF)) (isty-V (wf-extend (isty-ElV (fAppTy hf ha hF))))
    (trHT refl (gAFE f a F)
      (ty-App (arrV (isty-ElV ha)) (midB hf ha)
        (trHT refl (gAE f a) (ty-App (isty-V w) (opGBody w hf) hg ha)) hF))
    hc
  where w = wfTm hf

------------------------------------------------------------------------
-- Congruences
------------------------------------------------------------------------

private
  arrEq : {n : Num} {G : Ctx n} {a a' : Expr n} -> HasType G a V -> ConvTm G a a' V ->
          TyEq G (Arr (ElV a) V) (Arr (ElV a') V)
  arrEq ha ca = tyeq-Pi (isty-ElV ha) (isty-V w1) (isty-V w1) (tyeq-ElV ca) (tyeq-refl (isty-V w1))
    where w1 = wf-extend (isty-ElV ha)

fAppCong : {n : Num} {G : Ctx n} {f f' a a' F F' : Expr n} ->
           HasType G f OpF -> HasType G a V ->
           ConvTm G f f' OpF -> ConvTm G a a' V -> ConvTm G F F' (Arr (ElV a) V) ->
           ConvTm G (fApp f a F) (fApp f' a' F') V
fAppCong hf ha cf ca cF =
  conv-App (arrV (isty-ElV ha)) (isty-V w1) (arrEq ha ca) (tyeq-refl (isty-V w1))
    (conv-App (isty-V w) (bodyF w) (tyeq-refl (isty-V w)) (tyeq-refl (bodyF w)) cf ca) cF
  where
    w = wfTm hf
    w1 = wf-extend (arrV (isty-ElV ha))

-- the body of OpG, at convertible f
opGBodyEq : {n : Num} {G : Ctx n} {f f' : Expr n} -> WfCtx G ->
            HasType G f OpF -> HasType G f' OpF -> ConvTm G f f' OpF ->
            TyEq (extend G V) (OpGB (wkExpr (wkExpr f))) (OpGB (wkExpr (wkExpr f')))
opGBodyEq w hf hf' cf =
  tyeq-Pi (h1 w) (arrV (isty-ElV (fa2 w hf))) (arrV (isty-ElV (fa2 w hf'))) (tyeq-refl (h1 w))
    (tyeq-Pi (isty-ElV (fa2 w hf)) (isty-V w3) (isty-V w3)
       (tyeq-ElV (fAppCong (wwf w hf) (ty-var {i = fsuc fzero} (w2 w))
                    (wkCv (h1 w) (wkCv (isty-V w) cf))
                    (conv-refl (ty-var {i = fsuc fzero} (w2 w))) (conv-refl (ty-var (w2 w)))))
       (tyeq-refl (isty-V w3)))
  where w3 = wf-extend (isty-ElV (fa2 w hf))

gAppCong : {n : Num} {G : Ctx n} {f f' g g' a a' F F' c c' : Expr n} ->
           HasType G f OpF -> HasType G f' OpF -> HasType G g (OpG f) -> HasType G a V ->
           HasType G F (Arr (ElV a) V) ->
           ConvTm G f f' OpF -> ConvTm G g g' (OpG f) -> ConvTm G a a' V ->
           ConvTm G F F' (Arr (ElV a) V) -> ConvTm G c c' (ElV (fApp f a F)) ->
           ConvTm G (gApp f g a F c) (gApp f' g' a' F' c') V
gAppCong {G = G} {f = f} {f'} {a = a} {a'} {F} hf hf' hg ha hF cf cg ca cF cc =
  conv-App (isty-ElV hfa) (isty-V w4) (tyeq-ElV (fAppCong hf ha cf ca cF)) (tyeq-refl (isty-V w4))
    (trCv refl refl (gAFE f a F)
      (conv-App (arrV (isty-ElV ha)) (midB hf ha) (arrEq ha ca) qMid
        (trCv refl refl (gAE f a)
          (conv-App (isty-V w) (opGBody w hf) (tyeq-refl (isty-V w)) (opGBodyEq w hf hf' cf) cg ca))
        cF))
    cc
  where
    w = wfTm hf
    hfa = fAppTy hf ha hF
    w4 = wf-extend (isty-ElV hfa)
    hA = arrV (isty-ElV ha)
    wA = wf-extend hA
    fa1 = fAppTy (wkTm hA hf) (wkTm hA ha) (ty-var wA)
    w5 = wf-extend (isty-ElV fa1)
    qMid : TyEq (extend G (Arr (ElV a) V)) (Arr (ElV (fApp (wkExpr f) (wkExpr a) x0)) V)
                (Arr (ElV (fApp (wkExpr f') (wkExpr a') x0)) V)
    qMid = tyeq-Pi (isty-ElV fa1) (isty-V w5) (isty-V w5)
             (tyeq-ElV (fAppCong (wkTm hA hf) (wkTm hA ha) (wkCv hA cf) (wkCv hA ca)
                          (conv-refl (ty-var wA))))
             (tyeq-refl (isty-V w5))

-- f = f' : OpF  ==>  OpG f = OpG f'
opGEq : {n : Num} {G : Ctx n} {f f' : Expr n} -> WfCtx G ->
        HasType G f OpF -> HasType G f' OpF -> ConvTm G f f' OpF -> TyEq G (OpG f) (OpG f')
opGEq w hf hf' cf =
  tyeq-Pi (isty-V w) (opGBody w hf) (opGBody w hf') (tyeq-refl (isty-V w)) (opGBodyEq w hf hf' cf)

