{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- SubstitutionLemma.agda
--
-- Renaming lemma, substitution lemma, and presupposition for
-- HasType and ConvTm.  All proved in one mutual block.
-- 0 postulates.
------------------------------------------------------------------------

module SubstitutionLemma where

open import Basic using (Nat ; zero ; suc ; Eq ; refl ; Eq-cong ;
  Eq-transport ; Eq-sym ; Pair ; mkSigma ; fst ; snd)
open import RawSyntax using (Fin ; fzero ; fsuc ;
  Expr ; Var ; U ; Pi ; Lam ; App ;
  Ren ; liftRen ; renExpr ; wkRen ; wkExpr ;
  Sub ; liftSub ; substExpr ; subst1Sub ; subst1 ;
  Eq-trans ; Eq-cong2-Expr ;
  liftRen-ext ; renExpr-ext ;
  ren-ren ; ren-subst ; subst-ren ; subst-subst ;
  liftSub-ext ; substExpr-ext ;
  ren-wk-comm ; subst-wk-comm ;
  wkExpr-is-subst ; subst-var-ren)
open import TypingRules using (Ctx ; empty ; extend ; lookup ;
  WfCtx ; wf-empty ; wf-extend ;
  HasType ; ty-var ; ty-conv ; ty-U ; ty-Pi ; ty-Lam ; ty-App ;
  ConvTm ;
  conv-refl ; conv-sym ; conv-trans ; conv-conv ;
  conv-beta ; conv-Pi ; conv-funext ; conv-App-fun ; conv-App-arg)
open import Reduction using (idSub ; substExpr-id ; subst-subst1-comm)

------------------------------------------------------------------------
-- Part 1: Auxiliary equalities
------------------------------------------------------------------------

-- renExpr r (subst1 B a) = subst1 (renExpr (liftRen r) B) (renExpr r a)
ren-subst1 : {n m : Nat} (r : Ren n m) (B : Expr (suc n)) (a : Expr n) ->
  Eq (renExpr r (subst1 B a)) (subst1 (renExpr (liftRen r) B) (renExpr r a))
ren-subst1 r B a =
  Eq-trans (ren-subst r (subst1Sub a) B)
    (Eq-trans (substExpr-ext _ _ ext B)
      (Eq-sym (subst-ren (subst1Sub (renExpr r a)) (liftRen r) B)))
  where
    ext : (i : Fin _) ->
      Eq (renExpr r (subst1Sub a i))
         (subst1Sub (renExpr r a) (liftRen r i))
    ext fzero    = refl
    ext (fsuc i) = refl

-- substExpr (subst1Sub a) (wkExpr e) = e
-- (substituting a for var 0 in a weakened term gives back the original)
subst1-wk : {n : Nat} (e : Expr n) (a : Expr n) ->
  Eq (substExpr (subst1Sub a) (wkExpr e)) e
subst1-wk e a =
  Eq-trans (subst-ren (subst1Sub a) wkRen e)
    (Eq-trans (substExpr-ext _ idSub (\ i -> refl) e)
      (substExpr-id e))

------------------------------------------------------------------------
-- Part 2: Type-preserving renamings
------------------------------------------------------------------------

RenTypes : {n m : Nat} -> Ctx n -> Ctx m -> Ren n m -> Set
RenTypes G H r = (i : Fin _) -> Eq (lookup H (r i)) (renExpr r (lookup G i))

-- Weakening renaming: always type-preserving
wkRen-RenTypes : {n : Nat} {G : Ctx n} {C : Expr n} ->
  RenTypes G (extend G C) wkRen
wkRen-RenTypes i = refl

-- Lifting preserves RenTypes
liftRen-RenTypes : {n m : Nat} {G : Ctx n} {H : Ctx m}
  {r : Ren n m} {A : Expr n} ->
  RenTypes G H r ->
  RenTypes (extend G A) (extend H (renExpr r A)) (liftRen r)
liftRen-RenTypes {r = r} {A = A} rt fzero = Eq-sym (ren-wk-comm r A)
liftRen-RenTypes {G = G} {r = r} rt (fsuc i) =
  Eq-trans (Eq-cong wkExpr (rt i))
    (Eq-sym (ren-wk-comm r (lookup G i)))

------------------------------------------------------------------------
-- Part 3: Well-typed substitutions
------------------------------------------------------------------------

WtSub : {h g : Nat} -> Ctx h -> Ctx g -> Sub h g -> Set
WtSub H G sigma = (i : Fin _) -> HasType H (sigma i) (substExpr sigma (lookup G i))

------------------------------------------------------------------------
-- Part 4: The big mutual block
--
-- Contains:
--   ren-HasType, ren-ConvTm          (renaming lemma)
--   subst-HasType, subst-ConvTm      (substitution lemma)
--   typing-ConvTm                    (presupposition: ConvTm → HasType)
--   wk-HasType, wk-ConvTm            (weakening, special case of ren)
--   liftSub-WtSub                    (lifting well-typed substitutions)
--   ctx-conv-HasType, ctx-conv-ConvTm (context conversion)
------------------------------------------------------------------------

{-# TERMINATING #-}
mutual

  -- Renaming preserves HasType
  ren-HasType : {n m : Nat} {G : Ctx n} {H : Ctx m}
    {r : Ren n m} {M A : Expr n} ->
    RenTypes G H r -> WfCtx H ->
    HasType G M A -> HasType H (renExpr r M) (renExpr r A)

  -- Renaming preserves ConvTm
  ren-ConvTm : {n m : Nat} {G : Ctx n} {H : Ctx m}
    {r : Ren n m} {M N A : Expr n} ->
    RenTypes G H r -> WfCtx H ->
    ConvTm G M N A -> ConvTm H (renExpr r M) (renExpr r N) (renExpr r A)

  -- Substitution preserves HasType
  subst-HasType : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {sigma : Sub h g} {M A : Expr g} ->
    WtSub H G sigma -> WfCtx H ->
    HasType G M A -> HasType H (substExpr sigma M) (substExpr sigma A)

  -- Substitution preserves ConvTm
  subst-ConvTm : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {sigma : Sub h g} {M N A : Expr g} ->
    WtSub H G sigma -> WfCtx H ->
    ConvTm G M N A ->
    ConvTm H (substExpr sigma M) (substExpr sigma N) (substExpr sigma A)

  -- Presupposition: extract HasType from both sides of ConvTm
  typing-ConvTm : {n : Nat} {G : Ctx n} {M N A : Expr n} ->
    ConvTm G M N A -> Pair (HasType G M A) (HasType G N A)

  -- Weakening (special case of renaming with wkRen)
  wk-HasType : {n : Nat} {G : Ctx n} {C M A : Expr n} ->
    HasType G C U -> HasType G M A ->
    HasType (extend G C) (wkExpr M) (wkExpr A)
  wk-HasType {G = G} {C = C} dC d = ren-HasType (wkRen-RenTypes {G = G} {C = C}) (wf-extend dC) d

  wk-ConvTm : {n : Nat} {G : Ctx n} {C M N A : Expr n} ->
    HasType G C U -> ConvTm G M N A ->
    ConvTm (extend G C) (wkExpr M) (wkExpr N) (wkExpr A)
  wk-ConvTm {G = G} {C = C} dC d = ren-ConvTm (wkRen-RenTypes {G = G} {C = C}) (wf-extend dC) d

  -- Lifting a well-typed substitution to extended contexts
  liftSub-WtSub : {h g : Nat} {H : Ctx h} {G : Ctx g}
    {sigma : Sub h g} {A : Expr g} ->
    WtSub H G sigma -> WfCtx H -> HasType G A U ->
    WtSub (extend H (substExpr sigma A)) (extend G A) (liftSub sigma)
  liftSub-WtSub {sigma = sigma} {A = A} ws wfH dA fzero =
    -- Need: HasType (extend H sA) (Var fzero) (substExpr (liftSub sigma) (wkExpr A))
    -- substExpr (liftSub sigma) (wkExpr A) = wkExpr (substExpr sigma A) [by subst-wk-comm]
    Eq-transport (\ T -> HasType (extend _ (substExpr sigma A)) (Var fzero) T)
      (Eq-sym (subst-wk-comm sigma A))
      (ty-var (wf-extend (subst-HasType ws wfH dA)))
  liftSub-WtSub {H = H} {G = G} {sigma = sigma} {A = A} ws wfH dA (fsuc i) =
    Eq-transport (\ T -> HasType (extend H (substExpr sigma A)) (wkExpr (sigma i)) T)
      (Eq-sym (subst-wk-comm sigma (lookup G i)))
      (wk-HasType (subst-HasType ws wfH dA) (ws i))

  -- Well-typed identity substitution for context conversion
  -- from (extend G A) to (extend G A') when ConvTm G A A' U
  ctx-conv-WtSub : {n : Nat} {G : Ctx n} {A A' : Expr n} ->
    HasType G A U -> HasType G A' U -> ConvTm G A A' U ->
    WtSub (extend G A') (extend G A) idSub
  ctx-conv-WtSub {G = G} {A = A} {A' = A'} dA dA' convAA' fzero =
    Eq-transport (\ T -> HasType (extend G A') (Var fzero) T)
      (Eq-sym (Eq-trans (substExpr-ext idSub _ (\ i -> refl) (wkExpr A))
        (substExpr-id (wkExpr A))))
      (ty-conv (ty-var (wf-extend dA'))
               (wk-ConvTm dA' (conv-sym convAA'))
               (wk-HasType dA' dA))
  ctx-conv-WtSub {G = G} {A' = A'} dA dA' convAA' (fsuc i) =
    Eq-transport (\ T -> HasType (extend G A') (Var (fsuc i)) T)
      (Eq-sym (Eq-trans (substExpr-ext idSub _ (\ j -> refl) (wkExpr (lookup G i)))
        (substExpr-id (wkExpr (lookup G i)))))
      (ty-var (wf-extend dA'))

  -- Context conversion: move HasType from (extend G A) to (extend G A')
  ctx-conv-HasType : {n : Nat} {G : Ctx n} {A A' : Expr n}
    {M B : Expr (suc n)} ->
    HasType G A U -> HasType G A' U -> ConvTm G A A' U ->
    HasType (extend G A) M B -> HasType (extend G A') M B
  ctx-conv-HasType {M = M} {B = B} dA dA' convAA' d =
    let d' = subst-HasType (ctx-conv-WtSub dA dA' convAA') (wf-extend dA') d
    in Eq-transport (\ X -> HasType (extend _ _) X B)
         (substExpr-id M)
         (Eq-transport (\ Y -> HasType (extend _ _) (substExpr idSub M) Y)
           (substExpr-id B) d')

  -- Context conversion for ConvTm
  ctx-conv-ConvTm : {n : Nat} {G : Ctx n} {A A' : Expr n}
    {M N B : Expr (suc n)} ->
    HasType G A U -> HasType G A' U -> ConvTm G A A' U ->
    ConvTm (extend G A) M N B -> ConvTm (extend G A') M N B
  ctx-conv-ConvTm {M = M} {N = N} {B = B} dA dA' convAA' d =
    let d' = subst-ConvTm (ctx-conv-WtSub dA dA' convAA') (wf-extend dA') d
    in Eq-transport (\ X -> ConvTm (extend _ _) X N B)
         (substExpr-id M)
         (Eq-transport (\ Y -> ConvTm (extend _ _) (substExpr idSub M) Y B)
           (substExpr-id N)
           (Eq-transport (\ Z -> ConvTm (extend _ _) (substExpr idSub M) (substExpr idSub N) Z)
             (substExpr-id B) d'))

  --------------------------------------------------------------------
  -- ren-HasType cases
  --------------------------------------------------------------------

  -- ty-var
  ren-HasType {r = r} rt wfH (ty-var {i = i} _) =
    Eq-transport (\ T -> HasType _ (Var (r i)) T) (rt i)
      (ty-var wfH)

  -- ty-U
  ren-HasType rt wfH (ty-U _) = ty-U wfH

  -- ty-conv
  ren-HasType rt wfH (ty-conv d1 d2 d3) =
    ty-conv (ren-HasType rt wfH d1)
            (ren-ConvTm rt wfH d2)
            (ren-HasType rt wfH d3)

  -- ty-Pi
  ren-HasType {r = r} rt wfH (ty-Pi d1 d2) =
    let d1' = ren-HasType rt wfH d1
    in ty-Pi d1' (ren-HasType (liftRen-RenTypes rt) (wf-extend d1') d2)

  -- ty-Lam
  ren-HasType {r = r} rt wfH (ty-Lam d1 d2 d3) =
    let d1' = ren-HasType rt wfH d1
        wfH' = wf-extend d1'
        rt' = liftRen-RenTypes rt
    in ty-Lam d1' (ren-HasType rt' wfH' d2) (ren-HasType rt' wfH' d3)

  -- ty-App
  ren-HasType {r = r} rt wfH
    (ty-App {A = A} {B = B} {f = f} {a = a} d1 d2 d3 d4) =
    let d1' = ren-HasType rt wfH d1
    in Eq-transport (\ T -> HasType _ (App (renExpr r f) (renExpr r a)) T)
         (Eq-sym (ren-subst1 r B a))
         (ty-App d1' (ren-HasType (liftRen-RenTypes rt) (wf-extend d1') d2)
                 (ren-HasType rt wfH d3) (ren-HasType rt wfH d4))

  --------------------------------------------------------------------
  -- ren-ConvTm cases
  --------------------------------------------------------------------

  -- conv-refl
  ren-ConvTm rt wfH (conv-refl d) = conv-refl (ren-HasType rt wfH d)

  -- conv-sym
  ren-ConvTm rt wfH (conv-sym d) = conv-sym (ren-ConvTm rt wfH d)

  -- conv-trans
  ren-ConvTm rt wfH (conv-trans d1 d2) =
    conv-trans (ren-ConvTm rt wfH d1) (ren-ConvTm rt wfH d2)

  -- conv-conv
  ren-ConvTm rt wfH (conv-conv d1 d2 d3) =
    conv-conv (ren-ConvTm rt wfH d1)
              (ren-ConvTm rt wfH d2)
              (ren-HasType rt wfH d3)

  -- conv-beta
  ren-ConvTm {r = r} rt wfH
    (conv-beta {A = A} {B = B} {M = M} {a = a} d1 d2 d3 d4) =
    let d1' = ren-HasType rt wfH d1
        wfH' = wf-extend d1'
        rt' = liftRen-RenTypes rt
        beta' = conv-beta d1'
                  (ren-HasType rt' wfH' d2)
                  (ren-HasType rt' wfH' d3)
                  (ren-HasType rt wfH d4)
    in Eq-transport
         (\ T -> ConvTm _ (App (Lam (renExpr r A) (renExpr (liftRen r) M))
                               (renExpr r a))
                           (renExpr r (subst1 M a)) T)
         (Eq-sym (ren-subst1 r B a))
         (Eq-transport
           (\ S -> ConvTm _ (App (Lam (renExpr r A) (renExpr (liftRen r) M))
                                 (renExpr r a)) S
                             (subst1 (renExpr (liftRen r) B) (renExpr r a)))
           (Eq-sym (ren-subst1 r M a))
           beta')

  -- conv-Pi
  ren-ConvTm {r = r} rt wfH (conv-Pi {A = A} d1 d2) =
    let dA = fst (typing-ConvTm d1)
        dA' = ren-HasType rt wfH dA
        wfH' = wf-extend dA'
        rt' = liftRen-RenTypes rt
    in conv-Pi (ren-ConvTm rt wfH d1)
               (ren-ConvTm rt' wfH' d2)

  -- conv-funext
  ren-ConvTm {r = r} rt wfH
    (conv-funext {A = A} {B = B} {f = f} {g = g} dA d df dg) =
    let dA' = ren-HasType rt wfH dA
        wfH' = wf-extend dA'
        rt' = liftRen-RenTypes rt
        -- d : ConvTm (extend G A) (App (wkExpr f) (Var fzero))
        --                          (App (wkExpr g) (Var fzero)) B
        -- renExpr (liftRen r) (App (wkExpr f) (Var fzero))
        --   = App (renExpr (liftRen r) (wkExpr f)) (renExpr (liftRen r) (Var fzero))
        --   = App (wkExpr (renExpr r f)) (Var fzero)  [by ren-wk-comm, liftRen r fzero = fzero]
        d'  = ren-ConvTm rt' wfH' d
        -- d' has renExpr'd terms; need to show they match conv-funext shape
        -- renExpr (liftRen r) (wkExpr f) = wkExpr (renExpr r f) by ren-wk-comm
        eqf = ren-wk-comm r f
        eqg = ren-wk-comm r g
        d'' = Eq-transport
                (\ X -> ConvTm (extend _ (renExpr r A))
                  (App X (Var fzero))
                  (App (renExpr (liftRen r) (wkExpr g)) (Var fzero))
                  (renExpr (liftRen r) B))
                eqf d'
        d''' = Eq-transport
                 (\ Y -> ConvTm (extend _ (renExpr r A))
                   (App (wkExpr (renExpr r f)) (Var fzero))
                   (App Y (Var fzero))
                   (renExpr (liftRen r) B))
                 eqg d''
    in conv-funext dA' d''' (ren-HasType rt wfH df) (ren-HasType rt wfH dg)

  -- conv-App-fun
  ren-ConvTm {r = r} rt wfH
    (conv-App-fun {A = A} {B = B} {f = f} {f' = f'} {a = a} dA dB d1 d2) =
    let dA' = ren-HasType rt wfH dA
    in Eq-transport
         (\ T -> ConvTm _ (App (renExpr r f) (renExpr r a))
                           (App (renExpr r f') (renExpr r a)) T)
         (Eq-sym (ren-subst1 r B a))
         (conv-App-fun dA'
           (ren-HasType (liftRen-RenTypes rt) (wf-extend dA') dB)
           (ren-ConvTm rt wfH d1)
           (ren-HasType rt wfH d2))

  -- conv-App-arg
  ren-ConvTm {r = r} rt wfH
    (conv-App-arg {A = A} {B = B} {f = f} {a = a} {a' = a'} dA dB d1 d2) =
    let dA' = ren-HasType rt wfH dA
    in Eq-transport
         (\ T -> ConvTm _ (App (renExpr r f) (renExpr r a))
                           (App (renExpr r f) (renExpr r a')) T)
         (Eq-sym (ren-subst1 r B a))
         (conv-App-arg dA'
           (ren-HasType (liftRen-RenTypes rt) (wf-extend dA') dB)
           (ren-HasType rt wfH d1)
           (ren-ConvTm rt wfH d2))

  --------------------------------------------------------------------
  -- subst-HasType cases
  --------------------------------------------------------------------

  -- ty-var
  subst-HasType ws wfH (ty-var {i = i} _) = ws i

  -- ty-U
  subst-HasType ws wfH (ty-U _) = ty-U wfH

  -- ty-conv
  subst-HasType ws wfH (ty-conv d1 d2 d3) =
    ty-conv (subst-HasType ws wfH d1)
            (subst-ConvTm ws wfH d2)
            (subst-HasType ws wfH d3)

  -- ty-Pi
  subst-HasType {sigma = sigma} ws wfH (ty-Pi {A = A} d1 d2) =
    let d1' = subst-HasType ws wfH d1
    in ty-Pi d1' (subst-HasType (liftSub-WtSub ws wfH d1) (wf-extend d1') d2)

  -- ty-Lam
  subst-HasType {sigma = sigma} ws wfH (ty-Lam {A = A} d1 d2 d3) =
    let d1' = subst-HasType ws wfH d1
        wfH' = wf-extend d1'
        ws' = liftSub-WtSub ws wfH d1
    in ty-Lam d1' (subst-HasType ws' wfH' d2) (subst-HasType ws' wfH' d3)

  -- ty-App
  subst-HasType {sigma = sigma} ws wfH
    (ty-App {A = A} {B = B} {f = f} {a = a} d1 d2 d3 d4) =
    let d1' = subst-HasType ws wfH d1
    in Eq-transport
         (\ T -> HasType _ (App (substExpr sigma f) (substExpr sigma a)) T)
         (subst-subst1-comm sigma B a)
         (ty-App d1' (subst-HasType (liftSub-WtSub ws wfH d1) (wf-extend d1') d2)
                 (subst-HasType ws wfH d3) (subst-HasType ws wfH d4))

  --------------------------------------------------------------------
  -- subst-ConvTm cases
  --------------------------------------------------------------------

  -- conv-refl
  subst-ConvTm ws wfH (conv-refl d) = conv-refl (subst-HasType ws wfH d)

  -- conv-sym
  subst-ConvTm ws wfH (conv-sym d) = conv-sym (subst-ConvTm ws wfH d)

  -- conv-trans
  subst-ConvTm ws wfH (conv-trans d1 d2) =
    conv-trans (subst-ConvTm ws wfH d1) (subst-ConvTm ws wfH d2)

  -- conv-conv
  subst-ConvTm ws wfH (conv-conv d1 d2 d3) =
    conv-conv (subst-ConvTm ws wfH d1)
              (subst-ConvTm ws wfH d2)
              (subst-HasType ws wfH d3)

  -- conv-beta
  subst-ConvTm {sigma = sigma} ws wfH
    (conv-beta {A = A} {B = B} {M = M} {a = a} d1 d2 d3 d4) =
    let d1' = subst-HasType ws wfH d1
        wfH' = wf-extend d1'
        ws' = liftSub-WtSub ws wfH d1
        beta' = conv-beta d1'
                  (subst-HasType ws' wfH' d2)
                  (subst-HasType ws' wfH' d3)
                  (subst-HasType ws wfH d4)
    in Eq-transport
         (\ T -> ConvTm _
           (App (Lam (substExpr sigma A) (substExpr (liftSub sigma) M))
                (substExpr sigma a))
           (substExpr sigma (subst1 M a)) T)
         (subst-subst1-comm sigma B a)
         (Eq-transport
           (\ S -> ConvTm _
             (App (Lam (substExpr sigma A) (substExpr (liftSub sigma) M))
                  (substExpr sigma a)) S
             (subst1 (substExpr (liftSub sigma) B) (substExpr sigma a)))
           (subst-subst1-comm sigma M a)
           beta')

  -- conv-Pi
  subst-ConvTm {sigma = sigma} ws wfH (conv-Pi {A = A} d1 d2) =
    let dA = fst (typing-ConvTm d1)
        dA' = subst-HasType ws wfH dA
    in conv-Pi (subst-ConvTm ws wfH d1)
               (subst-ConvTm (liftSub-WtSub ws wfH dA) (wf-extend dA') d2)

  -- conv-funext
  subst-ConvTm {sigma = sigma} ws wfH
    (conv-funext {A = A} {B = B} {f = f} {g = g} dA d df dg) =
    let dA' = subst-HasType ws wfH dA
        wfH' = wf-extend dA'
        ws' = liftSub-WtSub ws wfH dA
        d' = subst-ConvTm ws' wfH' d
        -- d' : ConvTm (extend H sA)
        --        (App (substExpr (liftSub sigma) (wkExpr f)) (substExpr (liftSub sigma) (Var fzero)))
        --        (App (substExpr (liftSub sigma) (wkExpr g)) (substExpr (liftSub sigma) (Var fzero)))
        --        (substExpr (liftSub sigma) B)
        -- substExpr (liftSub sigma) (wkExpr f) = wkExpr (substExpr sigma f) by subst-wk-comm
        -- substExpr (liftSub sigma) (Var fzero) = Var fzero
        eqf = subst-wk-comm sigma f
        eqg = subst-wk-comm sigma g
        d'' = Eq-transport
                (\ X -> ConvTm (extend _ (substExpr sigma A))
                  (App X (Var fzero))
                  (App (substExpr (liftSub sigma) (wkExpr g)) (Var fzero))
                  (substExpr (liftSub sigma) B))
                eqf d'
        d''' = Eq-transport
                 (\ Y -> ConvTm (extend _ (substExpr sigma A))
                   (App (wkExpr (substExpr sigma f)) (Var fzero))
                   (App Y (Var fzero))
                   (substExpr (liftSub sigma) B))
                 eqg d''
    in conv-funext dA' d'''
         (subst-HasType ws wfH df) (subst-HasType ws wfH dg)

  -- conv-App-fun
  subst-ConvTm {sigma = sigma} ws wfH
    (conv-App-fun {A = A} {B = B} dA dB d1 d2) =
    let dA' = subst-HasType ws wfH dA
    in Eq-transport
         (\ T -> ConvTm _ _ _ T)
         (subst-subst1-comm sigma B _)
         (conv-App-fun dA'
           (subst-HasType (liftSub-WtSub ws wfH dA) (wf-extend dA') dB)
           (subst-ConvTm ws wfH d1)
           (subst-HasType ws wfH d2))

  -- conv-App-arg
  subst-ConvTm {sigma = sigma} ws wfH
    (conv-App-arg {A = A} {B = B} dA dB d1 d2) =
    let dA' = subst-HasType ws wfH dA
    in Eq-transport
         (\ T -> ConvTm _ _ _ T)
         (subst-subst1-comm sigma B _)
         (conv-App-arg dA'
           (subst-HasType (liftSub-WtSub ws wfH dA) (wf-extend dA') dB)
           (subst-HasType ws wfH d1)
           (subst-ConvTm ws wfH d2))

  --------------------------------------------------------------------
  -- typing-ConvTm: extract HasType from ConvTm
  --------------------------------------------------------------------

  -- conv-refl
  typing-ConvTm (conv-refl d) = mkSigma d d

  -- conv-sym
  typing-ConvTm (conv-sym d) =
    let ih = typing-ConvTm d
    in mkSigma (snd ih) (fst ih)

  -- conv-trans
  typing-ConvTm (conv-trans d1 d2) =
    mkSigma (fst (typing-ConvTm d1)) (snd (typing-ConvTm d2))

  -- conv-conv
  typing-ConvTm (conv-conv d1 d2 d3) =
    let ih = typing-ConvTm d1
    in mkSigma (ty-conv (fst ih) d2 d3) (ty-conv (snd ih) d2 d3)

  -- conv-beta
  typing-ConvTm (conv-beta {A = A} {B = B} {M = M} {a = a} d1 d2 d3 d4) =
    mkSigma (ty-App d1 d2 (ty-Lam d1 d2 d3) d4)
            (subst-HasType (subst1-WtSub d1 d4) (typing-WfCtx d1) d3)

  -- conv-Pi
  typing-ConvTm (conv-Pi d1 d2) =
    let dA  = fst (typing-ConvTm d1)
        dA' = snd (typing-ConvTm d1)
        dB  = fst (typing-ConvTm d2)
        dB' = ctx-conv-HasType dA dA' d1 (snd (typing-ConvTm d2))
    in mkSigma (ty-Pi dA dB) (ty-Pi dA' dB')

  -- conv-funext
  typing-ConvTm (conv-funext dA d df dg) = mkSigma df dg

  -- conv-App-fun
  typing-ConvTm (conv-App-fun dA dB d1 d2) =
    let df  = fst (typing-ConvTm d1)
        df' = snd (typing-ConvTm d1)
    in mkSigma (ty-App dA dB df d2) (ty-App dA dB df' d2)

  -- conv-App-arg: need ConvTm G (subst1 B a') (subst1 B a) U for ty-conv
  -- Built via (λx:A.B) applied to a and a', using conv-beta + conv-App-arg
  typing-ConvTm (conv-App-arg {A = A} {B = B} {f = f} {a = a} {a' = a'} dA dB d1 d2) =
    mkSigma (ty-App dA dB d1 da) sndD
    where
      da  = fst (typing-ConvTm d2)
      da' = snd (typing-ConvTm d2)
      wfG = typing-WfCtx dA
      -- HasType G (subst1 B a) U via substitution lemma
      dBa  = subst-HasType (subst1-WtSub dA da) wfG dB
      -- Build ConvTm G (subst1 B a') (subst1 B a) U using U:U trick:
      -- λ(x:A).B : Π(x:A).U, then use conv-beta and conv-App-arg
      dU     = ty-U (wf-extend dA)
      dLamAB = ty-Lam dA dU dB
      -- (λ(x:A).B) a  = subst1 B a  : U  (conv-beta, result type is subst1 U a = U)
      -- (λ(x:A).B) a' = subst1 B a' : U
      beta-a  = conv-beta dA dU dB da
      beta-a' = conv-beta dA dU dB da'
      -- (λ(x:A).B) a conv (λ(x:A).B) a' : U  (conv-App-arg)
      app-conv = conv-App-arg dA dU dLamAB d2
      -- Chain: subst1 B a' ← (Lam A B) a' ← (Lam A B) a → subst1 B a
      convBa'Ba : ConvTm _ (subst1 B a') (subst1 B a) U
      convBa'Ba = conv-trans (conv-sym beta-a')
                    (conv-trans (conv-sym app-conv) beta-a)
      -- HasType G (App f a') (subst1 B a) via ty-conv
      sndD = ty-conv (ty-App dA dB d1 da') convBa'Ba dBa

  -- Helper: build WtSub for subst1Sub a
  subst1-WtSub : {n : Nat} {G : Ctx n} {A a : Expr n} ->
    HasType G A U -> HasType G a A ->
    WtSub G (extend G A) (subst1Sub a)
  subst1-WtSub {G = G} {A = A} {a = a} dA da fzero =
    Eq-transport (\ T -> HasType G a T) (Eq-sym (subst1-wk A a)) da
  subst1-WtSub {G = G} {A = A} {a = a} dA da (fsuc i) =
    Eq-transport (\ T -> HasType G (Var i) T)
      (Eq-sym (subst1-wk (lookup G i) a))
      (ty-var (typing-WfCtx dA))

  -- Helper: extract WfCtx from HasType
  typing-WfCtx : {n : Nat} {G : Ctx n} {M A : Expr n} ->
    HasType G M A -> WfCtx G
  typing-WfCtx (ty-var wf)       = wf
  typing-WfCtx (ty-conv d _ _)   = typing-WfCtx d
  typing-WfCtx (ty-U wf)         = wf
  typing-WfCtx (ty-Pi d _)       = typing-WfCtx d
  typing-WfCtx (ty-Lam d _ _)    = typing-WfCtx d
  typing-WfCtx (ty-App d _ _ _)  = typing-WfCtx d
