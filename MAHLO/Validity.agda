{-# OPTIONS --without-K --exact-split --safe #-}

------------------------------------------------------------------------
-- MAHLO/Validity.agda
--
-- Validity of judgements in the PER model (mahlo-plan.tex Sec. 6.4,
-- after Abel--Coquand Sec. 5.3): related environments rho = rho' in
-- [G], and the validity of the five judgement forms.  Also the generic
-- rules (variables, conversion, equivalence) and the semantic
-- introduction and elimination of Pi and Sigma.
------------------------------------------------------------------------

open import MAHLO.Basic
open import MAHLO.TermModel
import MAHLO.Model
import MAHLO.Fixpoint

module MAHLO.Validity (TM : TermModel) (M : MAHLO.Model.Model TM)
                      (Fx : MAHLO.Fixpoint.Fixpoint TM) where

open TermModel TM
open MAHLO.Model TM using (Env ; cons)
open MAHLO.Model.Model M
open import MAHLO.Candidate TM
open MAHLO.Fixpoint TM
open Fixpoint Fx
open Cand V
open import MAHLO.Type TM M Fx public
open import MAHLO.Syntax
  renaming (Pi to tPi ; Sigma to tSigma ; Nat to tNat ; V to tV)
open import MAHLO.Typing

------------------------------------------------------------------------
-- Elements of types
------------------------------------------------------------------------

-- t = t' in [a], where a = b in Type
record TmV (a b t t' : D) : Set1 where
  constructor tmv
  field
    X  : Rel
    ty : TyR a b X
    el : X t t'

tmvTr : {a a2 b b2 t t2 t' t2' : D} -> a ~~ a2 -> b ~~ b2 -> t ~~ t2 -> t' ~~ t2' ->
        TmV a b t t' -> TmV a2 b2 t2 t2'
tmvTr ea eb et et' (tmv X d x) = tmv X (TyR-cl2 ea eb d) (TyR-el2 d et et' x)

tyvTr : {a a2 b b2 : D} -> a ~~ a2 -> b ~~ b2 -> TyV a b -> TyV a2 b2
tyvTr ea eb (tyv X d) = tyv X (TyR-cl2 ea eb d)

-- move the right endpoint of the type
retype : {a b c t t' : D} {Y : Rel} -> TmV a b t t' -> TyR a c Y -> TmV a c t t'
retype (tmv X d x) dY = tmv _ dY (fst (funL d dY) x)

-- read an element at another derivation with the same left endpoint
elAt : {a b c t t' : D} {Y : Rel} -> TmV a b t t' -> TyR a c Y -> Y t t'
elAt p dY = TmV.el (retype p dY)

tmSym : {a b t t' : D} -> TmV a b t t' -> TmV b a t' t
tmSym (tmv X d x) = tmv X (sym d) (IsPER.sy (per d) x)

-- an element of a small type
tmSm : {a b t t' : D} -> R a b -> I a t t' -> TmV a b t t'
tmSm r i = tmv _ (tySm r ~-refl) i

------------------------------------------------------------------------
-- Pairs of Set1
------------------------------------------------------------------------

record _&_ (A B : Set1) : Set1 where
  constructor _,,_
  field
    p1 : A
    p2 : B
open _&_ public

infixr 4 _,,_

record Unit1 : Set1 where
  constructor tt1

------------------------------------------------------------------------
-- Environments
------------------------------------------------------------------------

tl : {n : Num} -> Env (suc n) -> Env n
tl rho i = rho (fsuc i)

EnvR : {n : Num} -> Ctx n -> Env n -> Env n -> Set1
EnvR empty rho rho' = Unit1
EnvR (extend G A) rho rho' =
  EnvR G (tl rho) (tl rho') &
  TmV (den A (tl rho)) (den A (tl rho')) (rho fzero) (rho' fzero)

EnvR-sym : {n : Num} (G : Ctx n) {rho rho' : Env n} -> EnvR G rho rho' -> EnvR G rho' rho
EnvR-sym empty e = tt1
EnvR-sym (extend G A) (e ,, t) = EnvR-sym G e ,, tmSym t

EnvR-trans : {n : Num} (G : Ctx n) {rho rho' rho'' : Env n} ->
             EnvR G rho rho' -> EnvR G rho' rho'' -> EnvR G rho rho''
EnvR-trans empty e e' = tt1
EnvR-trans (extend G A) (e ,, tmv X d x) (e' ,, tmv Y d' y) =
  EnvR-trans G e e' ,,
  tmv X (trans d d') (IsPER.tr (per d) x (snd (funR d (sym d')) y))

EnvR-rl : {n : Num} (G : Ctx n) {rho rho' : Env n} -> EnvR G rho rho' -> EnvR G rho rho
EnvR-rl G e = EnvR-trans G e (EnvR-sym G e)

EnvR-rr : {n : Num} (G : Ctx n) {rho rho' : Env n} -> EnvR G rho rho' -> EnvR G rho' rho'
EnvR-rr G e = EnvR-trans G (EnvR-sym G e) e

envCons : {n : Num} {G : Ctx n} {A : Expr n} {rho rho' : Env n} {v v' : D} ->
          EnvR G rho rho' -> TmV (den A rho) (den A rho') v v' ->
          EnvR (extend G A) (cons rho v) (cons rho' v')
envCons e t = e ,, t

------------------------------------------------------------------------
-- Validity
------------------------------------------------------------------------

ValTy : {n : Num} -> Ctx n -> Expr n -> Set1
ValTy {n} G A = {rho rho' : Env n} -> EnvR G rho rho' -> TyV (den A rho) (den A rho')

ValTm : {n : Num} -> Ctx n -> Expr n -> Expr n -> Set1
ValTm {n} G t A = {rho rho' : Env n} -> EnvR G rho rho' ->
  TmV (den A rho) (den A rho') (den t rho) (den t rho')

ValTyEq : {n : Num} -> Ctx n -> Expr n -> Expr n -> Set1
ValTyEq {n} G A B = {rho rho' : Env n} -> EnvR G rho rho' -> TyV (den A rho) (den B rho')

ValConv : {n : Num} -> Ctx n -> Expr n -> Expr n -> Expr n -> Set1
ValConv {n} G t u A = {rho rho' : Env n} -> EnvR G rho rho' ->
  TmV (den A rho) (den A rho') (den t rho) (den u rho')

ValCtx : {n : Num} -> Ctx n -> Set1
ValCtx empty = Unit1
ValCtx (extend G A) = ValCtx G & ValTy G A

------------------------------------------------------------------------
-- Generic rules
------------------------------------------------------------------------

v-var : {n : Num} (G : Ctx n) (i : Fin n) -> ValTm G (Var i) (lookup G i)
v-var G i e = tmvTr ~~-refl ~~-refl (~~-sym (den-Var i)) (~~-sym (den-Var i)) (look G i e)
  where
    look : {n : Num} (G : Ctx n) (i : Fin n) {rho rho' : Env n} -> EnvR G rho rho' ->
           TmV (den (lookup G i) rho) (den (lookup G i) rho') (rho i) (rho' i)
    look (extend G A) fzero {rho} {rho'} (e ,, t) =
      tmvTr (~~-sym (den-wk rho A)) (~~-sym (den-wk rho' A)) ~~-refl ~~-refl t
    look (extend G A) (fsuc i) {rho} {rho'} (e ,, t) =
      tmvTr (~~-sym (den-wk rho (lookup G i))) (~~-sym (den-wk rho' (lookup G i))) ~~-refl ~~-refl
        (look G i e)

-- the left and the right side of a valid equation are valid
vconv-l : {n : Num} {G : Ctx n} {t u A : Expr n} -> ValConv G t u A -> ValTm G t A
vconv-l {G = G} c e =
  let tmv X d x = c e
      tmv Y d' y = c (EnvR-rr G e)
      XY = funR d d'
  in tmv X d (IsPER.tr (per d) x (snd XY (IsPER.sy (per d') y)))

vconv-r : {n : Num} {G : Ctx n} {t u A : Expr n} -> ValConv G t u A -> ValTm G u A
vconv-r {G = G} c e =
  let tmv X d x = c e
      tmv Y d' y = c (EnvR-rl G e)
      XY = funL d d'
  in tmv X d (IsPER.tr (per d) (snd XY (IsPER.sy (per d') y)) x)

v-tyeq-refl : {n : Num} {G : Ctx n} {A : Expr n} -> ValTy G A -> ValTyEq G A A
v-tyeq-refl h e = h e

v-tyeq-sym : {n : Num} {G : Ctx n} {A B : Expr n} -> ValTyEq G A B -> ValTyEq G B A
v-tyeq-sym {G = G} h e = let tyv X d = h (EnvR-sym G e) in tyv X (sym d)

v-tyeq-trans : {n : Num} {G : Ctx n} {A B C : Expr n} ->
               ValTyEq G A B -> ValTyEq G B C -> ValTyEq G A C
v-tyeq-trans {G = G} h k e =
  let tyv X d = h e
      tyv Y d' = k (EnvR-rr G e)
  in tyv X (trans d d')

-- element of A at rho,rho' and A = B: element of B
private
  conv-sem : {a a' b b' t t' : D} {Z Y : Rel} -> TyR a b Z -> TyR a b' Y ->
             TmV a a' t t' -> TmV b b' t t'
  conv-sem d1 d2 (tmv X d x) = tmv _ (trans (sym d1) d2) (fst (funL d d1) x)

v-ty-conv : {n : Num} {G : Ctx n} {t A B : Expr n} ->
            ValTm G t A -> ValTyEq G A B -> ValTm G t B
v-ty-conv {G = G} vt h e =
  conv-sem (TyV.ty (h (EnvR-rl G e))) (TyV.ty (h e)) (vt e)

v-conv-conv : {n : Num} {G : Ctx n} {t u A B : Expr n} ->
              ValConv G t u A -> ValTyEq G A B -> ValConv G t u B
v-conv-conv {G = G} vt h e =
  conv-sem (TyV.ty (h (EnvR-rl G e))) (TyV.ty (h e)) (vt e)

v-conv-refl : {n : Num} {G : Ctx n} {t A : Expr n} -> ValTm G t A -> ValConv G t t A
v-conv-refl h e = h e

v-conv-sym : {n : Num} {G : Ctx n} {t u A : Expr n} -> ValConv G t u A -> ValConv G u t A
v-conv-sym {G = G} h e = tmSym (h (EnvR-sym G e))

v-conv-trans : {n : Num} {G : Ctx n} {t u w A : Expr n} ->
               ValConv G t u A -> ValConv G u w A -> ValConv G t w A
v-conv-trans {G = G} h k e =
  let tmv X d x = h e
      tmv Y d' y = k (EnvR-rr G e)
  in tmv X d (IsPER.tr (per d) x (snd (funR d d') y))

------------------------------------------------------------------------
-- Semantic Pi and Sigma
------------------------------------------------------------------------

piIntro : {a b A A' F F' t t' : D} {X : Rel} -> TyR a b X ->
          a ~~ Pi A F -> b ~~ Pi A' F' ->
          ((v v' : D) {Y : Rel} -> TyR A A' Y -> Y v v' ->
             TmV (app F v) (app F' v') (app t v) (app t' v')) ->
          X t t'
piIntro d ea eb h =
  snd eX (\ v v' i -> elAt (h v v' dA i) (dF v v' i))
  where open PiInv (invPi d ea eb)

piElim : {a b A A' F F' t t' v v' : D} {X Y : Rel} -> TyR a b X ->
         a ~~ Pi A F -> b ~~ Pi A' F' -> X t t' ->
         TyR A A' Y -> Y v v' -> TmV (app F v) (app F' v') (app t v) (app t' v')
piElim {v = v} {v'} d ea eb x dY y =
  tmv _ (dF v v' i) (fst eX x v v' i)
  where
    open PiInv (invPi d ea eb)
    i = fst (funL dY dA) y

sigIntro : {a b A A' F F' p p' c : D} {X : Rel} -> TyR a b X ->
           a ~~ Sig A F -> b ~~ Sig A' F' ->
           TmV A A' (pr1 p) (pr1 p') ->
           TmV (app F (pr1 p)) c (pr2 p) (pr2 p') ->
           X p p'
sigIntro d ea eb t1 t2 = snd eX (i , elAt t2 (dF _ _ i))
  where
    open SigInv (invSig d ea eb)
    i = elAt t1 dA

sigElim1 : {a b A A' F F' p p' : D} {X : Rel} -> TyR a b X ->
           a ~~ Sig A F -> b ~~ Sig A' F' -> X p p' -> TmV A A' (pr1 p) (pr1 p')
sigElim1 d ea eb x = tmv _ dA (fst (fst eX x))
  where open SigInv (invSig d ea eb)

sigElim2 : {a b A A' F F' p p' : D} {X : Rel} -> TyR a b X ->
           a ~~ Sig A F -> b ~~ Sig A' F' -> X p p' ->
           TmV (app F (pr1 p)) (app F' (pr1 p')) (pr2 p) (pr2 p')
sigElim2 d ea eb x = tmv _ (dF _ _ (fst (fst eX x))) (snd (fst eX x))
  where open SigInv (invSig d ea eb)
