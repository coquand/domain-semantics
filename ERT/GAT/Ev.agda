{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- ERT.GAT.Ev
--
-- The lifting from T_T to the GAT by evaluation in an environment of
-- GAT terms (sterbac4 §4, ceil(-)).  Port of UNIT/Ev.seg.
--   ev t e     t with variable i read as e i;  up e: q, (e i) p
--   idv        q, q p, q p p, ...;  ceil t = ev t idv
--   ev-ext, ev-ren (raw);  er-ev: |ev t e| = t[|e|];
--   Lemma 17: er-ceil |ceil t| = t,  er-ceilC.
------------------------------------------------------------------------

module ERT.GAT.Ev where

open import ERT.Basic
open import ERT.TarskiSyntax
import ERT.TarskiTyping as TT
open import ERT.TarskiMeta using (idSub ; substExpr-id)
open import ERT.GAT.Syntax
open import ERT.GAT.TLib using (wkS ; ren-as-subst)

Env : Nat -> Nat -> Set
Env n k = Fin n -> GE k

up : {n k : Nat} -> Env n k -> Env (suc n) (suc k)
up e fzero    = gq
up e (fsuc i) = gsb (e i) gp

ev : {n k : Nat} -> Expr n -> Env n k -> GE k
ev (Var i)        e = e i
ev (Pi A B)       e = gpi (ev A e) (ev B (up e))
ev (U l)          e = guu l
ev (El l a)       e = gel l (ev a e)
ev (Lam A B b)    e = glam (ev A e) (ev B (up e)) (ev b (up e))
ev (App A B c a)  e = gapp (ev A e) (ev B (up e)) (ev c e) (ev a e)
ev (PiCode l a b) e = gpic l (ev a e) (ev b (up e))
ev (UCode m l)    e = guc m l
ev (Lift m l a)   e = glf m l (ev a e)

idv : {n : Nat} -> Env n n
idv fzero    = gq
idv (fsuc i) = gsb (idv i) gp

ceil : {n : Nat} -> Expr n -> GE n
ceil t = ev t idv

ceilC : {n : Nat} -> TT.Ctx n -> GC n
ceilC TT.empty        = gnil
ceilC (TT.extend G A) = gext (ceilC G) (ceil A)

------------------------------------------------------------------------
-- pointwise equal environments

GPt : {n k : Nat} -> Env n k -> Env n k -> Set
GPt r r' = (i : Fin _) -> Eq (r i) (r' i)

up-ext : {n k : Nat} (r r' : Env n k) -> GPt r r' -> GPt (up r) (up r')
up-ext r r' e fzero    = refl
up-ext r r' e (fsuc i) = Eq-cong (\ Z -> gsb Z gp) (e i)

ev-ext : {n k : Nat} (t : Expr n) (r r' : Env n k) -> GPt r r' -> Eq (ev t r) (ev t r')
ev-ext (Var i)        r r' e = e i
ev-ext (Pi A B)       r r' e = Eq-cong2 gpi (ev-ext A r r' e) (ev-ext B (up r) (up r') (up-ext r r' e))
ev-ext (U l)          r r' e = refl
ev-ext (El l a)       r r' e = Eq-cong (gel l) (ev-ext a r r' e)
ev-ext (Lam A B b)    r r' e =
  Eq-cong3 glam (ev-ext A r r' e) (ev-ext B (up r) (up r') (up-ext r r' e)) (ev-ext b (up r) (up r') (up-ext r r' e))
ev-ext (App A B c a)  r r' e =
  Eq-cong4 gapp (ev-ext A r r' e) (ev-ext B (up r) (up r') (up-ext r r' e)) (ev-ext c r r' e) (ev-ext a r r' e)
ev-ext (PiCode l a b) r r' e = Eq-cong2 (gpic l) (ev-ext a r r' e) (ev-ext b (up r) (up r') (up-ext r r' e))
ev-ext (UCode m l)    r r' e = refl
ev-ext (Lift m l a)   r r' e = Eq-cong (glf m l) (ev-ext a r r' e)

------------------------------------------------------------------------
-- renaming (raw)

up-ren : {n m k : Nat} (e : Env m k) (r : Ren n m) -> GPt (\ i -> up e (liftRen r i)) (up (\ i -> e (r i)))
up-ren e r fzero    = refl
up-ren e r (fsuc i) = refl

ev-ren : {n m k : Nat} (t : Expr n) (e : Env m k) (r : Ren n m) -> Eq (ev (renExpr r t) e) (ev t (\ i -> e (r i)))
ev-ren (Var i)        e r = refl
ev-ren (Pi A B)       e r =
  Eq-cong2 gpi (ev-ren A e r) (Eq-trans (ev-ren B (up e) (liftRen r)) (ev-ext B _ _ (up-ren e r)))
ev-ren (U l)          e r = refl
ev-ren (El l a)       e r = Eq-cong (gel l) (ev-ren a e r)
ev-ren (Lam A B b)    e r =
  Eq-cong3 glam (ev-ren A e r) (Eq-trans (ev-ren B (up e) (liftRen r)) (ev-ext B _ _ (up-ren e r)))
    (Eq-trans (ev-ren b (up e) (liftRen r)) (ev-ext b _ _ (up-ren e r)))
ev-ren (App A B c a)  e r =
  Eq-cong4 gapp (ev-ren A e r) (Eq-trans (ev-ren B (up e) (liftRen r)) (ev-ext B _ _ (up-ren e r)))
    (ev-ren c e r) (ev-ren a e r)
ev-ren (PiCode l a b) e r =
  Eq-cong2 (gpic l) (ev-ren a e r) (Eq-trans (ev-ren b (up e) (liftRen r)) (ev-ext b _ _ (up-ren e r)))
ev-ren (UCode m l)    e r = refl
ev-ren (Lift m l a)   e r = Eq-cong (glf m l) (ev-ren a e r)

ev-wk : {n k : Nat} (t : Expr n) (e : Env (suc n) k) -> Eq (ev (wkExpr t) e) (ev t (\ i -> e (fsuc i)))
ev-wk t e = ev-ren t e wkRen

------------------------------------------------------------------------
-- erasure of an evaluation; Lemma 17

eE : {n k : Nat} -> Env n k -> Sub k n
eE e i = eT (e i)

er-up : {n k : Nat} (e : Env n k) -> (i : Fin (suc n)) -> Eq (eT (up e i)) (liftSub (eE e) i)
er-up e fzero    = refl
er-up e (fsuc i) = Eq-sym (ren-as-subst wkRen (eT (e i)))

er-bd : {n k : Nat} (B : Expr (suc n)) (e : Env n k) -> Eq (eT (ev B (up e))) (substExpr (eE (up e)) B)
  -> Eq (eT (ev B (up e))) (substExpr (liftSub (eE e)) B)
er-bd B e ih = Eq-trans ih (substExpr-ext _ _ (er-up e) B)

er-ev : {n k : Nat} (t : Expr n) (e : Env n k) -> Eq (eT (ev t e)) (substExpr (eE e) t)
er-ev (Var i)        e = refl
er-ev (Pi A B)       e = Eq-cong2 Pi (er-ev A e) (er-bd B e (er-ev B (up e)))
er-ev (U l)          e = refl
er-ev (El l a)       e = Eq-cong (El l) (er-ev a e)
er-ev (Lam A B b)    e = Eq-cong3 Lam (er-ev A e) (er-bd B e (er-ev B (up e))) (er-bd b e (er-ev b (up e)))
er-ev (App A B c a)  e = Eq-cong4 App (er-ev A e) (er-bd B e (er-ev B (up e))) (er-ev c e) (er-ev a e)
er-ev (PiCode l a b) e = Eq-cong2 (PiCode l) (er-ev a e) (er-bd b e (er-ev b (up e)))
er-ev (UCode m l)    e = refl
er-ev (Lift m l a)   e = Eq-cong (Lift m l) (er-ev a e)

er-idv : {n : Nat} (i : Fin n) -> Eq (eT (idv i)) (Var i)
er-idv fzero    = refl
er-idv (fsuc i) = Eq-cong (substExpr wkS) (er-idv i)

-- Lemma 17 (right inverse, strict)
er-ceil : {n : Nat} (t : Expr n) -> Eq (eT (ceil t)) t
er-ceil t = Eq-trans (er-ev t idv) (Eq-trans (substExpr-ext _ idSub er-idv t) (substExpr-id t))

er-ceilC : {n : Nat} (G : TT.Ctx n) -> Eq (eC (ceilC G)) G
er-ceilC TT.empty        = refl
er-ceilC (TT.extend G A) = Eq-cong2 TT.extend (er-ceilC G) (er-ceil A)
