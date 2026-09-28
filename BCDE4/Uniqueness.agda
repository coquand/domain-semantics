{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Uniqueness
--
-- The uniqueness lemma (Lemma 4.10 of the Russell/Tarski comparison,
-- cf. ERT.Uniqueness) for T_T with internal levels:
--
--   (types)  Γ ⊢ A type,  Γ ⊢ B type,  |A| = |B|   ⇒   Γ ⊢ A = B
--
--   (terms)  Γ ⊢ u₀ : A₀,  Γ ⊢ u₁ : A₁,  |u₀| = |u₁|   ⇒   either
--              (1) Γ ⊢ A₀ = A₁  and  Γ ⊢ u₀ = u₁ : A₀,  or
--              (2) Γ ⊢ A₀ = U_{n₀},  Γ ⊢ A₁ = U_{n₁}  and the two codes
--                  agree at the join of their universes:
--                    Γ ⊢ ↑^{n₀∨n₁}_{n₀} u₀ = ↑^{n₀∨n₁}_{n₁} u₁ : U_{n₀∨n₁}
--
--   (El)     Γ ⊢ B type,  Γ ⊢ a : U_l,  |B| = |a|   ⇒   Γ ⊢ B = El_l a
--
-- Case (2) replaces Sterbac's "common base code": levels have no least
-- element (bcde.pdf excludes a level 0), so ∅^α : U_α and ∅^β : U_β have
-- no common code below both, but they agree at α ∨ β.  With lifts
-- ↑^m_l for l ⩽ m (and ↑^l_l a = a) the Π-code case needs no case split
-- on the levels of domain and codomain: both agree at the same join.
--
-- In a context with a loop everything is equal (collapse); otherwise
-- universes are injective (BCDE4.TarskiInj).  Loops are decidable
-- (BCDE4.LC.Loop), so each statement first decides the context.
--
-- The binders ⟨ψ⟩t, ⟨α⟩u and t l carry their types (as λ and app do):
-- without these annotations the lemma fails, e.g. ⟨ψ⟩(↑^{n₀}_k v) and
-- ⟨ψ⟩(↑^{n₁}_k v) erase to the same term but have the non-convertible
-- types [ψ]U_{n₀} and [ψ]U_{n₁}.
--
-- The recursion is on the Tarski expressions and derivations (size-
-- change: every cycle decreases some expression or derivation).
------------------------------------------------------------------------

module BCDE4.Uniqueness where

open import BCDE4.Basic
open import BCDE4.Levels
import BCDE4.RussellSyntax as R
open import BCDE4.TarskiSyntax
open import BCDE4.TarskiTyping
import BCDE4.Erasure as E
open import BCDE4.TarskiMeta
open import BCDE4.TarskiLsub using (lsub-ConvTy ; lsk-inst ; lok-inst)
open import BCDE4.TarskiMetaCong using (subst1-cong-Ty)
open import BCDE4.TarskiInj using (U-inj)
open import BCDE4.LC.Loop using (decLoop)

------------------------------------------------------------------------
-- Levels: the join
------------------------------------------------------------------------

leL-supl : {T : LCtx} (l m : LExpr) -> LeL T l (lsup l m)
leL-supl l m = v-trans (v-sym v-assoc) (v-sup v-idem v-refl)

leL-supr : {T : LCtx} (l m : LExpr) -> LeL T m (lsup l m)
leL-supr l m = v-trans v-comm (v-trans v-assoc (v-sup v-refl v-idem))

sup-lub : {T : LCtx} {l m p : LExpr} -> LeL T l p -> LeL T m p -> LeL T (lsup l m) p
sup-lub lp mp = v-trans v-assoc (v-trans (v-sup v-refl mp) lp)

sup-mono : {T : LCtx} {l l' m m' : LExpr} -> LeL T l l' -> LeL T m m' -> LeL T (lsup l m) (lsup l' m')
sup-mono {l' = l'} {m' = m'} ll mm = sup-lub (leL-trans ll (leL-supl l' m')) (leL-trans mm (leL-supr l' m'))

valid-supl : {T : LCtx} {l m : LExpr} -> Valid T l m -> Valid T l (lsup l m)
valid-supl v = v-trans (v-sym v-idem) (v-sup v-refl v)

valid-supr : {T : LCtx} {l m : LExpr} -> Valid T l m -> Valid T m (lsup l m)
valid-supr v = v-trans (v-sym v-idem) (v-sup (v-sym v) v-refl)

------------------------------------------------------------------------
-- Injectivity of the Russell constructors
------------------------------------------------------------------------

private
  R-Pi-inj : {n : Nat} {A A' : R.Expr n} {B B' : R.Expr (suc n)} ->
    Eq (R.Pi A B) (R.Pi A' B') -> Pair (Eq A A') (Eq B B')
  R-Pi-inj refl = mkSigma refl refl

  R-Lam-inj : {n : Nat} {A A' : R.Expr n} {B B' b b' : R.Expr (suc n)} ->
    Eq (R.Lam A B b) (R.Lam A' B' b') -> Pair (Eq A A') (Pair (Eq B B') (Eq b b'))
  R-Lam-inj refl = mkSigma refl (mkSigma refl refl)

  R-App-inj : {n : Nat} {A A' c c' a a' : R.Expr n} {B B' : R.Expr (suc n)} ->
    Eq (R.App A B c a) (R.App A' B' c' a') ->
    Pair (Eq A A') (Pair (Eq B B') (Pair (Eq c c') (Eq a a')))
  R-App-inj refl = mkSigma refl (mkSigma refl (mkSigma refl refl))

  R-Grd-inj : {n : Nat} {c c' : Constr} {A A' : R.Expr n} ->
    Eq (R.Grd c A) (R.Grd c' A') -> Pair (Eq c c') (Eq A A')
  R-Grd-inj refl = mkSigma refl refl

  R-GLam-inj : {n : Nat} {c c' : Constr} {A A' t t' : R.Expr n} ->
    Eq (R.GLam c A t) (R.GLam c' A' t') -> Pair (Eq c c') (Pair (Eq A A') (Eq t t'))
  R-GLam-inj refl = mkSigma refl (mkSigma refl refl)

  R-LPi-inj : {n : Nat} {A A' : R.Expr n} -> Eq (R.LPi A) (R.LPi A') -> Eq A A'
  R-LPi-inj refl = refl

  R-LLam-inj : {n : Nat} {A A' u u' : R.Expr n} ->
    Eq (R.LLam A u) (R.LLam A' u') -> Pair (Eq A A') (Eq u u')
  R-LLam-inj refl = mkSigma refl refl

  R-LApp-inj : {n : Nat} {A A' t t' : R.Expr n} {l l' : LExpr} ->
    Eq (R.LApp A t l) (R.LApp A' t' l') -> Pair (Eq l l') (Pair (Eq A A') (Eq t t'))
  R-LApp-inj refl = mkSigma refl (mkSigma refl refl)

------------------------------------------------------------------------
-- The statement
------------------------------------------------------------------------

-- case (2): both are codes, agreeing at the join of their universes
record Joins {n : Nat} (G : Ctx n) (u₀ u₁ A₀ A₁ : Expr n) : Set where
  constructor mkJoins
  field
    n₀    : LExpr
    n₁    : LExpr
    A₀≡U  : ConvTy G A₀ (U n₀)
    A₁≡U  : ConvTy G A₁ (U n₁)
    agree : ConvTm G (Lift (lsup n₀ n₁) n₀ u₀) (Lift (lsup n₀ n₁) n₁ u₁) (U (lsup n₀ n₁))

Result : {n : Nat} -> Ctx n -> Expr n -> Expr n -> Expr n -> Expr n -> Set
Result G u₀ u₁ A₀ A₁ = Either (Pair (ConvTy G A₀ A₁) (ConvTm G u₀ u₁ A₀)) (Joins G u₀ u₁ A₀ A₁)

DecLoop : {n : Nat} -> Ctx n -> Set
DecLoop G = Either (Loop (lctx G)) (LoopFree (lctx G))

------------------------------------------------------------------------
-- Collapse
------------------------------------------------------------------------

collapse-Ty : {n : Nat} {G : Ctx n} {A B : Expr n} -> Loop (lctx G) -> IsType G A -> IsType G B -> ConvTy G A B
collapse-Ty lp dA dB = conv-Ty-trans (conv-Ty-collapse lp dA) (conv-Ty-sym (conv-Ty-collapse lp dB))

collapse-Tm : {n : Nat} {G : Ctx n} {u₀ u₁ A : Expr n} -> Loop (lctx G) -> HasType G u₀ A -> HasType G u₁ A ->
  ConvTm G u₀ u₁ A
collapse-Tm lp d₀ d₁ =
  conv-trans (conv-collapse lp (typing-IsType d₀) d₀) (conv-sym (conv-collapse lp (typing-IsType d₀) d₁))

collapse-Res : {n : Nat} {G : Ctx n} {u₀ u₁ A₀ A₁ : Expr n} -> Loop (lctx G) ->
  HasType G u₀ A₀ -> HasType G u₁ A₁ -> Result G u₀ u₁ A₀ A₁
collapse-Res lp d₀ d₁ =
  let c = collapse-Ty lp (typing-IsType d₀) (typing-IsType d₁)
  in inl (mkSigma c (collapse-Tm lp d₀ (ty-conv d₁ (conv-Ty-sym c))))

------------------------------------------------------------------------
-- Working with case (2)
------------------------------------------------------------------------

-- an agreement at k persists at every K ⩾ k
liftUp : {n : Nat} {G : Ctx n} {p q k K : LExpr} {u v : Expr n} ->
  LeL (lctx G) p k -> LeL (lctx G) q k -> LeL (lctx G) k K ->
  HasType G u (U p) -> HasType G v (U q) ->
  ConvTm G (Lift k p u) (Lift k q v) (U k) -> ConvTm G (Lift K p u) (Lift K q v) (U K)
liftUp pk qk kK du dv c =
  conv-trans (conv-sym (conv-Lift-Lift pk kK du))
    (conv-trans (conv-cong-Lift kK c) (conv-Lift-Lift qk kK dv))

-- the agreement of two codes of universes U_{n₀}, U_{n₁}, from either case
joinAt : {n : Nat} {G : Ctx n} {u₀ u₁ : Expr n} {n₀ n₁ : LExpr} ->
  HasType G u₀ (U n₀) -> HasType G u₁ (U n₁) -> Result G u₀ u₁ (U n₀) (U n₁) ->
  ConvTm G (Lift (lsup n₀ n₁) n₀ u₀) (Lift (lsup n₀ n₁) n₁ u₁) (U (lsup n₀ n₁))
joinAt {G = G} {u₀} {u₁} {n₀} {n₁} d₀ d₁ r = go (decLoop (lctx G)) r
  where
    go : DecLoop G -> Result G u₀ u₁ (U n₀) (U n₁) ->
      ConvTm G (Lift (lsup n₀ n₁) n₀ u₀) (Lift (lsup n₀ n₁) n₁ u₁) (U (lsup n₀ n₁))
    go (inl lp) _ = collapse-Tm lp (ty-Lift (leL-supl n₀ n₁) d₀) (ty-Lift (leL-supr n₀ n₁) d₁)
    go (inr lf) (inl (mkSigma cTy c)) =
      conv-trans (conv-cong-Lift (leL-supl n₀ n₁) c)
        (conv-Lift-lvl (U-inj lf cTy) v-refl (leL-supl n₀ n₁) (ty-conv d₁ (conv-Ty-sym cTy)))
    go (inr lf) (inr (mkJoins m₀ m₁ e₀ e₁ ag)) =
      let v₀ = U-inj lf e₀
          v₁ = U-inj lf e₁
          vk = v-sup v₀ v₁
      in conv-trans (conv-Lift-lvl v₀ vk (leL-supl n₀ n₁) d₀)
           (conv-trans (conv-conv ag (conv-Ty-U-lvl (typing-WfCtx d₀) (v-sym vk)))
              (conv-sym (conv-Lift-lvl v₁ vk (leL-supr n₀ n₁) d₁)))

-- at a common type the two cases coincide
sameType : {n : Nat} {G : Ctx n} {u₀ u₁ A : Expr n} ->
  HasType G u₀ A -> HasType G u₁ A -> Result G u₀ u₁ A A -> ConvTm G u₀ u₁ A
sameType d₀ d₁ (inl p) = snd p
sameType {G = G} {u₀} {u₁} {A} d₀ d₁ (inr j) = go (decLoop (lctx G)) j
  where
    go : DecLoop G -> Joins G u₀ u₁ A A -> ConvTm G u₀ u₁ A
    go (inl lp) _ = collapse-Tm lp d₀ d₁
    go (inr lf) (mkJoins n₀ n₁ e₀ e₁ ag) =
      let v  = U-inj lf (conv-Ty-trans (conv-Ty-sym e₀) e₁)
          w₀ = valid-supl v
          w₁ = valid-supr v
          c  = conv-trans (conv-sym (conv-Lift-refl w₀ (ty-conv d₀ e₀)))
                 (conv-trans ag (conv-Lift-refl w₁ (ty-conv d₁ e₁)))
      in conv-conv c (conv-Ty-trans (conv-Ty-U-lvl (typing-WfCtx d₀) (v-sym w₀)) (conv-Ty-sym e₀))

-- the decodings of two codes that agree at the join
elJoin : {n : Nat} {G : Ctx n} {a₀ a₁ : Expr n} {l₀ l₁ : LExpr} ->
  HasType G a₀ (U l₀) -> HasType G a₁ (U l₁) ->
  ConvTm G (Lift (lsup l₀ l₁) l₀ a₀) (Lift (lsup l₀ l₁) l₁ a₁) (U (lsup l₀ l₁)) ->
  ConvTy G (El l₀ a₀) (El l₁ a₁)
elJoin {l₀ = l₀} {l₁} da₀ da₁ j =
  conv-Ty-trans (conv-Ty-sym (conv-Ty-El-Lift (leL-supl l₀ l₁) da₀))
    (conv-Ty-trans (conv-Ty-El j) (conv-Ty-El-Lift (leL-supr l₀ l₁) da₁))

-- transport of a result along a conversion of either type
convL : {n : Nat} {G : Ctx n} {u₀ u₁ A A₀ A₁ : Expr n} -> Result G u₀ u₁ A A₁ -> ConvTy G A A₀ ->
  Result G u₀ u₁ A₀ A₁
convL (inl (mkSigma cTy ctm)) c = inl (mkSigma (conv-Ty-trans (conv-Ty-sym c) cTy) (conv-conv ctm c))
convL (inr (mkJoins n₀ n₁ e₀ e₁ ag)) c = inr (mkJoins n₀ n₁ (conv-Ty-trans (conv-Ty-sym c) e₀) e₁ ag)

convR : {n : Nat} {G : Ctx n} {u₀ u₁ A A₀ A₁ : Expr n} -> Result G u₀ u₁ A₀ A -> ConvTy G A A₁ ->
  Result G u₀ u₁ A₀ A₁
convR (inl (mkSigma cTy ctm)) c = inl (mkSigma (conv-Ty-trans cTy c) ctm)
convR (inr (mkJoins n₀ n₁ e₀ e₁ ag)) c = inr (mkJoins n₀ n₁ e₀ (conv-Ty-trans (conv-Ty-sym c) e₁) ag)

-- a lift on the left:  ↑^m_l a  against  u₁
uLiftL : {n : Nat} {G : Ctx n} {a u₁ A₁ : Expr n} {m l : LExpr} -> LoopFree (lctx G) ->
  LeL (lctx G) l m -> HasType G a (U l) -> HasType G u₁ A₁ ->
  Result G a u₁ (U l) A₁ -> Result G (Lift m l a) u₁ (U m) A₁
uLiftL {m = m} {l} lf le da d₁ (inl (mkSigma cTy c)) =
  inr (mkJoins m l (conv-Ty-refl (is-U (typing-WfCtx da))) (conv-Ty-sym cTy)
    (conv-trans (conv-Lift-Lift le (leL-supl m l) da) (conv-cong-Lift (leL-trans le (leL-supl m l)) c)))
uLiftL {m = m} {l} lf le da d₁ (inr (mkJoins n₀ n₁ e₀ e₁ ag)) =
  let v₀  = U-inj lf e₀
      K   = lsup m n₁
      lK  = leL-trans le (leL-supl m n₁)
      n₀m = leL-trans (leL-refl (v-sym v₀)) le
  in inr (mkJoins m n₁ (conv-Ty-refl (is-U (typing-WfCtx da))) e₁
       (conv-trans (conv-Lift-Lift le (leL-supl m n₁) da)
         (conv-trans (conv-Lift-lvl v₀ v-refl lK da)
           (liftUp (leL-supl n₀ n₁) (leL-supr n₀ n₁) (sup-mono n₀m (leL-refl v-refl))
              (ty-conv da e₀) (ty-conv d₁ e₁) ag))))

-- a lift on the right:  u₀  against  ↑^m_l a
uLiftR : {n : Nat} {G : Ctx n} {u₀ a A₀ : Expr n} {m l : LExpr} -> LoopFree (lctx G) ->
  LeL (lctx G) l m -> HasType G u₀ A₀ -> HasType G a (U l) ->
  Result G u₀ a A₀ (U l) -> Result G u₀ (Lift m l a) A₀ (U m)
uLiftR {m = m} {l} lf le d₀ da (inl (mkSigma cTy c)) =
  inr (mkJoins l m cTy (conv-Ty-refl (is-U (typing-WfCtx da)))
    (conv-trans (conv-cong-Lift (leL-supl l m) (conv-conv c cTy))
                (conv-sym (conv-Lift-Lift le (leL-supr l m) da))))
uLiftR {m = m} {l} lf le d₀ da (inr (mkJoins n₀ n₁ e₀ e₁ ag)) =
  let v₁  = U-inj lf e₁
      lK  = leL-trans le (leL-supr n₀ m)
      n₁m = leL-trans (leL-refl (v-sym v₁)) le
  in inr (mkJoins n₀ m e₀ (conv-Ty-refl (is-U (typing-WfCtx da)))
       (conv-trans (liftUp (leL-supl n₀ n₁) (leL-supr n₀ n₁) (sup-mono (leL-refl v-refl) n₁m)
                      (ty-conv d₀ e₀) (ty-conv da e₁) ag)
         (conv-trans (conv-sym (conv-Lift-lvl v₁ v-refl lK da))
           (conv-sym (conv-Lift-Lift le (leL-supr n₀ m) da)))))

------------------------------------------------------------------------
-- The mutual induction
------------------------------------------------------------------------

term-uniq : {n : Nat} {G : Ctx n} {u₀ u₁ A₀ A₁ : Expr n} ->
  HasType G u₀ A₀ -> HasType G u₁ A₁ -> Eq (E.erase u₀) (E.erase u₁) -> Result G u₀ u₁ A₀ A₁
type-uniq : {n : Nat} {G : Ctx n} {A B : Expr n} ->
  IsType G A -> IsType G B -> Eq (E.erase A) (E.erase B) -> ConvTy G A B
uniq-El : {n : Nat} {G : Ctx n} {B a T : Expr n} {l : LExpr} ->
  IsType G B -> HasType G a T -> ConvTy G T (U l) -> Eq (E.erase B) (E.erase a) -> ConvTy G B (El l a)

term-uniqF : {n : Nat} {G : Ctx n} {u₀ u₁ A₀ A₁ : Expr n} -> DecLoop G ->
  HasType G u₀ A₀ -> HasType G u₁ A₁ -> Eq (E.erase u₀) (E.erase u₁) -> Result G u₀ u₁ A₀ A₁
type-uniqF : {n : Nat} {G : Ctx n} {A B : Expr n} -> DecLoop G ->
  IsType G A -> IsType G B -> Eq (E.erase A) (E.erase B) -> ConvTy G A B
uniq-ElF : {n : Nat} {G : Ctx n} {B a T : Expr n} {l : LExpr} -> DecLoop G ->
  IsType G B -> HasType G a T -> ConvTy G T (U l) -> Eq (E.erase B) (E.erase a) -> ConvTy G B (El l a)

-- the same with the code first (keeps the order of the arguments of type-uniq)
uniq-ElL : {n : Nat} {G : Ctx n} {a T B : Expr n} {l : LExpr} ->
  HasType G a T -> ConvTy G T (U l) -> IsType G B -> Eq (E.erase a) (E.erase B) -> ConvTy G (El l a) B
uniq-ElLF : {n : Nat} {G : Ctx n} {a T B : Expr n} {l : LExpr} -> DecLoop G ->
  HasType G a T -> ConvTy G T (U l) -> IsType G B -> Eq (E.erase a) (E.erase B) -> ConvTy G (El l a) B

tuVar : {n : Nat} {G : Ctx n} {i : Fin n} {u₁ A₁ : Expr n} -> LoopFree (lctx G) -> HasType G (Var i) (lookup G i) -> WfCtx G ->
  HasType G u₁ A₁ -> Eq (R.Var i) (E.erase u₁) -> Result G (Var i) u₁ (lookup G i) A₁
tuLam : {n : Nat} {G : Ctx n} {A₀ : Expr n} {B₀ b₀ : Expr (suc n)} {u₁ A₁ : Expr n} -> LoopFree (lctx G) -> HasType G (Lam A₀ B₀ b₀) (Pi A₀ B₀) ->
  IsType G A₀ -> IsType (extend G A₀) B₀ -> HasType (extend G A₀) b₀ B₀ ->
  HasType G u₁ A₁ -> Eq (E.erase (Lam A₀ B₀ b₀)) (E.erase u₁) -> Result G (Lam A₀ B₀ b₀) u₁ (Pi A₀ B₀) A₁
tuApp : {n : Nat} {G : Ctx n} {A₀ c₀ a₀ : Expr n} {B₀ : Expr (suc n)} {u₁ A₁ : Expr n} -> LoopFree (lctx G) -> HasType G (App A₀ B₀ c₀ a₀) (subst1 B₀ a₀) ->
  IsType G A₀ -> IsType (extend G A₀) B₀ -> HasType G c₀ (Pi A₀ B₀) -> HasType G a₀ A₀ ->
  HasType G u₁ A₁ -> Eq (E.erase (App A₀ B₀ c₀ a₀)) (E.erase u₁) ->
  Result G (App A₀ B₀ c₀ a₀) u₁ (subst1 B₀ a₀) A₁
tuGLam : {n : Nat} {G : Ctx n} {c : Constr} {A₀ t₀ u₁ A₁ : Expr n} -> LoopFree (lctx G) -> HasType G (GLam c A₀ t₀) (Grd c A₀) ->
  WfCtx G -> IsType (addC G c) A₀ -> HasType (addC G c) t₀ A₀ ->
  HasType G u₁ A₁ -> Eq (E.erase (GLam c A₀ t₀)) (E.erase u₁) -> Result G (GLam c A₀ t₀) u₁ (Grd c A₀) A₁
tuLLam : {n : Nat} {G : Ctx n} {A₀ t₀ u₁ A₁ : Expr n} -> LoopFree (lctx G) -> HasType G (LLam A₀ t₀) (LPi A₀) ->
  WfCtx G -> IsType (addL G) A₀ -> HasType (addL G) t₀ A₀ ->
  HasType G u₁ A₁ -> Eq (E.erase (LLam A₀ t₀)) (E.erase u₁) -> Result G (LLam A₀ t₀) u₁ (LPi A₀) A₁
tuLApp : {n : Nat} {G : Ctx n} {A₀ t₀ u₁ A₁ : Expr n} {l : LExpr} -> LoopFree (lctx G) -> HasType G (LApp A₀ t₀ l) (lsub1 A₀ l) ->
  IsType (addL G) A₀ -> HasType G t₀ (LPi A₀) ->
  HasType G u₁ A₁ -> Eq (E.erase (LApp A₀ t₀ l)) (E.erase u₁) -> Result G (LApp A₀ t₀ l) u₁ (lsub1 A₀ l) A₁
tuPiCode : {n : Nat} {G : Ctx n} {a₀ : Expr n} {b₀ : Expr (suc n)} {l₀ : LExpr} {u₁ A₁ : Expr n} -> LoopFree (lctx G) -> HasType G (PiCode l₀ a₀ b₀) (U l₀) ->
  HasType G a₀ (U l₀) -> HasType (extend G (El l₀ a₀)) b₀ (U l₀) ->
  HasType G u₁ A₁ -> Eq (E.erase (PiCode l₀ a₀ b₀)) (E.erase u₁) -> Result G (PiCode l₀ a₀ b₀) u₁ (U l₀) A₁
tuUCode : {n : Nat} {G : Ctx n} {m l : LExpr} {u₁ A₁ : Expr n} -> LoopFree (lctx G) -> HasType G (UCode m l) (U m) ->
  WfCtx G -> LtL (lctx G) l m ->
  HasType G u₁ A₁ -> Eq (R.U l) (E.erase u₁) -> Result G (UCode m l) u₁ (U m) A₁
tuEmpCode : {n : Nat} {G : Ctx n} {l : LExpr} {u₁ A₁ : Expr n} -> LoopFree (lctx G) -> HasType G (EmpCode l) (U l) ->
  WfCtx G ->
  HasType G u₁ A₁ -> Eq R.Emp (E.erase u₁) -> Result G (EmpCode l) u₁ (U l) A₁
uLam : {n : Nat} {G : Ctx n} {A₀ A₁ : Expr n} {B₀ b₀ B₁ b₁ : Expr (suc n)} -> LoopFree (lctx G) ->
  IsType G A₀ -> IsType (extend G A₀) B₀ -> HasType (extend G A₀) b₀ B₀ ->
  IsType G A₁ -> IsType (extend G A₁) B₁ -> HasType (extend G A₁) b₁ B₁ ->
  Pair (Eq (E.erase A₀) (E.erase A₁)) (Pair (Eq (E.erase B₀) (E.erase B₁)) (Eq (E.erase b₀) (E.erase b₁))) ->
  Result G (Lam A₀ B₀ b₀) (Lam A₁ B₁ b₁) (Pi A₀ B₀) (Pi A₁ B₁)
uApp : {n : Nat} {G : Ctx n} {A₀ c₀ a₀ A₁ c₁ a₁ : Expr n} {B₀ B₁ : Expr (suc n)} -> LoopFree (lctx G) ->
  IsType G A₀ -> IsType (extend G A₀) B₀ -> HasType G c₀ (Pi A₀ B₀) -> HasType G a₀ A₀ ->
  IsType G A₁ -> IsType (extend G A₁) B₁ -> HasType G c₁ (Pi A₁ B₁) -> HasType G a₁ A₁ ->
  Pair (Eq (E.erase A₀) (E.erase A₁)) (Pair (Eq (E.erase B₀) (E.erase B₁))
    (Pair (Eq (E.erase c₀) (E.erase c₁)) (Eq (E.erase a₀) (E.erase a₁)))) ->
  Result G (App A₀ B₀ c₀ a₀) (App A₁ B₁ c₁ a₁) (subst1 B₀ a₀) (subst1 B₁ a₁)
uGLam : {n : Nat} {G : Ctx n} {c c' : Constr} {A₀ t₀ A₁ t₁ : Expr n} -> Eq c c' -> LoopFree (lctx G) ->
  WfCtx G -> IsType (addC G c) A₀ -> HasType (addC G c) t₀ A₀ ->
  IsType (addC G c') A₁ -> HasType (addC G c') t₁ A₁ ->
  Eq (E.erase A₀) (E.erase A₁) -> Eq (E.erase t₀) (E.erase t₁) ->
  Result G (GLam c A₀ t₀) (GLam c' A₁ t₁) (Grd c A₀) (Grd c' A₁)
uLLam : {n : Nat} {G : Ctx n} {A₀ u₀ A₁ u₁ : Expr n} -> LoopFree (lctx G) ->
  WfCtx G -> IsType (addL G) A₀ -> HasType (addL G) u₀ A₀ ->
  IsType (addL G) A₁ -> HasType (addL G) u₁ A₁ ->
  Pair (Eq (E.erase A₀) (E.erase A₁)) (Eq (E.erase u₀) (E.erase u₁)) ->
  Result G (LLam A₀ u₀) (LLam A₁ u₁) (LPi A₀) (LPi A₁)
uLApp : {n : Nat} {G : Ctx n} {A₀ t₀ A₁ t₁ : Expr n} {l l' : LExpr} -> Eq l l' -> LoopFree (lctx G) ->
  IsType (addL G) A₀ -> HasType G t₀ (LPi A₀) -> IsType (addL G) A₁ -> HasType G t₁ (LPi A₁) ->
  Eq (E.erase A₀) (E.erase A₁) -> Eq (E.erase t₀) (E.erase t₁) ->
  Result G (LApp A₀ t₀ l) (LApp A₁ t₁ l') (lsub1 A₀ l) (lsub1 A₁ l')
uPiCode : {n : Nat} {G : Ctx n} {a₀ a₁ : Expr n} {b₀ b₁ : Expr (suc n)} {l₀ l₁ : LExpr} -> LoopFree (lctx G) ->
  HasType G a₀ (U l₀) -> HasType (extend G (El l₀ a₀)) b₀ (U l₀) ->
  HasType G a₁ (U l₁) -> HasType (extend G (El l₁ a₁)) b₁ (U l₁) ->
  Pair (Eq (E.erase a₀) (E.erase a₁)) (Eq (E.erase b₀) (E.erase b₁)) ->
  Result G (PiCode l₀ a₀ b₀) (PiCode l₁ a₁ b₁) (U l₀) (U l₁)
tyU : {n : Nat} {G : Ctx n} {l : LExpr} {B : Expr n} -> LoopFree (lctx G) -> IsType G (U l) -> WfCtx G ->
  IsType G B -> Eq (E.erase (U l)) (E.erase B) -> ConvTy G (U l) B
tyPi : {n : Nat} {G : Ctx n} {A₀ : Expr n} {B₀ : Expr (suc n)} {B : Expr n} -> LoopFree (lctx G) -> IsType G (Pi A₀ B₀) ->
  IsType G A₀ -> IsType (extend G A₀) B₀ ->
  IsType G B -> Eq (E.erase (Pi A₀ B₀)) (E.erase B) -> ConvTy G (Pi A₀ B₀) B
tyGrd : {n : Nat} {G : Ctx n} {c : Constr} {A₀ : Expr n} {B : Expr n} -> LoopFree (lctx G) -> IsType G (Grd c A₀) ->
  WfCtx G -> IsType (addC G c) A₀ ->
  IsType G B -> Eq (E.erase (Grd c A₀)) (E.erase B) -> ConvTy G (Grd c A₀) B
tyLPi : {n : Nat} {G : Ctx n} {A₀ : Expr n} {B : Expr n} -> LoopFree (lctx G) -> IsType G (LPi A₀) ->
  WfCtx G -> IsType (addL G) A₀ ->
  IsType G B -> Eq (E.erase (LPi A₀)) (E.erase B) -> ConvTy G (LPi A₀) B
tyEmp : {n : Nat} {G : Ctx n} {B : Expr n} -> LoopFree (lctx G) -> IsType G (Emp) -> WfCtx G ->
  IsType G B -> Eq (E.erase (Emp)) (E.erase B) -> ConvTy G (Emp) B
uGrd : {n : Nat} {G : Ctx n} {c c' : Constr} {A₀ A₁ : Expr n} -> Eq c c' ->
  WfCtx G -> IsType (addC G c) A₀ -> IsType (addC G c') A₁ -> Eq (E.erase A₀) (E.erase A₁) ->
  ConvTy G (Grd c A₀) (Grd c' A₁)
ueU : {n : Nat} {G : Ctx n} {l : LExpr} {a T : Expr n} {l' : LExpr} -> LoopFree (lctx G) -> IsType G (U l) -> WfCtx G ->
  HasType G a T -> ConvTy G T (U l') -> Eq (E.erase (U l)) (E.erase a) -> ConvTy G (U l) (El l' a)
uePi : {n : Nat} {G : Ctx n} {A₀ : Expr n} {B₀ : Expr (suc n)} {a T : Expr n} {l' : LExpr} -> LoopFree (lctx G) -> IsType G (Pi A₀ B₀) ->
  IsType G A₀ -> IsType (extend G A₀) B₀ ->
  HasType G a T -> ConvTy G T (U l') -> Eq (E.erase (Pi A₀ B₀)) (E.erase a) -> ConvTy G (Pi A₀ B₀) (El l' a)
ueGrd : {n : Nat} {G : Ctx n} {c : Constr} {A₀ : Expr n} {a T : Expr n} {l' : LExpr} -> LoopFree (lctx G) -> IsType G (Grd c A₀) ->
  WfCtx G -> IsType (addC G c) A₀ ->
  HasType G a T -> ConvTy G T (U l') -> Eq (E.erase (Grd c A₀)) (E.erase a) -> ConvTy G (Grd c A₀) (El l' a)
ueLPi : {n : Nat} {G : Ctx n} {A₀ : Expr n} {a T : Expr n} {l' : LExpr} -> LoopFree (lctx G) -> IsType G (LPi A₀) ->
  WfCtx G -> IsType (addL G) A₀ ->
  HasType G a T -> ConvTy G T (U l') -> Eq (E.erase (LPi A₀)) (E.erase a) -> ConvTy G (LPi A₀) (El l' a)
ueEmp : {n : Nat} {G : Ctx n} {a T : Expr n} {l' : LExpr} -> LoopFree (lctx G) -> IsType G (Emp) -> WfCtx G ->
  HasType G a T -> ConvTy G T (U l') -> Eq (E.erase (Emp)) (E.erase a) -> ConvTy G (Emp) (El l' a)
ueCU : {n : Nat} {G : Ctx n} {l : LExpr} {a T : Expr n} {l' : LExpr} -> LoopFree (lctx G) ->
  HasType G a T -> ConvTy G T (U l') -> IsType G (U l) -> WfCtx G ->
  Eq (E.erase a) (E.erase (U l)) -> ConvTy G (El l' a) (U l)
ueCPi : {n : Nat} {G : Ctx n} {A₀ : Expr n} {B₀ : Expr (suc n)} {a T : Expr n} {l' : LExpr} -> LoopFree (lctx G) ->
  HasType G a T -> ConvTy G T (U l') -> IsType G (Pi A₀ B₀) ->
  IsType G A₀ -> IsType (extend G A₀) B₀ ->
  Eq (E.erase a) (E.erase (Pi A₀ B₀)) -> ConvTy G (El l' a) (Pi A₀ B₀)
ueCGrd : {n : Nat} {G : Ctx n} {c : Constr} {A₀ : Expr n} {a T : Expr n} {l' : LExpr} -> LoopFree (lctx G) ->
  HasType G a T -> ConvTy G T (U l') -> IsType G (Grd c A₀) ->
  WfCtx G -> IsType (addC G c) A₀ ->
  Eq (E.erase a) (E.erase (Grd c A₀)) -> ConvTy G (El l' a) (Grd c A₀)
ueCLPi : {n : Nat} {G : Ctx n} {A₀ : Expr n} {a T : Expr n} {l' : LExpr} -> LoopFree (lctx G) ->
  HasType G a T -> ConvTy G T (U l') -> IsType G (LPi A₀) ->
  WfCtx G -> IsType (addL G) A₀ ->
  Eq (E.erase a) (E.erase (LPi A₀)) -> ConvTy G (El l' a) (LPi A₀)
ueCEmp : {n : Nat} {G : Ctx n} {a T : Expr n} {l' : LExpr} -> LoopFree (lctx G) ->
  HasType G a T -> ConvTy G T (U l') -> IsType G (Emp) -> WfCtx G ->
  Eq (E.erase a) (E.erase (Emp)) -> ConvTy G (El l' a) (Emp)

term-uniq {G = G} d₀ d₁ e = term-uniqF (decLoop (lctx G)) d₀ d₁ e
uniq-ElL {G = G} d cT dB e = uniq-ElLF (decLoop (lctx G)) d cT dB e
type-uniq {G = G} dA dB e = type-uniqF (decLoop (lctx G)) dA dB e
uniq-El {G = G} dB d cT e = uniq-ElF (decLoop (lctx G)) dB d cT e

term-uniqF {G = G} (inl lp) d₀ d₁ e = collapse-Res lp d₀ d₁
term-uniqF (inr lf) (ty-conv d c) d₁ e = convL (term-uniqF (inr lf) d d₁ e) c
term-uniqF (inr lf) (ty-collapse lp _) d₁ e = absurd (lf lp)
term-uniqF (inr lf) (ty-Lift le da) d₁ e = uLiftL lf le da d₁ (term-uniq da d₁ e)
term-uniqF (inr lf) d₀@(ty-var dG) d₁ e = tuVar lf d₀ dG d₁ e
term-uniqF (inr lf) d₀@(ty-Lam dA₀ dB₀ db₀) d₁ e = tuLam lf d₀ dA₀ dB₀ db₀ d₁ e
term-uniqF (inr lf) d₀@(ty-App dA₀ dB₀ dc₀ da₀) d₁ e = tuApp lf d₀ dA₀ dB₀ dc₀ da₀ d₁ e
term-uniqF (inr lf) d₀@(ty-GLam dG dA₀ dt₀) d₁ e = tuGLam lf d₀ dG dA₀ dt₀ d₁ e
term-uniqF (inr lf) d₀@(ty-LLam dG dA₀ du₀) d₁ e = tuLLam lf d₀ dG dA₀ du₀ d₁ e
term-uniqF (inr lf) d₀@(ty-LApp dA₀ dt₀) d₁ e = tuLApp lf d₀ dA₀ dt₀ d₁ e
term-uniqF (inr lf) d₀@(ty-PiCode da₀ db₀) d₁ e = tuPiCode lf d₀ da₀ db₀ d₁ e
term-uniqF (inr lf) d₀@(ty-UCode dG lt₀) d₁ e = tuUCode lf d₀ dG lt₀ d₁ e
term-uniqF (inr lf) d₀@(ty-EmpCode dG) d₁ e = tuEmpCode lf d₀ dG d₁ e

tuVar lf d₀ dG (ty-conv d c) e = convR (term-uniqF (inr lf) d₀ d e) c
tuVar lf d₀ dG (ty-collapse lp _) e = absurd (lf lp)
tuVar lf d₀ dG (ty-Lift le da) e = uLiftR lf le d₀ da (term-uniq d₀ da e)
tuVar lf _ dG (ty-var {i = i} dG') refl =
  inl (mkSigma (conv-Ty-refl (wfCtx-lookup dG i)) (conv-refl (ty-var dG)))
tuVar lf _ dG (ty-Lam _ _ _) ()
tuVar lf _ dG (ty-App _ _ _ _) ()
tuVar lf _ dG (ty-GLam _ _ _) ()
tuVar lf _ dG (ty-LLam _ _ _) ()
tuVar lf _ dG (ty-LApp _ _) ()
tuVar lf _ dG (ty-PiCode _ _) ()
tuVar lf _ dG (ty-UCode _ _) ()
tuVar lf _ dG (ty-EmpCode _) ()

tuLam lf d₀ dA₀ dB₀ db₀ (ty-conv d c) e = convR (term-uniqF (inr lf) d₀ d e) c
tuLam lf d₀ dA₀ dB₀ db₀ (ty-collapse lp _) e = absurd (lf lp)
tuLam lf d₀ dA₀ dB₀ db₀ (ty-Lift le da) e = uLiftR lf le d₀ da (term-uniq d₀ da e)
tuLam lf _ dA₀ dB₀ db₀ (ty-Lam dA₁ dB₁ db₁) e = uLam lf dA₀ dB₀ db₀ dA₁ dB₁ db₁ (R-Lam-inj e)
tuLam lf _ dA₀ dB₀ db₀ (ty-var _) ()
tuLam lf _ dA₀ dB₀ db₀ (ty-App _ _ _ _) ()
tuLam lf _ dA₀ dB₀ db₀ (ty-GLam _ _ _) ()
tuLam lf _ dA₀ dB₀ db₀ (ty-LLam _ _ _) ()
tuLam lf _ dA₀ dB₀ db₀ (ty-LApp _ _) ()
tuLam lf _ dA₀ dB₀ db₀ (ty-PiCode _ _) ()
tuLam lf _ dA₀ dB₀ db₀ (ty-UCode _ _) ()
tuLam lf _ dA₀ dB₀ db₀ (ty-EmpCode _) ()

tuApp lf d₀ dA₀ dB₀ dc₀ da₀ (ty-conv d c) e = convR (term-uniqF (inr lf) d₀ d e) c
tuApp lf d₀ dA₀ dB₀ dc₀ da₀ (ty-collapse lp _) e = absurd (lf lp)
tuApp lf d₀ dA₀ dB₀ dc₀ da₀ (ty-Lift le da) e = uLiftR lf le d₀ da (term-uniq d₀ da e)
tuApp lf _ dA₀ dB₀ dc₀ da₀ (ty-App dA₁ dB₁ dc₁ da₁) e = uApp lf dA₀ dB₀ dc₀ da₀ dA₁ dB₁ dc₁ da₁ (R-App-inj e)
tuApp lf _ dA₀ dB₀ dc₀ da₀ (ty-var _) ()
tuApp lf _ dA₀ dB₀ dc₀ da₀ (ty-Lam _ _ _) ()
tuApp lf _ dA₀ dB₀ dc₀ da₀ (ty-GLam _ _ _) ()
tuApp lf _ dA₀ dB₀ dc₀ da₀ (ty-LLam _ _ _) ()
tuApp lf _ dA₀ dB₀ dc₀ da₀ (ty-LApp _ _) ()
tuApp lf _ dA₀ dB₀ dc₀ da₀ (ty-PiCode _ _) ()
tuApp lf _ dA₀ dB₀ dc₀ da₀ (ty-UCode _ _) ()
tuApp lf _ dA₀ dB₀ dc₀ da₀ (ty-EmpCode _) ()

tuGLam lf d₀ dG dA₀ dt₀ (ty-conv d c) e = convR (term-uniqF (inr lf) d₀ d e) c
tuGLam lf d₀ dG dA₀ dt₀ (ty-collapse lp _) e = absurd (lf lp)
tuGLam lf d₀ dG dA₀ dt₀ (ty-Lift le da) e = uLiftR lf le d₀ da (term-uniq d₀ da e)
tuGLam lf _ dG dA₀ dt₀ (ty-GLam _ dA₁ dt₁) e =
  uGLam (fst (R-GLam-inj e)) lf dG dA₀ dt₀ dA₁ dt₁ (fst (snd (R-GLam-inj e))) (snd (snd (R-GLam-inj e)))
tuGLam lf _ dG dA₀ dt₀ (ty-var _) ()
tuGLam lf _ dG dA₀ dt₀ (ty-Lam _ _ _) ()
tuGLam lf _ dG dA₀ dt₀ (ty-App _ _ _ _) ()
tuGLam lf _ dG dA₀ dt₀ (ty-LLam _ _ _) ()
tuGLam lf _ dG dA₀ dt₀ (ty-LApp _ _) ()
tuGLam lf _ dG dA₀ dt₀ (ty-PiCode _ _) ()
tuGLam lf _ dG dA₀ dt₀ (ty-UCode _ _) ()
tuGLam lf _ dG dA₀ dt₀ (ty-EmpCode _) ()

tuLLam lf d₀ dG dA₀ du₀ (ty-conv d c) e = convR (term-uniqF (inr lf) d₀ d e) c
tuLLam lf d₀ dG dA₀ du₀ (ty-collapse lp _) e = absurd (lf lp)
tuLLam lf d₀ dG dA₀ du₀ (ty-Lift le da) e = uLiftR lf le d₀ da (term-uniq d₀ da e)
tuLLam lf _ dG dA₀ du₀ (ty-LLam _ dA₁ du₁) e = uLLam lf dG dA₀ du₀ dA₁ du₁ (R-LLam-inj e)
tuLLam lf _ dG dA₀ du₀ (ty-var _) ()
tuLLam lf _ dG dA₀ du₀ (ty-Lam _ _ _) ()
tuLLam lf _ dG dA₀ du₀ (ty-App _ _ _ _) ()
tuLLam lf _ dG dA₀ du₀ (ty-GLam _ _ _) ()
tuLLam lf _ dG dA₀ du₀ (ty-LApp _ _) ()
tuLLam lf _ dG dA₀ du₀ (ty-PiCode _ _) ()
tuLLam lf _ dG dA₀ du₀ (ty-UCode _ _) ()
tuLLam lf _ dG dA₀ du₀ (ty-EmpCode _) ()

tuLApp lf d₀ dA₀ dt₀ (ty-conv d c) e = convR (term-uniqF (inr lf) d₀ d e) c
tuLApp lf d₀ dA₀ dt₀ (ty-collapse lp _) e = absurd (lf lp)
tuLApp lf d₀ dA₀ dt₀ (ty-Lift le da) e = uLiftR lf le d₀ da (term-uniq d₀ da e)
tuLApp lf _ dA₀ dt₀ (ty-LApp dA₁ dt₁) e =
  uLApp (fst (R-LApp-inj e)) lf dA₀ dt₀ dA₁ dt₁ (fst (snd (R-LApp-inj e))) (snd (snd (R-LApp-inj e)))
tuLApp lf _ dA₀ dt₀ (ty-var _) ()
tuLApp lf _ dA₀ dt₀ (ty-Lam _ _ _) ()
tuLApp lf _ dA₀ dt₀ (ty-App _ _ _ _) ()
tuLApp lf _ dA₀ dt₀ (ty-GLam _ _ _) ()
tuLApp lf _ dA₀ dt₀ (ty-LLam _ _ _) ()
tuLApp lf _ dA₀ dt₀ (ty-PiCode _ _) ()
tuLApp lf _ dA₀ dt₀ (ty-UCode _ _) ()
tuLApp lf _ dA₀ dt₀ (ty-EmpCode _) ()

tuPiCode lf d₀ da₀ db₀ (ty-conv d c) e = convR (term-uniqF (inr lf) d₀ d e) c
tuPiCode lf d₀ da₀ db₀ (ty-collapse lp _) e = absurd (lf lp)
tuPiCode lf d₀ da₀ db₀ (ty-Lift le da) e = uLiftR lf le d₀ da (term-uniq d₀ da e)
tuPiCode lf _ da₀ db₀ (ty-PiCode da₁ db₁) e = uPiCode lf da₀ db₀ da₁ db₁ (R-Pi-inj e)
tuPiCode lf _ da₀ db₀ (ty-var _) ()
tuPiCode lf _ da₀ db₀ (ty-Lam _ _ _) ()
tuPiCode lf _ da₀ db₀ (ty-App _ _ _ _) ()
tuPiCode lf _ da₀ db₀ (ty-GLam _ _ _) ()
tuPiCode lf _ da₀ db₀ (ty-LLam _ _ _) ()
tuPiCode lf _ da₀ db₀ (ty-LApp _ _) ()
tuPiCode lf _ da₀ db₀ (ty-UCode _ _) ()
tuPiCode lf _ da₀ db₀ (ty-EmpCode _) ()

tuUCode lf d₀ dG lt₀ (ty-conv d c) e = convR (term-uniqF (inr lf) d₀ d e) c
tuUCode lf d₀ dG lt₀ (ty-collapse lp _) e = absurd (lf lp)
tuUCode lf d₀ dG lt₀ (ty-Lift le da) e = uLiftR lf le d₀ da (term-uniq d₀ da e)
tuUCode {m = m₀} {l} lf _ dG lt₀ (ty-UCode {m = m₁} _ lt₁) refl =
  inr (mkJoins m₀ m₁ (conv-Ty-refl (is-U dG)) (conv-Ty-refl (is-U dG))
    (conv-trans (conv-Lift-UCode dG lt₀ (leL-supl m₀ m₁)) (conv-sym (conv-Lift-UCode dG lt₁ (leL-supr m₀ m₁)))))
tuUCode lf _ dG lt₀ (ty-var _) ()
tuUCode lf _ dG lt₀ (ty-Lam _ _ _) ()
tuUCode lf _ dG lt₀ (ty-App _ _ _ _) ()
tuUCode lf _ dG lt₀ (ty-GLam _ _ _) ()
tuUCode lf _ dG lt₀ (ty-LLam _ _ _) ()
tuUCode lf _ dG lt₀ (ty-LApp _ _) ()
tuUCode lf _ dG lt₀ (ty-PiCode _ _) ()
tuUCode lf _ dG lt₀ (ty-EmpCode _) ()

tuEmpCode lf d₀ dG (ty-conv d c) e = convR (term-uniqF (inr lf) d₀ d e) c
tuEmpCode lf d₀ dG (ty-collapse lp _) e = absurd (lf lp)
tuEmpCode lf d₀ dG (ty-Lift le da) e = uLiftR lf le d₀ da (term-uniq d₀ da e)
tuEmpCode {l = l₀} lf _ dG (ty-EmpCode {l = l₁} _) refl =
  inr (mkJoins l₀ l₁ (conv-Ty-refl (is-U dG)) (conv-Ty-refl (is-U dG))
    (conv-trans (conv-Lift-EmpCode dG (leL-supl l₀ l₁)) (conv-sym (conv-Lift-EmpCode dG (leL-supr l₀ l₁)))))
tuEmpCode lf _ dG (ty-var _) ()
tuEmpCode lf _ dG (ty-Lam _ _ _) ()
tuEmpCode lf _ dG (ty-App _ _ _ _) ()
tuEmpCode lf _ dG (ty-GLam _ _ _) ()
tuEmpCode lf _ dG (ty-LLam _ _ _) ()
tuEmpCode lf _ dG (ty-LApp _ _) ()
tuEmpCode lf _ dG (ty-PiCode _ _) ()
tuEmpCode lf _ dG (ty-UCode _ _) ()

uLam lf dA₀ dB₀ db₀ dA₁ dB₁ db₁ (mkSigma eA (mkSigma eB eb)) =
  let cA   = type-uniq dA₀ dA₁ eA
      dB₁' = ctx-conv-IsType dA₁ dA₀ (conv-Ty-sym cA) dB₁
      db₁' = ctx-conv-HasType dA₁ dA₀ (conv-Ty-sym cA) db₁
      cB   = type-uniq dB₀ dB₁' eB
      db₁'' = ty-conv db₁' (conv-Ty-sym cB)
      cb   = sameType db₀ db₁'' (term-uniq db₀ db₁'' eb)
  in inl (mkSigma (conv-Ty-Pi dA₀ dB₀ cA cB)
       (conv-trans (conv-cong-Lam-body dA₀ dB₀ db₀ cb) (conv-cong-Lam-Ty dA₀ dB₀ cA cB (presup-r-ConvTm cb))))

uApp lf dA₀ dB₀ dc₀ da₀ dA₁ dB₁ dc₁ da₁ (mkSigma eA (mkSigma eB (mkSigma ec ea))) =
  let cA   = type-uniq dA₀ dA₁ eA
      dB₁' = ctx-conv-IsType dA₁ dA₀ (conv-Ty-sym cA) dB₁
      cB   = type-uniq dB₀ dB₁' eB
      dc₁' = ty-conv dc₁ (conv-Ty-sym (conv-Ty-Pi dA₀ dB₀ cA cB))
      cc   = sameType dc₀ dc₁' (term-uniq dc₀ dc₁' ec)
      da₁' = ty-conv da₁ (conv-Ty-sym cA)
      ca   = sameType da₀ da₁' (term-uniq da₀ da₁' ea)
      cBa  = subst1-cong-Ty ca dA₀ dB₀
      cBB  = subst-ConvTy (subst1-WtSub dA₀ da₁') (typing-WfCtx da₀) cB
  in inl (mkSigma (conv-Ty-trans cBa cBB)
       (conv-trans (conv-cong-App-fun dA₀ dB₀ cc da₀)
         (conv-trans (conv-cong-App-arg dA₀ dB₀ dc₁' ca cBa)
           (conv-conv (conv-cong-App-Ty dA₀ dB₀ cA cB dc₁' da₁') (conv-Ty-sym cBa)))))

uGLam refl lf dG dA₀ dt₀ dA₁ dt₁ eA et =
  let cA   = type-uniq dA₀ dA₁ eA
      dt₁' = ty-conv dt₁ (conv-Ty-sym cA)
      ct   = sameType dt₀ dt₁' (term-uniq dt₀ dt₁' et)
  in inl (mkSigma (conv-Ty-Grd dG dA₀ cA)
       (conv-trans (conv-cong-GLam dG dA₀ dt₀ ct) (conv-cong-GLam-Ty dG dA₀ cA (presup-r-ConvTm ct))))

uLLam lf dG dA₀ du₀ dA₁ du₁ (mkSigma eA eu) =
  let cA   = type-uniq dA₀ dA₁ eA
      du₁' = ty-conv du₁ (conv-Ty-sym cA)
      cu   = sameType du₀ du₁' (term-uniq du₀ du₁' eu)
  in inl (mkSigma (conv-Ty-LPi dG dA₀ cA)
       (conv-trans (conv-cong-LLam dG dA₀ du₀ cu) (conv-cong-LLam-Ty dG dA₀ cA (presup-r-ConvTm cu))))

uLApp {G = G} {l = l} refl lf dA₀ dt₀ dA₁ dt₁ eA et =
  let cA   = type-uniq dA₀ dA₁ eA
      dt₁' = ty-conv dt₁ (conv-Ty-sym (conv-Ty-LPi (typing-WfCtx dt₀) dA₀ cA))
      ct   = sameType dt₀ dt₁' (term-uniq dt₀ dt₁' et)
  in inl (mkSigma (lsub-ConvTy (lsk-inst G l) (lok-inst G l) cA)
       (conv-trans (conv-cong-LApp-fun {l = l} dA₀ ct) (conv-cong-LApp-Ty {l = l} dA₀ cA (presup-r-ConvTm ct))))

uPiCode {l₀ = l₀} {l₁} lf da₀ db₀ da₁ db₁ (mkSigma ea eb) =
  let ja   = joinAt da₀ da₁ (term-uniq da₀ da₁ ea)
      cEl  = elJoin da₀ da₁ ja
      db₁' = ctx-conv-HasType (isType-El da₁) (isType-El da₀) (conv-Ty-sym cEl) db₁
      jb   = joinAt db₀ db₁' (term-uniq db₀ db₁' eb)
      -- the lifted domain, and the codomain moved over it
      la₀  = ty-Lift (leL-supl l₀ l₁) da₀
      cE₀  = conv-Ty-sym (conv-Ty-El-Lift (leL-supl l₀ l₁) da₀)
      lb₀  = ctx-conv-HasType (isType-El da₀) (isType-El la₀) cE₀ (ty-Lift (leL-supl l₀ l₁) db₀)
      jb'  = ctx-conv-ConvTm (isType-El da₀) (isType-El la₀) cE₀ jb
      wf   = typing-WfCtx da₀
  in inr (mkJoins l₀ l₁ (conv-Ty-refl (is-U wf)) (conv-Ty-refl (is-U wf))
       (conv-trans (conv-Lift-PiCode (leL-supl l₀ l₁) da₀ db₀)
         (conv-trans (conv-cong-PiCode la₀ lb₀ ja jb')
           (conv-sym (conv-Lift-PiCode (leL-supr l₀ l₁) da₁ db₁)))))

type-uniqF (inl lp) dA dB e = collapse-Ty lp dA dB
type-uniqF (inr lf) (is-El da) dB e = uniq-ElL da (conv-Ty-refl (is-U (typing-WfCtx da))) dB e
type-uniqF (inr lf) dA@(is-U dG) dB e = tyU lf dA dG dB e
type-uniqF (inr lf) dA@(is-Pi dA₀ dB₀) dB e = tyPi lf dA dA₀ dB₀ dB e
type-uniqF (inr lf) dA@(is-Grd dG dA₀) dB e = tyGrd lf dA dG dA₀ dB e
type-uniqF (inr lf) dA@(is-LPi dG dA₀) dB e = tyLPi lf dA dG dA₀ dB e
type-uniqF (inr lf) dA@(is-Emp dG) dB e = tyEmp lf dA dG dB e

tyU lf dA dG (is-El da) e = uniq-El dA da (conv-Ty-refl (is-U (typing-WfCtx da))) e
tyU lf _ dG (is-U _) refl = conv-Ty-refl (is-U dG)
tyU lf _ dG (is-Pi _ _) ()
tyU lf _ dG (is-Grd _ _) ()
tyU lf _ dG (is-LPi _ _) ()
tyU lf _ dG (is-Emp _) ()

tyPi lf dA dA₀ dB₀ (is-El da) e = uniq-El dA da (conv-Ty-refl (is-U (typing-WfCtx da))) e
tyPi lf _ dA₀ dB₀ (is-Pi dA₁ dB₁) e =
  let cA   = type-uniq dA₀ dA₁ (fst (R-Pi-inj e))
      dB₁' = ctx-conv-IsType dA₁ dA₀ (conv-Ty-sym cA) dB₁
  in conv-Ty-Pi dA₀ dB₀ cA (type-uniq dB₀ dB₁' (snd (R-Pi-inj e)))
tyPi lf _ dA₀ dB₀ (is-U _) ()
tyPi lf _ dA₀ dB₀ (is-Grd _ _) ()
tyPi lf _ dA₀ dB₀ (is-LPi _ _) ()
tyPi lf _ dA₀ dB₀ (is-Emp _) ()

tyGrd lf dA dG dA₀ (is-El da) e = uniq-El dA da (conv-Ty-refl (is-U (typing-WfCtx da))) e
tyGrd lf _ dG dA₀ (is-Grd _ dA₁) e = uGrd (fst (R-Grd-inj e)) dG dA₀ dA₁ (snd (R-Grd-inj e))
tyGrd lf _ dG dA₀ (is-U _) ()
tyGrd lf _ dG dA₀ (is-Pi _ _) ()
tyGrd lf _ dG dA₀ (is-LPi _ _) ()
tyGrd lf _ dG dA₀ (is-Emp _) ()

tyLPi lf dA dG dA₀ (is-El da) e = uniq-El dA da (conv-Ty-refl (is-U (typing-WfCtx da))) e
tyLPi lf _ dG dA₀ (is-LPi _ dA₁) e = conv-Ty-LPi dG dA₀ (type-uniq dA₀ dA₁ (R-LPi-inj e))
tyLPi lf _ dG dA₀ (is-U _) ()
tyLPi lf _ dG dA₀ (is-Pi _ _) ()
tyLPi lf _ dG dA₀ (is-Grd _ _) ()
tyLPi lf _ dG dA₀ (is-Emp _) ()

tyEmp lf dA dG (is-El da) e = uniq-El dA da (conv-Ty-refl (is-U (typing-WfCtx da))) e
tyEmp lf _ dG (is-Emp _) refl = conv-Ty-refl (is-Emp dG)
tyEmp lf _ dG (is-U _) ()
tyEmp lf _ dG (is-Pi _ _) ()
tyEmp lf _ dG (is-Grd _ _) ()
tyEmp lf _ dG (is-LPi _ _) ()

uGrd refl dG dA₀ dA₁ e = conv-Ty-Grd dG dA₀ (type-uniq dA₀ dA₁ e)

uniq-ElF (inl lp) dB d cT e = collapse-Ty lp dB (isType-El (ty-conv d cT))
uniq-ElF (inr lf) (is-El db) d cT e =
  let d' = ty-conv d cT in elJoin db d' (joinAt db d' (convR (term-uniq db d e) cT))
uniq-ElF (inr lf) dB@(is-U dG) d cT e = ueU lf dB dG d cT e
uniq-ElF (inr lf) dB@(is-Pi dA₀ dB₀) d cT e = uePi lf dB dA₀ dB₀ d cT e
uniq-ElF (inr lf) dB@(is-Grd dG dA₀) d cT e = ueGrd lf dB dG dA₀ d cT e
uniq-ElF (inr lf) dB@(is-LPi dG dA₀) d cT e = ueLPi lf dB dG dA₀ d cT e
uniq-ElF (inr lf) dB@(is-Emp dG) d cT e = ueEmp lf dB dG d cT e

ueU lf dB dG (ty-conv d c) cT e = ueU lf dB dG d (conv-Ty-trans c cT) e
ueU lf dB dG (ty-collapse lp _) cT e = absurd (lf lp)
ueU lf dB dG (ty-Lift le da) cT e =
  conv-Ty-trans (uniq-El dB da (conv-Ty-refl (is-U (typing-WfCtx da))) e)
    (conv-Ty-trans (conv-Ty-sym (conv-Ty-El-Lift le da)) (conv-Ty-El-lvl (U-inj lf cT) (ty-Lift le da)))
ueU lf _ dG (ty-UCode dG' lt) cT refl =
  conv-Ty-trans (conv-Ty-sym (conv-Ty-El-UCode dG' lt)) (conv-Ty-El-lvl (U-inj lf cT) (ty-UCode dG' lt))
ueU lf _ dG (ty-var _) cT ()
ueU lf _ dG (ty-Lam _ _ _) cT ()
ueU lf _ dG (ty-App _ _ _ _) cT ()
ueU lf _ dG (ty-GLam _ _ _) cT ()
ueU lf _ dG (ty-LLam _ _ _) cT ()
ueU lf _ dG (ty-LApp _ _) cT ()
ueU lf _ dG (ty-PiCode _ _) cT ()
ueU lf _ dG (ty-EmpCode _) cT ()

uePi lf dB dA₀ dB₀ (ty-conv d c) cT e = uePi lf dB dA₀ dB₀ d (conv-Ty-trans c cT) e
uePi lf dB dA₀ dB₀ (ty-collapse lp _) cT e = absurd (lf lp)
uePi lf dB dA₀ dB₀ (ty-Lift le da) cT e =
  conv-Ty-trans (uniq-El dB da (conv-Ty-refl (is-U (typing-WfCtx da))) e)
    (conv-Ty-trans (conv-Ty-sym (conv-Ty-El-Lift le da)) (conv-Ty-El-lvl (U-inj lf cT) (ty-Lift le da)))
uePi lf _ dA dB (ty-PiCode da db) cT e =
  let cA  = uniq-El dA da (conv-Ty-refl (is-U (typing-WfCtx da))) (fst (R-Pi-inj e))
      db' = ctx-conv-HasType (isType-El da) dA (conv-Ty-sym cA) db
      cB  = uniq-El dB db' (conv-Ty-refl (is-U (typing-WfCtx db'))) (snd (R-Pi-inj e))
  in conv-Ty-trans (conv-Ty-Pi dA dB cA cB)
       (conv-Ty-trans (conv-Ty-sym (conv-Ty-El-PiCode da db)) (conv-Ty-El-lvl (U-inj lf cT) (ty-PiCode da db)))
uePi lf _ dA₀ dB₀ (ty-var _) cT ()
uePi lf _ dA₀ dB₀ (ty-Lam _ _ _) cT ()
uePi lf _ dA₀ dB₀ (ty-App _ _ _ _) cT ()
uePi lf _ dA₀ dB₀ (ty-GLam _ _ _) cT ()
uePi lf _ dA₀ dB₀ (ty-LLam _ _ _) cT ()
uePi lf _ dA₀ dB₀ (ty-LApp _ _) cT ()
uePi lf _ dA₀ dB₀ (ty-UCode _ _) cT ()
uePi lf _ dA₀ dB₀ (ty-EmpCode _) cT ()

ueGrd lf dB dG dA₀ (ty-conv d c) cT e = ueGrd lf dB dG dA₀ d (conv-Ty-trans c cT) e
ueGrd lf dB dG dA₀ (ty-collapse lp _) cT e = absurd (lf lp)
ueGrd lf dB dG dA₀ (ty-Lift le da) cT e =
  conv-Ty-trans (uniq-El dB da (conv-Ty-refl (is-U (typing-WfCtx da))) e)
    (conv-Ty-trans (conv-Ty-sym (conv-Ty-El-Lift le da)) (conv-Ty-El-lvl (U-inj lf cT) (ty-Lift le da)))
ueGrd lf _ dG dA₀ (ty-var _) cT ()
ueGrd lf _ dG dA₀ (ty-Lam _ _ _) cT ()
ueGrd lf _ dG dA₀ (ty-App _ _ _ _) cT ()
ueGrd lf _ dG dA₀ (ty-GLam _ _ _) cT ()
ueGrd lf _ dG dA₀ (ty-LLam _ _ _) cT ()
ueGrd lf _ dG dA₀ (ty-LApp _ _) cT ()
ueGrd lf _ dG dA₀ (ty-PiCode _ _) cT ()
ueGrd lf _ dG dA₀ (ty-UCode _ _) cT ()
ueGrd lf _ dG dA₀ (ty-EmpCode _) cT ()

ueLPi lf dB dG dA₀ (ty-conv d c) cT e = ueLPi lf dB dG dA₀ d (conv-Ty-trans c cT) e
ueLPi lf dB dG dA₀ (ty-collapse lp _) cT e = absurd (lf lp)
ueLPi lf dB dG dA₀ (ty-Lift le da) cT e =
  conv-Ty-trans (uniq-El dB da (conv-Ty-refl (is-U (typing-WfCtx da))) e)
    (conv-Ty-trans (conv-Ty-sym (conv-Ty-El-Lift le da)) (conv-Ty-El-lvl (U-inj lf cT) (ty-Lift le da)))
ueLPi lf _ dG dA₀ (ty-var _) cT ()
ueLPi lf _ dG dA₀ (ty-Lam _ _ _) cT ()
ueLPi lf _ dG dA₀ (ty-App _ _ _ _) cT ()
ueLPi lf _ dG dA₀ (ty-GLam _ _ _) cT ()
ueLPi lf _ dG dA₀ (ty-LLam _ _ _) cT ()
ueLPi lf _ dG dA₀ (ty-LApp _ _) cT ()
ueLPi lf _ dG dA₀ (ty-PiCode _ _) cT ()
ueLPi lf _ dG dA₀ (ty-UCode _ _) cT ()
ueLPi lf _ dG dA₀ (ty-EmpCode _) cT ()

ueEmp lf dB dG (ty-conv d c) cT e = ueEmp lf dB dG d (conv-Ty-trans c cT) e
ueEmp lf dB dG (ty-collapse lp _) cT e = absurd (lf lp)
ueEmp lf dB dG (ty-Lift le da) cT e =
  conv-Ty-trans (uniq-El dB da (conv-Ty-refl (is-U (typing-WfCtx da))) e)
    (conv-Ty-trans (conv-Ty-sym (conv-Ty-El-Lift le da)) (conv-Ty-El-lvl (U-inj lf cT) (ty-Lift le da)))
ueEmp lf _ dG (ty-EmpCode dG') cT refl =
  conv-Ty-trans (conv-Ty-sym (conv-Ty-El-EmpCode dG')) (conv-Ty-El-lvl (U-inj lf cT) (ty-EmpCode dG'))
ueEmp lf _ dG (ty-var _) cT ()
ueEmp lf _ dG (ty-Lam _ _ _) cT ()
ueEmp lf _ dG (ty-App _ _ _ _) cT ()
ueEmp lf _ dG (ty-GLam _ _ _) cT ()
ueEmp lf _ dG (ty-LLam _ _ _) cT ()
ueEmp lf _ dG (ty-LApp _ _) cT ()
ueEmp lf _ dG (ty-PiCode _ _) cT ()
ueEmp lf _ dG (ty-UCode _ _) cT ()

uniq-ElLF (inl lp) d cT dB e = collapse-Ty lp (isType-El (ty-conv d cT)) dB
uniq-ElLF (inr lf) d cT (is-El db) e =
  let d' = ty-conv d cT in elJoin d' db (joinAt d' db (convL (term-uniq d db e) cT))
uniq-ElLF (inr lf) d cT dB@(is-U dG) e = ueCU lf d cT dB dG e
uniq-ElLF (inr lf) d cT dB@(is-Pi dA₀ dB₀) e = ueCPi lf d cT dB dA₀ dB₀ e
uniq-ElLF (inr lf) d cT dB@(is-Grd dG dA₀) e = ueCGrd lf d cT dB dG dA₀ e
uniq-ElLF (inr lf) d cT dB@(is-LPi dG dA₀) e = ueCLPi lf d cT dB dG dA₀ e
uniq-ElLF (inr lf) d cT dB@(is-Emp dG) e = ueCEmp lf d cT dB dG e

ueCU lf (ty-conv d c) cT dB dG e = ueCU lf d (conv-Ty-trans c cT) dB dG e
ueCU lf (ty-collapse lp _) cT _ dG e = absurd (lf lp)
ueCU lf (ty-Lift le da) cT dB dG e =
  conv-Ty-trans (conv-Ty-sym (conv-Ty-El-lvl (U-inj lf cT) (ty-Lift le da)))
    (conv-Ty-trans (conv-Ty-El-Lift le da) (uniq-ElL da (conv-Ty-refl (is-U (typing-WfCtx da))) dB e))
ueCU lf (ty-UCode dG' lt) cT _ dG refl =
  conv-Ty-trans (conv-Ty-sym (conv-Ty-El-lvl (U-inj lf cT) (ty-UCode dG' lt))) (conv-Ty-El-UCode dG' lt)
ueCU lf (ty-var _) cT _ dG ()
ueCU lf (ty-Lam _ _ _) cT _ dG ()
ueCU lf (ty-App _ _ _ _) cT _ dG ()
ueCU lf (ty-GLam _ _ _) cT _ dG ()
ueCU lf (ty-LLam _ _ _) cT _ dG ()
ueCU lf (ty-LApp _ _) cT _ dG ()
ueCU lf (ty-PiCode _ _) cT _ dG ()
ueCU lf (ty-EmpCode _) cT _ dG ()

ueCPi lf (ty-conv d c) cT dB dA₀ dB₀ e = ueCPi lf d (conv-Ty-trans c cT) dB dA₀ dB₀ e
ueCPi lf (ty-collapse lp _) cT _ dA₀ dB₀ e = absurd (lf lp)
ueCPi lf (ty-Lift le da) cT dB dA₀ dB₀ e =
  conv-Ty-trans (conv-Ty-sym (conv-Ty-El-lvl (U-inj lf cT) (ty-Lift le da)))
    (conv-Ty-trans (conv-Ty-El-Lift le da) (uniq-ElL da (conv-Ty-refl (is-U (typing-WfCtx da))) dB e))
ueCPi lf (ty-PiCode da db) cT _ dA dB e =
  let cA  = uniq-ElL da (conv-Ty-refl (is-U (typing-WfCtx da))) dA (fst (R-Pi-inj e))
      dB' = ctx-conv-IsType dA (isType-El da) (conv-Ty-sym cA) dB
      cB  = uniq-ElL db (conv-Ty-refl (is-U (typing-WfCtx db))) dB' (snd (R-Pi-inj e))
  in conv-Ty-trans (conv-Ty-sym (conv-Ty-El-lvl (U-inj lf cT) (ty-PiCode da db)))
       (conv-Ty-trans (conv-Ty-El-PiCode da db) (conv-Ty-Pi (isType-El da) (isType-El db) cA cB))
ueCPi lf (ty-var _) cT _ dA₀ dB₀ ()
ueCPi lf (ty-Lam _ _ _) cT _ dA₀ dB₀ ()
ueCPi lf (ty-App _ _ _ _) cT _ dA₀ dB₀ ()
ueCPi lf (ty-GLam _ _ _) cT _ dA₀ dB₀ ()
ueCPi lf (ty-LLam _ _ _) cT _ dA₀ dB₀ ()
ueCPi lf (ty-LApp _ _) cT _ dA₀ dB₀ ()
ueCPi lf (ty-UCode _ _) cT _ dA₀ dB₀ ()
ueCPi lf (ty-EmpCode _) cT _ dA₀ dB₀ ()

ueCGrd lf (ty-conv d c) cT dB dG dA₀ e = ueCGrd lf d (conv-Ty-trans c cT) dB dG dA₀ e
ueCGrd lf (ty-collapse lp _) cT _ dG dA₀ e = absurd (lf lp)
ueCGrd lf (ty-Lift le da) cT dB dG dA₀ e =
  conv-Ty-trans (conv-Ty-sym (conv-Ty-El-lvl (U-inj lf cT) (ty-Lift le da)))
    (conv-Ty-trans (conv-Ty-El-Lift le da) (uniq-ElL da (conv-Ty-refl (is-U (typing-WfCtx da))) dB e))
ueCGrd lf (ty-var _) cT _ dG dA₀ ()
ueCGrd lf (ty-Lam _ _ _) cT _ dG dA₀ ()
ueCGrd lf (ty-App _ _ _ _) cT _ dG dA₀ ()
ueCGrd lf (ty-GLam _ _ _) cT _ dG dA₀ ()
ueCGrd lf (ty-LLam _ _ _) cT _ dG dA₀ ()
ueCGrd lf (ty-LApp _ _) cT _ dG dA₀ ()
ueCGrd lf (ty-PiCode _ _) cT _ dG dA₀ ()
ueCGrd lf (ty-UCode _ _) cT _ dG dA₀ ()
ueCGrd lf (ty-EmpCode _) cT _ dG dA₀ ()

ueCLPi lf (ty-conv d c) cT dB dG dA₀ e = ueCLPi lf d (conv-Ty-trans c cT) dB dG dA₀ e
ueCLPi lf (ty-collapse lp _) cT _ dG dA₀ e = absurd (lf lp)
ueCLPi lf (ty-Lift le da) cT dB dG dA₀ e =
  conv-Ty-trans (conv-Ty-sym (conv-Ty-El-lvl (U-inj lf cT) (ty-Lift le da)))
    (conv-Ty-trans (conv-Ty-El-Lift le da) (uniq-ElL da (conv-Ty-refl (is-U (typing-WfCtx da))) dB e))
ueCLPi lf (ty-var _) cT _ dG dA₀ ()
ueCLPi lf (ty-Lam _ _ _) cT _ dG dA₀ ()
ueCLPi lf (ty-App _ _ _ _) cT _ dG dA₀ ()
ueCLPi lf (ty-GLam _ _ _) cT _ dG dA₀ ()
ueCLPi lf (ty-LLam _ _ _) cT _ dG dA₀ ()
ueCLPi lf (ty-LApp _ _) cT _ dG dA₀ ()
ueCLPi lf (ty-PiCode _ _) cT _ dG dA₀ ()
ueCLPi lf (ty-UCode _ _) cT _ dG dA₀ ()
ueCLPi lf (ty-EmpCode _) cT _ dG dA₀ ()

ueCEmp lf (ty-conv d c) cT dB dG e = ueCEmp lf d (conv-Ty-trans c cT) dB dG e
ueCEmp lf (ty-collapse lp _) cT _ dG e = absurd (lf lp)
ueCEmp lf (ty-Lift le da) cT dB dG e =
  conv-Ty-trans (conv-Ty-sym (conv-Ty-El-lvl (U-inj lf cT) (ty-Lift le da)))
    (conv-Ty-trans (conv-Ty-El-Lift le da) (uniq-ElL da (conv-Ty-refl (is-U (typing-WfCtx da))) dB e))
ueCEmp lf (ty-EmpCode dG') cT _ dG refl =
  conv-Ty-trans (conv-Ty-sym (conv-Ty-El-lvl (U-inj lf cT) (ty-EmpCode dG'))) (conv-Ty-El-EmpCode dG')
ueCEmp lf (ty-var _) cT _ dG ()
ueCEmp lf (ty-Lam _ _ _) cT _ dG ()
ueCEmp lf (ty-App _ _ _ _) cT _ dG ()
ueCEmp lf (ty-GLam _ _ _) cT _ dG ()
ueCEmp lf (ty-LLam _ _ _) cT _ dG ()
ueCEmp lf (ty-LApp _ _) cT _ dG ()
ueCEmp lf (ty-PiCode _ _) cT _ dG ()
ueCEmp lf (ty-UCode _ _) cT _ dG ()
