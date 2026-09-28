# Generates BCDE4/Uniqueness.agda
HEAD = r'''{-# OPTIONS --without-K --exact-split #-}

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

term-uniq {G = G} d₀ d₁ e = term-uniqF (decLoop (lctx G)) d₀ d₁ e
uniq-ElL {G = G} d cT dB e = uniq-ElLF (decLoop (lctx G)) d cT dB e
type-uniq {G = G} dA dB e = type-uniqF (decLoop (lctx G)) dA dB e
uniq-El {G = G} dB d cT e = uniq-ElF (decLoop (lctx G)) dB d cT e
'''

# plain term heads: name, pattern-args (left, as bound vars), arity
terms = [
 ('Var',    'ty-var',     ['dG']),
 ('Lam',    'ty-Lam',     ['dA₀','dB₀','db₀']),
 ('App',    'ty-App',     ['dA₀','dB₀','dc₀','da₀']),
 ('GLam',   'ty-GLam',    ['dG','dA₀','dt₀']),
 ('LLam',   'ty-LLam',    ['dG','dA₀','du₀']),
 ('LApp',   'ty-LApp',    ['dA₀','dt₀']),
 ('PiCode', 'ty-PiCode',  ['da₀','db₀']),
 ('UCode',  'ty-UCode',   ['dG','lt₀']),
 ('EmpCode','ty-EmpCode', ['dG']),
]
arity = {c: len(a) for (_, c, a) in terms}

def us(k): return ' '.join(['_']*k)

def split_arg(t):
    t = t.lstrip()
    if t[0] == '(':
        depth = 0
        for i,ch in enumerate(t):
            if ch == '(': depth += 1
            elif ch == ')':
                depth -= 1
                if depth == 0: return t[:i+1], t[i+1:]
    i = 0
    while i < len(t) and t[i] not in ' \n': i += 1
    return t[:i], t[i:]

out = [HEAD]

# term-uniqF dispatch
out.append('''term-uniqF {G = G} (inl lp) d₀ d₁ e = collapse-Res lp d₀ d₁
term-uniqF (inr lf) (ty-conv d c) d₁ e = convL (term-uniqF (inr lf) d d₁ e) c
term-uniqF (inr lf) (ty-collapse lp _) d₁ e = absurd (lf lp)
term-uniqF (inr lf) (ty-Lift le da) d₁ e = uLiftL lf le da d₁ (term-uniq da d₁ e)''')
for (nm, c, args) in terms:
    out.append(f"term-uniqF (inr lf) d₀@({c} {' '.join(args)}) d₁ e = tu{nm} lf d₀ {' '.join(args)} d₁ e")
out.append('')

# per-head functions
sig = {
 'Var': ('{n : Nat} {G : Ctx n} {i : Fin n} {u₁ A₁ : Expr n} -> LoopFree (lctx G) -> WfCtx G ->\n'
         '  HasType G u₁ A₁ -> Eq (R.Var i) (E.erase u₁) -> Result G (Var i) u₁ (lookup G i) A₁'),
 'Lam': ('{n : Nat} {G : Ctx n} {A₀ : Expr n} {B₀ b₀ : Expr (suc n)} {u₁ A₁ : Expr n} -> LoopFree (lctx G) ->\n'
         '  IsType G A₀ -> IsType (extend G A₀) B₀ -> HasType (extend G A₀) b₀ B₀ ->\n'
         '  HasType G u₁ A₁ -> Eq (E.erase (Lam A₀ B₀ b₀)) (E.erase u₁) -> Result G (Lam A₀ B₀ b₀) u₁ (Pi A₀ B₀) A₁'),
 'App': ('{n : Nat} {G : Ctx n} {A₀ c₀ a₀ : Expr n} {B₀ : Expr (suc n)} {u₁ A₁ : Expr n} -> LoopFree (lctx G) ->\n'
         '  IsType G A₀ -> IsType (extend G A₀) B₀ -> HasType G c₀ (Pi A₀ B₀) -> HasType G a₀ A₀ ->\n'
         '  HasType G u₁ A₁ -> Eq (E.erase (App A₀ B₀ c₀ a₀)) (E.erase u₁) ->\n'
         '  Result G (App A₀ B₀ c₀ a₀) u₁ (subst1 B₀ a₀) A₁'),
 'GLam': ('{n : Nat} {G : Ctx n} {c : Constr} {A₀ t₀ u₁ A₁ : Expr n} -> LoopFree (lctx G) ->\n'
          '  WfCtx G -> IsType (addC G c) A₀ -> HasType (addC G c) t₀ A₀ ->\n'
          '  HasType G u₁ A₁ -> Eq (E.erase (GLam c A₀ t₀)) (E.erase u₁) -> Result G (GLam c A₀ t₀) u₁ (Grd c A₀) A₁'),
 'LLam': ('{n : Nat} {G : Ctx n} {A₀ t₀ u₁ A₁ : Expr n} -> LoopFree (lctx G) ->\n'
          '  WfCtx G -> IsType (addL G) A₀ -> HasType (addL G) t₀ A₀ ->\n'
          '  HasType G u₁ A₁ -> Eq (E.erase (LLam A₀ t₀)) (E.erase u₁) -> Result G (LLam A₀ t₀) u₁ (LPi A₀) A₁'),
 'LApp': ('{n : Nat} {G : Ctx n} {A₀ t₀ u₁ A₁ : Expr n} {l : LExpr} -> LoopFree (lctx G) ->\n'
          '  IsType (addL G) A₀ -> HasType G t₀ (LPi A₀) ->\n'
          '  HasType G u₁ A₁ -> Eq (E.erase (LApp A₀ t₀ l)) (E.erase u₁) -> Result G (LApp A₀ t₀ l) u₁ (lsub1 A₀ l) A₁'),
 'PiCode': ('{n : Nat} {G : Ctx n} {a₀ : Expr n} {b₀ : Expr (suc n)} {l₀ : LExpr} {u₁ A₁ : Expr n} -> LoopFree (lctx G) ->\n'
            '  HasType G a₀ (U l₀) -> HasType (extend G (El l₀ a₀)) b₀ (U l₀) ->\n'
            '  HasType G u₁ A₁ -> Eq (E.erase (PiCode l₀ a₀ b₀)) (E.erase u₁) -> Result G (PiCode l₀ a₀ b₀) u₁ (U l₀) A₁'),
 'UCode': ('{n : Nat} {G : Ctx n} {m l : LExpr} {u₁ A₁ : Expr n} -> LoopFree (lctx G) ->\n'
           '  WfCtx G -> LtL (lctx G) l m ->\n'
           '  HasType G u₁ A₁ -> Eq (R.U l) (E.erase u₁) -> Result G (UCode m l) u₁ (U m) A₁'),
 'EmpCode': ('{n : Nat} {G : Ctx n} {l : LExpr} {u₁ A₁ : Expr n} -> LoopFree (lctx G) ->\n'
             '  WfCtx G ->\n'
             '  HasType G u₁ A₁ -> Eq R.Emp (E.erase u₁) -> Result G (EmpCode l) u₁ (U l) A₁'),
}

same = {
 'Var': "tuVar lf dG (ty-var {i = i} dG') refl =\n  inl (mkSigma (conv-Ty-refl (wfCtx-lookup dG i)) (conv-refl (ty-var dG)))",
 'Lam': "tuLam lf dA₀ dB₀ db₀ (ty-Lam dA₁ dB₁ db₁) e = uLam lf dA₀ dB₀ db₀ dA₁ dB₁ db₁ (R-Lam-inj e)",
 'App': "tuApp lf dA₀ dB₀ dc₀ da₀ (ty-App dA₁ dB₁ dc₁ da₁) e = uApp lf dA₀ dB₀ dc₀ da₀ dA₁ dB₁ dc₁ da₁ (R-App-inj e)",
 'GLam': "tuGLam lf dG dA₀ dt₀ (ty-GLam _ dA₁ dt₁) e =\n  uGLam (fst (R-GLam-inj e)) lf dG dA₀ dt₀ dA₁ dt₁ (fst (snd (R-GLam-inj e))) (snd (snd (R-GLam-inj e)))",
 'LLam': "tuLLam lf dG dA₀ du₀ (ty-LLam _ dA₁ du₁) e = uLLam lf dG dA₀ du₀ dA₁ du₁ (R-LLam-inj e)",
 'LApp': "tuLApp lf dA₀ dt₀ (ty-LApp dA₁ dt₁) e =\n  uLApp (fst (R-LApp-inj e)) lf dA₀ dt₀ dA₁ dt₁ (fst (snd (R-LApp-inj e))) (snd (snd (R-LApp-inj e)))",
 'PiCode': "tuPiCode lf da₀ db₀ (ty-PiCode da₁ db₁) e = uPiCode lf da₀ db₀ da₁ db₁ (R-Pi-inj e)",
 'UCode': "tuUCode {m = m₀} {l} lf dG lt₀ (ty-UCode {m = m₁} _ lt₁) refl =\n"
          "  inr (mkJoins m₀ m₁ (conv-Ty-refl (is-U dG)) (conv-Ty-refl (is-U dG))\n"
          "    (conv-trans (conv-Lift-UCode dG lt₀ (leL-supl m₀ m₁)) (conv-sym (conv-Lift-UCode dG lt₁ (leL-supr m₀ m₁)))))",
 'EmpCode': "tuEmpCode {l = l₀} lf dG (ty-EmpCode {l = l₁} _) refl =\n"
            "  inr (mkJoins l₀ l₁ (conv-Ty-refl (is-U dG)) (conv-Ty-refl (is-U dG))\n"
            "    (conv-trans (conv-Lift-EmpCode dG (leL-supl l₀ l₁)) (conv-sym (conv-Lift-EmpCode dG (leL-supr l₀ l₁)))))",
}

import re as _re
for (nm, c, args) in terms:
    a = ' '.join(args)
    sg = sig[nm]
    res = _re.search(r"Result G (.*) u₁ (.*) A₁$", sg)
    # the left term and type, to type the whole derivation
    body = sg.split('Result G ',1)[1]
    u0, rest = split_arg(body)
    _u1, rest = split_arg(rest)
    A0, rest = split_arg(rest)
    sg = sg.replace('-> LoopFree (lctx G) ->', f'-> LoopFree (lctx G) -> HasType G {u0} {A0} ->', 1)
    out.append(f"tu{nm} : {sg}")
    out.append(f"tu{nm} lf d₀ {a} (ty-conv d c) e = convR (term-uniqF (inr lf) d₀ d e) c")
    out.append(f"tu{nm} lf d₀ {a} (ty-collapse lp _) e = absurd (lf lp)")
    out.append(f"tu{nm} lf d₀ {a} (ty-Lift le da) e = uLiftR lf le d₀ da (term-uniq d₀ da e)")
    out.append(same[nm].replace(f"tu{nm} ", f"tu{nm} ", 1).replace(" lf ", " lf _ ", 1))
    for (_, c2, args2) in terms:
        if c2 == c: continue
        out.append(f"tu{nm} lf _ {a} ({c2} {us(len(args2))}) ()")
    out.append('')

# same-head helpers
out.append(r'''uLam : {n : Nat} {G : Ctx n} {A₀ A₁ : Expr n} {B₀ b₀ B₁ b₁ : Expr (suc n)} -> LoopFree (lctx G) ->
  IsType G A₀ -> IsType (extend G A₀) B₀ -> HasType (extend G A₀) b₀ B₀ ->
  IsType G A₁ -> IsType (extend G A₁) B₁ -> HasType (extend G A₁) b₁ B₁ ->
  Pair (Eq (E.erase A₀) (E.erase A₁)) (Pair (Eq (E.erase B₀) (E.erase B₁)) (Eq (E.erase b₀) (E.erase b₁))) ->
  Result G (Lam A₀ B₀ b₀) (Lam A₁ B₁ b₁) (Pi A₀ B₀) (Pi A₁ B₁)
uLam lf dA₀ dB₀ db₀ dA₁ dB₁ db₁ (mkSigma eA (mkSigma eB eb)) =
  let cA   = type-uniq dA₀ dA₁ eA
      dB₁' = ctx-conv-IsType dA₁ dA₀ (conv-Ty-sym cA) dB₁
      db₁' = ctx-conv-HasType dA₁ dA₀ (conv-Ty-sym cA) db₁
      cB   = type-uniq dB₀ dB₁' eB
      db₁'' = ty-conv db₁' (conv-Ty-sym cB)
      cb   = sameType db₀ db₁'' (term-uniq db₀ db₁'' eb)
  in inl (mkSigma (conv-Ty-Pi dA₀ dB₀ cA cB)
       (conv-trans (conv-cong-Lam-body dA₀ dB₀ db₀ cb) (conv-cong-Lam-Ty dA₀ dB₀ cA cB (presup-r-ConvTm cb))))

uApp : {n : Nat} {G : Ctx n} {A₀ c₀ a₀ A₁ c₁ a₁ : Expr n} {B₀ B₁ : Expr (suc n)} -> LoopFree (lctx G) ->
  IsType G A₀ -> IsType (extend G A₀) B₀ -> HasType G c₀ (Pi A₀ B₀) -> HasType G a₀ A₀ ->
  IsType G A₁ -> IsType (extend G A₁) B₁ -> HasType G c₁ (Pi A₁ B₁) -> HasType G a₁ A₁ ->
  Pair (Eq (E.erase A₀) (E.erase A₁)) (Pair (Eq (E.erase B₀) (E.erase B₁))
    (Pair (Eq (E.erase c₀) (E.erase c₁)) (Eq (E.erase a₀) (E.erase a₁)))) ->
  Result G (App A₀ B₀ c₀ a₀) (App A₁ B₁ c₁ a₁) (subst1 B₀ a₀) (subst1 B₁ a₁)
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

uGLam : {n : Nat} {G : Ctx n} {c c' : Constr} {A₀ t₀ A₁ t₁ : Expr n} -> Eq c c' -> LoopFree (lctx G) ->
  WfCtx G -> IsType (addC G c) A₀ -> HasType (addC G c) t₀ A₀ ->
  IsType (addC G c') A₁ -> HasType (addC G c') t₁ A₁ ->
  Eq (E.erase A₀) (E.erase A₁) -> Eq (E.erase t₀) (E.erase t₁) ->
  Result G (GLam c A₀ t₀) (GLam c' A₁ t₁) (Grd c A₀) (Grd c' A₁)
uGLam refl lf dG dA₀ dt₀ dA₁ dt₁ eA et =
  let cA   = type-uniq dA₀ dA₁ eA
      dt₁' = ty-conv dt₁ (conv-Ty-sym cA)
      ct   = sameType dt₀ dt₁' (term-uniq dt₀ dt₁' et)
  in inl (mkSigma (conv-Ty-Grd dG dA₀ cA)
       (conv-trans (conv-cong-GLam dG dA₀ dt₀ ct) (conv-cong-GLam-Ty dG dA₀ cA (presup-r-ConvTm ct))))

uLLam : {n : Nat} {G : Ctx n} {A₀ u₀ A₁ u₁ : Expr n} -> LoopFree (lctx G) ->
  WfCtx G -> IsType (addL G) A₀ -> HasType (addL G) u₀ A₀ ->
  IsType (addL G) A₁ -> HasType (addL G) u₁ A₁ ->
  Pair (Eq (E.erase A₀) (E.erase A₁)) (Eq (E.erase u₀) (E.erase u₁)) ->
  Result G (LLam A₀ u₀) (LLam A₁ u₁) (LPi A₀) (LPi A₁)
uLLam lf dG dA₀ du₀ dA₁ du₁ (mkSigma eA eu) =
  let cA   = type-uniq dA₀ dA₁ eA
      du₁' = ty-conv du₁ (conv-Ty-sym cA)
      cu   = sameType du₀ du₁' (term-uniq du₀ du₁' eu)
  in inl (mkSigma (conv-Ty-LPi dG dA₀ cA)
       (conv-trans (conv-cong-LLam dG dA₀ du₀ cu) (conv-cong-LLam-Ty dG dA₀ cA (presup-r-ConvTm cu))))

uLApp : {n : Nat} {G : Ctx n} {A₀ t₀ A₁ t₁ : Expr n} {l l' : LExpr} -> Eq l l' -> LoopFree (lctx G) ->
  IsType (addL G) A₀ -> HasType G t₀ (LPi A₀) -> IsType (addL G) A₁ -> HasType G t₁ (LPi A₁) ->
  Eq (E.erase A₀) (E.erase A₁) -> Eq (E.erase t₀) (E.erase t₁) ->
  Result G (LApp A₀ t₀ l) (LApp A₁ t₁ l') (lsub1 A₀ l) (lsub1 A₁ l')
uLApp {G = G} {l = l} refl lf dA₀ dt₀ dA₁ dt₁ eA et =
  let cA   = type-uniq dA₀ dA₁ eA
      dt₁' = ty-conv dt₁ (conv-Ty-sym (conv-Ty-LPi (typing-WfCtx dt₀) dA₀ cA))
      ct   = sameType dt₀ dt₁' (term-uniq dt₀ dt₁' et)
  in inl (mkSigma (lsub-ConvTy (lsk-inst G l) (lok-inst G l) cA)
       (conv-trans (conv-cong-LApp-fun {l = l} dA₀ ct) (conv-cong-LApp-Ty {l = l} dA₀ cA (presup-r-ConvTm ct))))

uPiCode : {n : Nat} {G : Ctx n} {a₀ a₁ : Expr n} {b₀ b₁ : Expr (suc n)} {l₀ l₁ : LExpr} -> LoopFree (lctx G) ->
  HasType G a₀ (U l₀) -> HasType (extend G (El l₀ a₀)) b₀ (U l₀) ->
  HasType G a₁ (U l₁) -> HasType (extend G (El l₁ a₁)) b₁ (U l₁) ->
  Pair (Eq (E.erase a₀) (E.erase a₁)) (Eq (E.erase b₀) (E.erase b₁)) ->
  Result G (PiCode l₀ a₀ b₀) (PiCode l₁ a₁ b₁) (U l₀) (U l₁)
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
''')

# type-uniq
tys = [
 ('U',   'is-U',   ['dG']),
 ('Pi',  'is-Pi',  ['dA₀','dB₀']),
 ('Grd', 'is-Grd', ['dG','dA₀']),
 ('LPi', 'is-LPi', ['dG','dA₀']),
 ('Emp', 'is-Emp', ['dG']),
]
out.append('''type-uniqF (inl lp) dA dB e = collapse-Ty lp dA dB
type-uniqF (inr lf) (is-El da) dB e = uniq-ElL da (conv-Ty-refl (is-U (typing-WfCtx da))) dB e''')
for (nm, c, args) in tys:
    out.append(f"type-uniqF (inr lf) dA@({c} {' '.join(args)}) dB e = ty{nm} lf dA {' '.join(args)} dB e")
out.append('')

tysig = {
 'U':   ('{n : Nat} {G : Ctx n} {l : LExpr} {B : Expr n} -> LoopFree (lctx G) -> WfCtx G ->', 'U l'),
 'Pi':  ('{n : Nat} {G : Ctx n} {A₀ : Expr n} {B₀ : Expr (suc n)} {B : Expr n} -> LoopFree (lctx G) ->\n  IsType G A₀ -> IsType (extend G A₀) B₀ ->', 'Pi A₀ B₀'),
 'Grd': ('{n : Nat} {G : Ctx n} {c : Constr} {A₀ : Expr n} {B : Expr n} -> LoopFree (lctx G) ->\n  WfCtx G -> IsType (addC G c) A₀ ->', 'Grd c A₀'),
 'LPi': ('{n : Nat} {G : Ctx n} {A₀ : Expr n} {B : Expr n} -> LoopFree (lctx G) ->\n  WfCtx G -> IsType (addL G) A₀ ->', 'LPi A₀'),
 'Emp': ('{n : Nat} {G : Ctx n} {B : Expr n} -> LoopFree (lctx G) -> WfCtx G ->', 'Emp'),
}
tysame = {
 'U':   "tyU lf dG (is-U _) refl = conv-Ty-refl (is-U dG)",
 'Pi':  ("tyPi lf dA₀ dB₀ (is-Pi dA₁ dB₁) e =\n"
         "  let cA   = type-uniq dA₀ dA₁ (fst (R-Pi-inj e))\n"
         "      dB₁' = ctx-conv-IsType dA₁ dA₀ (conv-Ty-sym cA) dB₁\n"
         "  in conv-Ty-Pi dA₀ dB₀ cA (type-uniq dB₀ dB₁' (snd (R-Pi-inj e)))"),
 'Grd': "tyGrd lf dG dA₀ (is-Grd _ dA₁) e = uGrd (fst (R-Grd-inj e)) dG dA₀ dA₁ (snd (R-Grd-inj e))",
 'LPi': "tyLPi lf dG dA₀ (is-LPi _ dA₁) e = conv-Ty-LPi dG dA₀ (type-uniq dA₀ dA₁ (R-LPi-inj e))",
 'Emp': "tyEmp lf dG (is-Emp _) refl = conv-Ty-refl (is-Emp dG)",
}

for (nm, c, args) in tys:
    s, T = tysig[nm]
    a = ' '.join(args)
    s1 = s.replace('-> LoopFree (lctx G) ->', f'-> LoopFree (lctx G) -> IsType G ({T}) ->', 1)
    out.append(f"ty{nm} : {s1}\n  IsType G B -> Eq (E.erase ({T})) (E.erase B) -> ConvTy G ({T}) B")
    out.append(f"ty{nm} lf dA {a} (is-El da) e = uniq-El dA da (conv-Ty-refl (is-U (typing-WfCtx da))) e")
    out.append(tysame[nm].replace(" lf ", " lf _ ", 1))
    for (_, c2, args2) in tys:
        if c2 == c: continue
        out.append(f"ty{nm} lf _ {a} ({c2} {us(len(args2))}) ()")
    out.append('')

out.append('''uGrd : {n : Nat} {G : Ctx n} {c c' : Constr} {A₀ A₁ : Expr n} -> Eq c c' ->
  WfCtx G -> IsType (addC G c) A₀ -> IsType (addC G c') A₁ -> Eq (E.erase A₀) (E.erase A₁) ->
  ConvTy G (Grd c A₀) (Grd c' A₁)
uGrd refl dG dA₀ dA₁ e = conv-Ty-Grd dG dA₀ (type-uniq dA₀ dA₁ e)
''')

# uniq-El: dispatch on B (El first), then on the code derivation
out.append('''uniq-ElF (inl lp) dB d cT e = collapse-Ty lp dB (isType-El (ty-conv d cT))
uniq-ElF (inr lf) (is-El db) d cT e =
  let d' = ty-conv d cT in elJoin db d' (joinAt db d' (convR (term-uniq db d e) cT))''')
for (nm, c, args) in tys:
    out.append(f"uniq-ElF (inr lf) dB@({c} {' '.join(args)}) d cT e = ue{nm} lf dB {' '.join(args)} d cT e")
out.append('')

uesame = {
 'U': ["ueU lf dG (ty-UCode dG' lt) cT refl =\n"
       "  conv-Ty-trans (conv-Ty-sym (conv-Ty-El-UCode dG' lt)) (conv-Ty-El-lvl (U-inj lf cT) (ty-UCode dG' lt))"],
 'Pi': ["uePi lf dA dB (ty-PiCode da db) cT e =\n"
        "  let cA  = uniq-El dA da (conv-Ty-refl (is-U (typing-WfCtx da))) (fst (R-Pi-inj e))\n"
        "      db' = ctx-conv-HasType (isType-El da) dA (conv-Ty-sym cA) db\n"
        "      cB  = uniq-El dB db' (conv-Ty-refl (is-U (typing-WfCtx db'))) (snd (R-Pi-inj e))\n"
        "  in conv-Ty-trans (conv-Ty-Pi dA dB cA cB)\n"
        "       (conv-Ty-trans (conv-Ty-sym (conv-Ty-El-PiCode da db)) (conv-Ty-El-lvl (U-inj lf cT) (ty-PiCode da db)))"],
 'Grd': [],
 'LPi': [],
 'Emp': ["ueEmp lf dG (ty-EmpCode dG') cT refl =\n"
         "  conv-Ty-trans (conv-Ty-sym (conv-Ty-El-EmpCode dG')) (conv-Ty-El-lvl (U-inj lf cT) (ty-EmpCode dG'))"],
}
uematch = {'U': 'ty-UCode', 'Pi': 'ty-PiCode', 'Emp': 'ty-EmpCode', 'Grd': None, 'LPi': None}
for (nm, c, args) in tys:
    s, T = tysig[nm]
    a = ' '.join(args)
    s2 = s.replace('{B : Expr n}', "{a T : Expr n} {l' : LExpr}")
    s2 = s2.replace('-> LoopFree (lctx G) ->', f'-> LoopFree (lctx G) -> IsType G ({T}) ->', 1)
    out.append(f"ue{nm} : {s2}\n  HasType G a T -> ConvTy G T (U l') -> Eq (E.erase ({T})) (E.erase a) -> ConvTy G ({T}) (El l' a)")
    out.append(f"ue{nm} lf dB {a} (ty-conv d c) cT e = ue{nm} lf dB {a} d (conv-Ty-trans c cT) e")
    out.append(f"ue{nm} lf dB {a} (ty-collapse lp _) cT e = absurd (lf lp)")
    out.append(f"ue{nm} lf dB {a} (ty-Lift le da) cT e =\n"
               f"  conv-Ty-trans (uniq-El dB da (conv-Ty-refl (is-U (typing-WfCtx da))) e)\n"
               f"    (conv-Ty-trans (conv-Ty-sym (conv-Ty-El-Lift le da)) (conv-Ty-El-lvl (U-inj lf cT) (ty-Lift le da)))")
    out.extend([x.replace(" lf ", " lf _ ", 1) for x in uesame[nm]])
    for (_, c2, args2) in terms:
        if c2 == uematch[nm]: continue
        out.append(f"ue{nm} lf _ {a} ({c2} {us(len(args2))}) cT ()")
    out.append('')


out.append("""uniq-ElLF (inl lp) d cT dB e = collapse-Ty lp (isType-El (ty-conv d cT)) dB
uniq-ElLF (inr lf) d cT (is-El db) e =
  let d' = ty-conv d cT in elJoin d' db (joinAt d' db (convL (term-uniq d db e) cT))""")
for (nm, c, args) in tys:
    out.append(f"uniq-ElLF (inr lf) d cT dB@({c} {' '.join(args)}) e = ueC{nm} lf d cT dB {' '.join(args)} e")
out.append('')
ueLsame = {
 'U': ["ueCU lf (ty-UCode dG' lt) cT dG refl =\n"
       "  conv-Ty-trans (conv-Ty-sym (conv-Ty-El-lvl (U-inj lf cT) (ty-UCode dG' lt))) (conv-Ty-El-UCode dG' lt)"],
 'Pi': ["ueCPi lf (ty-PiCode da db) cT dA dB e =\n"
        "  let cA  = uniq-ElL da (conv-Ty-refl (is-U (typing-WfCtx da))) dA (fst (R-Pi-inj e))\n"
        "      dB' = ctx-conv-IsType dA (isType-El da) (conv-Ty-sym cA) dB\n"
        "      cB  = uniq-ElL db (conv-Ty-refl (is-U (typing-WfCtx db))) dB' (snd (R-Pi-inj e))\n"
        "  in conv-Ty-trans (conv-Ty-sym (conv-Ty-El-lvl (U-inj lf cT) (ty-PiCode da db)))\n"
        "       (conv-Ty-trans (conv-Ty-El-PiCode da db) (conv-Ty-Pi (isType-El da) (isType-El db) cA cB))"],
 'Grd': [], 'LPi': [],
 'Emp': ["ueCEmp lf (ty-EmpCode dG') cT dG refl =\n"
         "  conv-Ty-trans (conv-Ty-sym (conv-Ty-El-lvl (U-inj lf cT) (ty-EmpCode dG'))) (conv-Ty-El-EmpCode dG')"],
}
for (nm, c, args) in tys:
    sB, T = tysig[nm]
    a = ' '.join(args)
    pre, post = sB.split('-> LoopFree (lctx G) ->', 1)
    pre = pre.replace('{B : Expr n}', "{a T : Expr n} {l' : LExpr}")
    out.append(f"ueC{nm} : {pre}-> LoopFree (lctx G) ->\n  HasType G a T -> ConvTy G T (U l') -> IsType G ({T}) ->{post}\n"
               f"  Eq (E.erase a) (E.erase ({T})) -> ConvTy G (El l' a) ({T})")
    out.append(f"ueC{nm} lf (ty-conv d c) cT dB {a} e = ueC{nm} lf d (conv-Ty-trans c cT) dB {a} e")
    out.append(f"ueC{nm} lf (ty-collapse lp _) cT _ {a} e = absurd (lf lp)")
    out.append(f"ueC{nm} lf (ty-Lift le da) cT dB {a} e =\n"
               f"  conv-Ty-trans (conv-Ty-sym (conv-Ty-El-lvl (U-inj lf cT) (ty-Lift le da)))\n"
               f"    (conv-Ty-trans (conv-Ty-El-Lift le da) (uniq-ElL da (conv-Ty-refl (is-U (typing-WfCtx da))) dB e))")
    out.extend([_re.sub(r"cT ", "cT _ ", x, count=1) for x in ueLsame[nm]])
    for (_, c2, args2) in terms:
        if c2 == uematch[nm]: continue
        out.append(f"ueC{nm} lf ({c2} {us(len(args2))}) cT _ {a} ()")
    out.append('')

text = '\n'.join(out)
import re
head, rest = text.split("term-uniq {G = G} d₀ d₁ e = term-uniqF",1)
rest = "term-uniq {G = G} d₀ d₁ e = term-uniqF" + rest
lines = rest.split('\n'); sigs=[]; body=[]; i=0
while i < len(lines):
    L=lines[i]
    m=re.match(r"^([A-Za-z][A-Za-z0-9₀₁-]*) : ", L)
    if m:
        sig=[L]; i+=1
        while i < len(lines) and lines[i].startswith('  '):
            sig.append(lines[i]); i+=1
        sigs.append('\n'.join(sig)); continue
    body.append(L); i+=1
open('/Users/coquand/DOMAIN/BCDE4/Uniqueness.agda', 'w').write(head + '\n'.join(sigs) + '\n\n' + '\n'.join(body))

