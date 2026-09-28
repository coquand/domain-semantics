{-# OPTIONS --without-K --exact-split #-}

------------------------------------------------------------------------
-- BCDE4.Levels
--
-- Universe level expressions and constraints (bcde.pdf §4-§5):
--
--   l, m ::= α_i | l ∨ m | l⁺            (no least level)
--   ψ    ::= l = m                        (one equation)
--   Θ    ::= list of constraints
--
-- `Valid Θ l m` : l = m holds in the sup-semilattice with an
-- inflationary endomorphism _⁺ presented by the constraints Θ
-- (equational logic: congruence + the axioms + the hypotheses).
--
-- Level variables are de Bruijn indices (bound by level products [α]A);
-- a level context is just a list of constraints.  A context has a LOOP if l⁺ ≤ l is valid for
-- some l (bcde.pdf App. C); the collapse rules fire there.
------------------------------------------------------------------------

module BCDE4.Levels where

open import BCDE4.Basic

------------------------------------------------------------------------
-- Syntax
------------------------------------------------------------------------

data LExpr : Set where
  lvar  : Nat -> LExpr
  lsup  : LExpr -> LExpr -> LExpr
  lnext : LExpr -> LExpr

data Constr : Set where
  ceq : LExpr -> LExpr -> Constr

data LCtx : Set where
  lnil  : LCtx
  lcons : Constr -> LCtx -> LCtx

data LMem (c : Constr) : LCtx -> Set where
  lhere  : {Th : LCtx} -> LMem c (lcons c Th)
  lthere : {d : Constr} {Th : LCtx} -> LMem c Th -> LMem c (lcons d Th)

------------------------------------------------------------------------
-- Derivable equations
------------------------------------------------------------------------

data Valid (Th : LCtx) : LExpr -> LExpr -> Set where
  v-hyp   : {l m : LExpr} -> LMem (ceq l m) Th -> Valid Th l m
  v-refl  : {l : LExpr} -> Valid Th l l
  v-sym   : {l m : LExpr} -> Valid Th l m -> Valid Th m l
  v-trans : {l m p : LExpr} -> Valid Th l m -> Valid Th m p -> Valid Th l p
  v-sup   : {l l' m m' : LExpr} -> Valid Th l l' -> Valid Th m m' ->
            Valid Th (lsup l m) (lsup l' m')
  v-next  : {l l' : LExpr} -> Valid Th l l' -> Valid Th (lnext l) (lnext l')
  v-idem  : {l : LExpr} -> Valid Th (lsup l l) l
  v-comm  : {l m : LExpr} -> Valid Th (lsup l m) (lsup m l)
  v-assoc : {l m p : LExpr} -> Valid Th (lsup (lsup l m) p) (lsup l (lsup m p))
  v-nsup  : {l m : LExpr} -> Valid Th (lnext (lsup l m)) (lsup (lnext l) (lnext m))
  v-infl  : {l : LExpr} -> Valid Th (lsup l (lnext l)) (lnext l)

ValidC : LCtx -> Constr -> Set
ValidC Th (ceq l m) = Valid Th l m

-- the order of levels:  l ⩽ m  iff  l ∨ m = m,   l < m  iff  l⁺ ⩽ m
LeL : LCtx -> LExpr -> LExpr -> Set
LeL Th l m = Valid Th (lsup l m) m

LtL : LCtx -> LExpr -> LExpr -> Set
LtL Th l m = Valid Th (lsup (lnext l) m) m

-- the order is reflexive (up to equality) and transitive
leL-refl : {Th : LCtx} {l m : LExpr} -> Valid Th l m -> LeL Th l m
leL-refl v = v-trans (v-sup v v-refl) v-idem

leL-trans : {Th : LCtx} {l m p : LExpr} -> LeL Th l m -> LeL Th m p -> LeL Th l p
leL-trans {l = l} {m} {p} lm mp =
  -- l ∨ p = l ∨ (m ∨ p) = (l ∨ m) ∨ p = m ∨ p = p
  v-trans (v-sup v-refl (v-sym mp))
    (v-trans (v-sym v-assoc) (v-trans (v-sup lm v-refl) mp))

-- k < l ⩽ m  ⇒  k < m
ltL-leL : {Th : LCtx} {k l m : LExpr} -> LtL Th k l -> LeL Th l m -> LtL Th k m
ltL-leL kl lm = leL-trans kl lm

-- l < m  ⇒  l ⩽ m
ltL-leL' : {Th : LCtx} {l m : LExpr} -> LtL Th l m -> LeL Th l m
ltL-leL' {l = l} {m} lt =
  -- l ∨ m = l ∨ (l⁺ ∨ m) = (l ∨ l⁺) ∨ m = l⁺ ∨ m = m
  v-trans (v-sup v-refl (v-sym lt))
    (v-trans (v-sym v-assoc) (v-trans (v-sup v-infl v-refl) lt))

-- the order respects level equality
leL-resp : {Th : LCtx} {l l' m m' : LExpr} -> Valid Th l l' -> Valid Th m m' -> LeL Th l m -> LeL Th l' m'
leL-resp e f lm = v-trans (v-sup (v-sym e) (v-sym f)) (v-trans lm f)

ltL-resp : {Th : LCtx} {l l' m m' : LExpr} -> Valid Th l l' -> Valid Th m m' -> LtL Th l m -> LtL Th l' m'
ltL-resp e f lm = v-trans (v-sup (v-next (v-sym e)) (v-sym f)) (v-trans lm f)

------------------------------------------------------------------------
-- Loops
------------------------------------------------------------------------

-- l⁺ ≤ l, i.e. l⁺ ∨ l = l
Loop : LCtx -> Set
Loop Th = Sigma LExpr (\ l -> Valid Th (lsup (lnext l) l) l)

LoopFree : LCtx -> Set
LoopFree Th = Loop Th -> Empty

------------------------------------------------------------------------
-- Entailment between level contexts
------------------------------------------------------------------------

Entails : LCtx -> LCtx -> Set
Entails T Th = {c : Constr} -> LMem c Th -> ValidC T c

valid-ent : {T Th : LCtx} {l m : LExpr} -> Entails T Th -> Valid Th l m -> Valid T l m
valid-ent e (v-hyp h)     = e h
valid-ent e v-refl        = v-refl
valid-ent e (v-sym d)     = v-sym (valid-ent e d)
valid-ent e (v-trans d d') = v-trans (valid-ent e d) (valid-ent e d')
valid-ent e (v-sup d d')  = v-sup (valid-ent e d) (valid-ent e d')
valid-ent e (v-next d)    = v-next (valid-ent e d)
valid-ent e v-idem        = v-idem
valid-ent e v-comm        = v-comm
valid-ent e v-assoc       = v-assoc
valid-ent e v-nsup        = v-nsup
valid-ent e v-infl        = v-infl

validC-ent : {T Th : LCtx} (c : Constr) -> Entails T Th -> ValidC Th c -> ValidC T c
validC-ent (ceq l m) e d = valid-ent e d

ent-refl : {Th : LCtx} -> Entails Th Th
ent-refl {Th} {ceq l m} h = v-hyp h

ent-trans : {T1 T2 T3 : LCtx} -> Entails T1 T2 -> Entails T2 T3 -> Entails T1 T3
ent-trans e12 e23 {c} h = validC-ent c e12 (e23 h)

-- the weakening T, ψ ⊢ T
ent-wk : {Th : LCtx} (c : Constr) -> Entails (lcons c Th) Th
ent-wk c {ceq l m} h = v-hyp (lthere h)

-- extending both sides by the same constraint
ent-lift : {T Th : LCtx} (c : Constr) -> Entails T Th -> Entails (lcons c T) (lcons c Th)
ent-lift c e {c'} lhere      = ent-refl lhere
ent-lift c e {c'} (lthere h) = validC-ent c' (ent-wk c) (e h)

-- a valid constraint can be added on the right
ent-cons : {T Th : LCtx} (c : Constr) -> Entails T Th -> ValidC T c -> Entails T (lcons c Th)
ent-cons c e d lhere      = d
ent-cons c e d (lthere h) = e h

loop-ent : {T Th : LCtx} -> Entails T Th -> Loop Th -> Loop T
loop-ent e (mkSigma l d) = mkSigma l (valid-ent e d)

loopFree-ent : {T Th : LCtx} -> Entails T Th -> LoopFree T -> LoopFree Th
loopFree-ent e lf lp = lf (loop-ent e lp)

------------------------------------------------------------------------
-- Models in ℕ: a context with a model in the natural numbers
-- (successor, maximum) is loop-free.
------------------------------------------------------------------------

private
  max-idem : (m : Nat) -> Eq (max m m) m
  max-idem zero    = refl
  max-idem (suc m) = Eq-cong suc (max-idem m)

  max-comm : (m n : Nat) -> Eq (max m n) (max n m)
  max-comm zero    zero    = refl
  max-comm zero    (suc n) = refl
  max-comm (suc m) zero    = refl
  max-comm (suc m) (suc n) = Eq-cong suc (max-comm m n)

  max-assoc : (m n p : Nat) -> Eq (max (max m n) p) (max m (max n p))
  max-assoc zero    n       p       = refl
  max-assoc (suc m) zero    p       = refl
  max-assoc (suc m) (suc n) zero    = refl
  max-assoc (suc m) (suc n) (suc p) = Eq-cong suc (max-assoc m n p)

  max-suc : (m : Nat) -> Eq (max m (suc m)) (suc m)
  max-suc zero    = refl
  max-suc (suc m) = Eq-cong suc (max-suc m)

  suc-max-neq : (m : Nat) -> Eq (max (suc m) m) m -> Empty
  suc-max-neq zero    ()
  suc-max-neq (suc m) e = suc-max-neq m (suc-inj e)
    where
      suc-inj : {a b : Nat} -> Eq (suc a) (suc b) -> Eq a b
      suc-inj refl = refl

evalL : (Nat -> Nat) -> LExpr -> Nat
evalL r (lvar i)    = r i
evalL r (lsup l m)  = max (evalL r l) (evalL r m)
evalL r (lnext l)   = suc (evalL r l)

HoldsC : (Nat -> Nat) -> Constr -> Set
HoldsC r (ceq l m) = Eq (evalL r l) (evalL r m)

ModelN : (Nat -> Nat) -> LCtx -> Set
ModelN r Th = {c : Constr} -> LMem c Th -> HoldsC r c

evalL-sound : {Th : LCtx} (r : Nat -> Nat) -> ModelN r Th ->
  {l m : LExpr} -> Valid Th l m -> Eq (evalL r l) (evalL r m)
evalL-sound r mo {l} {m} (v-hyp h) = mo h
evalL-sound r mo v-refl          = refl
evalL-sound r mo (v-sym d)       = Eq-sym (evalL-sound r mo d)
evalL-sound r mo (v-trans d d')  = Eq-trans (evalL-sound r mo d) (evalL-sound r mo d')
evalL-sound r mo (v-sup d d')    = Eq-cong2 max (evalL-sound r mo d) (evalL-sound r mo d')
evalL-sound r mo (v-next d)      = Eq-cong suc (evalL-sound r mo d)
evalL-sound r mo (v-idem {l = l})        = max-idem (evalL r l)
evalL-sound r mo (v-comm {l = l} {m = m}) = max-comm (evalL r l) (evalL r m)
evalL-sound r mo (v-assoc {l = l} {m = m} {p = p}) = max-assoc (evalL r l) (evalL r m) (evalL r p)
evalL-sound r mo v-nsup          = refl
evalL-sound r mo (v-infl {l = l}) = max-suc (evalL r l)

loopFree-model : {Th : LCtx} (r : Nat -> Nat) -> ModelN r Th -> LoopFree Th
loopFree-model r mo (mkSigma l d) = suc-max-neq (evalL r l) (evalL-sound r mo d)

loopFree-nil : LoopFree lnil
loopFree-nil = loopFree-model (\ i -> zero) (\ ())

------------------------------------------------------------------------
-- Level substitution
------------------------------------------------------------------------

LSub : Set
LSub = Nat -> LExpr

lsubL : LSub -> LExpr -> LExpr
lsubL z (lvar i)   = z i
lsubL z (lsup l m) = lsup (lsubL z l) (lsubL z m)
lsubL z (lnext l)  = lnext (lsubL z l)

lsubC : LSub -> Constr -> Constr
lsubC z (ceq l m) = ceq (lsubL z l) (lsubL z m)

lsubTh : LSub -> LCtx -> LCtx
lsubTh z lnil         = lnil
lsubTh z (lcons c Th) = lcons (lsubC z c) (lsubTh z Th)

lidS : LSub
lidS i = lvar i

lwkS : LSub
lwkS i = lvar (suc i)

lshift : LExpr -> LExpr
lshift = lsubL lwkS

liftL : LSub -> LSub
liftL z zero    = lvar zero
liftL z (suc i) = lshift (z i)

-- the level substitution  0 ↦ l, i+1 ↦ i
lsub1S : LExpr -> LSub
lsub1S l zero    = l
lsub1S l (suc i) = lvar i

lcomp : LSub -> LSub -> LSub
lcomp z2 z1 i = lsubL z2 (z1 i)

lsubL-ext : (z z' : LSub) -> ((i : Nat) -> Eq (z i) (z' i)) -> (l : LExpr) -> Eq (lsubL z l) (lsubL z' l)
lsubL-ext z z' e (lvar i)   = e i
lsubL-ext z z' e (lsup l m) = Eq-cong2 lsup (lsubL-ext z z' e l) (lsubL-ext z z' e m)
lsubL-ext z z' e (lnext l)  = Eq-cong lnext (lsubL-ext z z' e l)

lsubL-comp : (z2 z1 : LSub) (l : LExpr) -> Eq (lsubL z2 (lsubL z1 l)) (lsubL (lcomp z2 z1) l)
lsubL-comp z2 z1 (lvar i)   = refl
lsubL-comp z2 z1 (lsup l m) = Eq-cong2 lsup (lsubL-comp z2 z1 l) (lsubL-comp z2 z1 m)
lsubL-comp z2 z1 (lnext l)  = Eq-cong lnext (lsubL-comp z2 z1 l)

lsubL-id : (l : LExpr) -> Eq (lsubL lidS l) l
lsubL-id (lvar i)   = refl
lsubL-id (lsup l m) = Eq-cong2 lsup (lsubL-id l) (lsubL-id m)
lsubL-id (lnext l)  = Eq-cong lnext (lsubL-id l)

lsubC-comp : (z2 z1 : LSub) (c : Constr) -> Eq (lsubC z2 (lsubC z1 c)) (lsubC (lcomp z2 z1) c)
lsubC-comp z2 z1 (ceq l m) = Eq-cong2 ceq (lsubL-comp z2 z1 l) (lsubL-comp z2 z1 m)

lsubC-ext : (z z' : LSub) -> ((i : Nat) -> Eq (z i) (z' i)) -> (c : Constr) -> Eq (lsubC z c) (lsubC z' c)
lsubC-ext z z' e (ceq l m) = Eq-cong2 ceq (lsubL-ext z z' e l) (lsubL-ext z z' e m)

lsubC-id : (c : Constr) -> Eq (lsubC lidS c) c
lsubC-id (ceq l m) = Eq-cong2 ceq (lsubL-id l) (lsubL-id m)

lsubTh-comp : (z2 z1 : LSub) (Th : LCtx) -> Eq (lsubTh z2 (lsubTh z1 Th)) (lsubTh (lcomp z2 z1) Th)
lsubTh-comp z2 z1 lnil         = refl
lsubTh-comp z2 z1 (lcons c Th) = Eq-cong2 lcons (lsubC-comp z2 z1 c) (lsubTh-comp z2 z1 Th)

lsubTh-ext : (z z' : LSub) -> ((i : Nat) -> Eq (z i) (z' i)) -> (Th : LCtx) -> Eq (lsubTh z Th) (lsubTh z' Th)
lsubTh-ext z z' e lnil         = refl
lsubTh-ext z z' e (lcons c Th) = Eq-cong2 lcons (lsubC-ext z z' e c) (lsubTh-ext z z' e Th)

lsubTh-id : (Th : LCtx) -> Eq (lsubTh lidS Th) Th
lsubTh-id lnil         = refl
lsubTh-id (lcons c Th) = Eq-cong2 lcons (lsubC-id c) (lsubTh-id Th)

-- lifting commutes with the shift
liftL-shift : (z : LSub) (l : LExpr) -> Eq (lsubL (liftL z) (lshift l)) (lshift (lsubL z l))
liftL-shift z l = Eq-trans (lsubL-comp (liftL z) lwkS l) (Eq-sym (lsubL-comp lwkS z l))

-- instantiating the fresh variable of a shifted level gives it back
lsub1-shift : (m l : LExpr) -> Eq (lsubL (lsub1S m) (lshift l)) l
lsub1-shift m l = Eq-trans (lsubL-comp (lsub1S m) lwkS l) (lsubL-id l)

-- a level substitution that validates the constraints of Th sends
-- Th-valid equations to T-valid ones
LSubOK : LCtx -> LCtx -> LSub -> Set
LSubOK T Th z = {c : Constr} -> LMem c Th -> ValidC T (lsubC z c)

valid-lsub : {T Th : LCtx} (z : LSub) -> LSubOK T Th z -> {l m : LExpr} ->
  Valid Th l m -> Valid T (lsubL z l) (lsubL z m)
valid-lsub z ok {l} {m} (v-hyp h) = ok h
valid-lsub z ok v-refl          = v-refl
valid-lsub z ok (v-sym d)       = v-sym (valid-lsub z ok d)
valid-lsub z ok (v-trans d d')  = v-trans (valid-lsub z ok d) (valid-lsub z ok d')
valid-lsub z ok (v-sup d d')    = v-sup (valid-lsub z ok d) (valid-lsub z ok d')
valid-lsub z ok (v-next d)      = v-next (valid-lsub z ok d)
valid-lsub z ok v-idem          = v-idem
valid-lsub z ok v-comm          = v-comm
valid-lsub z ok v-assoc         = v-assoc
valid-lsub z ok v-nsup          = v-nsup
valid-lsub z ok v-infl          = v-infl

validC-lsub : {T Th : LCtx} (z : LSub) (c : Constr) -> LSubOK T Th z -> ValidC Th c -> ValidC T (lsubC z c)
validC-lsub z (ceq l m) ok d = valid-lsub z ok d

lmem-map : (z : LSub) {c : Constr} {Th : LCtx} -> LMem c Th -> LMem (lsubC z c) (lsubTh z Th)
lmem-map z lhere      = lhere
lmem-map z (lthere h) = lthere (lmem-map z h)

lmem-unmap : (z : LSub) {d : Constr} (Th : LCtx) -> LMem d (lsubTh z Th) ->
  Sigma Constr (\ c -> Pair (LMem c Th) (Eq d (lsubC z c)))
lmem-unmap z (lcons c Th) lhere      = mkSigma c (mkSigma lhere refl)
lmem-unmap z (lcons c Th) (lthere h) =
  let r = lmem-unmap z Th h in mkSigma (fst r) (mkSigma (lthere (fst (snd r))) (snd (snd r)))

-- the image of a theory under z is validated by z
lsubOK-self : (z : LSub) (Th : LCtx) -> LSubOK (lsubTh z Th) Th z
lsubOK-self z Th {ceq l m} h = v-hyp (lmem-map z h)

-- entailment composed with a valid level substitution
lsubOK-ent : {T T' Th : LCtx} (z : LSub) -> Entails T' T -> LSubOK T Th z -> LSubOK T' Th z
lsubOK-ent {T} {T'} {Th} z e ok {c} h = validC-ent (lsubC z c) e (ok h)

-- a level substitution maps an entailment to an entailment
ent-lsub : {T Th : LCtx} (z : LSub) -> Entails T Th -> Entails (lsubTh z T) (lsubTh z Th)
ent-lsub {T} {Th} z e {d} h =
  let r = lmem-unmap z Th h
  in Eq-transport (ValidC (lsubTh z T)) (Eq-sym (snd (snd r)))
       (validC-lsub z (fst r) (lsubOK-self z T) (e (fst (snd r))))

-- validity is stable under the shift
valid-shift : {Th : LCtx} {l m : LExpr} -> Valid Th l m -> Valid (lsubTh lwkS Th) (lshift l) (lshift m)
valid-shift {Th} = valid-lsub lwkS (lsubOK-self lwkS Th)

-- loops are preserved by valid level substitutions
loop-lsub : {T Th : LCtx} (z : LSub) -> LSubOK T Th z -> Loop Th -> Loop T
loop-lsub z ok (mkSigma l d) = mkSigma (lsubL z l) (valid-lsub z ok d)

-- instantiating the fresh variable of a shifted theory
lsubC-inst-shift : (l : LExpr) (c : Constr) -> Eq (lsubC (lsub1S l) (lsubC lwkS c)) c
lsubC-inst-shift l c = Eq-trans (lsubC-comp (lsub1S l) lwkS c) (Eq-trans (lsubC-ext _ _ (\ i -> refl) c) (lsubC-id c))

lsubOK-inst : (l : LExpr) (Th : LCtx) -> LSubOK Th (lsubTh lwkS Th) (lsub1S l)
lsubOK-inst l Th {d} h =
  let r = lmem-unmap lwkS Th h
      c = fst r
  in Eq-transport (ValidC Th)
       (Eq-sym (Eq-trans (Eq-cong (lsubC (lsub1S l)) (snd (snd r))) (lsubC-inst-shift l c)))
       (ent-refl (fst (snd r)))

------------------------------------------------------------------------
-- Equivalent constraints  ψ ⇔ ψ'  in Θ  (bcde.pdf: judgements are
-- invariant under level equality, so [ψ]A = [ψ']A for such ψ, ψ')
------------------------------------------------------------------------

EquivC : LCtx -> Constr -> Constr -> Set
EquivC Th c c' = Pair (ValidC (lcons c Th) c') (ValidC (lcons c' Th) c)

equivC-sym : {Th : LCtx} {c c' : Constr} -> EquivC Th c c' -> EquivC Th c' c
equivC-sym q = mkSigma (snd q) (fst q)

equivC-refl : {Th : LCtx} (c : Constr) -> EquivC Th c c
equivC-refl c = mkSigma (ent-refl {_} {c} lhere) (ent-refl {_} {c} lhere)

-- a valid constraint stays valid when replaced by an equivalent one
equivC-valid : {Th : LCtx} {c c' : Constr} -> EquivC Th c c' -> ValidC Th c -> ValidC Th c'
equivC-valid {c = c} {c' = c'} q v = validC-ent c' (ent-cons c ent-refl v) (fst q)

-- along an entailment
equivC-ent : {T Th : LCtx} {c c' : Constr} -> Entails T Th -> EquivC Th c c' -> EquivC T c c'
equivC-ent {c = c} {c' = c'} e q =
  mkSigma (validC-ent c' (ent-lift c e) (fst q)) (validC-ent c (ent-lift c' e) (snd q))

-- along a valid level substitution
lsubOK-cons : {T Th : LCtx} (z : LSub) (c : Constr) -> LSubOK T Th z ->
  LSubOK (lcons (lsubC z c) T) (lcons c Th) z
lsubOK-cons z (ceq l m) ok lhere                        = v-hyp lhere
lsubOK-cons z (ceq l m) ok {ceq l' m'} (lthere h) =
  validC-ent (lsubC z (ceq l' m')) (ent-wk (lsubC z (ceq l m))) (ok h)

equivC-lsub : {T Th : LCtx} (z : LSub) {c c' : Constr} -> LSubOK T Th z ->
  EquivC Th c c' -> EquivC T (lsubC z c) (lsubC z c')
equivC-lsub z {c} {c'} ok q =
  mkSigma (validC-lsub z c' (lsubOK-cons z c ok) (fst q))
          (validC-lsub z c (lsubOK-cons z c' ok) (snd q))

------------------------------------------------------------------------
-- Canonical codes of levels (the only non-syntactic ingredient needed
-- for level products): a code function that identifies levels equal in
-- T, with a decoding back to a representative.  Such a structure exists
-- whenever equality of levels in T is decidable (Bezem–Coquand, the
-- uniform word problem for sup-semilattices with an inflationary
-- endomorphism): code a canonical normal form.  Codes need not be
-- surjective; a code k is CANONICAL when lcode (ldec k) = k (the codes of
-- levels are exactly the canonical ones).  The model is parameterised by it.
------------------------------------------------------------------------

record LDec (T : LCtx) : Set where
  field
    lcode       : LExpr -> Nat
    lcode-sound : {l m : LExpr} -> Valid T l m -> Eq (lcode l) (lcode m)
    ldec        : Nat -> LExpr
    ldec-code   : (l : LExpr) -> Valid T (ldec (lcode l)) l

LDecAll : Set
LDecAll = (T : LCtx) -> LDec T

-- extending a level environment by one level
lconsS : LExpr -> LSub -> LSub
lconsS l z zero    = l
lconsS l z (suc i) = z i
