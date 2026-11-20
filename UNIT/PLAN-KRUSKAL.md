# Constructive uniform Kruskal via open induction — plan

Sources: `~/CANONICITY/kruskal2.pdf` (Coquand, *An inductive proof of
Kruskal's theorem*), `~/CANONICITY/concomb.pdf` (open induction),
`~/CANONICITY/freund1.pdf` (Freund–Rathjen–Weiermann, uniform Kruskal
⇔ Π¹₁-CA₀).

## Done (commit 53e8535)
- `TransBar.seg`: bars on transition systems, Lemmas 1–2, `AccU`.
- `OpenInduction.seg`: kruskal2 Prop 1 + Corollary; words instance.
- `VarSets.seg`: sets over a poset, P(X), k-ary relations, AF.
- `VarRamsey.seg`: kruskal2 Prop 2 (port of `AlmostFull.ram` with states);
  `afInter` for variable binary relations.

## Done: variable Higman, kruskal2 Prop 4 (`VarHigman.seg`, 2026-11-20)
`Higman[C,le,..,Y0,Y,Y-mono,prec,prec-mono,af].higman : AFR emb` over
words, postulate-free, in All.seg.  Deviations from the sketch below:
- lt on words = "is the immediate tail of" (enough: only tails compared).
- Z-letter = (y, w, q) meaning word y w with history q before it;
  Xz a z = Pre ((y w) q) h_a.  Position order decided by `LtN` on lengths
  (R a z z' := len q < len q' -> w ≼ w' ∨ K a), so non-increasing pairs
  are vacuous without Lemma 2.
- Generic `Map.barMap` (bars along maps of sets over posets with a stable
  relation RelP between predicates) does F, both product pull-backs.
- Generic `Esc.esc` handles "leaves with < 2 Z-letters": bar for Q ∨ K ⇒
  bar for Q, one extra step.
- G is not fed through the tree: the letters of h are put into the
  predicate (`upS BS (G h)`, from `secMono`), and `mainT` recurses on the
  product tree calling `VarOpen.prop` at each node; empty new words give a
  bar in one step (`oneStep`), so G just skips empty words.

## Done: variable Kruskal, kruskal2 Prop 5 (`VarMinBad.seg`, `VarKruskal.seg`, 2026-11-20)
`Kruskal[C,le,..,Y0,Y,Y-mono,prec,prec-mono,af].kruskal : AFR embT` for
finite trees with labels in a set Y over C (the paper only states the
ordinary version; the variable one costs nothing here).  Postulate-free.
- `VarMinBad.On`: the part shared by Props 4 and 5, generic in a
  well-founded "component" relation lt (closed for validity) and an
  increasing e with `eSub : lt v u -> e x v -> e x u`: prefixes/lengths,
  goodness, C' = M(B), Z-letters (v, u, q) with `lt v u`, R, `afR` (map F).
  VarHigman predates it and keeps its own copy (not ported).
- Trees: `data F = fnil | fcons y k r` (forests), `Tr = Y0 * F`; lt =
  "immediate subtree"; `embT` by recursion on the target forest (`opsF`
  returns the Higman embedding into it and "embeds in one of its trees").
- R^W almost full: `VarHigman.Higman` instantiated on Z over C'.
- Product letters (u, q) (tree + position), components root and the word
  `ws` of Z-letters of its immediate subtrees; `afInter` after pull-backs.
- `KZ.kzEmb`: R^W between words of positions in order => forests embed or
  K; `mainT`/`thm` as in VarHigman, no empty-word case.

## Then (updated)
- Uniform version (freund1 Thm 3.10): replace "forests + Higman on Z" by a
  dilator-like W with "W preserves almost-fullness over variable sets".

## Design decisions for Props 4–5
- (commit after 53e8535) VarRamsey trees are **labelled and
  proof-dependent**: `sp st0 f` with `f c x : le st0 c -> X c x -> WT`, and
  `Sec (sp st0 f) A st = le st0 st × ∀ c x l0 l m. …` (any proof `l0` of
  `le st0 c`, so `secState` keeps the tree).  `ram` returns `Bar` (tree +
  proof); trees can now be built from hypotheses on the choice.
- Open induction is used in VarRamsey form: `E st h := Bar (upH A h) st`
  with `upH A (x::h) = up (upH A h) x`; no separate bridge needed.
- The poset for the auxiliary relation is
  `C' = (c : C) * (h : history) * Valid c h * M c h`, ordered by
  `le c c' × h' extends h` (proofs ignored).
- **Positions as prefixes**: a Z-letter is a prefix `p` of the history
  (`Pre p h`, from OpenInduction), `head p` is the word, `tail p` the
  earlier history; "earlier" = proper prefix.  No index arithmetic, and
  positions are stable under extension.
  R a p p' := ProperPre p p' → tail(head p) ≼ tail(head p') ∨ good a.h.
- X-history along a Z-path: `map (tail ∘ head) zs ++ tail p₀`.
- No general `fromM`: the final step recurses on the product bar directly,
  calling Prop (E hereditary on M) at each node.

## Open induction with states (Sec style)
`M (st, u) := ∀ c ≥ st. ∀ v <lex u valid at c. E (c, v)`; Prop: E hereditary
on M by induction on the length of the new word, with Q(x) := ∀ c ≥ st,
x ∈ X(c) → E (c, u x); uses that E is increasing in the state (`secState`).

## Higman, variable (kruskal2 Prop 4)
1. Lists: Higman embedding `emb r c`, tails, lengths, histories (lists of
   words, latest first), prefix order (refl/trans), lex order by lengths.
2. B = good for `emb` (2-ary GoodK); increasing along steps and in c.
3. Z over C': letters i with i < |h| and h_i nonempty.
   R (c,h,…) i j := i < j → tail h_i ≼ tail h_j ∨ B (c, h).
4. R is AF: from state a = (c,h,…), first letter i: bar from
   E (c, h_<i · tail h_i) (in M(c,h) because tail h_i is shorter); map its
   tree letter-wise (Z-letter j at state a' ↦ word tail(h'_j)).  Leaf
   cases: goodness inside h_<i or h_k ≼ tail h'_j ⇒ h' good (escape);
   tail ≼ tail ⇒ R.  (Leaves with < 2 Z-letters: one more step.)
5. Product: `afInter` on Y × Z (Y via pull-back along the head letter).
6. B is a bar on M: Lemma 2 (empty word ⇒ good next step), then the map
   G : history ↦ (head h_i, i) sequence; product-good at i<j ⇒ h good.
7. Corollary of open induction ⇒ `emb` AF.

## Then
- Kruskal (Prop 5): trees over Y, Z = immediate subtrees with escape,
  variable Higman on Z, product with Y, open induction.
- Uniform version: replace "words over Z + Higman" by a dilator-like W
  with hypothesis "W preserves AF of relations over variable sets"; check
  simple normal PO-dilators satisfy it.

## seg gotchas
- `split` only at the top of a definition (not inside `where`/`let`).
- Types quantifying over predicates/relations live in `U l+`.
