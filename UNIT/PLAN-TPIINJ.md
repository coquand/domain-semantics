# SUPERSEDED 2026-11-22: Pi-injectivity for T_Tarski is not needed; see PLAN-TR.md.
# Kept: TSem, TSound, TRed; the domain is now levelled (LTypes..LSoundF), TInv done.

# PLAN-TPIINJ: Pi-injectivity for T_Tarski in Unit, by the filter-domain adequacy

Goal (sterbac4 §2 Thms 8-10 for the GAT, by transfer through Thm 16 / L18-19):
for T_Tarski (TTyping.Der, unscoped) prove
  Pi-injectivity   G |- pi A B = pi A' B'  =>  G |- A = A',  G.A |- B = B'
  U-injectivity    G |- U_m = U_n  =>  m = n      (and U/Pi no-confusion)
by the method of Consequences.seg (MIN, U:U): soundness in the filter
model, a relation at compact witnesses, adequacy, evaluation at the bottom
environment and the element pi om om.  Decided 2026-11-22 (user: dev in Unit;
the Agda port ERT/GAT/ is parked).

## Reuse
* Unchanged: Types, Consistency, Typing, Filter (the domain), and the
  filter-level lemmas of Sound.seg (HasTy, sound-pi, sound-lam, App, Beta, Eta,
  pi-univ-clash, ...), Laws of the relation that do not mention syntax.
* Re-done for T_Tarski syntax (file prefix T): Sem, Sound, Reduction, RelC,
  LawsC, AdeqBase, AdeqPi/Lam/App/Fun, Adequacy, Consequences.

## Design
* Model: levels collapse.  [[U_n]] = [[U^n_m]] = U, [[T_n a]] = [[t^n_m a]] = [[a]],
  [[Pi_n(a,b)]] = [[Pi(a,b)]] = piF; annotations of lam/app ignored.
* Head reduction: beta (annotations ignored) and the Tarski steps
  T_n(Pi_n(a,b)) -> Pi(T_n a, T_n b),  T_n(U^n_m) -> U_m,  T_n(t^n_m a) -> T_m a,
  T_n a -> T_n a' when a -> a' (and the t-steps on codes).
* Relation: as RelC, with the type clause at univ: T, T' reduce to U_m and
  U_m (the SAME m: U-injectivity is syntactic, the model cannot see levels);
  terms of U_n related at u iff their decodings T_n a, T_n a' are related
  as types at u.
* One adequacy case per T_Tarski rule (34), dispatched by one split.

## Files
1. TSem.seg      semantics, Lemmas 3.4-3.7                       [x]
2. TSound.seg    Fits over Cx, soundness (Thm 2.31)               [ ]
3. TRed.seg      head reduction, determinism, normal forms        [ ]
4. TRel.seg      relation at compact witnesses (RelC)             [ ]
5. TLaws.seg     laws L2-L7 (LawsC)                               [ ]
6. TAdeq*.seg    adequacy (Thm 2.35)                              [ ]
7. TPiInj.seg    Pi-injectivity, U-injectivity, no-confusion      [ ]
8. GAT inversion (Thms 8-10) by transfer                         [ ]
