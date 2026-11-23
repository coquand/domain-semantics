# PLAN-UNIV-DELTA: a simplicial model of T_Russell with one universe

Handoff, 2026-11-23. Read this whole file before touching code.

## 1. Goal

Instantiate the generic Russell semantics (`DOMAIN/UNIT/RSem.seg`) in the
**simplicial** model of `~/CANONICITY/unit/core`, with excluded middle as
a parameter, for one universe (N = 0). It is the analogue of
`DOMAIN/UNIT/russell-posets` (the poset model, done).

A `TEModel[0]` (`DOMAIN/UNIT/EhrhardTEModel.seg`) consists of:
- an Ehrhard CwF whose four sorts are sets;
- Π, as a term bijection natural in substitutions;
- one universe U₀ with decoding T, natural;
- a Π-code with **strict** decoding T(Π₀(a,b)) = Π(T a, T b), natural.

The fields for the hierarchy are vacuous at N = 0. See
`russell-posets/PosetTEModel.seg` for how they are discharged.

## 2. Why the poset argument does not transfer, and the chosen route

Read `~/CANONICITY/unit/doc/model.tex`: §§3–5, §8.1 (posets), §8.2
(simplicial sets, Theorem "hornbox" and the remarks after it).

- **Posets.** The universe's classifier is Fib itself (compositions), and
  El's structure is glued from the codes' own compositions (the interval
  is tiny). So El⌜A⌝ = A holds *with* the fibration structure, and the
  Π-code is the name of the Π-type (Huber, Definition 1.1.4). This is
  formalised in `sag-model/FibName*`, `FibUnivPi`.
- **Δ.** y[m]×Δ[1] is not representable, so the classifier is the set of
  horn-filling *operations* (`CDeltaCl`, `isFib`, no uniformity), and El's
  fibration structure is hornbox(2) applied once, using excluded middle
  (`CDeltaElFib`, `CDeltaHornToFib`). Naming a fibrant type (A, c) keeps
  only the horn operation (1)(c), and decoding rebuilds compositions by
  (2). Since (2)∘(1) ≠ id, **El⌜A⌝ = A fails on structures**. Do not try
  to prove it.

**Chosen route: types as code maps** (Voevodsky's universe-category CwF).
Take two universe levels U₀ ⊂ U₁ (core is level-polymorphic), and the
level inclusion ι : U₀ → U₁.
- The CwF has types over Γ = maps A : Γ → U₁, and terms = sections of El₁
  along A. Every type carries, by definition, El₁'s structure moved along
  A.
- Substitution is composition: strictly functorial.
- Context extension, p, q, lift, sec come from the presheaf CwF.
- All four sorts are sets.
- Π(A, B) := ⌜Π_gen(El A, El B)⌝₁, where Π_gen is the generic Π of fibrant
  types (Theorem "type formers"), and ⌜–⌝₁ names a fibrant type, with
  horn operation (1)(structure), in U₁. Terms of Π(A, B) are sections of
  the underlying Π presheaf, so the term bijection is presheaf-level.
- U₀ as a type is the code of U₀ in U₁. For a : Γ → U₀, T(a) := ι∘a, and
  Π₀(a, b) := ⌜Π_gen(El₀ a, El₀ b)⌝₀.

Strict decoding then reduces to ι∘⌜X⌝₀ = ⌜X⌝₁ for small fibrant X, and
that reduces to:

> **Key lemma.** hornbox(2) is natural along monomorphisms: for
> s : D → G injective on points at each stage, (2) applied to (A[s], h[s])
> equals (2)(A, h) moved along s. Apply it to ι, which is a mono, together
> with invariance of (2) and (1) under the change of level.

**Informal proof of the key lemma** (checked by hand against `core`,
2026-11-23). The normalised fillers (`CDNormB`–`E`) are defined by
recursion on the dimension N of a problem b:
- K(b) = sᵢ*(K(dᵢ*b)) for the first i with b degenerate along sᵢ;
- otherwise the face-uniform 4a step from h (`CDFill`).

Compare the two instances by induction on N:
- **(i) The 4a step agrees for any s,** because h[s] is h on the image
  problem (classifier substitution is pointwise).
- **(ii) The degeneracy decision agrees for monos.**
  - `DegR N b i` = `ProbRel b (sᵢ*dᵢ*b)` (`CDeltaHornBox`) compares points
    of the line context and the partial elements.
  - For A[s] the points are in D. For A they are their images in G. The
    partial elements are the same, since A[s] has A's fibres.
  - s mono ⇒ s^I mono ⇒ the two propositions are equivalent.
  - `Found` (first degenerate index with minimality, or none) is a
    proposition, so it gives the same index whatever `lem` returns.
- **(iii) Conclusion.** Equal fillers give equal compositions (ends via
  `CompK.fromFill`), hence equal structures (`rc-ext`).

`model.tex` agrees: (2) fails to be natural only along substitutions that
identify points. For ι:
- injectivity: `smallC`/`liftV` are injective (`liftV-inj`), and the horn
  operation is the same data;
- El₁ along ι is El₀ read at level a⁺: same fibres
  (`V1.Ix (smallC v) = W0.Ix v` definitionally), and El's horn operation
  at a code is that code's (`CDElHorn`).

**Points not checked by hand:**
- that `CDStageA.Prob` for A[s] is literally "D-point plus A-elements";
- how the move along s (`CFibSub` carts) unfolds for structures built by
  `CompK.fromFill`.

## 3. Ground rules (from the user)

- **Git.** Never `git add -u` or `git add -A` (not in DOMAIN, not in
  CANONICITY). Stage explicit paths. Commit or push only when the user
  asks; do not commit in this task.
- **Wording.** Say "U : U", never "Type:Type".
- **Status.** Report status plainly: proved, open, stuck on X. Do not
  over-claim.
- **Proof checks are fast.** Keep files small. Δ files are heavy:
  split, use `opaque` where core does, and check performance early.
- **Check that a new file is really checked.** After a first green check,
  plant a deliberate error, see it rejected, then restore the file.
- **Where to write:**
  - **Only new files.** In `~/CANONICITY/unit/core/` (or a new directory
    there), and in a new directory `~/DOMAIN/UNIT/russell-delta/` for the
    `TEModel[0]` instance, modelled on `russell-posets/` including its
    `check.py`.
  - **Never edit existing files** in either repository; that is a stop
    condition. Do not touch the user's untracked files. Other sessions may
    be working in `DOMAIN/UNIT` and in `~/DOMAIN-id`; leave them alone.
- **Checkers.** The main checker for `core`
  (`cd ~/CANONICITY/unit && ./segc core`, or `$(cabal list-bin exe:seg)`).
  The indexed checker for the integration with `DOMAIN/UNIT` (it now has
  the same lock rules):

      /Users/coquand/CANONICITY/unit-indexed/dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg

  Use temporary loaders for checking new core files; delete them after.

## 4. Mode and stop conditions

**Proceed autonomously through D0–D5** and keep the log in §6 up to date.
Stop and report only for:
1. **A conceptual gap.** The key lemma is false (e.g. (2) is not natural
   along ι after all); the code-map CwF cannot be made an Ehrhard CwF with
   sets; Π_gen or (1) does not commute with the change of level; or
   anything else that needs an idea not in this file or `model.tex`.
2. **Scope.** A change to an existing file, or to a checker, is needed.
3. **No progress.** A step fails repeatedly for reasons you cannot find.

Routine work (long inductions, splitting slow files, transport lemmas) is
not a reason to stop. At the end, report the final state, the checks run,
and all new files in both repositories.

## 5. Plan

- **D0. Key lemma** (e.g. `core/CDHornNat.seg` and parts).
  - Naturality of hornbox(2) along a mono s, by a comparison induction
    following `CDNormB`–`E` (the stages K with sides and (A)/(B)), then
    for the composition structures.
  - Then the instance at ι, including the change of level for (2) and
    (1).
  - Record in the log whether it holds.
- **D1. Code-map Ehrhard CwF** over Δ (`core/CDCodeCwF.seg` …).
  - Types = maps into U₁, terms = sections of El₁, substitution =
    composition; the Ehrhard operations; sets.
  - If it can be done generically over the base (posets and Δ), do so;
    otherwise Δ only.
  - The CwF record is `core/CwF.seg` (Ehrhard form).
- **D2. Π.** Π(A,B) := ⌜Π_gen(El A, El B)⌝₁.
  - Naturality: naming commutes with substitution, and Π_gen is natural
    (core's Theorem "type formers").
  - Term bijection (`Pi-iso`, `Pi-iso-nat`).
- **D3. Universe and Π-code.**
  - U₀ as the code of U₀ in U₁ (core's fibrant universe, `CFibU3.fibU` or
    the Δ final statement).
  - T(a) := ι∘a, Π₀ := ⌜Π_gen(El₀ a, El₀ b)⌝₀.
  - `Dec-pic` by D0 plus commutation of Π_gen and (1) with the change of
    level (compare `sag-model/FibPiSmall.seg`).
  - `pic-nat`.
- **D4. `TEModel[0]` and the Russell semantics** in
  `~/DOMAIN/UNIT/russell-delta/`.
  - An adapter to `DOMAIN/UNIT`'s `EhrhardCwF`, as
    `russell-posets/EhrhardFromCore.seg`.
  - Contexts form a set, as `PosetContextSet`.
  - The instance; `RSem.Interpret[…, zero, model]` with lem as a
    parameter.
  - A closed example as in `russell-posets/PosetRSemCheck.seg`.
  - `check.py` modelled on `russell-posets/check.py`, linking core instead
    of sag-model.
- **D5. Report.** Summarise.
  - Do not edit `gat-ehrhard.tex`. Write a draft paragraph for its §14
    and §15 in the log instead; the user will decide.

## 6. Checklist and log

- [x] D0 key lemma: (2) natural along monos; instance at ι with change of level
- [x] D1 code-map Ehrhard CwF over Δ (sets)
- [x] D2 Π, naturality, term bijection
- [x] D3 U₀, T, Π-code with strict decoding and naturality
- [x] D4 TEModel[0], Russell semantics, closed example, russell-delta/check.py green
- [x] D5 report and draft tex paragraph

Log:

- D0 started. Read the model and core construction. `CDStageA.Prob`
  packages a line with a specified start and a partial element of the
  strict fibre over that start. `CCart` already supplies the maps on
  these points and strict fibres, and `MoveComp.unique` reduces equality
  of compositions to equality of the moved values. The main checker
  accepted the existing `CDeltaHornToFib` and `CDeltaFinal` in a
  temporary loader (34 declarations).

- D0, general comparison proved. `CDHornNat` reflects degeneracy along
  a stagewise injective map and compares the two shuffle chains and
  normalised fillers. Its final law allows different fibre levels
  whenever the cartesian map preserves the given horn fillers. The main
  checker accepted 267 declarations and rejected an injected type error
  in each of the nine proof files. The indexed checker also accepted
  the existing `CDeltaFinal`.
- D0, universe instance in progress. `CDeltaCl[a+]` also changes the
  codes of the base category, so its maps and sieves did not convert
  directly to those of `CDeltaCl[a]` in a checker probe. I am lifting
  the original base codes with `smallC` to keep the map and sieve data
  fixed while reusing the higher universe construction.
- D0, universe comparison proved for hornbox(2). The lifted base
  reuses the original maps, interval and sieves. Lifting a code preserves
  its horn operation and reflects code equality. The two El families
  form a cartesian map over the inclusion, and their horn operations
  respect that map. The main checker accepted `restrict-fib`.
- D0, hornbox(1) under moves is still open. Starting the independent
  code-map CwF construction while the comparison for naming remains
  open.
- D0 complete. `CDBoxNat` proves hornbox(1) commutes with cartesian
  moves, including changes of level, by comparing the composition
  problems on the retraction line. This direction permits arbitrary
  context maps. Together with `restrict-fib` this gives the required
  comparisons at the universe levels.
- D1 complete. `CCodeCwF` builds the code-map Ehrhard CwF over an
  arbitrary small base category. `CDCodeContext` instantiates it with
  the higher simplicial code presheaf, and `CCodeContextSet` gives the
  set proof for contexts. The main checker accepted 122 D1 declarations.
  The indexed checker accepted all 682 selected D0–D1 declarations.
  Each new D0–D1 file rejected a deliberate type error in the temporary
  loader, then the original text was restored.
- D2 started. `CDName` names the chosen horn operation of a fibrant type.
  The main checker accepted naturality of naming along substitutions
  and the underlying type equality after decoding a name (86
  declarations). The Π record and its equations are open.
- D2 complete. `CDCodePi` names the generic fibrant product and
  transports the presheaf term bijection along the underlying
  decoding equality. Reindexing compares the dependent types and
  their terms together. The main checker accepted the resulting
  `PiStr`, including `Pi-iso-nat`.
- D3 started. The checked universe type is the name of the lower
  universe over the terminal context, reindexed to each context.
  `CDCodeUniverse` reads its terms as code maps and checks naturality
  and injectivity of decoding. `CDSmallPi` supplies small codes for
  the generic product. The main checker accepted 285 selected
  declarations through these D2–D3 modules.
- D3 complete. `CDCodeSmall` uses the fibration of El₀ for the small
  readings and compares it with El₁ using D0. `CDNameSmall` checks
  that inclusion preserves the name of the small product.
  `CDCodePic` proves strict decoding, and `CDCodePicNat` uses
  injectivity of decoding and product naturality to prove the
  substitution law with the transported binder. The main checker
  accepted all 113 declarations under `CDDeltaModel`.
- `CDHornSub` specializes D0 to the ordinary pullback of a horn
  operation along a monomorphism. The main checker accepted all
  24 declarations.
- D4, targeted check passed. `DeltaTEModel` reuses the existing
  `EhrhardFromCore` adapter and instantiates `RSem.Interpret` at zero
  with excluded middle as a parameter. The indexed checker accepted
  all 49 declarations in the instance and closed Russell example.
  The complete integration check is pending.
- Validation before installation passed. The main checker checked all
  11,876 declarations in the temporary core loader. The indexed
  integration loader checked all 14,207 declarations. Both reported
  zero failures. Across the temporary loaders, the checkers rejected a
  deliberate type error in each of the 49 new core files and both new
  integration proof files. All 49 installed core files match their
  checked sources byte for byte.
- D4 complete. The default `UNIT/russell-delta/check.py` command, run
  against the installed core files, checked 14,207 declarations with
  zero failures in 37.25 seconds. The closed term has type
  `Π (A : U₀). U₀`, and its direct and converted derivations agree.
- D5 complete. The drafts below are for `gat-ehrhard.tex` §§14–15.
  The work is uncommitted. The new proof files and the integration
  checker are in the two directories specified in §3.

### Draft paragraph for §14

> \paragraph{Simplicial sets.} For the simplicial model we use two
> levels of the presheaf of horn-filling operations. A type over
> $\Gamma$ is a map $\Gamma\to\U_1$, and its terms are sections of
> $\mathsf{El}_1$ pulled back along this map. Substitution is composition of
> code maps. The dependent product is the name of the generic fibrant
> product, with the term bijection inherited from the underlying
> presheaf product. The universe $\U_0$ is named in $\U_1$, and decoding
> a map to $\U_0$ is postcomposition with the level inclusion
> $\iota:\U_0\to\U_1$. Horn-to-box filling commutes with cartesian
> moves over stagewise injective maps. Such a map reflects degeneracy
> of filling problems, and the prism construction respects the moved
> horn fillers. Applying this comparison to $\iota$, together with
> the compatibility of box-to-horn filling and product codes with
> lifting, gives the strict equation
> $\T(\Pi_0(a,b))=\Pi(\T a,\T b)$ and its substitution law. This gives
> an Ehrhard model of level $0$ with excluded middle for propositions
> as a parameter.

### Draft paragraph for §15

> The simplicial instance uses \seg{CANONICITY/unit/core}.
> \seg{CDHornNat} compares normalized horn-to-box fillers,
> \seg{CCodeCwF} constructs the code-map category with families, and
> \seg{CDCodePi} and \seg{CDCodePic} give products and strict decoding.
> \seg{UNIT/russell-delta/DeltaTEModel} instantiates \seg{RSem.Interpret}
> with the level-$0$ model, and \seg{DeltaRSemCheck} checks the closed
> term $\lambda A:\U_0.\,\Pi(x:A).\,A$ and the agreement of its direct
> and converted derivations. \seg{russell-delta/check.py} checks the
> simplicial instance together with the Russell syntax and semantics
> using the indexed checker.
