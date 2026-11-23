# PLAN-UNIV1: a univalent model of T_Russell with one universe

Handoff, 2026-11-23. Read this whole file before touching code.

## 1. Goal

Instantiate the generic Russell semantics (`DOMAIN/UNIT/RSem.seg`: every
bounded T_Russell judgement has a denotation in any `TEModel[N]`,
independent of the lift) in the univalent model of
`~/CANONICITY/unit/sag-model`, for N = 0 (one universe).

For N = 0 the rules for `uc`, `lf` and cumulativity cannot apply (they need
m < n ≤ 0). So a `TEModel[0]` (`DOMAIN/UNIT/EhrhardTEModel.seg`) is an
Ehrhard CwF whose sorts are sets, with Π and one Tarski universe closed
under Π. In detail, the universe needs:
- U and its decoding T, both natural in substitutions;
- a Π-code `pic a b`;
- strict decoding T(pic a b) = Π(T a, T b);
- naturality of `pic`.

The model already has everything except the Π-code with strict decoding:
- `FibCwF` (fibrant types; Ty/El/Sub are sets);
- `FibCwF.fibPi` (Π);
- `CwFU.UnivStr` with instance `FibUniv.fibUniv` (U = Cod, decoding = Dec).

The approach follows Huber's thesis (`~/DOMAIN/shuber.pdf`, Definition
1.1.4 and §1.2.4). Prove the strict equation

    T(⌜A⌝) = A        for every small fibrant type A over Γ, as fibrant
                      types (underlying type AND fibration structure)

Then define `pic a b := ⌜Π(T a, T b)⌝`, so the Π-code needs nothing else.

## 2. Ground rules (from the user)

- **Git.** Never `git add -u` or `git add -A` (not in DOMAIN, not in
  CANONICITY). Stage explicit paths. Commit or push only when the user asks.
- **Wording.** Say "U : U", never "Type:Type".
- **Status.** Report status plainly: proved, open, stuck on X. Flag an
  obstruction as soon as you see it, especially if the informal argument in
  section 4 fails somewhere.
- **Proof checks are fast.** Keep files that check in seconds; split large
  proofs (sag-model files are typically < 2 s each).
- **Check that a new file is really checked.** After a first green check,
  plant a deliberate error, see it rejected, then restore the file.
- **The model is in `~/CANONICITY/unit`, the user's repository.**
  - Add new files in `sag-model/`.
  - Do not edit existing files there without asking the user. That
    includes the one-line `opaque` fix in section 3.
- **Other sessions are working in `DOMAIN/UNIT`** (the annotation work,
  `PLAN-ANNOT*.md`). Do not touch their files. For DOMAIN/UNIT, only create
  new files and add your own import line, once green.

## 3. Facts established (2026-11-23)

### Checkers
- The model trees are checked with the main checker:

      cd ~/CANONICITY/unit && ./segc sag-model     # or: $(cabal list-bin exe:seg) All.seg in sag-model/

- `DOMAIN/UNIT` needs the indexed checker (indexed families `GDer`, `RDer`):

      /Users/coquand/CANONICITY/unit-indexed/dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg

- The indexed checker accepts `core` and `sag-model` once the single line
  `opaque CExt2.ExtB2.extOb ;` (in `core/CExt4.seg:217` and
  `sag-model/CExt4.seg:217`) is removed. That line makes opaque a name of a
  parameterised module via a qualified path, which the indexed checker
  rejects.
  - With the line removed, in scratch copies: core 18106 declarations, 0
    failed, 55 s; sag-model 12305 declarations, 0 failed, 44 s.
  - Timing is unchanged without the opaque.
  - Whether to delete the line or extend the indexed checker is the user's
    decision.

### The model
Read `~/CANONICITY/unit/doc/model.tex`:
- §3, relative contractibility: Definition `def:rc`, Lemma `lem:rc-ext`,
  Construction `con:move`, Lemma `lem:move-laws`, Lemma `lem:tr-move`;
- §4, fibrations;
- §5, small types and the universe: the code map ⌜A⌝ and ⌜A⌝*El = A as
  types;
- §8.1, posets: Lemma `lem:el-yon`.

Also read `sag-model/M1.md`, steps 3 and later (universe, univalence
bridge, the caveats about `elTr` and `comp-idr`).

Relevant files (all in `sag-model/`):

| File | Contents |
|---|---|
| `FibCwF.seg` | `FC` (CwF of structured types), `MoveNat`, `PiN`, `FPi`, `fibPi` |
| `FibUniv.seg` | `Cod`, `Dec` (El along `clMap c`), `Dec-nat`, `fibUniv` |
| `CwFU.seg` | `Univ[l, C].UnivStr` (Cod, Cod-nat, Dec, Dec-nat) |
| `CUniv.seg` (core) | `U0 X = Σ (A : PTy[yX]) Cl(yX, A)`, `uAct`, `codeU`, `UCtx`, `EGen`, `fib0` |
| `CElC.seg` | El along a code map `c : D -> U` (`Fam[D,c].ElTy`, `.fib` = elFib moved along c), `elSub`, `ElCong`, `Yon` (El along the code of F over yZ is F, on types), `elCnat` |
| `CPosEl1-4.seg` | El is fibrant on posets (`CPosEl4.elFib`), glued from the codes' own compositions |
| `CPosEl5.seg` | **`lem:el-yon` formalised**: for F in U(Z), El's fibration moved along the Yoneda cart of F is F's own (`law`) |
| `CSmall.seg`, `CSmallFull3.seg`, `CFibFinal.seg` | small types over large contexts, `up`, `smallC` |
| `VLift.seg`, `VCode.seg` | lifting iterative sets k -> l, `liftV` preserves `mkV` etc. |

## 4. The informal argument (checked by hand, 2026-11-23)

Let Γ be a context and (A, c) a small fibrant type over Γ.

1. **Code map.** ⌜A⌝ρ := (A ρ̂, c ρ̂) ∈ U(X) for ρ ∈ Γ(X), where ρ̂ : yX → Γ
   is the Yoneda map and c ρ̂ is c moved along ρ̂. It is natural by the move
   laws and the Yoneda laws. Equivalently ⌜A⌝ ∘ ρ̂ = (⌜A⌝ρ)^, the Yoneda
   code of ⌜A⌝ρ.
2. **Underlying types.** T(⌜A⌝) = ⌜A⌝*El has fibre (Aρ̂)(X, id) =
   A(X, ρ̂ id). This equals A(X, ρ) up to `comp-idr` (`model.tex` §5.2;
   `CElC.Yon` does the Yoneda case). Types form a set, so this
   propositional identity law is enough.
3. **Structures: reduce to Yoneda points.** Restrict the structure of
   T(⌜A⌝) (elFib moved along ⌜A⌝) along ρ̂. By the move law for composites
   it is elFib moved along (⌜A⌝ρ)^. By `lem:el-yon` (`CPosEl5.law`) this
   is the structure of ⌜A⌝ρ, which is c moved along ρ̂.
4. **Structures: locality.** A relative contractibility structure k over Γ
   is determined by its values k(ρ, φ, u) (`lem:rc-ext`). The value of the
   moved structure ρ̂*k at the generic point id equals k at ρ̂(id) = ρ,
   through the cart (`con:move`). For compositions the points are points
   of the line context. Since the interval is tiny on posets
   (yX × I = y(X × [1])), a line of Γ at X is a point of Γ at X × [1], so
   again a Yoneda point. Hence two structures that agree after moving along
   every Yoneda point are equal. With step 3: the structure of T(⌜A⌝) is c.
5. **Π-code.** Set pic a b := ⌜Π(T a, T b)⌝. Two more lemmas are needed:
   - (S) Π of small types is small. The fibres of FibCwF's Π at level a+,
     on types with level-a fibres, are the lifts (`smallC` / `liftV`) of
     the level-a Π-fibres. Use the `VLift` lemmas: liftV preserves `mkV`
     and Π-codes.
   - (N) ⌜A⌝σ = ⌜Aσ⌝ (Huber: ⌜A⌝σ = ⌜Aσ⌝). This gives `pic-nat` together
     with `Pi-nat` (`PiN.law`) and `Dec-nat`.

   Then T(pic a b) = Π(T a, T b) by step 4.

Risk points:
- Step 4 relies on the move's value at the generic point being literally
  k at ρ̂(id), plus a transport along ρ̂ id = ρ. This must line up with how
  `FC.subS` / `clSub` move structures (`CFibSub` carts).
- Step 3 needs the move along the composite ⌜A⌝ ∘ ρ̂ to match the
  composite of moves with the right carts (`CCartLaws2.compFib`,
  `congFib`).
- (S) may need care with the levels of `FibCwF[a, a+]`.

## 5. Plan

- **U0. Locality lemma** (new file, e.g. `FibLocal.seg`). Two fibration
  structures on a type over Γ that agree after moving along every Yoneda
  point (of the line context) are equal. Do this first and report: it
  decides whether the approach works.
- **U1. Code map and decoding** (e.g. `FibName.seg`).
  - Define ⌜A⌝ for (A, c) small fibrant over Γ, natural (N).
  - Prove `Dec G ⌜A⌝ = (A, c)` in `FC.STy G`, by steps 2–4.
  - Also prove ⌜Dec c⌝ = c (Huber's second equation). It is not needed
    for T_E, but it is cheap and makes the universe a strict classifier.
- **U2. Smallness of Π** (e.g. `FibPiSmall.seg`). (S) as above.
- **U3. Π-code** (e.g. `FibUnivPi.seg`).
  - `pic`, `pic-nat` and `Dec-pic : Dec G (pic a b) = Pi G (Dec a) (Dec b)`.
  - Package it as a record extending `UnivStr` (a "universe closed under
    Π"); `M1.md` calls this the closure record.
- **U4. `TEModel[0]` instance and the Russell semantics.**
  - Integration decision first. The instance needs `EhrhardTEModel.seg`
    (DOMAIN/UNIT) and `fibCwF` / `fibPi` / `fibUniv` + U3 (sag-model) in one
    checker run, i.e. the indexed checker plus the `opaque` fix (section 3).
  - Options: copy the needed DOMAIN/UNIT files (syntax cone + TEInterp +
    RSem, about 70 files) into a new directory next to sag-model, or
    vendor sag-model into DOMAIN/UNIT (hundreds of files).
  - Ask the user before choosing.
  - Then instantiate RSem at N = 0 and check a closed example (as
    `RSemCheck.seg` does for V).
- **U5. Documentation.** Update the paragraph "A univalent model with one
  universe" in §13 of `DOMAIN/UNIT/gat-ehrhard.tex`; it currently states
  the informal argument and "not formalised yet". Re-read the file right
  before editing: other sessions edit it too.

## 6. Checklist

DONE 2026-11-23: U0-U3 in sag-model (FibLocal*, FibName*, FibPi*, FibUnivInj,
CwFUnivPi, FibUnivPi); U4 in UNIT/russell-posets (PosetTEModel, PosetRSemCheck,
check.py: 15288 declarations, 0 failed); indexed checker ported to the main
checker's lock resolution; U5 in gat-ehrhard.tex section 13.

- [x] U0 locality lemma (reported to the user)
- [x] U1 code map, T(⌜A⌝) = A as fibrant types, ⌜T c⌝ = c
- [x] U2 Π of small types is small
- [x] U3 Π-code with strict decoding and naturality
- [x] U4 TEModel[0] instance, Russell semantics at N = 0 (integration decided with the user)
- [x] U5 tex paragraph updated
