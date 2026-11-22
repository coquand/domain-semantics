# Next session: finish sterbac4.pdf (after §4 with Ehrhard-GAT, 2026-11-22)

Read first: `UNIT/PLAN-GAT.md` (design of §4, file list, admissible premises),
`UNIT/gat-ehrhard.tex` (the note). Paper text: `sterbac4.pdf` in DOMAIN root.

Checker: from `UNIT/`,
  SEG=/Users/coquand/CANONICITY/unit-indexed/dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg
  $SEG GATCheck.seg        (704 decls, 0 failed, 0.2 s)
Full repo check: `python3 UNIT/check.py` from DOMAIN (All.seg imports the §4 files at the end).
Nothing committed yet (branch hide-old-archives); ask before committing.
NEXT: item 2 below (GAT inversion by transfer).

## State of the paper

| sterbac4 | status | where |
|---|---|---|
| §4 GAT <-> T_Tarski (L15-19, Thm 20) | DONE, Ehrhard variant, bare GAT syntax | UNIT (seg) |
| §5 T_Tarski <-> T_Russell | DONE | ERT/ (Agda --safe) |
| §6 T_Russell <-> T_PTS (joins/coercions, no normalisation) | DONE | ERT/StripUniqNF, SectionR |
| §7 internal levels / constraints | DONE | BCDE4/ |
| presup (L22-24) + lean systems | DONE | UNIT TPresup TLean GPresup GLean |
| §2 Thms 8-10 (inversion) for the GAT | MISSING | |
| Remark 14 (models interpret T_PTS) | MISSING (largest) | |

## Agreed order of work

1. DONE 2026-11-22: presuppositions. TPresup (T_Tarski, Lemmas 22-24),
   TLean (paper A.2 rules, translations both ways), GPresup + GLean (GAT).
   GAT got one new rule gs-cx (context conversion of both ends of a
   substitution); without it the GAT presup lemma is FALSE
   (lift_A(id) = id : G.A[id] -> G.A). Only gap to A.2: sym+trans instead of
   the euclidean rule (translating needs refl at a non-subderivation,
   i.e. presup + substitution lemma for the A.2 system itself).

2. **Inversion for the GAT (Thms 8-10) by transfer**: GAT judgement
   -> (Thm 16) T_Tarski -> inversion in T_Tarski -> back by Lemma 18/19
   (unique-ty in Thm20.seg). Needs in seg: U-injectivity, U/Pi no-confusion
   and Pi-injectivity for (unscoped) T_Tarski. ERT has U-inj/no-conf for T_T
   (ERT/Injectivity.agda, from MIN finite-element model) and Pi-inj only for
   T_R (ERT/PiInjectivityR.agda, adequacy). UNIT has Pi-injectivity for MIN's
   U:U syntax via the displayed logical relation (README.txt: ScottGlueing*,
   IndependentProofRelevant). Decide: adapt UNIT's relation to levelled
   T_Tarski, or derive T_T Pi-inj from T_R via §5. User directive (memory):
   inversion from the DOMAIN MODEL, not syntactic confluence.

3. **One end-to-end theorem GAT ≅ PTS**: §4 is seg/unscoped, §5-6 Agda/scoped.
   Recommended: port the §4 seg files (~3.2k lines: TSyntax..Thm20) to Agda
   over ERT's TarskiSyntax/TarskiTyping (scoped Fin n), or add an
   unscoped<->scoped bridge. Alternative: port ERT to seg (~6k lines).
   Compile-time rule: <=20 s per file.

4. (Optional) Dybjer <-> Ehrhard GAT with the paper's context annotations.
5. (Later) Remark 14: partial interpretation of the bare GAT into an
   Ehrhard CwF (~/CANONICITY/unit/core/CwF.seg record) + soundness.

## Practical notes from §4

- Long seg terms: generate with small Python scripts (see style of L18Eq/L18BE/L19);
  a paren-balance checker per top-level declaration saved a lot of time.
- seg accepts eta for functions and reduces splits under lambdas
  (e.g. idv (suc i) = gsb (idv i) gp definitionally).
- GAT rule argument orders: read GAT.seg; GSound.seg's `sound` split lists
  every constructor with binder names (useful to generate other splits).
