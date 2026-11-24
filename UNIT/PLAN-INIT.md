# PLAN-INIT: initiality of the term model of T_E (bounded levels N)

Plan, 2026-11-24. Orchestrated by the main session; several agents work in
parallel on disjoint files. Read this whole file before touching code.

## 1. Goal

For every level bound N and every Ehrhard model M of level N
(`EhrhardTEModel.TEModel[N]`, at the same universe level l as the syntax):

1. **Term model.** The derivable judgements of T_E (`GAT.seg`, `GDer`)
   modulo judgemental equality form a `TEModel[N]`, called `TM`.
2. **Morphisms.** A notion of (strict) morphism of `TEModel[N]`s:
   maps of contexts, substitutions, types and terms that preserve every
   operation of the record.
3. **Existence.** The interpretation of `TEInterp` (`TEInterpSound.sound`)
   descends to the quotients and gives a morphism `TM -> M`.
4. **Uniqueness.** Every morphism `TM -> M` agrees with it (pointwise, on
   contexts, types, terms and substitutions).

Corollary for the paper: T_Russell (via `RGAT`, Theorem 28 and uniqueness of
lifting) is in bijection with the elements of the initial model; at N = 0,
unique morphisms into the V, poset and simplicial models. The strong form
(Russell's own term model with implicit substitution is an isomorphic
model) is out of scope.

## 2. Ground rules (from the user)

- **New files only**, prefix `Init` (e.g. `InitQuot.seg`). Do not edit any
  existing file. Do not touch the user's untracked files (`Syntactic*`,
  `SmallQuotient.seg`, `QuotientPresheaf.seg`, `Scott*`, `Presheaf*`,
  `_dev*`, ...): you may READ them for technique, and copy code from them
  into new `Init*` files (say so in a comment).
- **No git** operations that change state (no add, commit, stash, checkout).
- **Wording**: "U : U", never "Type:Type". Status plainly: proved / open /
  stuck on X.
- **Checks fast**: each file should check in seconds; split files by
  groups of operations/rules.
- **Plant an error** in each new file after it first checks green, see it
  rejected, restore.
- **Checker** (indexed families):

      SEG=/Users/coquand/CANONICITY/unit-indexed/dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg
      cd ~/DOMAIN/UNIT && $SEG GATCheck.seg     # existing cone, 0 failed

- **Own driver per agent**: `InitCheck<Part>.seg` (e.g. `InitCheckF.seg`),
  importing what you need. The final `InitCheck.seg` is assembled by the
  orchestrator.
- **Stop only for a conceptual problem** (a statement here is false, a
  needed principle is missing, a level problem that cannot be solved
  locally), or if an existing file must change. Otherwise continue to the
  end of your part, then report: what is proved, files, checks run.

## 3. Facts to use

- Syntax and rules: `GAT.seg` (`GE`, `GJ`, `GDer`, inside module
  `BoundedSyntax (N)`; see `GATCheck.seg` for the import cone).
  Note: `GDer` has no rule for symmetry or transitivity of context
  equality; they are derived in `RGAT.seg` (`cx-sym`, `cx-trans`).
  Presuppositions: `GPresup.seg` (`gpresup`). Lean rules: `GLean.seg`.
- Models: `EhrhardCwF.seg` (`CwF`, `PiStr`), `EhrhardTEModel.seg`
  (`TEModel[N]`).
- Interpretation: `TEInterp.seg` (`Interpret[l,N,M]`), `TEInterpBase`
  (telescopes `Tel`, `ctx`, `Partial`, `Denotes`), `TEDenote` (`meaning`,
  `CtxDown`, `TyDown`, `TmDown`, `SubDown`), `TEInterpJudgement` (`SoundJ`,
  functionality lemmas), `TEInterpSound` (`sound : (J : GJ) -> GDer J ->
  SoundJ J`). Contexts denote telescopes; `ctx (extend g a) = C.ext (ctx g) a`
  definitionally.
- Quotients: `SmallQuotient.seg` (user's, untracked) has effective small
  quotients `Quot (A) (rel) ...` with `inc`, `induction` (into
  propositions), `relates`, `effective`, `set`, `Descend` (maps into a set
  at level l, with a propositional `beta`), `DescendLarge`. They need the
  parameters `ua`, `images`, `surjections` (see
  `SyntacticCategoryCheck.seg` for how a driver supplies them;
  `Replacement.seg`, `Truncation.seg`, `TruncationCombinators.seg`,
  `Axioms.seg`, `FunExtUA.seg` are tracked). Copy what you need into
  `InitQuot.seg`.
- The carriers need NOT be sets (the quotient is a set). Derivations go
  under propositional truncation: write `||J||` for
  `Truncation[l].Trunc[GDer J].carrier`.

## 4. Design of the term model (fixed; deviations must be reported)

Sorts are quotients **fibrewise over a fixed class of contexts**, so that
no dependent quotient elimination is needed:

- `CtxPre = (G : GE) * ||gjwf G||`, relation `||gjeqcx G D||`
  (reflexivity `gc-refl`, symmetry/transitivity from `RGAT`).
  `Ctx = quotient`; `cls G h : Ctx`.
- `TyPre (c : Ctx) = (G A : GE) * (h : ||gjty G A||) * Id Ctx (cls G _) c`
  (the context's well-formedness from `gpresup`), relation
  `||gjeqty G A B||` (move along the context equality obtained from
  `effective` and `gt-cx`/`ge-cx` where needed).
- `ElPre (c) (T : Ty c) = (G A a : GE) * (h : ||gjtm G a A||) *
  Id (Ty c) (clsTy ...) T`, relation `||gjeqtm G a b A||`.
- `SubPre (d c : Ctx) = (D s G : GE) * ||gjsub D s G|| * Id Ctx [D] d *
  Id Ctx [G] c`, relation `||gjeqsub D s t G||`.

Operations are defined for fixed context classes by `Descend` (twice for
two arguments: descend into a function set), with propositional
**beta lemmas** on representatives, e.g.
`subT d c (clsTy G A) (clsSub D s G) = clsTy D (gsb A s)`.
Transport in `El c` along a path `T = T'` in `Ty c` only changes the
propositional last component: prove this once (by `idJ`) and use it for
every field whose type contains `subst`.

Every field of `TEModel[N]` (`cwf`, `isSetCtx`, `products`, `univ`,
`decode`, `pic`, `uc`, `lf`, and all equations) is then proved by quotient
induction (targets are paths in sets, hence propositions), beta lemmas,
and `relates` with the corresponding `GDer` rule.

## 5. Morphisms (fixed shape; details in `InitHom.seg`)

`record Hom (M M' : TEModel[N])` with
`ctx : M.Ctx -> M'.Ctx`, `sub`, `ty`, `tm` over `ctx`/`ty`, and one law per
operation of `TEModel[N]` (nil, ext, id, o, eps, p, q, lift, sec, subT,
subt, Pi, the Pi-iso maps, univ, decode, pic, uc, lf), stated with the
transports forced by `ctx-ext`, `ctx-nil`, `ty-subT`. Prefer stating the
term-level laws as equalities in total spaces `(A : Ty' G') * El' G' A`
(Σ-paths) where this removes transports. Uniqueness is stated pointwise:
for H, H' : Hom TM M, `H.ctx c = H'.ctx c`, and the type/term/substitution
components agree as elements of the total spaces over the context.

## 6. Parts and agents

| Part | Files | Depends on | Content |
|---|---|---|---|
| F | `InitQuot`, `InitSorts`, `InitOps*`, `InitCheckF` | — | quotient library; sorts; all operations with beta lemmas; the El-transport lemma |
| H | `InitHom*`, `InitCheckH` | — | morphism record; identity morphism as a sanity check; lemmas turning each law into total-space form |
| A | `InitModel*`, `InitCheckA` | F | all equations: `TM : TEModel[N]` |
| E | `InitExist*`, `InitCheckE` | F, H | interpretation descends; it is a `Hom TM M` |
| U | `InitUniq*`, `InitCheckU` | F, H | every `Hom TM M` agrees with the interpretation (induction on `GDer`, generated case list like `TEInterpSound`) |
| T | `InitTheorem`, `InitCheck` | all | statement of initiality; driver; tex (orchestrator) |

F and H run first, in parallel. A, E, U run in parallel once F and H have
reported their interfaces (record field names, beta lemma names). E and U
need A only for the final statement (`Hom TM M` needs `TM : TEModel[N]`):
until A is done, state E and U over the **operations** of F (a record of
operations without equations, or directly the definitions), so that they
do not wait for A.

## 7. Log (agents append here: date, part, status, files, checks)


- 2026-11-24, Part H, DONE (proved, no postulates). Driver `InitCheckH.seg`:
  342 declarations, 0 failed, 0.09 s; `GATCheck.seg` still 0 failed.
  Planted errors rejected in every new file (Base, Laws, RelA, RelB, Step, Id).
  Files: `InitHom.seg` (module `Morphism (l, N, M, M')` importing
  `InitHomBase`, `InitHomLaws`, `InitHomRelA`, `InitHomRelB`, `InitHomStep`),
  `InitHomIdentity.seg` (module `Identity (l, N, M)` importing `InitHomId`).
  Use: `module Mo = InitHom.Morphism[l,N,M,M'] ; open Mo.InitHomBase ; open Mo.InitHomLaws ; ...`.
  * `InitHomBase`: total spaces of M' (`TyT'`, `Term' X`, `TmT'`, `SubT'`,
    `CodT'`, `DomT'`, `CodeT' n`, `CodeF' n X`, `iota n`), transports
    `mvTy`, `mvEl`, `mvCode` with `tot-mv*`, fibre lemmas `fib`, `fibe`,
    `fibTy`, `fibTm`, `fibEl`, `codPath`, `domPath`, `iota-inj`, `lift-el`.
  * `InitHomLaws`: `record Hom` (fields `ctx sub ty tm`, laws `ctx-nil ctx-ext
    sub-id sub-o sub-eps sub-p sub-lift sub-sec ty-subT ty-Pi ty-univ ty-decode
    tm-subt tm-q tm-lam tm-pic tm-uc tm-lf`; derived `ext' mv-ty mv-el code
    dec-ext mv-code`); relations `RCtx RTy RTm RSub`; `record Agree (H H')`
    (`ctx-ag ty-ag tm-ag sub-ag`). No field for Pi-iso.fun: derived (`rel-fun`).
  * `InitHomRelA/B`: relational form `rel-*` of every law (related arguments
    give related results), canonical images `canon-ty-ext`, `canon-tm-ext`,
    `code-rel`, `code-path`, `canon-code-ext`.
  * `InitHomStep`: uniqueness steps `ag-*` for two morphisms H, H' (one per
    operation incl. `ag-fun`), `AgC AgT AgE AgS`, `mkAgree`.
  * `InitHomId`: `idHom : Hom` (all laws refl), `agree-refl`.
  Open: composition of morphisms not done (not needed for initiality).

- 2026-11-24, Part F, DONE (proved, no postulates). Driver `InitCheckF.seg`:
  4569 declarations (whole GATCheck cone included), 0 failed, 1.9 s.
  Planted errors rejected in every new file (Quot, Sorts, OpsCtx, OpsSub,
  OpsExt, OpsPi, OpsU, OpsTest). Driver shape:
  `module InitF (ua) (images) (surjections) (N : Base.Nat) { fe ; propUA ;
  import Truncation ; import TruncationCombinators ; import InitQuot ;
  import InitSorts ; import InitOpsCtx ; import InitOpsSub ; import InitOpsExt ;
  import InitOpsPi ; import InitOpsU ; import InitOpsTest ; }` after
  `import GATCheck ; open GATCheck ; import Replacement ;`. Every Init file
  is a `level l` segment with `module B = BoundedSyntax[N] ; open B.GAT[l] ;
  open InitQuot[l] ; open InitSorts[l] ; open InitOps*[l]` (module aliases
  are not re-exported by `open`, so each file declares its own `B`, `GP`).
  * `InitQuot`: copy of SmallQuotient's Quot (inc, induction, relates,
    effective, set) + `rep`; mere existence `Sq sq sq-prop sq-rec sq-map..6
    sq-pair`; `Choice[W,B,sB,f,const]` (`elim : Sq W -> B`, `beta`).
  * `InitSorts`: `Pf J = Sq (GDer J)`, `pf-map..6`, presups `wf-ty wf-tm
    ty-tm wf-dom wf-cod`; derived rule `eqsub-cx` (GDer has no context
    conversion for gjeqsub: s = s gid = t gid = t, then gid s = gid t).
    Sorts and constructors (all proofs/paths are free arguments):
    `Ctx`, `cls G w`; `Ty c`, `clsTy c G A h w pc`; `El c T`,
    `clsEl c T G A a h hA w pc pT`; `Sub d c`, `clsSub d c D s G h wD wG pd pc`
    (pc : Id Ctx (cls G w) c, pT : Id (Ty c) (clsTy ..) T). Sets
    `isSetCtx isSetTy isSetEl isSetSub`. Per sort: `-eq` (relates; relation
    at the context/type of the FIRST representative, so the second may sit
    over any other raw context of the class), `-irr`, `-eff`, `same-*`,
    `*-ind`, `Rep*`/`mkRep*`/`rep-*` and accessors (`rtG rtA rtH rtW rtP rtE`,
    `reG reA rea reH reHA reW reP reT reE`, `rsD rss rsG rsH rsWD rsWG rsPD
    rsPG rsE`), `same-rc same-rt same-re same-rs`, `ty-move clsTy-move
    rt-move re-move re-eq re-ty`. Transport: `tr-ty`, `tr-sub`, `tr-el`
    (families over any X), and the plan's `el-transport c T T' e ...`.
  * Operations (`InitOpsCtx/Sub/Ext/Pi/U`), types exactly those of
    `TEModel[N]`: `nil ext id eps o subT subt p q lift sec Pi pi-fun pi-inv
    univ decode pic uc lf` (Pi-iso: `fun = pi-fun` raw `app-q A B f =
    gapp (A p) (B lift_A(p)) (f p) q`, `inv = pi-inv` raw `glam`; levels
    `EhrhardTEModel.LevelAt N`/`StrictAt N`). Beta lemmas `<op>-beta`: for
    ANY representatives (Rep* args) of the arguments, the op is the class of
    the evident raw expression, with ARBITRARY raw context (and raw type,
    for terms), derivation and paths of the result; `id- eps- p- q- univ-
    uc-beta` need no representative. Helpers `ext-beta'`, `ext-der`,
    `subT-der subT-beta' subT-rep p-rep Pi-der Pi-rep univ-rep decode-rep
    re-ctx subt-der`, GDer lemmas `app-q-der`, `app-q-eq`.
  * `InitOpsTest`: usage check, the CwF fields `subT-id`, `subt-id` (the
    latter with `el-transport`), proved; Part A may reuse them.
  Deviations from section 4 (technical, recorded): (1) no nested Descend:
  each operation is ONE unique choice (`Choice`) over the product of the
  representative types `Rep*` of all its arguments; this also handles the
  operations whose result type depends on an argument (p, q, lift, sec,
  Pi, pic, ...) without dependent elimination or funext. (2) Rep types
  carry free well-formedness witnesses and (for El) the type derivation.
  (3) Relations at the first representative's context, symmetric/transitive
  by context conversion (`ge-cx`, `gm-ecx`, `eqsub-cx`). cx-sym/cx-trans
  used from `B.RGAT`, not copied. Open: all equations of TEModel (Part A).

- 2026-11-24, Part A: **InitModelShape ready.** File `InitModelShape.seg`
  (`level l` segment, opens InitSorts/InitOpsCtx/Sub/Ext/Pi/U[l]; import
  it after the F files, as in driver `InitCheckA.seg`: 4620 declarations,
  0 failed). `record Eqs` = all equation fields of CwF / PiStr / TEModel[N]
  for F's operations, same names as in the records (`o-idl ... q-sec`,
  `Pi-nat`, `Pi-fun-inv`, `Pi-inv-fun` (the two Iso laws), `Pi-iso-nat`,
  `univ-nat decode-nat el-lf el-pic el-uc lf-pic lf-uc lf-lf pic-nat
  uc-nat lf-nat`; derived copies `p-lift-T p-sec-T code-sub up-code
  lift-binder`). `mk (e : Eqs) : EhrhardTEModel[l].TEModel[N]` (via
  `mkCwF e`, `mkPi e`, `mkIso e`): operations are F's definitionally,
  e.g. `(mk e).cwf.subT = subT`, `((mk e).products.Pi-iso c A B).fun =
  pi-fun c A B` by refl (`mk-subT`, `mk-pi-fun`, `mk-lf`). Set-ness is F's.
  Next: `eqs : Eqs`, `TM = mk eqs` in `InitModel*.seg`.

- 2026-11-24, Part E, DONE (proved, no postulates). Driver `InitCheckE.seg`:
  4960 declarations (F cone + InitModelShape included), 0 failed, 2.5 s;
  `GATCheck.seg` still 0 failed. Planted errors rejected in every new file
  (Base, Maps, LawsA, LawsB, Hom; also a missing Hom field is rejected).
  Driver shape: as InitCheckF plus `import InitHom` at top level and
  `import InitModelShape` after the F files, then
  `module Exist (l : Level) (M : EhrhardTEModel[l].TEModel[N]) { import
  InitExistBase ; import InitExistMaps ; import InitExistLawsA ; import
  InitExistLawsB ; import InitExistHom ; }` (segments without `level`,
  free names l, N, M).
  **Interface:** `InitExistHom.exist (e : InitModelShape[l].Eqs) :
  InitHom.Morphism[l,N,mk e,M].InitHomLaws.Hom` (= `ExistHom[e].exHom`);
  for Part T: `exist eqs` with `TM = mk eqs`.
  * Method: types/terms/substitutions are interpreted at the FIXED
    telescope `tel c` of their context class (no transport): `tel c : Tel`,
    `hty c T : C.Ty (ctx (tel c))`, `htm c T t`, `hsub d c s` (InitExistMaps),
    each by `Choice` on representatives; weak constancy = soundness of the
    equality judgement + functionality. Down lemmas for ANY representative:
    `tel-down`, `hty-down(-r)`, `htm-down(-r)`, `hsub-down(-r)`. Hom.ctx c =
    `hctx c = ctx (tel c)`.
  * `InitExistBase`: soundness values are propositions (`ctxval-prop`,
    `tyval-prop`, `termat-prop`, `subval-prop`), values from mere
    derivations `cval tval mval sval`, conversions `cx-conv ty-conv tm-conv
    sub-conv`, fibre functionality `ty-fn tm-fn sub-fn`, moves along a
    path of telescopes with ARBITRARY context path `ty-down-mv tm-down-mv
    code-down-mv`, total-space lemmas `sub-tot tm-tot`.
  * Laws (each: representatives, F's `Op*.beta`, the down lemmas of
    TEInterpIntro/Formers, functionality): `InitExistLawsA`: `ex-ctx-nil
    tel-ext ex-ctx-ext ex-sub-id ex-sub-o ex-sub-eps ex-sub-p ex-ty-subT
    ex-sub-lift ex-sub-sec ex-tm-subt ex-tm-q`; `InitExistLawsB`: `ex-ty-Pi
    ex-tm-lam ex-ty-univ ex-ty-decode ex-tm-pic ex-tm-uc ex-tm-lf`, with the
    Hom transports reproduced (`my-mv-ty my-mv-el my-code my-dec-ext
    my-mv-code`), definitionally those of the built Hom.
  * The laws do not use `e` (they hold for F's operations); only the final
    `Hom` value mentions `mk e`. Nothing open in Part E.

- 2026-11-24, Part U, DONE (proved, no postulates). Driver `InitCheckU.seg`
  (module `InitU (ua) (images) (surjections) (N)`, imports F files,
  `InitModelShape`, then the U files; `import Paths ; import InitHom ;` at
  top): 5002 declarations, 0 failed, 2.7 s; `GATCheck.seg` still OK.
  Planted errors rejected in every new file.
  **Interface**: `InitUniq.seg` (`level l` segment):
  `init-uniq (e : Eqs) (M' : EM.TEModel[N]) (H H' : InitHom.Morphism[l,N,mk e,M'].InitHomLaws.Hom)
     : InitHom.Morphism[l,N,mk e,M'].InitHomLaws.Agree[H, H']`,
  also as `Uq[e,M'].V[H,H'].agree` with components `ag-ctx ag-ty ag-el ag-sub`.
  Files:
  * `InitUniqTot` (F level): total spaces `TotTy TotTm TotSub`, canonical
    classes `cTy cEl cSub`, points `tT tE tS`, reps `rT rE rS`; `-gen`
    (class over any context/type with paths = canonical point), `-from`
    (element equal to a class), conversions `tT-cx tE-cx tE-conv tE-eq
    tS-cx`; GDer lemma `app-sec-eq` (gsb (app-q A B f) (gsec A a) =
    gapp A B f a, by gm-eta, gm-eapp, gm-beta); `lower-bound`.
  * `InitUniqCls`, `InitUniqClsTm` (F level): one class lemma `cl-<op>` per
    formation rule (nil ext id comp eps p lift sec subT Pi univ decode q sb
    lam app pic uc lf): op at the canonical argument classes = canonical
    class of the conclusion (beta lemma + -from); argument classes named
    there (`eC eP tyB elB codeC codeg pUg sT sE sP piT pP fC funC secC
    appT dC dE dP bC`). app = subt (Pi-iso.fun f) (sec a), then app-sec-eq.
  * `InitUniqBase` (module `Uq (e) (M')`, inner `V (H H')`): `QC QT QE QS`,
    `QJ : GJ -> U l` (Top on equalities), moves `mvC mvT mvE mvS`,
    propositions `propC propT propE propS`, `ihT-at ihE-at ihS-at`.
  * `InitUniqCaseA/B`: the 23 non-equality cases (formation: ag-<op> of
    InitHomStep at the canonical classes, moved along cl-<op>; conversion
    gs-cx gt-cx gm-conv gm-cx: IH moved along -cx/-conv).
  * `InitUniqInd`: `uniq : (J : GJ) -> GDer J -> QJ J`, GENERATED by
    `gen_init_uniq.py` (equality rules -> tt; others -> case-<rule> with all
    binders and IHs).
  * `InitUniq`: quotient induction + sq-rec (targets are paths in sets of
    M') + uniq + ih*-at.
  Not needed from Part A: any equation of `e` (uniqueness holds for every
  e). Nothing open in Part U.

- 2026-11-24, Part A, DONE (proved, no postulates). Driver `InitCheckA.seg`
  (module `InitA (ua) (images) (surjections) (N)`, same shape as InitCheckF):
  4906 declarations (GATCheck cone + F + A), 0 failed, 2.5 s; `GATCheck.seg`
  and `InitCheckF.seg` still 0 failed. Planted errors rejected in every new
  file (Shape, Rep, RepOps, Cat, Ext, Pi, U, Model).
  **Interface**: `InitModelShape` (`record Eqs`, `mk (e : Eqs) : TEModel[N]`,
  see the entry above); `InitModel`: `eqs : Eqs`, `TM : EhrhardTEModel[l].TEModel[N]
  = mk eqs` (operations definitionally F's: `TM-subT TM-pi-inv TM-decode` by refl).
  Files:
  * `InitModelRep`: normalised representatives over FIXED raw contexts with
    GDer (not Pf) derivations: `CP c`, `NT c g T`, `NS d c gd gc s`,
    `NE c g T x t`; `with-cp/nt/ns/ne` (they merely exist; eliminators into
    props); `nt-eq ns-eq ne-eq` (relates); transport `cp-tr nt-tr ns-subst
    ne-subst`; `ns-move` (other raw contexts), `ne-retype` (other raw type).
  * `InitModelRepOps`: every operation on normalised reps (`nil-cp ext-cp
    id-n eps-n o-n subT-n subt-n p-n q-n lift-n sec-n Pi-n pi-inv-n pi-fun-n
    univ-n decode-n dext-cp pic-n uc-n lf-n`, codes `NC n c g a`).
  * `InitModelCat` (o-idl o-idr o-assoc eps-uniq subT-id subT-o subt-id
    subt-o), `InitModelExt` (lift-id lift-o p-lift p-sec sec-o lift-p-sec-q
    q-lift q-sec), `InitModelPi` (Pi-nat Pi-fun-inv Pi-inv-fun Pi-iso-nat;
    GDer lemma `app-q-beta`), `InitModelU` (univ-nat decode-nat el-lf el-pic
    el-uc lf-pic lf-uc lf-lf pic-nat uc-nat lf-nat; `cs-n` = rep of a
    substituted code). Each equation: with-cp/with-n* (goal a path in a
    set), both sides by RepOps, one GDer rule (only Pi-fun-inv needs a
    chain: `app-q-beta`, by gm-lam-sb, gm-eapp, gm-beta, gm-sb-comp,
    gq-lift-p-sec-q, gm-sb-id). Fields with a transport are proved for an
    ARBITRARY path (`-gen`, or modules `Nat (un)`/`Nat2 (dn)` for any proof
    of univ-nat/decode-nat, top-level wrappers `*-u`); `InitModel` applies
    them to the record's paths (copies `plT psT` of p-lift-T, p-sec-T).
  No equation of TEModel[N] needed anything beyond its GDer rule. Nothing
  open in Part A.

- 2026-11-24, Part T (orchestrator): DONE. `InitTheorem.seg` (existence =
  `Exist[l,M].InitExistHom.exist InitModel[l].eqs`, `uniqueness`,
  `uniqueness2`), driver `InitCheck.seg` (module `Init (ua) (images)
  (surjections) (N)`, submodules `Exist (l) (M)`, `Initial (l) (M)`):
  5516 declarations, 0 failed, 3.0 s; planted error in `uniqueness`
  rejected, restored. gat-ehrhard.tex §14 paragraph "Initiality" with
  Theorem (initiality), §15 paragraph and table rows; PDF 14 pages.
