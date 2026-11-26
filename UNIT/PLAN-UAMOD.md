# PLAN-UAMOD: univalence of the category of Ehrhard models (TEModel[N])

Plan, 2026-11-26. Orchestrated by the main session; agents work in
parallel on disjoint files. Read this whole file before touching code.
Continues PLAN-INIT.md (read its sections 2, 3 and the Part C log).

## 1. Goal

The precategory of models of level N with strict morphisms (`HomS`,
`InitModelsCat.pre`) is univalent, in the form of `Category.seg`:
`Univalent preS`, via `Category.FromTotal` (it suffices that
`Singl x = (y : ob) * Iso x y` is a proposition for every object x).

Checker fact (tested 2026-11-26): records have NO eta (`e = new
IsoData[.. e.fun ..]` is not refl). So with objects the record
`TEModel[N]`, `Id TEModel M M'` cannot be characterised, and the record
precategory `pre` cannot be proved univalent. Objects are therefore a
nested Sigma type `TEModelS` (all fields of CwF, PiStr, IsoData and
TEModel flattened), with `toRec : TEModelS -> TEModel[N]`, and
`preS` = the precategory with `ob = TEModelS`,
`hom x y = HomS (toRec x) (toRec y)`, identity and composition from `pre`.

## 2. Ground rules (as PLAN-INIT)

- New files only, prefix `InitUA`. Do not edit existing files (in
  particular not `Init*.seg` of PLAN-INIT, `Category.seg`, `Prelude.seg`).
  Do not touch the user's untracked files.
- No git operations that change state.
- Wording: "U : U", never "Type:Type". Status plainly: proved / open /
  stuck on X.
- Checks fast (seconds); split files.
- Plant an error in each new file after it first checks green, see it
  rejected, restore.
- Checker:

      SEG=/Users/coquand/CANONICITY/unit-indexed/dist-newstyle/build/aarch64-osx/ghc-9.6.7/seg-0.1.0.0/x/seg/build/seg/seg
      cd ~/DOMAIN/UNIT && $SEG InitCheckC.seg     # 0 failed

- Own driver per agent: `InitUACheck<Part>.seg`.
- Stop only for a conceptual problem (a statement here is false, a
  needed principle is missing) or if an existing file must change.
  Otherwise continue to the end of your part, then report: what is
  proved, files, checks run. Append a log entry to section 6.
- Checker facts: Sigma types have eta, Pi types have eta, `idJ` computes
  on `refl` definitionally (see `Category.IsoSet.idtoiso-refl`).

## 3. Proof architecture

Fix x : TEModelS, M = toRec x.

1. (Part I) `isIso` of `pre` is a proposition; an iso `f : pre.hom M M'`
   has components that are bi-invertible: `CompEqOver ...`
   (`InitUAEquiv.seg`: `BiInv` is a Sigma form of bi-invertibility).
2. B := (y : TEModelS) * (h : HomS M (toRec y)) * CompEq h.
   The map Singl x -> B, (y, h, i) |-> (y, h, comp-eq i), together with
   isProp B and isProp (isIso h), gives isProp (Singl x)
   (two elements with equal images have equal (y, h), and isIso is a
   proposition). No inverse morphisms need to be built.
3. isProp B: B is a retract (by Sigma reshuffling, round trip refl) of a
   layered type L = Sigma of blocks S, C1, C2, P, V, E, each block a
   family over the previous ones. L is contractible because each block,
   at the centre of the previous blocks (x's own data, identity maps,
   refl laws), is contractible (Parts S, C1, C2, P, V, E), and a Sigma
   over a contractible base whose fibre at the centre is contractible is
   contractible.
4. (Part G) assemble, `FromTotal`, `univalent : Univalent preS`.

## 4. Interface files (Phase 0, orchestrator)

- `InitUAEquiv.seg` (level l segment): `BiInv A B f`, `idBiInv`,
  `biinv-rec`, `rec-biinv`, `CompEqOver (Ctx Sub Ty El) (Ctx' Sub' Ty' El')
  (ctx sub ty tm)`.
- `InitUAObj.seg` (level l, free N): `Srt`, `Sets`, `Ops1`, `Ops2`,
  `OpsP`, `OpsV`, `Eqs` (29 equations), `TEModelS`; naming modules
  `S0[s]`, `S1[s,c1]`, `S2[s,c1,c2]`, `SP[..,pp]`, `SV[..,v]`, `SE[..]`
  (equation types `OIdl ... LfNatT`, derived `p-lift-T p-sec-T code-sub
  up-code lift-binder`), `Y[y]` (all components of y, and the record
  `Y[y].rec`), `toRec`, `fromRec`, `from-to` (refl).
- `InitUACat.seg` (free l, N, fe): `preS` (ob TEModelS, rest from `pre`).
- `InitUALib.seg` (level l): `Centred A a0 = (u : A) -> Id A a0 u`,
  `sing-l`, `sing-r`, `sigma` (Sigma over centred base, fibre centred at
  the centre), `pi` (funext), `pi-sigma`/`sigma-pi` (choice, definitional),
  `retract`, `prop`, `sigmaH` (base in U l+, fibre in U l: NO
  cumulativity in the checker, so mixed levels need this form).
- `InitUALayer.seg` (free l, N, fe, x : TEModelS): `M = toRec x`, `C`, `P`;
  `DataO s`, `CompEqO s d`, naming module `D0[s,d]` (ctx sub ty tm, total
  spaces Term TmT CodT SubT of the target); law modules `L1`, `L2`
  (`CtxExt` = ce), `LP` (mvTy mvEl mvTyS mvElS), `LV` (CodeF TyUniv codeS
  TyDecode decExtS mvCode mvCodeS); blocks `SBlk C1Blk C2Blk PBlk VBlk
  EBlk`, `L`; `HomTo y`, `B`, `toL`, `fromL`, `from-to-L` (refl);
  centres `idD idCE sb0 c1b0 c2b0 pb0 vb0 eb0 centre` (laws are refl:
  all transports reduce at the centre); statements
  `SContr C1Contr C2Contr PContr VContr EContr`.
  Driver shape: `InitUACheckLayer.seg` (module T (N) { import InitUAObj ;
  module C (l) (fe) { import InitUACat ; module X (x) { import
  InitUALayer ; } } }). Inside X refer to `InitUALayer.SBlk` etc. or
  `open InitUALayer`.

## 5. Parts

| Part | Files | Content |
|---|---|---|
| I | `InitUAIso*`, `InitUACheckI` | isIso prop; iso => CompEqOver (DONE) |
| S | `InitUABlkS*`, `InitUACheckS` | `SContr` (needs ua) |
| C1 | `InitUABlkC1*`, `InitUACheckC1` | `C1Contr` |
| C2 | `InitUABlkC2*`, `InitUACheckC2` | `C2Contr` |
| P | `InitUABlkP*`, `InitUACheckP` | `PContr` |
| V | `InitUABlkV*`, `InitUACheckV` | `VContr` |
| G | `InitUABlkE*`, `InitUAUniv*`, `InitUACheck` | `EContr`; assembly with the five other block proofs as module PARAMETERS (then instantiated at the end), univalence of preS |

Method for a block (suggested): at the centre every law of the block is
a path between x's operation (identity maps applied) and the new
operation, possibly in a total space over a set. Reorder the block
(Sigma reshuffles have refl round trips; use `InitUALib.retract`) so that
each new operation is followed by its law, turn each law into a pointwise
path in a fibre (over a set: `InitHomBase.fib`-style, or
`InitUAIsoLemmas.fib-any`), and contract operation+law as a singleton
(`sing-l`/`sing-r`, `pi`, `pi-sigma`), left to right with `sigma`. Later
laws mention earlier operations; after contracting an earlier pair to
its centre the later ones are at refl and reduce definitionally.

## 6. Log

- 2026-11-26, Part I: DONE (proved, no postulates; new files only).
  Driver `InitUACheckI.seg` (imports InitCheckC's cone + InitUAEquiv +
  the files below): 778 declarations, 0 failed, 0.29 s. `InitCheckC.seg`
  still 702 declarations, 0 failed. Planted errors rejected in all four
  new files, restored.
  Files and interface:
  * `InitUAIsoProp` (level k l, `module On (C : Category[k,l].Precategory)`):
    `inv-unique x y f u v : Id (C.hom y x) u.1 v.1`,
    `laws-prop x y f g`, and
    `iso-prop (x y : C.ob) (f : C.hom x y) : Prelude[l].isProp (C.isIso x y f)`.
    Use as `InitUAIsoProp[k,l].On[C].iso-prop`.
  * `InitUAIsoLemmas` (level l, generic): `fib-any` (over a set A, a path
    (x,b) = (y,b') gives subst e b = b' for ANY e : x = y), `pair-path`,
    `regroup`/`regroup-path` ((a,(b,c)) -> ((a,b),c)), and
    `module Fib (A sA F A' sA' F' c pi d rho r rt st)`: `back`, `sec-eq`,
    `ret-eq`, `biinv (a : A) : InitUAEquiv[l].BiInv (F a) (F' (c a)) (pi a)`
    (fibrewise inverse = rho then transport along r; section via
    subst-proj + fib-any).
  * `InitUAIso` (wrapper): `module IsoComp (l) (N) (fe) (M M' : TEModel[N])
    { import InitUAIsoComp }`.
  * `InitUAIsoComp` (segment of IsoComp; MC = InitHomS.ModelsCat[l,N,fe].InitModelsCat):
    `CompEq (f : MC.pre.hom M M') : U l` (abbreviation of the CompEqOver),
    `module On (f) (i)` with `ag1`, `ag2` (hom-agree of i.2.1, i.2.2),
    `eq-ctx eq-sub eq-ty eq-tm`, `compeq`; and
    `iso-compeq (f : MC.pre.hom M M') (i : MC.pre.isIso M M' f)
       : InitUAEquiv[l].CompEqOver M.cwf.Ctx M.cwf.Sub M.cwf.Ty M.cwf.El
           M'.cwf.Ctx M'.cwf.Sub M'.cwf.Ty M'.cwf.El f.1.1 f.1.2.1 f.1.2.2.1 f.1.2.2.2`.
    Use as `InitUAIso.IsoComp[l,N,fe,M,M'].iso-compeq f i`.
  Notes: the maps of compS are the composed maps definitionally, so
  Agree's fields are directly homotopies over the bases; Ctx: g.ctx is a
  two-sided inverse (ctx-ag of ag2 / ag1); Sub, Ty, El are Fib over the
  sets Ctx x Ctx, Ctx and TyT = (G : Ctx) * Ty G. Section and retraction
  maps are the same map. Nothing open in Part I.
- 2026-11-26, Part V: DONE (proved, no postulates; new files only).
  Driver `InitUACheckV.seg` (shape of InitUACheckLayer, imports
  `InitUABlkV` inside X after InitUALayer, `final : InitUALayer.VContr =
  InitUABlkV.v-contr`): 1053 declarations, 0 failed, 0.37 s.
  `InitUACheckLayer.seg` still 1009 declarations, 0 failed. Planted errors
  rejected in both new files, restored.
  Interface: `InitUABlkV.v-contr : InitUALayer.VContr` (inside X).
  File `InitUABlkV` (segment, free l N fe x): generic `piC` (Pi of centred
  pairs (f, law) is centred, by `retract` of pi-sigma/sigma-pi + `pi fe`),
  `sg1` (pointwise based path space); reshuffled block
  `R = (u : UT) * (dd : DT u) * PT u dd * UcT u * LfT u` (univ'+tu,
  decode'+td, pic'+law, uc'+law, lf'+law, with own copies `cS decE mvS`
  of codeS/decExtS/mvCodeS, convertible with LV's), `toR`/`fromR` (round
  trip refl), centres `u0 d0 p0 c0 f0`, contractions `hU hD hP hC hF`,
  assembled by `InitUALib.sigma`; `fromR r0` is `vb0` definitionally.
  Everything reduces as planned: at tu = refl codeS is the identity, at
  td = refl decExtS = trans refl (ap refl) = refl and mvCodeS is the
  identity. Nothing open in Part V.

- 2026-11-26, Part P: DONE (proved, no postulates; new files only).
  Files: `InitUABlkP.seg` (segment, free l N fe x), driver
  `InitUACheckP.seg` (InitUACheckLayer shape, `import InitUALayer ;
  import InitUABlkP ;` inside X): 1072 declarations, 0 failed, 0.34 s.
  `InitUACheckLayer.seg` still 1009 declarations, 0 failed. Planted error
  (wrong centre for fun') rejected, restored.
  Interface: `InitUABlkP.p-contr : InitUALayer.PContr` (inside X).
  Proof: PBlk at the centre is a retract (round trip refl) of
  Q = (w : W) * (v : VT Pi') * FunT Pi' inv', with
  W = (G A B) -> (P : Ty G) * Id (Ty G) (Pi0 G A B) P (centred: funext +
  sing-l, `cpi3`), VT Pi0 = (G A B b) -> (i : El G (Pi0 G A B)) *
  Id (Term G) (Pi0, inv0 b) (Pi0, i) (each fibre a retract of a singleton,
  via a copy of InitHomBase.fib, Term G a set; `cpi4`), and
  FunT Pi0 inv0 = (fun' : ...) * fun-inv' * inv-fun' centred at x's
  (fun, fun-inv, inv-fun): fun0 f = fun' (inv0 (fun0 f)) = fun' f (by
  fun-inv' and ap fun' inv-fun0), laws are props (El sets, `prop4`),
  `Sigma-eq`. Assembled with `InitUALib.sigma` twice and
  `InitUALib.retract`; `rP q0` is `pb0` definitionally. Nothing open in
  Part P.
- 2026-11-26, Part C1: DONE (proved, no postulates; new files only).
  Driver `InitUACheckC1.seg` (shape of InitUACheckLayer; imports
  InitUAIsoLemmas, InitUABlkC1Lib at top level, InitUABlkC1 inside X
  after InitUALayer): 1085 declarations, 0 failed, 0.36 s.
  Planted errors rejected in InitUABlkC1, InitUABlkC1Lib and the driver,
  restored. Files and interface:
  * `InitUABlkC1Lib` (level l): `psig fe A F R c r0 h` (Sigma of a
    dependent function and a pointwise relation is centred at (c, r0)
    if each fibre Sigma is; retract via pi-sigma/sigma-pi + pi), and
    `embSing B E sE j back c` ((b : B) * Id E (j c) (j b) centred at
    (c, refl) for E a set and back : j b = j b' -> b = b').
  * `InitUABlkC1` (segment inside X): `c1-contr : InitUALayer.C1Contr`.
    Use as `InitUABlkC1.c1-contr` inside X.
  Method: C1Blk sb0 is a retract (toK/fromK, refl round trip) of
  K = (nil',law) * (id',law) * (o',law) * (eps',law) * (subT',law) *
  (subt',law); nil' by sing-l; id', o', subT' by nested psig + sing-l;
  eps' (after nil' at the centre) and subt' (after subT') by psig +
  embSing into SubT / Term (sets by isSet-Sigma), back maps from
  InitUAIsoLemmas.fib-any at refl. Nothing open in Part C1.
- 2026-11-26, Part S: DONE (proved, no postulates; new files only).
  Driver `InitUACheckS.seg` (shape of InitUACheckLayer; module C takes
  `(l) (fe : Axioms[l].FunExt) (ua : Axioms[l].Univalence)
  (fe1 : Axioms[l+].FunExt)`): 1058 declarations, 0 failed, 0.34 s.
  `InitUACheckLayer.seg` still 1009 declarations, 0 failed. Planted errors
  rejected in both new files, restored.
  Interface: `InitUABlkS.s-contr : InitUALayer.SContr` (inside X).
  Extra hypothesis: funext at l+ (`fe1`), needed because the sorts
  Sub' Ty' El' are families X -> U l, whose paths live in a type in
  U l+; univalence at l alone does not give this. Part G supplies it as
  `FunExtUA[l+].FE[ua @l+].fe` from `ua : [l] Axioms[l].Univalence`
  (as in InitCheckInitial).
  Files:
  * `InitUABlkSLem` (free l, ua, fe, fe1; import in C): `EB A =
    (B : U l) * (f : A -> B) * BiInv A B f`, `eb-centred` (retract, round
    trip refl, of (B : U l) * Equiv A B, centred by `eqind`), fibrewise
    `EB1/eb1-centred` (one index), `EB2/eb2-centred` (dependent pair of
    indices; Sub uses J = \ D -> Ctx), `isProp-isSet`.
  * `InitUABlkS` (free l, N, fe, ua, fe1, x; import in X after
    InitUALayer): `Lay = (cp : CP) * (sp : SP cp) * (tp : TP cp) * EP cp tp`,
    each part ((sort, map, BiInv), set-ness); `toLay`/`fromLay` with
    `fromLay (toLay u) = u` and `fromLay lay0 = sb0` by refl; parts
    contracted by `InitUALib[l].sigmaH` (base EB*, fibre the set-ness
    proposition), assembled by `InitUALib[l+].sigma`, then `retract`.
  Nothing open in Part S.
- 2026-11-26, Part C2: DONE (proved, no postulates; new files only).
  Driver `InitUACheckC2.seg` (shape of InitUACheckLayer; imports
  `InitUABlkC2Lib` at top, `InitUABlkC2` inside X after InitUALayer):
  1072 declarations, 0 failed, 0.36 s. Planted errors rejected in all
  three new files, restored.
  Interface: `InitUABlkC2.c2-contr : InitUALayer.C2Contr` (inside X; the
  driver also re-exports it as `X.c2-contr`).
  * `InitUABlkC2Lib` (level l): `fib-any` (copy), `fib` (refl case),
    `emb B W sW i f b0 : Centred ((b : B) * Id W (i b0) (i b)) (b0, refl)`
    for W a set and f : i b = i b' -> b = b' (retract of sing-l; round
    trip by isSet W).
  * `InitUABlkC2` (segment of X): block reordered (refl round trip) into
    R = (ext', ce) * (p', lp) * (lift', ll) * (sec', ls) * (q', lq);
    (ext', ce) by pi/sing-l; at ext' = C.ext each law is a product (pi,
    funext) of `emb` instances with W = SubT or TmT (sets by
    isSet-Sigma over x's set-ness), fibre maps fibSub/fibTm; q' after p'.
    Assembled with `sigma` and `retract`.

- 2026-11-26, Part G: DONE (proved, no postulates; new files only).
  `InitUACheck.seg` (final driver): 1516 declarations, 0 failed, 0.50 s.
  `InitUACheckG.seg` (block E + assembly with the five other blocks as
  module parameters): 1230 declarations, 0 failed, 0.39 s. Planted
  errors rejected in all four new .seg files, restored.
  RESULT: `UA[ua,N].C[l].univalent : Category[l+,l].Univalent InitUACat.preS`
  and `UA[ua,N].C[l].category : Category[l+,l].Category` (pre = preS),
  relative only to `ua : [l] Axioms[l].Univalence` (fe, fe1 from FunExtUA).
  Files and interface:
  * `InitUABlkE` (free l, N, fe; in module C): `eqProp1 .. eqProp8`
    (a K-fold dependent Pi of paths in sets is a proposition), and
    `EP[s,h,c1,c2,pp,v].eqs-prop : isProp (Eqs s c1 c2 pp v)` for
    h : Sets s (tails T1..T29 of Eqs with their dependencies as
    parameters; T1 = Eqs by unfolding).
  * `InitUABlkEX` (free l, N, fe, x; in X after InitUALayer):
    `e-prop`, `e-contr : InitUALayer.EContr` (InitUALib.prop at eb0).
  * `InitUAUnivX` (free l, N, fe, hS hC1 hC2 hP hV, x; enclosing module
    has X (x) with InitUALayer, InitUABlkEX): `hL` (L centred at centre:
    sigmaH over SBlk, then sigma x4), `hB` (InitUALib[l+].retract,
    toL/fromL refl), `propB`, `phi` (uses
    `InitUAIso.IsoComp[l,N,fe,toRec x,toRec y].InitUAIsoComp.iso-compeq`,
    converts to CompEqO y.1 f.1 as expected), `same-hom`, and
    `singl-prop : Prelude[l+].isProp (Category[l+,l].Singletons[preS].Singl x)`
    (idJ over (y : TEModelS) * preS.hom x y, then over isIso with
    InitUAIsoProp[l+,l].On[preS].iso-prop).
  * `InitUAUniv` (free l, N, fe, hS..hV; enclosing module has Ux (x)
    importing InitUAUnivX): `singl-prop`, `univalent` (FromTotal),
    `category`.
  * Block hypotheses are functions of x: `hS : (x : TEModelS) ->
    X[x].InitUALayer.SContr` etc. (module G of InitUACheckG); in
    InitUACheck they are definitions `hS x = X[x].InitUABlkS.s-contr`,
    `hC1 .. c1-contr`, `hC2 .. c2-contr`, `hP .. p-contr`, `hV .. v-contr`.
  Notes: `U` is a keyword (module name `Ux`); module C of the final
  driver defines ua, fe, fe1 from `uaA : [l] Axioms[l].Univalence`.
  Nothing open in Part G.
