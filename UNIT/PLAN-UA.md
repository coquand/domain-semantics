# Categories of embeddings with univalence and replacement (2026-11-19)

User: "do a parallel development with univalence and see what can be
simplified"; work in seg with the theory parameters of All.seg (ua, images,
surjections = univalence and Rijke's replacement), as for Scott domains
(ScottSmallness, ScottDomainObjects, CategorySIP) and the algebra examples
of ~/CANONICITY/unit/sag (freegroup: size results with replacement).

Key point: RIGIDITY of finite objects (StabRigid, iterated by StabCEF).
With univalence, rigid finite objects form a SET, and the "small basis" of
finite objects is obtained effectively (no chosen codes), as the compact
basis of a Scott domain (ScottSmallness: mere smallness untruncated).

## Level 0 (DONE)
LOUnivalent.seg: univalence for decidable linear orders (LOSingleton by
UA.eqind on the carrier; LOUnivalence.univalent : Id LO P Q ~ LOIso P Q).
FinLOSmall.seg: rigid (via StabRigid.Fix), isoProp (an iso onto [m] is
unique), isoN ([n] ~ [m] => n = m, via LOFin.psi and ones <= len),
snProp, FinLO = (A : LO) * ||(n : N) * LOIso A [n]||, untr, and
small : Replacement.Small FinLO  (FinLO ~ N).

## Level 1: finite dilators
- DONE (2026-11-19) SFUnivalent.seg: univalence of Stab(C) for EVERY C
  (so at every level: dilators, 2-ptykes, ...): Id SF[C] X Y ~ NI X Y
  (natural isos at all objects).  Family induction (Pi of LOSingleton
  totals), base fibre: naturality forces arr' = arr, the rest are props.
- DONE SFLocSmall.seg: NI X Y ~ FinNI X Y (natural isos on FINITE objects,
  a small type): restrict / extend (Over.Ext of the family and of its
  inverse; det shows the extensions are inverse); hence
  locally-small C : Replacement.LocallySmall SF[C].
- DONE (2026-11-19) FinDil.seg, module FD[F] for every CEF F:
  FinDil : U l = replacement image of Decode : Code[F] -> SF[F.C]
  (codomain locally small by SFLocSmall); elim = surjectivity of q.
  Uniq: rigidity => FinNI (D K) Y is a prop => Id SF (D K) Y is a prop;
  hence set : isSet FinDil.  Iso: rigidity => ANY pair of maps
  D K -> D K', D K' -> D K is an iso, so iso = two finite hom searches
  (StabHom + EnumDec); decEq : decidable equality on FinDil.
  FinDil0 = finite dilators up to iso (F = FinOrd).
- DONE (2026-11-19) enumeration, in three files:
  StabTab.seg: a finite TABLE tau i hi i' hi' t ht (generators i, i',
  listed joint type t of gen i, gen i') gives comparisons at every level,
  read at the LEAST listed joint type through which the pair factors
  (searchL + LstUniq; invariance by jt-uniq, no duplicate-consistency
  condition needed, unlike StabSum.SV1).  Validity = finitely many
  checks (refl at generators; flip/eq at pair joint types; transitivity
  at ternary joint types, StabJt0.Tern), decidable; a valid table is a
  code (TabV.Laws.code).
  StabTabCov.seg: TabCov (a table agreeing with a code is valid; the
  codes are iso by identity maps), TblOf (a code's own table), GenIso
  (codes transported along generator isos; rigidity of finite objects).
  StabEnum.seg: EnumIso F (lists of finite objects covering up to iso)
  -> EnumIso Stab(F) (enumStab); enumFO, enumDil, enumPty, enumPty3;
  FinDilEnum.hit: every element of FinDil occurs (merely) in the lists.
- DONE (2026-11-19) MonoEnum.seg (Girard3 without the code parameter):
  MonoFin (monotonicity at the joint types of each generator with
  itself; decidable), MSound: MonoFin => FinDilWF.Mono; MonoTr: the iso
  copy produced by the enumeration of a monotone code is MonoFin; enumLO
  and the lists LM b of MonoFin codes over LOCEF; Flat: stratified lists
  -> sequence (padding); code : N -> Code, monoN, complete (every
  monotone code is iso to some code n); Girard3E = FinDilWF.Girard3M
  over this sequence.  Remaining classical input for the Pi^1_4 theorem:
  every finite dilator is monotone (Girard), joint-type completeness, e3.
- DONE (2026-11-19) FinDilCanon.seg: canonical representatives WITHOUT
  canonical forms: least index of the enumeration in the class (a prop,
  by decEq), rep : FinDil -> Code, FinDil ~ decidable subset of N
  (finDilSub for dilators).
- DONE CospanUniq.seg (any catemb C): jointly surjective (JS) cospans:
  Epi (maps out of Z determined by the legs) and Med (a map between two
  factorisations of (f,g), compatible with legs and m, m'); Uniq: for
  decoded codes, JS factoring cospans give the same element of FinDil.
## Measurement: StabJt layer 7d (2026-11-19)
  Strict jt-uniq (equality of JT entries = equality of CODES) costs:
  CN 76 + CovCan 30 + DetA 148 + DetB 123 + CanP 64 + Epi7 32 = ~470
  lines (canonical-form filter, word/table/map determinacy).
  Univalent replacement:
  * canonical choice: FinDilCanon (~100 lines, generic, reusable);
  * uniqueness up to iso + epi: CospanUniq (~130 lines, generic in C);
  * still needed: JS for the listed sum entries (decidable via
    generators; ~100 lines est., the content of DetA.uA/vB).
  So uniqueness-up-to-iso costs ~250 lines instead of ~470, and is
  conceptual (no word/table equality).  BUT the CEF interface demands
  STRICT jt-uniq: to profit, either (a) change CatEmbFin.CEF.jt-uniq to
  'unique up to iso of cospans' (users: StabTab.FJPost, StabSum.LI,
  StabJt itself; FinOrd/LOCEF trivially), or (b) a univalent CEF with
  Fin = FinDil classes (rep), where iso => equality; (b) needs all
  StabCEF fields transported along rep (est. 300+ lines) -- no net
  saving in size, only in concepts.
- DONE (2026-11-19) parallel route (a) WITHOUT changing the interface:
  Dedup.seg (generic, any catemb with Bishop-finite homs): a listing
  that covers, is jointly epi and unique UP TO ISO becomes strictly
  unique by dropping entries with an earlier iso copy (iso decidable).
  StabCEF2.seg: Stab(F) : CF.CEF again, uniqueness from CospanUniq.Med
  (JS of canonical entries from DetA.uA/vB + view) and epi from
  CospanUniq.Epi; dilCEF2, ptyCEF2, pty3CEF2.
  Line count: Stab-specific 107 (StabCEF2) + generic 202 (Dedup) + 126
  (CospanUniq) = 435, replacing ~290 lines of StabJt (DetA after vB,
  DetB, CanP, Epi7).  Net: Stab-specific part 107 vs 290; the rest is
  generic (reusable for any category), so no total size win.
## What should simplify
- StabJt layer 7d (canonical entries CN, DetA, DetB, jt-uniq via funext on
  tables and J on code paths): "unique up to iso" becomes equality, the
  multicoproduct condition becomes contractibility of factorisations.
- LabTree3/Girard3: the parameter "sequence of codes" can be replaced by
  the canonical enumeration of FinDil (the classical completeness theorem
  needs all finite dilators up to iso).
- Type-3 size workarounds (Gens P, small data for existentials): images
  by replacement.
