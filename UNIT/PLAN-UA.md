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
- OPEN: enumeration N ->> FinDil.  Code[F] is NOT enumerable as it
  stands (ord : (d : Fin) -> ... ranges over all finite levels); need
  codes determined by a finite level (ord at the joint types of pairs of
  generators, cf. StabHom.OrdN / jt), then Code ~ a decidable subset of N.
## What should simplify
- StabJt layer 7d (canonical entries CN, DetA, DetB, jt-uniq via funext on
  tables and J on code paths): "unique up to iso" becomes equality, the
  multicoproduct condition becomes contractibility of factorisations.
- LabTree3/Girard3: the parameter "sequence of codes" can be replaced by
  the canonical enumeration of FinDil (the classical completeness theorem
  needs all finite dilators up to iso).
- Type-3 size workarounds (Gens P, small data for existentials): images
  by replacement.
