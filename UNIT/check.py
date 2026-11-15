#!/usr/bin/env python3
"""Check dependencies, all declarations, and the independent sessions.

Usage: python3 UNIT/check.py [path/to/seg]
UNIT_CHECKER is also accepted; otherwise use the recorded local checker.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys


def main():
    root = Path(__file__).resolve().parent
    manifest = json.loads((root / "vendor-manifest.json").read_text())
    for item in manifest["files"]:
        path = root / item["file"]
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        if digest != item["sha256"]:
            sys.exit(f"Dependency differs from snapshot: {path}")
        if (root / path.name).resolve() != path.resolve():
            sys.exit(f"Import does not point to snapshot: {root / path.name}")
    if len(sys.argv) > 2:
        sys.exit(__doc__)
    checker = Path(sys.argv[1] if len(sys.argv) == 2 else
                   os.environ.get("UNIT_CHECKER", manifest["checker"]["path"]))
    checker = checker.expanduser().resolve()
    if not checker.is_file():
        sys.exit("Unit checker missing. Pass its path or set UNIT_CHECKER.")
    projector_imports = set(re.findall(
        r"\bimport\s+(\w+)\s*;", (root / "IndependentProjectorCheck.seg").read_text()))
    forbidden = projector_imports & {
        "SemanticProjector", "SemanticLaws", "BinarySemantic", "ProjectorLeast",
        "ProjectorFixedPoint", "KleeneProjector", "StageTyping",
        "StageCompatibility", "StageComparison",
        "UniverseProductProjector",
    }
    if forbidden:
        sys.exit(f"Projector independence check imports forbidden modules: {sorted(forbidden)}")
    product_imports = set(re.findall(
        r"\bimport\s+(\w+)\s*;", (root / "IndependentDependentProductCheck.seg").read_text()))
    forbidden = product_imports & {
        "Types", "Typing", "Filter", "Domain", "ExtFilter", "Finitary",
        "SemanticProjector", "SemanticLaws", "BinaryMaps", "ProjectorOperator",
        "SectionProjector", "DependentProductProjector",
    }
    if forbidden:
        sys.exit(f"General dependent-product check imports forbidden modules: {sorted(forbidden)}")
    cusl_imports = set(re.findall(
        r"\bimport\s+(\w+)\s*;", (root / "CUSLFpCheck.seg").read_text()))
    forbidden = cusl_imports & {
        "Types", "Typing", "Filter", "Domain", "ExtFilter", "Finitary",
        "CompactFamilies", "Projector", "ProjectorDomain", "SemanticProjector",
        "FinitaryInterior", "FinitaryInteriorContinuity", "All",
    }
    if forbidden:
        sys.exit(f"CUSL Fp check imports forbidden modules: {sorted(forbidden)}")
    structural_imports = set(re.findall(
        r"\bimport\s+(\w+)\s*;", (root / "StructuralTypedLawsCheck.seg").read_text()))
    forbidden = structural_imports & {
        "SemanticProjector", "SemanticLaws", "BinarySemantic", "ProjectorLeast",
        "ProjectorFixedPoint", "ProjectorEquations", "KleeneProjector",
        "UniverseProductProjector", "StageTyping", "StageCompatibility",
        "StageComparison", "IndependentRelationRawLaws", "All",
    }
    if forbidden:
        sys.exit(f"Structural typed-law check imports forbidden modules: {sorted(forbidden)}")
    witness_imports = set(re.findall(
        r"\bimport\s+(\w+)\s*;", (root / "WitnessSearchCheck.seg").read_text()))
    allowed_witness_imports = {
        "Base", "Prelude", "Lib", "Axioms", "FunExtUA", "Replacement",
        "Truncation", "TruncationCombinators", "BoundedWitnessSearch",
    }
    if witness_imports - allowed_witness_imports:
        sys.exit(f"Witness search check imports unrelated modules: {sorted(witness_imports - allowed_witness_imports)}")
    derivation_imports = set(re.findall(
        r"\bimport\s+(\w+)\s*;", (root / "DerivationSearchCheck.seg").read_text()))
    allowed_derivation_imports = allowed_witness_imports | {
        "Syntax", "SyntaxDecision", "DerivationSorts", "ConstructorEnumeration",
        "DerivationSignature", "DerivationEnumeration", "ConstructorWitnessSearch",
        "DerivationRecovery", "DerivationEnumerationChecks",
    }
    if derivation_imports - allowed_derivation_imports:
        sys.exit(f"Derivation recovery imports unrelated proof modules: {sorted(derivation_imports - allowed_derivation_imports)}")
    relation_imports = set(re.findall(
        r"\bimport\s+(\w+)\s*;", (root / "IndependentLogicalRelationCheck.seg").read_text()))
    forbidden = relation_imports & {
        "RelC", "LawsC", "AdeqBase", "AdeqPi", "AdeqLam", "AdeqApp",
        "AdeqFun", "Adequacy", "Consequences", "SubjRed",
    }
    if forbidden:
        sys.exit(f"New inversion/subject-reduction check imports old proofs: {sorted(forbidden)}")
    # Typing.seg also contains order-equivalence helpers used by the basis
    # library. The new projector/typed-law proofs must not use its typing
    # family, constructors or elimination lemmas, even though it is in scope.
    for source in (
        "NormalizedCompactCover.seg", "StructuralProjectorLaws.seg",
        "ProjectorPredicateCases.seg", "ProjectorFunctionSupport.seg",
        "IndependentRelationClauseLaws.seg", "IndependentRelationTypedSteps.seg",
        "IndependentRelationTypedTerms.seg", "IndependentRelationTypedStages.seg",
        "IndependentRelationTypedLaws.seg",
    ):
        code = re.sub(r"--[^\n]*", "", (root / source).read_text())
        if re.search(r"\b(?:Typing|Tp|t-bot|t-univ|t-pi|t-lam|en-om|en-arr|en-meet|tp-[\w-]+)\b", code):
            sys.exit(f"Structural proof refers to inductive compact typing: {source}")
    recorded = hashlib.sha256(checker.read_bytes()).hexdigest() == manifest["checker"]["sha256"]
    print(f"Dependencies: {len(manifest['files'])} hashes verified", flush=True)
    print(f"Checker: {checker} ({'recorded build' if recorded else 'different build'})", flush=True)
    for source in ("All.seg", "CUSLFpCheck.seg", "IndependentDependentProductCheck.seg",
                   "IndependentProjectorCheck.seg", "StructuralTypedLawsCheck.seg",
                   "IndependentLogicalRelationCheck.seg", "WitnessSearchCheck.seg",
                   "DerivationSearchCheck.seg"):
        try:
            result = subprocess.run([str(checker), source], cwd=root,
                                    text=True, capture_output=True, timeout=60)
        except subprocess.TimeoutExpired:
            sys.exit(f"Unit check of {source} timed out after 60 seconds.")
        print(result.stdout, end="")
        print(result.stderr, end="", file=sys.stderr)
        if result.returncode:
            sys.exit(result.returncode)
        if not re.search(re.escape(source) + r": \d+ declarations, 0 failed,", result.stdout):
            sys.exit(f"Checker did not report a complete successful check of {source}.")


if __name__ == "__main__":
    main()
