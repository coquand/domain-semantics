#!/usr/bin/env python3
"""Check the one-universe Russell interpretation against the simplicial model."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
from tempfile import TemporaryDirectory

HERE = Path(__file__).resolve().parent
UNIT = HERE.parent

FOUNDATION = ("Base", "Prelude", "Lib", "Paths", "Axioms", "FunExtUA")
SEMANTICS = ("EhrhardCwF", "EhrhardTEModel", "TEInterp", "RSem")
CORE = (
    "CDDeltaRussell", "CDHornSub", "CDUniverseBase", "CDUniverseLift", "CDUniverseEl",
    "CDUniverseCart", "CDUniverseHorn", "CDDeltaUniverses",
    "CCodeCwF", "CDCodeContext", "CDBoxNat", "CDName", "CDCodeFib",
    "CDFibReindex", "CDStructPi", "CDPiReindex", "CDCodePi",
    "CDCodeUniverse", "CDPiLift", "CDPiParts", "CDPiCode", "CDSmallPi",
    "CDDeltaModel",
)
INTEGRATION = ("EhrhardFromCore", "DeltaTEModel", "DeltaRSemCheck")


def imports(source):
    return re.findall(r"\bimport\s+(\w+)\s*;", re.sub(r"--[^\n]*", "", source))


def sources(directory, roots):
    pending = list(roots)
    result = {}
    while pending:
        name = pending.pop()
        if name in result:
            continue
        path = directory / (name + ".seg")
        pending.extend(imports(path.read_text()))
        result[name] = path
    return result


def import_lines(names, indent=""):
    return "".join(f"{indent}import {name} ;\n" for name in names)


def main():
    manifest = json.loads((UNIT / "vendor-manifest.json").read_text())
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checker", nargs="?", type=Path,
                        default=Path(os.environ.get("UNIT_CHECKER", manifest["checker"]["path"])))
    parser.add_argument("--core", type=Path, default=Path.home() / "CANONICITY/unit/core")
    parser.add_argument("--only", action="append", default=[])
    args = parser.parse_args()

    gat = (UNIT / "GATCheck.seg").read_text()
    syntax = re.search(r"^module BoundedSyntax\b.*?\bimport RGAT\s*;", gat, re.M | re.S)
    if syntax is None:
        parser.error("could not locate the Russell syntax imports through RGAT in GATCheck.seg")
    unit = sources(UNIT, (*FOUNDATION, *imports(syntax[0]), *SEMANTICS))

    entry = (args.core / "All.seg").read_text()
    prefix = re.search(r"^import Base\b.*?^  import CClassical\s*;", entry, re.M | re.S)
    if prefix is None:
        parser.error("could not locate the core imports through CClassical in All.seg")
    core = sources(args.core, (*imports(prefix[0]), *CORE))
    for name in unit.keys() & core.keys():
        if unit[name].read_bytes() != core[name].read_bytes():
            parser.error(f"source collision for {name}.seg: {unit[name]} and {core[name]}")

    core_entry = prefix[0]
    for name in FOUNDATION:
        core_entry = re.sub(rf"^import {name}\s*;\s*\n", "", core_entry, count=1, flags=re.M)

    loader = (
        import_lines(FOUNDATION) + "\n" + syntax[0] + "\n} ;\n\n"
        + import_lines(SEMANTICS) + "\n" + core_entry + "\n"
        + import_lines((*CORE, *INTEGRATION), "  ") + "} ;\n"
    )
    files = unit | core | {
        "EhrhardFromCore": UNIT / "russell-posets" / "EhrhardFromCore.seg",
        **{name: HERE / (name + ".seg") for name in INTEGRATION[1:]},
    }
    checker = args.checker.expanduser().resolve(strict=True)
    with TemporaryDirectory(prefix="russell-delta-check-") as space:
        workspace = Path(space)
        for name, path in files.items():
            (workspace / (name + ".seg")).symlink_to(path.resolve(strict=True))
        (workspace / "All.seg").write_text(loader)
        selection = [arg for name in args.only for arg in ("--only", name)]
        return subprocess.run([checker, "All.seg", *selection], cwd=workspace).returncode


if __name__ == "__main__":
    raise SystemExit(main())
