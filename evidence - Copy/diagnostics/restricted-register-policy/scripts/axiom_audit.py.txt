"""Reject nonstandard axioms in printed Lean declaration censuses."""
from __future__ import annotations

import re

STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def audit_log(output: str) -> dict[str, list[str]]:
    if "sorryAx" in output:
        raise ValueError("sorryAx in Lean output")
    results = {}
    for name, raw in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output):
        axioms = [item.strip() for item in raw.split(",") if item.strip()]
        unexpected = set(axioms) - STANDARD
        if unexpected:
            raise ValueError(f"{name} has nonstandard axioms: {sorted(unexpected)}")
        results[name] = axioms
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        results[name] = []
    return results


def require_declarations(output: str, names: set[str]) -> dict[str, list[str]]:
    """An empty or truncated log cannot certify a requested declaration."""
    census = audit_log(output)
    missing = names - census.keys()
    if missing:
        raise ValueError(f"missing axiom census for declarations: {sorted(missing)}")
    return {name: census[name] for name in sorted(names)}
