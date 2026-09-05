"""Require a complete audit and only Lean's three standard foundational axioms."""
from pathlib import Path
import re
import sys

audit_source = Path("Audit.lean").read_text()
expected = set(re.findall(r"^#print axioms (\S+)$", audit_source, re.M))
output = Path(sys.argv[1]).read_text()
found = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output))
found.update({name: "" for name in re.findall(r"'([^']+)' does not depend on any axioms", output)})
if not expected or set(found) != expected:
    raise SystemExit(f"Incomplete axiom audit: expected {sorted(expected)}, got {sorted(found)}")
allowed = {"propext", "Classical.choice", "Quot.sound"}
for name, axioms in found.items():
    extra = {a.strip() for a in axioms.split(",") if a.strip()} - allowed
    if extra:
        raise SystemExit(f"Unexpected axioms in {name}: {sorted(extra)}")

for path in Path("FrontierTheorems").rglob("*.lean"):
    source = path.read_text()
    # Public files open their namespace prefixes before their declarations.
    namespaces = re.findall(r"^namespace (\S+)$", source, re.M)
    prefix = ".".join(namespaces)
    if not namespaces:
        raise SystemExit(f"Missing namespace in {path}")
    names = re.findall(r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|private)\s+)?(?:theorem|lemma|def) (\S+)", source, re.M)
    missing = {f"{prefix}.{name}" for name in names} - expected
    if missing:
        raise SystemExit(f"Unaudited declarations in {path}: {sorted(missing)}")
print(f"PASS: {len(expected)} declarations audited; only standard Lean axioms.")
