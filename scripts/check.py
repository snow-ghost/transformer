#!/usr/bin/env python3
"""Check source completeness and the kernel-reported axioms of every named theorem."""
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def code_only(source):
    result = []
    i = depth = 0
    quoted = False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                result.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif quoted:
            if source[i] == "\\":
                i += 2
            elif source[i] == '"':
                quoted = False
                i += 1
            else:
                result.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif source.startswith("/-", i):
            depth = 1
            i += 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        elif source[i] == '"':
            quoted = True
            i += 1
        else:
            result.append(source[i])
            i += 1
    return "".join(result)


def declarations(source):
    scopes = []
    for line in code_only(source).splitlines():
        line = line.strip()
        namespace = re.match(r"namespace (\S+)", line)
        if namespace:
            scopes.append(("namespace", namespace[1]))
        elif re.match(r"(?:noncomputable )?section(?:\s|$)", line):
            scopes.append(("section", ""))
        elif re.match(r"end(?:\s|$)", line):
            if not scopes:
                raise ValueError("Unbalanced Lean scope")
            scopes.pop()
        else:
            theorem = re.match(r"(?:@\[[^]]*\]\s*)?(?:theorem|lemma)\s+([\w.']+)", line)
            if theorem:
                yield ".".join([name for kind, name in scopes if kind == "namespace"] + [theorem[1]])


def main():
    files = sorted((ROOT / "VerifiedClassifier").glob("*.lean"))
    names = []
    for path in files + sorted(ROOT.glob("*.lean")):
        source = path.read_text()
        banned = re.search(r"\b(?:sorry|admit|axiom|unsafe|native_decide|trace_state)\b", code_only(source))
        if banned:
            raise SystemExit(f"Forbidden proof escape in {path.name}: {banned[0]}")
        if path.parent.name == "VerifiedClassifier":
            names.extend(declarations(source))
    checks = "import VerifiedClassifier\n\n" + "".join(f"#print axioms {name}\n" for name in names)
    if (ROOT / "Checks.lean").read_text() != checks:
        raise SystemExit("Checks.lean is stale: add an axiom check for every named theorem in module order.")
    run = subprocess.run(["lake", "env", "lean", "Checks.lean"], cwd=ROOT, text=True, capture_output=True)
    if run.returncode:
        raise SystemExit(run.stdout + run.stderr)
    rows = re.findall(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", run.stdout, re.S)
    if len(rows) != len(names) or {row[0] for row in rows} != set(names):
        raise SystemExit("Incomplete axiom audit:\n" + run.stdout)
    used = {a.strip() for _, _, axioms in rows for a in axioms.split(",") if a.strip()}
    if not used <= ALLOWED_AXIOMS:
        raise SystemExit(f"Unexpected axioms: {used - ALLOWED_AXIOMS}")
    if "warning:" in run.stdout or "error:" in run.stdout:
        raise SystemExit(run.stdout)
    print(f"Checked {len(names)} named theorems; axioms: {', '.join(sorted(used))}")


if __name__ == "__main__":
    main()
