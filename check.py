#!/usr/bin/env python3
"""Mechanical build and recursive dependency audit; no semantic verdict."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
IDENT = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom)\b")


def check_runtime_version(toolchain, output):
    expected = re.fullmatch(r"leanprover/lean4:v([^\s]+)", toolchain.strip())
    actual = re.search(r"\bversion ([^,\s)]+)", output)
    if not expected or not actual or expected[1] != actual[1]:
        raise ValueError('runtime version does not match lean-toolchain')


def targets(content):
    start = "<!-- lean-targets:start -->"
    end = "<!-- lean-targets:end -->"
    if content.count(start) != 1 or content.count(end) != 1:
        raise ValueError("TARGETS target markers missing or duplicated")
    rows = []
    for line in content.split(start)[1].split(end)[0].splitlines():
        line = line.strip()
        if not line:
            continue
        if not (line.startswith('|') and line.endswith('|')):
            raise ValueError("invalid TARGETS target table line: " + line)
        cells = [c.strip().strip('`') for c in line.strip('|').split('|')]
        if cells in (['Module', 'Declaration', 'Kind'], ['\u6a21\u5757', '\u58f0\u660e', '\u7c7b\u578b']) or (
                len(cells) == 3 and all(re.fullmatch(r':?-{3,}:?', c) for c in cells)):
            continue
        if len(cells) != 3 or cells[2] not in {"environment", "paper"}:
            raise ValueError("invalid TARGETS target row: " + line)
        module, declaration, kind = cells
        if not IDENT.fullmatch(module) or not IDENT.fullmatch(declaration):
            raise ValueError("invalid Lean identifier in target row")
        if (module, declaration, kind) in rows:
            raise ValueError("duplicate target")
        rows.append((module, declaration, kind))
    if not rows:
        raise ValueError("target table empty; retain the environment control")
    return rows


def parse_axioms(output, declarations):
    found = {}
    for name, raw in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]", output):
        found[name] = {x.strip() for x in raw.split(',') if x.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        found[name] = set()
    if set(found) != set(declarations):
        raise ValueError("missing/unexpected recursive axiom output")
    for name, axioms in found.items():
        if axioms - ALLOWED:
            raise ValueError(f"disallowed dependencies for {name}: {sorted(axioms - ALLOWED)}")
    return found


def main():
    report = ["# Lean mechanical check", "", "Semantic correspondence is a separate review.", ""]
    success = False
    env = dict(os.environ, LEAN_NUM_THREADS='1')
    report.append('Resource controls: Lake scheduler threads=1; local Lean builds and audit use -j1.\n')

    def run(args, timeout=300):
        result = subprocess.run(args, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=timeout, env=env)
        report.extend(["$ " + ' '.join(args), "```text", result.stdout.rstrip(), "```", ""])
        if result.returncode:
            raise RuntimeError(f"command exited {result.returncode}: {' '.join(args)}")
        return result.stdout

    try:
        sources = sorted(p for p in ROOT.rglob('*.lean') if '.lake' not in p.relative_to(ROOT).parts)
        inputs = sources + [ROOT / n for n in ('lean-toolchain', 'lakefile.toml',
                  'lake-manifest.json', 'TARGETS.md', 'check.py', 'check.sh')]
        before = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
        rows = targets((ROOT/'TARGETS.md').read_text())
        report.append(f"Registered paper declarations: {sum(k == 'paper' for _, _, k in rows)}. "
                      "Environment controls are not paper results.\n")
        for p in sources:
            for lineno, line in enumerate(p.read_text().splitlines(), 1):
                if FORBIDDEN.search(line):
                    raise ValueError(f"forbidden token: {p.relative_to(ROOT)}:{lineno}")
        report.append("Local Lean source token scan: PASS (including comments).\n")
        run(['lake', '--version'], 20)
        manifest = json.loads((ROOT/'lake-manifest.json').read_text())
        for package in manifest['packages']:
            if package['type'] != 'git':
                raise ValueError('unlocked/non-git dependency: ' + package['name'])
            path = ROOT/manifest['packagesDir']/package['name']
            revision = run(['git', '-C', str(path), 'rev-parse', 'HEAD'], 20).strip()
            if revision != package['rev']:
                raise ValueError('dependency revision mismatch: ' + package['name'])
            dirty = run(['git', '-C', str(path), 'status', '--porcelain', '--untracked-files=no'], 20)
            if dirty.strip():
                raise ValueError('modified tracked dependency files: ' + package['name'])
        check_runtime_version((ROOT/'lean-toolchain').read_text(),
                              run(['lake', 'env', 'lean', '--version'], 20))
        run(['lake', 'build'])
        imports = '\n'.join('import ' + m for m in sorted({m for m, _, _ in rows})) + '\n'
        (ROOT/'.lake').mkdir(exist_ok=True)
        outputs = []
        # Keep the same full target set; each serial batch retains the 300s limit.
        with tempfile.TemporaryDirectory(prefix='audit-', dir=ROOT/'.lake') as tmp:
            for start in range(0, len(rows), 100):
                batch = rows[start:start + 100]
                audit = imports + ''.join(
                    f'#check @{declaration}\n#print axioms {declaration}\n'
                    for _, declaration, _ in batch)
                path = Path(tmp)/f'Audit{start // 100 + 1}.lean'
                path.write_text(audit)
                output = run(['lake', 'env', 'lean', '-j1', str(path)])
                parse_axioms(output, [d for _, d, _ in batch])
                outputs.append(output)
        parse_axioms('\n'.join(outputs), [d for _, d, _ in rows])
        after = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
        if before != after:
            raise ValueError('inputs changed during check; evidence is stale')
        report.extend(['## Bound inputs (SHA-256)', '', '```text',
                       *[f'{v}  {k}' for k, v in before.items()], '```', ''])
        success = True
    except (OSError, ValueError, RuntimeError, subprocess.TimeoutExpired) as error:
        report.extend(['Failure: ' + str(error), ''])
    report.insert(2, 'Mechanical result: **PASS**.' if success else 'Mechanical result: **FAIL**.')
    (ROOT/'CHECK_REPORT.md').write_text('\n'.join(report).rstrip() + '\n')
    print(report[2])
    print('Report: ' + str(ROOT/'CHECK_REPORT.md'))
    return 0 if success else 1


if __name__ == '__main__':
    sys.exit(main())
