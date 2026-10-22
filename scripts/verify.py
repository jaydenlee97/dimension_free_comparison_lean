#!/usr/bin/env python3
"""Build the complete paper root and audit all loaded project declarations."""
from pathlib import Path
import hashlib
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from lean_source import strip_comments

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'verification' / 'latest'
OUT.mkdir(parents=True, exist_ok=True)
os.chdir(ROOT)
launcher = shlex.split(os.environ.get('LEAN_LAUNCHER', ''))

def run(args, log):
    with (OUT / log).open('w') as f:
        p = subprocess.run(launcher + args, stdout=f, stderr=subprocess.STDOUT)
    if p.returncode:
        print((OUT / log).read_text())
        raise SystemExit(f'FAILED: {args}, exit {p.returncode}')
    return (OUT / log).read_text()

sources = sorted([ROOT / 'GaussianMixturePaper.lean', ROOT / 'Audit.lean'] +
                 list((ROOT / 'GaussianComparison').glob('*.lean')) +
                 list((ROOT / 'GaussianMixturePaper').glob('*.lean')))
before = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
module_sources = {
    str(p.relative_to(ROOT).with_suffix('')).replace(os.sep, '.'): p
    for p in sources if p.name != 'Audit.lean'
}
module_imports = {
    name: re.findall(r'^import\s+([\w.]+)\s*$', strip_comments(p.read_text()), re.M)
    for name, p in module_sources.items()
}
reachable = set()
pending = ['GaussianMixturePaper']
while pending:
    name = pending.pop()
    if name in reachable or name not in module_sources:
        continue
    reachable.add(name)
    pending.extend(module_imports[name])
omitted = module_sources.keys() - reachable
if omitted:
    raise SystemExit(f'Project source modules missing from public root: {sorted(omitted)}')
for p in sources:
    text = strip_comments(p.read_text())
    for forbidden in (r'\bsorry\b', r'\badmit\b', r'\baxiom\b', r'\bnative_decide\b',
                      r'\bunsafe\b', r'\bimplemented_by\b'):
        if re.search(forbidden, text):
            raise SystemExit(f'Forbidden proof mechanism {forbidden} in {p}')

if '--fresh' in sys.argv:
    # Remove only this package's generated build outputs, never dependency sources.
    shutil.rmtree(ROOT / '.lake' / 'build', ignore_errors=True)
version = run(['lean', '--version'], 'lean-version.txt').strip()
build = run(['lake', 'build'], 'build.log')
audit = run(['lake', 'env', 'lean', 'Audit.lean'], 'axioms-and-statements.log')
totals = re.findall(r'AUDIT_TOTAL\|(\d+)\|(\d+)', audit)
if len(totals) != 1:
    raise SystemExit('Missing or repeated audit completion marker')
records = re.findall(r'^AUDIT\|([^|\n]+)\|([^\n]*)$', audit, re.M)
if not records:
    raise SystemExit('No audited theorems')
if len(records) != int(totals[0][1]):
    raise SystemExit('Theorem audit output is incomplete')
allow = {'propext', 'Classical.choice', 'Quot.sound'}
found = {}
for name, axs in records:
    axioms = [a.strip() for a in axs.split(',') if a.strip()]
    if set(axioms) - allow:
        raise SystemExit(f'Unapproved axioms: {name}: {axioms}')
    found[name] = axioms
required = json.loads((ROOT / 'verification' / 'required-theorems.json').read_text())
missing = set(required) - found.keys()
if missing:
    raise SystemExit(f'Required endpoints not audited: {sorted(missing)}')
after = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
if before != after:
    raise SystemExit('Sources changed during verification')
(OUT / 'source-sha256.json').write_text(json.dumps(after, indent=2) + '\n')
(OUT / 'theorem-axioms.json').write_text(json.dumps(dict(sorted(found.items())), indent=2) + '\n')
status = {
    'verified_at_utc': datetime.now(timezone.utc).isoformat(),
    'lean': version,
    'build_exit': 0, 'axiom_audit_exit': 0,
    'fresh_project_build': '--fresh' in sys.argv,
    'source_modules_in_public_root': sorted(reachable),
    'declarations_audited': int(totals[0][0]),
    'theorem_declarations_audited': int(totals[0][1]),
    'required_endpoints': required,
    'allowed_axioms': sorted(allow),
    'whole_paper_complete': False,
    'scope': 'See docs/coverage.md; a successful build is not a claim of full manuscript coverage.',
}
(OUT / 'status.json').write_text(json.dumps(status, indent=2) + '\n')
print(json.dumps(status, indent=2))
