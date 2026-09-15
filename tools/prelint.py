#!/usr/bin/env python3
"""Cheap repository checks that run before Lean compilation.

This intentionally does not pretend to be a Lean parser.  It catches the failure
modes that previously broke Rasq packaging: missing local imports, modules omitted
from the umbrella target/lake globs, and proof placeholders.
"""
from __future__ import annotations

import re
import sys
import tomllib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "StochasticQuantization"
UMBRELLA = ROOT / "StochasticQuantization.lean"
LAKE = ROOT / "lakefile.toml"

module_files = sorted(SRC.rglob("*.lean"))
modules = {
    "StochasticQuantization." + ".".join(p.relative_to(SRC).with_suffix("").parts): p
    for p in module_files
}

errors: list[str] = []

import_re = re.compile(r"^import\s+([A-Za-z0-9_.]+)\s*$", re.M)
placeholder_re = re.compile(r"\b(sorry|admit|axiom)\b")

for module, path in modules.items():
    text = path.read_text()
    for imp in import_re.findall(text):
        if imp.startswith("StochasticQuantization.") and imp not in modules:
            errors.append(f"{path}: missing local import {imp}")
    # Strip block and line comments before the coarse placeholder scan.
    stripped = re.sub(r"/-.*?-\s*/", "", text, flags=re.S)
    stripped = re.sub(r"--.*", "", stripped)
    m = placeholder_re.search(stripped)
    if m:
        errors.append(f"{path}: proof placeholder/token {m.group(1)!r}")

umbrella_text = UMBRELLA.read_text()
umbrella_imports = set(import_re.findall(umbrella_text))

# Require every local module to be reachable from the umbrella import graph, not
# necessarily imported directly.  This permits intentional aggregators such as
# `StochasticQuantization.Theory`.
graph: dict[str, set[str]] = {}
for module, path in modules.items():
    graph[module] = {
        imp for imp in import_re.findall(path.read_text())
        if imp.startswith("StochasticQuantization.")
    }
reachable = set()
stack = [imp for imp in umbrella_imports if imp.startswith("StochasticQuantization.")]
while stack:
    module = stack.pop()
    if module in reachable:
        continue
    reachable.add(module)
    stack.extend(graph.get(module, ()))
for module in modules:
    if module not in reachable:
        errors.append(f"module not reachable from umbrella imports: {module}")

lake_text = LAKE.read_text()
try:
    lake_cfg = tomllib.loads(lake_text)
except tomllib.TOMLDecodeError as exc:
    errors.append(f"lakefile.toml is not valid TOML: {exc}")
    lake_cfg = {}

# Detect local import cycles. Lean can diagnose these too, but catching them here
# gives a much cheaper failure before dependency compilation.
WHITE, GRAY, BLACK = 0, 1, 2
color = {m: WHITE for m in modules}
stack_path: list[str] = []
def visit(m: str) -> None:
    color[m] = GRAY
    stack_path.append(m)
    for n in graph.get(m, ()):
        if n not in modules:
            continue
        if color[n] == WHITE:
            visit(n)
        elif color[n] == GRAY:
            j = stack_path.index(n)
            errors.append("local import cycle: " + " -> ".join(stack_path[j:] + [n]))
    stack_path.pop()
    color[m] = BLACK

for module in modules:
    if color[module] == WHITE:
        visit(module)

for module in modules:
    if f'"{module}"' not in lake_text:
        errors.append(f"lakefile missing glob {module}")

# Lake globs should not contain accidental duplicate module entries.
glob_entries: list[str] = []
for target in lake_cfg.get("lean_lib", []):
    glob_entries.extend(target.get("globs", []))
seen: set[str] = set()
for entry in glob_entries:
    if entry in seen:
        errors.append(f"duplicate lake glob: {entry}")
    seen.add(entry)

# Every umbrella local import should resolve too.
for imp in umbrella_imports:
    if imp.startswith("StochasticQuantization.") and imp not in modules:
        errors.append(f"umbrella imports nonexistent module {imp}")

if errors:
    print("PRELINT: FAIL")
    for err in errors:
        print(" -", err)
    sys.exit(1)

print(f"PRELINT: PASS ({len(modules)} Lean modules; imports acyclic; TOML/globs resolved; no placeholders)")
