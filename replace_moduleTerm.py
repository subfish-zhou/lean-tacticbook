#!/usr/bin/env python3
"""Replace backtick identifiers with {moduleTerm}`Name` in Ch01-Ch03 verso files."""

import re
import sys

TARGETS = [
    # Single-word types only — Expr.* constructors are inductive ctors,
    # not resolvable by {moduleTerm}, so we skip them.
    "Expr", "MVarId", "FVarId", "Name", "Level", "Syntax", "LocalDecl",
    "LocalContext", "CoreM", "MetaM", "TermElabM", "TacticM",
    "Bool", "Nat", "String", "Unit", "Option", "IO", "List", "Array",
    "Environment", "BinderInfo", "Literal", "MData",
]

# Sort by length descending so Expr.app matches before Expr
TARGETS.sort(key=len, reverse=True)

# Escape dots for regex
escaped = [re.escape(t) for t in TARGETS]
# Pattern: standalone backtick identifier, not already inside {moduleTerm} or {lit} etc.
# Match `Name` but not part of a larger backtick expression like `Name.foo` (for single words)
# or `Expr.app.something` (for dotted names)
PATTERN = re.compile(
    r'(?<!\{moduleTerm\})'   # not already moduleTerm
    r'(?<!\{lit\})'          # not already lit
    r'`(' + '|'.join(escaped) + r')`'
    r'(?!`)'                 # not part of ```
)


def should_skip_line(line: str) -> bool:
    """Skip lines that are inside code blocks, headings, or already tagged."""
    stripped = line.strip()
    # Skip headings
    if stripped.startswith('#') and not stripped.startswith('#doc'):
        return True
    return False


def process_file(filepath: str) -> int:
    with open(filepath, 'r') as f:
        lines = f.readlines()

    in_code_block = False
    new_lines = []
    total_replacements = 0

    for line in lines:
        stripped = line.strip()

        # Track code blocks (``` with optional language tag)
        if stripped.startswith('```'):
            in_code_block = not in_code_block
            new_lines.append(line)
            continue

        if in_code_block:
            new_lines.append(line)
            continue

        if should_skip_line(line):
            new_lines.append(line)
            continue

        # Do the replacement
        def replacer(m):
            name = m.group(1)
            return '{moduleTerm}`' + name + '`'

        new_line, count = PATTERN.subn(replacer, line)
        total_replacements += count
        new_lines.append(new_line)

    with open(filepath, 'w') as f:
        f.writelines(new_lines)

    return total_replacements


def main():
    base = "/home/azureuser/.openclaw/workspace/lean-auto-book/verso/LeanAutoBook"
    files = [
        f"{base}/Ch01MetaprogrammingModel.lean",
        f"{base}/Ch02Expr.lean",
        f"{base}/Ch03FirstTactic.lean",
    ]

    for filepath in files:
        count = process_file(filepath)
        print(f"{filepath}: {count} replacements")


if __name__ == "__main__":
    main()
