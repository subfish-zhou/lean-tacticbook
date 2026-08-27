#!/usr/bin/env python3
"""Repair same-page fragment links under Verso's document-wide <base> URL.

Verso may emit ``href="#section"`` inside ``ChXX/index.html`` while the page
also declares ``<base href="./../">``. Browsers then resolve the fragment
against the site root instead of the current chapter. This postprocessor
rewrites only fragments that name an ID present in the same HTML file.
"""

from __future__ import annotations

import argparse
from html.parser import HTMLParser
from pathlib import Path
import re


class IdCollector(HTMLParser):
    def __init__(self) -> None:
        super().__init__()
        self.ids: set[str] = set()

    def handle_starttag(self, tag: str, attrs: list[tuple[str, str | None]]) -> None:
        del tag
        values = dict(attrs)
        for key in ("id", "name"):
            if values.get(key):
                self.ids.add(values[key] or "")


HREF_FRAGMENT = re.compile(r'''href=(?P<q>["'])#(?P<frag>[^"']+)(?P=q)''')


def rewrite_page(path: Path, site_root: Path) -> int:
    text = path.read_text(encoding="utf-8")
    parser = IdCollector()
    parser.feed(text)
    rel_dir = path.parent.relative_to(site_root).as_posix()
    if rel_dir == ".":
        return 0

    count = 0

    def replace(match: re.Match[str]) -> str:
        nonlocal count
        fragment = match.group("frag")
        if fragment not in parser.ids:
            return match.group(0)
        count += 1
        quote = match.group("q")
        return f"href={quote}{rel_dir}/#{fragment}{quote}"

    updated = HREF_FRAGMENT.sub(replace, text)
    if updated != text:
        path.write_text(updated, encoding="utf-8")
    return count


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("html_root", type=Path)
    args = ap.parse_args()
    root = args.html_root.resolve()
    if not (root / "index.html").is_file():
        raise SystemExit(f"missing site index: {root / 'index.html'}")
    changed = sum(rewrite_page(path, root) for path in sorted(root.rglob("*.html")))
    print(f"fixed_same_page_fragments={changed}")


if __name__ == "__main__":
    main()
