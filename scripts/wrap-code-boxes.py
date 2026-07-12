#!/usr/bin/env python3
"""Post-process verso HTML output to wrap code blocks in labelled boxes.

Verso emits markdown `\[可运行\]` etc. as `<p>...[可运行]</p>` paragraphs
right before the corresponding code block. This script:

  1. finds each `<p>` whose stripped text ends in one of the known markers
  2. removes that `<p>`
  3. wraps the immediately following `<pre>...</pre>` or bare
     `<code class="hl lean block">...</code>` in
     `<div class="codebox codebox-<slug>"><header>...</header>...</div>`

Idempotent — running twice is safe (already-wrapped blocks have no matching
`<p>` before them).
"""
from __future__ import annotations
import re, sys, pathlib

# marker text -> (css slug, header label)
MARKERS: list[tuple[str, str, str]] = [
    ("可运行",       "runnable",   "可运行"),
    ("示意",         "hint",       "示意"),
    ("源码节选",     "excerpt",    "源码节选"),
    ("伪代码",       "pseudo",     "伪代码"),
    ("练习·故意错误", "bug",        "练习 · 故意错误"),
    ("练习模板",     "template",   "练习模板"),
]

# regex chunk that matches `<p …>…[MARKER]</p>` — the marker can be at end of
# any-inner-content <p>, but we insist it's the last significant text.
def marker_p_pattern(marker: str) -> re.Pattern[str]:
    esc = re.escape(marker)
    # <p …>whitespace [marker] whitespace</p>
    # allow leading text before [marker] within the paragraph, but require
    # the marker to appear literally (with square brackets)
    return re.compile(
        r'<p\b[^>]*>\s*(?:[^<]*?)\[' + esc + r'\]\s*</p>\s*',
        flags=re.S,
    )

# code block variants we want to wrap. Each returns the full block string.
# We match:
#   <pre …>…</pre>
#   <code class="hl lean block" …>…</code>
CODE_BLOCK_RE = re.compile(
    r'(?P<block>'
    r'<pre\b[^>]*>.*?</pre>'
    r'|<code\s+class="[^"]*\bhl\b[^"]*\blean\b[^"]*\bblock\b[^"]*"[^>]*>.*?</code>'
    r')',
    flags=re.S,
)

def wrap_html(html: str) -> tuple[str, int]:
    total = 0
    for marker, slug, label in MARKERS:
        pat = marker_p_pattern(marker)
        def repl(m: re.Match[str]) -> str:
            nonlocal total
            after = html[m.end():]
            block_m = CODE_BLOCK_RE.match(after)
            if not block_m:
                # No adjacent code block — leave the paragraph in place.
                return m.group()
            block = block_m.group('block')
            total += 1
            wrapped = (
                f'<div class="codebox codebox-{slug}">'
                f'<header class="codebox-header">{label}</header>'
                f'{block}'
                f'</div>'
            )
            # We consumed both the <p>…</p> AND the following code block.
            # Return replacement here; append rest of `after` after block.
            return wrapped + after[block_m.end():]

        # We can't use a single re.sub because `repl` consumed extra chars
        # beyond the match. Do it manually.
        out = []
        pos = 0
        while pos < len(html):
            m = pat.search(html, pos)
            if not m:
                out.append(html[pos:])
                break
            out.append(html[pos:m.start()])
            after = html[m.end():]
            block_m = CODE_BLOCK_RE.match(after)
            if not block_m:
                out.append(m.group())
                pos = m.end()
                continue
            block = block_m.group('block')
            total += 1
            out.append(
                f'<div class="codebox codebox-{slug}">'
                f'<header class="codebox-header">{label}</header>'
                f'{block}'
                f'</div>'
            )
            pos = m.end() + block_m.end()
        html = ''.join(out)
    return html, total

CSS = r'''
/* === codebox: labelled wrappers around code fences ===================== */
.codebox {
  margin: 1em 0;
  border-radius: 6px;
  overflow: hidden;
  border: 1px solid rgba(0,0,0,0.08);
}
.codebox-header {
  padding: 4px 12px;
  font-size: 0.82em;
  font-weight: 600;
  letter-spacing: 0.02em;
  border-bottom: 1px solid rgba(0,0,0,0.08);
  display: block;
}
/* strip the inner block's own margin so the header sits flush */
.codebox pre,
.codebox > code.hl.lean.block {
  margin: 0 !important;
  border-left: none !important;
  border-radius: 0 !important;
}
.codebox > code.hl.lean.block { display: block; }

/* Lean-highlighted variants (runnable / hint / excerpt): light green */
.codebox-runnable,
.codebox-hint,
.codebox-excerpt {
  background-color: #f8fdf8;
  border-color: #cfe6cf;
}
.codebox-runnable > .codebox-header,
.codebox-hint > .codebox-header,
.codebox-excerpt > .codebox-header {
  background-color: #e3f4e3;
  color: #1e5a1e;
  border-bottom-color: #cfe6cf;
}

/* Pseudo-code: light yellow */
.codebox-pseudo {
  background-color: #fffbea;
  border-color: #f0e2a3;
}
.codebox-pseudo > .codebox-header {
  background-color: #fdf3c5;
  color: #7a5a00;
  border-bottom-color: #f0e2a3;
}

/* Deliberate error: light red */
.codebox-bug {
  background-color: #fff4f4;
  border-color: #f2c5c5;
}
.codebox-bug > .codebox-header {
  background-color: #fddede;
  color: #8b1a1a;
  border-bottom-color: #f2c5c5;
}

/* Exercise template: light red-orange (tan warning) */
.codebox-template {
  background-color: #fff7ec;
  border-color: #f3d3a8;
}
.codebox-template > .codebox-header {
  background-color: #fde6c3;
  color: #7a4a00;
  border-bottom-color: #f3d3a8;
}

/* Special-case bash blocks kept inside a runnable box: keep the light blue
   background for the code area so shell blocks stand out visually. */
.codebox-runnable pre.hl.bash.block {
  background-color: #f4faff;
}
'''

def inject_css(html: str) -> str:
    """Insert our extra CSS before </head>. Idempotent via unique marker."""
    marker = '/* codebox-injected-v1 */'
    if marker in html:
        return html
    style_block = f'<style>{marker}{CSS}</style>'
    if '</head>' in html:
        return html.replace('</head>', style_block + '</head>', 1)
    return style_block + html

def process_file(path: pathlib.Path) -> int:
    src = path.read_text()
    wrapped, n = wrap_html(src)
    wrapped = inject_css(wrapped)
    if wrapped != src:
        path.write_text(wrapped)
    return n

def main(root: str) -> None:
    total_wrapped = 0
    total_files = 0
    for p in pathlib.Path(root).rglob('*.html'):
        n = process_file(p)
        if n:
            total_wrapped += n
            total_files += 1
            print(f'  {p.relative_to(root)}: {n} boxes')
    print(f'Total: {total_wrapped} boxes across {total_files} files')

if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else '_out/html-multi')
