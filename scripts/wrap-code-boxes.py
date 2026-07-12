#!/usr/bin/env python3
"""Post-process verso HTML output to wrap code blocks in labelled boxes.

Verso emits markdown `\[可运行\]` etc. as `<p>...[可运行]</p>` paragraphs
right before the corresponding code block. This script:

  1. finds each `<p>` whose stripped text ends in one of the known markers
  2. removes that `<p>`
  3. wraps the immediately following `<pre>...</pre>` or bare
     `<code class="hl lean block">...</code>` in
     `<div class="codebox codebox-<slug>"><div class="codebox-header">...</div>...</div>`
     (NOT <header> tag — verso's book.css has `header { position:fixed; top:0 }`
      which would pin every codebox header to the viewport top.)

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
                f'<div class="codebox-header">{label}</div>'
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
                f'<div class="codebox-header">{label}</div>'
                f'{block}'
                f'</div>'
            )
            pos = m.end() + block_m.end()
        html = ''.join(out)
    # Second pass: tokenize plain <pre>Lean-content</pre> inside hint / excerpt /
    # bug / template codeboxes. Verso's `leanBug` code_block_expander is flaky
    # about certain bodies (empirically only bodies starting with `import …`
    # get the .hl.lean.block.bug treatment), so we do it here for guaranteed
    # coverage. Idempotent: <pre class="hl …"> is skipped.
    html = highlight_hint_bug_boxes(html)
    return html, total


LEAN_KEYWORDS = frozenset("""
import open namespace end section variable universe def theorem lemma example
abbrev structure class inductive instance elab elab_rules syntax macro
macro_rules notation infix infixl infixr prefix postfix deriving attribute
export let fun match with do if then else return pure have show by at in for
while where mutual unless sorry admit exact intro intros apply cases induction
refine rw simp trivial ring linarith omega constructor assumption contradiction
decide aesop
""".split())

def _lean_tokenize_line(line: str) -> str:
    """Return HTML-safe tokenised line: keywords → span.keyword, strings → span.literal,
    -- comments → span.comment, digits → span.literal. Non-alnum passes through."""
    out = []
    i = 0
    n = len(line)
    def esc(s: str) -> str:
        return s.replace('&','&amp;').replace('<','&lt;').replace('>','&gt;').replace('"','&quot;')
    while i < n:
        c = line[i]
        # -- comment
        if c == '-' and i+1 < n and line[i+1] == '-':
            out.append('<span class="comment">' + esc(line[i:]) + '</span>')
            i = n
        # "…" string
        elif c == '"':
            j = i + 1
            while j < n and line[j] != '"':
                j += 1
            j = j + 1 if j < n else j
            out.append('<span class="literal">' + esc(line[i:j]) + '</span>')
            i = j
        # identifier / keyword
        elif c.isalpha() or c == '_':
            j = i
            while j < n and (line[j].isalnum() or line[j] in "_'"):
                j += 1
            word = line[i:j]
            if word in LEAN_KEYWORDS:
                out.append('<span class="keyword">' + esc(word) + '</span>')
            else:
                out.append(esc(word))
            i = j
        # digits → literal
        elif c.isdigit():
            j = i
            while j < n and (line[j].isdigit() or line[j] == '.'):
                j += 1
            out.append('<span class="literal">' + esc(line[i:j]) + '</span>')
            i = j
        else:
            out.append(esc(c))
            i += 1
    return ''.join(out)


def _looks_like_lean_snippet(body: str) -> bool:
    """Heuristic: text looks like Lean (has keyword / arrow / colon pattern),
    NOT just plain prose like pseudocode."""
    # keyword match
    for kw in LEAN_KEYWORDS:
        if re.search(rf'\b{re.escape(kw)}\b', body):
            return True
    # arrow / bind
    if '←' in body or '→' in body or ':=' in body or '=>' in body:
        return True
    # type-signature form  identifier ':' with capital letters after
    if re.search(r'\b[A-Za-z_][A-Za-z_0-9.]*\s*:\s*[A-Z]', body):
        return True
    return False


_HIGHLIGHT_PRE_RE = re.compile(
    r'(<div class="codebox codebox-(hint|excerpt|bug|template)">'
    r'<div class="codebox-header">[^<]*</div>)'
    r'<pre>([\s\S]*?)</pre>'
    r'(</div>)',
)

def highlight_hint_bug_boxes(html: str) -> str:
    def repl(m: re.Match[str]) -> str:
        head, kind, body_html, tail = m.group(1), m.group(2), m.group(3), m.group(4)
        # decode HTML entities back to raw text for retokenization
        raw = (body_html
               .replace('&lt;', '<')
               .replace('&gt;', '>')
               .replace('&quot;', '"')
               .replace('&amp;', '&'))
        if not _looks_like_lean_snippet(raw):
            return m.group(0)
        lines = raw.split('\n')
        highlighted = '\n'.join(_lean_tokenize_line(line) for line in lines)
        return (
            f'{head}'
            f'<pre class="hl lean block bug"><code>{highlighted}</code></pre>'
            f'{tail}'
        )
    return _HIGHLIGHT_PRE_RE.sub(repl, html)


CSS = r'''
/* Override verso's default all-black Lean palette with a proper syntax scheme
   (defaults live in verso-vars.css and map every token colour to `black`). */
:root {
  --verso-code-keyword-color: #a626a4;   /* purple- import/def/example/… (Lean 传统) */
  --verso-code-const-color:   #005cc5;   /* blue  - known constants      */
  --verso-code-literal-color: #005cc5;   /* blue  - number/string lit    */
  --verso-code-var-color:     #24292e;   /* dark  - bound variables      */
  --verso-code-sort-color:    #22863a;   /* green - Type/Prop/Sort       */
  --verso-code-typed-color:   #24292e;
}
.hl.lean .keyword { color: var(--verso-code-keyword-color); font-weight: bold; }
.hl.lean .const   { color: var(--verso-code-const-color); }
.hl.lean .literal { color: var(--verso-code-literal-color); }
.hl.lean .var     { color: var(--verso-code-var-color); font-style: italic; }
.hl.lean .sort    { color: var(--verso-code-sort-color); font-weight: bold; }
.hl.lean .comment { color: #6a737d; font-style: italic; }

.codebox {
  margin: 1em 0;
  border-left: 3px solid #ccc;
  border-radius: 4px;
  overflow: hidden;
}
.codebox-header {
  display: inline-block;
  padding: 1px 10px;
  margin: 0;
  font-size: 0.72em;
  font-weight: 600;
  letter-spacing: 0.03em;
  border-radius: 0 0 6px 0;
  line-height: 1.6;
  vertical-align: top;
}
/* strip the inner block's own margin so the pill sits flush to the top */
.codebox pre,
.codebox > code.hl.lean.block {
  margin: 0 !important;
  border-left: none !important;
  border-radius: 0 !important;
}
.codebox > code.hl.lean.block {
  display: block;
  padding: 0.6em 1em;
  background-color: transparent;
}

/* Lean-highlighted variants (runnable / hint / excerpt / bug): light green */
.codebox-runnable,
.codebox-hint,
.codebox-excerpt,
.codebox-bug {
  background-color: #f8fdf8;
  border-left-color: #4caf50;
}
.codebox-runnable > .codebox-header,
.codebox-hint > .codebox-header,
.codebox-excerpt > .codebox-header,
.codebox-bug > .codebox-header {
  background-color: #4caf50;
  color: #fff;
}

/* Deliberate error: keep code green (it's Lean), but tint the pill red so
   readers spot it as "this is meant to fail". */
.codebox-bug > .codebox-header {
  background-color: #d9534f;
}

/* Pseudo-code: light yellow */
.codebox-pseudo {
  background-color: #fffbea;
  border-left-color: #d4a017;
}
.codebox-pseudo > .codebox-header {
  background-color: #d4a017;
  color: #fff;
}

/* Exercise template: warm tan */
.codebox-template {
  background-color: #fff7ec;
  border-left-color: #e6913a;
}
.codebox-template > .codebox-header {
  background-color: #e6913a;
  color: #fff;
}

/* If the runnable box contains a bash snippet, switch its accent to blue
   (bash shell blocks are visually distinct from Lean). */
.codebox-runnable:has(pre.hl.bash.block) {
  background-color: #f4faff;
  border-left-color: #2196f3;
}
.codebox-runnable:has(pre.hl.bash.block) > .codebox-header {
  background-color: #2196f3;
}

/* Inner pre backgrounds transparent so the box tint shows through. */
.codebox > pre {
  background-color: transparent;
  padding: 0.6em 1em;
}
'''

def inject_css(html: str) -> str:
    """Insert our extra CSS before </head>. Idempotent via unique marker."""
    marker = '/* codebox-injected-v2 */'
    if marker in html:
        return html
    # remove any older version to avoid stale styles
    html = re.sub(r'<style>/\* codebox-injected-v\d+ \*/.*?</style>',
                  '', html, flags=re.S)
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
