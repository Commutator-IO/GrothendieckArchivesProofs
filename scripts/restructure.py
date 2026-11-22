#!/usr/bin/env python3
"""Issue #39, step 2: move `Grothendieck/FolderN*.lean` into a topic tree, as in Mathlib.

Rerunnable on any checkout of `main`: it moves every file whose folder (cote) is in `TOPIC`,
rewrites the `import` lines of every Lean file and the `Grothendieck/…lean` paths written in the
text files of the repository, and writes the old-path → new-path table to
`docs/review/restructure-map.md` (to rewire the links of grothendieck-project from it). Files
already moved are left alone, so the script can be run again after other pull requests merge.

Only paths change: declaration names, and so the namespaces `Grothendieck.FolderN…`, stay as
they are, and the cote and page of each statement is carried by its `@[montpellier]` attribute
(step 3), not by the file name. `Grothendieck/Upstream/` (backports of Mathlib lemmas), `Buffalo/`
(already in topic directories `AG`, `Groupes`, `Topos`), `OpenProblems/` and the support files
of `KEEP` (`Grothendieck/Attr.lean`) keep their layout.

Usage, from the repository root:  python3 scripts/restructure.py [--dry-run]
"""

import re
import subprocess
import sys
from pathlib import Path

# The topic of each folder of the Montpellier notes (by cote), Mathlib's top-level names.
TOPIC = {}
def _set(topic, cotes):
    for c in cotes.split():
        TOPIC[c] = topic

_set("AlgebraicGeometry",
     "2 11 13 16 18 29 37 40 41 49 50 53 55 58 62 63 64 82 83 90 91 93 101 125 126 128 "
     "140_1 146 147")
_set("RingTheory", "5 21 22 23 39 43 46 67 77 84 94 100 136 153 155 160")
_set("CategoryTheory", "19 98 104 106 107 113 114 115 118 137 158 161_1 161_2 161_3")
_set("Topology", "42 120 121 150 151")
_set("Combinatorics", "74 76 79 80 81 88 89 148 152 154")
_set("Geometry", "69 70 72 73 85 86 161_6")
_set("RepresentationTheory", "10 44 123")
_set("GroupTheory", "133")
_set("NumberTheory", "78 145")
_set("Order", "156_1 156_2 156_3 156_4 156_5 156_6 156_7 156_8 156_9")
_set("LinearAlgebra", "1")
_set("AlgebraicTopology", "68")

# Files of `Grothendieck/` that are not named after a folder.
NAMED = {
    "EffectiveVenken": "AlgebraicGeometry",
    "EffectiveVenkenRelation": "AlgebraicGeometry",
    "Ihes2ILL5": "CategoryTheory",
}
IHES = "CategoryTheory"  # IhesSGA6_*: pseudo-coherence, K-groups of triangulated categories

FOLDER = re.compile(r"^Folder(\d+(?:_\d+)?)")


# Support files that are not notes of a folder and stay in `Grothendieck/`.
KEEP = {"Attr"}  # the source attributes of step 3


def topic_of(stem: str):
    if stem in NAMED:
        return NAMED[stem]
    if stem.startswith("IhesSGA6"):
        return IHES
    m = FOLDER.match(stem)
    if not m:
        return None
    # `Folder161_2Classifying` has cote 161_2, `Folder2KCoherent` cote 2, `Folder22Adic` cote 22.
    return TOPIC.get(m.group(1))


WIDTH = 100
CONT = re.compile(r"^\s*(?:[*+-] |#|-/|/-|```|$)")  # lines that start a new block


def _cut(line: str) -> int:
    """The last space at or before column `WIDTH` that is outside a code span, or -1."""
    best, ticks = -1, 0
    for i, ch in enumerate(line[: WIDTH + 1]):
        if ch == "`":
            ticks += 1
        elif ch == " " and ticks % 2 == 0 and line[:i].strip():
            best = i
    return best


def reflow(text: str, new_paths: set) -> str:
    """Re-wrap the comment lines that a rewritten path made longer than `WIDTH`.

    The overflow is carried to the next line of the same paragraph (or to a new line), and that
    line is re-wrapped in turn. Lines without a new path are left alone unless they receive
    overflow, so code and the rest of the file are unchanged."""
    lines = text.split("\n")
    dirty = {i for i, l in enumerate(lines) if len(l) > WIDTH and any(q in l for q in new_paths)}
    i = 0
    while i < len(lines):
        line = lines[i]
        if i in dirty and len(line) > WIDTH and (c := _cut(line)) > 0:
            body = line.lstrip()
            ind = line[: len(line) - len(body)]
            cont = ind + ("  " if re.match(r"[*+-] ", body) else "")
            head, rest = line[:c].rstrip(), line[c + 1 :].strip()
            lines[i] = head
            nxt = lines[i + 1] if i + 1 < len(lines) else None
            if ("-/" not in rest and nxt is not None and not CONT.match(nxt)
                    and nxt.startswith(cont) and not nxt[len(cont):].startswith(" ")):
                lines[i + 1] = cont + rest + " " + nxt.strip()
            else:
                lines.insert(i + 1, cont + rest)
                dirty = {j + 1 if j > i else j for j in dirty}
            dirty.add(i + 1)
        i += 1
    return "\n".join(lines)


def main(dry: bool) -> None:
    root = Path(".")
    moves = {}  # old module -> new module
    for f in sorted((root / "Grothendieck").glob("*.lean")):
        if f.stem in KEEP:
            continue
        t = topic_of(f.stem)
        if t is None:
            sys.exit(f"no topic for {f}: add its cote to TOPIC")
        moves[f"Grothendieck.{f.stem}"] = f"Grothendieck.{t}.{f.stem}"
    # Moves of earlier runs, from the table, so that imports of files moved then are rewritten
    # in files added since.
    mp = Path("docs/review/restructure-map.md")
    earlier = {}
    if mp.exists():
        for l in mp.read_text(encoding="utf-8").split("\n"):
            m = re.match(r"^\| `([^`]+)\.lean` \| `([^`]+)\.lean` \|$", l)
            if m:
                earlier[m.group(1).replace("/", ".")] = m.group(2).replace("/", ".")
    for old, new in moves.items():
        src = Path(*old.split(".")).with_suffix(".lean")
        dst = Path(*new.split(".")).with_suffix(".lean")
        print(f"{src} -> {dst}")
        if not dry:
            dst.parent.mkdir(parents=True, exist_ok=True)
            subprocess.run(["git", "mv", str(src), str(dst)], check=True)
    if dry:
        return
    moved_now = dict(moves)
    moves = {**earlier, **moves}
    if not moves:
        print("nothing to move")
        return
    imp = re.compile(r"^(\s*(?:public\s+)?(?:meta\s+)?import\s+)(\S+)", re.M)
    paths = {"/".join(o.split(".")) + ".lean": "/".join(n.split(".")) + ".lean"
             for o, n in moves.items()}
    path_re = re.compile("|".join(re.escape(p) for p in sorted(paths, key=len, reverse=True)))
    tracked = subprocess.run(["git", "ls-files"], capture_output=True, text=True,
                             check=True).stdout.split()
    for name in tracked:
        p = Path(name)
        if (p.suffix not in {".lean", ".md", ".yml", ".yaml", ".toml", ".py", ".json", ".txt"}
                and p.name != "NOTICE"):
            continue
        if name == "docs/review/restructure-map.md":
            continue
        text = p.read_text(encoding="utf-8")
        new = text
        if p.suffix == ".lean":
            new = imp.sub(lambda m: m.group(1) + moves.get(m.group(2), m.group(2)), new)
        new = path_re.sub(lambda m: paths[m.group(0)], new)
        if p.suffix == ".lean" and new != text:
            new = reflow(new, set(paths.values()))
        if new != text:
            p.write_text(new, encoding="utf-8")
    # Keep the root module's imports sorted.
    rootf = Path("Grothendieck.lean")
    lines = rootf.read_text(encoding="utf-8").split("\n")
    idx = [i for i, l in enumerate(lines) if l.startswith("public import Grothendieck.")]
    if idx:
        block = sorted(lines[i] for i in idx)
        for i, l in zip(idx, block):
            lines[i] = l
        rootf.write_text("\n".join(lines), encoding="utf-8")
    # The table, cumulative over runs.
    rows = {}
    if mp.exists():
        for l in mp.read_text(encoding="utf-8").split("\n"):
            m = re.match(r"^\| `([^`]+)` \| `([^`]+)` \|$", l)
            if m:
                rows[m.group(1)] = m.group(2)
    rows.update(paths)
    out = ["<!-- Written by scripts/restructure.py (issue #39, step 2). -->", "",
           "# From one file per folder to a topic tree", "",
           "Old path → new path of every moved file. Declaration names are unchanged.", "",
           "| Old path | New path |", "|---|---|"]
    out += [f"| `{o}` | `{n}` |" for o, n in sorted(rows.items())]
    mp.write_text("\n".join(out) + "\n", encoding="utf-8")
    print(f"moved {len(moved_now)} files now, {len(moves)} in all; table in {mp}")


if __name__ == "__main__":
    main("--dry-run" in sys.argv)
