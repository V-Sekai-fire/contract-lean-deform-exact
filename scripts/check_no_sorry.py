#!/usr/bin/env python3
"""No admitted goals. Enforced, because the build does not enforce it.

`sorry` typechecks. A file full of them builds green and `lake build` exits 0 whether every
theorem is closed or none of them are -- the warning scrolls past and the exit code says
nothing. So the build is not the gate.

It also refuses the quieter routes. `sorryAx` is what `sorry` elaborates to and can be
written directly. `native_decide` discharges a goal by running compiled code, which trusts
the compiler rather than the kernel, so the kernel never checks it. Both are assertion with
extra steps.

COMMENTS ARE STRIPPED FIRST, AND THE FIRST VERSION OF THIS FILE IS WHY. Written as a grep,
it matched the word `sorry` in its own docstring and failed a repository with zero admitted
goals -- a gate that always fails, which PITFALLS 2 rates worse than none because it teaches
people to ignore output. Lean block comments nest, so this scans rather than pattern-matches.

Enumeration rather than sampling: every tracked .lean file is read, and the count prints even
when it is zero, because a gate that says nothing on success is one nobody can tell ran.

Usage:  python scripts/check_no_sorry.py [root] [--self-test]
"""
import os
import re
import sys

BANNED = re.compile(r"\bsorry\b|\bsorryAx\b|\bnative_decide\b")


def strip_comments(src):
    """Lean source with `--` line comments and nestable `/- -/` blocks blanked out.

    Characters are replaced by spaces rather than deleted so line and column numbers still
    point at the real source. A gate that reports the wrong line is a gate somebody stops
    trusting on the second use.
    """
    out = list(src)
    i, n, depth = 0, len(src), 0
    while i < n:
        if depth == 0 and src.startswith("--", i):
            while i < n and src[i] != "\n":
                out[i] = " "
                i += 1
            continue
        if src.startswith("/-", i):
            depth += 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if depth > 0 and src.startswith("-/", i):
            depth -= 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if depth > 0 and src[i] != "\n":
            out[i] = " "
        i += 1
    return "".join(out)


def scan(root):
    problems, files = [], 0
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d != ".lake"]
        for f in sorted(filenames):
            if not f.endswith(".lean"):
                continue
            path = os.path.join(dirpath, f)
            files += 1
            try:
                src = open(path, encoding="utf-8").read()
            except OSError as exc:                                # noqa: BLE001
                # Unreadable is unchecked, and unchecked must not read as clean.
                problems.append("%s: unreadable (%s)" % (path, exc))
                continue
            for i, line in enumerate(strip_comments(src).splitlines(), 1):
                m = BANNED.search(line)
                if m:
                    problems.append("%s:%d: %s" % (path, i, m.group(0)))
    return problems, files


def main(argv):
    root = argv[1] if len(argv) > 1 and not argv[1].startswith("--") else "."
    problems, files = scan(root)
    print("checked %d Lean file(s) under %s" % (files, root))
    for p in problems:
        print("  FAIL  %s" % p)
    if problems:
        print("\nFAIL: %d admitted goal(s). A theorem with an admitted goal is a conjecture."
              % len(problems))
        return 1
    print("  ok    0 admitted goals: no sorry, no sorryAx, no native_decide")

    if "--self-test" in argv:
        # A gate that cannot fail certifies the defect, so it proves it can fail.
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            open(os.path.join(d, "Admitted.lean"), "w").write(
                "theorem admitted : 1 = 1 := by sorry\n")
            planted, _ = scan(d)
            if not planted:
                print("  MISS  the control did not fire on a planted sorry")
                return 1
            open(os.path.join(d, "Admitted.lean"), "w").write(
                "/- the word sorry inside a comment -/\ntheorem t : 1 = 1 := rfl\n")
            commented, _ = scan(d)
            if commented:
                print("  MISS  the control fired on a comment: %s" % commented[0])
                return 1
        print("  ok    control fires on a planted sorry and not on one in a comment")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
