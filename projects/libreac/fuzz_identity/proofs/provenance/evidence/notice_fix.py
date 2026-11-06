#!/usr/bin/env python3
"""notice_fix.py - make each wrong Theorem Labs donor notice of the unit true, from its row of notice-claims.tsv.

THE INPUT

notice-claims.tsv as notice_claims.py (in this directory) writes it: a header row, one row per donor notice, and
"# ..." total lines, which are skipped. A row is WRONG when its verdict is "counts differ", "donor holds under half"
or "omits changes". The script reads no other row.

For each wrong row it reads line `line` of proofs/`file` in the unit. That line must be one whole notice,
    (* Modified by <name>, <date>: <body> *)
from its first character to its last, with no other "(*" or "*)" in <body>.

THE RULE

 - <name> is "Theorem Labs" (a notice of ours). <name> and <date> stay. What changes depends on the column
   claimed_counts, which says whether the notice gives figures:
   (i) claimed_counts is "-": the notice gives no figures, and its verdict says it declares fewer changes than the
       file has, or cites a file that holds less than half of it. Its body becomes, from the row's columns donor,
       categories, loc, new_or_changed and left_out, and from the measure of the categories below:
           made from <donor>[, with its <categories> changed]; <new_or_changed> of its <loc> lines of code are new
           or changed and <left_out> lines of the source are left out.
       <categories> keeps only the categories of the column that change the measure. The column copies what the
       old notice declared, and no measure checks that declaration, so a category is kept only when the measure
       needs it: the categories are taken in the column's order, and a category is dropped when notice_claims.py's
       measure of the row's file against its donor (read as the row reads it), with the categories kept so far
       and the ones not yet taken but without this one, gives the row's matched. Dropping it then changes no
       figure. The kept categories are written as an English list: "a", "a and b", "a, b and c". When none is
       kept, or the column is "-", the part in brackets is left out. This is the form of the third PLAIN pattern
       of notice_claims.py, and of the notices that commit c58d5c3e2002 added (for example "made from
       projects/cgif/cgif_file_fuzzer/proofs/lib/YL0s.v, with its module paths changed; 1 of its 294 lines of code
       is new or changed and 1 line of the source is left out."). The other words of the old body are not columns,
       so the new body does not keep them: a donor image sha256, "for libreac/fuzz_identity's program walk", "its
       addresses moved to libreac/fuzz_identity's ASan build" (the column then reads "addresses", and the new body
       says "addresses ... changed" only when the measure needs that category).
   (ii) claimed_counts is not "-": the notice gives figures, and its verdict is "counts differ" (the only wrong
       verdict a notice with figures can have), which says its figures are not the measured ones. Only its figures
       change; every other byte of the line stays. In a "made" notice, the clause that notice_claims.py's
       COUNTS_MADE finds ("N of its M lines of code are new or changed and K lines of the source are left out") is
       written again from new_or_changed, loc and left_out, as in (i). In a "match" notice, the two numbers of the
       clause that COUNTS_MATCH finds ("N of its M lines of code ... match lines of") become matched and loc.
   Where a clause is written again, "lines" becomes "line" after the number 1, and "are" becomes "is" when its
   subject is 1.
 - <name> is "Rares Buhai" (an outside contributor's notice): the script does not change the line. It counts the
   row as routed to the licence tool of record (fix/licence-of-record), next series, per the CI/CD lead 04:44Z.
 - Any other <name>: the row is refused.

So each new line is made from its row's columns, the measure of its categories in (i), the templates above, and the
old line's own text (its head, and in (ii) its words around the figures). It has no other input.

THE REFUSALS

The script leaves a refused row's line as it is, and prints the row with the reason. It refuses a row when:
 - its line is not one whole notice as above (for example a notice that runs over two lines);
 - donor is "-", or a column that a number is read from is not a number, or (in (i)) categories names a category
   other than module paths, addresses and numbers;
 - (ii) the line has no clause that COUNTS_MADE or COUNTS_MATCH finds with the claimed figures, or (match) matched
   or loc is 1, where "lines ... match" would need other words;
 - the row does not hold for the tree: notice_claims.py, run on the line as it is now, does not give the row's
   form, donor, read_at, categories, claimed_counts, loc, donor_loc, matched, new_or_changed, left_out and verdict;
 - notice_claims.py, run on the new line in the new file, does not give the verdict "agrees", the form "made
   plain" in (i) and the row's form in (ii), and the row's loc, donor_loc, matched, new_or_changed and left_out.

THE CHECKS

The script makes every new file in memory and runs checks 1 and 2 on it. If one fails, it writes nothing and exits
1. With --write and both checks passed, it writes the files. Then it runs check 3 on the files on disk, and exits 1
if check 3 fails.
 1. Mapping, both ways. Each line that is different in a file after the run is the line of exactly one rewritten
    row. Each wrong Theorem Labs row that is not refused has exactly one line that is different. The line of each
    wrong Rares Buhai row is not changed. No file gets more or fewer lines.
 2. Code. In each changed file, the text with every comment removed (notice_claims.py's strip_comments, which
    writes a blank for each character of a comment, then the blanks at the end of each line removed) is byte-equal
    to the same text of the file before the run.
 3. The contributor's lines, over every .v file of the unit. A contributor line is a line that contains
    "Modified by Rares Buhai".
    (a) Each contributor line of commit --contrib-pin is byte-equal to the line with the same number in the file
        on disk, and the disk has no other contributor line.
    (b) Item 17 of the OSS Verify release's comment-pass rulings (2026-11-01): each contributor line of commit
        --merge-base, with notice_claims.py's to_new_layout applied (proofs/<p>/<t>/lib/ becomes
        projects/<p>/<t>/proofs/lib/), is byte-equal to the line with the same number in the file on disk, and the
        disk has no other contributor line.

THE OUTPUT

One line per rewritten row (REWRITE), refused row (REFUSED) and routed row (ROUTED), then the totals: rows read,
wrong rows by name, lines changed, lines added, and each check with its counts.

USAGE

  python3 notice_fix.py --repo <repository root> --unit projects/libreac/fuzz_identity \\
      [--table notice-claims.tsv] [--rev HEAD] [--contrib-pin 0a3a06762f6b] [--merge-base 1aeda8ab8602] \\
      [--only <file>:<line> ...] [--write]
Without --write it writes nothing. --only limits the rows that are rewritten to the ones named (a trial run).
"""
import argparse
import hashlib
import os
import re
import subprocess
import sys

sys.dont_write_bytecode = True  # no __pycache__ in the evidence directory
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from notice_claims import (COUNTS_MADE, COUNTS_MATCH, Repo, assess, measure, notices, resolve,  # noqa: E402
                           strip_comments, to_new_layout)

WRONG = {"counts differ", "donor holds under half", "omits changes"}
OURS = "Theorem Labs"
CONTRIBUTOR = "Rares Buhai"
CONTRIB_MARK = "Modified by " + CONTRIBUTOR
ROUTE = "licence tool of record (fix/licence-of-record), next series, per the CI/CD lead 04:44Z"
NOTICE_LINE = re.compile(r"^\(\* Modified by (?P<who>[^,]+), (?P<date>[0-9-]+): (?P<body>.*) \*\)$")
KNOWN_CATS = ("module paths", "addresses", "numbers")
MEASURED = ("form", "donor", "read_at", "categories", "claimed_counts", "loc", "donor_loc", "matched",
            "new_or_changed", "left_out", "verdict")
COUNTS = ("loc", "donor_loc", "matched", "new_or_changed", "left_out")


def english_list(items):
    return items[0] if len(items) == 1 else ", ".join(items[:-1]) + " and " + items[-1]


def number(row, column):
    if not row[column].isdigit():
        raise ValueError(f"{column} is {row[column]!r}, not a number")
    return int(row[column])


def made_clause(row):
    n, m, k = number(row, "new_or_changed"), number(row, "loc"), number(row, "left_out")
    return (f"{n} of its {m} line{'' if m == 1 else 's'} of code {'is' if n == 1 else 'are'} new or changed and "
            f"{k} line{'' if k == 1 else 's'} of the source {'is' if k == 1 else 'are'} left out")


def needed_categories(row, matched_under):
    """The categories of the row's column that change the measure (rule (i)); matched_under(cats) is the measure's
    matched for the row's file against its donor under cats."""
    cats = [] if row["categories"] == "-" else row["categories"].split(", ")
    for c in cats:
        if c not in KNOWN_CATS:
            raise ValueError(f"categories names {c!r}, which a made-from notice cannot declare")
    want, kept = number(row, "matched"), list(cats)
    for c in cats:
        without = [x for x in kept if x != c]
        if matched_under(without) == want:
            kept = without
    return kept


def new_body(row, old, matched_under):
    """(the new body of a row whose old body is old, the form notice_claims.py must then give), or raise ValueError
    with the reason of the refusal."""
    donor = row["donor"]
    if donor == "-" or not donor:
        raise ValueError("donor is '-'")
    if row["claimed_counts"] == "-":  # (i)
        cats = needed_categories(row, matched_under)
        with_cats = f", with its {english_list(cats)} changed" if cats else ""
        return f"made from {donor}{with_cats}; {made_clause(row)}.", "made plain"
    claimed = row["claimed_counts"].split("/")  # (ii)
    kind = row["form"].split()[0]
    m = (COUNTS_MADE if kind == "made" else COUNTS_MATCH if kind == "match" else None)
    m = m.search(old) if m else None
    if not m or list(m.groups()) != claimed:
        raise ValueError(f"no {kind} clause with the claimed figures {row['claimed_counts']} in the line")
    if kind == "made":
        return old[:m.start()] + made_clause(row) + old[m.end():], row["form"]
    matched, loc = number(row, "matched"), number(row, "loc")
    if 1 in (matched, loc):
        raise ValueError(f"matched {matched} of loc {loc}: 'lines ... match' would need other words")
    return old[:m.start(1)] + str(matched) + old[m.end(1):m.start(2)] + str(loc) + old[m.end(2):], row["form"]


def measure_line(repo, rev_id, unit_proofs, text, lineno):
    for line, notice in notices(text):
        if line == lineno:
            return assess(repo, rev_id, unit_proofs, text, notice)
    return None


def code_text(text):
    return "\n".join(line.rstrip() for line in strip_comments(text).split("\n"))


def git(root, *args):
    return subprocess.run(["git", *args], cwd=root, capture_output=True, check=True).stdout


def contributor_lines(data):
    """{line number: line bytes} of the contributor lines of a file's bytes."""
    mark = CONTRIB_MARK.encode()
    return {i + 1: line for i, line in enumerate(data.split(b"\n")) if mark in line}


def at_commit(root, rev, unit):
    """{path under the repository: {line number: line bytes}} of the contributor lines of the unit's .v files at rev."""
    out = git(root, "grep", "-l", "-z", "-F", CONTRIB_MARK, rev, "--", f"{unit}/*.v")
    paths = [p.decode().split(":", 1)[1] for p in out.split(b"\0") if p]
    result = {}
    cat = subprocess.Popen(["git", "cat-file", "--batch"], cwd=root, stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    try:
        for path in paths:
            cat.stdin.write(f"{rev}:{path}\n".encode())
            cat.stdin.flush()
            head = cat.stdout.readline().split()
            size = int(head[2])
            data = cat.stdout.read(size)
            cat.stdout.read(1)
            result[path] = contributor_lines(data)
    finally:
        cat.stdin.close()
        cat.wait()
    return result


def on_disk(root, unit):
    result = {}
    for d, _, fs in os.walk(os.path.join(root, unit)):
        for f in fs:
            if f.endswith(".v"):
                p = os.path.join(d, f)
                with open(p, "rb") as fh:
                    lines = contributor_lines(fh.read())
                if lines:
                    result[os.path.relpath(p, root)] = lines
    return result


def check_contributor(root, unit, rev, now, mapped):
    """(lines equal, lines at rev, failures) of check 3a (mapped False) or 3b (mapped True)."""
    then = at_commit(root, rev, unit)
    equal, total, fails = 0, 0, []
    for path in sorted(set(then) | set(now)):
        old, new = then.get(path, {}), now.get(path, {})
        for ln in sorted(set(old) | set(new)):
            if ln not in old:
                fails.append(f"{path}:{ln}: a contributor line that {rev} does not have")
                continue
            total += 1
            want = to_new_layout(old[ln].decode("utf-8")).encode("utf-8") if mapped else old[ln]
            if new.get(ln) == want:
                equal += 1
            else:
                fails.append(f"{path}:{ln}: not equal to {rev}'s line{' after the layout mapping' if mapped else ''}")
    return equal, total, fails


def read_table(path):
    with open(path, encoding="utf-8") as f:
        lines = [line.rstrip("\n") for line in f if not line.startswith("#")]
    header = lines[0].split("\t")
    return [dict(zip(header, line.split("\t"))) for line in lines[1:] if line]


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--repo", required=True, help="repository root (the directory that holds projects/)")
    ap.add_argument("--unit", required=True, help="unit directory under the repository")
    ap.add_argument("--table", default=os.path.join(os.path.dirname(os.path.abspath(__file__)), "notice-claims.tsv"))
    ap.add_argument("--rev", default="HEAD", help="commit at which projects/ donors are read (default HEAD)")
    ap.add_argument("--contrib-pin", default="0a3a06762f6b")
    ap.add_argument("--merge-base", default="1aeda8ab8602")
    ap.add_argument("--only", action="append", default=[], help="<file>:<line>; rewrite only the rows named")
    ap.add_argument("--write", action="store_true", help="write the files (default: print only)")
    args = ap.parse_args()

    root = os.path.abspath(args.repo)
    repo = Repo(root)
    rev_id = repo.commit(args.rev)
    if not rev_id:
        sys.exit(f"notice_fix: {args.rev} is not a commit of {root}")
    unit_proofs = os.path.join(root, args.unit, "proofs")
    with open(args.table, "rb") as f:
        table_sha = hashlib.sha256(f.read()).hexdigest()
    rows = read_table(args.table)
    print(f"notice_fix: table {os.path.relpath(args.table, root)} sha256 {table_sha}; donors at {rev_id[:12]}")

    keys = [(r["file"], int(r["line"])) for r in rows]
    if len(set(keys)) != len(keys):
        sys.exit("notice_fix: the table has two rows for one line")
    only = {(o.rsplit(":", 1)[0], int(o.rsplit(":", 1)[1])) for o in args.only}

    wrong = [r for r in rows if r["verdict"] in WRONG]
    by_name, rewrite, refused, routed = {}, {}, [], []
    texts = {}
    for r in wrong:
        rel, ln = r["file"], int(r["line"])
        if rel not in texts:
            with open(os.path.join(unit_proofs, rel), "rb") as f:
                texts[rel] = f.read().decode("utf-8")
        lines = texts[rel].split("\n")
        line = lines[ln - 1] if 0 < ln <= len(lines) else ""
        m = NOTICE_LINE.match(line)
        who = m.group("who") if m else (re.search(r"Modified by ([^,]+),", line) or [None, "?"])[1]
        by_name[who] = by_name.get(who, 0) + 1
        if who == CONTRIBUTOR:
            routed.append((rel, ln, line))
            continue
        if only and (rel, ln) not in only:
            continue
        if who != OURS:
            refused.append((rel, ln, f"the notice is {who}'s, neither ours nor the contributor's"))
            continue
        if not m or "(*" in m.group("body") or "*)" in m.group("body"):
            refused.append((rel, ln, "the line is not one whole notice"))
            continue
        now = measure_line(repo, rev_id, unit_proofs, texts[rel], ln)
        diff = [c for c in MEASURED if now is None or str(now[c]) != r[c]]
        if diff:
            refused.append((rel, ln, "the row does not hold for the tree: " + ", ".join(
                f"{c} {r[c]!r} measured {None if now is None else str(now[c])!r}" for c in diff)))
            continue
        theirs, _ = resolve(repo, rev_id, unit_proofs, r["donor"], line)
        try:
            body, form = new_body(r, m.group("body"), lambda cats: measure(texts[rel], theirs, cats)[2])
        except ValueError as e:
            refused.append((rel, ln, str(e)))
            continue
        rewrite[(rel, ln)] = (line, f"(* Modified by {OURS}, {m.group('date')}: {body} *)", r, form)

    # The new files, in memory.
    new_texts = {}
    for (rel, ln), (old, new, _, _) in sorted(rewrite.items()):
        lines = new_texts.get(rel, texts[rel]).split("\n")
        lines[ln - 1] = new
        new_texts[rel] = "\n".join(lines)
    # The new line, measured in the new file.
    for (rel, ln), (old, new, r, form) in sorted(rewrite.items()):
        after = measure_line(repo, rev_id, unit_proofs, new_texts[rel], ln)
        bad = after is None or after["form"] != form or after["verdict"] != "agrees" or any(
            str(after[c]) != r[c] for c in COUNTS)
        if bad:
            refused.append((rel, ln, "the new line does not agree with the measure: " + (
                "no notice" if after is None else f"{after['form']}, {after['verdict']}")))
            lines = new_texts[rel].split("\n")
            lines[ln - 1] = old
            new_texts[rel] = "\n".join(lines)
            del rewrite[(rel, ln)]
    new_texts = {rel: t for rel, t in new_texts.items() if t != texts[rel]}

    for (rel, ln), (old, new, _, _) in sorted(rewrite.items()):
        print(f"REWRITE\t{rel}:{ln}\t{new}")
    for rel, ln, why in sorted(refused):
        print(f"REFUSED\t{rel}:{ln}\t{why}")
    for rel, ln, _ in sorted(routed):
        print(f"ROUTED\t{rel}:{ln}\t{ROUTE}")

    # Check 1: mapping, both ways.
    changed, fails1, added = set(), [], 0
    for rel, t in new_texts.items():
        a, b = texts[rel].split("\n"), t.split("\n")
        added += len(b) - len(a)
        if len(a) != len(b):
            fails1.append(f"{rel}: {len(a)} lines before, {len(b)} after")
            continue
        changed |= {(rel, i + 1) for i, (x, y) in enumerate(zip(a, b)) if x != y}
    line_no_row = sorted(changed - set(rewrite))
    row_no_line = sorted(set(rewrite) - changed)
    fails1 += [f"{rel}:{ln}: a changed line with no row" for rel, ln in line_no_row]
    fails1 += [f"{rel}:{ln}: a rewritten row with no changed line" for rel, ln in row_no_line]
    routed_changed = [(rel, ln) for rel, ln, line in routed
                      if rel in new_texts and new_texts[rel].split("\n")[ln - 1] != line]
    fails1 += [f"{rel}:{ln}: a contributor row's line changed" for rel, ln in routed_changed]
    # Check 2: code.
    code_equal = sum(code_text(texts[rel]) == code_text(t) for rel, t in new_texts.items())
    fails2 = [f"{rel}: its code changed" for rel, t in new_texts.items() if code_text(texts[rel]) != code_text(t)]

    print(f"rows read {len(rows)}; wrong {len(wrong)}: " + ", ".join(f"{k} {v}" for k, v in sorted(by_name.items())))
    print(f"rewritten {len(rewrite)}; refused {len(refused)}; routed {len(routed)}")
    print(f"lines changed {len(changed)} in {len(new_texts)} files; lines added {added}")
    print(f"check 1 mapping: {len(changed)} changed lines with a row, {len(rewrite)} rewritten rows with a line; "
          f"{len(line_no_row)} lines with no row, {len(row_no_line)} rows with no line; "
          f"{len(routed) - len(routed_changed)} of {len(routed)} contributor rows' lines unchanged: "
          f"{'PASS' if not fails1 else 'FAIL'}")
    print(f"check 2 code: {code_equal} of {len(new_texts)} changed files equal with comments removed: "
          f"{'PASS' if not fails2 else 'FAIL'}")
    for f in fails1 + fails2:
        print(f"  {f}")
    if fails1 or fails2:
        print("notice_fix: nothing written")
        sys.exit(1)

    if args.write:
        for rel, t in sorted(new_texts.items()):
            with open(os.path.join(unit_proofs, rel), "wb") as f:
                f.write(t.encode("utf-8"))
        print(f"wrote {len(new_texts)} files")
    else:
        print("no --write: nothing written")

    # Check 3: the contributor's lines, on disk.
    now = on_disk(root, args.unit)
    ok = True
    for name, rev, mapped in (("3a byte-equal to", args.contrib_pin, False),
                              ("3b item 17, equal after the layout mapping to", args.merge_base, True)):
        equal, total, fails = check_contributor(root, args.unit, rev, now, mapped)
        n_now = sum(len(v) for v in now.values())
        ok_here = not fails and equal == total == n_now
        ok = ok and ok_here
        print(f"check {name} {rev}: {equal} of {total} contributor lines ({n_now} on disk): "
              f"{'PASS' if ok_here else 'FAIL'}")
        for f in fails:
            print(f"  {f}")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
