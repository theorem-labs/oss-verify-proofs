#!/usr/bin/env python3
"""hdrfix.py IN.v OUT.v -- the committed-header rule applied to the COMMENTS
of one generated lib/B file; code text is never touched (stripcmp.py proves it). Every rewrite is in place on its line,
so no line number moves. The donor's Copyright / SPDX lines stay unchanged; every dated `Modified by Theorem Labs`
notice stays as an undated `Modified by Theorem Labs:` notice (Apache-2.0 4(b)); dates, agent / lane names, host paths
and branch names go (a branch name becomes the bare commit sha); a frozen or third-party tool is named by its sha256 (and the
start-up tool set commit that holds it), this slice's own writer by its repo-relative path in provenance/evidence/startup-B/.
"""
import re, sys

# A rule that removes a branch, lane or worker name matches it by its SHAPE (a branch token before a commit sha, a
# lane or worker token before a possessive or a tool path), not by the literal name, so this file holds no such name.
SUBS = [
    (r'Modified by Theorem Labs, 20\d\d-\d\d(?:-\d\d)?:', 'Modified by Theorem Labs:'),
    (r'\([\w.-]+/[\w.-]+ dbb5a97ad14 startup-set-2026-10-30, frozen ([0-9a-f]{12})\)',
     r'(frozen \1, start-up tool set of commit dbb5a97ad14)'),
    (r', [\w.-]+/[\w.-]+ dbb5a97ad14 startup-set-2026-10-30\)', ', start-up tool set of commit dbb5a97ad14)'),
    (r'\bport-[a-z]+ tools/startup/', ''),
    (r'origin/ossv/recipes (?=[0-9a-f]{7,})', 'commit '),
    (r'origin/[a-z]+/[a-z]+-tools (?=[0-9a-f]{7,})', 'commit '),
    (r"by port-[a-z]+'s(?=\s)", 'by'),
    (r"\bh-[a-z]+-[a-z0-9]+'s gen_ab1hk\.py", 'gen_ab1hk.py (sha256 0f51cb9cdb18)'),
    (r"\bh-[a-z]+-[a-z0-9]+'s collector/boxb1\.py \(sha256 0fe1e96732e2", 'boxb1.py (sha256 0fe1e96732e2'),
    (r'\(pass ([12]), h-[a-z]+-[a-z0-9]+ \w+, ', r'(pass \1, '),
    (r'on the pau-pipeline-next3 ORIGINAL bin/fuzz_uci/fuzz_uci\.asan-ubsan;',
     'on the pinned fuzz_uci.asan-ubsan (sha256 a1b86e424adde6f65d345459822690a6c21e9e606446b91b4ad25e9f3ef6e7fc);'),
    (r'Image: pau-pipeline-next3 ORIGINAL bin/fuzz_uci/fuzz_uci\.asan-ubsan sha256', 'Image: the pinned fuzz_uci.asan-ubsan, sha256'),
    (r'Image: the pau-pipeline-next3 ORIGINAL bin/fuzz_uci/fuzz_uci\.asan-ubsan of reac-repacer,',
     'Image: the pinned bin/fuzz_uci/fuzz_uci.asan-ubsan of reac-repacer,'),
    (r'\(reac-repacer/fuzz_uci asan-ubsan, pau-pipeline-next3 ORIGINAL\)', '(the reac-repacer/fuzz_uci asan-ubsan pin)'),
    (r'\(pau-pipeline-next3 reac-repacer result/bin/fuzz_uci\)', '(the reac-repacer/fuzz_uci asan-ubsan pin)'),
    (r'; generator h-[a-z]+-[a-z0-9]+ [\w-]+/sub/exitdrv/gen_exitB\.py\.', '; generator provenance/evidence/startup-B/exitdrv/gen_exitB.py.'),
    # second pass (on the text of 44d69bf53aa): frozen / third-party tools are named by sha256 only (their copies hold
    # host-path regexes and cannot ship in provenance/evidence/); this lane's own writer lives in its evidence slice
    (r'provenance/evidence/tools/(atable|gen_ad2|gen_ad1k|af0m|ae3i)\.py \(frozen', r'\1.py (frozen'),
    (r'provenance/evidence/tools/(gen_ab1hk|boxb1)\.py \(sha256', r'\1.py (sha256'),
    (r'provenance/evidence/exitdrv/gen_exitB\.py', 'provenance/evidence/startup-B/exitdrv/gen_exitB.py'),
    (r'names UciSyms -> UciSyms and its addresses moved to reac-repacer/fuzz_uci\'s ASan build\.',
     'record name TfibSyms -> UciSyms and its addresses moved to reac-repacer/fuzz_uci\'s ASan+UBSan build.'),
]
OUT_OF_COMMENT = re.compile(r'\(\*|\*\)')


def comment_spans(t):
    spans, depth, start, i = [], 0, 0, 0
    while i < len(t) - 1:
        two = t[i:i + 2]
        if two == '(*':
            if depth == 0:
                start = i
            depth += 1
            i += 2
            continue
        if two == '*)' and depth:
            depth -= 1
            i += 2
            if depth == 0:
                spans.append((start, i))
            continue
        i += 1
    return spans


def fix(t):
    out, last, n = [], 0, 0
    for a, b in comment_spans(t):
        out.append(t[last:a])
        c = t[a:b]
        for rx, rep in SUBS:
            c, k = re.subn(rx, rep, c)
            n += k
        assert c.count('\n') == t[a:b].count('\n')
        out.append(c)
        last = b
    out.append(t[last:])
    return ''.join(out), n


if __name__ == '__main__':
    src, dst = sys.argv[1], sys.argv[2]
    t2, n = fix(open(src).read())
    open(dst, 'w').write(t2)
    print('hdrfix %s: %d rewrites' % (src.split('/')[-1], n))
