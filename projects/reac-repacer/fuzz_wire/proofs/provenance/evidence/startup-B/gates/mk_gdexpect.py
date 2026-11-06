#!/usr/bin/env python3
"""mk_gdexpect.py BASE OUT -- writes gate GD's expectation file (gates/GD.expect) from the trunk clone ($TR), so no commit
sha in it is typed by hand: for each of the 19 lib/B files it compares lib/B/<name>.v at BASE (a full commit sha) with
the trunk clone's HEAD and writes `<name> equal`, or `<name> <class> <commits> lines <n,...> <reason>` where the commits
are exactly those of `git log BASE..HEAD` that change the file (oldest first, 12 digits), the lines are exactly the
lines that differ (the line counts must be equal), the class is `comment` when the comment-stripped texts are equal
(gates/tools/stripcmp.py) and `code` otherwise, and the reason is this file's REASONS entry. A changed file with no
REASONS entry is class `comment-pass` (a comment-only pass over lib/B: a scrub, a licence header, a sha converter)
when its comment-stripped text is EQUAL to the base's, with a fixed reason that says so. Every changed file, with a
REASONS entry or not, must also be comment-stripped EQUAL to its bytes in the run of record (RECORD, each file's
sha256 checked against RECORD_SHA256 first). A change since the run of record that is not comment-only, a code change
in a file with no REASONS entry, a REASONS entry for an equal file, or a record file with another sha256 stops the run
(exit 2, nothing written). A HEAD older than the per-project layout is read at the path it holds. The text passes
textguard.py before it is written (exit 2 and nothing written on a forbidden token).

  python3 mk_gdexpect.py b4dc8707252afd0001c6461acc83580493ed3ccf gates/GD.expect
"""
import hashlib
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.dont_write_bytecode = True
for _d in (os.path.join(HERE, '..', 'tools'), os.path.join(os.environ.get('W', ''), 'tools')):
    if os.path.isfile(os.path.join(_d, 'textguard.py')):
        sys.path.insert(0, _d)
        break
import textguard  # noqa: E402

STRIPCMP = os.path.join(HERE, 'tools', 'stripcmp.py')   # rc 0 iff the comment-stripped texts are equal

ALL19 = ('YB01 YB03 YB05 YB12 YB13 YB1h YB1k YB1l YB1m YB1v YCej YD1k YD1y YD2i YD2j YE23 YE37 YE3i YF0m').split()
LIB = 'projects/reac-repacer/fuzz_wire/proofs/lib/B/%s.v'
BASE_LIB = 'proofs/reac-repacer/fuzz_wire/lib/B/%s.v'   # lib/B at BASE: it predates the per-project layout, so it is read at the path it holds
# The run of record: the 19 files it gated are lib/B of RECORD (read at the path it holds), and RECORD_SHA256 is their
# sha256 as that run's logs/SHA256.inputs.txt lists them (that list's sha256 11dc740bb741)
RECORD = '56e88deda11edb8aa66cce8a6d9087225292341f'
RECORD_SHA256 = {
    'YB01': '65f4fb770ada68039677b304f32ed911025821b71834a1af28e6cda5b0bce75a',
    'YB03': '53a57742c23d22145c6a399369367456061513fa777885b93fa483383be73ab9',
    'YB05': '60f58b2ac6a9ecb5d8f8eb6880df59e70d365620acd5f0dc3fcc29edd6f3df4d',
    'YB12': '37a050459be73f971bc6b175ad556b773ad2376c5602ead76a9f827c950d6a86',
    'YB13': '3ff296d86432045566ca2d3970d6542038f09db35104095c1f321128d51fcce2',
    'YB1h': '3ea98fc90a84f427b1f771e44de90c0fdcc3c2d914034f4e45210decc2827c53',
    'YB1k': '7e0841cb72a249b601d9a937bf0f73545fd601362b5d1ff338c2c809bfb856e8',
    'YB1l': '00dfbb6ade0d68f3ad2befced91e0a767751d53de4c3b297556a2b619d1d1352',
    'YB1m': '1223c05904e760d761fdf46635e9acc7565eba374f68c66386ac89fc6cd277d8',
    'YB1v': 'b2ec68cede62c6719c16315add10446a69c6195fb11c9e7d8405bdc43d81ced5',
    'YCej': '3d7b982398b28fef50dc8ab716ff8cfcdb57123428b86819ffcfdba3b5a8188c',
    'YD1k': '70a6820a425026c6024f6990409f282e1179bade9b51de28be8149aadf997ce9',
    'YD1y': '9a00af588900e1f9c2ce9deab2ffbb4a89650a0c42aff7de411e773a80fe754a',
    'YD2i': '6180ff23d530e4d4aa01ec02d7979f983154e86ddf5329681c9b022fffc21929',
    'YD2j': '34ab3d3d31e890a1f10954b8d09ab2f2830b9e4068878e48f3c659a28701bcde',
    'YE23': 'd7bccb3d2bd87a22b480a524890ece95ef504a106d440bce3b070d8f1da96344',
    'YE37': '173bf04ca9ba76c31526ebc5d3faad2aafc0fd6ff126cec2659eba4b149db356',
    'YE3i': 'b642c0b52e772f187ba1dc12d516c4749e7486593b32a21f4852ff9fa31495a8',
    'YF0m': '040b99f21180b3339c3896f5912e3fe5c3705e8d8c42aa8de0591f4a8adad57e',
}
PASS_REASON = ('a comment-only pass over lib/B: no REASONS entry; comment-stripped EQUAL (stripcmp) to the base and to the '
               'run of record\'s bytes (commit %s, each sha256 checked)' % RECORD[:12])
TOOLNAMES = ('the tool-name change: from exitdrv/gen_exitW.py, line 4 (the notice) names the data map by role (map tool '
             'sha256 4d51ec1c0069) and line 5 (the Read-from line) names the generator gen_exitW.py by name and sha256 '
             '(comment-formats row CL7b)')
REASONS = {
    'YB05': 'the tool-name change: from tools/mk_yb05_wire.py, the notice (line 4) names the relocation tools by role and '
            'sha256 (4d51ec1c0069, 2d846496640d)',
    'YD1y': TOOLNAMES,
    'YE23': TOOLNAMES,
    'YE37': 'the exit-driver writer\'s n = 0 proof: gen_exitW.py b38434be6f64 writes `]].` where `].` left the YE37.v:179 '
            'bracket list unclosed (the B core build stopped there); YE37.vo compiles in the B core with it (Build '
            'section); lines 4 and 5: ' + TOOLNAMES,
    'YF0m': 'NOTICE lines only: nsW.py cd059cec21be keeps the record rename out of the provenance notice (line 4), and af0m '
            'f8201f503394 of the start-up set at commit f141794333162b writes the notice heads with their month and names '
            'itself (lines 3-5)',
}
HEAD = """# GD.expect -- what gate GD (run_gates.sh) expects of the 19 lib/B files against a BASE commit. GD reads this file, and
# the WANT of every GD step on the 19 comes from it; nothing about GD's expected result is kept anywhere else.
# Written by gates/mk_gdexpect.py from the trunk clone (base..HEAD); do not edit by hand.
#   base <full commit sha>   the commit whose proofs/reac-repacer/fuzz_wire/lib/B/<name>.v each file is compared with
#   <name> equal             byte-equal to the base
#   <name> <class> <commit>[,<commit>...] lines <n>[,<n>...] <reason>
#                            the file differs from the base: <class> is the kind of change, the commits are exactly the
#                            commits of the trunk clone (base..HEAD) that change the file, the lines are exactly the lines
#                            that differ (same line count in both), and the reason says why the change is wanted
#     comment                comment-stripped EQUAL (stripcmp); not Require-only (reqdiff refuses a comment by design)
#     require                Require sentences only (reqdiff); comment-stripped different
#     code                   a code change: comment-stripped different and not Require-only; nothing in GD can show it
#                            is right, so the reason names the check that does (a build, a gate)
# The base is the last delivered head before the current changes: b4dc8707252a, the commit that released the push
# hold (G9p passes against the B core's re-guarded YD1g).
"""
# written only when a row is comment-pass, before the base line's note, so a GD.expect without one is unchanged
PASS_HEAD = """#     comment-pass           a file with no REASONS entry in the writer, changed by a comment-only pass over lib/B (a
#                            scrub, a licence header, a sha converter): comment-stripped EQUAL to the base and to the run
#                            of record's bytes (commit %s); GD runs the comment class's steps on it
""" % RECORD[:12]
HEAD_TAIL = '# The base is the last delivered head'


def git(*a):
    return subprocess.run(['git', '-C', os.environ['TR'], *a], check=True, capture_output=True, text=True).stdout


def git_bytes(*a):
    return subprocess.run(['git', '-C', os.environ['TR'], *a], check=True, capture_output=True).stdout


def head_text(n):
    """lib/B/<n>.v at HEAD; a HEAD older than the per-project layout holds it at BASE_LIB"""
    r = subprocess.run(['git', '-C', os.environ['TR'], 'cat-file', '-e', 'HEAD:' + LIB % n], capture_output=True)
    return git('show', 'HEAD:' + (LIB if r.returncode == 0 else BASE_LIB) % n)


def record_text(n, bad):
    """lib/B/<n>.v of the run of record, or None (with a refusal in bad) when its sha256 is not RECORD_SHA256's"""
    raw = git_bytes('show', '%s:%s' % (RECORD, BASE_LIB % n))
    got = hashlib.sha256(raw).hexdigest()
    if got != RECORD_SHA256[n]:
        bad.append('%s: lib/B of the run of record (commit %s) has sha256 %s, the record list names %s'
                   % (n, RECORD[:12], got[:12], RECORD_SHA256[n][:12]))
        return None
    return raw.decode().replace('\r\n', '\n').replace('\r', '\n')   # as git() reads text


def stripped_equal(a, b):
    with tempfile.TemporaryDirectory() as d:
        pa, pb = os.path.join(d, 'a.v'), os.path.join(d, 'b.v')
        open(pa, 'w').write(a)
        open(pb, 'w').write(b)
        rc = subprocess.run([sys.executable, STRIPCMP, pa, pb], capture_output=True).returncode
    if rc not in (0, 1):
        sys.exit('mk_gdexpect: %s exited %d (0 or 1 expected): nothing written' % (STRIPCMP, rc))
    return rc == 0


def changed(a, b):
    la, lb = a.split('\n'), b.split('\n')
    if len(la) != len(lb):
        return 'line counts %d / %d' % (len(la), len(lb))
    return 'lines %s' % [i + 1 for i, (x, y) in enumerate(zip(la, lb)) if x != y]


def main():
    base, out = sys.argv[1:3]
    if not re.fullmatch(r'[0-9a-f]{40}', base):
        sys.exit('mk_gdexpect: BASE must be a full commit sha')
    rows, bad, npass = ['base ' + base], [], 0
    for n in ALL19:
        a, b = git('show', '%s:%s' % (base, BASE_LIB % n)), head_text(n)
        r = record_text(n, bad)
        if r is not None and r != b and not stripped_equal(r, b):
            bad.append('%s: changed since the run of record (commit %s) and not comment-only: comment-stripped DIFFERENT '
                       '(stripcmp), %s differ from the record' % (n, RECORD[:12], changed(r, b)))
            continue
        if a == b:
            if n in REASONS:
                bad.append('%s: equal to the base, but REASONS has an entry for it' % n)
            rows.append('%s equal' % n)
            continue
        la, lb = a.split('\n'), b.split('\n')
        if len(la) != len(lb):
            bad.append('%s: %d / %d lines (GD needs the same line count)' % (n, len(la), len(lb)))
            continue
        lines = [i + 1 for i, (x, y) in enumerate(zip(la, lb)) if x != y]
        commits = [c[:12] for c in reversed(git('log', '--format=%H', '%s..HEAD' % base, '--', BASE_LIB % n, LIB % n).split())]
        cls = 'comment' if stripped_equal(a, b) else 'code'
        if n in REASONS:
            reason = REASONS[n]
        elif cls == 'comment':
            cls, reason, npass = 'comment-pass', PASS_REASON, npass + 1
        else:
            bad.append('%s: changed (code, lines %s) but REASONS has no entry for it' % (n, lines))
            continue
        rows.append('%s %s %s lines %s %s' % (n, cls, ','.join(commits), ','.join(map(str, lines)), reason))
    if bad:
        for b in bad:
            sys.stderr.write('mk_gdexpect: %s: refused, nothing written\n' % b)
        sys.exit(2)
    text = (HEAD.replace(HEAD_TAIL, PASS_HEAD + HEAD_TAIL, 1) if npass else HEAD) + '\n'.join(rows) + '\n'
    textguard.refuse(text, out)
    open(out, 'w').write(text)
    print('mk_gdexpect: wrote %s: base %s; %s' % (out, base[:12], '; '.join(r.split(' lines ')[0] for r in rows[1:]
                                                                       if not r.endswith(' equal'))))


if __name__ == '__main__':
    main()
