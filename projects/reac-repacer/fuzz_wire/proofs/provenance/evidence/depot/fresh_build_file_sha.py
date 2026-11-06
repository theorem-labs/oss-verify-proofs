#!/usr/bin/env python3
"""fresh_build_file_sha.py -- the per-file record that a build compiled exactly the .v files of a commit, by the
sha256 of the FILE BYTES (no git object id).

  fresh_build_file_sha.py hash DIR PREFIX > LIST.tsv
      run where the build's copy is (the build VM's workspace DIR): one row `sha256<TAB>path` per .v file under
      DIR/PREFIX, path relative to DIR.
  fresh_build_file_sha.py table REPO REV PREFIX LIST.tsv REV_LABEL COPY_LABEL > OUT.tsv
      one row per .v file of REV under PREFIX: the path, the sha256 of its bytes at REV (git cat-file blob), the
      sha256 LIST gives for the same path (`-` if the copy lacks it), and `yes` if they are equal; then one row per
      path of LIST that REV lacks. The header names the two columns `file sha256 at REV_LABEL` and
      `file sha256 of COPY_LABEL`. Exit 1 if any row is not `yes`."""
import hashlib, os, subprocess, sys


def main():
    if sys.argv[1:2] == ['hash']:
        d, prefix = sys.argv[2:4]
        rows = []
        for dp, _, fn in os.walk(os.path.join(d, prefix)):
            for f in fn:
                if f.endswith('.v'):
                    p = os.path.join(dp, f)
                    rows.append('%s\t%s' % (hashlib.sha256(open(p, 'rb').read()).hexdigest(), os.path.relpath(p, d)))
        print('\n'.join(sorted(rows, key=lambda r: r.split('\t')[1])))
        return
    if sys.argv[1:2] != ['table']:
        sys.exit(__doc__)
    repo, rev, prefix, lst, rev_label, copy_label = sys.argv[2:8]
    copy = {}
    for l in open(lst).read().splitlines():
        if l.strip():
            s, p = l.split('\t')
            copy[p] = s
    paths = [l.split('\t', 1)[1] for l in subprocess.run(['git', '-C', repo, 'ls-tree', '-r', rev, '--', prefix],
                                                         capture_output=True, text=True, check=True).stdout.splitlines()
             if l.endswith('.v')]
    print('path\tfile sha256 at %s\tfile sha256 of %s\tequal' % (rev_label, copy_label))
    bad = 0
    for p in sorted(paths):
        b = subprocess.run(['git', '-C', repo, 'cat-file', 'blob', '%s:%s' % (rev, p)], capture_output=True, check=True).stdout
        s = hashlib.sha256(b).hexdigest()
        c = copy.get(p, '-')
        ok = 'yes' if c == s else 'no'
        bad += ok != 'yes'
        print('%s\t%s\t%s\t%s' % (p, s, c, ok))
    for p in sorted(set(copy) - set(paths)):
        print('%s\t-\t%s\tno' % (p, copy[p]))
        bad += 1
    sys.exit(1 if bad else 0)


if __name__ == '__main__':
    main()
