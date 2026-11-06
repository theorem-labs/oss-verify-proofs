#!/usr/bin/env python3
"""scrub_out.py -- the one writer of a record's committed slice. Read-only on SRC; writes only OUT.

Copies SRC into OUT (default SRC/commit), leaving out what is not committed: env.sh (the host paths of the images),
the planted ELF copies (*.elf), RECORD.md and MANIFEST.md (written separately), logs, caches and OUT itself.
  - Tool scripts (every file under a tools/ directory, and run.sh) are copied byte for byte: they must already hold no
    host path (their inputs are arguments or environment values).
  - Every other file is a raw output: each image path given with --img is rewritten to its TOKEN, and each path of a
    file under a --tooldir to the file's name (the bare --tooldir to `tools`).
  - Every images.sha256 becomes the table `token<TAB>sha256<TAB>image`, built from the --img list (sha256 measured
    here), which defines the tokens.
It refuses its own output (exit 1; OUT is left as it was) when any file or file name in it still holds a path under
the home or mnt roots, an internal branch prefix (the word cold and a slash), a worker name (h, a dash, a word and a
dash) or the tool registry's branch name (case-insensitive; FORBIDDEN below), and when an --img path is missing.
On success OUT is replaced whole.
usage: scrub_out.py SRC [--out OUT] [--tooldir DIR]... [--img TOKEN PATH IMAGE]..."""
import argparse, hashlib, os, re, shutil, sys

# spelled with one-letter classes so that this file does not hold the text it refuses
FORBIDDEN = re.compile(rb'/[h]ome/|/[m]nt/|[c]old/|(?<![a-z0-9_])[h]-[a-z][a-z0-9]*-|[f]leet', re.I)
SKIP_DIRS = {'__pycache__', 'earlier'}       # earlier/: prior versions of record, archived; not shipped with this record
SKIP_FILES = {'env.sh', 'RECORD.md', 'REVIEW.md', 'MANIFEST.md'}
SKIP_EXT = ('.elf', '.log', '.pyc')


def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('src')
    ap.add_argument('--out')
    ap.add_argument('--tooldir', action='append', default=[])
    ap.add_argument('--img', nargs=3, action='append', default=[], metavar=('TOKEN', 'PATH', 'IMAGE'))
    a = ap.parse_args()
    src = os.path.abspath(a.src)
    out = os.path.abspath(a.out or os.path.join(src, 'commit'))
    tmp = out + '.tmp'
    bad, subst, imgrows = [], {}, []
    for tok, p, what in a.img:
        if not re.fullmatch(r'[A-Z][A-Z0-9_]*', tok):
            bad.append('token %r is not UPPER_CASE' % tok)
        if not os.path.isfile(p):
            bad.append('--img %s: the path given is not a file' % tok); continue
        for v in {p, os.path.abspath(p), os.path.realpath(p)}:
            subst[v.encode()] = tok.encode()
        imgrows.append((tok, sha(p), what))
    for d in a.tooldir:
        for v in {d.rstrip('/'), os.path.abspath(d), os.path.realpath(d)}:
            subst[v.encode()] = b'tools'
            if os.path.isdir(v):
                for n in os.listdir(v):
                    subst[(v + '/' + n).encode()] = n.encode()
    keys = sorted(subst, key=len, reverse=True)
    shutil.rmtree(tmp, ignore_errors=True)
    written = rewritten = 0
    for root, dirs, files in os.walk(src):
        dirs[:] = sorted(x for x in dirs if x not in SKIP_DIRS and os.path.join(root, x) not in (out, tmp))
        for n in sorted(files):
            if n in SKIP_FILES or n.endswith(SKIP_EXT):
                continue
            sp = os.path.join(root, n); rel = os.path.relpath(sp, src); dp = os.path.join(tmp, rel)
            os.makedirs(os.path.dirname(dp), exist_ok=True)
            data = open(sp, 'rb').read()
            if 'tools' in rel.split(os.sep)[:-1] or n == 'run.sh':
                pass                                      # a tool script: copied byte for byte
            elif n == 'images.sha256':
                data = b'token\tsha256\timage\n' + b''.join(('%s\t%s\t%s\n' % r).encode() for r in imgrows)
                rewritten += 1
            else:
                new = data
                for k in keys:
                    new = new.replace(k, subst[k])
                rewritten += new != data
                data = new
            for m in FORBIDDEN.finditer(data):
                bad.append('%s:%d: forbidden text left (%d bytes at offset %d)'
                           % (rel, data.count(b'\n', 0, m.start()) + 1, m.end() - m.start(), m.start()))
            if FORBIDDEN.search(rel.encode()):
                bad.append('%s: forbidden text in the file name' % rel)
            with open(dp, 'wb') as f:
                f.write(data)
            shutil.copymode(sp, dp)                       # run.sh and the tools stay executable
            written += 1
    if bad:
        shutil.rmtree(tmp, ignore_errors=True)
        for b in bad:
            print('scrub_out: REFUSED: ' + b, file=sys.stderr)
        sys.exit(1)
    shutil.rmtree(out, ignore_errors=True)
    os.rename(tmp, out)
    print('scrub_out: %d files written to %s (%d raw outputs rewritten); %d image tokens; 0 forbidden hits'
          % (written, os.path.relpath(out, src), rewritten, len(imgrows)))


if __name__ == '__main__':
    main()
