"""pins.py (startup-Y evidence copy): the pinned-original gate that hsform.py calls (pins.provenance), cut from
pins.py sha256 4778073f01be (start-up tool set 2026-10-29), lines 39-44, 77-96, 99-133, 136-141. Changes: the pin table is ONLY the file
that OSSV_BINARIES_TSV names (the repository index/binaries.tsv); the original's two fallbacks to host locations are
removed, and the refusal message names that variable. The rest of pins.py (emitcheck, stamp) is not shipped."""
import hashlib, os, sys

DEFAULT_INDEX = os.environ.get('OSSV_BINARIES_TSV')
EXTRA = [x for x in os.environ.get('OSSV_PIN_TABLES', '').split(':') if x]


def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def tables(index=None):
    """[(label, lines)] of every pin table the gate consults, in order."""
    out = []
    chosen = index or DEFAULT_INDEX
    if chosen:
        out.append(('%s (sha256 %s)' % (chosen, sha256(chosen)[:12]), open(chosen).read().splitlines()))
    for t in EXTRA:
        out.append(('%s (OSSV_PIN_TABLES)' % t, open(t).read().splitlines()))
    if not out:
        sys.exit('pins: no pin table to consult: set OSSV_BINARIES_TSV to the repository index/binaries.tsv.')
    return out


def pinned(image, index=None):
    """(project, harness, build, file, sha) of the pinned row whose sha256 is the image's; exits 1 when there is none.
    Besides the index, OSSV_PIN_TABLES (colon-separated) names more pin tables for units pinned elsewhere (the pau
    pipelines, e.g. pau-libreac-v190): each is a binaries.tsv-format file or a SHA256SUMS file (`sha  path`)."""
    s = sha256(image)
    base = os.path.basename(image)
    parts = set(os.path.abspath(image).split(os.sep))
    consulted, same_name = [], []
    for label, lines in tables(index):
        consulted.append(label)
        for line in lines:
            p = line.rstrip('\n').split('\t')
            if len(p) >= 8:
                if p[7] == s:
                    return p[0], p[1], p[2], p[3], s
                if p[3] == base or p[3].split('.')[0] == base:
                    # the unit the image's own path names first: that row is the generation it should have been
                    same_name.append((0 if p[0] in parts else 1,
                                      '%s/%s %s %s is pinned at sha256 %s' % (p[0], p[1], p[2], p[3], p[7])))
                continue
            q = line.split()
            if len(q) == 2 and q[0] == s:
                return 'pin', os.path.basename(label.split(' ')[0]), '-', os.path.basename(q[1].lstrip('*')), s
    sys.exit('pins: REFUSED: %s (sha256 %s) is not a pinned original.\n'
             '  consulted: %s\n'
             '%s'
             '  Read the unit\'s own published image; OSSV_BINARIES_TSV names the index that pins it.'
             % (image, s, '\n             '.join(consulted),
                ''.join('  note: %s\n' % n for _, n in sorted(same_name)[:6])))


def provenance(image, twin=None, index=None):
    proj, harness, build, fname, s = pinned(image, index)
    line = '(* Read from: %s (%s/%s %s) sha256 %s' % (fname, proj, harness, build, s)
    if twin:
        line += '; unstripped twin sha256 %s' % sha256(twin)
    return line + ' *)'
