"""oft port-layout: move an old-layout tree to the per-project layout; oft port-branch: port an old-layout
branch onto it, or a branch made before the Rocq namespace rename onto the renamed tree (OSSV-162), or both.

Every file under proofs/<p>/<h>/, counterexamples/<p>/<h>/, findings/<p>/<h>/ and patches/<p>/, and each
findings/<p>/unpatched.yaml, goes to the path layout.moved gives it, by prefix and whatever its name: a stray file (a
*.v.wip, a note) travels with its folder, and lint judges it where it lands.  A file already in the per-project layout
stays where it is, so a second run does nothing.

It refuses a path the per-project layout gives no place (proofs/lib/, proofs/lib-lean/, a file directly under
proofs/<p>/ or proofs/), a symbolic link, and a move whose target is already there with other content (a file whose
bytes differ, a folder, or a file where one of the target's folders goes).  When it refuses anything it moves nothing:
it moves a tree whole, or none of it.  It moves files and nothing else: the dune files of the per-project proofs and
counterexamples folders are `oft generate`'s to write.

It works on a working tree (port_worktree), where what git never tracks is left where it is, or on a commit
(port_commit): the commit's tree moved in a temporary index and written into the repository, with no checkout and no
blob read, so a blobless clone serves.

port-branch ports a branch made on the old layout onto a layout commit LC, whose tree is its first parent's ported, in
a worktree: it merges LC's parent into the branch (a conflict in a generated file takes the base's side), ports the
merged commit and commits that with LC as second parent, checks that the port commit changes LC exactly as the merged
commit changes LC's parent with every path moved, then merges the per-project base and renders the generated files
again.  It pushes nothing: it prints the commands that would.

With a namespace commit NC (whose tree is its first parent's renamed by `oft rename-namespace`), port-branch merges NC's
parent into the branch, takes NC's tree with each file the branch changed taken from the branch and renamed
(nsrename.rename_paths), commits that with NC as second parent, and checks the port file by file; no whole-tree rename
runs.  A branch that already holds NC has the files it changed since renamed.
"""
import bisect
import filecmp
import hashlib
import os
import posixpath
import re
import shlex
import stat
import subprocess
import sys
import tempfile

from . import layout, nsrename, paths

# why a path is refused
NO_PLACE = ("it has no place in the per-project layout (only proofs/<project>/<harness>/, "
            "counterexamples/<project>/<harness>/, findings/<project>/ and patches/<project>/ move)")
NO_PLACE_LIB_LEAN = "proofs/lib-lean/ has no place in the per-project layout"
A_LINK = "a symbolic link"
TAKEN = "%s is already there with other content"


class PortError(Exception):
    """A tree port-layout refuses: refused is [(path, why)], sorted by path, and the message one line per refusal."""

    def __init__(self, refused):
        self.refused = refused
        super().__init__("\n".join("refused %s: %s" % r for r in refused))


class GitError(Exception):
    """A git command that failed."""


def _git(repo, *args, input=None, env=None, ok=(0,)):
    """The completed `git -C repo ARGS`, its output as bytes, env added to this process's environment; GitError when
    its exit status is not one of ok."""
    r = subprocess.run(["git", "-C", repo, *args], input=input, capture_output=True,
                       env=None if env is None else dict(os.environ, **env))
    if r.returncode not in ok:
        raise GitError("git %s: %s" % (" ".join(args), r.stderr.decode(errors="replace").strip()))
    return r


def _out(repo, *args):
    """The standard output of `git -C repo ARGS` as text, without its trailing newline."""
    return _git(repo, *args).stdout.decode("utf-8", "surrogateescape").rstrip("\n")


def _old(rel):
    """Whether rel is under an old-layout top folder (layout.OLD_TOPS)."""
    top, sep, _ = rel.partition("/")
    return bool(sep) and top in layout.OLD_TOPS


def plan(rels):
    """([(path, its new path)], [(path, why it is refused)]) for the repository-relative paths rels.  Each path under an
    old-layout top folder moves to layout.moved(path), or is refused when the per-project layout gives it no place; any
    other path is not port-layout's, and is in neither list."""
    moves, refused = [], []
    for rel in rels:
        if not _old(rel):
            continue
        to = layout.moved(rel)
        if to is not None:
            moves.append((rel, to))
        elif rel.startswith("proofs/lib-lean/"):
            refused.append((rel, NO_PLACE_LIB_LEAN))
        else:
            refused.append((rel, NO_PLACE))
    return moves, refused


def _in_the_way(moves, kind_of, same):
    """[(path, why)] for each move whose target is taken: by a folder, by a file with other content (same(path, target)
    false), by a file where one of the target's folders goes, or by the target of an earlier move.  kind_of(rel) is
    "file", "dir" or None for what the tree holds at rel before anything moves."""
    refused = []
    targets, folders = set(), set()   # the targets of the moves let through so far, and every folder above them
    for src, dst in moves:
        blocker, above = None, []
        kind = kind_of(dst)
        if kind == "dir" or dst in folders or dst in targets or (kind == "file" and not same(src, dst)):
            blocker = dst
        else:
            d = posixpath.dirname(dst)
            while d and d not in folders:
                above.append(d)
                d = posixpath.dirname(d)
            blocker = next((d for d in reversed(above) if d in targets or kind_of(d) == "file"), None)
        if blocker is None:
            targets.add(dst)
            folders.update(above)
        else:
            refused.append((src, TAKEN % blocker))
    return refused


def _report_refused(refused, out):
    for rel, why in refused:
        print("refused %s: %s" % (rel, why), file=out)
    print("oft port-layout: %d file(s) refused; nothing moved" % len(refused), file=out)


# ------------------------------------------------------------------------------------------------ the working tree


def _untracked(rel):
    """Whether rel is something git never tracks: what paths.ignored says (a build's _build/ among it), and the
    unpatched binaries in findings/<p>/bin/ that `oft fetch --findings` unpacked before the per-project layout."""
    parts = rel.split("/")
    return paths.ignored(rel) or (parts[0] == "findings" and len(parts) >= 3 and parts[2] == "bin")


def _worktree_files(root):
    """(the files, the symbolic links) under root's old-layout top folders, as sorted repository-relative paths, what
    git never tracks left out."""
    files, links = [], []
    for top in layout.OLD_TOPS:
        if os.path.islink(os.path.join(root, top)):
            links.append(top)   # os.walk would follow it, and move files from wherever it points
            continue
        for dp, dns, fns in os.walk(os.path.join(root, top)):
            rel_dir = os.path.relpath(dp, root).replace(os.sep, "/")
            keep = []
            for d in dns:
                rel = "%s/%s" % (rel_dir, d)
                if _untracked(rel):
                    continue
                if os.path.islink(os.path.join(dp, d)):
                    links.append(rel)
                else:
                    keep.append(d)
            dns[:] = keep
            for f in fns:
                rel = "%s/%s" % (rel_dir, f)
                if not _untracked(rel):
                    (links if os.path.islink(os.path.join(dp, f)) else files).append(rel)
    return sorted(files), sorted(links)


def _kind_on_disk(root, rel):
    """"dir", "file" (a symbolic link among them) or None for what root holds at rel."""
    try:
        st = os.lstat(os.path.join(root, rel))
    except (FileNotFoundError, NotADirectoryError):
        return None
    return "dir" if stat.S_ISDIR(st.st_mode) else "file"


def _same_bytes(root, src, dst):
    """Whether dst is a regular file with src's bytes."""
    a, b = os.path.join(root, src), os.path.join(root, dst)
    return not os.path.islink(b) and os.path.isfile(b) and filecmp.cmp(a, b, shallow=False)


def port_worktree(root, dry_run=False, out=sys.stdout):
    """Move root's old-layout files to the per-project layout, then remove the old folders they leave empty; with
    dry_run print each move and move nothing.  0 when the files moved or there was nothing to move, 1 when anything is
    refused (each refusal printed, and nothing moved)."""
    files, links = _worktree_files(root)
    moves, refused = plan(files)
    refused += [(rel, A_LINK) for rel in links]
    refused += _in_the_way(moves, lambda rel: _kind_on_disk(root, rel), lambda s, d: _same_bytes(root, s, d))
    if refused:
        _report_refused(sorted(refused), out)
        return 1
    if dry_run:
        for src, dst in moves:
            print("%s -> %s" % (src, dst), file=out)
        print("oft port-layout: %d file(s) to move; nothing moved (dry run)" % len(moves), file=out)
        return 0
    made = set()
    for src, dst in moves:
        folder = os.path.dirname(os.path.join(root, dst))
        if folder not in made:
            os.makedirs(folder, exist_ok=True)
            made.add(folder)
        os.replace(os.path.join(root, src), os.path.join(root, dst))
    for top in layout.OLD_TOPS:
        for dp, _dns, _fns in os.walk(os.path.join(root, top), topdown=False):
            if not os.listdir(dp):
                os.rmdir(dp)
    if moves:
        print("oft port-layout: %d file(s) moved; now run ./oft generate" % len(moves), file=out)
    else:
        print("oft port-layout: 0 file(s) moved", file=out)
    return 0


# ------------------------------------------------------------------------------------------------ a commit


def _ls_tree(repo, commit):
    """{path: (mode, object id)} of every file of commit's tree."""
    raw = _git(repo, "ls-tree", "-r", "-z", "--full-tree", commit).stdout
    entries = {}
    for rec in raw.split(b"\0"):
        if rec:
            meta, path = rec.split(b"\t", 1)
            mode, _kind, oid = meta.decode().split()
            entries[path.decode("utf-8", "surrogateescape")] = (mode, oid)
    return entries


def port_commit(repo, commit):
    """The id of commit's tree with its old-layout files moved to the per-project layout, as port_worktree moves them;
    the tree is written into repo's objects and nothing else changes (no ref, no index, no working tree).  Raises
    PortError with every refusal when port-layout refuses the tree."""
    entries = _ls_tree(repo, commit)
    moves, refused = plan(rel for rel, (mode, _oid) in entries.items() if mode != "120000")
    refused += [(rel, A_LINK) for rel, (mode, _oid) in entries.items() if mode == "120000" and _old(rel)]
    sources = {src for src, _dst in moves}
    have = {rel: e for rel, e in entries.items() if rel not in sources}
    names = sorted(have)

    def kind_of(rel):
        if rel in have:
            return "file"
        i = bisect.bisect_left(names, rel + "/")
        return "dir" if i < len(names) and names[i].startswith(rel + "/") else None

    refused += _in_the_way(moves, kind_of, lambda src, dst: have[dst][1] == entries[src][1])
    if refused:
        raise PortError(sorted(refused))
    if not moves:
        return _out(repo, "rev-parse", "%s^{tree}" % commit)
    for src, dst in moves:
        have[dst] = entries[src]
    info = b"".join(b"%s %s\t%s\0" % (mode.encode(), oid.encode(), rel.encode("utf-8", "surrogateescape"))
                    for rel, (mode, oid) in have.items())
    with tempfile.TemporaryDirectory(prefix="oft-port-") as d:
        env = {"GIT_INDEX_FILE": os.path.join(d, "index")}
        _git(repo, "update-index", "-z", "--add", "--index-info", input=info, env=env)
        return _git(repo, "write-tree", "--missing-ok", env=env).stdout.decode().strip()


def layout_cli(root, commit=None, dry_run=False, out=sys.stdout):
    """`oft port-layout`: port root's working tree, or with commit print the id of that commit's tree ported."""
    if commit is None:
        return port_worktree(root, dry_run=dry_run, out=out)
    try:
        print(port_commit(root, commit), file=out)
    except PortError as e:
        _report_refused(e.refused, out)
        return 1
    except GitError as e:
        print("FAIL oft port-layout: %s" % e, file=out)
        return 1
    return 0


# ------------------------------------------------------------------------------------------------ a branch


# the per-project base a ported branch is merged with when --onto names none
ONTO = "origin/main"
# port-branch's exit statuses: 0 ported; 1 an argument refused or git failed; then
CONFLICT = 2        # a conflict the branch's owner resolves (or the generated files do not render)
REFUSED = 3         # files port-layout refuses
MISMATCH = 4        # the port commit's change is not the branch's moved
NO_MERGE_BASE = 5   # the branch shares no history with the layout commit's parent


def _rev(repo, rev):
    """The commit rev names, or None."""
    r = _git(repo, "rev-parse", "--verify", "--quiet", rev + "^{commit}", ok=(0, 1))
    return r.stdout.decode().strip() if r.returncode == 0 else None


def _is_ancestor(repo, a, b):
    return _git(repo, "merge-base", "--is-ancestor", a, b, ok=(0, 1)).returncode == 0


def _branch(repo, branch):
    """(the branch's name on origin, its tip) for BRANCH: the local branch of that name, else origin's (BRANCH may
    say origin/); (None, None) when neither exists."""
    candidates = [("refs/heads/" + branch, branch), ("refs/remotes/origin/" + branch, branch)]
    if branch.startswith("origin/"):
        candidates.append(("refs/remotes/" + branch, branch[len("origin/"):]))
    for ref, name in candidates:
        tip = _rev(repo, ref)
        if tip:
            return name, tip
    return None, None


def _changes(repo, a, b, where=lambda rel: rel):
    """{(old mode, new mode, old object id, new object id, status, where(path))} of every path that differs between
    commits a and b."""
    raw = _git(repo, "diff-tree", "-r", "-z", "--no-renames", a, b).stdout.decode("utf-8", "surrogateescape")
    fields = raw.split("\0")
    return {tuple(meta.lstrip(":").split()) + (where(rel),) for meta, rel in zip(fields[0::2], fields[1::2]) if meta}


def _not_resumable(root, worktree, tip):
    """Why the existing folder worktree cannot carry on a port of the branch whose tip is tip, or None: it must be the
    top of a worktree of root's repository, hold tip, and have no change that is not committed."""
    def ask(d, *what):
        r = _git(d, "rev-parse", *what, ok=range(256))
        lines = r.stdout.decode("utf-8", "surrogateescape").splitlines() if r.returncode == 0 else []
        return [os.path.realpath(os.path.join(d, x)) for x in lines]
    common, top = ask(root, "--git-common-dir"), ask(worktree, "--git-common-dir", "--show-toplevel")
    if top != common + [os.path.realpath(worktree)]:
        return "%s exists and is not a worktree of this repository" % worktree
    if not _is_ancestor(root, tip, _out(worktree, "rev-parse", "HEAD")):
        return "%s exists and does not hold the branch's tip %s" % (worktree, tip)
    if _out(worktree, "status", "--porcelain", "--untracked-files=no"):
        return "%s has changes that are not committed: commit them, then run this again" % worktree
    return None


def _merge(worktree, rev, what, branch, again, out):
    """Merge rev into worktree's HEAD and commit the merge; True when it is committed.  A conflict in a file
    paths.is_gen calls generated takes rev's side, since step 4 renders it again; any other conflict, or a merge git
    does not start, is left to the branch's owner, printed with `again`, the command that carries on: then False."""
    r = _git(worktree, "merge", "--no-edit", "-q", rev, ok=range(256))
    if r.returncode == 0:
        return True
    stages = {}
    for rec in _git(worktree, "ls-files", "-u", "-z").stdout.decode("utf-8", "surrogateescape").split("\0"):
        if rec:
            meta, rel = rec.split("\t", 1)
            stages.setdefault(rel, set()).add(meta.split()[2])
    hand = sorted(rel for rel in stages if not paths.is_gen(rel))
    for rel in sorted(set(stages) - set(hand)):
        if "3" in stages[rel]:
            _git(worktree, "checkout", "--theirs", "--", rel)
            _git(worktree, "add", "--", rel)
        else:
            _git(worktree, "rm", "-q", "-f", "--", rel)
    if not stages:
        print("oft port-branch: git did not merge %s into %s: %s" % (what, branch, r.stderr.decode(errors="replace")
                                                                       .strip()), file=out)
    elif hand:
        print("oft port-branch: merging %s into %s leaves %d conflict(s) for the branch's owner to resolve:"
              % (what, branch, len(hand)), file=out)
        for rel in hand:
            print("  " + rel, file=out)
    else:
        _git(worktree, "commit", "-q", "--no-edit")
        return True
    print("resolve it in %s (`git add` each file), then run:" % worktree, file=out)
    print("  git -C %s commit --no-edit && %s" % (shlex.quote(worktree), again), file=out)
    return False


def _untracked_files(worktree):
    raw = _git(worktree, "ls-files", "-o", "--exclude-standard", "-z").stdout
    return {rel for rel in raw.split(b"\0") if rel}


# An option line of `oft generate --help` that lists --skip-shared (after any short form of it): not the flag named in
# the prose of another option's help, and not a longer option that begins with it (argparse would read --skip-shared
# as an abbreviation of that option)
SKIP_SHARED_OPTION = re.compile(r"(?m)^  (?:-\w+, )*--skip-shared(?![\w-])")

# Run by a tree's own tools: of the paths on standard input, each ended by NUL, write those paths.is_shared names
# (the shared generated files), each ended by NUL
_SHARED_OF = ("import sys\n"
              "from oft import paths\n"
              "names = sys.stdin.buffer.read().decode('utf-8', 'surrogateescape').split('\\0')\n"
              "sys.stdout.buffer.write(b''.join(p.encode('utf-8', 'surrogateescape') + b'\\0' for p in names\n"
              "                                 if p and paths.is_shared(p)))\n")


def _own_python(root, args, input=None):
    """The completed `python ARGS` (its output as bytes) with root's own tools, run as ./oft there runs them: in root,
    with root/tools first on PYTHONPATH.  `python -m` and `-c` put the working folder first on sys.path, and the
    PYTHONPATH ./oft gave this process names these tools' folder, which is left out: no other copy of the tools is
    imported, and in a root without tools/oft the run fails."""
    root = os.path.abspath(root)
    these = os.path.realpath(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    kept = [p for p in os.environ.get("PYTHONPATH", "").split(os.pathsep) if p and os.path.realpath(p) != these]
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1",
               PYTHONPATH=os.pathsep.join([os.path.join(root, "tools")] + kept))
    return subprocess.run([sys.executable, *args], cwd=root, env=env, input=input, capture_output=True)


def offers_skip_shared(root):
    """True when root's own tools take `oft generate --skip-shared` (the shared generated files are rendered
    after each merge, never in a pull request): their `generate --help` lists it as an option (SKIP_SHARED_OPTION).
    port-branch's step 4 and `oft revisions --write-revisions` (revisions.render_command) read the flag this one way."""
    usage = _own_python(root, ["-m", "oft", "--root", os.path.abspath(root), "generate", "--help"]).stdout
    return SKIP_SHARED_OPTION.search(usage.decode("utf-8", "replace")) is not None


def _render(worktree, skip_shared, out):
    """Render worktree's generated files with its own tools, as `./oft generate` there would (the branch with the
    per-project base merged carries that base's tools, which its CI renders with), with --skip-shared when skip_shared.
    Prints what it printed; returns its exit status."""
    done = _own_python(worktree, ["-m", "oft", "--root", os.path.abspath(worktree), "generate"]
                       + (["--skip-shared"] if skip_shared else []))
    out.write((done.stdout + done.stderr).decode("utf-8", "replace"))
    return done.returncode


def _restore_shared(worktree, onto):
    """Give each shared generated file that differs from onto's (paths.is_shared of the worktree's own tools, which
    take --skip-shared) onto's version, and remove those onto lacks: the line renders them after each merge and lint's
    paths rule refuses a pull request that changes one, while an old-layout branch committed its own
    renders of them.  None when done, else what the tools printed when they could not name the shared files."""
    rec = _git(worktree, "diff", "--no-renames", "--name-status", "-z", onto, "--").stdout.split(b"\0")
    status = dict(zip(rec[1::2], rec[0::2]))            # path: its status against onto (A: onto lacks it)
    if not status:
        return None
    named = _own_python(worktree, ["-c", _SHARED_OF], input=b"".join(rel + b"\0" for rel in status))
    if named.returncode != 0:
        return named.stderr.decode("utf-8", "replace").strip() or "exit %d" % named.returncode
    shared = [rel for rel in named.stdout.split(b"\0") if rel in status]
    back = [rel for rel in shared if status[rel] != b"A"]
    gone = [rel for rel in shared if status[rel] == b"A"]
    if back:
        _git(worktree, "--literal-pathspecs", "checkout", onto, "--pathspec-from-file=-", "--pathspec-file-nul",
             input=b"\0".join(back))
    if gone:
        _git(worktree, "--literal-pathspecs", "rm", "-q", "-f", "--pathspec-from-file=-", "--pathspec-file-nul",
             input=b"\0".join(gone))
    return None


class _Namespace(object):
    """A namespace commit NC whose tree is its first parent's renamed (`oft rename-namespace`), with the names each
    one's release.yaml gives (keys.release_names: the defaults where it names none)."""

    def __init__(self, nc, np, old, new):
        self.nc, self.np = nc, np
        (self.old, self.old_stem), (self.new, self.new_stem) = old, new

    def rename(self, repo, commit, rels):
        """{path: its bytes renamed} of rels at commit (nsrename.rename_paths; release.yaml also gets NC's names)."""
        got = nsrename.rename_paths(repo, commit, rels, self.old, self.new, self.old_stem, self.new_stem)
        if "release.yaml" in got:
            got["release.yaml"] = nsrename.set_release_names(got["release.yaml"].decode("utf-8"), self.new,
                                                             self.new_stem).encode("utf-8")
        return got

    def generated_away(self, rel):
        """Whether rel is an opam file of the old stem: NC removed them all, and the render writes the new ones."""
        return nsrename._old_opam(rel, self.old_stem)


def _blob_id(data):
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def _namespace_commit(root, namespace_commit):
    """The _Namespace of NC, or the reason it is none."""
    from . import keys
    nc = _rev(root, namespace_commit)
    np = nc and _rev(root, nc + "^1")
    if not np:
        return None, "%s is no commit with a parent" % namespace_commit
    old, new = keys.release_names(root, np), keys.release_names(root, nc)
    if old == new:
        return None, ("%s is no rename of the Rocq namespace: its release.yaml names %s and %s, as its first parent's "
                      "does" % (namespace_commit, new[0], new[1]))
    return _Namespace(nc, np, old, new), None


def _changed(repo, a, b):
    """The paths that differ between commits a and b."""
    raw = _git(repo, "diff-tree", "-r", "-z", "--no-renames", "--name-only", a, b).stdout.decode("utf-8",
                                                                                              "surrogateescape")
    return [rel for rel in raw.split("\0") if rel]


def _tree_with(repo, commit, files, removed):
    """The id of commit's tree with files ({path: (mode, bytes)}) written and removed taken out; nothing else changes
    (no ref, no index, no working tree)."""
    info = []
    for rel, (mode, data) in sorted(files.items()):
        oid = _git(repo, "hash-object", "-w", "--stdin", input=data).stdout.decode().strip()
        info.append(b"%s %s\t%s\0" % (mode.encode(), oid.encode(), rel.encode("utf-8", "surrogateescape")))
    info += [b"0 %s\t%s\0" % (b"0" * 40, rel.encode("utf-8", "surrogateescape")) for rel in sorted(removed)]
    with tempfile.TemporaryDirectory(prefix="oft-port-") as d:
        env = {"GIT_INDEX_FILE": os.path.join(d, "index")}
        _git(repo, "read-tree", commit, env=env)
        _git(repo, "update-index", "-z", "--index-info", input=b"".join(info), env=env)
        return _git(repo, "write-tree", "--missing-ok", env=env).stdout.decode().strip()


def _namespace_problems(repo, ns, b1, pc, changed, fresh):
    """Step Q4: (path, why) of each path outside the generated files where the port commit pc is not NC's tree with the
    branch's change renamed (fresh: Q2's {path: B1's blob renamed}), or where NC changes a path the branch changed by
    more than the rename (the port takes the branch's version of such a path, so the rest of NC's change to it would be
    lost).  A file the rename leaves alone (nsrename.EXEMPT) renames to itself, so NC must leave it as NC's parent has
    it, and the port must hold the branch's."""
    np_files, b1_files = _ls_tree(repo, ns.np), _ls_tree(repo, b1)
    nc_files, pc_files = _ls_tree(repo, ns.nc), _ls_tree(repo, pc)
    touched = set(changed)
    hand = sorted(rel for rel in touched if not paths.is_gen(rel))
    try:
        np_fresh = ns.rename(repo, ns.np, [rel for rel in hand if rel in np_files])
    except nsrename.Error as e:
        return [(line.split(":", 1)[0], "the rename refuses %s's copy, so %s is no rename of it: %s"
                 % (ns.np, ns.nc, line)) for line in str(e).splitlines()]
    problems = []
    for rel in sorted(set(nc_files) | set(pc_files)):
        if rel not in touched and not paths.is_gen(rel) and pc_files.get(rel) != nc_files.get(rel):
            problems.append((rel, "the port differs from %s in a file the branch did not change" % ns.nc))
    for rel in hand:
        if rel not in b1_files:
            if rel in pc_files:
                problems.append((rel, "the branch deleted it, and the port has it"))
        elif pc_files.get(rel) != (b1_files[rel][0], _blob_id(fresh[rel])):
            problems.append((rel, "the port's blob is not the rename of the branch's"))
        if rel in np_files:
            if nc_files.get(rel, (None, None))[1] != _blob_id(np_fresh[rel]):
                problems.append((rel, "%s changes it by more than the rename, and the branch changed it too: the "
                                      "port would drop that change" % ns.nc))
        elif rel in nc_files:
            problems.append((rel, "%s adds it, and the branch added it too" % ns.nc))
    return problems


def _port_namespace(worktree, name, ns, again, out):
    """The namespace steps Q0-Q4 in worktree (port_branch); the worktree's HEAD ends at the port.  0, or an exit
    status."""
    def say(text):
        print(text, file=out)

    def refused(e):
        for line in str(e).splitlines():
            say("refused %s" % line)
        say("oft port-branch: the rename refuses %d file(s); nothing ported" % len(str(e).splitlines()))
        return REFUSED

    start = _out(worktree, "rev-parse", "HEAD")
    if _is_ancestor(worktree, ns.nc, start):
        # Q0: the branch is past the rename; the files it changed since may still name the old namespace
        since = _out(worktree, "merge-base", ns.nc, start)
        now = _ls_tree(worktree, start)
        rels = [rel for rel in _changed(worktree, since, start) if rel in now]
        away = [rel for rel in rels if ns.generated_away(rel)]
        try:
            fresh = ns.rename(worktree, start, [rel for rel in rels if rel not in away])
        except nsrename.Error as e:
            return refused(e)
        for rel, data in fresh.items():
            if _blob_id(data) != now[rel][1]:
                with open(os.path.join(worktree, rel), "wb") as fh:
                    fh.write(data)
                _git(worktree, "add", "--", rel)
        if away:
            _git(worktree, "rm", "-q", "-f", "--pathspec-from-file=-", "--pathspec-file-nul",
                 input=b"\0".join(rel.encode("utf-8", "surrogateescape") for rel in away))
        if _git(worktree, "diff", "--cached", "--quiet", ok=(0, 1)).returncode == 1:
            _git(worktree, "commit", "-q", "-m", "oft port-branch: the old namespace in files added after the rename")
            say("oft port-branch: %s already holds %s; renamed the old namespace in the files it changed since"
                % (name, ns.nc))
        else:
            say("oft port-branch: %s already holds %s" % (name, ns.nc))
        return 0
    # Q1: the base the rename was made from
    if not _is_ancestor(worktree, ns.np, start) and not _merge(worktree, ns.np, "%s^1 (%s)" % (ns.nc, ns.np), name,
                                                               again, out):
        return CONFLICT
    b1 = _out(worktree, "rev-parse", "HEAD")
    # Q2: NC's tree with each path the branch changed taken from the branch, renamed
    changed = _changed(worktree, ns.np, b1)
    b1_files = _ls_tree(worktree, b1)
    kept = [rel for rel in changed if rel in b1_files and not ns.generated_away(rel)]
    try:
        fresh = ns.rename(worktree, b1, kept)
    except nsrename.Error as e:
        return refused(e)
    removed = [rel for rel in changed if rel not in kept]
    tree = _tree_with(worktree, ns.nc, {rel: (b1_files[rel][0], data) for rel, data in fresh.items()}, removed)
    # Q3
    pc = _out(worktree, "commit-tree", tree, "-p", b1, "-p", ns.nc,
              "-m", "oft port-branch: %s onto the Rocq namespace %s (OSSV-162)" % (name, ns.new))
    # Q4
    problems = _namespace_problems(worktree, ns, b1, pc, changed, fresh)
    if problems:
        say("oft port-branch: the port commit %s is not %s with the branch's change renamed:" % (pc, ns.nc))
        for rel, why in problems:
            say("  %s: %s" % (rel, why))
        return MISMATCH
    _git(worktree, "checkout", "-q", "--detach", pc)
    say("oft port-branch: %s onto the Rocq namespace %s: %d file(s) the branch changed, %d renamed"
        % (name, ns.new, len(changed), sum(1 for rel, data in fresh.items() if _blob_id(data) != b1_files[rel][1])))
    return 0


def port_branch(root, branch, worktree, layout_commit=None, namespace_commit=None, onto=ONTO, out=sys.stdout):
    """`oft port-branch`: port BRANCH in the worktree DIR onto the layout commit LC, the namespace commit NC, or both
    (the layout first), and push nothing.  LC must be a commit whose tree is its first parent's ported (port_commit),
    NC one whose release.yaml names another namespace or opam stem than its first parent's (the rename of its first
    parent, `oft rename-namespace`), and onto a commit that holds each.  The steps:
      0. DIR is a new worktree of the branch's tip when it does not exist (or is an empty folder); one an earlier run
         left goes on from its HEAD;
      1. unless LC's parent is in the branch already, merge it (old layout); a conflict in a generated file takes the
         parent's side, any other stops with 2 for the branch's owner to resolve;
      2. the merged commit B1 ported: refusals stop with 3; else the port commit C, with parents B1 and LC;
      3. LC..C must be LC^1..B1 with every path through layout.canonical (status, modes and object ids), else 4;
      Q0. a branch that already holds NC: the files it changed since its merge base with NC renamed (rename_paths of
         nsrename) and committed as "oft port-branch: the old namespace in files added after the rename" when anything
         changed; then step 4;
      Q1. unless NC's parent is in the branch, merge it (conflicts as in 1);
      Q2. the port tree: NC's tree with each path the merged commit B1 changes against NC's parent taken from B1 and
         renamed (rename_paths; release.yaml also gets NC's names; an opam file of the old stem, or a path B1
         deleted, is removed); no whole-tree rename runs; a file the rename refuses stops with 3, each printed;
      Q3. the port commit PC, with parents B1 and NC;
      Q4. outside the generated files, PC holds NC's blob of every path the branch did not change, and the rename of
         B1's blob of every path it did; and NC changes no path the branch changed by more than the rename (the port
         would drop the rest of that change); else 4, naming each path;
      4. the port checked out, onto merged (conflicts as in 1), the generated files rendered again by the worktree's
         own tools (`./oft generate`, with --skip-shared when those tools take it, and then each shared generated file
         set to onto's version, or removed where onto has none) and committed as "oft generate after port-branch" when
         anything changed;
      5. the commands that push the result and tell its pull request printed; none is run.
    A branch that already holds LC skips steps 1-3.  5 when the branch shares no history with the parent of the first
    commit it lacks; 1 when an argument is refused or git fails."""
    try:
        return _port_branch(root, branch, worktree, layout_commit, namespace_commit, onto, out)
    except GitError as e:
        print("FAIL oft port-branch: %s" % e, file=out)
        return 1


def _port_branch(root, branch, worktree, layout_commit, namespace_commit, onto, out):
    def say(text):
        print(text, file=out)

    if not layout_commit and not namespace_commit:
        say("oft port-branch: name --layout-commit LC, --namespace-commit NC, or both")
        return 1
    name, tip = _branch(root, branch)
    if tip is None:
        say("oft port-branch: %s is no branch of this repository or of origin" % branch)
        return 1
    lc = lp = ns = None
    if layout_commit:
        lc = _rev(root, layout_commit)
        lp = lc and _rev(root, lc + "^1")
        if not lp:
            say("oft port-branch: %s is no commit with a parent" % layout_commit)
            return 1
        try:
            pure = port_commit(root, lp) == _out(root, "rev-parse", lc + "^{tree}")
        except PortError:
            pure = False
        if not pure:
            say("oft port-branch: %s is not a pure port of its first parent" % layout_commit)
            return 1
    if namespace_commit:
        ns, why = _namespace_commit(root, namespace_commit)
        if ns is None:
            say("oft port-branch: %s" % why)
            return 1
    base = _rev(root, onto)
    for commit, given, what in ((lc, layout_commit, "per-project base"), (ns and ns.nc, namespace_commit,
                                                                           "renamed base")):
        if commit and (not base or not _is_ancestor(root, commit, base)):
            say("oft port-branch: %s does not hold %s, so it is no %s to port onto" % (onto, given, what))
            return 1
    fresh = not os.path.lexists(worktree) or (os.path.isdir(worktree) and not os.listdir(worktree))
    if not fresh:
        why = _not_resumable(root, worktree, tip)
        if why:
            say("oft port-branch: %s" % why)
            return 1
    start = tip if fresh else _out(worktree, "rev-parse", "HEAD")
    again = ["./oft", "port-branch", branch]
    for flag, value in (("--layout-commit", layout_commit), ("--namespace-commit", namespace_commit)):
        if value:
            again += [flag, value]
    again = " ".join(shlex.quote(a) for a in again + ["--worktree", worktree, "--onto", onto])
    ported = lc is None or _is_ancestor(root, lc, start)
    first, first_name = (lp, layout_commit) if not ported else (
        (ns.np, namespace_commit) if ns and not _is_ancestor(root, ns.nc, start) else (None, None))
    if first and _git(root, "merge-base", start, first, ok=(0, 1)).returncode == 1:
        say("oft port-branch: %s has no merge base with %s^1 (%s): it cannot be ported" % (branch, first_name, first))
        return NO_MERGE_BASE
    if fresh:
        _git(root, "worktree", "add", "-q", "--detach", worktree, tip)
    if lc and ported:
        say("oft port-branch: %s already holds %s" % (branch, layout_commit))
    elif lc:
        if not _is_ancestor(root, lp, start) and not _merge(worktree, lp, "%s^1 (%s)" % (layout_commit, lp), branch,
                                                             again, out):
            return CONFLICT
        b1 = _out(worktree, "rev-parse", "HEAD")
        try:
            tree = port_commit(worktree, b1)
        except PortError as e:
            say(str(e))
            say("oft port-branch: %d file(s) refused; nothing ported" % len(e.refused))
            return REFUSED
        c = _out(worktree, "commit-tree", tree, "-p", b1, "-p", lc,
                 "-m", "oft port-branch: %s onto the per-project layout" % name)
        want, got = _changes(worktree, lp, b1, layout.canonical), _changes(worktree, lc, c)
        if want != got:
            say("oft port-branch: the port commit %s does not change %s as %s changes %s, every path moved:"
                % (c, lc, b1, lp))
            for row in sorted(want - got):
                say("  only before the port: %s %s %s" % (row[4], row[3], row[5]))
            for row in sorted(got - want):
                say("  only after the port:  %s %s %s" % (row[4], row[3], row[5]))
            return MISMATCH
        _git(worktree, "checkout", "-q", "--detach", c)
    if ns:
        rc = _port_namespace(worktree, name, ns, again, out)
        if rc:
            return rc
    if not _merge(worktree, onto, onto, branch, again, out):
        return CONFLICT
    if lc:
        # a branch that already held LC (its owner merged the per-project base) may still add old-layout paths that
        # git's rename detection did not move, a new fuzz target's proofs folder say: they move too, or the port stops
        head = _out(worktree, "rev-parse", "HEAD")
        try:
            tree = port_commit(worktree, head)
        except PortError as e:
            say(str(e))
            say("oft port-branch: %d file(s) refused; nothing ported" % len(e.refused))
            return REFUSED
        if tree != _out(worktree, "rev-parse", head + "^{tree}"):
            c = _out(worktree, "commit-tree", tree, "-p", head,
                     "-m", "oft port-branch: the old-layout paths %s still had, onto the per-project layout" % name)
            _git(worktree, "checkout", "-q", "--detach", c)
    before = _untracked_files(worktree)
    skip_shared = offers_skip_shared(worktree)
    if _render(worktree, skip_shared, out) != 0:
        say("oft port-branch: the generated files do not render in %s; fix that there, commit, and run: %s"
            % (worktree, again))
        return CONFLICT
    why = skip_shared and _restore_shared(worktree, onto)
    if why:
        say("oft port-branch: the tools in %s take --skip-shared but did not name their shared generated files: %s"
            % (worktree, why))
        return CONFLICT
    _git(worktree, "add", "-u")
    new = sorted(_untracked_files(worktree) - before)
    if new:
        _git(worktree, "add", "--pathspec-from-file=-", "--pathspec-file-nul", input=b"\0".join(new))
    if _git(worktree, "diff", "--cached", "--quiet", ok=(0, 1)).returncode == 1:
        _git(worktree, "commit", "-q", "-m", "oft generate after port-branch")
    final = _out(worktree, "rev-parse", "HEAD")
    onto_what = " and ".join(([] if lc is None else ["the per-project layout"])
                             + ([] if ns is None else ["the Rocq namespace %s" % ns.new]))
    say("oft port-branch: %s ported onto %s in %s: %s" % (branch, onto_what, worktree, final))
    # git's sparse object walk (pack.useSparse, on by default) sends every moved file again when it pushes a commit on
    # top of the move: 2.41 GB against 462 KB on the real tree, and GitHub refuses a push over 2 GB
    say("nothing is pushed; to push it, a fast-forward of %s:" % name)
    say("  git -c pack.useSparse=false push origin %s" % shlex.quote("%s:refs/heads/%s" % (final, name)))
    say("and, for a pull request whose head is %s:" % name)
    say("  gh pr comment %s --body %s" % (shlex.quote(name), shlex.quote(
        "Ported to %s by oft port-branch: %s" % (onto_what, final))))
    return 0
