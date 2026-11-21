#!/usr/bin/env python3
"""Emit a twin file using the unit index and carrier profile.

The same sections, binders, statements and proof scripts are replayed with the
twinned names renamed. Missing grant arguments are marked, never invented.
Rules and limits are in README.md.
"""
import os
import re
from .rocqparse import (IDENT, REF_RE, blank_text,
                        parse_binders, PROOF_KW, _find_top)
ECONSTRUCTOR_RE = re.compile(r"\becon(?:structor)\b")

#: Tactics whose argument is the NAME of a constant, not a term: a reference there
#: must stay a bare name, never become an application.  `fold` is NOT one of them --
#: it takes a term, so a discharged section definition keeps its arguments there
COMBINATORS = {"first", "solve", "try", "repeat", "now", "idtac", "progress", "all",
               "once", "exactly_once", "timeout", "time", "abstract", "do", "fail",
               "guard", "assert_succeeds", "assert_fails", "tryif", "only"}

#: `name:` openers of a tactic-in-term, whose `:` is not a type ascription.
TERM_COLON = {"ltac", "ltac2", "constr", "uconstr", "open_constr", "eval", "type",
              "ident", "numgoals", "lazymatch", "match", "context"}

UNFOLD_RE = re.compile(r"\bunfold\b")
STRAT_RE = re.compile(r"\b(?:cbn|cbv|simpl|lazy|vm_compute|native_compute|red|hnf|"
                      r"delta|pattern|decompose)\b\s*(\[[^\]]*\])")


def const_regions(text):
    """Spans of `text` where an identifier is a constant name, not a term."""
    out = []
    for m in UNFOLD_RE.finditer(text):
        j = m.end()
        while j < len(text):
            c = text[j]
            if c in ";|":
                break
            if c == "." and (j + 1 >= len(text) or text[j + 1] in " \t\r\n"):
                break        # Sentence dot, not a qualified name.
            if text.startswith(" in ", j) or text.startswith(" with ", j):
                break
            j += 1
        out.append((m.end(), j))
    for m in STRAT_RE.finditer(text):
        out.append(m.span(1))
    return out

HEADER_COMMENT_RE = re.compile(r"^\s*\(\*")


# ------------------------------------------------------------------ names



def load_twins(path, pkg):
    """Read `rtwins.tsv` -> {full R1 name: (twin module, twin name)}."""
    out = {}
    if not path:
        return out
    with open(path, encoding="utf8") as fh:
        head = None
        for line in fh:
            line = line.rstrip("\n")
            if not line.strip() or line.startswith("#"):
                continue
            cols = line.split("\t")
            if head is None:
                head = cols
                continue
            row = dict(zip(head, cols))
            full = pkg + "." + row["r1_module"] + "." + row["name"]
            out[full] = (row["twin_module"], row["twin_name"])
    return out


def load_ltacs(path, pkg):
    """Read `rltacs.tsv` -> {full Ltac name: the twin module that holds its copy}."""
    out = {}
    if not path:
        return out
    with open(path, encoding="utf8") as fh:
        head = None
        for line in fh:
            cols = line.rstrip("\n").split("\t")
            if head is None:
                head = cols
                continue
            row = dict(zip(head, cols))
            out[pkg + "." + row["r1_module"] + "." + row["name"]] = row["twin_module"]
    return out


def load_overrides(path, pkg):
    """Read `overrides.tsv`.

    Returns ({full R1 name: (twin module, twin name, existing)},
             {full R1 name or module that is skipped},
             {full R1 module: (twin module, existing)} for a `<module>.*` line).
    """
    maps, skips, modmaps = {}, set(), {}
    if not path:
        return maps, skips, modmaps
    with open(path, encoding="utf8") as fh:
        for line in fh:
            line = line.split("#")[0].rstrip()
            if not line.strip():
                continue
            cols = [c.strip() for c in line.split("\t") if c.strip()]
            if len(cols) < 2:
                continue
            key, val = cols[0], cols[1]
            if val == "skip":
                skips.add(pkg + "." + key)
                continue
            tm, _, tn = val.partition(".")
            existing = len(cols) > 2 and cols[2] == "1"
            if key.endswith(".*"):
                # Module-wide mapping; declaration names follow the profile.
                modmaps[pkg + "." + key[:-2]] = (tm, existing)
                continue
            maps[pkg + "." + key] = (tm, tn or None, existing)
    return maps, skips, modmaps


# ------------------------------------------------------------------ binders

FORALL_RE = re.compile(r"\b(forall|fun)\b")


def _binder_names_after(text, i):
    """Names bound by the binder list that starts at offset `i` of `text`."""
    depth = 0
    j = i
    while j < len(text):
        c = text[j]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            if depth == 0:
                break
            depth -= 1
        elif depth == 0 and (c == "," or text.startswith("=>", j)):
            break
        j += 1
    try:
        return [n for g in parse_binders(text[i:j]) for n in g[0]]
    except Exception:
        return re.findall(IDENT, text[i:j])


def bound_names(text, proof=False):
    """Over-approximate the names bound locally in `text` (already blanked).

    Over-approximating is the safe side: a name taken for a binder is left alone, so a
    wrong guess shows up as a build error, never as a silent wrong rename.
    """
    out = set()
    for m in FORALL_RE.finditer(text):
        out.update(_binder_names_after(text, m.end()))
    for m in re.finditer(r"[({]\s*(" + IDENT + r"(?:\s+" + IDENT + r")*)\s*:(?!=)",
                         text):
        names = m.group(1).split()
        if names[-1] in TERM_COLON:
            # `exact (foo a b ltac:(lia))` is an application, not a binder group:
            # This colon belongs to ltac syntax, not a type ascription.
            continue
        out.update(names)
    if proof:
        # Each of these runs to the end of its own tactic: `;` ends it as surely as
        # `.` does, or a following constant-name list would become a binder.
        for m in re.finditer(r"\bintros?\b([^.;]*)", text):
            out.update(re.findall(IDENT, m.group(1)))
        for m in re.finditer(r"\bas\s*(\[[^.]*?\]|\([^.]*?\)|" + IDENT + r")",
                             text):
            out.update(re.findall(IDENT, m.group(1)))
        for m in re.finditer(r"\b(?:set|pose|remember|assert|epose|eset)\b"
                             r"\s*\(\s*(" + IDENT + r")", text):
            out.add(m.group(1))
        for m in re.finditer(r"\beqn\s*:\s*(" + IDENT + r")", text):
            out.add(m.group(1))
        for m in re.finditer(r"\bremember\b[^.;]*?\bas\s+(" + IDENT + r")", text):
            out.add(m.group(1))
        # `revert` and `clear` name hypotheses; `generalize`, `specialize`,
        # `exists`, `destruct` and `induction` take TERMS, which may well be the
        # twinned lemmas, so their arguments are references, not binders
        # (for example, `generalize reach_A2_1 reach_A2_0.`).
        for m in re.finditer(r"\b(?:revert|clear)\b([^.;]*)", text):
            out.update(re.findall(IDENT, m.group(1)))
    return out


# ------------------------------------------------------------------ generator

class Gen(object):
    def __init__(self, ix, r1mod, twins, tmod, identity=False, note=None,
                 admit=False):
        self.ix = ix
        self.r1mod = r1mod
        self.profile = ix.profile
        self.vf = ix.files[r1mod]
        self.twins = twins              # full R1 name -> (twin module, twin name)
        self.tmod = tmod
        self.identity = identity
        self.admit = admit
        self.note = note
        self.r1short = r1mod.rsplit(".", 1)[1]
        self.used_twin_modules = set()
        self.copied = set()          # declarations copied under their released name
        self.ltac_home = {}          # full Ltac name -> twin module holding its copy
        self._secstack = None
        self._ltac_here = None
        self.siblings = True         # copy a sibling tactic that calls a copy
        self.sec_bound = [{}]        # names the replayed sections bind, per level
        self.open_sections = []      # the R1 sections open where we are writing
        self.renames = {}               # old written form -> new written form
        self.hand = []                  # (line, why)
        #: section hypotheses renamed because their type names a twinned declaration
        self.hyp_renames = {}

    # -- helpers ------------------------------------------------------

    def is_twinned(self, full):
        return full in self.twins

    def written(self, full):
        """How a twinned declaration is written inside this file."""
        tm, tn = self.twins[full]
        if tm == self.tmod:
            return tn
        self.used_twin_modules.add(tm)
        return tm + "." + tn

    def rewrite(self, start, end, proof_from=None, extra_local=None):
        """Rewrite the source span [start, end) of the R1 file.

        Every reference that names a twinned declaration becomes the twin's written
        form; every unqualified reference to a declaration of this R1 file that is not
        copied gets its module qualifier; a renamed section hypothesis gets its new
        name.  Comments and string literals are never touched: the reference spans come
        from the blanked text.
        """
        src = self.vf.src[start:end]
        bl = self.vf.blank[start:end]
        cut = (proof_from - start) if proof_from is not None else len(bl)
        bound = bound_names(bl[:cut], proof=False) | \
            bound_names(bl[cut:], proof=True)
        local = dict(extra_local or {})
        regions = const_regions(bl)
        # A destructed section variable is a unification hole only after that
        # tactic, never in the already-elaborated statement.
        self.destructed = [(m.start(), m.group(1)) for m in re.finditer(
            r"\b(?:destruct|induction|case)\s+(" + IDENT + r")\b", bl)
            if m.start() >= cut]
        edits = []
        for m in REF_RE.finditer(bl):
            name = m.group(1)
            a, b = m.start(1), m.end(1)
            if name in COMBINATORS:
                after = bl[b:b + 24].lstrip()
                before = bl[:a].rstrip()
                if after.startswith(("[", "(")) or not before or \
                        before[-1] in ".;|{}+-*>":
                    continue          # tactic position: syntax, not a reference
            at_sign = bool(a) and bl[a - 1] == "@"
            bare = at_sign or any(lo <= a < hi for lo, hi in regions)
            new = self.map_ref(name, bound, local, bare=bare, warn=at_sign, at=a)
            if new is not None and new != name:
                edits.append((a, b, new))
        out = []
        pos = 0
        for a, b, new in edits:
            out.append(src[pos:a])
            out.append(new)
            pos = b
        out.append(src[pos:])
        return "".join(out)

    def map_ref(self, name, bound, local, bare=False, warn=False, at=None):
        """The written form a reference `name` takes in the twin, or None."""
        if name in local:
            return local[name]
        if name in self.hyp_renames:
            return self.hyp_renames[name]
        for frame in self.sec_bound:
            if name in frame:
                return None          # the twin's own section binds this name
        head = name.split(".")[0]
        if name in bound or (head in bound and "." not in name):
            return None
        raw = self.ix._resolve_raw(name, self.r1mod)
        if raw is None:
            return None
        it = self.ix.by_full.get(raw)
        # A notation or tactic of this very file: it is copied, under its twin name
        # when it is twinned, under its own name otherwise.
        if it is not None and it.module == self.r1mod and it.kind in ("notation",
                                                                      "ltac"):
            if self.is_twinned(raw):
                return self.written(raw)
            return None
        full = self.ix.alias(raw)
        if self.is_twinned(full):
            return self.written(full)
        if full in self.copied:
            # copied into this file under its released name: leave it bare, the copy
            # is the last definition of that name here.
            return name.split(".")[-1] if "." in name else None
        home = self.ltac_home.get(full)
        if home and home != self.tmod:
            # the tactic's copy lives in another twin file; import that file and
            # leave the call as it is -- the copy wins by being imported last.
            self.used_twin_modules.add(home)
            return None
        if full.startswith(self.r1mod + ".") and "." not in name:
            # a declaration of this R1 file that we do not copy: qualify it, so the
            # twin names the released one and not itself, and give it the arguments
            # the section discharged it over when the reference is inside that
            # section.
            tgt = self.ix.by_full.get(full)
            here = self.open_sections
            around = self.section_stack().get(full, [])
            if (tgt is not None and tgt.kw in PROOF_KW and around
                    and any(self.explicit_binders(s) for s in around)
                    and not any(s in here for s in around)):
                # A lemma of a closed section of this file: R1 writes its discharged
                # arguments itself, and if it does not, no text rule can work them
                # out -- a lemma's discharge follows its proof term.  Say so, rather
                # than let a type error explain it.
                note = ("%s.%s is a lemma of a closed section: check that R1 supplies "
                        "its discharged arguments here, else copy it (--names %s)"
                        % (self.r1short, name, name))
                if note not in [h[1] for h in self.hand]:
                    self.hand.append((0, note))
            if tgt is not None and tgt.kind == "let" and around:
                # a section `Let` is inlined when the section closes: there is no
                # constant `<R1 module>.<name>` to point at.  The twin replays the
                # `Let` itself, so the bare name is the right one.
                return None
            if tgt is not None and around:
                # Seen from the twin, every section of the R1 file is closed, so
                # `<R1 module>.<name>` is the fully discharged constant.  R1's own
                # text already supplies the arguments of the sections that are
                # closed where it writes the reference; the twin adds the rest --
                # the explicit variables of the sections still open there.  So
                # Only the sections still open here need extra arguments.
                args = self.discharge_args(tgt, around,
                                           only=[s for s in around if s in here])
                gone = set(n for off, n in getattr(self, "destructed", ())
                           if at is not None and off < at)
                args = ["_" if a in gone else a for a in args]
                if args and not bare:
                    return "(%s.%s %s)" % (self.r1short, name, " ".join(args))
                if args and bare and warn:
                    # `@name` with the section arguments spelled out is not something
                    # the generator guesses: `@` also asks for the implicit ones.
                    self.hand.append((0, "@%s.%s takes %d section argument(s) and the"
                                         " implicit ones: write the application"
                                      % (self.r1short, name, len(args))))
            return self.r1short + "." + name
        return None

    # -- the file ------------------------------------------------------

    def header(self):
        out = []
        for line in self.vf.src.splitlines():
            if HEADER_COMMENT_RE.match(line) and line.rstrip().endswith("*)"):
                out.append(line)
            elif line.strip() == "":
                continue
            else:
                break
        rel = self.vf.path.split("/proofs/lib/", 1)[-1]
        what = self.note or ("the R-typed declarations restated over the budget "
                             "carrier, with twin modules imported last")
        out.append("(* Modified by Theorem Labs, 2026-11: made from %s: %s. *)"
                   % (rel, what))
        return out

    def _stack_of(self, it, stacks):
        """The sections around `it`, for a declaration or a copied tactic."""
        if it.full in stacks:
            return stacks[it.full]
        out, stack = [], []
        for x in self.vf.items:
            if x is it:
                return list(stack)
            if x.kind == "section_open":
                stack.append(x)
            elif x.kind == "section_close":
                if stack:
                    stack.pop()
        return out

    def ltac_copies_here(self):
        """Tactics of this R1 file whose copy belongs in this twin module.

        The census names the ones the witness's proofs reach; a sibling tactic of the
        same file that calls one of those would, as the released tactic, reach the
        released lemma and fail to fire on a strengthened goal, so it is copied too.
        """
        if self._ltac_here is not None:
            return self._ltac_here
        mine = set(i.full for i in self.vf.items
                   if i.kind == "ltac" and i.name
                   and self.ltac_home.get(i.full) == self.tmod)
        if not self.siblings:
            self._ltac_here = mine
            return mine
        changed = True
        while changed:
            changed = False
            for it in self.vf.items:
                if it.kind != "ltac" or not it.name or it.full in mine:
                    continue
                bl = self.vf.blank[it.start:it.end]
                for m in REF_RE.finditer(bl):
                    raw = self.ix._resolve_raw(m.group(1), self.r1mod)
                    if raw in mine:
                        mine.add(it.full)
                        changed = True
                        break
        self._ltac_here = mine
        return mine

    def sections_with_tactics(self):
        """Sections enclosing a tactic of this file whose copy lives in this twin."""
        need = set()
        stack = []
        for k, it in enumerate(self.vf.items):
            if it.kind == "section_open":
                stack.append(k)
            elif it.kind == "section_close":
                if stack:
                    stack.pop()
            elif it.kind == "ltac" and it.name and \
                    it.full in self.ltac_copies_here():
                need.update(stack)
        return need

    def sections_with_copies(self, copied):
        """Indices of the section_open items that enclose a copied declaration."""
        need = set()
        stack = []
        for k, it in enumerate(self.vf.items):
            if it.kind == "section_open":
                stack.append(k)
            elif it.kind == "section_close":
                if stack:
                    stack.pop()
            elif it.kind == "decl" and it.full in copied:
                need.update(stack)
        return need

    def section_stack(self):
        """{full name of a declaration: the section_open items around it}."""
        if self._secstack is None:
            out, stack = {}, []
            for it in self.vf.items:
                if it.kind == "section_open":
                    stack.append(it)
                elif it.kind == "section_close":
                    if stack:
                        stack.pop()
                elif it.kind in ("decl", "let") and it.name:
                    out[it.full] = list(stack)
                    for c in (it.constructors or []):
                        # a projection of a section `Record` takes the section's
                        # arguments too.
                        out[".".join([it.module] + list(it.modules or [])
                                     + [c])] = list(stack)
            self._secstack = out
        return self._secstack

    def explicit_binders(self, sec):
        """Does section `sec` bind an explicit `Variable`/`Hypothesis`/`Let`?

        A section that binds only implicit `Context`s costs a reference nothing: the
        twin re-binds the same contexts, so `<R1 module>.<name>` means the same term.
        """
        seen = False
        depth = 0
        for it in self.vf.items:
            if it.start < sec.start:
                continue
            if it.kind == "section_open":
                depth += 1
                continue
            if it.kind == "section_close":
                depth -= 1
                if depth <= 0:
                    break
                continue
            if depth != 1:
                continue
            if it.kind in ("variable", "hypothesis", "let"):
                seen = True
            if it.kind == "context" and it.args:
                if any(g[2] in ("(", "") for g in it.args):
                    seen = True
        return seen

    def section_items(self, secs):
        """The commands of the sections `secs` themselves: [(its section, command)].

        Only this chain's section levels are included; sibling sections bind
        variables outside these declarations' scope.
        """
        if not secs:
            return []
        want = list(secs)
        out = []
        stack = []
        for it in self.vf.items:
            if it.kind == "section_open":
                stack.append(it)
                continue
            if it.kind == "section_close":
                if stack:
                    stack.pop()
                continue
            if stack and stack == want[:len(stack)]:
                out.append((stack[-1], it))
        return out

    def discharge_args(self, it, secs, only=None):
        """The arguments the discharged form of `it` takes, in order.

        Rocq discharges a transparent constant over exactly the section variables its
        type and body mention, transitively through the other section declarations it
        mentions.  A section `Let` is discharged as a let-in, not as an argument, so
        it is not in the list, but what it mentions is; an implicit `Context {..}`
        binder is not in the list either, because the twin re-binds the same context
        and Rocq fills it in. Definitions are re-pointed at the released constant;
        lemmas are copied because proof-term discharge is not predictable here.
        """
        pairs = [(sec, x) for sec, x in self.section_items(secs)
                 if x.start < it.start]
        items = [x for _sec, x in pairs]
        body = self.vf.blank[it.start:it.end]
        # A name the body binds itself (`fun p => ...`) is not the section variable
        # of the same name, so it must not pull that variable into the argument list
        shadowed = bound_names(body, proof=False)
        used = set(m.group(1) for m in REF_RE.finditer(body)) - shadowed
        changed = True
        while changed:
            changed = False
            for x in items:
                if x.kind in ("variable", "context", "hypothesis") and x.args:
                    # Rocq discharges per variable, not per binder group: a group
                    # `Variables (Lc Ac mc mdc : T)` brings in only the ones the body
                    # needs, and their types.
                    for g in x.args:
                        if not any(n in used for n in g[0]):
                            continue
                        for m in REF_RE.finditer(blank_text(g[1])):
                            if m.group(1) not in used:
                                used.add(m.group(1))
                                changed = True
                    continue
                names = list(x.names or [])
                if x.name:
                    names.append(x.name)
                if not any(n in used for n in names):
                    continue
                for m in REF_RE.finditer(self.vf.blank[x.start:x.end]):
                    if m.group(1) not in used:
                        used.add(m.group(1))
                        changed = True
        args = []
        for sec, x in pairs:
            if x.kind not in ("variable", "context", "hypothesis"):
                continue
            if only is not None and sec not in only:
                continue
            for g in (x.args or []):
                if g[2] not in ("(", ""):
                    continue            # implicit: Rocq fills it in
                for n in g[0]:
                    if n in used:
                        args.append(n)
        return args

    def same_section_closure(self, copied):
        """Declarations that have to be copied along with `copied`.

        A reference from a copied proof to a declaration of a section that is STILL
        OPEN there means the undischarged form; `<R1 module>.<name>` outside the
        section means the discharged one, which takes the section's variables as
        arguments.  Copying the declaration as well keeps the two the same, and it
        costs nothing: such a declaration is not R-typed, so its released proof
        still proves it.  A section that binds only implicit `Context`s is left
        alone.
        """
        stacks = self.section_stack()
        extra = set()
        work = list(copied)
        tact = [i for i in self.vf.items
                if i.kind == "ltac" and i.name and i.full in self.ltac_copies_here()]
        seen = set()
        while work or tact:
            if tact:
                it = tact.pop()
                name = it.full
            else:
                name = work.pop()
                it = self.ix.by_full.get(name)
            if name in seen:
                continue
            seen.add(name)
            if it is None or it.module != self.r1mod:
                continue
            here = self._stack_of(it, stacks)
            bl = self.vf.blank[it.start:it.end]
            for m in REF_RE.finditer(bl):
                raw = self.ix._resolve_raw(m.group(1), self.r1mod)
                if raw is None:
                    continue
                full = self.ix.alias(raw)
                if full in copied or full in extra or self.is_twinned(full):
                    continue
                tgt = self.ix.by_full.get(full)
                if tgt is None or tgt.module != self.r1mod:
                    continue
                if tgt.kind not in ("decl", "let"):
                    continue
                if tgt.kw not in PROOF_KW:
                    continue          # a definition is re-pointed, not copied
                around = stacks.get(full, [])
                if not around:
                    continue
                # Copy when the reference and the lemma SHARE a section that binds
                # explicit variables: whatever that section will discharge into the
                # lemma, R1's text does not write, and a lemma's discharge follows
                # its proof term, which no text pass can predict.  A shared section
                # with only implicit Contexts needs nothing.
                shared = [s for s in around if s in here]
                if not shared:
                    continue          # nothing in common: R1 writes the application
                if not any(self.explicit_binders(s) for s in shared):
                    continue
                extra.add(full)
                work.append(full)
        return extra

    def generate(self, names):
        vf = self.vf
        decls = [i for i in vf.items
                 if i.kind in ("decl", "let") and i.name]
        copied = set()
        for it in decls:
            if it.name in names or it.full in names:
                copied.add(it.full)
        cons = set()
        for d in decls:
            cons.update(d.constructors or [])
        tactics = set(i.name for i in vf.items
                      if i.kind in ("ltac", "notation") and i.name)
        # a constructor comes with its inductive, and a tactic or notation is
        # written by the section replay, never as a twinned declaration
        names = [n for n in names
                 if n.rsplit(".", 1)[-1] not in cons
                 and n.rsplit(".", 1)[-1] not in tactics]
        missing = [n for n in names
                   if not any(d.name == n or d.full == n for d in decls)]
        if missing:
            # `overrides.tsv` is shared: a line may name a declaration of another
            # branch.  Say so and write the rest, rather than refuse the file.
            sys.stderr.write("warning: not in %s, left out: %s\n"
                             % (self.r1short, ", ".join(sorted(missing))))
            names = [n for n in names if n not in missing]
        if not names and not self.ltac_copies_here():
            raise SystemExit("nothing to twin in %s" % self.r1mod)
        self.twinned = set(copied)
        extra = self.same_section_closure(copied)
        self.copied = extra
        copied = copied | extra
        self.tactics_only = not copied
        need_sec = self.sections_with_copies(copied)
        if self.tactics_only:
            # A twin module that holds nothing but tactic copies:
            # replay the sections those tactics live in, and nothing else.
            need_sec = self.sections_with_tactics()

        body = []
        stack = []
        emitted_sec = []
        for k, it in enumerate(vf.items):
            if it.kind == "require":
                continue
            if it.kind == "section_open":
                stack.append(k)
                self.sec_bound.append({})
                self.open_sections.append(it)
                if k in need_sec:
                    body.append(it.text.strip())
                    emitted_sec.append(k)
                continue
            if it.kind == "section_close":
                op = stack.pop() if stack else None
                if len(self.sec_bound) > 1:
                    self.sec_bound.pop()
                if self.open_sections:
                    self.open_sections.pop()
                if emitted_sec and emitted_sec[-1] == op:
                    emitted_sec.pop()
                    body.append(it.text.strip())
                continue
            if it.kind == "module_open" or it.kind == "module_close":
                body.append(it.text.strip())
                continue
            # a command of a section that is not replayed is dropped with it
            inside = bool(stack) and all(s in need_sec for s in stack)
            at_top = not stack
            if it.kind == "decl":
                if it.full in copied:
                    body.append(self.emit_decl(it))
                continue
            if not (inside or at_top):
                continue
            emitted = self.emit_aux(it, copied)
            if emitted:
                body.append(emitted)

        head = self.header()
        head.extend(self.require_block())
        return "\n".join(head + [""] + [b for b in body if b]) + "\n"

    def require_block(self):
        out = []
        for it in self.vf.items:
            if it.kind == "require":
                out.append(it.text.strip())
        pre, short = self.r1mod.rsplit(".", 1)
        out.append("From %s Require Import %s." % (pre, short))
        if self.used_twin_modules:
            out.append("From %s.%s Require Import %s."
                       % (self.ix.pkg, self.ix.twin_dir, " ".join(sorted(self.used_twin_modules))))
        return out

    def emit_aux(self, it, copied):
        """A non-declaration command of the R1 file, if the twin needs it."""
        if it.kind == "require":
            return None
        if it.kind == "arguments":
            tgt = self.ix._resolve_raw(it.name, self.r1mod)
            if tgt is None or not self.is_twinned(self.ix.alias(tgt)):
                return None
            return self.rewrite(it.start, it.end).strip()
        if it.kind in ("notation", "ltac"):
            importable = not (it.is_local or it.sections)
            redefines = "::=" in (it.text or "")
            touches = self.touches_twin(it)
            if redefines:
                # `Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::=
                # constr:(false).` and its restore change how `lia` runs; they are
                # settings of this file, so they are carried over in place.
                return it.text.strip()
            if it.kind == "ltac" and it.full in self.ltac_copies_here():
                pass                 # this twin module is the home of its copy
            elif importable and not touches:
                return None          # it comes in with the `Require Import`
            # Keep the notation/tactic's defining name; rewrite only its body.
            k = _find_top(self.vf.blank[it.start:it.end], ":=")
            if it.name and k > 0:
                keep = {it.name: it.name}
                if it.kind == "ltac":
                    # a tactic's formal parameters bind over its whole body, and
                    # qualifying them would not be valid tactic syntax.
                    head = self.vf.blank[it.start:it.start + k]
                    head = head.split(it.name, 1)[-1]
                    for prm in re.findall(IDENT, head):
                        keep[prm] = prm
                lhs = self.rewrite(it.start, it.start + k, extra_local=keep)
                # In the body, the notation's own name means the IMPORTED
                # declaration it abbreviates, not the notation itself.
                body = {}
                outer = self.ix.scope(self.r1mod).get(it.name)
                if outer is not None:
                    outer = self.ix.alias(outer)
                    body[it.name] = (self.written(outer)
                                     if self.is_twinned(outer) else it.name)
                if it.kind == "ltac":
                    body.update(keep)
                rhs = self.rewrite(it.start + k, it.end, extra_local=body)
                text = (lhs + rhs).strip()
                return self.mark_grants(text, it.line) if it.kind == "ltac" else text
            text = self.rewrite(it.start, it.end).strip()
            return self.mark_grants(text, it.line) if it.kind == "ltac" else text
        if it.kind in ("variable", "context", "hypothesis", "let"):
            return self.emit_binder(it)
        if it.kind in ("hint", "other"):
            return it.text.strip()
        return None

    def touches_twin(self, it):
        bl = self.vf.blank[it.start:it.end]
        for m in REF_RE.finditer(bl):
            raw = self.ix._resolve_raw(m.group(1), self.r1mod)
            if raw is not None and self.is_twinned(self.ix.alias(raw)):
                return True
        return False

    def emit_binder(self, it):
        """A `Variable`/`Context`/`Hypothesis`/`Let` of a replayed section.

        A hypothesis whose type names a twinned declaration is retyped over the twin
        and renamed, so that the twin's statement after discharge is the twin's and the
        two can never be confused.  The binder's own names are left alone: a section
        `Let x := ...` declares `x`, and qualifying it would make `Let M.x := ...`.
        """
        keep = dict((n, n) for n in (it.names or []))
        if it.name:
            keep[it.name] = it.name
        text = self.rewrite(it.start, it.end, extra_local=keep)
        self.sec_bound[-1].update(keep)
        if it.kind == "hypothesis" and self.touches_twin(it):
            for nm in (it.names or []):
                new = self.profile.twin_name(nm)
                self.hyp_renames[nm] = new
                text = re.sub(r"(?<![A-Za-z0-9_'.])" + re.escape(nm) +
                              r"(?![A-Za-z0-9_'])", new, text, count=1)
        return text.strip()

    def own_params(self, it):
        """Names the declaration's own parameter list binds, for its whole text.

        `Lemma wrange_cases E1 rs hv x :` binds `E1`, even where the file also has a
        section definition called `E1`.
        """
        bl = self.vf.blank[it.start:it.start + len(it.stmt or "")]
        m = re.search(r"(?<![A-Za-z0-9_'])" + re.escape(it.name or "") +
                      r"(?![A-Za-z0-9_'])", bl)
        if not m:
            return {}
        rest = bl[m.end():]
        k = _find_top(rest, ":=")
        j = _find_top(rest, ":")
        cut = min([x for x in (k, j) if x >= 0] or [len(rest)])
        out = {}
        for g in parse_binders(rest[:cut]):
            for n in g[0]:
                out[n] = n
        for n in re.findall(r"(?<![A-Za-z0-9_'])(" + IDENT + r")(?![A-Za-z0-9_'])",
                            re.sub(r"[({\[][^)}\]]*[)}\]]", " ", rest[:cut])):
            out[n] = n
        return out

    def emit_decl(self, it):
        """One copied declaration: statement, proof, renames and HAND markers."""
        proof_at = it.start + len(it.stmt)
        if self.admit and it.proof:
            # statement check only: the proof is left out, so `About` can be asked
            # before a person has repaired the script.
            text = self.rewrite(it.start, proof_at,
                                extra_local=self.own_params(it))
            new = self.twins[it.full][1] if self.is_twinned(it.full) else it.name
            text = re.sub(r"(?<![A-Za-z0-9_'.])" + re.escape(it.name) +
                          r"(?![A-Za-z0-9_'])", new, text, count=1)
            using = "Proof."
            if it.proof_using:
                names = " ".join(self.hyp_renames.get(w, w)
                                 for w in it.proof_using.split())
                using = "Proof using %s." % names
            return text.rstrip() + "\n" + using + "\nAdmitted."
        text = self.rewrite(it.start, it.end, proof_from=proof_at,
                            extra_local=self.own_params(it))
        new = self.twins[it.full][1] if self.is_twinned(it.full) else it.name
        text = re.sub(r"(?<![A-Za-z0-9_'.])" + re.escape(it.name) +
                      r"(?![A-Za-z0-9_'])", new, text, count=1)
        self.renames[it.name] = new
        return self.mark_grants(text, it.line, (it.stmt or "").count("\n") + 1)

    def mark_grants(self, text, line_number, statement_lines=0):
        out = []
        for off, line in enumerate(text.rstrip().split("\n")):
            bl = blank_text(line)
            proof = off >= statement_lines or re.search(r"\bProof\b", bl)
            if proof and (self.profile.node_re.search(bl) or
                          (ECONSTRUCTOR_RE.search(bl) and self.profile.twin_relation in bl)):
                line = line.rstrip() + "   (* HAND: grant *)"
                self.hand.append((line_number + off, line.strip()[:60]))
            out.append(line)
        return "\n".join(out)


