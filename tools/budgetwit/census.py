#!/usr/bin/env python3
"""R-typed declaration census along explicitly discovered usage-path roots.

Statements, discharged section hypotheses, proof references and called tactic
bodies determine the dependency walk. Rules and limits are in README.md.
"""
from collections import Counter, defaultdict

from .rocqparse import REF_RE
from .gen_v import load_overrides


class Census(object):
    def __init__(self, ix, roots, unit, overrides=None):
        self.ix = ix
        self.unit = unit
        self.profile = ix.profile
        self.omaps, oskips, self.omods = load_overrides(overrides, ix.pkg)
        self.omaps = {**self.profile.overrides(ix), **self.omaps}
        skip = list(self.profile.skip) + list(oskips)
        full = unit.qualify
        self.seeds = set(self.profile.seeds(ix))
        self.roots = [full(r) for r in roots]
        missing = [r for r in self.roots if r not in ix.by_full]
        if missing:
            raise ValueError("root not found: " + ", ".join(missing))
        self.skip_exact = set(full(s) for s in skip if not s.endswith(".*"))
        self.skip_mod = set(full(s[:-2]) for s in skip if s.endswith(".*"))
        self._refs = {}
        self._rtyped = None
        self._universe = None
        self.ndecl = 0
        self._ltac_refs = {}
        self.twins = {}            # full name -> Item
        self.reason = {}           # full name -> the twin that reached it
        self.ltacs = {}            # full Ltac name -> set of twins its body names
        self.unresolved = Counter()

    # -- references ----------------------------------------------------

    def refs_in(self, mod, text_blank):
        out = []
        for m in REF_RE.finditer(text_blank):
            nm = m.group(1)
            tgt = self.ix.resolve(nm, mod)
            if tgt is None:
                if "." in nm:
                    self.unresolved[nm] += 1
                continue
            out.append(tgt)
        return out

    def decl_refs(self, it, part):
        """`part` is 'stmt' (type and body) or 'proof'."""
        key = (it.full, part)
        if key in self._refs:
            return self._refs[key]
        vf = self.ix.files[it.module]
        # a section `Let` is one sentence: all of it is its statement and body
        slen = len(it.stmt) if it.stmt else (it.end - it.start)
        if part == "stmt":
            bl = vf.blank[it.start:it.start + slen]
        else:
            bl = vf.blank[it.start + slen:it.end]
        res = self.refs_in(it.module, bl)
        self._refs[key] = res
        return res

    def sect_refs(self, it):
        """What the section binders that are discharged INTO `it` name.

        A section `Hypothesis H : cannot_open_hyp.` becomes part of the statement
        when the section closes, so a definition that only ever appears as the type
        of a section hypothesis is still named by the twin and still has to be
        twinned. Only the binders Rocq actually discharges
        count: the ones the `Proof using` clause lists and the ones the statement
        names, plus what those binders' own types name -- a section whose hypothesis
        is unused by this declaration changes nothing about its statement.
        """
        key = (it.full, "sect")
        if key in self._refs:
            return self._refs[key]
        vf = self.ix.files[it.module]
        stack = []
        for x in vf.items:
            if x.start >= it.start:
                break
            if x.kind == "section_open":
                stack.append([])
            elif x.kind == "section_close":
                if stack:
                    stack.pop()
            elif x.kind in ("variable", "context", "hypothesis", "let") and stack:
                stack[-1].append(x)
        binders = [x for lvl in stack for x in lvl]
        slen = len(it.stmt) if it.stmt else (it.end - it.start)
        stmt = vf.blank[it.start:it.start + slen]
        wanted = set((it.proof_using or "").split())
        for m in REF_RE.finditer(stmt):
            wanted.add(m.group(1))
        if not it.proof_using:
            # Without a `Proof using` clause Rocq discharges whatever the script
            # uses, so every name the script writes is a candidate.
            for m in REF_RE.finditer(vf.blank[it.start + slen:it.end]):
                wanted.add(m.group(1))
        taken = []
        changed = True
        while changed:
            changed = False
            for x in binders:
                if x in taken:
                    continue
                if any(n in wanted for n in (x.names or [])) or \
                        (x.kind == "context" and not x.names):
                    taken.append(x)
                    for m in REF_RE.finditer(vf.blank[x.start:x.end]):
                        if m.group(1) not in wanted:
                            wanted.add(m.group(1))
                            changed = True
        out = []
        for x in taken:
            out.extend(self.refs_in(it.module, vf.blank[x.start:x.end]))
        self._refs[key] = out
        return out

    def ltac_body_refs(self, it, seen=None):
        """What an `Ltac` body names, following calls of other tactics."""
        if it.full in self._ltac_refs:
            return self._ltac_refs[it.full]
        seen = seen or set()
        if it.full in seen:
            return []
        seen.add(it.full)
        vf = self.ix.files[it.module]
        bl = vf.blank[it.start:it.end]
        out = []
        for tgt in self.refs_in(it.module, bl):
            tit = self.ix.by_full.get(tgt)
            if tit is not None and tit.kind == "ltac" and tgt != it.full:
                out.append(tgt)
                out.extend(self.ltac_body_refs(tit, seen))
            else:
                out.append(tgt)
        self._ltac_refs[it.full] = out
        return out

    # -- R-typed -------------------------------------------------------

    def skipped(self, name):
        if name in self.skip_exact:
            return True
        mod = name.rsplit(".", 1)[0]
        return mod in self.skip_mod

    def excluded(self, name):
        tail = name[len(self.ix.pkg) + 1:]
        return any(tail.startswith(e) or ("." + e) in ("." + tail)
                   for e in self.unit.excluded)

    def universe(self):
        """The modules a declaration reachable from a root can live in.

        A reference of a module names a module that module requires, so the roots'
        require closure holds every declaration the route can reach.
        """
        if self._universe is not None:
            return self._universe
        seen = set()
        work = [r.rsplit(".", 1)[0] for r in self.roots]
        while work:
            m = work.pop()
            if m in seen or m not in self.ix.files:
                continue
            seen.add(m)
            vf = self.ix.files[m]
            for _kind, name in vf.requires:
                f = self.ix._full_module(name, m)
                if f and f not in seen:
                    work.append(f)
        self._universe = seen
        return seen

    def build_rtyped(self):
        """Propagate R-typedness from the seeds, in one pass over the universe.

        `X` is R-typed when its statement (for a theorem) or its statement and body
        (for a definition) names an R-typed declaration, so this is reachability
        backwards along the statement references, from the four seeds.  Doing it as a
        graph, not as a recursion, is what makes the census finish: the recursive form
        re-reads the same statements for every path that reaches them.
        """
        back = defaultdict(list)       # target -> [declarations naming it]
        univ = self.universe()
        ndecl = 0
        for mod in univ:
            vf = self.ix.files.get(mod)
            if vf is None:
                continue
            for it in vf.items:
                if it.kind not in ("decl", "let") or not it.name:
                    continue
                name = it.full
                if self.skipped(name) or self.excluded(name):
                    continue
                ndecl += 1
                for tgt in self.decl_refs(it, "stmt") + self.sect_refs(it):
                    if tgt != name:
                        back[tgt].append(name)
        self.ndecl = ndecl
        got = set()
        work = [s for s in self.seeds]
        while work:
            cur = work.pop()
            for src in back.get(cur, ()):
                if src in got:
                    continue
                got.add(src)
                work.append(src)
        for s in self.seeds:
            got.add(s)
        self._rtyped = got
        return got

    def rtyped(self, name):
        if self._rtyped is None:
            self.build_rtyped()
        if name in self._rtyped:
            return True
        it = self.ix.by_full.get(name)
        if it is not None and it.kind == "notation":
            tgt = self.ix.alias(name)
            return tgt != name and tgt in self._rtyped
        return False

    # -- the route -----------------------------------------------------

    def walk(self):
        work = [(name, "root") for name in self.roots]
        while True:
            while work:
                name, why = work.pop()
                if name in self.twins:
                    continue
                it = self.ix.by_full.get(name)
                if it is None or it.kind not in ("decl", "let"):
                    continue
                if self.skipped(name) or self.excluded(name):
                    continue
                self.twins[name] = it
                self.reason[name] = why
                targets = (self.decl_refs(it, "stmt") + self.sect_refs(it)
                           + self.decl_refs(it, "proof"))
                extra = []
                for tgt in targets:
                    tit = self.ix.by_full.get(tgt)
                    if tit is not None and tit.kind == "ltac":
                        extra.extend(self.ltac_body_refs(tit))
                        self.ltacs.setdefault(tgt, set())
                for tgt in targets + extra:
                    tit = self.ix.by_full.get(tgt)
                    if (tgt not in self.twins and tit is not None
                            and tit.kind in ("decl", "let") and self.rtyped(tgt)
                            and not self.skipped(tgt) and not self.excluded(tgt)):
                        work.append((tgt, name))

            before = set(self.ltacs)
            for it in self.auxiliary_tactics():
                self.ltacs.setdefault(it.full, set())
                for tgt in self.ltac_body_refs(it):
                    tit = self.ix.by_full.get(tgt)
                    if tit is None or self.skipped(tgt) or self.excluded(tgt):
                        continue
                    if tit.kind == "ltac":
                        self.ltacs.setdefault(tgt, set())
                    elif (tit.kind in ("decl", "let") and self.rtyped(tgt)
                          and tgt not in self.twins):
                        work.append((tgt, it.full))
            if not work and before == set(self.ltacs):
                break

        for name in self.omaps:
            if name in self.twins or self.skipped(name):
                continue
            it = self.ix.by_full.get(name)
            if it is not None and it.kind in ("decl", "let"):
                self.twins[name] = it
                self.reason[name] = "overrides.tsv"
        for name in list(self.ltacs):
            it = self.ix.by_full.get(name)
            if it is None:
                continue
            names = set(self.ltac_body_refs(it)).intersection(self.twins)
            vf = self.ix.files[it.module]
            if not names and not self.profile.tactic_words.search(vf.blank[it.start:it.end]):
                del self.ltacs[name]
            else:
                self.ltacs[name] = names

    def auxiliary_tactics(self):
        """Tactic copies emitted by Gen must have their R-typed dependencies too.

        Gen replays a sibling tactic when its body mentions a twin, even if the
        entry proofs never call that sibling. Declaration and tactic closure
        therefore need a joint fixed point, not a final tactic-only pass.
        """
        active = set(self.twins) | set(self.omaps)
        modules = set()
        for name in set(self.twins) | set(self.ltacs):
            it = self.ix.by_full[name]
            override = self.omaps.get(name)
            existing = override[2] if override else self.omods.get(it.module, (None, False))[1]
            if existing:
                continue
            if it.kind == "ltac":
                vf = self.ix.files[it.module]
                if (not active.intersection(self.ltac_body_refs(it))
                        and not self.profile.tactic_words.search(vf.blank[it.start:it.end])):
                    continue
            modules.add(it.module)
        for module in sorted(modules):
            for it in self.ix.files[module].items:
                if it.kind != "ltac" or not it.name:
                    continue
                references = self.ltac_body_refs(it)
                if (it.full in self.ltacs or active.intersection(references)
                        or set(self.ltacs).intersection(references)):
                    yield it

    # -- the table -----------------------------------------------------

    def rows(self):
        out = []
        for name, it in sorted(self.twins.items()):
            mod = it.module[len(self.ix.pkg) + 1:]
            vf = self.ix.files[it.module]
            slen = len(it.stmt) if it.stmt else (it.end - it.start)
            proof = vf.blank[it.start + slen:it.end]
            sites = [ln for ln in proof.split("\n") if self.profile.node_re.search(ln)]
            short = name.rsplit(".", 1)[-1]
            tn, tm, ex = self.profile.twin_name(short), self.profile.twin_module(it.module), False
            ov = self.omaps.get(name)
            if ov is not None:
                tm, tn2, ex = ov
                tn = tn2 or tn
            elif it.module in self.omods:
                tm, ex = self.omods[it.module]
            refs = []
            for tgt in (self.decl_refs(it, "stmt") + self.sect_refs(it)
                        + self.decl_refs(it, "proof")):
                if tgt in self.twins and tgt != name:
                    refs.append(tgt[len(self.ix.pkg) + 1:])
            lt = []
            for tgt in set(self.decl_refs(it, "proof")):
                if tgt in self.ltacs:
                    lt.append(tgt[len(self.ix.pkg) + 1:])
            out.append(dict(r1_module=mod, name=short, kw=it.kw.lower(),
                            start=it.line, end=it.endline,
                            lines=it.endline - it.line + 1,
                            twin_module=tm, twin_name=tn,
                            existing=1 if ex else 0,
                            nodes=len(sites),
                            node_sites=";".join(s.strip()[:40] for s in sites[:3]),
                            ltacs=";".join(sorted(set(lt))),
                            refs=";".join(sorted(set(refs))[:12])))
        return out


COLS = ["r1_module", "name", "kw", "start", "end", "lines", "twin_module",
        "twin_name", "existing", "nodes", "node_sites", "ltacs", "refs"]


