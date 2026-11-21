#!/usr/bin/env python3
"""Text parser and name resolver for one released Rocq proof library.

Reads `.v` files as text -- no Rocq runs -- and gives the census and the generator:

  * the sentences of a file, with the comments and the string literals blanked out
    (positions are kept, so every span still indexes into the original text);
  * the commands that matter: `From ... Require [Import|Export]`, `Import`/`Export`,
    `Section`/`Module`/`End`, `Variable(s)`/`Context`/`Hypothes(i|e)s`/`Let`,
    `Notation`/`Local Notation`/`Tactic Notation`, `Ltac`/`Ltac2`, `Arguments`, `Hint`,
    and the declarations (`Lemma`, `Theorem`, `Definition`, `Fixpoint`, `Inductive`,
    `Record`, `Class`, `Instance`, `Example`, `Corollary`, `Fact`, `Remark`, ...)
    with their proof up to `Qed.` / `Defined.` / `Admitted.`;
  * an index of every declaration, inductive constructor and record field of the tree,
    and a resolver from a name as it is written to the declaration it names.

The resolver follows Rocq's rule that a short name resolves to the LAST import that
brings it, so a file that imports a `BudgetWit` twin module after the released module
gets the twin.  Limits are in README.md.
"""
import os
import re
from collections import defaultdict


IDENT = r"[A-Za-z_][A-Za-z0-9_']*"
QID = r"%s(?:\.%s)*" % (IDENT, IDENT)
IDENT_RE = re.compile(IDENT)
QID_RE = re.compile(QID)
#: Every identifier-or-qualified-identifier occurrence, with its span.
REF_RE = re.compile(r"(?<![A-Za-z0-9_'.@])@?(" + QID + r")")

TERMINATORS = ("Qed", "Defined", "Admitted", "Abort", "Save")

#: Keywords that always carry a proof script.
PROOF_KW = ("Lemma", "Theorem", "Corollary", "Fact", "Remark", "Proposition",
            "Property", "Goal")
#: Keywords that may be given by a term (`:= ...`) or by a proof script.
TERM_KW = ("Definition", "Fixpoint", "CoFixpoint", "Example", "Instance", "Let",
           "SubClass")
#: Keywords that introduce constructors or fields.
TYPE_KW = ("Inductive", "CoInductive", "Variant", "Record", "Structure", "Class")

DECL_KW = PROOF_KW + TERM_KW + TYPE_KW

#: Prefixes a declaration may carry before its keyword.
MODIFIERS = ("Local", "Global", "Program", "Polymorphic", "Monomorphic", "Private",
             "#[export]", "#[global]", "#[local]", "#[universes(polymorphic)]")

ATTR_RE = re.compile(r"^\s*#\[[^\]]*\]\s*")


# --------------------------------------------------------------- lexing

def blank_text(src):
    """Return `src` with comments and string literals blanked (spaces), same length.

    Rocq comments `(* ... *)` nest; a string literal inside a comment does not open a
    string, and `"` inside a string is escaped by doubling.  Newlines are kept so that
    line numbers of the blanked text are the line numbers of the source.
    """
    out = list(src)
    i, n = 0, len(src)
    depth = 0
    in_str = False
    while i < n:
        c = src[i]
        if in_str:
            if c == '"':
                if i + 1 < n and src[i + 1] == '"':
                    out[i] = out[i + 1] = ' '
                    i += 2
                    continue
                in_str = False
                out[i] = ' '
                i += 1
                continue
            if c != '\n':
                out[i] = ' '
            i += 1
            continue
        if depth:
            if c == '(' and i + 1 < n and src[i + 1] == '*':
                depth += 1
                out[i] = out[i + 1] = ' '
                i += 2
                continue
            if c == '*' and i + 1 < n and src[i + 1] == ')':
                depth -= 1
                out[i] = out[i + 1] = ' '
                i += 2
                continue
            if c == '"':
                # a string inside a comment: Rocq still reads it as a string, so an
                # unbalanced `*)` in it does not close the comment.  Blank it through.
                j = i + 1
                while j < n:
                    if src[j] == '"':
                        if j + 1 < n and src[j + 1] == '"':
                            j += 2
                            continue
                        break
                    j += 1
                for k in range(i, min(j + 1, n)):
                    if src[k] != '\n':
                        out[k] = ' '
                i = j + 1
                continue
            if c != '\n':
                out[i] = ' '
            i += 1
            continue
        if c == '(' and i + 1 < n and src[i + 1] == '*':
            depth = 1
            out[i] = out[i + 1] = ' '
            i += 2
            continue
        if c == '"':
            in_str = True
            out[i] = ' '
            i += 1
            continue
        i += 1
    return "".join(out)


def split_sentences(blank):
    """Split blanked Rocq text into sentences; return [(start, end)] offsets.

    A sentence ends at a `.` followed by whitespace or end of file.  `..` (the recursive
    notation marker) and the `.` of a qualified name never end one, and `.(` (record
    projection) does not either.
    """
    res = []
    n = len(blank)
    start = 0
    while start < n and blank[start] in " \t\r\n":
        start += 1          # the file's head comment is not part of the first command
    i = start
    while i < n:
        c = blank[i]
        if c == '.':
            if i + 1 < n and blank[i + 1] == '.':
                i += 2
                continue
            if i and blank[i - 1] == '.':
                i += 1
                continue
            if i + 1 >= n or blank[i + 1] in " \t\r\n":
                res.append((start, i + 1))
                i += 1
                while i < n and blank[i] in " \t\r\n":
                    i += 1
                start = i
                continue
        i += 1
    if blank[start:].strip():
        res.append((start, n))
    return res


# --------------------------------------------------------------- the model

class Item(object):
    """One parsed top-level command."""

    __slots__ = ("kind", "name", "names", "kw", "start", "end", "line", "endline",
                 "text", "module", "sections", "modules", "stmt", "proof",
                 "constructors", "is_local", "attrs", "proof_using", "notation_body",
                 "args")

    def __init__(self, **kw):
        for s in self.__slots__:
            setattr(self, s, kw.get(s))

    @property
    def full(self):
        if self.name is None:
            return None
        pre = ".".join([self.module] + list(self.modules or []))
        return pre + "." + self.name

    def __repr__(self):
        return "<%s %s @%s>" % (self.kind, self.name, self.line)


class VFile(object):
    def __init__(self, path, module, src):
        self.path = path
        self.module = module
        self.src = src
        self.blank = blank_text(src)
        self.items = []
        #: (kind, module) in textual order; kind in {'require','import','export'}
        self.requires = []
        self._lines = None

    def lineno(self, off):
        if self._lines is None:
            self._lines = [0]
            for m in re.finditer("\n", self.src):
                self._lines.append(m.end())
        lo, hi = 0, len(self._lines) - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if self._lines[mid] <= off:
                lo = mid
            else:
                hi = mid - 1
        return lo + 1

    def decls(self):
        return [i for i in self.items if i.kind == "decl"]


REQ_RE = re.compile(r"^\s*(?:From\s+(" + QID + r")\s+)?Require\s+"
                    r"(Import|Export)?\s*(.*)$", re.S)
IMPORT_RE = re.compile(r"^\s*(Import|Export)\s+(.*)$", re.S)
SECTION_RE = re.compile(r"^\s*Section\s+(" + IDENT + r")\s*$")
MODULE_RE = re.compile(r"^\s*Module\s+(?:Type\s+)?(?:Import\s+|Export\s+)?("
                       + IDENT + r")\b(.*)$", re.S)
END_RE = re.compile(r"^\s*End\s+(" + IDENT + r")\s*$")
BINDER_RE = re.compile(r"^\s*(Variables?|Context|Hypothes[ie]s|Let|Universe|"
                       r"Implicit\s+Types?)\b", re.S)
NOTATION_RE = re.compile(r"^\s*(?:(?:Local|Global|Export)\s+|#\[[^\]]*\]\s*)*"
                         r"(Reserved\s+Notation|Tactic\s+Notation|Notation|"
                         r"Abbreviation|Infix|Declare\s+Scope)\b", re.S)
LTAC_RE = re.compile(r"^\s*(?:(?:Local|Global)\s+|#\[[^\]]*\]\s*)*"
                     r"Ltac2?\b\s*(?:Notation\s+)?(" + QID + r")?", re.S)
ARGS_RE = re.compile(r"^\s*(?:(?:Local|Global)\s+|#\[[^\]]*\]\s*)*Arguments\s+("
                     + QID + r")", re.S)
HINT_RE = re.compile(r"^\s*(?:(?:Local|Global|Export)\s+|#\[[^\]]*\]\s*)*"
                     r"(?:Hint|Existing\s+Instance|Existing\s+Class)\b", re.S)
PROOF_USING_RE = re.compile(r"^\s*Proof\s+using\b([^.]*)\.", re.S)


def _strip_mods(s):
    """Drop attributes and `Local`/`Global`/... from the head of a sentence."""
    out = s
    while True:
        m = ATTR_RE.match(out)
        if m:
            out = out[m.end():]
            continue
        m = re.match(r"^\s*(Local|Global|Program|Polymorphic|Monomorphic|Private|"
                     r"#\[[^\]]*\])\s+", out)
        if m:
            out = out[m.end():]
            continue
        return out


def _top_level_split(s, seps):
    """Yield spans of `s` split on `seps` at bracket depth 0."""
    depth = 0
    last = 0
    i = 0
    while i < len(s):
        c = s[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0:
            for sep in seps:
                if s.startswith(sep, i):
                    yield (last, i)
                    last = i + len(sep)
                    i += len(sep) - 1
                    break
        i += 1
    yield (last, len(s))


def _find_top(s, sub, start=0):
    """Offset of `sub` in `s` at bracket depth 0, or -1."""
    depth = 0
    i = 0
    while i < len(s):
        c = s[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0 and i >= start and s.startswith(sub, i):
            return i
        i += 1
    return -1


def _constructors(body):
    """Constructor names of an `Inductive`/`Variant` body (the text after `:=`)."""
    names = []
    for a, b in _top_level_split(body, ["|"]):
        chunk = body[a:b].strip()
        if not chunk:
            continue
        m = re.match(r"^(" + IDENT + r")\b", chunk)
        if m and ":" in chunk or (m and "forall" in chunk):
            names.append(m.group(1))
        elif m:
            names.append(m.group(1))
    return names


def parse_binders(text):
    """Binder groups of a `Variable`/`Context`/`Hypothesis` command.

    Returns [(names, type text, open bracket)]; the bracket is `(`, `{`, `[`, `` ` ``
    or `` for the unbracketed `Variable x y : T` form.
    """
    s = text.strip()
    out = []
    i = 0
    if not s.startswith(("(", "{", "[", "`")):
        k = _find_top(s, ":")
        if k < 0:
            return [([n for n in IDENT_RE.findall(s)], "", "")]
        return [([n for n in IDENT_RE.findall(s[:k])], s[k + 1:].strip(), "")]
    while i < len(s):
        if s[i] in " \t\r\n":
            i += 1
            continue
        br = ""
        if s[i] == "`":
            br = "`"
            i += 1
            if i < len(s) and s[i] in "({":
                br += s[i]
        if i >= len(s):
            break
        if s[i] not in "({[":
            break
        if not br:
            br = s[i]
        close = {"(": ")", "{": "}", "[": "]"}[s[i]]
        depth = 0
        j = i
        while j < len(s):
            if s[j] in "({[":
                depth += 1
            elif s[j] in ")}]":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        inner = s[i + 1:j]
        k = _find_top(inner, ":")
        if k < 0:
            out.append(([n for n in IDENT_RE.findall(inner)[:1]], inner.strip(), br))
        else:
            out.append(([n for n in IDENT_RE.findall(inner[:k])],
                        inner[k + 1:].strip(), br))
        i = j + 1
    return out


def _record_fields(body):
    """Record constructor and field names from the text after `:=`."""
    names = []
    m = re.match(r"\s*(" + IDENT + r")?\s*\{(.*)\}\s*$", body.strip(), re.S)
    if not m:
        return names
    if m.group(1):
        names.append(m.group(1))
    for a, b in _top_level_split(m.group(2), [";"]):
        chunk = m.group(2)[a:b].strip()
        mm = re.match(r"^(" + IDENT + r")\b", chunk)
        if mm:
            names.append(mm.group(1))
    return names


def parse_file(path, module, src=None):
    if src is None:
        with open(path, encoding="utf8", errors="replace") as fh:
            src = fh.read()
    vf = VFile(path, module, src)
    bl = vf.blank
    sents = split_sentences(bl)
    sections = []
    modules = []
    i = 0
    while i < len(sents):
        a, b = sents[i]
        raw = bl[a:b]
        body = raw.rstrip()
        if body.endswith("."):
            body = body[:-1]
        head = body.lstrip()

        def mk(kind, **kw):
            kw.setdefault("start", a)
            kw.setdefault("end", b)
            kw.setdefault("line", vf.lineno(a))
            kw.setdefault("endline", vf.lineno(b - 1))
            kw.setdefault("text", vf.src[a:b])
            kw.setdefault("module", module)
            kw.setdefault("sections", list(sections))
            kw.setdefault("modules", list(modules))
            return Item(kind=kind, **kw)

        m = REQ_RE.match(body)
        if m and head.startswith(("From ", "Require")):
            frm, how, rest = m.group(1), m.group(2) or "", m.group(3)
            mods = [w for w in re.split(r"\s+", rest.strip()) if w]
            full = [((frm + "." + w) if frm else w) for w in mods]
            kind = {"Import": "import", "Export": "export"}.get(how, "require")
            for f in full:
                vf.requires.append((kind, f))
            vf.items.append(mk("require", names=full, name=how or "", kw=kind))
            i += 1
            continue

        m = IMPORT_RE.match(body)
        if m and head.split(None, 1)[0] in ("Import", "Export"):
            how = m.group(1)
            mods = [w for w in re.split(r"\s+", m.group(2).strip()) if w]
            kind = "import" if how == "Import" else "export"
            for f in mods:
                vf.requires.append((kind, f))
            vf.items.append(mk("require", names=mods, name=how, kw=kind))
            i += 1
            continue

        m = SECTION_RE.match(body)
        if m:
            vf.items.append(mk("section_open", name=m.group(1)))
            sections.append(m.group(1))
            i += 1
            continue

        m = END_RE.match(body)
        if m:
            nm = m.group(1)
            if sections and sections[-1] == nm:
                sections.pop()
                vf.items.append(mk("section_close", name=nm))
            elif modules and modules[-1] == nm:
                modules.pop()
                vf.items.append(mk("module_close", name=nm))
            else:
                if sections:
                    sections.pop()
                vf.items.append(mk("section_close", name=nm))
            i += 1
            continue

        m = MODULE_RE.match(body)
        if m and head.startswith("Module"):
            nm = m.group(1)
            rest = m.group(2) or ""
            if ":=" in rest:            # module alias / application, no scope
                vf.items.append(mk("other", name=nm))
            else:
                vf.items.append(mk("module_open", name=nm))
                modules.append(nm)
            i += 1
            continue

        stripped = _strip_mods(body)
        is_local = bool(re.match(r"^\s*(Local\b|#\[\s*local\s*\])", body))

        if NOTATION_RE.match(body):
            mm = re.match(r"^\s*(?:Tactic\s+Notation|Notation|Abbreviation|"
                          r"Infix)\s+(.*)$",
                          _strip_mods(body), re.S)
            nm = None
            nbody = None
            if mm:
                rest = mm.group(1).strip()
                k = _find_top(rest, ":=")
                if k >= 0:
                    lhs, nbody = rest[:k].strip(), rest[k + 2:].strip()
                    mi = re.match(r"^(" + IDENT + r")\b", lhs)
                    if mi:
                        nm = mi.group(1)
            vf.items.append(mk("notation", name=nm, notation_body=nbody,
                               is_local=is_local))
            i += 1
            continue

        if re.match(r"^\s*Ltac2?\b", stripped):
            mm = re.match(r"^\s*Ltac2?\s+(?:Notation\s+)?(" + QID + r")", stripped)
            nm = mm.group(1) if mm else None
            k = _find_top(stripped, ":=")
            if k < 0:
                k = _find_top(stripped, "::=")
            lbody = stripped[k + 2:] if k >= 0 else ""
            vf.items.append(mk("ltac", name=nm, notation_body=lbody, is_local=is_local))
            i += 1
            continue

        m = ARGS_RE.match(body)
        if m:
            vf.items.append(mk("arguments", name=m.group(1)))
            i += 1
            continue

        if HINT_RE.match(body):
            vf.items.append(mk("hint"))
            i += 1
            continue

        if BINDER_RE.match(stripped):
            kw = re.match(r"^\s*(\S+)", stripped).group(1)
            mm = re.match(r"^\s*\S+\s+(.*)$", stripped, re.S)
            groups = parse_binders(mm.group(1)) if mm else []
            names = [n for g in groups for n in g[0]]
            kind = {"Variable": "variable", "Variables": "variable",
                    "Context": "context", "Hypothesis": "hypothesis",
                    "Hypotheses": "hypothesis", "Let": "let"}.get(kw, "other")
            if kind == "let":
                # `Let x := e.` is a definition in the section; keep it as a decl too
                mm2 = re.match(r"^\s*Let\s+(" + IDENT + r")", stripped)
                vf.items.append(mk("let", name=mm2.group(1) if mm2 else None,
                                   kw="Let", is_local=is_local))
                i += 1
                continue
            vf.items.append(mk(kind, names=names, kw=kw, is_local=is_local,
                               args=groups))
            i += 1
            continue

        mkw = re.match(r"^\s*(" + "|".join(DECL_KW) + r")\b(.*)$", stripped, re.S)
        if mkw:
            kw = mkw.group(1)
            rest = mkw.group(2)
            mn = re.match(r"\s*(" + IDENT + r")", rest)
            nm = mn.group(1) if mn else None
            assign = _find_top(rest, ":=")
            end_i = i
            proof_txt = ""
            pusing = None
            needs_proof = kw in PROOF_KW or assign < 0
            if needs_proof:
                j = i + 1
                while j < len(sents):
                    s2 = bl[sents[j][0]:sents[j][1]].strip()
                    # a closing brace or a bullet may share the sentence with the
                    # `Qed.` that follows it (`... lia. }` + newline + `Qed.`), so
                    # look past them; otherwise the declaration swallows the rest of
                    # the file.
                    w = re.match(r"^[\s\-+*{}]*(" + IDENT + r")", s2)
                    if w and w.group(1) in TERMINATORS:
                        break
                    j += 1
                if j < len(sents):
                    end_i = j
                    proof_txt = vf.src[sents[i + 1][0]:sents[j][1]] if j > i else ""
                    pm = PROOF_USING_RE.match(bl[sents[i + 1][0]:sents[i + 1][1]]) \
                        if j > i else None
                    if pm:
                        pusing = pm.group(1).strip()
                else:
                    end_i = i
            cons = []
            if kw in TYPE_KW and assign >= 0:
                tail = rest[assign + 2:]
                if kw in ("Record", "Structure", "Class"):
                    cons = _record_fields(tail)
                else:
                    cons = _constructors(tail)
            a2, b2 = sents[i][0], sents[end_i][1]
            it = mk("decl", name=nm, kw=kw, constructors=cons, is_local=is_local,
                    proof=proof_txt, proof_using=pusing,
                    stmt=vf.src[a2:sents[i][1]], start=a2, end=b2,
                    line=vf.lineno(a2), endline=vf.lineno(b2 - 1),
                    text=vf.src[a2:b2])
            vf.items.append(it)
            i = end_i + 1
            continue

        vf.items.append(mk("other"))
        i += 1
    return vf


# --------------------------------------------------------------- the index

class Index(object):
    """Every declaration of the tree, and name resolution for one file."""

    def __init__(self, root, pkg, only=None, profile=None, twin_dir="BudgetWit"):
        self.root = os.fspath(root)
        self.pkg = pkg
        self.profile = profile
        self.twin_dir = twin_dir
        self.files = {}            # module -> VFile
        self.by_full = {}          # full name -> Item
        self.module_names = defaultdict(dict)   # module -> {short: exported full}
        self.file_names = defaultdict(dict)     # module -> {short: full}, locals too
        self.short = defaultdict(list)          # short name -> [full]
        self._resolved = {}
        self._rawcache = {}
        self._aliascache = {}
        self.mod_by_suffix = defaultdict(list)
        paths = []
        for d, dirs, fs in os.walk(root):
            dirs[:] = sorted(n for n in dirs if n != twin_dir)
            for f in sorted(fs):
                if f.endswith(".v"):
                    paths.append(os.path.join(d, f))
        for p in sorted(paths):
            rel = os.path.relpath(p, root)[:-2].replace(os.sep, ".")
            mod = pkg + "." + rel
            if only is not None and rel.split(".")[0] not in only:
                continue
            self.files[mod] = None
            self._path = getattr(self, "_path", {})
            self._path[mod] = p
        for mod in self.files:
            self.load(mod)
        for mod in self.files:
            parts = mod.split(".")
            for k in range(1, len(parts) + 1):
                self.mod_by_suffix[".".join(parts[-k:])].append(mod)

    def load(self, mod):
        if self.files.get(mod) is not None:
            return self.files[mod]
        vf = parse_file(self._path[mod], mod)
        self.files[mod] = vf
        tbl = self.module_names[mod]
        loc = self.file_names[mod]
        rank = {"decl": 3, "let": 2, "ltac": 1, "notation": 0}
        for it in vf.items:
            if it.kind in ("decl", "let", "ltac", "notation") and it.name:
                full = it.full
                # A local notation can have
                # the same qualified name as the inductive it abbreviates.  The
                # declaration is what the name means; the notation is an alias of it.
                old = self.by_full.get(full)
                if old is None or rank[it.kind] >= rank[old.kind]:
                    self.by_full[full] = it
                short = full[len(mod) + 1:]
                loc[short] = full
                # A `Local` notation or tactic, or one declared inside a `Section`,
                # is gone for an importer: Rocq scopes it to the section / the file.
                hidden = (it.kind in ("notation", "ltac")
                          and (it.is_local or it.sections)
                          and not re.match(r"^\s*Global\b", it.text))
                if not hidden:
                    tbl[short] = full
                    self.short[it.name].append(full)
                for c in (it.constructors or []):
                    cfull = ".".join([mod] + list(it.modules or []) + [c])
                    self.by_full.setdefault(cfull, it)
                    loc.setdefault(cfull[len(mod) + 1:], cfull)
                    tbl.setdefault(cfull[len(mod) + 1:], cfull)
                    self.short[c].append(cfull)
        return vf

    def alias(self, full, _depth=0):
        """Follow a `Notation x := (@y ...)` alias to the declaration it names."""
        if _depth == 0:
            got = self._aliascache.get(full)
            if got is not None:
                return got
            got = self._alias_un(full, 0)
            self._aliascache[full] = got
            return got
        return self._alias_un(full, _depth)

    def _alias_un(self, full, _depth):
        it = self.by_full.get(full)
        if it is None or it.kind != "notation" or _depth > 8:
            return full
        body = it.notation_body or ""
        m = REF_RE.search(blank_text(body))
        if not m:
            return full
        head = m.group(1)
        if head == it.name:
            # A self-named notation abbreviates the imported declaration.
            tgt = self.scope(it.module).get(head)
            return tgt or full
        tgt = self.resolve(head, it.module)
        if tgt is None or tgt == full:
            return full
        return self.alias(tgt, _depth + 1)

    # ---- imports

    def import_seq(self, mod, _seen=None, _top=True):
        """Modules whose names are unqualified in `mod`, in effect order.

        Last entry wins.  `Require Import A` brings A's `Export`ed modules first, then
        A; a plain `Require` brings nothing unqualified but still loads A.
        """
        key = ("seq", mod)
        if key in self._resolved:
            return self._resolved[key]
        seen = set() if _seen is None else _seen
        out = []
        vf = self.files.get(mod)
        if vf is None:
            return out
        if vf is None:
            return out
        for kind, name in vf.requires:
            full = self._full_module(name, mod)
            if full is None:
                continue
            if kind == "require":
                continue
            if full in seen:
                out = [o for o in out if o != full]
            seen.add(full)
            out.extend(self.export_seq(full, set()))
            out.append(full)
        self._resolved[key] = out
        return out

    def export_seq(self, mod, seen):
        """Modules `mod` re-exports, in effect order."""
        if mod in seen:
            return []
        seen.add(mod)
        vf = self.files.get(mod)
        if vf is None:
            return []
        out = []
        for kind, name in vf.requires:
            if kind != "export":
                continue
            full = self._full_module(name, mod)
            if full is None:
                continue
            out.extend(self.export_seq(full, seen))
            out.append(full)
        return out

    def _full_module(self, name, here):
        if name in self.files:
            return name
        cands = [m for m in self.files if m == name or m.endswith("." + name)]
        if len(cands) == 1:
            return cands[0]
        if cands:
            # prefer the one in the same directory branch as `here`
            pre = here.rsplit(".", 1)[0]
            same = [c for c in cands if c.startswith(pre + ".")]
            if len(same) == 1:
                return same[0]
            cands.sort(key=len)
            return cands[0]
        return None

    # ---- resolution

    def scope(self, mod):
        """{short name -> full name} visible unqualified in `mod`, last import wins."""
        key = ("scope", mod)
        if key in self._resolved:
            return self._resolved[key]
        tbl = {}
        for m in self.import_seq(mod):
            tbl.update(self.module_names.get(m, {}))
        self._resolved[key] = tbl
        return tbl

    def mod_rank(self, mod):
        """{module: rank} for `mod`; a later import outranks an earlier one."""
        key = ("rank", mod)
        if key in self._resolved:
            return self._resolved[key]
        rank = {}
        for i, m in enumerate(self.import_seq(mod)):
            rank[m] = i + 1000
        vf = self.files.get(mod)
        for kind, name in (vf.requires if vf else []):
            f = self._full_module(name, mod)
            if f and f not in rank:
                rank[f] = 1
        rank[mod] = 10 ** 6
        self._resolved[key] = rank
        return rank

    def lookup_qualified(self, name, mod):
        """Resolve a partly qualified `A.b.c` as written in `mod`.

        Tried right to left: the longest module prefix that names a module of the
        tree wins, and among several modules with that suffix the one imported last.
        """
        parts = name.split(".")
        rank = self.mod_rank(mod)
        best = None
        best_score = None
        for i in range(len(parts) - 1, 0, -1):
            modpart = ".".join(parts[:i])
            short = ".".join(parts[i:])
            for cand in self.mod_by_suffix.get(modpart, ()):
                tbl = self.module_names.get(cand)
                if not tbl or short not in tbl:
                    continue
                score = (i, rank.get(cand, 0))
                if best_score is None or score > best_score:
                    best_score = score
                    best = tbl[short]
            if best is not None:
                return best
        return None

    def resolve(self, name, mod, local=None, follow=True):
        """Resolve `name` as written in module `mod`.  Returns a full name or None.

        `local` is a {name: full} of names bound in the file itself that take
        precedence over imports.  With `follow`, a `Notation` alias is followed to the
        declaration it abbreviates, including same-named local aliases).
        """
        got = self._resolve_raw(name, mod, local)
        if got is not None and follow:
            return self.alias(got)
        return got

    def _resolve_raw(self, name, mod, local=None):
        if local and name in local:
            return local[name]
        key = (mod, name)
        if key in self._rawcache:
            return self._rawcache[key]
        got = self._resolve_raw_un(name, mod)
        self._rawcache[key] = got
        return got

    def _resolve_raw_un(self, name, mod):
        own = self.file_names.get(mod, {})
        if name in own:
            return own[name]
        sc = self.scope(mod)
        if name in sc:
            return sc[name]
        if "." in name:
            got = self.lookup_qualified(name, mod)
            if got is not None:
                return got
            if name in self.by_full:
                return name
        return None


def references(text):
    """Every identifier occurrence of `text` (already blanked), with spans."""
    return [(m.group(1), m.start(1), m.end(1)) for m in REF_RE.finditer(text)]


BINDER_HINT_RE = re.compile(
    r"(?:\bintros?\b|\bforall\b|\bfun\b|\bintro\b|\bexists\b|\bdestruct\b.*?\bas\b|"
    r"\bas\b|\bset\b|\bpose\b|\bremember\b|\bassert\b)\s+([^.;|]*)")


def bound_names(text):
    """Over-approximate the names a proof script binds locally.

    Over-approximating is the safe side: a name taken for a binder is left alone by the
    generator, so a wrong guess shows up as a build error, never as a silent rename.
    """
    out = set()
    for m in BINDER_HINT_RE.finditer(text):
        for nm in IDENT_RE.findall(m.group(1)):
            out.add(nm)
    for m in re.finditer(r"[({\[]\s*(" + IDENT + r"(?:\s+" + IDENT + r")*)\s*:[^=]",
                         text):
        for nm in m.group(1).split():
            out.add(nm)
    return out


