#!/usr/bin/env python3
"""coqhyp.py: a Coq lexer and the hypothesis-position classifier of the TCA hypothesis-value audit (row
TCA; proves no function, kind: measurement). Imported by hyplist.py; no side effects.

lex(text) -> tokens (kind, text, line, col): comments and strings are skipped (nested comments, strings inside comments,
"" escapes); kinds: 'id' (qualified names kept whole, e.g. YP09.mkRegion), 'num' (0x.. hex or decimal), 'p' (punctuation:
-> <-> := : , ( ) [ ] { } ; | . and any other single character), 'end' (a sentence-ending '.').

classify(tokens) -> rows (token, cls, keyword, name, ctor) for every numeral in a HYPOTHESIS position, by these rules:
  section-hyp    every numeral of a Hypothesis / Hypotheses / Variable / Variables / Context / Axiom(s) / Parameter(s) /
                 Conjecture sentence (outside proof bodies);
  record-field   every numeral of a Record / Structure / Class sentence (the field types: a bundle of hypotheses, e.g.
                 A/AFgi.v free_hyps fh_SEED); inductive: every numeral of an Inductive / CoInductive sentence;
  lemma-premise  every numeral of a Lemma / Theorem / Corollary / Fact / Remark / Proposition / Example / Instance /
                 Goal statement that is not in its conclusion: binders before the statement colon, the types of leading
                 'forall' binders, and the left side of every top-level '->' (nested 'forall's in the conclusion
                 repeat the rule); numerals of the conclusion are goals (proved), not listed;
  fact-ctor      every numeral in the arguments of mkAF / mkAC / mkFacts / mkRegion / mkChunk / mkSS / mkSST / Rg /
                 region_ok / chunk_ok / afact_ok / atoms_ok / facts_ok / regions_ok (any qualifier), outside proof bodies
                 and outside lemma conclusions;
  state-spec     every numeral of the body of a Definition / Let whose declared type is one of afact, facts, region,
                 chunk, smem, sstate, or a list / product of them (the symbolic states and their facts);
  def-in-hyp     (hyplist.py) every numeral of a Definition / Let / Notation (outside proofs) that one of the
                 positions above names, directly or through other definitions (all depths).
Numerals inside proof bodies (Proof. .. Qed. / Defined. / Admitted.; or a statement with no ':=' up to its end) are
checked by the kernel as parts of proof terms and are not listed; the census counts them.
"""
import re

KW_HYP = {"Hypothesis", "Hypotheses", "Variable", "Variables", "Context", "Axiom", "Axioms", "Parameter", "Parameters",
          "Conjecture"}
KW_REC = {"Record": "record-field", "Structure": "record-field", "Class": "record-field", "Inductive": "inductive",
          "CoInductive": "inductive"}
KW_LEMMA = {"Lemma", "Theorem", "Corollary", "Fact", "Remark", "Proposition", "Example", "Instance", "Goal", "Property"}
KW_DEF = {"Definition", "Let", "Fixpoint", "CoFixpoint", "Notation", "Abbreviation"}
KW_END = {"Qed", "Defined", "Admitted", "Abort", "Save"}
PREFIX = {"Local", "Global", "Program", "Polymorphic", "Monomorphic", "Private", "#[local]", "#[global]", "#[export]"}
CTORS = {"mkAF", "mkAC", "mkFacts", "mkRegion", "mkChunk", "mkSS", "mkSST", "Rg", "region_ok", "chunk_ok", "afact_ok",
         "atoms_ok", "facts_ok", "regions_ok"}
STATE_TYPES = {"afact", "facts", "region", "chunk", "smem", "sstate"}

_ID = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")
_NUM = re.compile(r"0[xX][0-9a-fA-F_]+|[0-9][0-9_]*")
_PUNCT = ("<->", "->", ":=", "=>", "<-", "::", "++")


def lex(text):
    toks, i, n, line, col0 = [], 0, len(text), 1, 0

    def adv(j):
        nonlocal line, col0
        k = text.count("\n", i, j)
        if k:
            line += k
            col0 = text.rfind("\n", i, j) + 1
        return j

    while i < n:
        c = text[i]
        if c == "\n" or c in " \t\r":
            i = adv(i + 1)
            continue
        if text.startswith("(*", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("(*", j):
                    depth, j = depth + 1, j + 2
                elif text.startswith("*)", j):
                    depth, j = depth - 1, j + 2
                elif text[j] == '"':
                    j += 1
                    while j < n:
                        if text[j] == '"':
                            if text.startswith('""', j):
                                j += 2
                                continue
                            j += 1
                            break
                        j += 1
                else:
                    j += 1
            i = adv(j)
            continue
        if c == '"':
            j = i + 1
            while j < n:
                if text[j] == '"':
                    if text.startswith('""', j):
                        j += 2
                        continue
                    j += 1
                    break
                j += 1
            i = adv(j)
            continue
        if c.isdigit():
            m = _NUM.match(text, i)
            # a numeral glued to identifier characters is part of a name (e.g. 0x1234abc_lbl); never in Coq source here
            toks.append(("num", m.group(0), line, i - col0))
            i = m.end()
            continue
        if c.isalpha() or c == "_":
            m = _ID.match(text, i)
            toks.append(("id", m.group(0), line, i - col0))
            i = m.end()
            continue
        if c == "#" and text.startswith("#[", i):
            j = text.index("]", i) + 1
            toks.append(("id", text[i:j], line, i - col0))
            i = j
            continue
        if c == ".":
            nxt = text[i + 1] if i + 1 < n else " "
            if nxt in " \t\r\n" or text.startswith("(*", i + 1):
                toks.append(("end", ".", line, i - col0))
                i += 1
                continue
            if nxt == ".":
                j = i
                while j < n and text[j] == ".":
                    j += 1
                toks.append(("p", text[i:j], line, i - col0))
                i = j
                continue
        for p in _PUNCT:
            if text.startswith(p, i):
                toks.append(("p", p, line, i - col0))
                i += len(p)
                break
        else:
            toks.append(("p", c, line, i - col0))
            i += 1
    return toks


def sentences(toks):
    """split into sentences (lists of tokens); the '.' token closes one. Leading bullets / braces are separate items."""
    out, cur = [], []
    for t in toks:
        cur.append(t)
        if t[0] == "end":
            out.append(cur)
            cur = []
    if cur:
        out.append(cur)
    return out


def head(sent):
    """(keyword, index of the first token after the keyword and its prefixes); bullets and braces are skipped."""
    i = 0
    while i < len(sent) and sent[i][0] == "p" and sent[i][1] in ("-", "+", "*", "{", "}"):
        i += 1
    while i < len(sent) and sent[i][0] == "id" and (sent[i][1] in PREFIX or sent[i][1].startswith("#[")):
        i += 1
    if i < len(sent) and sent[i][0] == "id":
        return sent[i][1], i + 1
    return None, i


def top_index(seq, pred, start=0):
    d = 0
    for k in range(start, len(seq)):
        t = seq[k]
        if t[0] == "p" and t[1] in ("(", "[", "{"):
            d += 1
        elif t[0] == "p" and t[1] in (")", "]", "}"):
            d -= 1
        elif d == 0 and pred(t):
            return k
    return -1


def split_top(seq, what):
    parts, d, cur = [], 0, []
    for t in seq:
        if t[0] == "p" and t[1] in ("(", "[", "{"):
            d += 1
        elif t[0] == "p" and t[1] in (")", "]", "}"):
            d -= 1
        if d == 0 and t[0] == "p" and t[1] == what:
            parts.append(cur)
            cur = []
        else:
            cur.append(t)
    parts.append(cur)
    return parts


def conclusion(stmt):
    """stmt: tokens after the statement colon (without the final '.'); returns (premise tokens, conclusion tokens)."""
    prem = []
    rest = list(stmt)
    while True:
        if rest and rest[0][0] == "id" and rest[0][1] == "forall":
            k = top_index(rest, lambda t: t[0] == "p" and t[1] == ",", 1)
            if k < 0:
                return prem, rest
            prem += rest[:k + 1]
            rest = rest[k + 1:]
            continue
        parts = split_top(rest, "->")
        if len(parts) == 1:
            return prem, rest
        for p in parts[:-1]:
            prem += p
        rest = parts[-1]


STOP_AT_D0 = {";", ",", "|", ":=", "->", "<->", "=", "/", "\\", "::", "++", "<", ">", "=>"}


def ctor_spans(seq):
    """indices of the tokens inside the arguments of a fact constructor. The argument run of a constructor at depth d
    ends at the first ')' ']' '}' that closes the group holding it, or at a depth-d separator (; , | := -> <-> = /\\ \\/
    :: ++ < > =>) or keyword (in then else with)."""
    inside = set()
    depth = []
    d = 0
    for t in seq:
        depth.append(d)
        if t[0] == "p" and t[1] in ("(", "[", "{"):
            d += 1
        elif t[0] == "p" and t[1] in (")", "]", "}"):
            d -= 1
    for k, t in enumerate(seq):
        if t[0] == "id" and t[1].split(".")[-1] in CTORS:
            d0 = depth[k]
            for j in range(k + 1, len(seq)):
                tj = seq[j]
                if tj[0] == "end":
                    break
                if tj[0] == "p" and tj[1] in (")", "]", "}") and depth[j] <= d0:
                    break
                if depth[j] == d0 and ((tj[0] == "p" and tj[1] in STOP_AT_D0)
                                       or (tj[0] == "id" and tj[1] in ("in", "then", "else", "with"))):
                    break
                inside.add(j)
    return inside


def decl_type(sent, i):
    """for a Definition-like sentence starting its name at i: (name, type tokens or None, body tokens or None,
    has_body)."""
    if i >= len(sent) or sent[i][0] != "id":
        return None, None, None, False
    name = sent[i][1]
    k_assign = top_index(sent, lambda t: t[0] == "p" and t[1] == ":=", i + 1)
    k_colon = top_index(sent, lambda t: t[0] == "p" and t[1] == ":", i + 1)
    if k_assign < 0:
        return name, (sent[k_colon + 1:-1] if k_colon >= 0 else None), None, False
    ty = sent[k_colon + 1:k_assign] if 0 <= k_colon < k_assign else None
    return name, ty, sent[k_assign + 1:-1 if sent[-1][0] == "end" else len(sent)], True


def is_state_type(ty):
    if not ty:
        return False
    ids = [t[1].split(".")[-1] for t in ty if t[0] == "id"]
    if not ids or any(x in ("Prop", "Type", "Set") for x in ids):
        return False
    core = [x for x in ids if x not in ("list", "option", "prod", "nat", "Z", "N", "bool")]
    return bool(core) and all(x in STATE_TYPES for x in core)


def classify(toks):
    """returns (rows, census, used, defs, add, places): rows = [(tok, cls, keyword, name, ctor)] for every rule but
    def-in-hyp;
    census = counts of the numerals not listed, by place; used = identifiers named in those positions; defs = name ->
    Definition sentences of this file (outside proofs); add = the row adder (it skips a numeral already listed)."""
    rows = []
    census = {"in-proof": 0, "conclusion": 0, "other": 0, "definition": 0, "computed-state": 0}
    places = {}          # (line, col) -> (place, keyword, name) for numerals not listed

    def place(seq, where, kw, nm):
        for t in seq:
            if t[0] == "num":
                places[(t[2], t[3])] = (where, kw or "?", nm)
    sents = sentences(toks)
    in_proof = False
    defs = {}            # name -> Definition sentences (outside proofs)
    used = set()         # identifiers used in hypothesis positions
    listed = set()

    def add(t, cls, kind, name, extra=""):
        key = (t[2], t[3])
        if key in listed:
            return
        listed.add(key)
        rows.append((t, cls, kind, name, extra))

    def use_ids(seq):
        for t in seq:
            if t[0] == "id":
                used.add(t[1].split(".")[-1])

    for s in sents:
        kw, i = head(s)
        if in_proof:
            if kw in KW_END:
                in_proof = False
            census["in-proof"] += sum(1 for t in s if t[0] == "num")
            place(s, "in-proof", kw, "")
            continue
        if kw == "Proof":
            in_proof = True
            census["in-proof"] += sum(1 for t in s if t[0] == "num")
            place(s, "in-proof", kw, "")
            continue
        nums = [t for t in s if t[0] == "num"]
        name = s[i][1] if i < len(s) and s[i][0] == "id" else ""
        if kw in KW_HYP:
            for t in nums:
                add(t, "section-hyp", kw, name)
            use_ids(s[i:])
            continue
        if kw in KW_REC:
            for t in nums:
                add(t, KW_REC[kw], kw, name)
            use_ids(s[i:])
            continue
        if kw in KW_LEMMA:
            body = s[:-1] if s[-1][0] == "end" else s
            k_assign = top_index(body, lambda t: t[0] == "p" and t[1] == ":=", i)
            if kw == "Goal":
                k_colon = i - 1
            else:
                k_colon = top_index(body, lambda t: t[0] == "p" and t[1] == ":", i + 1)
            stmt_end = k_assign if k_assign >= 0 else len(body)
            binders = body[i + 1:k_colon] if k_colon > i else []
            stmt = body[k_colon + 1:stmt_end] if k_colon >= 0 else []
            prem, concl = conclusion(stmt)
            pset = {(t[2], t[3]) for t in binders + prem}
            for t in nums:
                if (t[2], t[3]) in pset:
                    add(t, "lemma-premise", kw, name)
                else:
                    census["conclusion"] += 1
                    place([t], "conclusion", kw, name)
            use_ids(binders + prem)
            if k_assign < 0:
                in_proof = True
            continue
        if kw in KW_DEF:
            nm, ty, bodyt, has_body = decl_type(s, i)
            if not has_body and kw != "Notation":
                in_proof = True
            spans = ctor_spans(s)
            st = is_state_type(ty)
            computed = bool(bodyt) and bodyt[0][0] == "id" and bodyt[0][1] == "Eval"
            for k, t in enumerate(s):
                if t[0] != "num":
                    continue
                if k in spans:
                    add(t, "fact-ctor", kw, nm or name, ctor_of(s, k))
                elif st and not computed:
                    add(t, "state-spec", kw, nm or name, " ".join(x[1] for x in ty)[:40])
                else:
                    census["computed-state" if st else "definition"] += 1
                    place([t], "computed-state" if st else "definition", kw, nm or name)
            if spans:
                use_ids([s[k] for k in spans])
            if st and not computed:
                use_ids(bodyt or [])
            defs.setdefault(nm or name, []).append(s)
            continue
        # any other vernacular (Section, Require, Hint, Arguments, Opaque, Notation-less commands, Ltac, ...)
        spans = ctor_spans(s)
        for k, t in enumerate(s):
            if t[0] == "num":
                if k in spans:
                    add(t, "fact-ctor", kw or "?", name, ctor_of(s, k))
                else:
                    census["other"] += 1
                    place([t], "other", kw, name)
    census["listed"] = len(rows)
    return rows, census, used, defs, add, places


def ctor_of(s, k):
    """the innermost fact constructor whose argument run holds token k (name only)."""
    for j in range(k - 1, -1, -1):
        t = s[j]
        if t[0] == "id" and t[1].split(".")[-1] in CTORS and _holds(s, j, k):
            return t[1].split(".")[-1]
    return ""


def _holds(s, j, k):
    d = 0
    for x in range(j + 1, k + 1):
        t = s[x]
        if t[0] == "p" and t[1] in ("(", "[", "{"):
            d += 1
        elif t[0] == "p" and t[1] in (")", "]", "}"):
            d -= 1
            if d < 0:
                return False
        elif d == 0 and ((t[0] == "p" and t[1] in STOP_AT_D0) or (t[0] == "id" and t[1] in ("in", "then", "else", "with"))):
            return False
    return True
