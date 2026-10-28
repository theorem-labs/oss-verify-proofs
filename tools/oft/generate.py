"""oft generate: render every generated file from the facts.

`render_all(tree)` is a pure function from the facts to {path: text}; the
exporter calls it too, so the public tree and its preview are rendered by
the same code.  `run(root, check=True)` compares instead of writing, and is
what CI runs: a hand-edited generated file, a stale one, or a facts change
without its rendering all fail it.
"""
import os
import sys

from . import facts, names, paths, render, rules, schema, shapes
from .facts import PHRASEBOOK as PB

THEORY_DEPS = "Stdlib stdpp ReadFile Flocq LinuxProcessSemantics OssFuzzTheorems.Core"
# A proof may also use Ltac2, which Rocq installs as its own theory; dune finds a theory only when it is listed.
PROOF_THEORY_DEPS = THEORY_DEPS + " Ltac2"
REPO_URL = "https://github.com/theorem-labs/oss-verify-proofs"
COUNT_WORDS = {1: "One", 2: "Two", 3: "Three", 4: "Four"}
STOP_WORDS = {"abort": "abort()", "assert": "assert()", "trap": "a trap", "throw": "an uncaught exception",
              "panic": "a panic", "raise": "an uncaught Python exception (status 79)",
              "fail": "t.Fatal, t.Error or t.Fail (status 79)", "print-only": "prints only", "return-only": "returns only"}
LIVE_WORDS = {True: "confirmed in the binary", False: "compiled out", "unknown": "not confirmed in the binary"}
KIND_ORDER = {"halts": 0, "agreement": 1, "bound": 2, "decidability": 3}
PAIR_ORDER = ["asan", "ubsan", "asan-ubsan"]   # ASan first: the headline pair, as in docs/statements.md
UPSTREAM_WORDS = {"reported": "reported upstream",
                  "fixed-upstream": "fixed upstream", "not-a-defect": "not a defect"}
READING_ORDER = {"budget": 0, "may-fail": 1, "alloc-forced-only": 1}
FALSE_STATUSES = ("refuted", "counterexample", "witnessed-false")
UNINSTRUMENTED_WORDS = {"libc": "the C library", "compiler-rt": "compiler-rt", "sanitizer-runtime": "the sanitizer runtime",
                        "cxx-runtime": "the C++ runtime", "fortran-runtime": "the Fortran runtime",
                        "image-library": "a library from the build image", "assembly": "assembly",
                        "fortran": "Fortran", "driver": "this repository's driver"}


# ------------------------------------------------------------------ helpers

def _t(template, block, **v):
    return render.fill(template, block, **v)


def _comment(text, first_indent_skip=True):
    """Prose for inside (** ... *): sanitised, wrapped, indented by 4."""
    w = render.wrap(render.rocq_comment_text(text), 80, "    ")
    return w[4:] if first_indent_skip else w


def _stop(c):
    return "exit(%d)" % c["exit_status"] if c["stops_with"] == "exit" else STOP_WORDS[c["stops_with"]]


def _exits_words(st):
    ex = st.get("exits", "any")
    if ex == "any":
        return "any status"
    return "status " + render.join_words([str(e) for e in sorted(ex)], "or")


def _library(h):
    lib = h.data["library"]
    name = (h.project.data.get("library") or {}).get("name", h.project.name)
    ver = (" " + lib["version"]) if lib.get("version") else ""
    label = facts.repo_label(lib["repository"])
    at = ("at %s" % lib["commit"][:8]) if "commit" in lib else ("release archive %s" % lib["archive_sha256"][:8])
    if label == name:
        return "%s%s (%s)" % (name, ver, at), name
    return "%s%s (%s %s)" % (name, ver, label, at), name


def _order(h):
    def build_rank(s):
        b = s.data["builds"][-1]
        return schema.BUILDS.index(b) if s.kind == "halts" else PAIR_ORDER.index(b)
    return sorted((s for s in h.statements.values()),
                  key=lambda s: (KIND_ORDER[s.kind], READING_ORDER[s.data["reading"]], build_rank(s)))


def _who(h):
    return "driver" if h.data["origin"] == "this-repository" else "harness"


def _origin(h):
    """The harness's origin as its pages word it: an upstream target of a project OSS-Fuzz does not have is the
    project's own, which OSS-Fuzz does not run."""
    o = h.data["origin"]
    return o + "_no_oss_fuzz" if o == "upstream" and "oss_fuzz" not in h.project.data else o


# the blocks with a variant for a language. A Rust build's UB checks are rustc's (-Zub-checks), whose failure is a
# panic, which the OSS Verify port's hook ends with status 79, and UBSan's in the C code its crates build (which trap);
# and a may-fail halts statement that allows any status says that a panic does not falsify it. A Python build's
# sanitizers instrument its C code: the interpreter, which runs the Python code as bytecode
LANG_BLOCKS = {
    "rust": {"build_ubsan", "note_ubsan", "note_asan-ubsan", "agree_ubsan", "agree_asan-ubsan",
             "fires_ubsan", "fires_asan-ubsan", "stronger"},
    "python": {"agree_asan", "agree_asan-ubsan"},
    # a Go driver calls a Go fuzz function, not LLVMFuzzerTestOneInput
    "go": {"driver_harness"},
}
# the languages whose fuzz targets' Statements.v header says how the port's runtime ends a failure (driver_<language>)
DRIVER_NOTES = ("rust", "python", "go")
# the template block of the project page's compiled sentence, per language (default: compiled, clang alone)
COMPILED = {"rust": "compiled_rust", "python": "compiled_python", "go": "compiled_go"}


def _lang(h, block):
    """The template block for this harness's language."""
    lang = h.project.data["language"]
    return block + "_" + lang if block in LANG_BLOCKS.get(lang, ()) else block


def _port_repository_words(port):
    """The port repository as a project page may publish it: the port's
    name, or a generic phrase for the held port's internal copy."""
    if port["repository"] == schema.INTERNAL_PORT_REPOSITORY:
        return "the internal copy of the OSS Verify port"
    return "`%s`" % port["repository"]


def _project_subject(proj):
    """The public name for a project's statement subjects: "OSS-Fuzz harnesses" or "fuzz targets"."""
    return ("OSS-Fuzz harnesses"
            if "oss_fuzz" in proj.data and not proj.targets(("oss-verify",)) else "fuzz targets")


def _binding_letters(h, st):
    return [chr(ord("a") + i) for i, c in enumerate(h.data["checks"]) if shapes.binds(c, st.data, h.data)]


# --------------------------------------------------------------- Statements.v

def statements_v(h):
    T = "Statements.v.tmpl"
    lib, lib_name = _library(h)
    builds = [b for b, _ in h.builds()]
    header = _t(T, "header",
                subject=_t(T, "subject_" + _origin(h), count=COUNT_WORDS[len(builds)], s="" if len(builds) == 1 else "s",
                           harness=h.name, project=h.project.name, library=lib),
                build_table="\n".join(_t(T, _lang(h, "build_" + b)) for b in builds),
                driver=(_t(T, "driver_api", library_name=lib_name, source=_source_words(h))
                        if h.data["origin"] == "this-repository"
                        else _t(T, _lang(h, "driver_harness"), entry=h.data["entry"])
                        + (_t(T, "driver_" + h.project.data["language"],
                              **({"go": h.project.data["build"]["go"]} if h.project.data["language"] == "go" else {}))
                           if h.project.data["language"] in DRIVER_NOTES else "")),
                checks=_checks_paragraph(h))
    sections, current, firsts = [], None, {}
    rendered = [s for s in _order(h) if s.rendered()]
    for st in _order(h):
        if st.kind != current:
            current = st.kind
            sections.append(_t(T, "section", title=_t(T, "title_" + st.kind)))
        if not st.rendered():
            sections.append(_t(T, "not_rendered", name=st.name, status=PB["statements"][st.status]["words"]))
            continue
        params, body = shapes.term(st.data, project=h.project.data)
        # a statement is written "As [first], for the X build" only after one of the same family; a project's own
        # budget pair is part of the family, so a statement with the project's own pair is stated "As" only one
        # with the same pair, and none on a harness enum is stated "As" one with an own pair
        family = (st.kind, st.data["reading"], st.data.get("abort"), st.data.get("machine"),
                  shapes.exits_key(st.data.get("exits", "any")), shapes.own_budgets(st.data, h.project.data))
        doc = _statement_doc(h, st, firsts.get(family), rendered, lib_name)
        firsts.setdefault(family, st.name)
        sections.append(_t(T, "definition", doc=_comment(doc), name=st.name, params=params, body=body))
    example = rendered[0].name if rendered else "<statement>"
    bounds = [s for s in rendered if s.kind == "bound"]
    proving = _t(T, "proving", project=h.project.name, harness=h.name, example=example,
                 bound_example=_t(T, "bound_example", name=bounds[0].name) if bounds else "")
    return _t(T, "file", project=h.project.name, harness=h.name, header=_comment(header, False),
              rocq=h.data["rocq"], distribution_require=" Distribution" if bounds else "",
              sections="\n" + "\n\n".join(sections) + "\n",
              proving=_comment(proving, False)) + "\n"


def _source_words(h):
    src = h.data["source"]
    if src.get("pending") or not src["files"]:
        return "its source is not in this release yet"
    return ", ".join(src["files"])


def _checks_paragraph(h):
    T = "Statements.v.tmpl"
    checks = h.data["checks"]
    if not checks:
        return _t(T, "checks_none", summary=h.data["summary"], who=_who(h), claim=_no_check_claim(h))
    items = [_t(T, "check_item", letter=chr(ord("a") + i), what=c["what"], stops=_stop(c),
                live=LIVE_WORDS[c["live"]]) for i, c in enumerate(checks)]
    live = _t(T, "live_all") if all(c["live"] is True for c in checks) else _t(T, "live_some")
    return _t(T, "checks_some", summary=h.data["summary"], who=_who(h), items="\n".join(items), live_note=live)


def _no_check_claim(h):
    """What a statement about a harness with no check of its own says."""
    if any(s.kind == "halts" for s in h.statements.values()):
        return "never crashes, hangs or trips a sanitizer"
    return ("never crashes or trips a sanitizer on the runs they cover; with no halts statement, nothing here rules "
            "out a run that never ends")


def ordinal(n):
    suffix = "th" if 10 <= n % 100 <= 20 else {1: "st", 2: "nd", 3: "rd"}.get(n % 10, "th")
    return "%d%s" % (n, suffix)


def witness_words(w):
    """The sentence a page shows for a witness: fixed by its typed fields."""
    if "input_hex" in w:
        hx = w["input_hex"]
        inp = ("the input file `%s`" % " ".join(hx[i:i + 2] for i in range(0, len(hx), 2))) if hx else "an empty input file"
    else:
        inp = "an input file of %s bytes (SHA-256 `%s`)" % (render.thousands(w["input"]["bytes"]), w["input"]["sha256"])
    if "refused" in w:
        r = w["refused"]
        what = {"mmap": "an mmap of %s bytes", "brk": "a brk growth of %s bytes", "mremap": "an mremap to %s bytes"}[
            r["call"]] % render.thousands(r["bytes"])
        head = "with %s, refusing the %s memory request (%s) makes the %s build end in" % (
            inp, ordinal(r["position"]), what, names.BUILD_WORDS[w["build"]])
    else:
        head = "with %s and nothing refused, the %s build ends in" % (inp, names.BUILD_WORDS[w["build"]])
    out = PB["witness"]["outcome"][w["outcome"]]
    if w["outcome"] == "exit":
        out = out.format(exit=w["exit"])
    after = (" " + PB["witness"]["after"][w["after"]]) if w.get("after") else ""
    return "%s %s%s (run under %s)" % (head, out, after, w["runner"])


def gap_of(st):
    """The model-gap features of a statement: its harness's, or its own."""
    return st.harness.data.get("model_gap") or st.data.get("gap") or []


def _statement_doc(h, st, first, rendered, lib_name):
    T = "Statements.v.tmpl"
    d = st.data
    san = d["builds"][-1]
    words = names.BUILD_WORDS[san]
    if st.kind == "halts":
        letters = _binding_letters(h, st)
        binds = ""
        if letters:
            binds = _t(T, "binds_one" if len(letters) == 1 else "binds_many",
                       letters=render.join_words("(%s)" % x for x in letters))
        if first and letters == _binding_letters(h, h.statements[first]):
            binds = ""          # the same as the statement this one is stated like
        ex = d.get("exits", "any")
        block = _lang(h, "note_" + san)
        if block == "note_ubsan_rust" and ex == "any":
            block += "_any"     # a failed rustc UB check exits with status 79, which such a statement allows
        note = _t(T, block)
        rejected = ""
        if ex != "any" and shapes.REJECTED in ex:
            rejected = _t(T, "rejected", where=render.join_words([r["where"] for r in h.data["rejects"]], "and"))
        if d["reading"] == "budget":
            if first:
                return "As [%s], for the %s build.%s%s" % (first, words, binds, note)
            return _t(T, "doc_halts_budget", build=words, budget=shapes.HALTS_BUDGET[1],
                      exits=_exits_words(d), rejected=rejected, binds=binds, note=note, library_name=lib_name)
        twin = names.statement_name("halts", d["builds"], "budget")
        stronger = _t(T, _lang(h, "stronger"), budget_name=twin) if any(s.name == twin for s in rendered) else ""
        if first:
            return "As [%s], for the %s build.%s%s%s" % (first, words, stronger, binds, note)
        has_asan = any(s.kind == "halts" and s.data["reading"] == "may-fail" and "asan" in s.data["builds"][0]
                       for s in rendered)
        return _t(T, "doc_halts_may_fail", build=words, exits=_exits_words(d), rejected=rejected, stronger=stronger,
                  binds=binds, note=note, no_asan="" if has_asan else _t(T, "no_asan", who=_who(h)))
    if st.kind == "agreement":
        budget, san_budget, own = shapes.budget_words(d, h.project.data)
        variant = ""
        if d.get("abort") == "signal":
            variant += _t(T, "variant_abort")
        if d.get("machine") == "rv64gc":
            variant += _t(T, "variant_rv64gc")
        lang = h.project.data["language"]
        # why the pair is read alloc-forced-only: in a Rust target its ASan pairs (the allocation-failure hook's
        # line), in a Python target every pair (CPython aborts when some allocations made at start are refused)
        if (not first and d["reading"] == "alloc-forced-only"
                and (lang == "python" or (lang == "rust" and "asan" in san))):
            variant += _t(T, "variant_alloc_" + lang)
        if own:
            plain_default, san_default = shapes.default_budget_words(san)
            variant += _t(T, "variant_own_budgets", plain=budget, plain_default=plain_default, san=san_budget,
                          san_build=words, san_default=san_default)
        san_note = _t(T, _lang(h, "agree_" + san), library_name=lib_name)
        if first:
            return "As [%s], for the %s build, with %s for the plain build.  %s%s" % (
                first, words, budget, san_note, variant)
        return _t(T, "doc_agreement", plain_budget=budget, environment=_t(T, "env_" + d["reading"]),
                  san_note=san_note, variant=variant,
                  not_claimed=_t(T, "not_claimed_asan") if "asan" in san else "")
    if first:
        return "As [%s], for the %s build." % (first, words)
    if st.kind == "bound":
        return _t(T, "doc_bound", san=words, agrees=names.statement_name("agreement", d["builds"], d["reading"]),
                  name=st.name)
    return _t(T, "doc_decidability", san=words)


# ------------------------------------------------------------ Characterise.v

def characterise_v(h):
    T = "Characterise.v.tmpl"
    rendered = [s for s in _order(h) if s.rendered() and s.kind in ("bound", "decidability")]
    if not rendered:
        return None
    pairs, defs = [], []
    for s in rendered:
        key = (s.data["reading"], s.data["builds"][-1], s.data.get("machine", "rv64g"))
        if key not in pairs:
            pairs.append(key)
    with_bound = {s.data["builds"][-1] for s in rendered if s.kind == "bound"}
    for reading, san, machine in pairs:
        for name, params, body in shapes.templates(reading, san, san in with_bound, machine):
            doc = (_t(T, "doc_classifies", san=names.BUILD_WORDS[san]) if name.endswith("_classifies")
                   else _t(T, "doc_rejects"))
            defs.append(_t(T, "definition", doc=_comment(doc), name=name, params=params, body=body))
    any_bound = bool(with_bound)
    header = _t(T, "header", and_bound=_t(T, "and_bound") if any_bound else "",
                and_rejects=_t(T, "and_rejects") if any_bound else "",
                and_claim=_t(T, "and_claim") if any_bound else "")
    return _t(T, "file", project=h.project.name, harness=h.name, header=_comment(header, False),
              rocq=h.data["rocq"], distribution_require=" Distribution" if any_bound else "",
              definitions="\n" + "\n\n".join(defs)) + "\n"


# ------------------------------------------------------- Images.v, dune files

def images_v(h):
    T = "Images.v.tmpl"
    builds = [b for b, _ in h.builds()]
    return _t(T, "file", project=h.project.name, harness=h.name, count=COUNT_WORDS[len(builds)].lower(),
              s="s" if len(builds) > 1 else "", header=_comment(_t(T, "header"), False), rocq=h.data["rocq"],
              modules=" ".join(names.BUILD_MODULE[b] for b in builds),
              definitions="\n".join(_t(T, "definition", ident=names.BUILD_IDENT[b], module=names.BUILD_MODULE[b])
                                    for b in builds),
              lemmas="\n".join(_t(T, "lemma", ident=names.BUILD_IDENT[b]) for b in builds)) + "\n"


def hex_targets(module, segments):
    out = []
    for i, chunks in enumerate(segments):
        if chunks == 1:
            out.append("%s_seg_%03d.hex" % (module, i))
        else:
            out.extend("%s_seg_%03d_chunk_%03d.hex" % (module, i, j) for j in range(chunks))
    return out


def images_dune(h):
    T = "images-dune.tmpl"
    rules_ = []
    for b, rec in h.builds():
        m = names.BUILD_MODULE[b]
        rules_.append(_t(T, "rule", targets=" ".join([m + ".v"] + hex_targets(m, rec["segments"])),
                         elf=h.elf_path(b), module=m, namespace=h.data["rocq"] + ".images"))
    return _t(T, "file", rules="\n".join(rules_)) + "\n"


def harness_dune(h):
    return _t("harness-dune.tmpl", "file", rocq=h.data["rocq"], package=names.opam_package(h.project.name),
              theories=THEORY_DEPS) + "\n"


def proof_dune(tree, sid):
    p, hn, s = sid.split("/")
    lib = (" " + names.rocq_proof(p, hn, "lib")) if "%s/%s" % (p, hn) in tree.proof_libs else ""
    return _t("proof-dune.tmpl", "file", rocq=names.rocq_proof(p, hn, s),
              package=names.opam_package(p) + "-proofs",
              theories=PROOF_THEORY_DEPS + " " + names.rocq_harness(p, hn) + lib) + "\n"


def proof_lib_dune(p, hn):
    return _t("proof-dune.tmpl", "lib", rocq=names.rocq_proof(p, hn, "lib"),
              package=names.opam_package(p) + "-proofs",
              theories=PROOF_THEORY_DEPS + " " + names.rocq_harness(p, hn)) + "\n"


def dune_project(tree):
    T = "dune-project.tmpl"
    pk = []
    for proj in sorted(tree.available(), key=lambda p: p.name):
        if "assets" not in proj.data:
            continue                    # every binary withheld: nothing to build, so no package
        pk.append(_t(T, "package", name=names.opam_package(proj.name),
                     synopsis="Theorem statements about %s's %s" % (proj.name, _project_subject(proj))))
    with_proofs = sorted({sid.split("/")[0] for sid in tree.proofs} | {u.split("/")[0] for u in tree.proof_libs})
    for p in with_proofs:
        pk.append(_t(T, "package", name=names.opam_package(p) + "-proofs",
                     synopsis="Proofs of statements about %s's %s" % (p, _project_subject(tree.projects[p]))))
    r = tree.release
    rv = r["rocq"]["version"].split(".")
    return _t(T, "file", packages=("\n" + "\n\n".join(pk)) if pk else "", rocq_min="%s.%s" % (rv[0], rv[1]),
              rocq_next="%s.%d" % (rv[0], int(rv[1]) + 1), lps_name=r["semantics"]["name"]) + "\n"


def project_opam(tree, proj):
    r = tree.release
    rv = r["rocq"]["version"].split(".")
    a = proj.data["assets"]["bin"]
    return _t("project.opam.tmpl", "file", package=names.opam_package(proj.name), release=r["release"],
              project=proj.name, subject=_project_subject(proj), rocq_min="%s.%s" % (rv[0], rv[1]),
              rocq_next="%s.%d" % (rv[0], int(rv[1]) + 1), lps_name=r["semantics"]["name"],
              bin_file=a["file"], bin_release=a["release"], bin_sha256=a["sha256"]) + "\n"


# ------------------------------------------------------------- Distribution.v

def distribution_header(h):
    T = "Distribution-header.v.tmpl"
    d = h.data["distribution"]
    comps = []
    hexs = d.get("prefix_hex", "")
    spaced = " ".join(hexs[i:i + 2] for i in range(0, len(hexs), 2))
    if "prefix" in d:
        prefix = _t(T, "prefix_long", n=render.thousands(d["prefix"]["bytes"]), sha=d["prefix"]["sha256"])
    elif hexs == "0" * 12:
        prefix = _t(T, "prefix_header", n=6, hex=spaced)
    elif hexs.startswith("0" * 12):
        rest = hexs[12:]
        prefix = _t(T, "prefix_header_and_payload", hex=" ".join(rest[i:i + 2] for i in range(0, len(rest), 2)))
    else:
        prefix = _t(T, "prefix_other", n=len(hexs) // 2, hex=spaced)
    pl = d["payload"]
    alphabet = (_t(T, "alphabet_bytes") if pl["alphabet"] == "bytes"
                else _t(T, "alphabet_custom", size=pl.get("alphabet_size", "?")) if pl["alphabet"] == "custom"
                else _t(T, "alphabet_named", name=pl["alphabet"], size=pl.get("alphabet_size", "?")))
    q = lambda s: '"%s"' % render.rocq_comment_text(s)
    c = d["components"]
    comps.append(_t(T, "payload", weight=c["payload"], argv0=q(d["argv0"]), input_file=q(d["input_file"]),
                    prefix=prefix, alphabet=alphabet, p=pl["p"], mean=render.thousands(pl["mean_bytes"])))
    comps.append(_t(T, "wrong_argc", weight=c["wrong_argc"], input_file=d["input_file"]))
    comps.append(_t(T, "missing_file", weight=c["missing_file"], input_file=d["input_file"], argv0=q(d["argv0"])))
    if "envp" in c:
        comps.append(_t(T, "envp", weight=c["envp"], input_file=d["input_file"],
                        envp=render.join_words((render.rocq_comment_text(e) for e in d.get("envp", [])), "or")))
    comps.append(_t(T, "full_support", weight=c["full_support"]))
    text = _t(T, "text", mass=d["mass"], components="\n".join(comps))
    return _t(T, "file", project=h.project.name, harness=h.name, text=render.wrap(text, 80, "    "))


def distribution_v(h):
    body = h.distribution_body()
    return distribution_header(h) + "\n" + (body if body is not None else "")


# --------------------------------------------------------------- READMEs

def _check_place(c):
    """'lines 66-74' or 'line 71': where a check is, as its README row names it."""
    rng = c["where"].rpartition(":")[2]
    return ("lines %s" if "-" in rng else "line %s") % rng


def _statement_line(h, st):
    T = "harness-README.md.tmpl"
    d = st.data
    san = names.BUILD_WORDS[d["builds"][-1]]
    if st.kind == "halts":
        if d["reading"] == "budget":
            letters = _binding_letters(h, st)
            if not letters:
                binds = ""
            elif len(letters) == len(h.data["checks"]):
                binds = "; so the check above holds" if len(letters) == 1 else "; so the checks above hold"
            else:
                bound = [_check_place(c) for i, c in enumerate(h.data["checks"]) if chr(ord("a") + i) in letters]
                binds = "; so the %s at %s above %s" % ("check" if len(bound) == 1 else "checks",
                                                        render.join_words(bound), "holds" if len(bound) == 1 else "hold")
            return _t(T, "line_halts_budget", budget=shapes.HALTS_BUDGET[1], build=san, exits=_exits_words(d),
                      binds=binds)
        return _t(T, "line_halts_may_fail", build=san, exits=_exits_words(d))
    if st.kind == "agreement":
        v = []
        if d.get("abort") == "signal":
            v.append("abort read as SIGABRT")
        if d.get("machine") == "rv64gc":
            v.append("RV64GC")
        if d["reading"] == "alloc-forced-only":
            v.append("memory refused only when forced")
        block = _lang(h, "fires_" + d["builds"][-1])
        fires = _t(T, block if block.endswith("_rust") else "fires", san=san)
        budget, san_budget, own = shapes.budget_words(d, h.project.data)
        return _t(T, "line_agreement", fires=fires, budget=budget, variant="".join("; " + x for x in v),
                  own=_t(T, "own_budgets", plain=budget, san=san_budget) if own else "")
    return _t(T, "line_" + st.kind, san=san)


def status_cell(tree, st, root="../../../"):
    """The status of a statement in words; `root` is the way from the page to
    the repository root (a harness page is three levels down, a project page
    two)."""
    w = PB["statements"][st.status]["words"]
    if st.status in ("proved", "refuted"):
        at = (" at b = %s" % st.proof.data["bound"]) if st.kind == "bound" and "bound" in st.proof.data else ""
        return "[%s](%s%s/)%s" % (w, root, st.proof.path, at)
    if st.status == "counterexample":
        return "[%s](%s%s/)" % (w, root, st.counterexample.path)
    if st.status == "suspected-false":
        return "%s: %s" % (w, render.md_cell(st.data["reason"]))
    if st.status == "witnessed-false":
        return "%s: %s" % (w, render.md_cell(witness_words(st.data["witness"])))
    if st.status == "withheld":
        return "%s: %s" % (w, PB["withheld"][st.data["withheld"]])
    if st.status == "model-gap" and st.data.get("gap"):
        return "%s: the binary %s" % (w, facts.feature_words(st.data["gap"]))
    if st.kind == "bound" and st.status == "open":
        return "open (best proved b: none)"
    return w


def why_words(st):
    """Why a statement that is not open or proved has its status."""
    return {"suspected-false": lambda: render.md_cell(st.data["reason"]),
            "witnessed-false": lambda: render.md_cell(witness_words(st.data["witness"])),
            "model-gap": lambda: (("each binary " if st.harness.data.get("model_gap") else "the binary ")
                                  + facts.feature_words(gap_of(st))
                                  + ("" if st.harness.data.get("model_gap") else ", which the model does not cover yet")),
            "withheld": lambda: PB["withheld"][st.data["withheld"]],
            "withdrawn": lambda: render.md_cell(st.data["reason"]),
            "counterexample": lambda: (("the run recorded for [%s](../%s/) refutes it too: there the %s build dies by "
                                        "%s, an error this statement forbids"
                                        % (st.counterexample.data["statement"], st.counterexample.path,
                                           names.BUILD_WORDS[st.counterexample.data["observed"]["build"]],
                                           st.counterexample.data["observed"]["signal"]))
                                       if st.derived_counterexample
                                       else render.md_cell(st.counterexample.data["note"])),
            "refuted": lambda: "a Rocq proof of its negation"}[st.status]()


def harness_readme(tree, h):
    T = "harness-README.md.tmpl"
    lib, lib_name = _library(h)
    src = h.data["source"]
    if src.get("pending"):
        source_link = _t(T, "source_pending")
    else:
        source_link = _t(T, "source_link", file=src["files"][0],
                         modified="modified; see below" if src["modified"] else "unmodified")
    intro = _t(T, "intro_" + _origin(h), harness=h.name, project=h.project.name, library=lib,
               library_name=lib_name, source_link=source_link)
    mods = ""
    if h.data["modifications"]:
        # a target OSS-Fuzz does not run differs from a libFuzzer build of it, not from what OSS-Fuzz runs
        block = ("modifications_libfuzzer" if _origin(h) in ("oss-verify", "upstream_no_oss_fuzz")
                 else "modifications")
        mods = "\n" + _t(T, block, items="\n".join("- " + m for m in h.data["modifications"])) + "\n"

    def link(where):
        f, _, rng = where.rpartition(":")
        a, _, b = rng.partition("-")
        anchor = "L%s-L%s" % (a, b) if b else "L%s" % a
        return f, anchor
    checks = []
    for c in h.data["checks"]:
        f, anchor = link(c["where"])
        checks.append(_t(T, "check_row", what=c["what"].rstrip("."), lines=_check_place(c),
                         file=f, anchor=anchor, stops=_stop(c), live=LIVE_WORDS[c["live"]]))
    if checks:
        halts = [s for s in h.statements.values() if s.kind == "halts"]
        bound = [c for i, c in enumerate(h.data["checks"])
                 if any(chr(ord("a") + i) in _binding_letters(h, s) for s in halts)]
        every = len(bound) == len(h.data["checks"]) and all(
            len(_binding_letters(h, s)) == len(h.data["checks"]) for s in halts)
        others = len(h.data["checks"]) - len(bound)
        if every:
            checks.append("\n" + _t(T, "checks_bind", that="them" if len(h.data["checks"]) > 1 else "it"))
        elif bound:
            places = render.join_words(_check_place(c) for c in bound)
            subject = ("any of the checks at %s" % places) if len(bound) > 1 else ("the check at %s" % places)
            text = _t(T, "checks_bind_some", subject=subject, that="them" if len(bound) > 1 else "it")
            if others:   # every check can be bound by some halts statement and still not by every one
                text += " " + _t(T, "checks_bind_others", others="checks" if others > 1 else "check")
            checks.append("\n" + text)
    else:
        checks.append(_t(T, "checks_none", who=_who(h), claim=_no_check_claim(h)))
    if h.data.get("rejects"):
        reject_rows = []
        for r in h.data["rejects"]:
            f, anchor = link(r["where"])
            reject_rows.append(_t(T, "reject_row", what=r["what"].rstrip("."), lines=_check_place(r), file=f,
                                  anchor=anchor))
        checks.append("\n" + _t(T, "rejects", who=_who(h), status=shapes.REJECTED, rows="\n".join(reject_rows)))
        returning = [c["where"][len("source/"):] for c in h.data["checks"] if c["stops_with"] == "return-only"]
        if returning:
            checks.append("\n" + _t(T, "rejects_return_only", status=shapes.REJECTED,
                                    lines=render.join_words(returning, "and")))
    files = ["[Statements.v](Statements.v)"] if h.builds() else []
    if characterise_v(h) is not None and h.builds():
        files.append("[Characterise.v](Characterise.v)")
    if "distribution" in h.data:
        files.append("[Distribution.v](Distribution.v)")
    gap = ""
    if h.data.get("model_gap"):
        gap = "\n" + _t(T, "model_gap", features=facts.feature_words(h.data["model_gap"])) + "\n"
    else:
        own = sorted({f for s in h.statements.values() if s.status == "model-gap" for f in s.data.get("gap", [])})
        if own:
            gap = "\n" + _t(T, "model_gap_some", features=facts.feature_words(own)) + "\n"
    rows = [_t(T, "row", name=s.name, line=_statement_line(h, s), status=status_cell(tree, s)) for s in _order(h)]
    brows = []
    for b, rec in h.builds(published_only=False):
        if rec.get("withheld"):
            brows.append(_t(T, "build_row_withheld", build=b, file=rec["file"], why=PB["withheld"][rec["withheld"]]))
        else:
            brows.append(_t(T, "build_row", build=b, file=rec["file"], bytes=render.thousands(rec["bytes"]),
                            sha=rec["sha256"]))
    check_it = (_t(T, "check_it", project=h.project.name, harness=h.name) if h.builds()
                else _t(T, "check_it_none"))
    urows = []
    for b, rec in h.builds():
        items = []
        for u in rec.get("uninstrumented") or []:
            src = (" from `%s`" % u["source"]) if u.get("source") else ""
            words = ("the OSS Verify port's driver" if u["kind"] == "driver" and facts.port(h.project)
                     else UNINSTRUMENTED_WORDS[u["kind"]])
            items.append("`%s`%s (%s)" % (u["name"], src, words))
        if items:
            urows.append(_t(T, "uninstrumented_row", build=b, items=", ".join(items)))
    if urows:
        uninstrumented = "\n" + _t(T, "uninstrumented", rows="\n".join(urows)) + "\n"
    elif h.builds() and h.project.data["language"] != "go":    # Go builds link no toolchain runtime and no sanitizer
        uninstrumented = "\n" + _t(T, "uninstrumented_none") + "\n"
    else:
        uninstrumented = ""
    return _t(T, "file", project=h.project.name, harness=h.name, intro=intro, summary=h.data["summary"],
              modifications=mods, who=_who(h), checks="\n".join(checks),
              files=", ".join(files) if files else "withheld", model_gap=gap, statement_rows="\n".join(rows),
              build_rows="\n".join(brows), uninstrumented=uninstrumented, check_it=check_it) + "\n"


def _counts(statements):
    c = {"n": 0, "proved": 0, "false": 0, "suspected": 0, "model_gap": 0, "withheld": 0, "open": 0}
    for s in statements:
        if s.status == "withdrawn":
            continue
        c["n"] += 1
        c["proved"] += s.status == "proved"
        c["false"] += s.status in FALSE_STATUSES
        c["suspected"] += s.status == "suspected-false"
        c["model_gap"] += s.status == "model-gap"
        c["withheld"] += s.status == "withheld"
        c["open"] += s.status == "open"
    return c


def _lead(tree, proj):
    T = "project-README.md.tmpl"
    d = proj.data
    if "oss_fuzz" in d:
        url = "https://github.com/google/oss-fuzz/tree/%s/projects/%s" % (d["oss_fuzz"]["commit"], proj.name)
        if d.get("homepage"):
            links = _t(T, "links_homepage", homepage=d["homepage"], homepage_label=facts.repo_label(d["homepage"]),
                       project=proj.name, oss_fuzz_url=url)
        else:
            links = _t(T, "links_oss_fuzz", project=proj.name, oss_fuzz_url=url)
    elif d.get("homepage"):
        links = _t(T, "links_homepage_no_oss_fuzz", homepage=d["homepage"],
                   homepage_label=facts.repo_label(d["homepage"]), project=proj.name)
    else:
        links = _t(T, "links_no_oss_fuzz", project=proj.name)
    desc = d.get("description", "")
    return _t(T, "lead", description=(desc.rstrip(".") + ". ") if desc else "", links=links)


PLACEHOLDER_DIGEST = "0" * 64


def _check_summary(ch):
    """The checks cell of a project page's table: how many, what kinds, how
    many of them weak, and how many were confirmed in the binary."""
    if not ch:
        return "none"
    n_live = sum(1 for x in ch if x["live"] is True)
    n_weak = sum(1 for x in ch if x["strength"] == "weak")
    kinds = sorted({x["kind"] for x in ch})
    parts = [", ".join(kinds)]
    if n_weak:
        parts.append("%d weak" % n_weak)
    parts.append("all confirmed in the binary" if n_live == len(ch) else "%d confirmed in the binary" % n_live)
    return "%s (%s)" % (render.plural(len(ch), "check", "checks"), "; ".join(parts))


def _coverage(T, block, targets, included, api_note, **values):
    """One coverage sentence of the status line: of these harness entries (targets), how many (included) have
    statements."""
    return _t(T, block, n_included=len(included), n_targets=len(targets),
              have=("fuzz target" if len(targets) == 1 else "fuzz targets")
              + (" has" if len(included) == 1 else " have"),
              api_note=api_note, **values)


def project_readme(tree, proj):
    T = "project-README.md.tmpl"
    d = proj.data
    status = d["status"]
    if status != "available":
        return _t(T, "file_short", project=proj.name, lead=_lead(tree, proj),
                  status_words=PB["projects"][status]["words"], sentence=facts.project_sentence(proj)) + "\n"
    hs = [proj.harnesses[e["name"]] for e in proj.entries() if e["status"] == "included" and e["name"] in proj.harnesses]
    oss_fuzz_targets = proj.targets()
    oss_verify_targets = proj.targets(("oss-verify",))
    included = [e for e in oss_fuzz_targets if e["status"] == "included"]
    oss_verify_included = [e for e in oss_verify_targets if e["status"] == "included"]
    api = any(e["name"] == names.API_DRIVER and e["status"] == "included" for e in proj.entries())
    stmts = [s for h in hs for s in h.statements.values()]
    c = _counts(stmts)
    builds = [(h, b, rec) for h in hs for b, rec in h.builds()]
    n_held = sum(1 for h in hs for _b, r in h.builds(published_only=False) if r.get("withheld"))
    wh = d.get("withheld") or {}
    lib = d["library"]
    withheld = ""
    if wh.get("unpublished"):
        withheld += _t(T, "withheld_unpublished")
    if wh.get("source_bundle"):
        withheld += _t(T, "withheld_source_bundle", library_name=lib["name"])
    patches = d.get("patches", [])
    glance = []
    for h in hs:
        hc = _counts(h.statements.values())
        parts = ["%d" % hc["n"]]
        for k, w in (("proved", "proved"), ("false", "known false"), ("suspected", "suspected false"),
                     ("model_gap", "blocked by the model"), ("withheld", "withheld")):
            if hc[k]:
                parts.append("%d %s" % (hc[k], w))
        glance.append(_t(T, "glance_row", name=h.name, summary=render.md_cell(h.data["summary"]),
                         checks=_check_summary(h.data["checks"]), counts=", ".join(parts)))
    not_inc = [e for e in proj.entries() if e["status"] == "not-included"]
    not_included = ""
    if not_inc:
        not_included = "\n" + _t(T, "not_included", items="; ".join(
            _t(T, "not_included_item", name=e["name"], reason=facts.harness_reason(proj, e)) for e in not_inc)) + "\n"
    fams = []
    kinds = {(s.kind, s.data["reading"]) for s in stmts if s.status != "withdrawn"}
    if ("halts", "budget") in kinds:
        by_words = {}
        for s in stmts:
            if s.kind == "halts" and s.data["reading"] == "budget":
                by_words.setdefault(_exits_words(s.data), set()).add(s.harness.name)
        common = max(sorted(by_words), key=lambda w: len(by_words[w]))
        others = ["%s for %s" % (w, render.join_words(sorted(by_words[w]), "and")) for w in sorted(by_words) if w != common]
        fams.append(_t(T, "family_halts", exits=common + (" (%s)" % "; ".join(others) if others else "")))
    if ("halts", "may-fail") in kinds:
        ex = {_exits_words(s.data) for s in stmts if s.kind == "halts" and s.data["reading"] == "may-fail"}
        fams.append(_t(T, "family_halts_may_fail", exits=" or ".join(sorted(ex))))
    for k in ("agreement", "bound", "decidability"):
        if any(s.kind == k for s in stmts):
            fams.append(_t(T, "family_" + k + ("_rust" if k == "agreement" and d["language"] == "rust" else "")))
    binding = ""
    bitems = []
    for h in hs:
        whats = [c_["what"] for i, c_ in enumerate(h.data["checks"])
                 if any(shapes.binds(c_, s.data, h.data) for s in h.statements.values())]
        if whats:
            bitems.append(_t(T, "binding_item", name=h.name,
                             whats="; ".join(render.lower_first(w.rstrip(".")) for w in whats)))
    if bitems:
        binding = "\n" + _t(T, "binding", items="\n".join(bitems)) + "\n"
    issues = []
    for h in hs:
        gap_done = False
        reasons = {s.data.get("withheld") for s in h.statements.values() if s.status == "withheld"}
        if h.statements and len(reasons) == 1 and all(s.status == "withheld" for s in h.statements.values()):
            issues.append(_t(T, "issue_row", what="%s: every statement" % h.name,
                             status=PB["statements"]["withheld"]["words"], why=PB["withheld"][reasons.pop()]))
            continue
        for s in _order(h):
            if s.status in ("open", "proved", "withdrawn"):
                continue
            if s.status == "model-gap" and h.data.get("model_gap"):
                if not gap_done:
                    issues.append(_t(T, "issue_row", what="%s: every statement" % h.name,
                                     status=PB["statements"]["model-gap"]["words"],
                                     why="each binary %s" % facts.feature_words(h.data["model_gap"])))
                    gap_done = True
                continue
            issues.append(_t(T, "issue_row", what="%s `%s`" % (h.name, s.name),
                             status=PB["statements"][s.status]["words"]
                             if s.status != "counterexample" else status_cell(tree, s, root="../../"),
                             why=why_words(s).replace("](../", "](../../")))
    issues_txt = _t(T, "issues_table", rows="\n".join(issues)) if issues else _t(T, "issues_none")
    pitems = [_t(T, "patch_item", id=p_["id"], summary=p_["summary"].rstrip("."), upstream=UPSTREAM_WORDS[p_["upstream"]])
              for p_ in patches]
    n_unlisted = lib.get("patch_count", 0) - len(patches)
    if n_unlisted > 0:
        pitems.append(_t(T, "patch_unlisted", n=render.plural(n_unlisted, "patch", "patches"),
                         more=" more" if patches else ""))
    mods = [h.name for h in hs if h.data["source"]["modified"]]
    harness_mods = ("the harness files are modified in %s (see each harness page)%s"
                    % (render.join_words("`%s`" % m for m in mods),
                       "; the others are unmodified" if len(mods) < len(hs) else "")) if mods else "unmodified"
    proofs = [(sid, pd) for sid, pd in sorted(tree.proofs.items()) if sid.split("/")[0] == proj.name]
    if proofs:
        ptxt = _t(T, "proofs_table", rows="\n".join(
            _t(T, "proof_row", id=sid, path="../../" + pd.path, result="refuted" if pd.refutes else "proved")
            for sid, pd in proofs))
    else:
        ptxt = _t(T, "proofs_none")
    notes = ("\n" + _t(T, "notes", text=proj.notes) + "\n") if proj.notes else ""
    a = d.get("assets") or {}
    src = a.get("src")
    rel = lambda tag: "%s/releases/tag/%s" % (REPO_URL, tag)
    recipe = facts.bin_recipe(tree, proj)
    this = ("v" + tree.release["release"], "v" + tree.release["release"] + "-src")

    def recipe_text():
        """The recipe the binary archive pins: beside the source asset, in this release or an earlier one, or in a
        release of its own, named apart."""
        if recipe and recipe["release"] != src["release"]:
            return _t(T, "recipe_apart", recipe_file=recipe["file"], recipe_release=recipe["release"],
                      recipe_url=rel(recipe["release"]))
        return _t(T, "recipe_this_release" if src["release"] in this else "recipe_that_release",
                  recipe_file=recipe["file"] if recipe else "(none)")

    oss_fuzz_runs_all = "oss_fuzz" in d and not oss_verify_targets
    get = (_t(T, "get_binaries", project=proj.name, bin_file=a["bin"]["file"], bin_release=a["bin"]["release"],
              bin_url=rel(a["bin"]["release"]),
              testcase="an OSS-Fuzz testcase" if oss_fuzz_runs_all else "a testcase")
           if "bin" in a else _t(T, "get_none"))
    licences = sorted({h.data["licence"] for h in hs})
    lib_licences = sorted({h.data["library"]["licence"] for h in hs} | {lib["licence"]})
    known_lib = [x for x in lib_licences if x != "NOASSERTION"]
    builder = d["build"]["builder"]
    port = facts.port(proj)
    copyleft_sentence = _copyleft_sources(tree, T, hs)
    # each group of fuzz targets has its own coverage sentence: OSS-Fuzz's, the project's own when OSS-Fuzz does not
    # have the project, and those OSS Verify builds; an API driver is noted with the first
    api_note = _t(T, "api_note") if api else ""
    sentences = []
    if "oss_fuzz" in d:
        sentences.append(_coverage(T, "coverage", oss_fuzz_targets, included, api_note))
        api_note = ""
    own_targets = [] if "oss_fuzz" in d else proj.targets(("upstream",))
    if own_targets:
        sentences.append(_coverage(T, "coverage_own", own_targets, [e for e in own_targets if e["status"] == "included"],
                                   api_note, project=proj.name))
        api_note = ""
    if oss_verify_targets:
        sentences.append(_coverage(T, "coverage_oss_verify", oss_verify_targets, oss_verify_included, api_note))
    coverage = " ".join(sentences)
    return _t(T, "file_available", project=proj.name, lead=_lead(tree, proj), coverage=coverage,
              sources=("project.yaml, */harness.yaml, proofs/, counterexamples/ and notes/%s.md" % proj.name
                       if proj.notes else "project.yaml, */harness.yaml, proofs/ and counterexamples/"),
              binaries=(_t(T, "binaries_some", n_binaries=render.plural(len(builds), "binary", "binaries"),
                           bytes=render.human_bytes(sum(r["bytes"] for _, _, r in builds)),
                           held=(", %d more withheld" % n_held) if n_held else "")
                        if builds else _t(T, "binaries_none")),
              counts=_t(T, "counts", n_statements=render.thousands(c["n"]), n_open=render.thousands(c["open"]),
                        n_proved=c["proved"], n_false=c["false"], n_suspected=c["suspected"],
                        n_model_gap=c["model_gap"],
                        withheld_part=(", %s withheld" % render.thousands(c["withheld"])) if c["withheld"] else ""),
              withheld=withheld, library_name=lib["name"],
              library_version=(lib["version"] + " ") if lib.get("version") else "",
              pin_short=("commit `%s`" % lib["commit"][:8]) if "commit" in lib
              else ("release archive `%s`" % lib["archive_sha256"][:8]),
              patches_note=_t(T, "patches_note", n_patches=render.plural(max(len(patches), lib.get("patch_count", 0)),
                                                                          "patch", "patches"))
              if patches or lib.get("patch_count") else "",
              glance_rows="\n".join(glance), not_included=not_included, families="\n".join(fams), binding=binding,
              issues=issues_txt, get_binaries=get,
              library_repo=lib["repository"],
              library_label=facts.repo_label(lib["repository"]),
              pin_long=("at `%s`" % lib["commit"]) if "commit" in lib
              else ("from the release archive whose SHA-256 is `%s`" % lib["archive_sha256"]),
              library_version_paren=(" (%s)" % lib["version"]) if lib.get("version") else "",
              build_system=PB["build_systems"][d["build"]["system"]],
              patch_items=(":\n" + "\n".join(pitems)) if pitems else "",
              harness_mods=harness_mods,
              # each block takes only its own toolchain's version, so a missing one fails here rather than render "None"
              compiled=(_t(T, "compiled_go", go=d["build"]["go"]) if d["language"] == "go"
                        else _t(T, COMPILED.get(d["language"], "compiled"), clang=d["build"]["clang"])),
              # a Go project's binaries run the port's patched Go runtime: the page says what the patches change
              runtime_item=(_t(T, "runtime_go", go=d["build"]["go"]) + "\n") if d["language"] == "go" else "",
              builder_sentence=(_t(T, "builder_unpublished") if builder.endswith(PLACEHOLDER_DIGEST)
                                else _t(T, "builder_port", builder=builder, port_path=port["path"],
                                        port_commit=port["commit"], port_repository=_port_repository_words(port),
                                        port_file=a["port"]["file"], port_url=rel(a["port"]["release"]),
                                        src_file=src["file"])
                                if port and src and "port" in a
                                else _t(T, "builder_port_no_archive", builder=builder, port_path=port["path"],
                                        port_commit=port["commit"], port_repository=_port_repository_words(port)) if port
                                else _t(T, "builder_published", builder=builder) if src
                                else _t(T, "builder_no_source", builder=builder)),
              proofs=ptxt, notes=notes,
              library_licence_sentence=(_t(T, "library_licence_copyleft", library_name=lib["name"])
                                        if not known_lib and wh.get("source_bundle") else
                                        _t(T, "library_licence_unknown", library_name=lib["name"])
                                        if not known_lib else
                                        _t(T, "library_licence_known", library_name=lib["name"],
                                           library_licence=render.join_words("`%s`" % x for x in known_lib)
                                           + (" (for some of its harnesses' builds; the others are not recorded yet)"
                                              if "NOASSERTION" in lib_licences else ""))),
              binary_licence_sentence=(_t(T, "binary_licences_unknown" + ("_go" if d["language"] == "go" else ""),
                                          library_name=lib["name"])
                                       if not licences or "NOASSERTION" in licences else
                                       _t(T, "binary_licences_known",
                                          binary_licences=render.join_words("`%s`" % x for x in licences))),
              source_sentence=(_t(T, "source_with_port", src_file=src["file"], src_release=src["release"],
                                  src_url=rel(src["release"]), manifest_file=a["src_manifest"]["file"],
                                  port_file=a["port"]["file"], port_release=a["port"]["release"],
                                  port_url=rel(a["port"]["release"]), port_path=port["path"],
                                  port_commit=port["commit"]) if src and port else
                               _t(T, "source_with_bundle", src_file=src["file"], src_release=src["release"],
                                  src_url=rel(src["release"]),
                                  manifest_file=(a.get("src_manifest") or {}).get("file", "(none)"),
                                  recipe=recipe_text())
                               if src else _t(T, "source_none")),
              copyleft_sentence=copyleft_sentence) + "\n"


def _copyleft_sources(tree, T, hs):
    """The sentence naming the release-wide source archives a copyleft binary's corresponding source also takes: the
    toolchain for every published copyleft harness, and the build image's libraries for those that link one."""
    srcs = (tree.release or {}).get("sources")
    cl = [h for h in hs if h.builds() and facts.copyleft(tree, h)]
    if not cl or not srcs:
        return ""
    linking = [h for h in cl if facts.image_libraries(h)]
    names_of = lambda group: render.join_words("`%s`" % h.name for h in group)
    who = (_t(T, "copyleft_who_all") if len(cl) == len(hs)
           else _t(T, "copyleft_who_some", harnesses=names_of(cl)))
    if not linking:
        sysroot = ""
    elif len(linking) == len(cl):
        sysroot = _t(T, "copyleft_sysroot", sysroot_file=srcs["sysroot"]["file"])
    else:
        sysroot = _t(T, "copyleft_sysroot_some", sysroot_file=srcs["sysroot"]["file"], harnesses=names_of(linking))
    return " " + _t(T, "copyleft_sources", who=who, toolchain_file=srcs["toolchain"]["file"], sysroot=sysroot,
                    sources_release=srcs["release"],
                    sources_url="%s/releases/tag/%s" % (REPO_URL, srcs["release"]))


# ------------------------------------------------------- top-level and index

def _project_row_counts(proj):
    return _counts([s for h in proj.harnesses.values() for s in h.statements.values()])


def _n_builds(proj, published):
    return sum(1 for h in proj.harnesses.values() for _b, r in h.builds(published_only=False)
               if bool(r.get("withheld")) != published)


def status_md(tree):
    T = "STATUS.md.tmpl"
    r = tree.release
    not_in_oss_fuzz = tree.not_in_oss_fuzz()
    projects = render.join_words("`%s`" % n for n in not_in_oss_fuzz)
    totals, rows = [], []
    for status, spec in PB["projects"].items():
        n = sum(1 for p in tree.projects.values() if p.data["status"] == status)
        if n:
            totals.append(_t(T, "total_row", words=spec["words"], n=render.thousands(n)))
    for proj in sorted(tree.projects.values(), key=lambda p: p.name):
        d = proj.data
        c = _project_row_counts(proj)
        if d["status"] == "available":
            # every fuzz target: OSS-Fuzz's, the project's own and those OSS Verify builds; not the API driver
            targets = proj.targets(facts.OSS_FUZZ_ORIGINS + ("oss-verify",))
            inc = sum(1 for e in targets if e["status"] == "included")
            t = "%d of %d" % (inc, len(targets))
            if any(e["name"] == names.API_DRIVER and e["status"] == "included" for e in proj.entries()):
                t += " + API driver"
            bins = "%d" % _n_builds(proj, True)
            held = _n_builds(proj, False)
            if held:
                bins += " (%d withheld)" % held
        else:
            t, bins = "-", "-"
        rows.append(_t(T, "row", project=proj.name, language=d["language"], words=PB["projects"][d["status"]]["words"],
                       targets=t, binaries=bins, statements=render.thousands(c["n"]), open=c["open"], proved=c["proved"],
                       false=c["false"], suspected=c["suspected"], blocked=c["model_gap"], withheld=c["withheld"]))
    return _t(T, "file", release=r["release"], oss_fuzz_commit8=r["oss_fuzz"]["commit"][:8], totals="\n".join(totals),
              title="Status of every project" if not_in_oss_fuzz else "Status of every OSS-Fuzz project",
              language_note=_t(T, "language_note") if not_in_oss_fuzz else "",
              not_in_oss_fuzz_note=_t(T, "not_in_oss_fuzz_note", projects=projects,
                                      pronoun="it" if len(not_in_oss_fuzz) == 1 else "them")
              if not_in_oss_fuzz else "",
              n_projects=render.thousands(len(tree.projects)), rows="\n".join(rows)) + "\n"


def statement_counts(tree):
    """{status: n} over every statement that is not withdrawn, plus the
    withheld ones by reason: the one place the README and the changelog take
    their numbers from."""
    by = {k: 0 for k in PB["statements"]}
    held = {k: 0 for k in PB["withheld"]}
    n = 0
    for s in tree.statements():
        if s.status == "withdrawn":
            continue
        n += 1
        by[s.status] += 1
        if s.status == "withheld":
            held[s.data["withheld"]] += 1
    return n, by, held


def counts_sentence(tree):
    """The statement counts in words, every status named, zeros included."""
    n, by, held = statement_counts(tree)
    if not n:
        return "no statements yet"
    th = render.thousands
    false = sum(by[k] for k in FALSE_STATUSES)
    parts = ["%s proved" % th(by["proved"]),
             "%s known false (%s counterexample%s, %s false (witnessed)%s)" % (
                 th(false), th(by["counterexample"]), "" if by["counterexample"] == 1 else "s",
                 th(by["witnessed-false"]), (", %s refuted" % th(by["refuted"])) if by["refuted"] else ""),
             "%s suspected false" % th(by["suspected-false"]),
             "%s blocked by the model" % th(by["model-gap"]),
             "%s withheld (%s waiting for their source bundle, %s not published yet)" % (
                 th(by["withheld"]), th(held["source-bundle"]), th(held["not-yet-published"])),
             "%s open" % th(by["open"])]
    return "%s statements: %s" % (th(n), ", ".join(parts))


def readme(tree):
    T = "README.md.tmpl"
    r = tree.release
    stmts = [s for s in tree.statements() if s.status != "withdrawn"]
    cov = [_t(T, "coverage_row", words=spec["words"], status=st,
              n=render.thousands(sum(1 for p in tree.projects.values() if p.data["status"] == st)))
           for st, spec in PB["projects"].items()
           if any(p.data["status"] == st for p in tree.projects.values())]
    ex = _example(stmts)
    if ex:
        params, body = shapes.term(ex.data, project=ex.harness.project.data)
        letters = _binding_letters(ex.harness, ex)
        shown = [render.lower_first(ex.harness.data["checks"][ord(x) - 97]["what"].rstrip(".")) for x in letters[:2]]
        if len(letters) > 2:
            shown[-1] += " (and %s more)" % render.plural(len(letters) - 2, "check", "checks")
        words = _t(T, "example_binds" if letters else "example_plain", build=names.BUILD_WORDS[ex.data["builds"][0]],
                   exits=_exits_words(ex.data), budget=shapes.HALTS_BUDGET[1], harness=ex.harness.name,
                   whats="; ".join(shown))
        example = _t(T, "example", example_id=ex.id, example_path="%s/Statements.v" % ex.harness.dir,
                     example_words=words, example_name=ex.name + params, example_body=body)
        eid, erev = ex.id, ex.revision
        unit = (ex.harness.project.name, ex.harness.name)
    else:
        example, eid, erev = _t(T, "example_none"), "project/harness/statement", 1
        unit = ("<project>", "<harness>")
    harnesses = list(tree.harnesses())
    n_four = sum(1 for h in harnesses if len(h.data["builds"]) == len(schema.BUILDS))
    four_builds = ("every harness has all four" if n_four == len(harnesses) else
                   "%s of the %s harnesses have all four" % (render.thousands(n_four), render.thousands(len(harnesses))))
    n_pub = sum(len(h.builds()) for h in harnesses)
    n_held = sum(len(h.builds(published_only=False)) for h in harnesses) - n_pub
    sem = r["semantics"]
    unreleased = sem["version"] == "unreleased"
    published = not unreleased or sem.get("published", False)
    if not unreleased:
        lps_version, lps_plain = "version %s" % sem["version"], "%s %s" % (sem["name"], sem["version"])
    elif published:
        at = "commit [`%s`](%s/commit/%s)" % (sem["commit"][:12], sem["repository"], sem["commit"])
        lps_version, lps_plain = at, "%s at %s" % (sem["name"], at)
    else:
        lps_version = "the version the checker image pins (not released yet)"
        lps_plain = "the %s that image carries (not released yet)" % sem["name"]
    _n, by, _held = statement_counts(tree)
    proved_words = ("none of them is proved yet (0 proved), some are known to be false, and proofs are added as "
                    "they are found." if not by["proved"] else
                    "%s %s proved, some are known to be false, and proofs are added as they are found."
                    % (render.thousands(by["proved"]), "is" if by["proved"] == 1 else "are"))
    proved = proved_rows(tree)
    checked = _checked_unit(proved, unit)
    if proved:
        proved_lead = _t(T, "proved_lead", n_entries=render.thousands(len(proved)),
                         n_libraries=render.thousands(len({x["library"] for x in proved})))
        proved_table = "\n".join([_t(T, "proved_table_head")] +
                                 [_t(T, "proved_row", library=x["library"], entry=x["entry"], builds=x["builds"],
                                     path=x["path"]) for x in proved])
    else:
        proved_lead = _t(T, "proved_lead_none")
        proved_table = proved_lead
    n_halts = sum(1 for x in proved for s in x["statements"] if s.kind == "halts")
    halts_words = (_t(T, "halts_none") if not n_halts else
                   _t(T, "halts_one") if n_halts == 1 else
                   _t(T, "halts_some", n_halts=render.thousands(n_halts)))
    # the OSS-Fuzz paragraph counts OSS-Fuzz's projects and their OSS-Fuzz targets alone (no OSS Verify target and no
    # API driver), as each project page and index/projects.tsv do
    oss_fuzz_available = [p for p in tree.available() if "oss_fuzz" in p.data]
    oss_fuzz_targets = [e for p in oss_fuzz_available for e in p.targets()]
    n_oss_fuzz_included = sum(1 for e in oss_fuzz_targets if e["status"] == "included")
    not_in_oss_fuzz = tree.not_in_oss_fuzz()
    projects = render.join_words("[`%s`](projects/%s/)" % (n, n) for n in not_in_oss_fuzz)
    any_port = any(facts.port(p) for p in tree.projects.values())
    return _t(T, "file", n_projects=render.thousands(len(tree.projects)),
              n_oss_fuzz_projects=render.thousands(tree.oss_fuzz_project_count()),
              n_available=render.thousands(len(tree.available())),
              n_oss_fuzz_available=render.thousands(len(oss_fuzz_available)),
              example=example, status_counts=counts_sentence(tree), coverage_rows="\n".join(cov),
              total_label="all projects" if not_in_oss_fuzz else "all OSS-Fuzz projects",
              not_in_oss_fuzz=_t(T, "not_in_oss_fuzz", projects=projects,
                                  project_directories=("a project directory" if len(not_in_oss_fuzz) == 1
                                                       else "project directories"),
                                  pronoun="it" if len(not_in_oss_fuzz) == 1 else "them")
              if not_in_oss_fuzz else "",
              source_description=(_t(T, "source_description_recipe_mixed" if any_port else "source_description_recipe")
                                  if facts.release_recipes(tree) else ""),
              port_description=_t(T, "port_description") if any_port else "",
              proved_words=proved_words, proved_lead=proved_lead, proved_table=proved_table,
              n_harnesses=render.thousands(len(harnesses)), n_oss_fuzz_included=render.thousands(n_oss_fuzz_included),
              n_oss_fuzz_targets=render.thousands(len(oss_fuzz_targets)),
              halts_words=halts_words,
              n_binaries=render.thousands(n_pub), n_withheld_binaries=render.thousands(n_held),
              n_statements=render.thousands(len(stmts)), oss_fuzz_commit8=r["oss_fuzz"]["commit"][:8],
              oss_fuzz_commit=r["oss_fuzz"]["commit"],
              not_checkable="" if published else _t(T, "not_checkable"),
              lps_name=sem["name"], lps_version=lps_version, lps_plain=lps_plain, lps_commit8=sem["commit"][:8],
              rocq_version=r["rocq"]["version"], four_builds=four_builds, checker_image=r["images"]["checker"],
              example_id=eid, example_revision=erev,
              # "Check a proof" fetches and checks a proved fuzz target the release carries (a held one is cut from
              # the proofs, so it is never named); the fetch comment lines up at one column whatever its name
              fetch_command=_padded("./oft fetch %s" % checked[0], 37),
              check_command="./oft check %s/%s" % checked) + "\n"


def _padded(command, width):
    return command + " " * max(1, width - len(command))


CHECKED = ("coturn", "FuzzStunClient")


def _checked_unit(proved, fallback):
    """The fuzz target the README's "Check a proof" fetches and checks: coturn/FuzzStunClient while it has a proof,
    else the first entry point with one, else fallback (the example statement's fuzz target)."""
    units = [(x["library"], x["entry"]) for x in proved]
    return CHECKED if CHECKED in units else units[0] if units else fallback


EXAMPLE = "zlib/checksum_fuzzer/plain_halts"


def _example(stmts):
    """The statement the README shows: zlib/checksum_fuzzer/plain_halts while it
    is open and published, else the open halts statement with the smallest
    plain image among harnesses whose checks it binds, else the smallest open
    halts statement, else anything."""
    for s in stmts:
        if s.id == EXAMPLE and s.status == "open" and s.rendered() and s.harness.builds():
            return s
    halts = [s for s in stmts if s.kind == "halts" and s.data["reading"] == "budget" and s.rendered()
             and s.harness.builds() and s.harness.data["source"]["files"]]
    size = lambda s: (dict(s.harness.builds()).get(s.data["builds"][0], {}).get("bytes", 0), s.id)
    for pick in ([s for s in halts if s.status == "open" and _binding_letters(s.harness, s)],
                 [s for s in halts if s.status == "open"], [s for s in stmts if s.rendered()]):
        if pick:
            return min(pick, key=size)
    return None


def _tsv(header, rows):
    clean = lambda v: str(v).replace("\t", " ").replace("\n", " ")
    return "\n".join(["\t".join(header)] + ["\t".join(clean(v) for v in r) for r in rows]) + "\n"


def index_files(tree):
    out = {}
    prow, hrow, srow, brow, crow = [], [], [], [], []
    for proj in sorted(tree.projects.values(), key=lambda p: p.name):
        d = proj.data
        targets = proj.targets()
        c = _project_row_counts(proj)
        prow.append([proj.name, d["language"], d["status"], d.get("reason") or "-", len(targets),
                     sum(1 for e in targets if e["status"] == "included"),
                     "yes" if any(e["name"] == names.API_DRIVER and e["status"] == "included"
                                  for e in proj.entries()) else "no",
                     _n_builds(proj, True), _n_builds(proj, False),
                     c["n"], c["open"], c["proved"], c["false"], c["suspected"], c["model_gap"], c["withheld"]])
    for h in tree.harnesses():
        c = _counts(h.statements.values())
        hrow.append([h.project.name, h.name, h.data["origin"], ",".join(b for b, _ in h.builds()) or "-",
                     c["n"], c["open"], c["proved"], c["false"], c["suspected"], c["model_gap"], c["withheld"],
                     ",".join(h.data.get("model_gap", [])) or "-"])
        for s in _order(h):
            d = s.data
            ex = d.get("exits", "-")
            detail = {"withheld": lambda: d["withheld"], "model-gap": lambda: ",".join(gap_of(s)),
                      "witnessed-false": lambda: "run of the %s build" % d["witness"]["build"],
                      "counterexample": lambda: s.counterexample.path}.get(s.status, lambda: "-")()
            srow.append([s.id, s.kind, ",".join(d["builds"]), d["reading"],
                         ex if isinstance(ex, str) else ",".join(str(e) for e in ex), s.status, detail, s.revision,
                         s.fingerprint or "-", s.proof.path if s.proof else "-"])
        for b, rec in h.builds(published_only=False):
            held = rec.get("withheld")
            brow.append([h.project.name, h.name, b, rec["file"], "withheld" if held else "published", held or "-",
                         "-" if held else rec["bytes"], "-" if held else rec["sha256"], h.data["licence"]])
        for i, ch in enumerate(h.data["checks"]):
            bound = [s.name for s in h.statements.values() if shapes.binds(ch, s.data, h.data)]
            crow.append([h.project.name, h.name, ch["kind"], ch["strength"], ch["stops_with"],
                         {True: "yes", False: "compiled out"}.get(ch["live"], "not found"), "halts" if bound else "-",
                         ch["where"], ch["what"]])
    out["index/projects.tsv"] = _tsv(["project", "language", "status", "reason", "oss_fuzz_targets", "included",
                                      "api_driver", "binaries", "binaries_withheld", "statements", "open", "proved",
                                      "false", "suspected_false", "blocked_by_model", "withheld"], prow)
    out["index/harnesses.tsv"] = _tsv(["project", "harness", "origin", "builds", "statements", "open", "proved",
                                       "false", "suspected_false", "blocked_by_model", "withheld", "model_gap"], hrow)
    out["index/statements.tsv"] = _tsv(["id", "kind", "builds", "reading", "exits", "status", "detail", "revision",
                                        "fingerprint", "proof"], srow)
    out["index/binaries.tsv"] = _tsv(["project", "harness", "build", "file", "status", "withheld_reason", "bytes",
                                      "sha256", "licence"], brow)
    out["analyses/harness-checks/checks.tsv"] = _tsv(["project", "harness", "kind", "strength", "stops_with",
                                                      "text_in_binary", "binds", "where", "what"], crow)
    out["index/STATUS.md"] = status_md(tree)
    proved = proved_rows(tree)
    out["index/PROOFS.md"] = proofs_md(proved)
    out["index/proofs.tsv"] = proofs_tsv(proved)
    issues = ["<!-- generated by oft generate; do not edit -->", "# Known issues", "",
              "Every statement in this release that is not open or proved.", "",
              "| statement | status | why |", "|---|---|---|"]
    n = 0
    for s in tree.statements():
        if s.status in ("open", "proved"):
            continue
        n += 1
        st_words = PB["statements"][s.status]["words"]
        if s.status == "counterexample":
            st_words = "[%s](../%s/)" % (st_words, s.counterexample.path)
        issues.append("| [%s](../%s/) | %s | %s |" % (s.id, s.harness.dir, st_words, why_words(s)))
    if not n:
        issues.append("| - | - | none |")
    out["analyses/known-issues.md"] = "\n".join(issues) + "\n"
    return out


# ------------------------------------------------------------------ the proved entry points

FAILURE_WORDS = {"may-fail": "every kind of call that LPS lets fail may fail without cause",
                 "alloc-forced-only": "every kind of call that LPS lets fail may fail without cause, except that a "
                                      "memory request fails only when the budget is spent or no address range is free",
                 "budget": "only the failures that the process's state forces"}


def _failure_words(d):
    w = FAILURE_WORDS[d["reading"]]
    return w + " (abort() is read as death by SIGABRT, which the statement forbids)" if d.get("abort") == "signal" else w


def proved_rows(tree):
    """One dict per entry point with a proof under proofs/, in project and harness order."""
    rows = []
    for h in tree.harnesses():
        proved = [s for s in _order(h) if s.status == "proved"]
        if not proved:
            continue
        rows.append({"library": h.project.name, "entry": h.name,
                     "path": "proofs/%s/%s/" % (h.project.name, h.name),
                     "statements": proved, "statement_file": "%s/Statements.v" % h.dir,
                     "builds": ", ".join(names.BUILD_WORDS[s.data["builds"][-1]] for s in proved
                                         if s.kind == "agreement") or "-",
                     "failures": render.join_words(sorted({_failure_words(s.data) for s in proved}), "and"),
                     "build_record": "proofs/%s/%s/provenance/PROVENANCE.md" % (h.project.name, h.name)})
    return rows


def proofs_md(rows):
    out = ["<!-- generated by oft generate; do not edit -->", "# The proved entry points", "",
           "One row for each entry point that has a proof. [README.md](../README.md#the-theorem-in-words) says what "
           "the statements mean, and [docs/statements.md](../docs/statements.md) gives each form. Every proof uses "
           "the LPS version and the checker image that [release.yaml](../release.yaml) names.", "",
           "| library | entry point | statements proved | system-call failures the statements allow | binaries | proof |",
           "|---|---|---|---|---|---|"]
    for r in rows:
        stmts = ", ".join("`%s`" % s.name for s in r["statements"])
        out.append("| %s | %s | %s ([statements](../%s)) | %s | [build record](../%s) | [%s](../%s) |" % (
            r["library"], r["entry"], stmts, r["statement_file"], r["failures"], r["build_record"],
            r["path"], r["path"]))
    if not rows:
        out.append("| - | - | none | - | - | - |")
    return "\n".join(out) + "\n"


def proofs_tsv(rows):
    return _tsv(["library", "entry_point", "statement", "kind", "build", "failures", "statement_file", "proof",
                 "build_record"],
                [[r["library"], r["entry"], s.name, s.kind, s.data["builds"][-1], _failure_words(s.data),
                  r["statement_file"], s.proof.path, r["build_record"]]
                 for r in rows for s in r["statements"]])


# ------------------------------------------------------------------ driver

def render_all(tree):
    out = {"README.md": readme(tree), "dune-project": dune_project(tree)}
    out.update(index_files(tree))
    for proj in tree.projects.values():
        out[os.path.join(proj.dir, "README.md")] = project_readme(tree, proj)
        if proj.data["status"] == "available" and "assets" in proj.data:
            out[os.path.join(proj.dir, names.opam_package(proj.name) + ".opam")] = project_opam(tree, proj)
    for h in tree.harnesses():
        out[os.path.join(h.dir, "README.md")] = harness_readme(tree, h)
        if "distribution" in h.data:
            out[os.path.join(h.dir, "Distribution.v")] = distribution_v(h)
        if not h.builds():
            continue
        out[os.path.join(h.dir, "dune")] = harness_dune(h)
        out[os.path.join(h.dir, "Images.v")] = images_v(h)
        out[os.path.join(h.dir, "images", "dune")] = images_dune(h)
        out[os.path.join(h.dir, "Statements.v")] = statements_v(h)
        ch = characterise_v(h)
        if ch is not None:
            out[os.path.join(h.dir, "Characterise.v")] = ch
    for sid, pd in tree.proofs.items():
        out[os.path.join(pd.path, "dune")] = proof_dune(tree, sid)
    for unit in tree.proof_libs:
        p, _, hn = unit.partition("/")
        out[os.path.join("proofs", p, hn, "lib", "dune")] = proof_lib_dune(p, hn)
    return out


def _rendered_path(rel):
    m = paths.classify(rel)
    return len(m) == 1 and (m[0][0] == "gen" or m[0][1].endswith("/Distribution.v"))


def existing_generated(root):
    """Every path on disk that `render_all` owns: the gen class, and
    Distribution.v, whose header it renders."""
    found = []
    for dp, dns, fns in os.walk(root):
        rel_dir = os.path.relpath(dp, root)
        dns[:] = [d for d in dns if not paths.ignored(os.path.normpath(os.path.join(rel_dir, d)))]
        for f in fns:
            rel = os.path.normpath(os.path.join(rel_dir, f))
            if _rendered_path(rel):
                found.append(rel)
    return found


def run(root, check=False, out=sys.stdout):
    tree = facts.load(root)
    rules.check(tree)
    if tree.errors:
        for e in tree.errors:
            print("error: " + e, file=out)
        print("oft generate: %d error(s) in the facts; nothing rendered" % len(tree.errors), file=out)
        return 1
    rendered = render_all(tree)
    bad = 0
    for rel, text in sorted(rendered.items()):
        p = os.path.join(root, rel)
        old = facts.read_raw(p) if os.path.isfile(p) else None
        if old == text:
            continue
        if check:
            print("%s: %s" % (rel, "missing" if old is None else "differs from its rendering"), file=out)
            bad += 1
        else:
            os.makedirs(os.path.dirname(p) or ".", exist_ok=True)
            with open(p, "w", encoding="utf-8", newline="\n") as f:
                f.write(text)
    stale = [r for r in existing_generated(root) if r not in rendered]
    for rel in sorted(stale):
        print("%s: generated file that the facts no longer produce; remove it" % rel, file=out)
        bad += 1
    if not rendered:
        print("oft generate: rendered nothing", file=out)
        return 1
    print("oft generate%s: %d files, %d problem(s)" % (" --check" if check else "", len(rendered), bad), file=out)
    return 1 if bad else 0
