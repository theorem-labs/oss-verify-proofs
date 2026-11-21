import hashlib
import re
from fractions import Fraction

from . import render, shapes

# up to 14: the images of a harness with its four builds, four originals and three classifier pairs (images_v)
COUNT_WORDS = {1: "One", 2: "Two", 3: "Three", 4: "Four", 5: "Five", 6: "Six", 7: "Seven", 8: "Eight", 9: "Nine",
               10: "Ten", 11: "Eleven", 12: "Twelve", 13: "Thirteen", 14: "Fourteen"}
PLAIN = {"project": r"[a-z0-9][a-z0-9_-]{0,99}", "harness": r"[A-Za-z0-9][A-Za-z0-9._+-]{0,149}",
         "namespace": r"[A-Za-z][A-Za-z0-9_]*(?:\.[A-Za-z][A-Za-z0-9_]*)*", "statement": r"[a-z][a-z0-9_]{0,99}",
         "file": r"[A-Za-z0-9][A-Za-z0-9._+-]{0,199}", "fraction": r"(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?",
         "hex": r"(?:[0-9a-f]{2})*", "sha256": r"[0-9a-f]{64}",
         "alphabet": r"bytes|printable|json|hex|digits|base64|alnum|custom"}


def plain(kind, value):
    if not (isinstance(value, str) and re.fullmatch(PLAIN[kind], value)):
        raise ValueError("%s %r is not one that tools/oft/claims.py writes" % (kind, value))
    return value


def count(value):
    if type(value) is not int or value < 0:
        raise ValueError("%r is not a count" % (value,))
    return value


def comment(text, first_indent_skip=True):
    """Prose for inside (** ... *): sanitised, wrapped, indented by 4."""
    w = render.wrap(render.rocq_comment_text(text), 80, "    ")
    return w[4:] if first_indent_skip else w


def rocq(namespace, project, harness):
    return "%s.%s.%s" % (plain("namespace", namespace), shapes.ident(plain("project", project)),
                         shapes.ident(plain("harness", harness)))


def builds(data):
    b = data.get("builds") or {}
    return [(k, b[k]) for k in shapes.BUILD_IDENT if k in b and not b[k].get("withheld")]


def originals(data):
    o = data.get("originals") or {}
    return [(k, o[k]) for k in shapes.BUILD_IDENT if k in o and not o[k].get("withheld")]


def classifiers(data):
    c = data.get("classifiers") or {}
    return [(role, k, c[k][role]) for k in shapes.BUILD_IDENT if k != "plain" and k in c for role in ("a", "b")
            if role in c[k] and not c[k][role].get("withheld")]


def images(data):
    """[(identifier, module, record)] of every binary the harness publishes, as Images.v and images/dune define them:
    its builds, then its originals, then its classifiers (harness.yaml builds, originals, classifiers)."""
    return ([(shapes.BUILD_IDENT[b], shapes.BUILD_MODULE[b], rec) for b, rec in builds(data)]
            + [(shapes.original_ident(b), shapes.original_module(b), rec) for b, rec in originals(data)]
            + [(shapes.classifier_ident(role, b), shapes.classifier_module(role, b), rec)
               for role, b, rec in classifiers(data)])


def rendered(st):
    return st.get("status") not in ("withheld", "withdrawn")


def elf_path(project, harness, rec):
    return "projects/%s/bin/%s/%s" % (project, harness, rec["file"])


def statements_v(namespace, project, harness, data, project_data, ordered, header, doc, status, proving):
    T = "Statements.v.tmpl"
    distribution = "distribution" in data
    sections, current = [], None
    for name in ordered:
        st = data["statements"][plain("statement", name)]
        if st["kind"] != current:
            current = st["kind"]
            sections.append(render.fill(T, "section", title=render.fill(T, "title_" + st["kind"])))
        if not rendered(st):
            sections.append(render.fill(T, "not_rendered", name=name, status=render.rocq_comment_text(status(name))))
            continue
        params, body = shapes.term(st, project=project_data, distribution=distribution)
        sections.append(render.fill(T, "definition", doc=comment(doc(name)), name=name, params=params, body=body))
    live = [st for st in data["statements"].values() if rendered(st)]
    bound = any(shapes.takes_bound(st["kind"], distribution) for st in live)
    classifier = any(st["kind"] in shapes.CLASSIFIER_KINDS for st in live)
    return render.fill(T, "file", project=project, harness=harness, header=comment(header, False),
                       namespace=namespace, rocq=rocq(namespace, project, harness),
                       distribution_require=" Distribution" if bound else "",
                       classifier_shapes=" ClassifierShapes" if classifier else "",
                       sections="\n" + "\n\n".join(sections) + "\n",
                       proving=comment(proving, False)) + "\n"


def images_v(namespace, project, harness, data):
    T = "Images.v.tmpl"
    images_ = images(data)
    return render.fill(T, "file", project=project, harness=harness, count=COUNT_WORDS[len(images_)].lower(),
                       s="s" if len(images_) > 1 else "", namespace=namespace, rocq=rocq(namespace, project, harness),
                       header=comment(render.fill(T, "header", namespace=namespace), False),
                       modules=" ".join(m for _, m, _ in images_),
                       definitions="\n".join(render.fill(T, "definition", ident=i, module=m) for i, m, _ in images_),
                       lemmas="\n".join(render.fill(T, "lemma", ident=i) for i, _, _ in images_)) + "\n"


def hex_targets(module, segments):
    out = []
    for i, chunks in enumerate(segments):
        if chunks == 1:
            out.append("%s_seg_%03d.hex" % (module, i))
        else:
            out.extend("%s_seg_%03d_chunk_%03d.hex" % (module, i, j) for j in range(chunks))
    return out


def images_dune(namespace, project, harness, data):
    T = "images-dune.tmpl"
    rules_ = []
    for _ident, m, rec in images(data):
        plain("file", rec["file"])
        rules_.append(render.fill(T, "rule", targets=" ".join([m + ".v"] + hex_targets(m, [
            count(c) for c in rec["segments"]])), elf=elf_path(project, harness, rec), module=m,
                                  namespace=rocq(namespace, project, harness) + ".images"))
    return render.fill(T, "file", rules="\n".join(rules_)) + "\n"


def distribution_header(project, harness, data):
    T = "Distribution-header.v.tmpl"
    d = data["distribution"]
    plain("project", project), plain("harness", harness), plain("hex", d.get("prefix_hex", ""))
    for value in [d["mass"], d["payload"]["p"]] + list(d["components"].values()):
        plain("fraction", value)
    for value in (d["payload"]["mean_bytes"], d["payload"].get("alphabet_size", 0),
                  d.get("prefix", {}).get("bytes", 0)):
        count(value)
    plain("alphabet", d["payload"]["alphabet"]), plain("sha256", d.get("prefix", {}).get("sha256", "0" * 64))
    comps = []
    hexs = d.get("prefix_hex", "")
    spaced = " ".join(hexs[i:i + 2] for i in range(0, len(hexs), 2))
    if "prefix" in d:
        prefix = render.fill(T, "prefix_long", n=render.thousands(d["prefix"]["bytes"]), sha=d["prefix"]["sha256"])
    elif hexs == "0" * 12:
        prefix = render.fill(T, "prefix_header", n=6, hex=spaced)
    elif hexs.startswith("0" * 12):
        rest = hexs[12:]
        prefix = render.fill(T, "prefix_header_and_payload",
                             hex=" ".join(rest[i:i + 2] for i in range(0, len(rest), 2)))
    else:
        prefix = render.fill(T, "prefix_other", n=len(hexs) // 2, hex=spaced)
    pl = d["payload"]
    alphabet = (render.fill(T, "alphabet_bytes") if pl["alphabet"] == "bytes"
                else render.fill(T, "alphabet_custom", size=pl.get("alphabet_size", "?")) if pl["alphabet"] == "custom"
                else render.fill(T, "alphabet_named", name=pl["alphabet"], size=pl.get("alphabet_size", "?")))
    q = lambda s: '"%s"' % render.rocq_comment_text(s)
    c = d["components"]
    comps.append(render.fill(T, "payload", weight=c["payload"], argv0=q(d["argv0"]), input_file=q(d["input_file"]),
                             prefix=prefix, alphabet=alphabet, p=pl["p"], mean=render.thousands(pl["mean_bytes"])))
    comps.append(render.fill(T, "wrong_argc", weight=c["wrong_argc"], input_file=d["input_file"]))
    comps.append(render.fill(T, "missing_file", weight=c["missing_file"], input_file=d["input_file"],
                             argv0=q(d["argv0"])))
    if "envp" in c:
        comps.append(render.fill(T, "envp", weight=c["envp"], input_file=d["input_file"],
                                 envp=render.join_words((render.rocq_comment_text(e) for e in d.get("envp", [])),
                                                        "or")))
    comps.append(render.fill(T, "full_support", weight=c["full_support"]))
    text = render.fill(T, "text", mass=d["mass"], components="\n".join(comps))
    return render.fill(T, "file", project=project, harness=harness, text=render.wrap(text, 80, "    "))


def distribution_v(project, harness, data, body):
    return distribution_header(project, harness, data) + "\n" + (body if body is not None else "")


def code(text):
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        c = text[i]
        if c == '"':
            j = i + 1
            while j < n and not (text[j] == '"' and text[j + 1:j + 2] != '"'):
                j += 2 if text[j] == '"' else 1
            if depth == 0:
                out.append(text[i:j + 1])
            i = j + 1
        elif text.startswith("(*", i):
            depth, i = depth + 1, i + 2
        elif depth and text.startswith("*)", i):
            depth, i = depth - 1, i + 2
            if depth == 0:
                out.append(" ")
        else:
            if depth == 0:
                out.append(c)
            i += 1
    return None if depth else "".join(out)


def sentences(text):
    c = code(text)
    if c is None or '"' in c or re.search(r"[^\t\n\r\x20-\x7e]", c):
        return None
    parts = re.split(r"\.(?=\s|$)", c)
    if parts[-1].strip():
        return None
    return [" ".join(p.split()) for p in parts[:-1]]


BYTES = re.compile(r"\[ ?((?:Z_to_bv 8 \d+; ?)*Z_to_bv 8 \d+) ?\]")
RAT = re.compile(r"\((\d+) # (\d+)\)%Q")
POSITIVE = ["Proof", "apply Qlt_le_weak", "reflexivity", "Qed"]
ENTRIES_NONNEG = ["Proof", "apply entries_nonneg_of_forallb", "reflexivity", "Qed"]
ENVP_ENTRY = "(file_core (path_argv prog path) [<B>] fs0 path stdin0 [], m_envp_each)"
HDR = "Definition hdr : list byte := "
ALPHABETS = {"printable": bytes(range(32, 127)), "digits": b"0123456789", "hex": b"0123456789ABCDEFabcdef",
             "base64": b"+/0123456789=ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz",
             "alnum": b"0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"}


def distribution_form(alpha, envp, chunks):
    s = ["From Stdlib Require Import ZArith NArith List QArith",
         "From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State",
         "From LinuxProcessSemantics.EquivalenceDefinition Require Import FinInput Measure MeasureLib",
         "Import ListNotations", "Open Scope bv_scope",
         "Definition prog : list byte := <B>", "Definition path : Fs.path := <B>",
         "Definition envp0 : list (list byte) := []", "Definition fs0 : Fs.Fs := [(path, [])]",
         "Definition stdin0 : list byte := []"]
    s += ["Definition hdr_%03d : list byte := <B>" % i for i in range(chunks)]
    s += [HDR + ("<CAT>" if chunks else "<B>")]
    if alpha:
        s += ["Definition alpha : list byte := List.nodup (fun x y => decide (x = y)) <B>",
              "Lemma alpha_nodup : List.NoDup alpha", "Proof", "apply List.NoDup_nodup", "Qed",
              "Lemma alpha_ne : alpha <> []", "Proof", "intros H", "vm_compute in H", "discriminate H", "Qed"]
    s += ["Definition p : Q := <Q>", "Lemma p_nonneg : (0 <= p)%Q"] + POSITIVE
    s += ["Lemma p_le_1 : (p <= 1)%Q"] + POSITIVE
    s += ["Definition payload : CoreDistribution := " + (
        "file_geometric_prefix_over_argv1 alpha alpha_nodup alpha_ne " if alpha else "file_geometric_prefix_argv1 ")
        + "hdr p prog envp0 fs0 path stdin0 p_nonneg p_le_1",
          "Definition m_payload : Q := <Q>", "Lemma m_payload_nonneg : (0 <= m_payload)%Q"] + POSITIVE
    s += ["Definition m_argv_arity_each : Q := <Q>",
          "Definition argv_arity_entries : list (FinCore * Q) := [ (file_core [prog] envp0 fs0 path stdin0 [], "
          "m_argv_arity_each); (file_core [prog; path; <B>] envp0 fs0 path stdin0 [], m_argv_arity_each) ]",
          "Lemma argv_arity_nonneg : forall e, List.In e argv_arity_entries -> (0 <= snd e)%Q"] + ENTRIES_NONNEG
    s += ["Definition argv_arity : CoreDistribution := finite_support argv_arity_entries argv_arity_nonneg",
          "Definition m_missing_file : Q := <Q>",
          "Definition missing_file_entries : list (FinCore * Q) := [ (mkFinCore (path_argv prog path) envp0 [] "
          "stdin0, m_missing_file) ]",
          "Lemma missing_file_nonneg : forall e, List.In e missing_file_entries -> (0 <= snd e)%Q"] + ENTRIES_NONNEG
    s += ["Definition missing_file : CoreDistribution := finite_support missing_file_entries missing_file_nonneg"]
    if envp is not None:
        s += ["Definition m_envp_each : Q := <Q>",
              "Definition envp_entries : list (FinCore * Q) := [ " + " ; ".join([ENVP_ENTRY] * envp) + " ]",
              "Lemma envp_nonneg : forall e, List.In e envp_entries -> (0 <= snd e)%Q"] + ENTRIES_NONNEG
        s += ["Definition envp : CoreDistribution := finite_support envp_entries envp_nonneg"]
    s += ["Definition base_half : Q := <Q>", "Lemma base_half_nonneg : (0 <= base_half)%Q"] + POSITIVE
    s += ["Lemma base_half_le_1 : (base_half <= 1)%Q"] + POSITIVE
    s += ["Definition base : CoreDistribution := full_support_base " + " ".join(["base_half"] * 8) + " "
          + " ".join(["base_half_nonneg base_half_le_1"] * 8),
          "Definition m_base : Q := <Q>", "Lemma m_base_nonneg : (0 <= m_base)%Q"] + POSITIVE
    s += ["Definition components : list CoreDistribution := [ cd_scale m_payload m_payload_nonneg payload; "
          "argv_arity; missing_file; " + ("envp; " if envp is not None else "")
          + "cd_scale m_base m_base_nonneg base ]",
          "Definition cd : CoreDistribution := cd_mix components",
          "Definition w : FinProcInput -> Q := cd_lift cd", "Definition M : Q := 100#100",
          "Definition w_nonneg : forall f, (0 <= w f)%Q := cd_lift_nonneg cd",
          "Lemma M_is : (cd_mass cd == M)%Q", "Proof", "vm_compute", "reflexivity", "Qed",
          "Lemma M_nonneg : (0 <= M)%Q"] + POSITIVE
    s += ["Definition w_core_blind : forall f g, fin_core f = fin_core g -> (w f == w g)%Q := cd_lift_core_blind cd",
          "Module Ascription <: Measure.DISTRIBUTION", "Definition w := w", "Definition M := M",
          "Definition w_nonneg := w_nonneg", "Definition M_nonneg := M_nonneg",
          "Definition w_core_blind := w_core_blind", "End Ascription"]
    return s


def fraction(s):
    a, _, b = str(s).partition("/")
    return Fraction(int(a), int(b or 1))


def distribution_body_error(body, data):
    d = data.get("distribution")
    if not isinstance(d, dict):
        return "harness.yaml has no distribution block"
    s = sentences(body)
    if s is None or any(re.search(r"<(?:B|Q|CAT)>", x) for x in s):
        return "its code is not lexable, holds a string, or holds a character a form has not"
    payload, components = d["payload"], d["components"]
    alpha, envp = payload["alphabet"] != "bytes", len(d["envp"]) if "envp" in components else None
    chunks = sum(1 for x in s if re.match(r"Definition hdr_\d{3} : list byte := ", x))
    values = []

    def byte_list(m):
        values.append(bytes(int(v) for v in re.findall(r"Z_to_bv 8 (\d+)", m.group(0))))
        return "<B>"

    def rational(m):
        values.append(Fraction(int(m.group(1)), int(m.group(2))))
        return "<Q>"
    got = []
    for x in s:
        cat = x[len(HDR):] if chunks and x.startswith(HDR) else ""
        if cat and re.findall(r"hdr_\d{3}", cat) == ["hdr_%03d" % i for i in range(chunks)] \
                and not re.sub(r"hdr_\d{3}|[()+ ]|%list", "", cat):
            x = HDR + "<CAT>"
        got.append(RAT.sub(rational, BYTES.sub(byte_list, x)))
    want = distribution_form(alpha, envp, chunks)
    if got != want:
        i = next((i for i, (x, y) in enumerate(zip(got, want)) if x != y), min(len(got), len(want)))
        return "it is not the form tools/oft/claims.py reads, from its sentence %d: %r" % (
            i + 1, (got[i:] or [""])[0][:200])
    it = iter(values)
    prog, path, hdr = next(it), next(it), b"".join(next(it) for _ in range(chunks or 1))
    alphabet = next(it) if alpha else None
    p, m_payload, each, argv3, m_missing = (next(it) for _ in range(5))
    m_envp, envs = (next(it), [next(it) for _ in range(envp)]) if envp is not None else (None, None)
    base_half, m_base = next(it), next(it)
    if (prog, path, argv3) != (d["argv0"].encode(), d["input_file"].encode(), b"x"):
        return "prog, path or the third argv word is not harness.yaml's"
    if "prefix_hex" in d:
        prefix = hdr == bytes.fromhex(d["prefix_hex"])
    else:
        prefix = (len(hdr), hashlib.sha256(hdr).hexdigest()) == (d["prefix"]["bytes"], d["prefix"]["sha256"])
    if not prefix:
        return "hdr is not harness.yaml's prefix"
    if alpha and (alphabet != (alphabet if payload["alphabet"] == "custom" else ALPHABETS.get(payload["alphabet"]))
                  or len(set(alphabet)) != len(alphabet) or len(alphabet) != payload["alphabet_size"]):
        return "alpha is not harness.yaml's alphabet, as alphabet_size distinct bytes"
    if envp is not None and envs != [e.encode() for e in d["envp"]]:
        return "the envp entries are not harness.yaml's envp"
    if (p, payload["length"], fraction(d["mass"]), base_half) != (fraction(payload["p"]), "geometric", 1,
                                                                  Fraction(1, 2)):
        return "p is not harness.yaml's, the payload's length is not geometric, the mass is not 1 or base_half not 1/2"
    vec = (m_payload, 2 * each, m_missing, None if envp is None else m_envp * envp, m_base)
    if any(v is not None and v <= 0 for v in vec) or vec != tuple(
            fraction(components[k]) if k in components else None
            for k in ("payload", "wrong_argc", "missing_file", "envp", "full_support")):
        return "its component weights %s are not harness.yaml's components, each above 0" % (
            ", ".join(str(v) for v in vec))
    return None
