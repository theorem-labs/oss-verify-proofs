"""From a statement's typed fields to its Rocq text.

Each statement in a harness.yaml names one definition of
theories/Shapes.v (<namespace>.Core.Shapes), or for a classifier statement
of theories/ClassifierShapes.v, and its arguments.  This module is the only
place that choice is made; a combination it does not list is an error,
never a guess.
"""
import re

BUILD_IDENT = {"plain": "plain", "ubsan": "ubsan", "asan": "asan", "asan-ubsan": "asan_ubsan"}
BUILD_MODULE = {"plain": "Plain", "ubsan": "Ubsan", "asan": "Asan", "asan-ubsan": "AsanUbsan"}

BUDGETS = {
    # module, plain-build bytes, sanitizer-build bytes (theories/Shapes.v's standard_budgets and asan_budgets)
    "standard": ("Budgets.Standard", 16 << 30, 512 << 30),
    "asan": ("Budgets.Asan", 2 << 30, 512 << 30),
}
HALTS_BUDGET = ("Budgets.Standard.lim_source", "16 GiB")

# The key of project.yaml `budgets.agrees` for each sanitizer build (the public shape), and the harness.yaml budgets
# an agreement statement of that build uses by default.
SANITIZER_KEY = {"ubsan": "undefined", "asan": "address", "asan-ubsan": "address"}
DEFAULT_BUDGETS = {"undefined": "standard", "address": "asan"}
# The smallest plain-side budget, one page: below it the budget premise covers no run at all.
MIN_PLAIN_BUDGET = 4096
UNITS = {"": 1, "KiB": 1 << 10, "MiB": 1 << 20, "GiB": 1 << 30, "TiB": 1 << 40}
# project.yaml's size grammar, from the schema that checks it; its one group is the unit
SIZE = re.compile(r"^[1-9][0-9]{0,15}(KiB|MiB|GiB|TiB)?$")

ENV = {"may-fail": "Env.may_fail", "alloc-forced-only": "Env.alloc_forced_only"}

# (reading, abort, machine) -> the agreement shape
AGREEMENT = {
    ("may-fail", "error", "rv64g"): "agrees",
    ("may-fail", "signal", "rv64g"): "agrees_abort_modelled",
    ("alloc-forced-only", "error", "rv64g"): "agrees_in",
    ("alloc-forced-only", "signal", "rv64g"): "agrees_in_abort_modelled",
    ("may-fail", "error", "rv64gc"): "agrees_rv64gc",
    ("may-fail", "signal", "rv64gc"): "agrees_abort_modelled_rv64gc",
    ("alloc-forced-only", "error", "rv64gc"): "agrees_in_rv64gc",
}

# The driver's status when a call of the fuzz target returns a value other than 0 or -1.  libFuzzer reserves
# those values; a libFuzzer built without assertions treats them as -1 (the input is rejected, not a crash).  A
# harness whose fuzz target returns one to turn an input away lists where (harness.yaml `rejects`).  A halts
# statement with a finite exit set includes this status exactly when the harness lists `rejects` (rules.py lints
# it); a halts statement with `exits: any` allows every status.
REJECTED = 78

# The set with 78 is spelled out in the statement rather than named in Shapes.Exits: any change to the code of
# theories/Shapes.v moves every statement's fingerprint, through its digest.  Statements.v opens neither list_scope
# nor a scope with N numerals (QArith's Q scope is open), so the term uses `cons` and lets the word width (64)
# come from `list word`; it elaborates to Z_to_bv 64 78 :: [Z_to_bv 64 0; Z_to_bv 64 2].
EXIT_SETS = {"any": "Exits.any", (0, 2): "Exits.ok_or_refused",
             (0, 2, REJECTED): "(cons (stdpp.bitvector.definitions.Z_to_bv _ %d%%Z) Exits.ok_or_refused)" % REJECTED}


class ShapeError(ValueError):
    pass


class PairError(ShapeError):
    """A malformed project.yaml budgets.agrees pair: reported once, against project.yaml, not per statement."""


def ident(name):
    """A Rocq identifier for an OSS-Fuzz project or harness name."""
    s = re.sub(r"[^A-Za-z0-9_]", "_", name)
    if s[:1].isdigit():
        s = "h_" + s
    return s


def exits_key(exits):
    return "any" if exits == "any" else tuple(sorted(set(exits)))


def image(build):
    return "Images." + BUILD_IDENT[build]


def size_bytes(text):
    """The bytes of a project.yaml size such as "2GiB" (schemas/project.yaml `size`)."""
    m = SIZE.match(text) if isinstance(text, str) else None
    if m is None:
        raise ShapeError("budget %r is not a size such as 2GiB" % (text,))
    unit = m.group(1) or ""
    return int(text[:len(text) - len(unit)]) * UNITS[unit]


def size_words(n):
    """A size in words, in the largest unit that divides it exactly: 2^30 is "1 GiB", 4352 GiB stays "4352 GiB"."""
    for unit in ("TiB", "GiB", "MiB", "KiB"):
        if n % UNITS[unit] == 0:
            return "%d %s" % (n // UNITS[unit], unit)
    return "%d bytes" % n


def project_pair(project, key):
    """The (plain, sanitizer) bytes of `project`'s (a project.yaml) own pair for sanitizer key `key`, or None."""
    pair = (((project or {}).get("budgets") or {}).get("agrees") or {}).get(key)
    if pair is None:
        return None
    if not isinstance(pair, list) or len(pair) != 2:
        raise PairError("budgets.agrees.%s is [plain, sanitizer]" % key)
    try:
        plain, san = size_bytes(pair[0]), size_bytes(pair[1])
    except ShapeError as e:
        raise PairError("budgets.agrees.%s: %s" % (key, e)) from None
    if plain < MIN_PLAIN_BUDGET:
        raise PairError("budgets.agrees.%s: the plain budget is at least %d bytes"
                         % (key, MIN_PLAIN_BUDGET))
    if san < plain:
        raise PairError("budgets.agrees.%s: the sanitizer budget is at least the plain one" % key)
    return plain, san


def is_own_pair(key, pair):
    """Does pair (bytes) differ from sanitizer key `key`'s default, so that statements carry it as literals?"""
    return pair is not None and pair != BUDGETS[DEFAULT_BUDGETS[key]][1:]


def agreement_budgets(st, project):
    """(enum, plain bytes, sanitizer bytes) for agreement statement `st`: enum is the BUDGETS key whose module the
    term names, or None when the term carries the project's own pair as literals.

    `project` is the statement's project.yaml.  A pair in its `budgets.agrees` for the statement's sanitizer
    replaces the harness.yaml `budgets` field, which the statement must then leave out; a pair equal to that
    sanitizer's default is the default enum, so it changes neither the term nor the fingerprint."""
    key = SANITIZER_KEY[st["builds"][1]]
    pair = project_pair(project, key)
    if pair is None:
        if "budgets" not in st:
            raise ShapeError("an agreement statement names its budgets")
        if st["budgets"] not in BUDGETS:
            raise ShapeError("budgets %r is not one of %s" % (st["budgets"], sorted(BUDGETS)))
        return (st["budgets"],) + BUDGETS[st["budgets"]][1:]
    if "budgets" in st:
        raise ShapeError("project.yaml budgets.agrees.%s sets this statement's budgets, so it names none" % key)
    return (None if is_own_pair(key, pair) else DEFAULT_BUDGETS[key],) + pair


def own_budgets(st, project):
    """The project's own (plain, sanitizer) bytes for statement `st`, or None when it uses a harness enum (and for
    every statement that is not an agreement)."""
    if st["kind"] != "agreement":
        return None
    enum, plain, san = agreement_budgets(st, project)
    return None if enum else (plain, san)


def budget_words(st, project):
    """(plain words, sanitizer words, own) for agreement statement `st`."""
    enum, plain, san = agreement_budgets(st, project)
    return size_words(plain), size_words(san), enum is None


def default_budget_words(san_build):
    """The default (plain, sanitizer) budgets in words for an agreement statement about `san_build`."""
    _, plain, san = BUDGETS[DEFAULT_BUDGETS[SANITIZER_KEY[san_build]]]
    return size_words(plain), size_words(san)


def term(st, project=None, *, distribution):
    """(parameters, body) of the Definition for statement fields `st`; `project` is the statement's
    project.yaml, whose project-level settings (`budgets`) the term depends on, and `distribution` says whether its
    harness.yaml has a distribution (a classifier-maybe statement is a bound with one, the empty maybe set without).
    Every caller says which: facts.Statement.term reads it from the statement's harness.

    `parameters` is the text between the name and the colon ("" or
    " (b : Q)")."""
    kind, builds, reading = st["kind"], st["builds"], st.get("reading")
    if kind not in CLASSIFIER_KINDS:
        for k in ("classifier", "originals"):
            if k in st:
                raise ShapeError("%s applies to classifier statements only" % k)
        if reading is None:
            raise ShapeError("a %s statement has a reading" % kind)
    if kind == "halts":
        if len(builds) != 1:
            raise ShapeError("a halts statement names exactly one build")
        ex = EXIT_SETS.get(exits_key(st.get("exits", "any")))
        if ex is None:
            raise ShapeError("exit set %r has no name in Shapes.Exits" % (st.get("exits"),))
        if reading == "budget":
            return "", "halts_within_budget %s %s %s" % (HALTS_BUDGET[0], ex, image(builds[0]))
        if reading == "may-fail":
            return "", "halts_may_fail %s %s" % (ex, image(builds[0]))
        raise ShapeError("halts statements have the readings budget and may-fail")
    if len(builds) != 2 or builds[0] != "plain" or builds[1] not in BUILD_IDENT or builds[1] == "plain":
        raise ShapeError("a pair statement names [plain, <sanitizer build>]")
    if "exits" in st:
        raise ShapeError("only halts statements have exits")
    if kind in CLASSIFIER_KINDS:
        return classifier_term(st, distribution=distribution)
    plain, san = image("plain"), image(builds[1])
    if kind == "agreement":
        shape = agreement_shape(st)
        env = (ENV[reading] + " ") if reading == "alloc-forced-only" else ""
        return "", "%s %s%s %s %s %s" % ((shape, env) + agreement_limits(st, project) + (plain, san))
    for k in ("budgets", "abort"):
        if k in st:
            raise ShapeError("%s applies to agreement statements only" % k)
    if reading not in ENV:
        raise ShapeError("pair statements have the readings may-fail and alloc-forced-only")
    gc = "_rv64gc" if st.get("machine") == "rv64gc" else ""
    if kind == "bound":
        return " (b : Q)", "disagrees_at_most%s %s Distribution.w Distribution.M %s %s b" % (gc, ENV[reading], plain, san)
    if kind == "decidability":
        return "", "agreement_decidable%s %s %s %s" % (gc, ENV[reading], plain, san)
    raise ShapeError("unknown kind %r" % kind)


def agreement_limits(st, project=None):
    """(plain-build limit, sanitizer-build limit) of agreement statement `st` as Rocq terms: the Budgets module's two
    limits when it uses a harness enum, else the project's own pair as literals (agreement_budgets)."""
    enum, plain_bytes, san_bytes = agreement_budgets(st, project)
    if enum:
        mod = BUDGETS[enum][0]
        return "%s.lim_source" % mod, "%s.lim_target" % mod
    return "0x%x%%Z" % plain_bytes, "0x%x%%Z" % san_bytes


# The classifier statements (theories/ClassifierShapes.v; docs/statements.md, "Classifier statements"), in the
# yes / no / maybe form: each names one classifier program of the pair, classifiers.<sanitizer build>.<a or b> in
# harness.yaml, which exits 0 for yes, 1 for no and 2 for maybe.
CLASSIFIER_KINDS = ("classifier-total", "classifier-sound", "classifier-maybe", "classifier-bound")
# the one classifier kind that names the builds, and so has a reading: the environment of the property it is sound for
READING_KINDS = ("classifier-sound",)


def takes_bound(kind, distribution):
    """Whether a statement of `kind`, in a harness with (`distribution` true) or without an input distribution, takes
    a bound (b : Q) first: a proof names its b (proof.yaml `bound`), and the statement depends on Distribution.v."""
    return kind in ("bound", "classifier-bound") or (kind == "classifier-maybe" and bool(distribution))


def classifier_ident(role, build):
    """The Images.v identifier of classifier `role` of the pair whose sanitizer build is `build`."""
    return "classifier_%s_%s" % (role, BUILD_IDENT[build])


def classifier_module(role, build):
    """The images/ module of classifier `role` of the pair whose sanitizer build is `build`."""
    return "Classifier%s%s" % (role.upper(), BUILD_MODULE[build])


def original_ident(build):
    return BUILD_IDENT[build] + "_original"


def original_module(build):
    return BUILD_MODULE[build] + "Original"


def classifier_image(role, build):
    return "Images." + classifier_ident(role, build)


def original_image(build):
    return "Images." + original_ident(build)


def classifier_term(st, *, distribution):
    """(parameters, body) of classifier statement `st`, whose builds are [plain, <sanitizer build>]: its kind and
    `classifier` (a or b) fix it, and for classifier-sound also `reading` and `originals`.  `originals: unpatched`
    names the originals, the builds without the patches (harness.yaml `originals`); `published` names the published
    builds in their place.  The classifier's own runs are judged with Env.forced_only (inside the shapes); `reading`
    is the environment of the property a sound classifier is sound for, so only classifier-sound has one.  A field a
    kind does not read is refused, so that no two spellings state one statement."""
    kind, builds, role = st["kind"], st["builds"], st.get("classifier")
    if role not in ("a", "b"):
        raise ShapeError("a classifier statement names its classifier, a or b")
    for k in ("budgets", "abort", "machine", "env"):
        if k in st:
            raise ShapeError("%s does not apply to a classifier statement" % k)
    if (kind in READING_KINDS) != ("reading" in st):
        raise ShapeError("a reading goes with a classifier-sound statement, and only there")
    if (kind == "classifier-sound") != ("originals" in st):
        raise ShapeError("originals goes with a classifier-sound statement, and only there")
    c = classifier_image(role, builds[1])
    if kind == "classifier-total":
        return "", "classifier_total3 %s" % c
    if kind == "classifier-maybe":
        if distribution:
            return " (b : Q)", "maybe_at_most %s Distribution.w Distribution.M b" % c
        return "", "maybe_empty %s" % c
    if kind == "classifier-bound":
        return " (b : Q)", "classifier_rejects_at_most %s Distribution.w Distribution.M b" % c
    reading = st["reading"]
    if reading not in ENV:
        raise ShapeError("classifier-sound statements have the readings may-fail and alloc-forced-only")
    if st["originals"] not in ("published", "unpatched"):
        raise ShapeError("originals is published or unpatched")
    plain, san = image("plain"), image(builds[1])
    if st["originals"] == "unpatched":
        plain_o, san_o = original_image("plain"), original_image(builds[1])
    else:
        plain_o, san_o = plain, san
    if role == "a":
        # A is sound for agreement of the two ORIGINALS: the pair without the patches
        return "", "classifies_good_inputs_sound %s %s %s %s" % (ENV[reading], plain_o, san_o, c)
    return "", "classifies_patch_diff_sound %s %s %s %s %s %s" % (ENV[reading], plain_o, plain, san_o, san, c)


def classifier_images(st):
    """[(what, build, role)] of the images classifier statement `st` names besides its builds, each as
    facts.Harness.image takes it: ("classifier", <its sanitizer build>, <its classifier, a or b>), and for an unpatched
    classifier-sound, ("original", <each of its builds>, None).  The fingerprint hashes each one's SHA-256, and rules.py
    holds harness.yaml to list each one and to list no classifier or original that no statement names."""
    builds = st["builds"]
    out = [("classifier", builds[-1], st.get("classifier"))]
    if st.get("originals") == "unpatched":
        out += [("original", b, None) for b in builds]
    return out


READING_ENV = {"may-fail": "may_fail", "alloc-forced-only": "alloc_forced_only", "budget": "forced_only"}


def agreement_shape(st):
    """The Shapes.v definition of agreement statement `st`; it does not depend on the budgets."""
    key = (st["reading"], st.get("abort", "error"), st.get("machine", "rv64g"))
    if key not in AGREEMENT:
        raise ShapeError("no agreement shape for reading/abort/machine %r" % (key,))
    return AGREEMENT[key]


def shape_name(st, *, distribution):
    """The Shapes.v (or ClassifierShapes.v) definition a statement uses; `distribution` as term() takes it, which
    chooses a classifier-maybe statement's shape."""
    return agreement_shape(st) if st["kind"] == "agreement" else term(st, distribution=distribution)[1].split()[0]


def templates(reading, san, with_distribution, machine="rv64g"):
    """The Characterise.v definitions for one (plain, san) pair: [(name, params, body)]."""
    s = BUILD_IDENT[san]
    gc = "_rv64gc" if machine == "rv64gc" else ""
    out = [("%s_classifies" % s, " (C : Image)",
            "classifies%s %s %s %s C" % (gc, ENV[reading], image("plain"), image(san)))]
    if with_distribution:
        out.append(("%s_classifier_rejects_at_most" % s, " (C : Image) (b : Q)",
                    "classifier_rejects_at_most C Distribution.w Distribution.M b"))
    return out


# The projects whose fuzz targets must carry the deviation record (harness.yaml `deviation`) and an `instance` on every
# statement but a classifier statement, which has no instance form: lint requires both (lint.check_deviation,
# lint.check_instances), and `oft check` fails a unit of such a project when a statement's instance has no lemma
# (check.check_instance).  It is here, in the checker, because oft check reads it, and deviation.py, which the
# enrolment writer and lint read, is not the checker (keys.NOT_THE_CHECKER): oft check never opens it.
REQUIRED = ()

# A statement's instance (harness.yaml statements.<s>.instance) is one process input on which every premise of the
# statement holds together.  Its lemma, <s>_instance in Instances/<s>.v of the fuzz target's proof library, proves
# instance_type of the input instance_input renders, named INSTANCE_INPUT (check.check_instance).
INSTANCE_INPUT = "oft_input"
# The argument vector of each instance path (theories/Driver.v): the driver reads the file only when argv has exactly
# two strings; with one, the distribution's first wrong-argument-count entry, it exits 2 and does not read it.
INSTANCE_ARGV = {"reaches-harness": "[%(prog)s; %(file)s]", "refused-by-driver": "[%(prog)s]"}
# The input file's name an instance takes on a harness with no distribution, beside argv0 the harness's own name: the
# names every distribution of the tree gives (input_file input.bin in each; argv0 the harness's name in most).
INSTANCE_INPUT_FILE = "input.bin"


def bytes_term(data):
    """The Rocq list of bytes `data`, as Distribution.v spells one: [Z_to_bv 8 102; Z_to_bv 8 117; ...]."""
    return "[%s]" % "; ".join("Z_to_bv 8 %d" % b for b in data)


def instance_finite(st):
    """Is the instance of statement `st` a finite input (FinProcInput) rather than a process input (ProcInput)?  It
    is for the kinds whose shapes term() writes over a distribution's finite inputs: bound (disagrees_at_most) and
    decidability (agreement_decidable)."""
    return st["kind"] in ("bound", "decidability")


def instance_abort(st):
    """The abort declaration of the process input of statement `st`'s instance: true for an agreement statement with
    abort: signal, whose shape reads valid_input_abort (agreement_premises), false for every other."""
    return st["kind"] == "agreement" and st.get("abort") == "signal"


def agreement_premises(st):
    """(input predicate, whether the budget premise is over run_scfg) of agreement statement `st`'s shape
    (theories/Shapes.v), from the fields that name the shape (agreement_shape): the predicate is valid_input, with
    _abort for abort: signal and _hwcap_rv64gc for machine: rv64gc; the budget premise is over run_scfg under the
    statement's environment for the reading alloc-forced-only (the agrees_in shapes), and over run for may-fail.
    ShapeError for fields that name no shape."""
    agreement_shape(st)
    predicate = "valid_input" + ("_abort" if st.get("abort") == "signal" else "") + (
        "_hwcap_rv64gc" if st.get("machine") == "rv64gc" else "")
    return predicate, st["reading"] == "alloc-forced-only"


def instance_input(h, st, data):
    """The Rocq term of the input of statement `st`'s instance, `h` being its harness.yaml and `data` the bytes of
    the instance file.  The argument vector follows the record's path (INSTANCE_ARGV), from the distribution's argv0
    and input_file, or, on a harness with no distribution, from the harness's name and INSTANCE_INPUT_FILE; the file
    system holds the input file with `data`.  A process input has the other fields of Premises.witness_input; a
    finite input (instance_finite) is MeasureLib's core_input of the file_core Distribution.v builds its entries with,
    over the file system [(input_file, [])]."""
    d = h.get("distribution") or {"argv0": h["harness"], "input_file": INSTANCE_INPUT_FILE}
    path = st["instance"]["path"]
    if path not in INSTANCE_ARGV:
        raise ShapeError("instance path %r has no input form" % (path,))
    prog, file = bytes_term(d["argv0"].encode()), bytes_term(d["input_file"].encode())
    argv = INSTANCE_ARGV[path] % {"prog": prog, "file": file}
    if instance_finite(st):
        return "core_input (file_core %s [] [(%s, [])] %s [] %s)" % (argv, file, file, bytes_term(data))
    return ("mkProcInput %s [] [(%s, %s)] IEof (Z_to_bv 64 0) (Z_to_bv 64 0) [] net_silent default_nofile "
            "(Z_to_bv 64 0) hwcap_rv64gc %s Sv48" % (argv, file, bytes_term(data),
                                                     "true" if instance_abort(st) else "false"))


def instance_type(st, project=None):
    """The type the lemma of statement `st`'s instance proves: the hypotheses of the statement's shape, the entries
    existential and the input INSTANCE_INPUT; `project` is the statement's project.yaml, whose budgets an agreement
    statement's limits depend on (agreement_limits).  The form comes from the fields that choose the shape in term()
    (kind, reading, abort, machine), and fields that choose no shape are refused there.  For the bound and
    decidability shapes, the finite input is valid and both builds have a valid entry on it (with the RV64GC word for
    machine: rv64gc): that the builds disagree on it is the event a bound measures, not a premise.  A classifier
    statement has no instance form (ShapeError; rules._classifier_statement refuses its `instance`)."""
    kind, builds, i = st["kind"], st["builds"], INSTANCE_INPUT
    if kind in CLASSIFIER_KINDS:
        raise ShapeError("a %s statement has no instance form" % kind)
    term(st, project, distribution=False)   # a classifier-maybe term alone reads it, and no classifier kind is here
    if kind == "halts":
        img = image(builds[0])
        entry = r"exists en, valid_entry %s en %s /\ valid_input %s" % (img, i, i)
        if st["reading"] == "budget":
            return entry + r" /\ ~ run_scfg_budget_refused forced_only_cfg %s %s en %s" % (img, HALTS_BUDGET[0], i)
        return entry
    plain, san = image("plain"), image(builds[1])
    if kind == "agreement":
        predicate, scfg = agreement_premises(st)
        lim = agreement_limits(st, project)[0]
        budget = ("run_scfg_budget_refused %s %s %s ep %s" % (ENV[st["reading"]], plain, lim, i) if scfg
                  else "run_budget_refused %s %s ep %s" % (plain, lim, i))
        return (r"exists ep es, valid_entry %s ep %s /\ valid_entry %s es %s /\ %s %s /\ ~ %s"
                % (plain, i, san, i, predicate, i, budget))
    p = "(to_proc_input %s)" % i
    hwcap = r" /\ in_hwcap %s = hwcap_rv64gc" % p if st.get("machine") == "rv64gc" else ""
    return (r"valid_fin_input %s%s /\ (exists ep es, valid_entry %s ep %s /\ valid_entry %s es %s)"
            % (i, hwcap, plain, p, san, p))


# The status a Rust or Go fuzz target exits with when it panics: the OSS Verify port's panic hook (Rust) or patched
# runtime (Go, for a panic on the fuzz target's goroutine; 80 on another) ends the process with it (docs/running.md),
# where a libFuzzer build would abort().
PANIC_STATUS = 79
# The status the process ends with when a fuzz target calls exit() during a call of the fuzz target, whatever
# argument it passes, unless a handler registered after the driver's guard ends the process first: the guard ends
# it with this one (docs/running.md, "What status 77 needs"; theories/Driver.v's harness_exited).  An exit() in
# LLVMFuzzerInitialize is not 77: a check records this in exit_reaches_guard (docs/facts.md, "A check").
HARNESS_EXIT_STATUS = 77
# The status a Python fuzz target exits with on an uncaught exception other than MemoryError and SystemExit: the OSS
# Verify port's interpreter host ends the process with it (docs/running.md), where atheris would report a crash.
PYTHON_UNCAUGHT_STATUS = 79
# The status a Go fuzz test exits with after t.Fatal, t.Error or t.Fail: the port's patched runtime and driver end the
# process with it, as they end a panic (docs/running.md), where OSS-Fuzz's build would crash.
GO_FAIL_STATUS = 79
STOP_STATUS = {"exit": HARNESS_EXIT_STATUS, "panic": PANIC_STATUS, "raise": PYTHON_UNCAUGHT_STATUS,
               "fail": GO_FAIL_STATUS}


def binds(check, st, harness):
    """Does a failure of `check`, a check of `harness`, contradict halts statement `st`?

    Computed, never read: a check that stops by abort, assert, trap or throw
    contradicts every halts statement; one that stops by a Rust or Go panic,
    by an uncaught Python exception other than SystemExit and MemoryError, or
    by t.Fatal, t.Error or t.Fail in a Go fuzz test (all three end the process
    with status 79), only a halts statement whose exit set leaves out that
    status; one that stops by exit()
    the same way with status 77, and only when its exit_reaches_guard is true;
    a print-only or return-only check contradicts nothing.  Only checks
    observed live in the binaries count, and only when the harness's
    failure_handlers is none: a handler that linked code installs (a signal
    handler, an exit handler registered after the driver's guard,
    std::set_terminate, a panic hook) can end a failed check with a status the
    statement allows, so with one present, or not read, the status is not
    established."""
    if st["kind"] != "halts" or check["live"] is not True or harness.get("failure_handlers") != "none":
        return False
    stop = check["stops_with"]
    if stop in ("abort", "assert", "trap", "throw"):
        return True
    if stop in STOP_STATUS:
        if stop == "exit" and check.get("exit_reaches_guard") is not True:
            return False
        exits = st.get("exits", "any")
        status = STOP_STATUS[stop]
        return exits != "any" and status not in exits
    return False
