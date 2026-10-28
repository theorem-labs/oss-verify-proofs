"""From a statement's typed fields to its Rocq text.

Each statement in a harness.yaml names one definition of
theories/Shapes.v (OssFuzzTheorems.Core.Shapes) and its arguments.  This
module is the only place that choice is made; a combination it does not
list is an error, never a guess.
"""
import re

from . import names, schema

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
SIZE = re.compile(schema.load_schema("project")["defs"]["size"]["pattern"])

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
# harness whose fuzz target returns one to turn an input away lists where (harness.yaml `rejects`), and its halts
# statements allow this status too.
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


def exits_key(exits):
    return "any" if exits == "any" else tuple(sorted(set(exits)))


def image(build):
    return "Images." + names.BUILD_IDENT[build]


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


def term(st, project=None):
    """(parameters, body) of the Definition for statement fields `st`; `project` is the statement's
    project.yaml, whose project-level settings (`budgets`) the term depends on.

    `parameters` is the text between the name and the colon ("" or
    " (b : Q)")."""
    kind, builds, reading = st["kind"], st["builds"], st["reading"]
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
    if len(builds) != 2 or builds[0] != "plain" or builds[1] not in names.BUILD_IDENT or builds[1] == "plain":
        raise ShapeError("a pair statement names [plain, <sanitizer build>]")
    if "exits" in st:
        raise ShapeError("only halts statements have exits")
    plain, san = image("plain"), image(builds[1])
    if kind == "agreement":
        shape = agreement_shape(st)
        enum, plain_bytes, san_bytes = agreement_budgets(st, project)
        if enum:
            mod = BUDGETS[enum][0]
            lims = "%s.lim_source %s.lim_target" % (mod, mod)
        else:
            lims = "0x%x%%Z 0x%x%%Z" % (plain_bytes, san_bytes)
        env = (ENV[reading] + " ") if reading == "alloc-forced-only" else ""
        return "", "%s %s%s %s %s" % (shape, env, lims, plain, san)
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


READING_ENV = {"may-fail": "may_fail", "alloc-forced-only": "alloc_forced_only", "budget": "forced_only"}


def agreement_shape(st):
    """The Shapes.v definition of agreement statement `st`; it does not depend on the budgets."""
    key = (st["reading"], st.get("abort", "error"), st.get("machine", "rv64g"))
    if key not in AGREEMENT:
        raise ShapeError("no agreement shape for reading/abort/machine %r" % (key,))
    return AGREEMENT[key]


def shape_name(st):
    """The Shapes.v definition a statement uses."""
    return agreement_shape(st) if st["kind"] == "agreement" else term(st)[1].split()[0]


def templates(reading, san, with_distribution, machine="rv64g"):
    """The Characterise.v definitions for one (plain, san) pair: [(name, params, body)]."""
    s = names.BUILD_IDENT[san]
    gc = "_rv64gc" if machine == "rv64gc" else ""
    out = [("%s_classifies" % s, " (C : Image)",
            "classifies%s %s %s %s C" % (gc, ENV[reading], image("plain"), image(san)))]
    if with_distribution:
        out.append(("%s_classifier_rejects_at_most" % s, " (C : Image) (b : Q)",
                    "classifier_rejects_at_most C Distribution.w Distribution.M b"))
    return out


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
