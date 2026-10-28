"""Closed schemas for the facts files (lint rule `schema`).

The schemas themselves are data, in tools/oft/schemas/*.yaml, in a small
vocabulary: object (closed: an unlisted key is an error), map, list, union,
enum, const, str, text, int, bool, ref, and the named scalar types in
SCALARS below.  `validate(kind, data)` returns a list of error strings; an
empty list means the document is well formed.  Rules that relate one field
to another (a reason is required unless a project is available, a statement's
name follows from its fields, ...) are in rules.py.
"""
import datetime
import os
import re

from . import yamlio

HERE = os.path.dirname(os.path.abspath(__file__))
KINDS = ("project", "harness", "release", "proof", "counterexample", "finding", "unpatched", "approvals")

BUILDS = ("plain", "ubsan", "asan", "asan-ubsan")
SANITIZER_BUILDS = BUILDS[1:]

# The OSS Verify port, and this repository's internal copy, which keeps the port's branches under oss-verify-port/
# and which only a project a finding holds back builds from.
OSS_VERIFY_REPOSITORY = "theorem-labs/oss-verify"
INTERNAL_PORT_REPOSITORY = "theorem-labs/oss-verify-proofs" + "-internal"

SCALARS = {
    "project-name": r"[a-z0-9][a-z0-9_-]{0,99}",
    "harness-name": r"[A-Za-z0-9][A-Za-z0-9._+-]{0,149}",
    "statement-name": r"[a-z][a-z0-9_]{0,99}",
    "statement-id": r"[a-z0-9][a-z0-9_-]*/[A-Za-z0-9][A-Za-z0-9._+-]*/[a-z][a-z0-9_]*",
    "fuzz-target": r"[a-z0-9][a-z0-9_-]{0,99}/[A-Za-z0-9][A-Za-z0-9._+-]{0,149}",
    "reason-code": r"[a-z][a-z-]{0,39}",
    "feature": r"[a-z][a-z0-9-]{0,39}",
    "sha256": r"[0-9a-f]{64}",
    "commit": r"[0-9a-f]{40}",
    "url": r"https://[A-Za-z0-9.-]+(/[^\s<>\"'`]*)?",
    "date": r"[0-9]{4}-[0-9]{2}-[0-9]{2}",
    "spdx": r"[A-Za-z0-9.+-]+( (AND|OR|WITH) [A-Za-z0-9.+-]+)*|\(.+\)( (AND|OR) .+)*",
    "fraction": r"(0|[1-9][0-9]*)(/[1-9][0-9]*)?",
    "image": r"ghcr\.io/theorem-labs/[a-z0-9._/-]+@sha256:[0-9a-f]{64}",
    "release-version": r"[0-9]{4}\.[0-9]{1,2}\.[0-9]+(-rc\.[0-9]+)?",
    # v<release>, or v<release>-src: a second release holding source assets and, for projects a recipe built, a build
    # recipe (a GitHub release holds at most 1,000 files)
    "release-tag": r"v[0-9]{4}\.[0-9]{1,2}\.[0-9]+(-rc\.[0-9]+)?(-src)?",
    # A project asset may instead live on its internal findings-<project>
    # release while a finding holds that project back.
    "asset-release-tag": r"v[0-9]{4}\.[0-9]{1,2}\.[0-9]+(-rc\.[0-9]+)?(-src)?|findings-[a-z0-9][a-z0-9_-]*",
    "oss-verify-repository": "|".join(re.escape(r) for r in (OSS_VERIFY_REPOSITORY, INTERNAL_PORT_REPOSITORY)),
    "build-name": "|".join(re.escape(b) for b in BUILDS),
    "archive-name": r"[A-Za-z0-9._+-]+\.a",
    # an SPDX expression whose parenthesised groups may sit anywhere, as a library's own files state it
    "spdx-expression": r"\(*[A-Za-z0-9.+-]+\)*( (AND|OR|WITH) \(*[A-Za-z0-9.+-]+\)*)*",
}

_CONTROL = re.compile(r"[\x00-\x08\x0b-\x1f\x7f]")

_SCHEMAS = {}


def load_schema(kind):
    if kind not in _SCHEMAS:
        _SCHEMAS[kind] = yamlio.load_file(os.path.join(HERE, "schemas", kind + ".yaml"))
    return _SCHEMAS[kind]


def validate(kind, data):
    """Structural errors in `data` against schemas/<kind>.yaml."""
    s = load_schema(kind)
    errors = []
    _check(s["root"], data, kind, s["defs"], errors)
    return errors


def validate_def(kind, name, value, path):
    """Structural errors in `value` against the definition `name` of schemas/<kind>.yaml, reported at `path`."""
    s = load_schema(kind)
    errors = []
    _check(s["defs"][name], value, path, s["defs"], errors)
    return errors


def _check(spec, value, path, defs, errors):
    t = spec["type"]
    err = errors.append
    if t == "ref":
        return _check(defs[spec["name"]], value, path, defs, errors)
    if t == "object":
        if not isinstance(value, dict):
            return err("%s: expected a mapping" % path)
        fields = spec["fields"]
        for key in value:
            if key not in fields:
                err("%s: unknown key %r" % (path, key))
        for key, sub in fields.items():
            if key not in value:
                if not sub.get("optional"):
                    err("%s: missing key %r" % (path, key))
                continue
            _check(sub, value[key], "%s.%s" % (path, key), defs, errors)
        return
    if t == "map":
        if not isinstance(value, dict) or not value:
            return err("%s: expected a non-empty mapping" % path)
        for key, sub in value.items():
            if not isinstance(key, str) or not _scalar_ok(spec["keys"], key):
                err("%s: bad key %r (want %s)" % (path, key, spec["keys"]))
            _check(spec["values"], sub, "%s.%s" % (path, key), defs, errors)
        return
    if t == "list":
        if not isinstance(value, list):
            return err("%s: expected a list" % path)
        if len(value) < spec.get("min", 0):
            err("%s: at least %d item(s) required" % (path, spec["min"]))
        for i, item in enumerate(value):
            _check(spec["items"], item, "%s[%d]" % (path, i), defs, errors)
        return
    if t == "union":
        for alt in spec["of"]:
            trial = []
            _check(alt, value, path, defs, trial)
            if not trial:
                return
        return err("%s: %r matches none of the allowed forms" % (path, value))
    if t == "const":
        if value != spec["value"] or type(value) is not type(spec["value"]):
            err("%s: must be %r, got %r" % (path, spec["value"], value))
        return
    if t == "enum":
        if not any(value == v and type(value) is type(v) for v in spec["values"]):
            err("%s: %r is not one of %s" % (path, value, spec["values"]))
        return
    if t == "bool":
        if not isinstance(value, bool):
            err("%s: expected true or false" % path)
        return
    if t == "int":
        if not isinstance(value, int) or isinstance(value, bool):
            return err("%s: expected an integer" % path)
        if "min" in spec and value < spec["min"]:
            err("%s: %d is below %d" % (path, value, spec["min"]))
        if "max" in spec and value > spec["max"]:
            err("%s: %d is above %d" % (path, value, spec["max"]))
        return
    if t in ("str", "text"):
        if not isinstance(value, str) or not value.strip():
            return err("%s: expected a non-empty string" % path)
        if value != value.strip():
            err("%s: leading or trailing whitespace" % path)
        if _CONTROL.search(value) or (t == "str" and "\n" in value):
            err("%s: control characters or line breaks" % path)
        if len(value) > spec.get("max", 200 if t == "str" else 2000):
            err("%s: longer than %d characters" % (path, spec.get("max", 200 if t == "str" else 2000)))
        if "pattern" in spec and not re.search(spec["pattern"], value):
            err("%s: %r does not match %s" % (path, value, spec["pattern"]))
        return
    if t in SCALARS:
        if not isinstance(value, str) or not _scalar_ok(t, value):
            err("%s: %r is not a valid %s" % (path, value, t))
        return
    raise ValueError("schema error at %s: unknown type %r" % (path, t))


def _scalar_ok(t, value):
    if not re.fullmatch(SCALARS[t], value):
        return False
    if t == "date":
        try:
            datetime.date.fromisoformat(value)
        except ValueError:
            return False
    return True


def fraction_value(s):
    """'3/50' -> (3, 50); '1' -> (1, 1)."""
    n, _, d = s.partition("/")
    return int(n), int(d or 1)
