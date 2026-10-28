"""Strict YAML for the facts files.

Four differences from yaml.safe_load, all on purpose:

- a mapping that repeats a key is an error (PyYAML silently keeps the last);
- only plain scalars `true`, `false`, `null`/`~`/empty, decimal integers and
  decimal floats are typed.  Dates, `yes`/`no`/`on`/`off`, octal, hex and
  sexagesimal numbers stay strings, so `2026-11-02` is the string it looks
  like and a harness named `on` is not a boolean;
- collections nested more than MAX_DEPTH deep are an error;
- an alias is an error: it repeats a node the text gives once, so a few
  aliases of aliases build a document far larger than its file.

`dump` writes the canonical form the generator and the exporter both use:
block style, keys in the order given, no aliases, LF line ends.

The loader parses with libyaml (the pinned PyYAML wheels carry it), about ten
times faster than PyYAML's pure-Python parser, with the same resolvers and
constructors.  libyaml builds the node tree recursively in C, where a text
nested deep enough overflows the stack and kills the process, and the
constructors and every reader of the data recurse in Python; so the depth is
first read from libyaml's events, which its parser produces with a stack of
its own.  A text libyaml cannot parse is parsed once more by the pure-Python
parser, only so the error reads as it always has (with the line it points
at); a result never comes from it.
"""
import re

import yaml


class YamlError(ValueError):
    pass


# Far deeper than any facts file nests, and shallow enough for every reader of the data to recurse.
MAX_DEPTH = 64
_OPEN = (yaml.SequenceStartEvent, yaml.MappingStartEvent)
_CLOSE = (yaml.SequenceEndEvent, yaml.MappingEndEvent)


class StrictLoader(yaml.CSafeLoader):
    pass


class _WordingLoader(yaml.SafeLoader):
    pass


def _mapping(loader, node, deep=False):
    loader.flatten_mapping(node)
    out = {}
    for key_node, value_node in node.value:
        key = loader.construct_object(key_node, deep=deep)
        if key in out:
            raise YamlError("duplicate key %r at line %d" % (key, key_node.start_mark.line + 1))
        out[key] = loader.construct_object(value_node, deep=deep)
    return out


for _L in (StrictLoader, _WordingLoader):
    _L.yaml_implicit_resolvers = {}
    _L.add_implicit_resolver("tag:yaml.org,2002:bool", re.compile(r"^(?:true|false)$"), list("tf"))
    _L.add_implicit_resolver("tag:yaml.org,2002:null", re.compile(r"^(?:~|null|)$"), ["~", "n", ""])
    _L.add_implicit_resolver("tag:yaml.org,2002:int", re.compile(r"^-?(?:0|[1-9][0-9]*)$"), list("-0123456789"))
    _L.add_implicit_resolver(
        "tag:yaml.org,2002:float", re.compile(r"^-?(?:0|[1-9][0-9]*)\.[0-9]+$"), list("-0123456789"))
    _L.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG, _mapping)


def _refused(text, limit):
    """Why text is refused before it is built, or None: collections nested more than limit deep, or an alias.  Read
    from libyaml's events up to the first error, if any (the load reports it)."""
    parser = StrictLoader(text)
    depth = 0
    try:
        for event in iter(parser.get_event, None):
            if isinstance(event, yaml.AliasEvent):
                return "an alias (*%s) at line %d: the facts give every value once" % (
                    event.anchor, event.start_mark.line + 1)
            if isinstance(event, _OPEN):
                depth += 1
                if depth > limit:
                    return "collections nested more than %d deep" % limit
            elif isinstance(event, _CLOSE):
                depth -= 1
    except yaml.YAMLError:
        pass
    finally:
        parser.dispose()
    return None


def load(text, where="<yaml>"):
    refused = _refused(text, MAX_DEPTH)
    if refused:
        raise YamlError("%s: %s" % (where, refused))
    try:
        return yaml.load(text, Loader=StrictLoader)
    except YamlError as e:
        raise YamlError("%s: %s" % (where, e)) from None
    except yaml.YAMLError as e:
        error = e
    try:
        yaml.load(text, Loader=_WordingLoader)
    except (YamlError, yaml.YAMLError) as e:
        error = e
    raise YamlError("%s: %s" % (where, error)) from None


def load_file(path):
    with open(path, encoding="utf-8") as f:
        return load(f.read(), where=str(path))


def compose(text):
    """The document's node tree, whose nodes carry the lines they are written
    on, or None when the text is not one YAML document."""
    try:
        return yaml.compose(text, Loader=StrictLoader)
    except yaml.YAMLError:
        return None


def mapping_value(node, key):
    """The value node of key in a mapping node, or None."""
    if not isinstance(node, yaml.MappingNode):
        return None
    for key_node, value_node in node.value:
        if getattr(key_node, "value", None) == key:
            return value_node
    return None


class _Dumper(yaml.SafeDumper):
    def ignore_aliases(self, data):
        return True


def _str(dumper, s):
    style = "|" if "\n" in s else None
    return dumper.represent_scalar("tag:yaml.org,2002:str", s, style=style)


_Dumper.add_representer(str, _str)


def dump(data):
    return yaml.dump(data, Dumper=_Dumper, sort_keys=False, allow_unicode=True,
                     default_flow_style=False, width=100)
