"""./oft finds the packages tools/oft/requirements.txt pins, and a run that reaches a missing one says which
requirement it is and where it looked, from a lint worker process too.

Before this, `./oft lint` on a box that does not ship idna died with a bare `ModuleNotFoundError: No module named
'idna'` raised inside one of lint.forked_map's workers, which named neither the requirement as a requirement nor
any directory (OSSV-175)."""
import os
import pickle
import re
import sys
import unittest
from unittest import mock

from oft import __main__ as cli
from oft import lint

TOOLS = os.path.dirname(os.path.dirname(os.path.abspath(cli.__file__)))
ROOT = os.path.dirname(TOOLS)
WRAPPER = os.path.join(ROOT, "oft")
REQUIREMENTS = os.path.join(TOOLS, "oft", "requirements.txt")


def pin_line(dist):
    """The line of requirements.txt that pins DIST, as the message quotes it, or None."""
    with open(REQUIREMENTS, encoding="utf-8") as f:
        for line in f:
            if re.match(r"%s\s*==" % re.escape(dist), line, re.I):
                return line.rstrip().rstrip("\\").rstrip()
    return None


def pinned():
    """The distributions requirements.txt pins, in its order."""
    with open(REQUIREMENTS, encoding="utf-8") as f:
        return [m.group(1) for m in (re.match(r"([A-Za-z0-9._-]+)==", line) for line in f) if m]


class Requirements(unittest.TestCase):
    """The two lists of requirements outside requirements.txt -- the wrapper's probe and __main__.REQUIREMENTS --
    name every distribution it pins, so a requirement added there cannot be missed by either."""

    IMPORT_NAME = {"PyYAML": "yaml"}   # a distribution whose import name is not its own

    def test_requirements_txt_pins_what_the_tools_import(self):
        self.assertEqual(sorted(pinned()), ["PyYAML", "idna"])

    def test_the_wrapper_probes_every_pinned_distribution(self):
        with open(WRAPPER, encoding="utf-8") as f:
            found = re.search(r'^oft_imports="([^"]*)"$', f.read(), re.M)
        self.assertIsNotNone(found, "./oft has no oft_imports line")
        probed = sorted(n.strip() for n in found.group(1).split(","))
        self.assertEqual(probed, sorted(self.IMPORT_NAME.get(d, d) for d in pinned()))

    def test_main_names_the_distribution_of_every_pinned_import(self):
        self.assertEqual(sorted(cli.REQUIREMENTS.values()), sorted(pinned()))
        for name, dist in cli.REQUIREMENTS.items():
            self.assertEqual(name, self.IMPORT_NAME.get(dist, dist))


class MissingRequirement(unittest.TestCase):
    """The message for a pinned requirement that is not installed."""

    def said(self, exc):
        said = cli._missing_requirement(exc)
        self.assertIsNotNone(said, "no message for %r" % (exc,))
        return said

    def test_it_names_the_requirement_its_pin_and_every_directory_it_looked_in(self):
        said = self.said(ModuleNotFoundError("No module named 'idna'", name="idna"))
        self.assertIn("the pinned requirement idna is not installed", said)
        self.assertIn(pin_line("idna"), said)
        self.assertIn(REQUIREMENTS, said)
        for entry in sys.path:
            self.assertIn(entry or os.getcwd(), said)
        self.assertIn("tools/oft/requirements.txt", said)
        self.assertIn("uv", said)

    def test_a_submodule_of_a_requirement_names_the_requirement(self):
        self.assertIn("the pinned requirement PyYAML is not installed",
                      self.said(ModuleNotFoundError("No module named 'yaml.cyaml'", name="yaml.cyaml")))

    def test_an_error_about_anything_else_keeps_its_traceback(self):
        """Only a requirement is reported this way: a module of the tools that is missing is a fault of the tools,
        and must not be presented as an install the reader has to make."""
        for exc in (ModuleNotFoundError("No module named 'oft.nowhere'", name="oft.nowhere"),
                    ModuleNotFoundError("No module named 'numpy'", name="numpy"),
                    ModuleNotFoundError("something else")):
            self.assertIsNone(cli._missing_requirement(exc))

    def test_an_error_that_lost_its_name_is_read_from_its_message(self):
        """concurrent.futures sends a worker's exception back pickled; an exception that arrives without its name
        attribute is still named by the text, which is what the reader sees."""
        exc = ModuleNotFoundError("No module named 'idna'")
        self.assertIsNone(exc.name)
        self.assertIn("the pinned requirement idna is not installed", self.said(exc))


class FromAWorker(unittest.TestCase):
    """The error of a lint worker process reaches the user as this message: that is where it was lost."""

    def test_a_pool_worker_s_missing_requirement_survives_the_trip_back(self):
        """lint.forked_map re-raises a worker's exception in this process. The exception travels pickled, so the
        name it carries must survive that trip for the message to name the requirement."""
        def boom(item):
            raise ModuleNotFoundError("No module named 'idna'", name="idna")

        back = pickle.loads(pickle.dumps(ModuleNotFoundError("No module named 'idna'", name="idna")))
        self.assertIn("the pinned requirement idna is not installed", cli._missing_requirement(back))
        with self.assertRaises(ModuleNotFoundError) as raised:
            lint.forked_map(boom, ["a", "b"], 2, chunksize=1)
        self.assertIsNotNone(cli._missing_requirement(raised.exception))

    def test_run_exits_with_the_message_and_no_traceback(self):
        """What the user sees for a command whose worker could not import the requirement: the message, as the
        status of SystemExit, and no traceback through concurrent.futures."""
        def boom(item):
            raise ModuleNotFoundError("No module named 'idna'", name="idna")

        with mock.patch.object(cli, "main", lambda argv=None: lint.forked_map(boom, ["a", "b"], 2, chunksize=1)):
            with self.assertRaises(SystemExit) as raised:
                cli.run([])
        self.assertIn("the pinned requirement idna is not installed", str(raised.exception.code))

    def test_run_keeps_an_error_that_is_not_a_requirement(self):
        with mock.patch.object(cli, "main", lambda argv=None: __import__("oft.nowhere")):
            with self.assertRaises(ModuleNotFoundError):
                cli.run([])


if __name__ == "__main__":
    unittest.main()
