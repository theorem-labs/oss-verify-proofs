"""The classifier and original images a harness can publish (harness.yaml `classifiers`, `originals`; docs/facts.md,
"Classifiers"), and the pin of the lps text that theories/ClassifierShapes.v copies
(rules.LPS_CLASSIFIER_NAMES_COPY)."""
import hashlib
import io
import os
import unittest

from oft import facts, fetch, lint, names, rules, shapes
from oft.tests.helpers import HERE, REPO, add_findings, edit, errors, tree

UNIT = "projects/zlib/checksum_fuzzer"
HARNESS = UNIT + "/harness.yaml"
SHAPES = "theories/ClassifierShapes.v"
# the nine sentences of the lps text that ClassifierShapes.v carries verbatim
BLOCK = os.path.join(HERE, "fixtures", "lps-classifier-names-block.v")
# stand-ins: the tests hash these, they are no binary's
SHA = {"a": "aa" * 32, "b": "bb" * 32, "plain": "cc" * 32, "asan": "dd" * 32}


def classifier(role, build="asan", **kw):
    rec = {"file": names.classifier_file("checksum_fuzzer", role, build), "bytes": 4096, "sha256": SHA[role],
           "segments": [1, 1]}
    rec.update(kw)
    return rec


def original(build, **kw):
    rec = {"file": names.original_file("checksum_fuzzer", build), "bytes": 8192, "sha256": SHA[build],
           "segments": [1, 1, 1, 1]}
    rec.update(kw)
    return rec


def shapes_file(block):
    return ("(** A stand-in of theories/ClassifierShapes.v. *)\nModule LpsBet618.\n" + block
            + "End LpsBet618.\n")


def block_text():
    with open(BLOCK, encoding="utf-8") as f:
        return f.read()


def eight(originals="unpatched", reading="alloc-forced-only"):
    """The eight classifier statements of the plain and asan pair, in the yes / no / maybe form: total, sound, maybe
    and bound, for A and B.  Only classifier-sound has a reading and originals."""
    out = {}
    for kind in shapes.CLASSIFIER_KINDS:
        for role in ("a", "b"):
            st = {"kind": kind, "builds": ["plain", "asan"], "classifier": role, "status": "open"}
            if kind in shapes.READING_KINDS:
                st.update(reading=reading, originals=originals)
            out[names.statement_name(kind, st["builds"], st.get("reading"), role)] = st
    return out


# the statements that name classifier b of the asan pair
NAMES_B = ("asan_cb_total", "asan_cb_sound", "asan_maybe_diff", "asan_bound_diff")


def with_images(t, change=None, statements=True):
    """Give zlib/checksum_fuzzer the two classifiers of its asan pair and the originals of plain and asan, and with
    `statements` the eight classifier statements that name them and the stand-in ClassifierShapes.v they need."""
    if statements:
        t.write(SHAPES, shapes_file(block_text()))

    def add(y):
        y["classifiers"] = {"asan": {"a": classifier("a"), "b": classifier("b")}}
        y["originals"] = {"plain": original("plain"), "asan": original("asan")}
        if statements:
            y["statements"].update(eight())
        if change:
            change(y)
    edit(t, HARNESS, add)


class Names(unittest.TestCase):
    def test_images_and_files(self):
        self.assertEqual((names.classifier_file("h", "a", "asan-ubsan"), names.classifier_ident("b", "asan-ubsan"),
                          names.classifier_module("a", "ubsan")),
                         ("h.classifier-a-asan-ubsan", "classifier_b_asan_ubsan", "ClassifierAUbsan"))
        self.assertEqual((names.original_ident("plain"), names.original_module("asan-ubsan"),
                          names.original_file("h", "asan")), ("plain_original", "AsanUbsanOriginal", "h.original-asan"))


class Rendering(unittest.TestCase):
    def test_images_dune_and_well_formedness(self):
        with tree() as t:
            with_images(t)
            self.assertEqual(errors(t), [])
            self.assertEqual(t.generate(), 0, t.last_output)
            iv = t.read(UNIT + "/Images.v")
            self.assertIn("Definition classifier_a_asan : Image := mkImage ClassifierAAsan.M.loaded_segments", iv)
            self.assertIn("Definition plain_original : Image := mkImage PlainOriginal.M.loaded_segments", iv)
            # every new image is checked well formed, as each build is, so no statement about it can hold because it
            # has no valid entry
            for ident in ("plain_original", "asan_original", "classifier_a_asan", "classifier_b_asan"):
                self.assertIn("Lemma %s_wf : image_wf %s.  Proof. check_image_wf. Qed." % (ident, ident), iv)
            dune = t.read(UNIT + "/images/dune")
            self.assertIn("ClassifierBAsan.v", dune)
            self.assertIn("projects/zlib/bin/checksum_fuzzer/checksum_fuzzer.classifier-b-asan", dune)
            self.assertIn("projects/zlib/bin/checksum_fuzzer/checksum_fuzzer.original-plain", dune)

    def test_a_harness_without_images_renders_as_main_does(self):
        """A harness with no classifier and no original renders what main renders: Statements.v imports Shapes and
        not ClassifierShapes, and neither Images.v nor images/dune names an original or a classifier."""
        with tree() as t:
            sv, iv, dune = (t.read(UNIT + rel) for rel in ("/Statements.v", "/Images.v", "/images/dune"))
        self.assertRegex(sv, r"\.Core Require Import Shapes\.\n")
        self.assertNotIn("ClassifierShapes", sv)
        self.assertNotRegex(iv, r"\w_original\b|\bclassifier_\w")
        for part in (".original-", ".classifier-"):
            self.assertNotIn(part, dune)

    def test_published_images_lists_every_pinned_binary(self):
        def held(y):
            rec = y["classifiers"]["asan"]["b"]
            for k in ("bytes", "sha256", "segments"):
                rec.pop(k)
            rec["withheld"] = "not-yet-published"
            # a statement that names a withheld image is withheld too
            for name in NAMES_B:
                y["statements"][name].update(status="withheld", withheld="not-yet-published")
        with tree() as t:
            with_images(t, held)
            self.assertEqual(errors(t), [])
            h = facts.load(t.root).projects["zlib"].harnesses["checksum_fuzzer"]
            got = h.published_images()
            # a withheld image is not published; each is its Images.v identifier, its images/ module and its file
            self.assertEqual([i for i, _m, _rec, _rel in got],
                             ["plain", "ubsan", "asan", "asan_ubsan", "plain_original", "asan_original",
                              "classifier_a_asan"])
            self.assertEqual([m for _i, m, _rec, _rel in got][4:], ["PlainOriginal", "AsanOriginal", "ClassifierAAsan"])
            self.assertEqual([rel for _i, _m, _rec, rel in got][4:],
                             ["projects/zlib/bin/checksum_fuzzer/checksum_fuzzer." + f
                              for f in ("original-plain", "original-asan", "classifier-a-asan")])
            # the images a classifier statement names are looked up as shapes.classifier_images gives them
            st = h.statements["asan_ca_sound"]
            self.assertEqual(shapes.classifier_images(st.data),
                             [("classifier", "asan", "a"), ("original", "plain", None), ("original", "asan", None)])
            self.assertEqual([h.image(*t)["file"] for t in shapes.classifier_images(st.data)],
                             ["checksum_fuzzer." + f for f in ("classifier-a-asan", "original-plain", "original-asan")])
            with self.assertRaisesRegex(ValueError, "'build'"):
                h.image("build", "asan")


class Rules(unittest.TestCase):
    def found(self, change=None):
        with tree() as t:
            with_images(t, change)
            return [str(e) for e in errors(t)]

    def assert_found(self, text, change=None):
        got = self.found(change)
        self.assertTrue(any(text in e for e in got), "%r not in %r" % (text, got))

    def test_a_classifier_pair_is_keyed_by_a_listed_sanitizer_build(self):
        def plain_pair(y):
            y["classifiers"]["plain"] = {"a": classifier("a", build="ubsan")}
        self.assert_found("keyed by a sanitizer build", plain_pair)

    def test_an_empty_classifier_pair_is_refused(self):
        def empty(y):
            y["classifiers"]["ubsan"] = {}
        self.assert_found("classifiers.ubsan: a classifier pair lists a, b or both", empty)

    def test_the_file_name_and_the_pin(self):
        self.assert_found("classifiers.asan.a.file must be checksum_fuzzer.classifier-a-asan",
                          lambda y: y["classifiers"]["asan"]["a"].update(file="checksum_fuzzer.classifier-a-ubsan"))
        self.assert_found("a published image has bytes, sha256 and segments",
                          lambda y: y["classifiers"]["asan"]["a"].pop("sha256"))
        self.assert_found("originals.plain.file must be checksum_fuzzer.original-plain",
                          lambda y: y["originals"]["plain"].update(file="checksum_fuzzer.original-asan"))

    def test_a_withheld_image_shows_no_pin(self):
        def held(y):
            y["classifiers"]["asan"]["a"]["withheld"] = "not-yet-published"
        self.assert_found("a withheld image shows no bytes, sha256 or segments", held)

    def test_a_withheld_image_asks_for_the_project_s_flag(self):
        """lint.check_disclosure reads the reason of a withheld image as it does a withheld build's: its project says
        that it withholds something for that reason (project.yaml `withheld`), and says so only while something is.
        Here the asan original alone is withheld for source-bundle: the one statement that names it, asan_cb_sound,
        is withheld for not-yet-published, the reason of classifier B, which it also names."""
        def held(y):
            for rec, reason in ((y["classifiers"]["asan"]["b"], "not-yet-published"),
                                (y["originals"]["asan"], "source-bundle")):
                for k in ("bytes", "sha256", "segments"):
                    rec.pop(k)
                rec["withheld"] = reason
            del y["statements"]["asan_ca_sound"]
            for name in NAMES_B:
                y["statements"][name].update(status="withheld", withheld="not-yet-published")
        with tree() as t:
            with_images(t, held)
            self.assertEqual(errors(t), [])
            got = [f.msg for f in lint.check_disclosure(facts.load(t.root))]
            self.assertIn("withholds an item (source-bundle) but does not say so: add withheld.source_bundle", got)
            edit(t, "projects/zlib/project.yaml", lambda y: y["withheld"].update(source_bundle=True))
            self.assertEqual([f.msg for f in lint.check_disclosure(facts.load(t.root))], [])

    def test_an_original_is_the_unpatched_binary_the_findings_run_on(self):
        bad = "its sha256 is not the one unpatched.yaml pins for the same build"
        with tree() as t:
            add_findings(t)
            with_images(t)
            got = [str(e) for e in errors(t)]
            self.assertTrue(any("originals.plain: " + bad in e for e in got), got)
            pins = facts.load(t.root).unpatched["zlib"]["harnesses"]["checksum_fuzzer"]
            edit(t, HARNESS, lambda y: [y["originals"][b].update(sha256=pins[b]["sha256"]) for b in ("plain", "asan")])
            got = [str(e) for e in errors(t)]
            self.assertFalse(any(bad in e for e in got), got)

    def test_images_move_no_other_fingerprint(self):
        with tree() as t:
            before = {s.id: s.fingerprint for s in facts.load(t.root).statements()}
            with_images(t)
            after = {s.id: s.fingerprint for s in facts.load(t.root).statements()}
            self.assertEqual({k: after[k] for k in before}, before)
            self.assertEqual(sorted(set(after) - set(before)), sorted("zlib/checksum_fuzzer/" + n for n in eight()))


class FetchAndCheck(unittest.TestCase):
    def test_a_missing_or_changed_classifier_or_original_is_refused(self):
        with tree() as t:
            data = b"stand-in original"
            with_images(t, lambda y: y["originals"]["plain"].update(bytes=len(data),
                                                                    sha256=hashlib.sha256(data).hexdigest()))
            bin_dir = "projects/zlib/bin/checksum_fuzzer/"
            t.write(bin_dir + names.original_file("checksum_fuzzer", "plain"), data.decode())
            t.write(bin_dir + names.classifier_file("checksum_fuzzer", "a", "asan"), "not the pinned bytes")
            h = facts.load(t.root).projects["zlib"].harnesses["checksum_fuzzer"]
            out = io.StringIO()
            n, _bad = fetch.verify_builds(t.root, h, out)
            lines = out.getvalue().splitlines()
            self.assertIn(bin_dir + "checksum_fuzzer.classifier-a-asan: does not match its SHA-256 in harness.yaml",
                          lines)
            self.assertIn(bin_dir + "checksum_fuzzer.classifier-b-asan: missing (run ./oft fetch zlib)", lines)
            self.assertIn(bin_dir + "checksum_fuzzer.original-asan: missing (run ./oft fetch zlib)", lines)
            self.assertFalse([x for x in lines if "original-plain" in x], lines)
            self.assertEqual(n, len(h.published_images()))


class LpsCopy(unittest.TestCase):
    """theories/ClassifierShapes.v carries the classifier definitions of the lps commit that
    rules.LPS_CLASSIFIER_NAMES_COPY names verbatim until the pinned lps has them; oft lint pins those bytes, so neither
    an edit of the copy nor a move of the pin changes the yes / no / maybe layer unseen."""

    def test_the_fixture_is_the_pinned_text(self):
        with open(BLOCK, "rb") as f:
            self.assertEqual(hashlib.sha256(f.read()).hexdigest(), rules.LPS_CLASSIFIER_NAMES_COPY["sha256"])

    def test_the_copy_must_stay_the_lps_text(self):
        bad = ("its copy of the lps definitions is not the text of lps %s"
               % rules.LPS_CLASSIFIER_NAMES_COPY["commit"][:12])
        with tree() as t:
            t.write(SHAPES, shapes_file(block_text()))
            self.assertFalse([e for e in map(str, errors(t)) if SHAPES in e])
            # one changed argument, the published build in the place of its original, is refused
            t.write(SHAPES, shapes_file(block_text().replace("agree_s cfg O1 P1", "agree_s cfg P1 O1")))
            self.assertTrue(any(bad in e for e in map(str, errors(t))))
            t.write(SHAPES, "(** no copy *)\n")
            self.assertTrue(any("carries no single copy of the lps definitions" in e for e in map(str, errors(t))))

    @unittest.skipUnless(os.path.isfile(os.path.join(REPO, SHAPES)), "theories/ is not in this checkout")
    def test_this_repository_carries_the_pinned_copy(self):
        with open(os.path.join(REPO, SHAPES), "rb") as f:
            data = f.read()
        begin, end = (rules.LPS_CLASSIFIER_NAMES_COPY[k].encode() for k in ("begin", "end"))
        block = data[data.index(begin) + len(begin):data.index(end)]
        self.assertEqual(hashlib.sha256(block).hexdigest(), rules.LPS_CLASSIFIER_NAMES_COPY["sha256"])


if __name__ == "__main__":
    unittest.main()
