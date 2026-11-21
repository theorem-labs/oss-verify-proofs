"""units.load reads a unit's images from its Images.v: an image for each harness.yaml build, and the images of the
originals and classifiers harness.yaml lists, which oft generate also writes there; any other image is refused.

Run from tools/: python3 -m unittest discover -s budgetwit -t . -p test_units.py"""
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest

from . import units


LIB_DUNE = "(include_subdirs qualified)\n(rocq.theory\n (name P.proofs.lib))\n"
BUILDS = "builds:\n  plain: {file: h.plain}\n  asan: {file: h.asan}\n"
# the builds, with an original of the plain build and classifier a of the asan pair, as oft's yamlio writes them
HARNESS = BUILDS + ("classifiers:\n  asan:\n    a:\n      file: h.classifier-a-asan\n"
                    "originals:\n  plain:\n    file: h.original-plain\n")


def image_line(ident, module):
    """The line oft generate's Images.v holds for one image."""
    return f"Definition {ident} : Image := mkImage {module}.M.loaded_segments {module}.M.init_pc {module}.M.phdrs.\n"


def load_with_images(root, images, harness=HARNESS):
    """units.load of a unit p/h under root whose harness.yaml is `harness` and whose Images.v defines `images`,
    [(identifier, module)]."""
    directory = root / "projects" / "p" / "h"
    (directory / "proofs" / "lib").mkdir(parents=True)
    (directory / "proofs" / "lib" / "dune").write_text(LIB_DUNE, encoding="utf8")
    (directory / "harness.yaml").write_text(harness, encoding="utf8")
    (directory / "Images.v").write_text("".join(image_line(*i) for i in images), encoding="utf8")
    return units.load("p/h", repo=root)


class ImagesTests(unittest.TestCase):
    def test_a_classifier_and_an_original_beside_the_builds_load(self):
        images = [("plain", "Plain"), ("asan", "Asan"), ("plain_original", "PlainOriginal"),
                  ("classifier_a_asan", "ClassifierAAsan")]
        with TemporaryDirectory() as directory:
            unit = load_with_images(Path(directory), images)
        self.assertEqual(unit.image_modules, dict(images))
        self.assertEqual(unit.image("classifier_a_asan"), ("classifier_a_asan", "ClassifierAAsan"))

    def test_a_build_without_its_image_is_refused(self):
        with TemporaryDirectory() as directory:
            with self.assertRaisesRegex(ValueError, r"Images\.v: no image of harness\.yaml builds \['asan'\]"):
                load_with_images(Path(directory), [("plain", "Plain"), ("classifier_a_asan", "ClassifierAAsan")])

    def test_an_image_harness_yaml_does_not_list_is_refused(self):
        """An Images.v that still defines a build harness.yaml no longer lists, or an original or a classifier it does
        not list, is stale: oft generate would not write it."""
        for name, stray, harness in (("a build no longer listed", ("ubsan", "Ubsan"), HARNESS),
                                     ("an original not listed", ("plain_original", "PlainOriginal"), BUILDS),
                                     ("a classifier not listed", ("classifier_b_asan", "ClassifierBAsan"), HARNESS)):
            with self.subTest(name), TemporaryDirectory() as directory:
                with self.assertRaisesRegex(ValueError, r"Images\.v: images \['%s'\] are of no harness\.yaml build, "
                                                        r"original or classifier" % stray[0]):
                    load_with_images(Path(directory), [("plain", "Plain"), ("asan", "Asan"), stray], harness)


if __name__ == "__main__":
    unittest.main()
