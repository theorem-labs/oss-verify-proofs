"""lint rule `records` (with --release): every fuzz target with a proof has a complete build record, and the record
says what the facts say of the binaries it describes, the archives they ship in and what built them."""
import hashlib
import io
import os
import unittest

from oft import facts, layout, port
from oft.tests.helpers import Public, Tree, add_build_record
from oft.tests.test_oss_verify import PORT, PORT_ASSET, add_standin

UNIT = "zlib/checksum_fuzzer"
RECORD = "proofs/zlib/checksum_fuzzer/provenance/PROVENANCE.yaml"
JSON_RECORD = "proofs/json/fuzzer-parse_bjdata/provenance/PROVENANCE.yaml"


def add_proof(t, sid):
    st = next(s for s in facts.load(t.root).statements() if s.id == sid)
    t.put_yaml("proofs/%s/proof.yaml" % sid, {
        "schema": "oss-fuzz-theorems/proof/1", "proves": sid, "fingerprint": st.fingerprint})
    t.write("proofs/%s/Proof.v" % sid, "Theorem holds : True. Proof. exact I. Qed.\n")


class Records(unittest.TestCase):
    def setUp(self):
        self.t = Tree()
        self.addCleanup(self.t.close)
        add_proof(self.t, UNIT + "/plain_halts")
        add_build_record(self.t)
        self.assertEqual(self.t.generate(), 0, self.t.last_output)

    def edit(self, rel=RECORD, **change):
        """Apply change to the record at rel: each key is a dotted path, each value its new value (None removes it)."""
        r = self.t.yaml(rel)
        for path, value in change.items():
            *parents, last = path.split(".")
            at = r
            for p in parents:
                at = at[int(p)] if isinstance(at, list) else at[p]
            if value is None:
                del at[int(last) if isinstance(at, list) else last]
            elif isinstance(at, list):
                at[int(last)] = value
            else:
                at[last] = value
        self.t.put_yaml(rel, r)

    def records(self, **kw):
        return [str(f) for f in self.t.lint(release=True, **kw) if f.rule == "records"]

    def assertFound(self, text, where=RECORD):
        found = self.records()
        self.assertTrue(any(f.startswith("records %s: " % where) and text in f for f in found), found)

    def test_a_complete_record_passes_every_rule(self):
        self.assertEqual([str(f) for f in self.t.lint(release=True)], [])

    def test_only_a_release_is_held_to_the_records(self):
        os.remove(self.t.path(RECORD))
        self.assertEqual([str(f) for f in self.t.lint()], [])
        self.assertEqual(self.records(), [
            "records %s: no build record: every fuzz target with a proof has one, which says what built its "
            "binaries" % RECORD])

    def test_an_unfinished_value(self):
        r = self.t.yaml(RECORD)
        r["upstream"]["licence_evidence"] = "TODO: read LICENSE"
        r["toolchain"]["static_asan"]["checked"] = {"pending": True}
        r["upstream"]["licence_in_release_records"] = "pending"
        self.t.put_yaml(RECORD, r)
        self.assertEqual(self.records(), [
            "records %s: unfinished values, which a published record never has (pending, NOASSERTION or TODO): "
            ".upstream.licence_evidence: TODO: read LICENSE; .toolchain.static_asan.checked.pending: true" % RECORD])

    def test_binaries_that_are_not_the_published_builds(self):
        self.edit(**{"binaries.1.sha256": "0" * 64})
        self.assertFound("binaries differ from the published builds of projects/zlib/checksum_fuzzer/harness.yaml "
                         "(each build's sha256 and bytes): ubsan")
        self.edit(**{"binaries.1": None})
        self.assertFound("3 binaries, not 4: a record has one of each build")
        self.edit(**{"binaries.0.build": "asan-ubsan"})
        self.assertFound("binaries names the build asan-ubsan more than once")

    def test_a_harness_with_fewer_published_builds(self):
        h = "projects/zlib/checksum_fuzzer/harness.yaml"
        y = self.t.yaml(h)
        y["builds"]["asan"] = {"file": "checksum_fuzzer.asan", "withheld": "not-yet-published"}
        self.t.put_yaml(h, y)
        self.assertFound("projects/zlib/checksum_fuzzer/harness.yaml publishes 3 builds, not 4")

    def test_a_builder_image_that_is_not_the_releases(self):
        self.edit(**{"toolchain.builder_image": "ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:" + "4" * 64})
        self.assertFound("toolchain.builder_image is not release.yaml's images.builder[0]")

    def test_records_name_one_static_asan_commit(self):
        """A build record without a proof (json's) is held to the rule too."""
        add_build_record(self.t, "json/fuzzer-parse_bjdata")
        self.assertEqual(self.records(), [])
        self.edit(JSON_RECORD, **{"toolchain.static_asan.commit": "c1" * 20})
        found = self.records()
        self.assertEqual(len(found), 2, found)
        for rel in (RECORD, JSON_RECORD):
            self.assertTrue(any(f.startswith("records %s: toolchain.static_asan.commit is " % rel) and
                                "every build record names the one static-asan commit" in f for f in found), found)
        self.edit(JSON_RECORD, **{"toolchain.static_asan.commit": None})
        self.assertFound("toolchain.static_asan.commit is None, not a full commit id", JSON_RECORD)

    def test_a_binary_archive_that_is_not_the_projects(self):
        self.edit(**{"binary_asset.sha256": "0" * 64})
        self.assertFound("binary_asset is not projects/zlib/project.yaml's assets.bin")
        self.edit(**{"binary_asset.bytes": "18000000"})
        self.assertFound("binary_asset.bytes: expected an integer")

    def test_source_archives_that_are_not_the_projects(self):
        self.edit(**{"source_asset.src_manifest": None})
        self.assertFound("source_asset is not projects/zlib/project.yaml's assets.src and assets.src_manifest: "
                         "the record has no source_asset.src_manifest, and project.yaml has assets.src_manifest")

    def test_a_record_names_its_archives_by_file_bytes_and_sha256_and_no_release(self):
        """Contract C1: project.yaml's assets are the one place that names an archive's release, so the fixture's
        record, which names none, passes (test_a_complete_record_passes_every_rule).  A record written before C1
        names a release too: it passes when that release is project.yaml's, and is refused when it is another."""
        r = self.t.yaml(RECORD)
        self.assertEqual([k for a in (r["binary_asset"], *r["source_asset"].values()) for k in a if k == "release"], [])
        self.edit(**{"binary_asset.release": "v2026.11.0", "source_asset.src.release": "v2026.11.0",
                     "source_asset.src_manifest.release": "v2026.11.0"})
        self.assertEqual(self.records(), [])
        self.edit(**{"binary_asset.release": "v2026.10.0"})
        self.assertFound("binary_asset is not projects/zlib/project.yaml's assets.bin")
        self.edit(**{"binary_asset.release": None, "source_asset.src.release": "v2026.10.0"})
        self.assertFound("source_asset is not projects/zlib/project.yaml's assets.src and assets.src_manifest")

    def test_licence_texts_are_exactly_the_components(self):
        lic = "proofs/zlib/checksum_fuzzer/provenance/LICENSES/"
        self.t.write(lic + "extra-LICENSE", "another text\n")
        self.assertFound("LICENSES/ is not the texts licence.components names: not named LICENSES/extra-LICENSE")
        os.remove(self.t.path(lic + "extra-LICENSE"))
        os.remove(self.t.path(lic + "musl-COPYRIGHT"))
        self.assertFound("LICENSES/ is not the texts licence.components names: missing LICENSES/musl-COPYRIGHT")
        self.edit(**{"licence.components": []})
        self.assertFound("LICENSES/ is not the texts licence.components names")

    def test_an_upstream_licence_nobody_confirmed(self):
        self.edit(**{"upstream.licence": None})
        self.assertFound("upstream.licence is None: the record names the upstream licence")

    SRC = {"file": "zlib-src.tar.zst", "sha256": "5b" * 32}
    MANIFEST = {"file": "zlib-src.MANIFEST.tsv", "sha256": "5c" * 32}
    RECIPE = {"file": "recipe.tar.zst", "sha256": "5d" * 32}
    TOOLCHAIN = {"file": "toolchain-src.tar.zst", "sha256": "1" * 64}

    def test_a_copyleft_component_cites_its_source_as_the_facts_pin_it(self):
        """licence.source_bundle is Contract C1's list: each file by name and the SHA-256 that project.yaml's assets
        or release.yaml's recipes and sources pin it with, the project's source archive among them."""
        self.edit(**{"licence.components.0.licence": "GPL-2.0-or-later"})
        self.assertFound("a GPL- or LGPL-licensed component, and licence.source_bundle is 'not required by the "
                         "licences; ")
        self.edit(**{"licence.source_bundle": [self.SRC, self.MANIFEST, self.RECIPE]})
        self.assertEqual(self.records(), [])
        self.edit(**{"licence.source_bundle": [self.MANIFEST, self.RECIPE]})
        self.assertEqual(self.records(), ["records %s: licence.source_bundle does not cite zlib-src.tar.zst, the "
                                          "project's source archive" % RECORD])
        self.edit(**{"licence.source_bundle": [dict(self.SRC, sha256="0" * 64), self.MANIFEST]})
        self.assertEqual(self.records(), [
            "records %s: licence.source_bundle cites zlib-src.tar.zst (sha256 %s), which neither "
            "projects/zlib/project.yaml's assets nor release.yaml's recipes and sources pin with that sha256"
            % (RECORD, "0" * 64)])
        self.edit(**{"licence.source_bundle": [self.SRC, self.MANIFEST, self.TOOLCHAIN]})
        self.assertEqual(self.records(), [
            "records %s: licence.source_bundle cites toolchain-src.tar.zst (sha256 %s), which neither "
            "projects/zlib/project.yaml's assets nor release.yaml's recipes and sources pin with that sha256"
            % (RECORD, "1" * 64)])
        r = self.t.yaml("release.yaml")
        r["sources"] = {"release": "sources-v1",
                        "toolchain": {"file": "toolchain-src.tar.zst", "bytes": 1, "sha256": "1" * 64},
                        "sysroot": {"file": "sysroot-src.tar.zst", "bytes": 1, "sha256": "2" * 64}}
        self.t.put_yaml("release.yaml", r)
        self.assertEqual(self.records(), [])

    def test_a_source_bundle_that_is_not_contract_c1_s_list(self):
        self.edit(**{"licence.components.0.licence": "LGPL-2.1-only"})
        text = "https://github.com/theorem-labs/oss-verify-proofs/releases/tag/v2026.11.0: `zlib-src.tar.zst`"
        for name, bundle in (("the text before C1", text), ("an empty list", []),
                             ("an entry that names a release", [dict(self.SRC, release="v2026.11.0")]),
                             ("a sha256 that is not 64 hex digits", [dict(self.SRC, sha256="5b")])):
            with self.subTest(bundle=name):
                self.edit(**{"licence.source_bundle": bundle})
                found = self.records()
                self.assertEqual(len(found), 1, found)
                self.assertIn("licence.source_bundle is %.80r, not a list of {file, sha256} entries (Contract C1"
                              % (bundle,), found[0])
        self.edit(**{"licence.source_bundle": [self.SRC, self.MANIFEST, self.SRC]})
        self.assertEqual(self.records(), ["records %s: licence.source_bundle cites zlib-src.tar.zst more than once"
                                          % RECORD])

    def test_a_patch_that_is_not_build_glue(self):
        self.edit(**{"recipe.patches.0.class": "Security fix."})
        self.assertFound("recipe.patches are not all build glue: 0001-build.patch (Security fix.)")

    def test_overlay_files_are_the_manifests(self):
        recipe = "proofs/zlib/checksum_fuzzer/provenance/recipe/"
        body = b"#!/bin/sh\nmake\n"
        self.t.write(recipe + "targets/checksum_fuzzer/build.sh", body, "wb")
        self.t.write(recipe + "MANIFEST.tsv", "path\tsha256\tkind\ntargets/checksum_fuzzer/build.sh\t%s\tours\n"
                     % hashlib.sha256(body).hexdigest())
        self.edit(**{"recipe.overlay": ["targets/checksum_fuzzer/build.sh"]})
        self.assertEqual(self.records(), [])
        self.t.write(recipe + "targets/checksum_fuzzer/build.sh", "#!/bin/sh\nmake all\n")
        self.assertFound("recipe.overlay files missing, or not of the sha256 recipe/MANIFEST.tsv gives: "
                         "targets/checksum_fuzzer/build.sh")
        self.edit(**{"recipe.overlay": ["../PROVENANCE.md"]})
        self.assertFound("recipe.overlay files missing, or not of the sha256 recipe/MANIFEST.tsv gives: "
                         "../PROVENANCE.md")

    FALLBACK = {"reason": "the rc.2 port of this proof did not pass the release check",
                "recipe_commit": "e" * 40,
                "builder_image": "ghcr.io/theorem-labs/oss-fuzz-theorems-toolchain@sha256:" + "5" * 64,
                "static_asan": {"internal_commit": "f" * 40, "public_commit": "d0" * 20},
                "rebuild": {"by": "a maintainer", "verdict": "identical x4", "evidence": "four sha256s matched"}}

    def test_a_fallback_record(self):
        self.edit(**{"fallback": dict(self.FALLBACK)})
        self.assertEqual(self.records(), [])
        self.edit(**{"fallback.recipe_commit": "e" * 12, "fallback.rebuild.verdict": "identical x3",
                     "fallback.static_asan.public_commit": None})
        found = self.records()
        for text in ("fallback: a reason, the recipe commit, and the builder image (and toolchain image, if given) "
                     "by digest", "fallback.static_asan.public_commit is None, not a full commit id",
                     "fallback: the rebuild gave identical x4, with its evidence"):
            self.assertTrue(any(text in f for f in found), (text, found))


class PerProjectRecords(unittest.TestCase):
    """A tree in the per-project layout is held to the same records: each record is read in its fuzz target's proofs
    folder, projects/<p>/<h>/proofs/provenance/ (layout.py), and each finding names it there."""
    NEW = layout.record_path("zlib", "checksum_fuzzer", layout.NEW)

    def setUp(self):
        self.t = Tree()
        self.addCleanup(self.t.close)
        add_proof(self.t, UNIT + "/plain_halts")
        add_build_record(self.t)
        self.assertEqual(port.port_worktree(self.t.root, out=io.StringIO()), 0)
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        self.assertTrue(os.path.isfile(self.t.path(self.NEW)))

    def records(self):
        return [str(f) for f in self.t.lint(release=True) if f.rule == "records"]

    def test_a_complete_record_passes_and_an_incomplete_one_is_named_where_it_is(self):
        self.assertEqual([str(f) for f in self.t.lint(release=True)], [])
        r = self.t.yaml(self.NEW)
        r["upstream"]["licence"] = None
        self.t.put_yaml(self.NEW, r)
        self.assertEqual(self.records(), ["records %s: upstream.licence is None: the record names the upstream "
                                          "licence" % self.NEW])

    def test_its_licence_texts_are_read_beside_it(self):
        self.t.write(os.path.dirname(self.NEW) + "/LICENSES/extra-LICENSE", "another text\n")
        self.assertEqual(self.records(), ["records %s: LICENSES/ is not the texts licence.components names: not named "
                                          "LICENSES/extra-LICENSE" % self.NEW])

    def test_a_fuzz_target_with_a_proof_and_no_record(self):
        os.remove(self.t.path(self.NEW))
        self.assertEqual(self.records(), ["records %s: no build record: every fuzz target with a proof has one, which "
                                          "says what built its binaries" % self.NEW])



class PortRecords(unittest.TestCase):
    """A port-built project's record names the port and its archive that the project's facts name."""
    UNIT = "standin/standin_eval_fuzzer"
    REL = "proofs/standin/standin_eval_fuzzer/provenance/PROVENANCE.yaml"

    def setUp(self):
        self.t = Tree()
        self.addCleanup(self.t.close)
        add_standin(self.t)
        self.assertEqual(self.t.generate(), 0, self.t.last_output)
        add_proof(self.t, self.UNIT + "/plain_halts")
        add_build_record(self.t, self.UNIT)
        r = self.t.yaml(self.REL)
        del r["recipe"]
        r["port"] = dict(PORT, asset={k: PORT_ASSET[k] for k in ("file", "bytes", "sha256")})   # Contract C1
        self.t.put_yaml(self.REL, r)
        self.assertEqual(self.t.generate(), 0, self.t.last_output)

    def port_findings(self):
        return [str(f) for f in self.t.lint(release=True, public=Public())
                if f.rule == "records" and "port" in f.msg]

    def test_the_port_and_its_archive_are_the_projects(self):
        self.assertEqual(self.port_findings(), [])
        r = self.t.yaml(self.REL)
        r["port"]["commit"] = "c" * 40
        r["port"]["asset"]["sha256"] = "8" * 64
        self.t.put_yaml(self.REL, r)
        self.assertEqual(self.port_findings(), [
            "records %s: port is not projects/standin/project.yaml's build.oss_verify" % self.REL,
            "records %s: port.asset is not projects/standin/project.yaml's assets.port" % self.REL])

    def test_a_record_of_an_earlier_port_build_is_refused(self):
        """A later build of some of the project's fuzz targets moves build.oss_verify and replaces the project's
        archives: a record of the earlier build (libdiginet's fuzz_codec, fuzz_decode and fuzz_frame on 2026-11-03)
        names a port commit, archives and a source bundle the facts no longer pin, and each is a finding."""
        y = self.t.yaml("projects/standin/project.yaml")
        a = y["assets"]
        r = self.t.yaml(self.REL)
        r["licence"]["components"][0]["licence"] = "GPL-3.0-or-later"
        r["licence"]["source_bundle"] = [{"file": a[k]["file"], "sha256": a[k]["sha256"]}
                                         for k in ("src", "src_manifest", "port")]
        self.t.put_yaml(self.REL, r)
        # the stand-in publishes one build of four: those findings are the same before and after
        before = [str(f) for f in self.t.lint(release=True, public=Public()) if f.rule == "records"]
        self.assertEqual([f for f in before if "asset" in f or "port" in f or "source_bundle" in f], [])
        y["build"]["oss_verify"]["commit"] = "e" * 40
        a["bin"]["sha256"], a["port"]["sha256"] = "6" * 64, "7" * 64
        self.t.put_yaml("projects/standin/project.yaml", y)
        new = [str(f) for f in self.t.lint(release=True, public=Public())
               if f.rule == "records" and str(f) not in before]
        self.assertEqual(new, ["records %s: %s" % (self.REL, text) for text in (
            "port is not projects/standin/project.yaml's build.oss_verify",
            "port.asset is not projects/standin/project.yaml's assets.port",
            "binary_asset is not projects/standin/project.yaml's assets.bin",
            "licence.source_bundle cites standin-port.tar.zst (sha256 %s), which neither "
            "projects/standin/project.yaml's assets nor release.yaml's recipes and sources pin with that sha256"
            % ("9" * 64))])

    def test_a_record_names_a_port_or_a_recipe_not_both(self):
        r = self.t.yaml(self.REL)
        r["recipe"] = {"asset": {"release": "v2026.11.0", "file": "recipe.tar.zst", "bytes": 2000000,
                                 "sha256": "5d" * 32}}
        self.t.put_yaml(self.REL, r)
        self.assertIn("records %s: the record names a port and a recipe: a port built the binaries, or a recipe did"
                      % self.REL, self.port_findings())

    def test_a_port_built_binary_archive_names_its_port_archive(self):
        y = self.t.yaml("projects/standin/project.yaml")
        for k in ("src", "src_manifest", "port"):
            del y["assets"][k]
        y["library"]["licence"] = "MIT"
        self.t.put_yaml("projects/standin/project.yaml", y)
        found = [str(f) for f in self.t.lint(release=True) if f.rule == "records"]
        self.assertIn("records projects/standin/project.yaml: a port-built project's binary archive goes with its "
                      "port archive, and assets.port is missing", found)


if __name__ == "__main__":
    unittest.main()
