"""oft fetch from a release that is not public (a draft), through the GitHub API (OFT_RELEASES_REPO), against
stand-in hosts on 127.0.0.1: one for the API and one for the storage host its asset URLs redirect to."""
import hashlib
import http.server
import io
import json
import os
import tempfile
import threading
import unittest
import urllib.request
from unittest import mock

from oft import facts, fetch
from oft.tests.helpers import tree
from oft.tests.test_fetch_check import HAVE_ZSTD, make_release


def run(fn, *args, **kw):
    out = io.StringIO()
    rc = fn(*args, out=out, **kw)
    return rc, out.getvalue()


class Host:
    """An HTTP host on 127.0.0.1 that answers each path in `routes` with (status, headers, body), and 404 for any
    other, and records each request as (path, Authorization header, Accept header)."""

    def __init__(self):
        self.routes, self.seen = {}, []
        host = self

        class Handler(http.server.BaseHTTPRequestHandler):
            def do_GET(self):
                host.seen.append((self.path, self.headers.get("Authorization"), self.headers.get("Accept")))
                status, headers, body = host.routes.get(self.path, (404, {}, b"not found"))
                self.send_response(status)
                for k, v in headers.items():
                    self.send_header(k, v)
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)

            def log_message(self, *args):
                pass

        self.server = http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        self.base = "http://127.0.0.1:%d" % self.server.server_port
        threading.Thread(target=self.server.serve_forever, daemon=True).start()

    def close(self):
        self.server.shutdown()
        self.server.server_close()


@unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
class Draft(unittest.TestCase):
    def setUp(self):
        self.api, self.storage = Host(), Host()
        self.addCleanup(self.api.close)
        self.addCleanup(self.storage.close)
        # a repository of its own for each test, since fetch lists a repository's releases once per process
        self.repo = "o/" + self.id().rsplit(".", 1)[1]
        self.listing = "/repos/%s/releases?per_page=100&page=1" % self.repo
        self.asset = "/repos/%s/releases/assets/7" % self.repo
        env = mock.patch.dict(os.environ, {"OFT_RELEASES_REPO": self.repo, "GH_TOKEN": "tok",
                                           "OFT_GITHUB_API": self.api.base})
        env.start()
        self.addCleanup(env.stop)
        # the public URL is a host of the test's own too, so that no test reaches GitHub whatever path fetch takes
        public = mock.patch.object(fetch, "RELEASES", self.storage.base + "/public")
        public.start()
        self.addCleanup(public.stop)

    def release(self, t, assets):
        """zlib's binaries packed as its release asset: (the tag project.yaml attaches it to, the archive's bytes, the
        binaries by member name)."""
        files = make_release(t, assets)
        with open(os.path.join(assets, "zlib-bin.tar.zst"), "rb") as f:
            data = f.read()
        return facts.load(t.root).projects["zlib"].data["assets"]["bin"]["release"], data, files

    def draft(self, tag, data, name="zlib-bin.tar.zst"):
        """The repository lists a published release and a draft `tag` holding `name`; the asset's API URL redirects
        to the storage host, which serves `data`."""
        listing = [{"tag_name": "v0.0.1", "draft": False, "assets": []},
                   {"tag_name": tag, "draft": True,
                    "assets": [{"name": name, "url": self.api.base + self.asset,
                                "digest": "sha256:" + hashlib.sha256(data).hexdigest()}]}]
        self.api.routes[self.listing] = (200, {"Content-Type": "application/json"}, json.dumps(listing).encode())
        self.api.routes[self.asset] = (302, {"Location": self.storage.base + "/blob/7"}, b"")
        self.storage.routes["/blob/7"] = (200, {}, data)

    def test_a_draft_asset_comes_through_the_api_with_the_same_checks(self):
        with tree() as t, tempfile.TemporaryDirectory() as a:
            tag, data, files = self.release(t, a)
            self.draft(tag, data)
            rc, out = run(fetch.fetch, t.root, ["zlib"])
            self.assertEqual(rc, 0, out)
            self.assertIn("8 binaries, each SHA-256 checked", out)
            for name, want in files.items():
                with open(t.path("projects/zlib/bin", name), "rb") as f:
                    self.assertEqual(f.read(), want)
            self.assertEqual(run(fetch.verify_sha, t.root, ["zlib"])[0], 0)
            # the asset was asked for as bytes, with the token, from the API host
            self.assertIn((self.asset, "Bearer tok", "application/octet-stream"), self.api.seen)

    def test_the_token_never_reaches_the_storage_host(self):
        """urllib sends a request's headers on to the host a redirect names; GitHub's asset redirect points at its
        storage host, which must not see the token."""
        with tree() as t, tempfile.TemporaryDirectory() as a:
            tag, data, _ = self.release(t, a)
            self.draft(tag, data)
            self.assertEqual(run(fetch.fetch, t.root, ["zlib"])[0], 0)
            self.assertEqual([p for p, _auth, _acc in self.storage.seen], ["/blob/7"])
            self.assertEqual([auth for _p, auth, _acc in self.storage.seen], [None])
            self.assertTrue(all(auth == "Bearer tok" for _p, auth, _acc in self.api.seen), self.api.seen)

    def test_a_draft_asset_that_is_not_the_pinned_one(self):
        with tree() as t, tempfile.TemporaryDirectory() as a:
            tag, data, _ = self.release(t, a)
            self.draft(tag, data + b"x")
            rc, out = run(fetch.fetch, t.root, ["zlib"])
            self.assertEqual(rc, 1)
            self.assertIn("project.yaml pins", out)
            self.assertEqual(os.listdir(t.path("projects/zlib/bin")), [])

    def test_a_tag_the_repository_has_no_release_of(self):
        with tree() as t, tempfile.TemporaryDirectory() as a:
            tag, data, _ = self.release(t, a)
            self.draft("v9.9.9", data)
            rc, out = run(fetch.fetch, t.root, ["zlib"])
            self.assertEqual(rc, 1)
            self.assertIn("%s has no release %s that this token can read" % (self.repo, tag), out)

    def test_a_release_without_the_asset(self):
        with tree() as t, tempfile.TemporaryDirectory() as a:
            tag, data, _ = self.release(t, a)
            self.draft(tag, data, name="other-bin.tar.zst")
            rc, out = run(fetch.fetch, t.root, ["zlib"])
            self.assertEqual(rc, 1)
            self.assertIn("%s's release %s has no asset zlib-bin.tar.zst" % (self.repo, tag), out)

    def test_no_token(self):
        with tree() as t, tempfile.TemporaryDirectory() as a:
            tag, data, _ = self.release(t, a)
            self.draft(tag, data)
            with mock.patch.dict(os.environ):
                os.environ.pop("GH_TOKEN", None)
                os.environ.pop("GITHUB_TOKEN", None)
                rc, out = run(fetch.fetch, t.root, ["zlib"])
            self.assertEqual(rc, 1)
            self.assertIn("OFT_RELEASES_REPO is set, and neither GH_TOKEN nor GITHUB_TOKEN is", out)
            self.assertEqual(self.api.seen, [])

    def test_one_listing_serves_a_whole_run(self):
        """The releases are listed once, however many assets the run takes (each listing is an API call)."""
        with tree() as t, tempfile.TemporaryDirectory() as a:
            tag, data, _ = self.release(t, a)
            self.draft(tag, data)
            for _ in range(3):
                self.assertEqual(run(fetch.fetch, t.root, ["zlib"])[0], 0)
            self.assertEqual([p for p, _auth, _acc in self.api.seen].count(self.listing), 1)
            self.assertEqual([p for p, _auth, _acc in self.api.seen].count(self.asset), 3)

    def test_the_source_option_wins_over_the_variable(self):
        with tree() as t, tempfile.TemporaryDirectory() as a:
            tag, data, _ = self.release(t, a)
            self.draft(tag, data)
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=a)
            self.assertEqual(rc, 0, out)
            self.assertEqual(self.api.seen, [])

    def test_a_release_on_the_second_page_of_the_listing(self):
        with tree() as t, tempfile.TemporaryDirectory() as a:
            tag, data, _ = self.release(t, a)
            self.draft(tag, data)
            second = "/repos/%s/releases?per_page=100&page=2" % self.repo
            self.api.routes[second] = self.api.routes[self.listing]
            first = [{"tag_name": "v0.%d" % i, "draft": False, "assets": []} for i in range(100)]
            self.api.routes[self.listing] = (200, {}, json.dumps(first).encode())
            rc, out = run(fetch.fetch, t.root, ["zlib"])
            self.assertEqual(rc, 0, out)
            self.assertEqual([p for p, _auth, _acc in self.api.seen if "/releases?" in p], [self.listing, second])

    def test_two_drafts_with_one_tag_take_the_pinned_copy(self):
        """Two drafts may carry one tag name; the copy whose recorded digest is the pinned SHA-256 is taken, whichever
        the listing names first."""
        with tree() as t, tempfile.TemporaryDirectory() as a:
            tag, data, _ = self.release(t, a)
            self.draft(tag, data)
            other = "/repos/%s/releases/assets/8" % self.repo
            stale = {"tag_name": tag, "draft": True,
                     "assets": [{"name": "zlib-bin.tar.zst", "url": self.api.base + other,
                                 "digest": "sha256:" + "f" * 64}]}
            listing = [stale] + json.loads(self.api.routes[self.listing][2])
            self.api.routes[self.listing] = (200, {}, json.dumps(listing).encode())
            self.api.routes[other] = (302, {"Location": self.storage.base + "/blob/8"}, b"")
            self.storage.routes["/blob/8"] = (200, {}, data + b"stale")
            rc, out = run(fetch.fetch, t.root, ["zlib"])
            self.assertEqual(rc, 0, out)
            self.assertEqual([p for p, _auth, _acc in self.storage.seen], ["/blob/7"])

    def test_an_api_answer_that_is_not_json(self):
        with tree() as t, tempfile.TemporaryDirectory() as a:
            tag, data, _ = self.release(t, a)
            self.draft(tag, data)
            self.api.routes[self.listing] = (200, {}, b"<html>sign in</html>")
            rc, out = run(fetch.fetch, t.root, ["zlib"])
            self.assertEqual(rc, 1)
            self.assertIn("the answer is not JSON", out)


class TokenStaysHome(unittest.TestCase):
    """The token follows a redirect only to the same scheme and host."""

    def follow(self, old, new):
        req = urllib.request.Request(old, headers={"Authorization": "Bearer tok"})
        return fetch._TokenStaysHome().redirect_request(req, None, 302, "Found", {}, new).get_header("Authorization")

    def test_the_token_follows_a_redirect_on_the_same_host_only(self):
        self.assertEqual(self.follow("https://api.example/a", "https://api.example/b"), "Bearer tok")
        self.assertIsNone(self.follow("https://api.example/a", "https://storage.example/b"))
        self.assertIsNone(self.follow("https://api.example/a", "http://api.example/b"))


@unittest.skipUnless(HAVE_ZSTD, "zstd is not installed")
class Public(unittest.TestCase):
    """Without OFT_RELEASES_REPO the download is the one it always was: the public release URL, with no token sent,
    a token in the environment or not."""

    def setUp(self):
        self.host = Host()
        self.addCleanup(self.host.close)
        env = mock.patch.dict(os.environ, {"GH_TOKEN": "tok"})
        env.start()
        self.addCleanup(env.stop)
        os.environ.pop("OFT_RELEASES_REPO", None)

    def test_the_url_is_the_public_release_url(self):
        asset = {"release": "v2026.10.2", "file": "zlib-bin.tar.zst", "bytes": 1, "sha256": "0" * 64}
        where = fetch._where(None, asset)
        self.assertEqual(where, fetch.RELEASES + "/v2026.10.2/zlib-bin.tar.zst")
        self.assertEqual(fetch._where("https://example.org/a/", asset), "https://example.org/a/zlib-bin.tar.zst")
        self.assertEqual(fetch._where("/some/dir", asset), "/some/dir/zlib-bin.tar.zst")

    def test_the_public_download_sends_no_token(self):
        public = mock.patch.object(fetch, "RELEASES", self.host.base + "/download")
        with tree() as t, tempfile.TemporaryDirectory() as a, public:
            make_release(t, a)
            tag = facts.load(t.root).projects["zlib"].data["assets"]["bin"]["release"]
            with open(os.path.join(a, "zlib-bin.tar.zst"), "rb") as f:
                self.host.routes["/download/%s/zlib-bin.tar.zst" % tag] = (200, {}, f.read())
            rc, out = run(fetch.fetch, t.root, ["zlib"])
            self.assertEqual(rc, 0, out)
            self.assertEqual([auth for _p, auth, _acc in self.host.seen], [None])

    def test_a_public_404_names_the_ways_out(self):
        public = mock.patch.object(fetch, "RELEASES", self.host.base + "/download")
        with tree() as t, tempfile.TemporaryDirectory() as a, public:
            make_release(t, a)
            rc, out = run(fetch.fetch, t.root, ["zlib"])
            self.assertEqual(rc, 1)
            self.assertIn("HTTP 404, no public release holds it", out)
            self.assertIn("set OFT_RELEASES_REPO=<owner>/<repo> and GH_TOKEN", out)
            self.assertIn("or pass --source DIR", out)

    def test_another_failure_of_the_public_url_is_not_explained_as_a_draft(self):
        public = mock.patch.object(fetch, "RELEASES", self.host.base + "/download")
        with tree() as t, tempfile.TemporaryDirectory() as a, public:
            make_release(t, a)
            tag = facts.load(t.root).projects["zlib"].data["assets"]["bin"]["release"]
            self.host.routes["/download/%s/zlib-bin.tar.zst" % tag] = (500, {}, b"down")
            rc, out = run(fetch.fetch, t.root, ["zlib"])
            self.assertEqual(rc, 1)
            self.assertIn("HTTP Error 500", out)
            self.assertNotIn("no public release holds it", out)

    def test_a_404_from_a_source_url_is_not_explained_as_a_draft(self):
        with tree() as t, tempfile.TemporaryDirectory() as a:
            make_release(t, a)
            rc, out = run(fetch.fetch, t.root, ["zlib"], source=self.host.base + "/mirror/")
            self.assertEqual(rc, 1)
            self.assertIn("HTTP Error 404", out)
            self.assertNotIn("OFT_RELEASES_REPO", out)


if __name__ == "__main__":
    unittest.main()
