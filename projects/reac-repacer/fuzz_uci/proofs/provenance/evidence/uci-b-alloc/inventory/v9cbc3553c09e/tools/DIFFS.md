# Tool copies: sources and changes

Written by mkdiffs.py. Each copy below is the script these records ran. A changed copy's diff against its original has no context lines and is the whole change; a host path that a copy now reads from the environment defaults to empty.

| tool | copy sha256 | original sha256 | source | changed lines |
|---|---|---|---|---|
| `bytecmp-1480ca2faea0.py` | `0ac2ec8db277b17e34a4a0e35804270157525dbacbc6b0283f95134dbfe129de` | `1480ca2faea075e866800faab4e18aea5fb4a96dcea17ef1fe8981f1bdd0f98f` | tool registry commit 797e8971d27d, tools/bytecmp/1480ca2faea0/bytecmp.py (its lines 39-151 are insnflow a36c2b82eb44, tools/insnflow/a36c2b82eb44/insnflow.py at the same commit) | 11 removed, 11 added (195 lines in, 195 lines out) |
| `drvcmp.py` | `a4c8056e896a102b67e1c872ae0b0da02ac08c4387e02dd939594202d735e2d8` | `27f7a0e92bb9fdd59033bcdc5e7fcb349a20e97f7c02c43f3f5ffbb55347f89e` | commit 7af39d3f61c, proofs/reac-repacer/fuzz_uci/provenance/evidence/uci-b-memcpy/drvcmp.py (the drvcmp.py of the image-B donor survey scripts (repacer/B-DONORS.md) with bytecmp switched to 1480ca2faea0) | 2 removed, 2 added (70 lines in, 70 lines out) |
| `inventory.py` | `c4e5592ab63d5d584fce9e0e188faa1e6c384fa51b544481492b87cbc02cfc64` | - | written for these records: interceptor inventory | - |
| `repin_check-9cbc3553c09e.py` | `15045c02875c3e5ba73c22c6a227559ad447e011b7fb0152679621a543cd3700` | `9cbc3553c09e71a3687353b0b6995081f8b42660b6b12ecd279757449c6d6e1a` | tool registry commit 797e8971d27d, tools/repin_check/9cbc3553c09e/repin_check.py (superseded by e5487165abb8) | 9 removed, 9 added (339 lines in, 339 lines out) |

## bytecmp-1480ca2faea0.py

- copy sha256 `0ac2ec8db277b17e34a4a0e35804270157525dbacbc6b0283f95134dbfe129de`
- original sha256 `1480ca2faea075e866800faab4e18aea5fb4a96dcea17ef1fe8981f1bdd0f98f`: tool registry commit 797e8971d27d, tools/bytecmp/1480ca2faea0/bytecmp.py (its lines 39-151 are insnflow a36c2b82eb44, tools/insnflow/a36c2b82eb44/insnflow.py at the same commit)
- sha256 of the unredacted diff: `f1e81d36c95e547346054f743cb1455b09bfa5c6ec8a2404cdfff1affc99b0ed`

```diff
--- a/bytecmp-1480ca2faea0.py
+++ b/bytecmp-1480ca2faea0.py
@@ -13 +13 @@
-import sys, hashlib
+import sys, hashlib, os
@@ -39,2 +39,2 @@
-# ---- insnflow block begin (owner <redacted>). The same bytes as <redacted> (record: <redacted>
-# tools/insnflow/). symreloc.py and elfdis.py CARRY this block instead of importing it, so that a tool's sha fixes its
+# ---- insnflow block begin. The same bytes as insnflow a36c2b82eb44 (tools/insnflow/a36c2b82eb44/insnflow.py, tool
+# registry commit 797e8971d27d) apart from comments. symreloc.py and elfdis.py CARRY this block instead of importing it, so that a tool's sha fixes its
@@ -76,4 +76,4 @@
-    A linear scan is wrong in both directions, as two lanes measured on 2026-10-29: it pairs an auipc with a word that is a
-    jump-table case entered from elsewhere (<redacted>, printf_core+0x890: a false differing reference), and it drops a
-    binding that a branch target does have, because the FALL-THROUGH path overwrote the register (<redacted> /
-    <redacted>, HaveStackTraceBasedSuppressions+0x3c: a false DIFFERENT). So this is a forward MUST analysis over the
+    A linear scan is wrong in both directions, as two measurements on 2026-10-29 showed: it pairs an auipc with a word that is a
+    jump-table case entered from elsewhere (printf_core+0x890: a false differing reference), and it drops a
+    binding that a branch target does have, because the FALL-THROUGH path overwrote the register
+    (HaveStackTraceBasedSuppressions+0x3c: a false DIFFERENT). So this is a forward MUST analysis over the
@@ -132 +132 @@
-                # so the WRITES_RD pop above kills nothing: a binding kept across an ecall was accepted (<redacted>, 16:35Z).
+                # so the WRITES_RD pop above kills nothing: a binding kept across an ecall was accepted (16:35Z).
@@ -163 +163 @@
-                # width or operation is a real difference (<redacted>, 16:15Z: `ld a2,0x18c(a2)` -> `lw a2,...`, lbu -> lb,
+                # width or operation is a real difference (16:15Z: `ld a2,0x18c(a2)` -> `lw a2,...`, lbu -> lb,
@@ -182,2 +182,2 @@
-base = {'A': '<redacted>',
-        'B': '<redacted>'}
+base = {'A': os.environ.get('BYTECMP_BASE_A', ''),  # unstripped fuzz_preset.asan of omx-clap-core
+        'B': os.environ.get('BYTECMP_BASE_B', '')}  # unstripped fuzz_preset.asan-ubsan of omx-clap-core
```

## drvcmp.py

- copy sha256 `a4c8056e896a102b67e1c872ae0b0da02ac08c4387e02dd939594202d735e2d8`
- original sha256 `27f7a0e92bb9fdd59033bcdc5e7fcb349a20e97f7c02c43f3f5ffbb55347f89e`: commit 7af39d3f61c, proofs/reac-repacer/fuzz_uci/provenance/evidence/uci-b-memcpy/drvcmp.py (the drvcmp.py of the image-B donor survey scripts (repacer/B-DONORS.md) with bytecmp switched to 1480ca2faea0)
- sha256 of the unredacted diff: `2aea8ead56bff0ecc685654c8192e3baf32db8e14cd70b61a5b42f43b701fef7`

```diff
--- a/drvcmp.py
+++ b/drvcmp.py
@@ -4,2 +4,2 @@
-Reuses, verbatim and without running their mains:
-  - bytecmp.py 1480ca2faea0 (<redacted> 96d2c32e2879 tools/bytecmp/1480ca2faea0/bytecmp.py; was 7daa0e2a03d9 in <redacted>'s copy): load / words /
+Reuses, without running their mains (these copies differ only in comments and in host paths read from the environment):
+  - bytecmp.py 1480ca2faea0 (tool registry commit 797e8971d27d, tools/bytecmp/1480ca2faea0/bytecmp.py): load / words /
```

## repin_check-9cbc3553c09e.py

- copy sha256 `15045c02875c3e5ba73c22c6a227559ad447e011b7fb0152679621a543cd3700`
- original sha256 `9cbc3553c09e71a3687353b0b6995081f8b42660b6b12ecd279757449c6d6e1a`: tool registry commit 797e8971d27d, tools/repin_check/9cbc3553c09e/repin_check.py (superseded by e5487165abb8)
- sha256 of the unredacted diff: `49d5ef8b583334a1095457b74f6d7cbad08e2b426b016994a844107716b3e4af`

```diff
--- a/repin_check-9cbc3553c09e.py
+++ b/repin_check-9cbc3553c09e.py
@@ -2,2 +2,2 @@
-"""repin_check.py -- independent check of <redacted>'s PSnp* restatement/re-pin (<redacted>
-17a8581f30c) against <redacted> (<redacted> 7e395de08f5).  Read-only.
+"""repin_check.py -- independent check of a PSnp* restatement/re-pin (commit 17a8581f30c) against the fm restatement
+(commit 7e395de08f5).  Read-only.
@@ -16,6 +16,6 @@
-IMG = {'A': '<redacted>',
-       'B': '<redacted>',
-       'F': '<redacted>'}
-PIN = {'A': ('<redacted>', 'd83eb25d', 'f0d2e8d40c7e3ed0'),
-       'B': ('<redacted>', 'f8f98a95', '3b5e1a099b535acf'),
-       'F': ('<redacted>', '0ba7e169', 'fc92e86bee065b5d')}
+IMG = {'A': os.environ.get('REPIN_IMG_A', ''),  # unstripped omx-clap-core fuzz_preset.asan
+       'B': os.environ.get('REPIN_IMG_B', ''),  # unstripped omx-clap-core fuzz_preset.asan-ubsan
+       'F': os.environ.get('REPIN_IMG_F', '')}  # unstripped omx-clap-core fuzz_manifest.asan
+PIN = {'A': (os.environ.get('REPIN_PIN_A', ''), 'd83eb25d', 'f0d2e8d40c7e3ed0'),  # pinned fuzz_preset.asan
+       'B': (os.environ.get('REPIN_PIN_B', ''), 'f8f98a95', '3b5e1a099b535acf'),  # pinned fuzz_preset.asan-ubsan
+       'F': (os.environ.get('REPIN_PIN_F', ''), '0ba7e169', 'fc92e86bee065b5d')}  # pinned fuzz_manifest.asan
@@ -224 +224 @@
-        # .bss or past the file bytes reads as None (<redacted>, 16:10Z: that used to raise); such a target is only
+        # .bss or past the file bytes reads as None (16:10Z: that used to raise); such a target is only
```
