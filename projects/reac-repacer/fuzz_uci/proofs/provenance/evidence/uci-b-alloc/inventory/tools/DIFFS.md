# Tool copies: sources and changes

Written by mkdiffs.py. Each copy below is the script these records ran. A changed copy's diff against its original has no context lines and is the whole change; a host path that a copy now reads from the environment defaults to empty.

| tool | copy sha256 | original sha256 | source | changed lines |
|---|---|---|---|---|
| `bytecmp-1480ca2faea0.py` | `0ac2ec8db277b17e34a4a0e35804270157525dbacbc6b0283f95134dbfe129de` | `1480ca2faea075e866800faab4e18aea5fb4a96dcea17ef1fe8981f1bdd0f98f` | tool registry commit 797e8971d27d, tools/bytecmp/1480ca2faea0/bytecmp.py (its lines 39-151 are insnflow a36c2b82eb44, tools/insnflow/a36c2b82eb44/insnflow.py at the same commit) | 11 removed, 11 added (195 lines in, 195 lines out) |
| `drvcmp.py` | `1b13206c79dd0721a7dfdefa2ab6cff9c2d5d2666920e46e449065ffaa56dd79` | `27f7a0e92bb9fdd59033bcdc5e7fcb349a20e97f7c02c43f3f5ffbb55347f89e` | commit 7af39d3f61c, proofs/reac-repacer/fuzz_uci/provenance/evidence/uci-b-memcpy/drvcmp.py (the drvcmp.py of the image-B donor survey scripts (repacer/B-DONORS.md) with bytecmp switched to 1480ca2faea0) | 8 removed, 8 added (70 lines in, 70 lines out) |
| `inventory.py` | `c4e5592ab63d5d584fce9e0e188faa1e6c384fa51b544481492b87cbc02cfc64` | - | written for these records: interceptor inventory | - |
| `mkdiffs.py` | `bd50962aa1a601d02cfa593e15dc9e45bb82686258d8e77a0f858327d33eef4d` | - | written for these records: the writer of this DIFFS.md | - |
| `repin_check-e5487165abb8.py` | `f268a01b33c56759fc3bef8a840116580ef1cb29eb4fb046f4ea3fd8d480bebc` | `e5487165abb8dfb7a39518a418fc24a0e815cea74918943bafbf35667c70ed11` | tool registry commit f69e6d74ebe, tools/repin_check/e5487165abb8/repin_check.py (supersedes 9cbc3553c09e: two different named targets are a difference) | 9 removed, 9 added (349 lines in, 349 lines out) |
| `scrub_out.py` | `4ee202522d7858dbffb751c5ce50d2c067a19d71359ec4dcd281de88bd71582e` | - | written for these records: the one writer of the committed slice | - |

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

- copy sha256 `1b13206c79dd0721a7dfdefa2ab6cff9c2d5d2666920e46e449065ffaa56dd79`
- original sha256 `27f7a0e92bb9fdd59033bcdc5e7fcb349a20e97f7c02c43f3f5ffbb55347f89e`: commit 7af39d3f61c, proofs/reac-repacer/fuzz_uci/provenance/evidence/uci-b-memcpy/drvcmp.py (the drvcmp.py of the image-B donor survey scripts (repacer/B-DONORS.md) with bytecmp switched to 1480ca2faea0)
- sha256 of the unredacted diff: `bc826d17df5d4afccdeb6161f9ed0c8dc2507027896c2e55b89489751895c9c2`

```diff
--- a/drvcmp.py
+++ b/drvcmp.py
@@ -4,2 +4,2 @@
-Reuses, verbatim and without running their mains:
-  - bytecmp.py 1480ca2faea0 (<redacted> 96d2c32e2879 tools/bytecmp/1480ca2faea0/bytecmp.py; was 7daa0e2a03d9 in <redacted>'s copy): load / words /
+Reuses, without running their mains (these copies differ only in comments and in host paths read from the environment):
+  - bytecmp.py 1480ca2faea0 (tool registry commit 797e8971d27d, tools/bytecmp/1480ca2faea0/bytecmp.py): load / words /
@@ -7,4 +7,4 @@
-  - repin_check.py 9cbc3553c09e (same commit, tools/repin_check/9cbc3553c09e/repin_check.py): class Img (lines 31-59)
-    and sx / targets / tcmp / w_off (lines 188-237), its target pass: every pc-relative target (jal, auipc+lo12 bound
-    by bytecmp's MUST dataflow) is resolved to symbol+offset on both images and compared; a target with no symbol is
-    compared by its bytes.
+  - repin_check.py e5487165abb8 (tool registry commit f69e6d74ebe, tools/repin_check/e5487165abb8/repin_check.py): class
+    Img (lines 31-59) and sx / targets / tcmp / w_off (lines 188-247), its target pass: every pc-relative target (jal, auipc+lo12 bound
+    by bytecmp's MUST dataflow) is resolved to symbol+offset on both images and compared; two different names, or a name
+    on one side only, are a difference; a target with no symbol on either side is compared by its bytes.
@@ -21 +21 @@
-_rc = open(os.path.join(HERE, 'repin_check-9cbc3553c09e.py')).read().split('\n')
+_rc = open(os.path.join(HERE, 'repin_check-e5487165abb8.py')).read().split('\n')
@@ -24 +24 @@
-exec('\n'.join(_rc[187:237]), _g)    # lines 188-237: sx, targets, tcmp, w_off
+exec('\n'.join(_rc[187:247]), _g)    # lines 188-247: sx, targets, tcmp, w_off
```

## repin_check-e5487165abb8.py

- copy sha256 `f268a01b33c56759fc3bef8a840116580ef1cb29eb4fb046f4ea3fd8d480bebc`
- original sha256 `e5487165abb8dfb7a39518a418fc24a0e815cea74918943bafbf35667c70ed11`: tool registry commit f69e6d74ebe, tools/repin_check/e5487165abb8/repin_check.py (supersedes 9cbc3553c09e: two different named targets are a difference)
- sha256 of the unredacted diff: `4ded988ecc5673e0d79b98ec5f274c5dc4860a9e72e6fa23c98a25a0e3fe91e9`

```diff
--- a/repin_check-e5487165abb8.py
+++ b/repin_check-e5487165abb8.py
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
@@ -234 +234 @@
-        # .bss or past the file bytes reads as None (<redacted>, 16:10Z: that used to raise); such a target is only
+        # .bss or past the file bytes reads as None (16:10Z: that used to raise); such a target is only
```
