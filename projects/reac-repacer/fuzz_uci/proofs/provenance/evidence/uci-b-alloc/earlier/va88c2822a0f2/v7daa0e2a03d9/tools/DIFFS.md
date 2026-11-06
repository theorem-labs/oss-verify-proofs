# Tool copies: sources and changes

Written by mkdiffs.py. Each copy below is the script these records ran. A changed copy's diff against its original has no context lines and is the whole change; a host path that a copy now reads from the environment defaults to empty.

| tool | copy sha256 | original sha256 | source | changed lines |
|---|---|---|---|---|
| `bytecmp-7daa0e2a03d9.py` | `d8c4befbf6953ed5c4870ceb64e716095cc5b223d9b02f04b0f8c178ed702820` | `7daa0e2a03d904b973bab1bbb68e57e0e32113d3620950132e296b7a6cc06e24` | tool registry commit 797e8971d27d, tools/bytecmp/7daa0e2a03d9/bytecmp.py | 9 removed, 9 added (152 lines in, 152 lines out) |
| `cietable.py` | `c82414f4b6d78d45d1fc214f8634985143635cdc03e512a7b4f7bee102eaa845` | - | written for these records: reads parseCIE's jump table | - |
| `closure.py` | `b50998fb3bd3db5ec374b380157492a819044f992c3fd895d3cb2f2764578f77` | `b50998fb3bd3db5ec374b380157492a819044f992c3fd895d3cb2f2764578f77` | image-B donor survey scripts (repacer/B-DONORS.md): closure.py (the same bytes as commit 7af39d3f61c, proofs/reac-repacer/fuzz_uci/provenance/evidence/uci-b-memcpy/closure.py) | unchanged |
| `drvcmp.py` | `4c3feca0363dcd23a454f19960ac467eb88eb91852afcfea840ca9d34ddea95e` | `fbbdb144ddfc1bbb743ec508071e3396b1f2794528b774d7fbc86d2a1dd366d0` | image-B donor survey scripts (repacer/B-DONORS.md): drvcmp.py (loads bytecmp 7daa0e2a03d9) | 2 removed, 2 added (70 lines in, 70 lines out) |
| `jtcheck.py` | `2e2f9c2126b21aa300f44228af1af74298db3c6e196da97b0038c12a3acfebce` | `2e2f9c2126b21aa300f44228af1af74298db3c6e196da97b0038c12a3acfebce` | image-B donor survey scripts (repacer/B-DONORS.md): jtcheck.py | unchanged |
| `paircl.py` | `16e1466be22de053d502d781cae2454b6dd862138a92c0a8c8eaa3b7638de9e4` | `16e1466be22de053d502d781cae2454b6dd862138a92c0a8c8eaa3b7638de9e4` | image-B donor survey scripts (repacer/B-DONORS.md): paircl.py (superseded by a88c2822a0f2) | unchanged |
| `pairtable.py` | `c3f983a0289cbbf58e9c5af1858d72bde33c214f9800dd2a886ba7c7c8ae557a` | - | written for these records: runs paircl.py via runpy; one TSV row per pair | - |
| `repin_check-9cbc3553c09e.py` | `15045c02875c3e5ba73c22c6a227559ad447e011b7fb0152679621a543cd3700` | `9cbc3553c09e71a3687353b0b6995081f8b42660b6b12ecd279757449c6d6e1a` | tool registry commit 797e8971d27d, tools/repin_check/9cbc3553c09e/repin_check.py (superseded by e5487165abb8) | 9 removed, 9 added (339 lines in, 339 lines out) |
| `syms.py` | `ebf764d5cdf2407a8172a220e5a9ac605a3a95b1b6341abb91bfdc4fb7d4100c` | - | written for these records: symbol lookup | - |

## bytecmp-7daa0e2a03d9.py

- copy sha256 `d8c4befbf6953ed5c4870ceb64e716095cc5b223d9b02f04b0f8c178ed702820`
- original sha256 `7daa0e2a03d904b973bab1bbb68e57e0e32113d3620950132e296b7a6cc06e24`: tool registry commit 797e8971d27d, tools/bytecmp/7daa0e2a03d9/bytecmp.py
- sha256 of the unredacted diff: `8c01112e59a3b436702bc19571c24a201e644e7171bd5a2b39b278dc4e97943e`

```diff
--- a/bytecmp-7daa0e2a03d9.py
+++ b/bytecmp-7daa0e2a03d9.py
@@ -13 +13 @@
-import sys, hashlib
+import sys, hashlib, os
@@ -46,4 +46,4 @@
-    A linear scan is wrong in both directions, as two lanes measured on 2026-10-29: it pairs an auipc with a word that is a
-    jump-table case entered from elsewhere (<redacted>, printf_core+0x890: a false differing reference), and it drops a
-    binding that a branch target does have, because the FALL-THROUGH path overwrote the register (<redacted> /
-    <redacted>, HaveStackTraceBasedSuppressions+0x3c: a false DIFFERENT). So this is a forward MUST analysis over the
+    A linear scan is wrong in both directions, as two measurements on 2026-10-29 showed: it pairs an auipc with a word that is a
+    jump-table case entered from elsewhere (printf_core+0x890: a false differing reference), and it drops a
+    binding that a branch target does have, because the FALL-THROUGH path overwrote the register
+    (HaveStackTraceBasedSuppressions+0x3c: a false DIFFERENT). So this is a forward MUST analysis over the
@@ -96 +96 @@
-            # so the WRITES_RD pop above kills nothing: a binding kept across an ecall was accepted (<redacted>, 16:35Z).
+            # so the WRITES_RD pop above kills nothing: a binding kept across an ecall was accepted (16:35Z).
@@ -121 +121 @@
-                # width or operation is a real difference (<redacted>, 16:15Z: `ld a2,0x18c(a2)` -> `lw a2,...`, lbu -> lb,
+                # width or operation is a real difference (16:15Z: `ld a2,0x18c(a2)` -> `lw a2,...`, lbu -> lb,
@@ -139,2 +139,2 @@
-base = {'A': '<redacted>',
-        'B': '<redacted>'}
+base = {'A': os.environ.get('BYTECMP_BASE_A', ''),  # unstripped fuzz_preset.asan of omx-clap-core
+        'B': os.environ.get('BYTECMP_BASE_B', '')}  # unstripped fuzz_preset.asan-ubsan of omx-clap-core
```

## drvcmp.py

- copy sha256 `4c3feca0363dcd23a454f19960ac467eb88eb91852afcfea840ca9d34ddea95e`
- original sha256 `fbbdb144ddfc1bbb743ec508071e3396b1f2794528b774d7fbc86d2a1dd366d0`: image-B donor survey scripts (repacer/B-DONORS.md): drvcmp.py (loads bytecmp 7daa0e2a03d9)
- sha256 of the unredacted diff: `9b2633b654b5e5c432759ebd1ebccb3a845dc1d58434c70b65e39a55ab12258b`

```diff
--- a/drvcmp.py
+++ b/drvcmp.py
@@ -4,2 +4,2 @@
-Reuses, verbatim and without running their mains:
-  - bytecmp.py 7daa0e2a03d9 (<redacted> 8cd71d3a4bb tools/bytecmp/7daa0e2a03d9/bytecmp.py): load / words /
+Reuses, without running their mains (these copies differ only in comments and in host paths read from the environment):
+  - bytecmp.py 7daa0e2a03d9 (tool registry commit 8cd71d3a4bb, tools/bytecmp/7daa0e2a03d9/bytecmp.py): load / words /
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
