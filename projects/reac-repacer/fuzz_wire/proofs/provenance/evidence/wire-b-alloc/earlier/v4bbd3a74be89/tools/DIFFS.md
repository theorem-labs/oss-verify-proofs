# Tool copies: sources and changes

Written by mkdiffs.py. Each copy below is the script these records ran. A changed copy's diff against its original has no context lines and is the whole change; a host path that a copy now reads from the environment defaults to empty.

| tool | copy sha256 | original sha256 | source | changed lines |
|---|---|---|---|---|
| `bytecmp-1480ca2faea0.py` | `145447a50bb2b51b84f7b39214a53261d63bd4ac7a8403b61846c4cbf91518a2` | `1480ca2faea075e866800faab4e18aea5fb4a96dcea17ef1fe8981f1bdd0f98f` | tool registry commit 797e8971d27d, tools/bytecmp/1480ca2faea0/bytecmp.py (its lines 39-151 are insnflow a36c2b82eb44, tools/insnflow/a36c2b82eb44/insnflow.py at the same commit) | 12 removed, 12 added (195 lines in, 195 lines out) |
| `closure_strict2.py` | `21028c256d69b6802aaa3f86f5d4e170dc836a37e8389bf84926aa212372634a` | `387ac56b542550b4f0b3ead93eeceee2ed7c75248926caaa925301012c6bc999` | cmpkit 4bbd3a74be89, closure_strict2.py: by-name closure, one compare per X address, loads strictcmp2 | 1 removed, 1 added (98 lines in, 98 lines out) |
| `drvcmp.py` | `5d36e4bd76c603759a93a2c9ce9fd6b1c18908b088fd416109019b4328c5d947` | `4d70e90bc1fa4d70fe1ea53e0208593ee5e87ff53c3b80c8b767ffdff4eaa3a6` | cmpkit 4bbd3a74be89, drvcmp.py: loader (bytecmp + repin_check Img / sx / targets / w_off), twins; no target pass | 7 removed, 7 added (60 lines in, 60 lines out) |
| `dupcheck.py` | `4c08955c12af4db3d5ca86440ed62e603e9d3a71aecf0a1c1b09f03828fe66fd` | - | written for these records: duplicate-name check for every function compared by name (strictcmp2 cmp and closure_strict2) | - |
| `escape.py` | `ef625371dd4977b802db1e61f1514cbe8a056b51f005595c9a74fe4c742e328d` | - | written for these records: second settlement pass for an escaping empty-string pointer: decoded escape sites, direct readers, the field reads from objscan.py, checked return-path words, and the equal window (support) | - |
| `jtcheck.py` | `5a9e1d5cc57f478e85c3d9a7eb828be58f290b141b7bf5f2ea0596ec60b8439e` | `824905e2621161bc7e85cd99db6e724f496e493ee3dae0868d10854b6d8be4c2` | cmpkit 4bbd3a74be89, jtcheck.py: jump / pointer / initializer tables, calls strictcmp2.tsame on every target pair | 4 removed, 4 added (274 lines in, 274 lines out) |
| `mkaccept.py` | `577f8b2aa016bbd95add275c8bc8efd963ef701f07d989a265b4ad5b46e3418e` | - | written for these records: writes ACCEPTANCES.tsv: the kit verdict (unchanged) + settle rows | - |
| `mkdiffs.py` | `5a16d9ee6f8369c43d380843946892f0ff498ccea5f3530583301f8a22606d87` | - | written for these records: the writer of this DIFFS.md | - |
| `objscan.py` | `a13d2bd9706c27d61d4f973de74156b9e895f1154dcfa6ad4f81b2c22de2d267` | - | written for these records: whole-image scan of every load of an object field that an escaping pointer is stored into, each followed to its readers | - |
| `otherrows.py` | `cffff72c9ebef3f91cd39266f1a52715422fc146bd1354a465678b5ae5bcd7ef` | - | written for these records: the function names the kit reports as other (closure_strict2 + paircl) | - |
| `paircl.py` | `e6df5ed4dd8b1a2b934b36b05b345442e5552935e65912c16b221f8e36305d4a` | `e6df5ed4dd8b1a2b934b36b05b345442e5552935e65912c16b221f8e36305d4a` | cmpkit 4bbd3a74be89, paircl.py: target-paired closure vs a stripped pin; every pair judged by strictcmp2.tcmp | unchanged |
| `repin_check-4c05cadaeba3.py` | `b66e5b0528db47c8eabe7a43b5e0ba8cc4ef428b48669eba335532036c8963c8` | `4c05cadaeba3b2ca013e56c056a39afe0f840d6662c6150ed1394e869d3b4353` | cmpkit 4bbd3a74be89, repin_check-4c05cadaeba3.py: shared class Img and sx / targets / w_off (drvcmp execs the blocks) | 8 removed, 8 added (334 lines in, 334 lines out) |
| `scrub_out.py` | `d8a9c91ca817b239896f7ad2500a38833d5215f772330248276730b82b45e7a6` | - | written for these records: the one writer of the committed slice | - |
| `settle.py` | `fbc54a9bdbc129380067f100315db55c87d4d951d9f079693c6c08e8f0f06b41` | - | written for these records: per-target settlement: TABLE / INDEXED / CSTR / RELSTR / INITIALIZER / NOT-PCREL (loads the kit's strictcmp2 and jtcheck) | - |
| `strictcmp2.py` | `61a95130e6d4b008bd55205ccfeb021cdc7ca6cb96bc1d2aa82076f643c55a38` | `16982e3ef42b8773ae979f587eebc32ad365a4012e874047f194779412d1a57c` | cmpkit 4bbd3a74be89, strictcmp2.py: THE ONE compare (tcmp and tsame), the kit's target rule | 3 removed, 3 added (285 lines in, 285 lines out) |
| `syms.py` | `ebf764d5cdf2407a8172a220e5a9ac605a3a95b1b6341abb91bfdc4fb7d4100c` | - | written for these records: symbol lookup | - |

## bytecmp-1480ca2faea0.py

- copy sha256 `145447a50bb2b51b84f7b39214a53261d63bd4ac7a8403b61846c4cbf91518a2`
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
@@ -107 +107 @@
bytecmp-1480ca2faea0.py: reworded after this version ran (a time of day dropped; earlier/SCRUB.tsv: sha256 0ac2ec8db277 as run -> 145447a50bb2 shipped); old bytes in the original (sha256 1480ca2faea0); the sha256 of the unredacted diff above is that of the copy as run
@@ -132 +132 @@
-                # so the WRITES_RD pop above kills nothing: a binding kept across an ecall was accepted (<redacted>).
+                # so the WRITES_RD pop above kills nothing: a binding kept across an ecall was accepted.
@@ -163 +163 @@
-                # width or operation is a real difference (<redacted>: `ld a2,0x18c(a2)` -> `lw a2,...`, lbu -> lb,
+                # width or operation is a real difference (`ld a2,0x18c(a2)` -> `lw a2,...`, lbu -> lb,
@@ -182,2 +182,2 @@
-base = {'A': '<redacted>',
-        'B': '<redacted>'}
+base = {'A': os.environ.get('BYTECMP_BASE_A', ''),  # unstripped fuzz_preset.asan of omx-clap-core
+        'B': os.environ.get('BYTECMP_BASE_B', '')}  # unstripped fuzz_preset.asan-ubsan of omx-clap-core
```

## closure_strict2.py

- copy sha256 `21028c256d69b6802aaa3f86f5d4e170dc836a37e8389bf84926aa212372634a`
- original sha256 `387ac56b542550b4f0b3ead93eeceee2ed7c75248926caaa925301012c6bc999`: cmpkit 4bbd3a74be89, closure_strict2.py: by-name closure, one compare per X address, loads strictcmp2
- sha256 of the unredacted diff: `c2ca74e8e7c32c2a57dc27c3a26cc697a2150ddc984e3e4b675365493b4fe28b`

```diff
--- a/closure_strict2.py
+++ b/closure_strict2.py
@@ -2 +2 @@
-"""closure_strict2.py -- closure_strict.py 16537c22e6bc with the fixes of <redacted>'s review (strictcmp/review/REVIEW.md):
+"""closure_strict2.py -- closure_strict.py 16537c22e6bc with the fixes of its review (REVIEW.md):
```

## drvcmp.py

- copy sha256 `5d36e4bd76c603759a93a2c9ce9fd6b1c18908b088fd416109019b4328c5d947`
- original sha256 `4d70e90bc1fa4d70fe1ea53e0208593ee5e87ff53c3b80c8b767ffdff4eaa3a6`: cmpkit 4bbd3a74be89, drvcmp.py: loader (bytecmp + repin_check Img / sx / targets / w_off), twins; no target pass
- sha256 of the unredacted diff: `a1df6662e2c25edff7e908ff0b80664ad6b5d8bcd74eba08cf51c62dfdefba64`

```diff
--- a/drvcmp.py
+++ b/drvcmp.py
@@ -2 +2 @@
-"""drvcmp.py -- KIT-SHAPED loader (<redacted> strictcmp/review): the names strictcmp2.py, closure_strict2.py and
+"""drvcmp.py -- KIT-SHAPED loader (the strictcmp review): the names strictcmp2.py, closure_strict2.py and
@@ -4,3 +4,3 @@
-  - class Img: lines 31-80 of <redacted>'s new repin_check.py (<redacted> file
-    sha256 4c05cadaeba3, frozen), read from `repin_check.py` beside this file (the kit's name) or, if absent, from
-    `repin_check-4c05cadaeba3.py` (this lane's copy); class text sha256 checked below: syms / byname / res without
+  - class Img: lines 31-80 of the new repin_check.py (file sha256 4c05cadaeba3, frozen), read from `repin_check.py`
+    beside this file (the kit's name) or, if absent, from `repin_check-4c05cadaeba3.py` (the kit's copy); class text
+    sha256 checked below: syms / byname / res without
@@ -10,2 +10,2 @@
-  - bytecmp 1480ca2faea0 (<redacted> tools/bytecmp/1480ca2faea0, version of record; file sha256 checked below),
-    `bytecmp-1480ca2faea0.py` beside this file, everything above its `base = {` line.
+  - bytecmp 1480ca2faea0 (tool registry commit 797e8971d27d, tools/bytecmp/1480ca2faea0; this file beside is that copy
+    with its comments scrubbed, code above `base = {` identical; file sha256 checked below), everything above that line.
@@ -21 +21 @@
-BC_SHA = '1480ca2faea075e866800faab4e18aea5fb4a96dcea17ef1fe8981f1bdd0f98f'
+BC_SHA = '145447a50bb2b51b84f7b39214a53261d63bd4ac7a8403b61846c4cbf91518a2'
```

## jtcheck.py

- copy sha256 `5a9e1d5cc57f478e85c3d9a7eb828be58f290b141b7bf5f2ea0596ec60b8439e`
- original sha256 `824905e2621161bc7e85cd99db6e724f496e493ee3dae0868d10854b6d8be4c2`: cmpkit 4bbd3a74be89, jtcheck.py: jump / pointer / initializer tables, calls strictcmp2.tsame on every target pair
- sha256 of the unredacted diff: `cc0c158c6f75693350335e3fca4c4f756e1442afcf6f5559512a62e13490b41c`

```diff
--- a/jtcheck.py
+++ b/jtcheck.py
@@ -5,2 +5,2 @@
-  strictcmp2.py 16982e3ef42b  -> `tsame`, the target rule of record (and qres / region / frd / cstr_rows), which loads
-  drvcmp.py     4d70e90bc1fa  -> class Img = repin_check 4c05cadaeba3 lines 31-80, targets / sx / w_off lines 209-231,
+  strictcmp2.py 61a95130e6d4  -> `tsame`, the target rule of record (and qres / region / frd / cstr_rows), which loads
+  drvcmp.py     5d36e4bd76c6  -> class Img = repin_check 4c05cadaeba3 lines 31-80, targets / sx / w_off lines 209-231,
@@ -40,2 +40,2 @@
-for _f, _want in (('strictcmp2.py', '16982e3ef42b8773ae979f587eebc32ad365a4012e874047f194779412d1a57c'),
-                  ('drvcmp.py', '4d70e90bc1fa4d70fe1ea53e0208593ee5e87ff53c3b80c8b767ffdff4eaa3a6')):
+for _f, _want in (('strictcmp2.py', '61a95130e6d4b008bd55205ccfeb021cdc7ca6cb96bc1d2aa82076f643c55a38'),
+                  ('drvcmp.py', '5d36e4bd76c603759a93a2c9ce9fd6b1c18908b088fd416109019b4328c5d947')):
```

## repin_check-4c05cadaeba3.py

- copy sha256 `b66e5b0528db47c8eabe7a43b5e0ba8cc4ef428b48669eba335532036c8963c8`
- original sha256 `4c05cadaeba3b2ca013e56c056a39afe0f840d6662c6150ed1394e869d3b4353`: cmpkit 4bbd3a74be89, repin_check-4c05cadaeba3.py: shared class Img and sx / targets / w_off (drvcmp execs the blocks)
- sha256 of the unredacted diff: `217fc0b2704c691cc2641e3331211aaee158ed53b47972b800905fed4097e73b`

```diff
--- a/repin_check-4c05cadaeba3.py
+++ b/repin_check-4c05cadaeba3.py
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
```

## strictcmp2.py

- copy sha256 `61a95130e6d4b008bd55205ccfeb021cdc7ca6cb96bc1d2aa82076f643c55a38`
- original sha256 `16982e3ef42b8773ae979f587eebc32ad365a4012e874047f194779412d1a57c`: cmpkit 4bbd3a74be89, strictcmp2.py: THE ONE compare (tcmp and tsame), the kit's target rule
- sha256 of the unredacted diff: `c954a302745b8772fa359e974551b9d193901c0d6f684449ca6b489b3efab844`

```diff
--- a/strictcmp2.py
+++ b/strictcmp2.py
@@ -2 +2 @@
-"""strictcmp2.py -- strictcmp.py 77daee258b95 with the fixes of <redacted>'s review (strictcmp/review/REVIEW.md).
+"""strictcmp2.py -- strictcmp.py 77daee258b95 with the fixes of its review (REVIEW.md).
@@ -14 +14 @@
strictcmp2.py: reworded after this version ran (a session name written as its role, a time of day dropped; earlier/SCRUB.tsv: sha256 5f6c05791a3f as run -> 61a95130e6d4 shipped); old bytes in the original (sha256 16982e3ef42b); the sha256 of the unredacted diff above is that of the copy as run
@@ -31 +31 @@
-     two offsets name the same STT_TLS symbol+offset (<redacted>'s GD plant: strictcmp read only the module word, 1, and
+     two offsets name the same STT_TLS symbol+offset (the GD plant: strictcmp read only the module word, 1, and
```
