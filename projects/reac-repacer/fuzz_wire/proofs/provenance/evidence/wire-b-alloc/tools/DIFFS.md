# Tool copies: sources and changes

Written by mkdiffs.py. Each copy below is the script these records ran. A changed copy's diff against its original has no context lines and covers the whole change; a host path that a copy now reads from the environment defaults to empty. Every changed comment word is a host path, a branch name, a session's citation dropped with its claim kept (kitscrub.py CITE), the kit's plain word `lane` (its word for a work stream, no session's name) reworded or dropped (kitscrub.py CITE; at ambiscan.py:7, ambiscan.py:13, bytecmp-1480ca2faea0.py:76, drvcmp.py:6, luiscan.py:2), a session name written as its role (`rolenames.py`), a time of day dropped, a README item label or count that jtcheck.py cites, set to its own package's README and controls, or dropped where no README item covers the sentence (kitscrub.py JT_WORDS; dropped at jtcheck.py:578), or a docstring word on what a kit sha256 pin names (jtcheck.py, drvcmp.py: kitscrub.py PIN_WORDS), which the `code compare` line measures: the syntax tree, docstrings left out, is the original's. A removed line is never reworded: a hunk, or a run of lines of a hunk, whose only change is that rewrite is shown as one line, `<copy>: ruling citations reworded by role and times of day dropped; old bytes in ...`, which names the original by its sha256, and in every removed line shown a host path, a branch name, a commit that is not released, a session name and a time of day are `<redacted>`. The sha256 of the unredacted diff lets a holder of the original check each diff.

| tool | copy sha256 | original sha256 | source | changed lines |
|---|---|---|---|---|
| `ambiscan.py` | `be1fbb80ad10ba0e8acd8d50daae0d4ca0b09bb3e5c96c17db4ad08a3665b906` | `9f61b4cee42207e6ae77f33c6ca2d9a9b8f938c38cff50b8c71c057b1e955d8d` | cmpkit 86da41d3ef68 (the tool registry), ambiscan.py: did a by-name compare take the wrong copy of a duplicated name | 2 removed, 2 added (0 comment, 2 docstring, 0 code) |
| `basescan.py` | `a500fff1960c819506f82fba4fcd6ecb9475196de8d0abebbb8c6cb0554f8ce3` | - | written for these records: shape (h): every load / store / AMO / jalr base of the compared set named as its full address in X and Y (roots in full); an address no symbol covers compared by its bytes or settled by jtcheck 226254f48c97's table rule | - |
| `bytecmp-1480ca2faea0.py` | `dc384f1b5867871e5be7b8a5199587c5ce96201b80578a997473e31000733b4d` | `1480ca2faea075e866800faab4e18aea5fb4a96dcea17ef1fe8981f1bdd0f98f` | cmpkit 86da41d3ef68 (the tool registry), bytecmp-1480ca2faea0.py = bytecmp 1480ca2faea0 of the tool registry (its lines 39-151 are insnflow a36c2b82eb44 of the same registry) | 11 removed, 11 added (4 comment, 4 docstring, 3 code) |
| `cite_gen.py` | `edd07bf9f7417ba4fd41e297b54054d4782547b1c6be75b2ed0ee1182cbf368e` | - | written for these records: reads the CITE table (parameter and return types and names) from the pinned compiler-rt source | - |
| `closure_strict3.py` | `6b2293dc84189972c830d8e88a503e07dded2c4150e8f9fb4edcb9112cc18fc0` | `a98d2b3e88574d09d4aee478ba4fed060a3c1577e2229f47affb116c3ccded4e` | cmpkit 86da41d3ef68 (the tool registry), closure_strict3.py: by-name closure, one compare per X address, every differing target printed | 3 removed, 3 added (0 comment, 3 docstring, 0 code) |
| `drvcmp.py` | `2fffab5c772f21d1c84a0fc3b70283afa415f657e401d9cb1b92c38b0fcf9a5d` | `4d70e90bc1fa4d70fe1ea53e0208593ee5e87ff53c3b80c8b767ffdff4eaa3a6` | cmpkit 86da41d3ef68 (the tool registry), drvcmp.py: loader (bytecmp + repin_check Img / sx / targets / w_off), twins; no target pass | 5 removed, 5 added (0 comment, 4 docstring, 1 code) |
| `dupcheck.py` | `4606bbcfaf5337c4544cd00802c6cfe7f0304aa8374cf6bebf65a1ec8b091cee` | - | written for these records: duplicate-name check for every function compared by name (strictcmp3 cmp and closure_strict3) | - |
| `earlierscrub.py` | `716d50b79f044aae3335ecab5e3e1b02356939cb5e64a0a185fd01f6873809a2` | - | written for these records: the writer of the rewrites of a shipped archive of a prior version (earlier/): the role rewrite, the time-of-day rewrite, the forbidden-word loader, the sha256 pin repair and the archive DIFFS.md notes of the role and time rewrites | - |
| `escape.py` | `ef625371dd4977b802db1e61f1514cbe8a056b51f005595c9a74fe4c742e328d` | - | written for these records: second settlement pass for an escaping empty-string pointer: decoded escape sites, direct readers, the field reads from objscan.py, checked return-path words, and the equal window (support) | - |
| `gates.py` | `a2a9422ec6857d89ac5d7ffd9721dd72dd354d196769b2fa855c8f2fa97374f2` | - | written for these records: the gate writer: one verdict file per unit gate (kit, lui, base, plants), each with its evidence lines and its `GATE ... VERDICT:` line, and the two negative controls it runs first | - |
| `handtable.py` | `95e3bc23db39b6dab63d3bd746e5088cfa609114e1976feec4af648708299d6b` | - | written for these records: the hand settlement of a table jtcheck 226254f48c97 refuses, under this record's rule: entries, dispatch, and the bound by a CFG walk, each on both images (parts (1)-(3) of that rule) | - |
| `jtcheck.py` | `94c2f3081b0c0c3d7fe3378b9c31c87da177d07d10cf1d878767bc7d44e0a4e8` | `226254f48c97ba6db570f21d68591e7601d6970cd9f06683dc2ebe2874458dc7` | jtcheck 226254f48c97 (the tool registry), the jtcheck of record for table verdicts, which supersedes the kit's jtcheck 8b0ea3862423 (sha256 8b0ea3862423e3941fd9d70ccc9bcb89cfd89b824fa348140e168880c9745fb7): jump / string tables and initializers, each table's entry size and count proven on the CFG (Flow.prove) or refused; strictcmp3.tcmp per function | 9 removed, 9 added (3 comment, 4 docstring, 2 code) |
| `kitscrub.py` | `b7b6c71d0687eef12ee627f76a7526225986ebf5679cfec312476677a2360ab4` | - | written for these records: the writer of this record's copies of the 9 kit files (jtcheck.py: of jtcheck 226254f48c97) (comment and docstring words, unused host-path constants, and the kit's own sha pins with the docstring words on them, set to the copies) | - |
| `luirows.py` | `66635dceece160bb57d6f89a4e9c8971806a758c4ca1e6862e564d026f8d3bf7` | - | written for these records: luiscan's exposed functions re-run on strictcmp3.tcmp by address (EXPOSED / RERUN rows) | - |
| `luiscan.py` | `25e8c224d06a1e620756821f1ab5f3fbff57e7f6c0ea6a6bca6448019de44f00` | `9ae61e4a0e018677862566a53e3b9a6c0f1a89c9f71a9012bf1893f8ec93edad` | cmpkit 86da41d3ef68 (the tool registry), luiscan.py: the rule-8 (lui) exposure scan per function | 4 removed, 4 added (0 comment, 4 docstring, 0 code) |
| `luitrace.py` | `06d2b10059328c1d49909fb4bb3ae2b511d2dd732e9a7f07f145e9d438a743c8` | - | written for these records: the hand trace of every lui value of every compared function (shapes a-g), with the settlement classes of the rulings | - |
| `mkaccept.py` | `984322748de50482cd70fb3e039d90bd12826ab852b5a7b114badac7ed0df2ae` | - | written for these records: writes ACCEPTANCES.tsv: the kit verdict (unchanged) + settle rows + one LUI row per lui-in-section target + the plants | - |
| `mkdiffs.py` | `e196c869957e72b6cb5fcc2cca1850518115f67f68e8e3fbfba4368154d6c85e` | - | written for these records: the writer of this DIFFS.md | - |
| `objscan.py` | `a13d2bd9706c27d61d4f973de74156b9e895f1154dcfa6ad4f81b2c22de2d267` | - | written for these records: whole-image scan of every load of an object field that an escaping pointer is stored into, each followed to its readers | - |
| `otherrows.py` | `478be38abafd5bd0c3a106676d85c879f72ec2d990196be458f2938f6622bd52` | - | written for these records: the function names the kit reports as other (closure_strict3 + paircl) | - |
| `paircl.py` | `926a9a88afcdc233aa5cd0451a0a8965217e1e08dbc09ffb4e7e8c3bd61017e1` | `926a9a88afcdc233aa5cd0451a0a8965217e1e08dbc09ffb4e7e8c3bd61017e1` | cmpkit 86da41d3ef68 (the tool registry), paircl.py: target-paired closure against a STRIPPED pin; every pair judged by strictcmp3.tcmp | 0 removed, 0 added (0 comment, 0 docstring, 0 code) |
| `plants.py` | `237bb0a60df5a283f1d98e5a23efc37ac4f744687f9a0b4fa9791c0c7bc44e7a` | - | written for these records: the plants: (a) lui + lui -> add -> a store base and (c) lui -> divuw -> slli -> a store base, both caught as DIFFERS; (b) a lui argument re-pointed to a uptr parameter, refused | - |
| `repin_check.py` | `47993ba4c4ff965a4dbcf71d8ea164dc74467c5aa68f9a631679688e925895dd` | `e6883477399df80d35e1810dd93f2d5c85aa4d07cb16fbc887ad625851d98a66` | cmpkit 86da41d3ef68 (the tool registry), repin_check.py: the shared class Img (lines 31-80) and sx / targets / w_off (209-231); `funcs` on strictcmp3 | 10 removed, 10 added (2 comment, 2 docstring, 6 code) |
| `rolenames.py` | `6f3a126a733e174ca0f486ec149e5b25b593fa420c1e871c718dae65c7dd00ed` | - | written for these records: the one place that knows how a ruling is cited in a shipped file: by the role that made it, never by a session name and with no time of day (used by kitscrub.py, scrub_out.py, earlierscrub.py and this writer); it also reads, at run time, the private list SCRUB_FORBIDDEN (outside the slice) that holds the text these writers refuse, redact or rewrite | - |
| `scrub_out.py` | `cda7256574a9c7f07c896aac6ca709a7b40781b853c4c6d7f23b04a7ace9379a` | - | written for these records: the one writer of the committed slice | - |
| `settle.py` | `4eeeae29391239cd05fa069163f59fed518337a82193313220980053d2f6da85` | - | written for these records: per-target settlement: TABLE / REFUSED / INDEXED / CSTR / RELSTR / INITIALIZER / NOT-PCREL (loads strictcmp3 through jtcheck 226254f48c97, and uses its table / copy_len, with the table shape its Flow.prove gives on both images: luitrace.table_proof2) | - |
| `strictcmp3.py` | `b553126fa2247d965b16c4f3f6008319d6355b49146b666e36fe51c3dda3cd55` | `65688e94214a74664ffa83a21c283412a64b81f8a7eaa40f970a91f4eb1319b7` | cmpkit 86da41d3ef68 (the tool registry), strictcmp3.py: THE ONE compare (tcmp, tsame, lui_scan / rule 8, the combined verdict) | 13 removed, 13 added (1 comment, 12 docstring, 0 code) |
| `syms.py` | `ebf764d5cdf2407a8172a220e5a9ac605a3a95b1b6341abb91bfdc4fb7d4100c` | - | written for these records: symbol lookup | - |

## ambiscan.py

- copy sha256 `be1fbb80ad10ba0e8acd8d50daae0d4ca0b09bb3e5c96c17db4ad08a3665b906`
- original sha256 `9f61b4cee42207e6ae77f33c6ca2d9a9b8f938c38cff50b8c71c057b1e955d8d`: cmpkit 86da41d3ef68 (the tool registry), ambiscan.py: did a by-name compare take the wrong copy of a duplicated name
- changed lines: 0 comment, 2 docstring, 0 code
- code compare: the syntax tree with docstrings left out is EQUAL (a comment is in no tree): every changed line is a comment or a docstring
- sha256 of the unredacted diff: `5bf276170bb7df4b58da8693d5ab7593577b9e61ae745f9f2b78f7698f6e3404`

```diff
--- a/ambiscan.py
+++ b/ambiscan.py
@@ -7 +7 @@
-the LOWEST-address copy (the asan_errors.cpp one), while the callers use other copies. ambiscan reads a lane's output
+the LOWEST-address copy (the asan_errors.cpp one), while the callers use other copies. ambiscan reads a record's output
@@ -13 +13 @@
-  X_ELF, Y_ELF: the two images the lane's compares used (both with .symtab). Each OUTFILE is a file or a directory
+  X_ELF, Y_ELF: the two images the compares used (both with .symtab). Each OUTFILE is a file or a directory
```

## bytecmp-1480ca2faea0.py

- copy sha256 `dc384f1b5867871e5be7b8a5199587c5ce96201b80578a997473e31000733b4d`
- original sha256 `1480ca2faea075e866800faab4e18aea5fb4a96dcea17ef1fe8981f1bdd0f98f`: cmpkit 86da41d3ef68 (the tool registry), bytecmp-1480ca2faea0.py = bytecmp 1480ca2faea0 of the tool registry (its lines 39-151 are insnflow a36c2b82eb44 of the same registry)
- changed lines: 4 comment, 4 docstring, 3 code
- code compare: every changed code line is line 13 the `os` import that environment read needs; line 182 a path read from the environment; line 183 a path read from the environment; the tree is otherwise the original's
- sha256 of the unredacted diff: `ebc975df001293b005a430124459ac5fa2262165d6b9c71519b3713b13190607`

```diff
--- a/bytecmp-1480ca2faea0.py
+++ b/bytecmp-1480ca2faea0.py
@@ -13 +13 @@
-import sys, hashlib
+import sys, hashlib, os
@@ -39 +39 @@
-# ---- insnflow block begin (owner <redacted>). The same bytes as <redacted> (record: <redacted>
+# ---- insnflow block begin. The same bytes as insnflow a36c2b82eb44 of the tool registry apart from comments and docstrings (record: the tool registry
@@ -76,4 +76,4 @@
-    A linear scan is wrong in both directions, as two lanes measured on 2026-10-29: it pairs an auipc with a word that is a
-    jump-table case entered from elsewhere (<redacted>, printf_core+0x890: a false differing reference), and it drops a
-    binding that a branch target does have, because the FALL-THROUGH path overwrote the register (<redacted> /
-    <redacted>, HaveStackTraceBasedSuppressions+0x3c: a false DIFFERENT). So this is a forward MUST analysis over the
+    A linear scan is wrong in both directions, as two measurements on 2026-10-29 showed: it pairs an auipc with a word that is a
+    jump-table case entered from elsewhere (printf_core+0x890: a false differing reference), and it drops a
+    binding that a branch target does have, because the FALL-THROUGH path overwrote the register
+    (HaveStackTraceBasedSuppressions+0x3c: a false DIFFERENT). So this is a forward MUST analysis over the
bytecmp-1480ca2faea0.py: ruling citations reworded by role and times of day dropped; old bytes in the tool registry (sha256 1480ca2faea0)
@@ -132 +132 @@
-                # so the WRITES_RD pop above kills nothing: a binding kept across an ecall was accepted (<redacted>, <redacted>).
+                # so the WRITES_RD pop above kills nothing: a binding kept across an ecall was accepted.
@@ -163 +163 @@
-                # width or operation is a real difference (<redacted>, <redacted>: `ld a2,0x18c(a2)` -> `lw a2,...`, lbu -> lb,
+                # width or operation is a real difference (`ld a2,0x18c(a2)` -> `lw a2,...`, lbu -> lb,
@@ -182,2 +182,2 @@
-base = {'A': '<redacted>',
-        'B': '<redacted>'}
+base = {'A': os.environ.get('KIT_BYTECMP_1480CA2FAEA0_182_1', ''),
+        'B': os.environ.get('KIT_BYTECMP_1480CA2FAEA0_183_1', '')}
```

## closure_strict3.py

- copy sha256 `6b2293dc84189972c830d8e88a503e07dded2c4150e8f9fb4edcb9112cc18fc0`
- original sha256 `a98d2b3e88574d09d4aee478ba4fed060a3c1577e2229f47affb116c3ccded4e`: cmpkit 86da41d3ef68 (the tool registry), closure_strict3.py: by-name closure, one compare per X address, every differing target printed
- changed lines: 0 comment, 3 docstring, 0 code
- code compare: the syntax tree with docstrings left out is EQUAL (a comment is in no tree): every changed line is a comment or a docstring
- sha256 of the unredacted diff: `a32e63a32228b496b4c45e360dad95d733d1e8d682e9685732419a0beead2481`

```diff
--- a/closure_strict3.py
+++ b/closure_strict3.py
@@ -2,2 +2,2 @@
-"""closure_strict3.py -- closure_strict2.py 387ac56b5425 (cmpkit 4bbd3a74be89) on strictcmp3.py (<redacted>,
-strictcmp/lui/LUI.md). Changes against closure_strict2:
+"""closure_strict3.py -- closure_strict2.py 387ac56b5425 (cmpkit 4bbd3a74be89) on strictcmp3.py
+(strictcmp/lui/LUI.md). Changes against closure_strict2:
@@ -8 +8 @@
-   printed `AMBIGUOUS root name` and went on with rc 0; strictcmp2 cmp took the lowest address, <redacted>);
+   printed `AMBIGUOUS root name` and went on with rc 0; strictcmp2 cmp took the lowest address);
```

## drvcmp.py

- copy sha256 `2fffab5c772f21d1c84a0fc3b70283afa415f657e401d9cb1b92c38b0fcf9a5d`
- original sha256 `4d70e90bc1fa4d70fe1ea53e0208593ee5e87ff53c3b80c8b767ffdff4eaa3a6`: cmpkit 86da41d3ef68 (the tool registry), drvcmp.py: loader (bytecmp + repin_check Img / sx / targets / w_off), twins; no target pass
- changed lines: 0 comment, 4 docstring, 1 code
- code compare: every changed code line is line 21 a sha256 pin set to this record's copy of the file it pins; the tree is otherwise the original's
- sha256 of the unredacted diff: `e1b2203ffb356fd3c216a980d1896e4393fe90f631126ccf8efb562300ba1b0e`

```diff
--- a/drvcmp.py
+++ b/drvcmp.py
@@ -2 +2 @@
-"""drvcmp.py -- KIT-SHAPED loader (<redacted> strictcmp/review): the names strictcmp2.py, closure_strict2.py and
+"""drvcmp.py -- KIT-SHAPED loader (the strictcmp review): the names strictcmp2.py, closure_strict2.py and
@@ -4 +4 @@
-  - class Img: lines 31-80 of <redacted>'s new repin_check.py (<redacted> file
+  - class Img: lines 31-80 of the new repin_check.py (file
@@ -6 +6 @@
-    `repin_check-4c05cadaeba3.py` (this lane's copy); class text sha256 checked below: syms / byname / res without
+    `repin_check-4c05cadaeba3.py` (the kit's copy); class text sha256 checked below: syms / byname / res without
@@ -10 +10 @@
-  - bytecmp 1480ca2faea0 (<redacted> tools/bytecmp/1480ca2faea0, version of record; file sha256 checked below),
+  - copy dc384f1b5867 of bytecmp 1480ca2faea0 (tool registry tools/bytecmp/1480ca2faea0, version of record; the copy's sha256 checked below),
@@ -21 +21 @@
-BC_SHA = '1480ca2faea075e866800faab4e18aea5fb4a96dcea17ef1fe8981f1bdd0f98f'
+BC_SHA = 'dc384f1b5867871e5be7b8a5199587c5ce96201b80578a997473e31000733b4d'
```

## jtcheck.py

- copy sha256 `94c2f3081b0c0c3d7fe3378b9c31c87da177d07d10cf1d878767bc7d44e0a4e8`
- original sha256 `226254f48c97ba6db570f21d68591e7601d6970cd9f06683dc2ebe2874458dc7`: jtcheck 226254f48c97 (the tool registry), the jtcheck of record for table verdicts, which supersedes the kit's jtcheck 8b0ea3862423 (sha256 8b0ea3862423e3941fd9d70ccc9bcb89cfd89b824fa348140e168880c9745fb7): jump / string tables and initializers, each table's entry size and count proven on the CFG (Flow.prove) or refused; strictcmp3.tcmp per function
- changed lines: 3 comment, 4 docstring, 2 code
- code compare: every changed code line is line 51 a sha256 pin set to this record's copy of the file it pins; line 52 a sha256 pin set to this record's copy of the file it pins; the tree is otherwise the original's
- sha256 of the unredacted diff: `e15ff5397f11d3c9bb3eb3a4462e167c35653351335a9b259f782742ba988213`

```diff
--- a/jtcheck.py
+++ b/jtcheck.py
@@ -4 +4 @@
-Loads the comparison kit beside it, checking each file's sha256:
+Loads the comparison kit beside it; named here are the kit originals, the pins below are set to this record's copies:
@@ -51,2 +51,2 @@
-for _f, _want in (('strictcmp3.py', '65688e94214a74664ffa83a21c283412a64b81f8a7eaa40f970a91f4eb1319b7'),
-                  ('drvcmp.py', '4d70e90bc1fa4d70fe1ea53e0208593ee5e87ff53c3b80c8b767ffdff4eaa3a6')):
+for _f, _want in (('strictcmp3.py', 'b553126fa2247d965b16c4f3f6008319d6355b49146b666e36fe51c3dda3cd55'),
+                  ('drvcmp.py', '2fffab5c772f21d1c84a0fc3b70283afa415f657e401d9cb1b92c38b0fcf9a5d')):
@@ -205 +205 @@
-# STORED TO MEMORY: the bytes settle it, the refusal is ON and it costs nothing - of the 63 tables the
+# STORED TO MEMORY: the bytes settle it, the refusal is ON and it costs nothing - of the 48 tables the
@@ -208,2 +208,2 @@
-# and the refusal is OFF by default - it flags 24 of those 63 and would cost 32 of 89 acceptances on the
-# record pairs (README A6, controls/escmeas.out and esccost.out).
+# and the refusal is OFF by default - it flags 18 of those 48, and turning it on costs 48 -> 30 acceptances on the
+# record pairs (README A5, controls/escmeas.out and esccost.out).
@@ -515 +515 @@
-        refuses here as it does at a write. The psABI assumption A3 does not cover a return address the bytes
+        refuses here as it does at a write. The psABI assumption A1 does not cover a return address the bytes
@@ -578 +578 @@
-          write one (README A3). The integer source is rs1 in all four.
+          write one. The integer source is rs1 in all four.
@@ -791 +791 @@
-          register may be dead), so it refuses only when `args` is set (README A6). None when it never leaves."""
+          register may be dead), so it refuses only when `args` is set (README A5). None when it never leaves."""
```

## luiscan.py

- copy sha256 `25e8c224d06a1e620756821f1ab5f3fbff57e7f6c0ea6a6bca6448019de44f00`
- original sha256 `9ae61e4a0e018677862566a53e3b9a6c0f1a89c9f71a9012bf1893f8ec93edad`: cmpkit 86da41d3ef68 (the tool registry), luiscan.py: the rule-8 (lui) exposure scan per function
- changed lines: 0 comment, 4 docstring, 0 code
- code compare: the syntax tree with docstrings left out is EQUAL (a comment is in no tree): every changed line is a comment or a docstring
- sha256 of the unredacted diff: `12e0866fb1236408dd0cae83933a8219ebf68f154f7af548ab9b40bf648c3d51`

```diff
--- a/luiscan.py
+++ b/luiscan.py
@@ -2 +2 @@
-"""luiscan.py -- exposure of strictcmp3.py's rule 8 (lui-built absolute values) per image and function, so that a lane
+"""luiscan.py -- exposure of strictcmp3.py's rule 8 (lui-built absolute values) per image and function, so that a record
luiscan.py: ruling citations reworded by role and times of day dropped; old bytes in the tool registry (sha256 9ae61e4a0e01)
luiscan.py: ruling citations reworded by role and times of day dropped; old bytes in the tool registry (sha256 9ae61e4a0e01)
```

## paircl.py

- copy sha256 `926a9a88afcdc233aa5cd0451a0a8965217e1e08dbc09ffb4e7e8c3bd61017e1`
- original sha256 `926a9a88afcdc233aa5cd0451a0a8965217e1e08dbc09ffb4e7e8c3bd61017e1`: cmpkit 86da41d3ef68 (the tool registry), paircl.py: target-paired closure against a STRIPPED pin; every pair judged by strictcmp3.tcmp
- changed lines: 0 comment, 0 docstring, 0 code
- code compare: the syntax tree with docstrings left out is EQUAL (a comment is in no tree): every changed line is a comment or a docstring
- sha256 of the unredacted diff: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`

```diff
```

## repin_check.py

- copy sha256 `47993ba4c4ff965a4dbcf71d8ea164dc74467c5aa68f9a631679688e925895dd`
- original sha256 `e6883477399df80d35e1810dd93f2d5c85aa4d07cb16fbc887ad625851d98a66`: cmpkit 86da41d3ef68 (the tool registry), repin_check.py: the shared class Img (lines 31-80) and sx / targets / w_off (209-231); `funcs` on strictcmp3
- changed lines: 2 comment, 2 docstring, 6 code
- code compare: every changed code line is line 16 a path read from the environment; line 17 a path read from the environment; line 18 a path read from the environment; line 19 a path read from the environment; line 20 a path read from the environment; line 21 a path read from the environment; the tree is otherwise the original's
- sha256 of the unredacted diff: `f2e024ed9996a9512f8369c0a2c002f30f2cbf09a122a84a8426de6b5b518ef4`

```diff
--- a/repin_check.py
+++ b/repin_check.py
@@ -2,2 +2,2 @@
-"""repin_check.py -- independent check of <redacted>'s PSnp* restatement/re-pin (<redacted>
-<redacted>) against <redacted> (<redacted> <redacted>).  Read-only.
+"""repin_check.py -- independent check of a PSnp* restatement / re-pin
+against the fm restatement.  Read-only.
@@ -16,6 +16,6 @@
-IMG = {'A': '<redacted>',
-       'B': '<redacted>',
-       'F': '<redacted>'}
-PIN = {'A': ('<redacted>', 'd83eb25d', 'f0d2e8d40c7e3ed0'),
-       'B': ('<redacted>', 'f8f98a95', '3b5e1a099b535acf'),
-       'F': ('<redacted>', '0ba7e169', 'fc92e86bee065b5d')}
+IMG = {'A': os.environ.get('KIT_REPIN_CHECK_16_1', ''),
+       'B': os.environ.get('KIT_REPIN_CHECK_17_1', ''),
+       'F': os.environ.get('KIT_REPIN_CHECK_18_1', '')}
+PIN = {'A': (os.environ.get('KIT_REPIN_CHECK_19_1', ''), 'd83eb25d', 'f0d2e8d40c7e3ed0'),
+       'B': (os.environ.get('KIT_REPIN_CHECK_20_1', ''), 'f8f98a95', '3b5e1a099b535acf'),
+       'F': (os.environ.get('KIT_REPIN_CHECK_21_1', ''), '0ba7e169', 'fc92e86bee065b5d')}
@@ -239 +239 @@
-    # interceptor (tbl_vsn's base table, A/AE34.v at <redacted>)
+    # interceptor (tbl_vsn's base table, in A/AE34.v)
@@ -251 +251 @@
-        if amb:   # a name several functions carry is refused, never resolved to the lowest copy (the kit's rule, <redacted>)
+        if amb:   # a name several functions carry is refused, never resolved to the lowest copy (the kit's rule)
```

## strictcmp3.py

- copy sha256 `b553126fa2247d965b16c4f3f6008319d6355b49146b666e36fe51c3dda3cd55`
- original sha256 `65688e94214a74664ffa83a21c283412a64b81f8a7eaa40f970a91f4eb1319b7`: cmpkit 86da41d3ef68 (the tool registry), strictcmp3.py: THE ONE compare (tcmp, tsame, lui_scan / rule 8, the combined verdict)
- changed lines: 1 comment, 12 docstring, 0 code
- code compare: the syntax tree with docstrings left out is EQUAL (a comment is in no tree): every changed line is a comment or a docstring
- sha256 of the unredacted diff: `3a338bab38cddf6247b2c540eef5238a31c39dc33ba9e27e974d4aa8c2a917b7`

```diff
--- a/strictcmp3.py
+++ b/strictcmp3.py
@@ -2,2 +2,2 @@
-"""strictcmp3.py -- strictcmp2.py 16982e3ef42b (the one compare of cmpkit 4bbd3a74be89) with these changes (<redacted>,
-strictcmp/lui/LUI.md): rule 8 (a lui-built absolute value is a target); rule 2 (compiler string labels: NAME-ONLY,
+"""strictcmp3.py -- strictcmp2.py 16982e3ef42b (the one compare of cmpkit 4bbd3a74be89) with these changes
+(strictcmp/lui/LUI.md): rule 8 (a lui-built absolute value is a target); rule 2 (compiler string labels: NAME-ONLY,
strictcmp3.py: ruling citations reworded by role and times of day dropped; old bytes in the tool registry (sha256 65688e94214a)
@@ -21 +21 @@
-     labels give `NAME-ONLY`, listed like an acceptance (<redacted>, fuzz_preset B: `.str.3{preset_file.c}` vs `.str.3`,
+     labels give `NAME-ONLY`, listed like an acceptance (fuzz_preset B: `.str.3{preset_file.c}` vs `.str.3`,
strictcmp3.py: ruling citations reworded by role and times of day dropped; old bytes in the tool registry (sha256 65688e94214a)
@@ -44 +44 @@
-     two offsets name the same STT_TLS symbol+offset (<redacted>'s GD plant: strictcmp read only the module word, 1, and
+     two offsets name the same STT_TLS symbol+offset (a GD plant: strictcmp read only the module word, 1, and
@@ -53 +53 @@
-  8. a lui-built ABSOLUTE value is a target (<redacted>'s plant: `lui t0,0x5f3; ld t1,0x750(t0)`, the same bytes in two
+  8. a lui-built ABSOLUTE value is a target (a plant: `lui t0,0x5f3; ld t1,0x750(t0)`, the same bytes in two
strictcmp3.py: ruling citations reworded by role and times of day dropped; old bytes in the tool registry (sha256 65688e94214a)
strictcmp3.py: ruling citations reworded by role and times of day dropped; old bytes in the tool registry (sha256 65688e94214a)
strictcmp3.py: ruling citations reworded by role and times of day dropped; old bytes in the tool registry (sha256 65688e94214a)
@@ -103 +103 @@
-  to give instead), nothing is compared, exit status 1 (strictcmp2 silently took the lowest address, <redacted>)."""
+  to give instead), nothing is compared, exit status 1 (strictcmp2 silently took the lowest address)."""
strictcmp3.py: ruling citations reworded by role and times of day dropped; old bytes in the tool registry (sha256 65688e94214a)
@@ -559 +559 @@
-    # (strictcmp2 took the lowest address: `MemToShadow` = the asan_errors.cpp copy of five, <redacted>)
+    # (strictcmp2 took the lowest address: `MemToShadow` = the asan_errors.cpp copy of five)
```
