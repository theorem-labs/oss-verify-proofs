# rt-setshadow/: the byte compare behind lib/A/Rt/RtSetShadow.v

## What was compared, and why

Image A of this unit is fuzz_transport.asan, pin sha256
e89be137db17b720e0310addc2dcc601998945478a9102e6a9850b0566106350 (builds.asan of
projects/libdiginet/fuzz_transport/harness.yaml). Its three shadow-fill entries `__asan_set_shadow_00`,
`__asan_set_shadow_f5` and `__asan_set_shadow_f8`, at 0x55270, 0x55378 and 0x55390, set n shadow bytes from a to the
value 0x00 (usable), 0xf5 (released frame) or 0xf8 (variable out of scope), by musl memset. Their proofs in this unit
are lib/A/Rt/RtSetShadow.v (theorems transport_set_shadow_00 / _f5 / _f8) and its three uses lib/A/Rt/RtSS00Cg.v,
lib/A/Rt/RtSSF5Cg.v and lib/A/Rt/RtSSF8Cg.v.

These proofs were relocated from the released proof of libreac/fuzz_grant: its lib/A/Rt/SetShadow.v
(projects/libreac/fuzz_grant/proofs/lib/A/Rt/SetShadow.v at recipes commit c3777b3715d0, file sha256
50fd0fe8abe7c18130f67648857f15aa2d4e02a788fe5036490c2684729f2afe), theorems grant_set_shadow_00 at line 190,
grant_set_shadow_f5 at line 192 and grant_set_shadow_f8 at line 194, over the donor entries 0x546bc, 0x547c4 and
0x547dc (lines 28-30). A relocated walk holds for this image only when this image's code is the donor's code. So the
three entries, and musl memset, which they jump to, were compared byte for byte with the donor image.

Verdict: each of the three entries is EQUAL-mod-pcrel to the donor's entry (24 bytes, 6 words; 2 pc-relative words;
0 real differences; 0 unmeasured; 0 differing targets). musl memset is EQUAL (0x9d614 vs 0x95e30, 248 bytes; 0
pc-relative words; 0 real differences).

## Images

| name in the commands | what it is | sha256 |
|---|---|---|
| images/fuzz_transport.asan | the unstripped twin of image A (it has the symbols) | 86efc3a80314981197619c115e313dbde50e8b86a6c5fefad4e5cc420250c792 |
| images/fuzz_transport.asan.pin | image A, the pin | e89be137db17b720e0310addc2dcc601998945478a9102e6a9850b0566106350 |
| images/fuzz_grant.asan | the unstripped twin of the donor image fuzz_grant.asan (pin c2c7559b29bd) | 57c26f99361583f69af95af52819bebfcf920468a03cf795b95e024fe9798a4d |

Each name is a symbolic link, in the scratch directory of the run, to the image file. The twin's PT_LOAD bytes are
equal to the pin's except the ELF header and the build-id note at 0x10028-0x102cb (../core-A/METHOD.md,
../core-A/records/STRICTCMP-RUNTIME.md). The three entries are in the .text PT_LOAD and the cells they read are in
the .got and .data PT_LOADs, which are equal in the twin and the pin. pin-reread.txt reads the entries and the cells
from the pin itself.

## Files and results

- strictcmp3-setshadow.out: the compare, one row per function (A = image A's twin, G = the donor's twin):

  | function | A | G | size | verdict | pcrel | real | unmeasured | target-differ |
  |---|---|---|---|---|---|---|---|---|
  | __asan_set_shadow_00 | 0x55270 | 0x546bc | 24 | EQUAL-mod-pcrel | 2 | 0 | 0 | 0 |
  | __asan_set_shadow_f5 | 0x55378 | 0x547c4 | 24 | EQUAL-mod-pcrel | 2 | 0 | 0 | 0 |
  | __asan_set_shadow_f8 | 0x55390 | 0x547dc | 24 | EQUAL-mod-pcrel | 2 | 0 | 0 | 0 |
  | memset | 0x9d614 | 0x95e30 | 248 | EQUAL | 0 | 0 | 0 | 0 |

  The C-string rule was ON (the default). No acceptances. The words-only verdict is the same as the verdict.
- strictcmp3-setshadow.err: the compare's stderr, 0 bytes (exit status 0).
- ssh-A.txt and ssh-G.txt: the three entries of each twin, word by word, with the cells they read. The 2 pc-relative
  words of each entry are its auipc / ld pair, which reads one .got cell: 0xa40b0 in image A, 0x9c890 in the donor.
  That cell holds 0xa5ef8 in image A (0x9e6d8 in the donor), the address of `__interception::real_memset`
  (`_ZN14__interception11real_memsetE`), which holds 0x9d614 (0x95e30), musl memset. The other 4 words of each
  entry are the same words in both images. strictcmp3 compares a .got cell that holds an address by the symbol of
  that address (rule 5 of its docstring), and the symbol is the same on both sides.
- pin-reread.txt: from the pin: the 6 words of each entry (the same words as ssh-A.txt), the cell 0xa40b0 = 0xa5ef8,
  the cell 0xa5ef8 = 0x9d614, and the .text, .got and .data section headers.
- luiscan-setshadow.out: the lui words of the four functions in both twins. The three entries have no lui word.
  memset has 1 lui word in each image, with insec 0, memfed 0, luiconst 0, unmeasured 0 and exposure 0. So
  strictcmp3's rule 8 (a lui-built absolute value is a target) has no target in these functions, and memset's
  verdict is the verdict of its words. Totals: functions 8, with-lui 2, with-exposure 0.
- sshdis.py: the reader that wrote ssh-A.txt and ssh-G.txt (pyelftools + capstone; it needs the twin's .symtab).
- pinread.py: the reader that wrote pin-reread.txt (pyelftools; by address only). It was written for this slice; see
  "Regeneration".

## Tools, by file sha256

The comparison kit is the nine files that its SHA256SUMS lists; that SHA256SUMS file has sha256
86da41d3ef68abf071a843e599786e5eb0a6ed77c4a6b6eb645e7498bffbee60 (the same kit as cmpkit 86da41d3ef68 in
../core-A/records/STRICTCMP-RUNTIME.md). The run used these kit files:

| file | sha256 | use |
|---|---|---|
| strictcmp3.py | 65688e94214a74664ffa83a21c283412a64b81f8a7eaa40f970a91f4eb1319b7 | the compare |
| luiscan.py | 9ae61e4a0e018677862566a53e3b9a6c0f1a89c9f71a9012bf1893f8ec93edad | the lui scan; loads strictcmp3.py |
| drvcmp.py | 4d70e90bc1fa4d70fe1ea53e0208593ee5e87ff53c3b80c8b767ffdff4eaa3a6 | loaded by strictcmp3.py |
| repin_check.py | e6883477399df80d35e1810dd93f2d5c85aa4d07cb16fbc887ad625851d98a66 | loaded by drvcmp.py (its ELF reader class only) |
| bytecmp-1480ca2faea0.py | 1480ca2faea075e866800faab4e18aea5fb4a96dcea17ef1fe8981f1bdd0f98f | loaded by drvcmp.py (the word compare) |

The kit files are not in this slice, because their code holds paths of the build host. They are named here only by
sha256. The two readers are in this slice: sshdis.py sha256
8990190bc97d2ed3103763f921b05d4540565605aa1916bbb4d78eb715417e6d, pinread.py sha256
24d6eb6978141a330f2909c3d86157e1c77a63c360e3725c7a7314f5e3670f65. Python 3.12.3, pyelftools 0.33, capstone 5.0.7.

## Re-run commands

Run on 2026-10-31 from a scratch directory that holds images/ (the three links above), cmpkit/ (the nine kit files
and their SHA256SUMS; `sha256sum -c SHA256SUMS` printed OK for all nine) and ev/ (sshdis.py and pinread.py), with
PYTHONDONTWRITEBYTECODE=1 in the environment:

```
python3 cmpkit/strictcmp3.py cmp __asan_set_shadow_00,__asan_set_shadow_f5,__asan_set_shadow_f8,memset A=images/fuzz_transport.asan G=images/fuzz_grant.asan A:G > strictcmp3-setshadow.out 2> strictcmp3-setshadow.err
python3 cmpkit/luiscan.py --fns __asan_set_shadow_00,__asan_set_shadow_f5,__asan_set_shadow_f8,memset images/fuzz_transport.asan images/fuzz_grant.asan > luiscan-setshadow.out
python3 ev/sshdis.py images/fuzz_transport.asan 86efc3a80314 __asan_set_shadow_00 __asan_set_shadow_f5 __asan_set_shadow_f8 > ssh-A.txt
python3 ev/sshdis.py images/fuzz_grant.asan 57c26f993615 __asan_set_shadow_00 __asan_set_shadow_f5 __asan_set_shadow_f8 > ssh-G.txt
python3 ev/pinread.py images/fuzz_transport.asan.pin e89be137db17 --words 0x55270:24,0x55378:24,0x55390:24 --u64 0xa40b0,0xa5ef8 --sections .text,.got,.data > pin-reread.txt
```

Each command exited with status 0 and wrote nothing to stderr. Controls of pinread.py: with the SHA12 000000000000 it
exits 1 (the sha256 does not match); with `--u64 0x700000` (no file bytes of any PT_LOAD) it exits 1.

## Regeneration

The first run of these commands (2026-10-31, by the lane that relocated the files) named each image by its path on
the build host. The commands above re-ran it with the neutral names. In each first-run output, each host path was
replaced by its neutral name, and the result was compared with the output here (diff). The only differences are the
image paths on the header lines; there is no other difference:

| file here | first-run output, sha256 (internal record) | lines that differ before the path replacement |
|---|---|---|
| strictcmp3-setshadow.out | c4f0c3b53020 | 1, 2 (the A and G image lines) |
| strictcmp3-setshadow.err | e3b0c44298fc (0 bytes) | none |
| luiscan-setshadow.out | f90392915934 | 2, 5 (the two `# image` lines) |
| ssh-A.txt | 86da49c6e22b | 1 |
| ssh-G.txt | 5e9c7d64c3b5 | 1 |
| pin-reread.txt | 769357cdee1b | 1 |

The command that wrote the first pin-reread.txt is not kept with that record, and sshdis.py cannot read the pin (the
pin has no .symtab; sshdis.py stops with AttributeError). pinread.py reads the same bytes by address. Its output is
equal to the first-run record except the image path on line 1.

## Internal records (not in this slice)

- memset-lui.txt (sha256 a5dcbd3969d4; internal record): the lui word of memset (`lui a1, 0x10101` at memset+0x48 in
  both images) and the instructions that use its value. The command that wrote it is not kept with it, so it was not
  regenerated. luiscan-setshadow.out gives the tool's count for the same word (exposure 0).
- The six first-run outputs in the table above: they name host paths.
- The records of the relocation itself: mkwalk.py (sha256 5771f712f6c9; internal record), which writes RtSetShadow.v
  from the donor file and walk-header.txt (sha256 b0456227180a; internal record); RtSetShadow.v (sha256 f7c8737affff;
  internal record), byte for byte lib/A/Rt/RtSetShadow.v of this unit (git blob 621cfe869fd1); RtSSAudit.v (sha256
  3c9f2f6377a4; internal record), an audit file that is not part of the build; grant-SetShadow.v (sha256
  50fd0fe8abe7; internal record), the donor file at c3777b3715d0.
