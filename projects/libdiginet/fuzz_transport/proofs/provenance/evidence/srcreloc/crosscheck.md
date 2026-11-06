# Hand cross-check of the moved numerals (relocate.py)

Sample: `sample20.tsv` (20 rows of `values.tsv`, every n-th distinct (file, old value) row, chosen by the script), plus
the codec rows that the sample does not reach (the call to strcmp, the strcmp walk's pcs, the two announce-name
strings, the RELRO block). The check does not use relocate.py's code: a separate Python script read the unstripped
twins with pyelftools (`.symtab` and the PT_LOAD bytes) and, for each row, compared:

1. the symbol S named in the row: donor address dv and size dz, fuzz_transport address tv and size tz; the row passes
   only if `new - tv == old - dv`, `0 <= old - dv < dz` and `dz == tz`;
2. the 4 bytes at `old` in the donor image and the 4 bytes at `new` in fuzz_transport's image: they must be equal (the
   instruction or data the numeral names is the same); for a string row, the NUL-terminated bytes at both;
3. the line of the relocated file, read again, to show what the numeral names there.

ELFs: the donor twins of `src-equality-v2.md` (fuzz_frame plain d28c8cc658e4, ubsan a32c718f58f7; fuzz_codec plain
fc6379b62efe, ubsan c0987f7c0263) and fuzz_transport's unstripped twins of the pinned builds (port commit 835f336c +
c47f6290: plain c2d42d895415, ubsan c53d4b20cfc1); relocate.py step S0 checks every sha256 on each run.

Checked again on 2026-10-30 for the sample of the run at those pins: 14 of the 20 rows have a new value (all ubsan:
the functions moved -0x1c), the other 6 keep theirs; every row is re-measured below.

## The 20 sampled rows

| file:line | old | new | symbol | donor S / size | transport S / size | offset kept | word at old = word at new | the line |
|---|---|---|---|---|---|---|---|---|
| Prog/codec_cells.v:61 | 0x1f3f8 | 0x21420 | personalities | 0x1f3f8 / 48 | 0x21420 / 48 | yes | 01000000 = 01000000 | `Definition PERS : Z := 0x21420.` |
| Prog/diginet_body_check.v:481 | 0x13b84 | 0x17c38 | diginet_body_check | 0x13b84 / 268 | 0x17c38 / 268 | yes | 130101f7 = 130101f7 | `F (Z_to_bv 64 0x17c38) fc None m0 (seg_rom rsegs))).` |
| Prog/diginet_frame_build.v:583 | 0x13990 | 0x179bc | diginet_frame_build | 0x138ac / 516 | 0x178d8 / 516 | yes | 13050000 = 13050000 | `(* 0x179bc .. 0x179e0: EtherType and numbytes *)` |
| Prog/diginet_frame_build_w_c.v:8 | 0x13908 | 0x17934 | diginet_frame_build | 0x138ac / 516 | 0x178d8 / 516 | yes | 63681517 = 63681517 | `as the calling convention gives an int argument. The binary tests bltu 1, a7 at 0x17934:` |
| Prog/diginet_frame_parse.v:452 | 0x1384c | 0x17878 | diginet_frame_parse | 0x136f0 / 444 | 0x1771c / 444 | yes | 13060000 = 13060000 | `(* 0x17878: the sum of the body *)` |
| U/Prog/codec_img.v:163 | 0x103a1 | 0x10339 | (.rodata string, rule (c)) | 'CNTRL\|24' at 0x103a1 | 'CNTRL\|24' at 0x10339 | string equal | occurs 1x in transport .rodata | `... 8 0x00; Z_to_bv 8 0x00]; C8 (Z_to_bv 64 0x10339); C1 (Z_to_bv 8 0x01); ...` |
| U/Prog/diginet_announce_parse.v:10 | 0x13f2c | 0x18548 | diginet_announce_parse | 0x13f04 / 192 | 0x18520 / 192 | yes | 631a0508 = 631a0508 | `UBSan branches to the trap at 0x185dc, not taken: 0x18548 (f & 7) and 0x1857c (ap & 7) by` |
| U/Prog/diginet_body_check.v:17 | 0x140ac | 0x18750 | diginet_body_check | 0x14028 / 328 | 0x186cc / 328 | yes | 6300050c = 6300050c | `The seven branches to the trap at 0x18810 are never taken: at 0x18750 and 0x1875c the` |
| U/Prog/diginet_body_check_w.v:78 | 0x14028 | 0x186cc | diginet_body_check | 0x14028 / 328 | 0x186cc / 328 | yes | 130101f7 = 130101f7 | `(* 0x186cc .. 0x18704: the frame, the saved regist ...` |
| U/Prog/diginet_body_check_w_c.v:16 | 0x1416c | 0x18810 | diginet_body_check | 0x14028 / 328 | 0x186cc / 328 | yes | 731000c0 = 731000c0 | `The seven trap branches to 0x18810 are not on this path: 0x18750 and 0x1875c follow an` |
| U/Prog/diginet_frame_build.v:483 | 0x13cbc | 0x182d8 | diginet_frame_build | 0x13c44 / 704 | 0x18260 / 704 | yes | 63661521 = 63661521 | `(* 0x182d0 .. 0x182d8: mode > DIGINET_SUM_ZERO *)` |
| U/Prog/diginet_frame_build.v:646 | 0x13e84 | 0x184a0 | diginet_frame_build | 0x13c44 / 704 | 0x18260 / 704 | yes | a38ea400 = a38ea400 | `(* 0x1848c .. 0x184a0: cmd and num_commands *)` |
| U/Prog/diginet_frame_build_c.v:43 | 0x13e2c | 0x18448 | diginet_frame_build | 0x13c44 / 704 | 0x18260 / 704 | yes | 63eab60c = 63eab60c | `0x18414, 0x18420, 0x18438, 0x18448, 0x18458, 0x18464, 0x1847c, 0x18488, 0x18498, 0x184ac:` |
| U/Prog/diginet_frame_build_w.v:253 | 0x13d20 | 0x1833c | diginet_frame_build | 0x13c44 / 704 | 0x18260 / 704 | yes | 13856400 = 13856400 | `(* 0x1833c: memcpy (out + 6, src, 6) *)` |
| U/Prog/diginet_frame_build_w_c.v:19 | 0x13cbc | 0x182d8 | diginet_frame_build | 0x13c44 / 704 | 0x18260 / 704 | yes | 63661521 = 63661521 | `body_len != 0 && body == 0 (0x182c0 .. 0x182cc), then the mode at 0x182d8 (bltu 1, a7: a7` |
| U/Prog/diginet_frame_parse.v:372 | 0x13a98 | 0x180b4 | diginet_frame_parse | 0x13a18 / 488 | 0x18034 / 488 | yes | 6302aa16 = 6302aa16 | `(* 0x180a8, 0x180b4: buf + 14, h + 1 *)` |
| U/Prog/diginet_frame_parse_c.v:32 | 0x13b58 | 0x18174 | diginet_frame_parse | 0x13a18 / 488 | 0x18034 / 488 | yes | 6302a90a = 6302a90a | `0x1816c, 0x18174, 0x18190, 0x181a0: the pointer-overflow checks of buf + 12 .. buf + 29` |
| U/Prog/diginet_msg_next.v:336 | 0x14318 | 0x189bc | diginet_msg_next | 0x141a0 / 480 | 0x18844 / 480 | yes | 2380f500 = 2380f500 | `evt rsegs Q (ST 0x189bc (Z_to_bv 64 v5) x6 x7 (Z_to_bv 64 c) (Z ...` |
| U/Prog/diginet_msg_next_w_c.v:12 | 0x141a4 | 0x18848 | diginet_msg_next | 0x141a0 / 480 | 0x18844 / 480 | yes | 6308051c = 6308051c | `against 0 (0x18848, 0x1884c), then c & 7 at 0x18854 (a branch to the trap at 0x18a20; the` |
| U/Prog/diginet_sum16.v:121 | 0x13950 | 0x17f6c | diginet_sum16 | 0x13944 / 80 | 0x17f60 / 80 | yes | 13070500 = 13070500 | `(* 0x17f68 snez a3, a0; 0x17f6c mv a4, a0; 0x17f70 mv a5, a0. *)` |

20 of 20 pass. Four words decoded by hand agree with the comment beside them: `0x0c050063` is `beq a0, zero, +0xc0`
(beqz to the trap 0x18810, U/Prog/diginet_body_check.v:17), `0xc0001073` is `csrrw zero, cycle, zero` (the canonical
unimp at the trap, U/Prog/diginet_body_check_w_c.v:16), `0x00050713` is `addi a4, a0, 0` (mv a4, a0,
U/Prog/diginet_sum16.v:121), `0x08051a63` is `bne a0, zero, +0x94` (bnez to the trap 0x185dc, U/Prog/diginet_announce_parse.v:10).

## The codec rows outside the sample

| what | donor | fuzz_transport | check |
|---|---|---|---|
| the call to strcmp in diginet_personality_from_name, plain (`calls strcmp at`, Prog/diginet_personality_from_name_c.v) | 0x15284: jal ra, +35392 -> 0x1dcc4 = strcmp | 0x17bf8: jal ra, +33300 -> 0x1fe0c = strcmp | both decode to a jal to the image's strcmp |
| the same, ubsan | 0x15638: jal ra -> 0x1e14c = strcmp | 0x1868c: jal ra, +33456 -> 0x2093c = strcmp | the same |
| strcmp walk pcs, plain (Prog/strcmp.v, ST ...) | 0x1dcf4, 0x1dcdc, 0x1dcc4 | 0x1fe3c, 0x1fe24, 0x1fe0c | strcmp + 0x30 / 0x18 / 0; the words at old and new are equal (strcmp's 56 bytes are byte-equal, S1) |
| strcmp walk pcs, ubsan (U/Prog/strcmp.v) | 0x1e17c, 0x1e164, 0x1e14c | 0x2096c, 0x20954, 0x2093c | the same (strcmp at 0x2093c, 56 bytes equal to the donor's) |
| CODEC_STR_C24 (rule (c), both builds) | 0x103a1 | 0x10339 | the bytes at 0x10339 are `CNTRL\|24\0` in both transport images, and 0x10339 is the name pointer at personalities + 8 (and at SPEC_C24 + 0) |
| CODEC_STR_PC (rule (c), both builds) | 0x10381 | 0x10330 | the bytes at 0x10330 are `MAINUNIT\0`; 0x10330 is the pointer at personalities + 32 (and at SPEC_PC + 0) |
| RELRO_BASE / codec_relro_base (rule (d)) | plain 0x1f1f0, ubsan 0x1f678 (.data.rel.ro start) | plain 0x213c8, ubsan 0x21ef8 | the .data.rel.ro section header of each transport twin; equal to Prog/T/TContract.v and U/Prog/T/TContract.v RELRO_BASE |
| RELRO_LEN / the codec_pers_at premise (rule (d)) | 568 (the block up to the end of personalities[]) | plain 152 (0x98), ubsan 216 (0xd8) | the .data.rel.ro size; equal to TContract.v RELRO_LEN; personalities (plain 0x21420, ubsan 0x21f90, 48 bytes) lies inside |
