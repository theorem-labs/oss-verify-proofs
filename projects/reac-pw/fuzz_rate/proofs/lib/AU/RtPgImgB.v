(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/leptonica/bilateral_fuzzer/lib/O2/O2Reloc.v, with its addresses changed; 147 of its 158 lines of code are new or changed and 285 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgImgA.v at 7379c28ff70f; the same record for
   image B (fuzz_rate.asan-ubsan), with every value re-measured on image B's own pinned bytes: the side-stack class,
   the seven cut pcs, the real frame's size, the seven cut lists, the frame's two shadow patterns, the three segments'
   write ranges, the checked real-frame range, the registered globals, the strings, the read-only cells and the four
   tables; check_csv's image-B stack bound is added. *)
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; symbols and the frame descriptor from the
   unstripped twin a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, whose loaded bytes differ only
   at the ELF header's section-table fields 0x10028 .. 0x1003e and the build-id note 0x102b8 .. 0x102cb, which no code
   reads): the record lib/A/RtPgCSpec.v's segment contracts rate_build_contract / rate_check_contract /
   rate_csv_contract read, filled with image B's values, each measured from the image's code and data.
   Statement data only: proves no function (kind: statement text).

   LLVMFuzzerTestOneInput 0x8076c (11756 bytes, 2939 instructions, one float instruction: `flw fa0` 0x82dbc). Its
   prologue takes a real frame of 544 bytes below the entry sp S (`addi sp,sp,-544` 0x8076c), keeps S in s0
   (0x807a8) and the 32-aligned base R = (S - 544) & -32 in s1 and sp (0x807ac, 0x807b0), saves ra, s0 .. s11 at
   [S - 0x68, S) (0x80774 .. 0x807a4) and loads K (the runtime's shadow offset) into s4 through the GOT cell 0x9c170
   (0x807c4, 0x807cc); the frame for locals F is a side-stack frame of class 4 (`li a0,704` 0x807d8,
   `jal __asan_stack_malloc_4` 0x807dc; s8 = its result, s9 = F, spilled to R+0x10 and R+0x60 at 0x80eac / 0x80ed0)
   holding t[96] at F+0x20, ch[24] at F+0xa0, r[4] at F+0xe0, e (104 bytes) at F+0xf0, e42 (104 bytes) at F+0x180,
   e62 (104 bytes) at F+0x210 and hz at F+0x2a0 (the frame descriptor string at 0x113f3), with s3 = (F >> 3) + K
   (0x80820, 0x8084c) and the 88 shadow bytes rate_B_shA written at 0x80850 .. 0x809b0 (0xf1 left guard, 0xf8 out of
   scope, 0xf2 middle guards, 0xf3 right guard). Image B keeps parts[4] and asked[0] / asked[1] on the real frame
   (R+0x198 .. R+0x1b7 and R+0x198 / R+0x19c, `sw` 0x82e30 / 0x82e34), not in the frame for locals. The cuts (the
   plain walk's RATE_BUILD / RATE_MALLOC2 / RATE_CHECK / RATE_CHECK_END / RATE_CSV / RATE_FREE):
   C1 0x80ae4 `bnez a0` after malloc(pp) (jal 0x80ae0, a0 = s5 = 19744 from 0x80ad4 / 0x80ad8);
   C2 0x82a2c `jal` malloc(pod) (a0 = len + (len == 0) from 0x82a24 / 0x82a28); C3 0x82a30 `beqz a0`;
   C4 0x82f9c `ld s4,0x18(s1)` after check_code(reac_rate_refuse_code(4), 4) returned (jal 0x82f98);
   C5 0x82fac `jal` malloc(buf) (a0 = buflen + (buflen == 0) from 0x82fa0 / 0x82fa4 / 0x82fa8); C6 0x82fb0 `beqz a0`;
   C7 0x82fec `mv a0,s5` after check_csv's return (jal 0x82fe8), before free(buf) 0x82ff0, free(pod) 0x82ff8 and
   free(pp) 0x83000. The live values at each cut are the ones every path reaching it sets and the code after it
   reads (measured from the listing and the ELF, with the instruction that sets each and the one that first reads
   it): the four header cells R+0x30 / R+0x38 / R+0x40 / R+0x48 hold b6 << 8 (0x82d68, `slli` 0x82d64), b5
   (0x828c8), b4 << 8 (0x82898, `slli` 0x82894) and b3 (0x82794), each 0 when the input is shorter (0x80a48 ..
   0x80a54, 0x80ac0 .. 0x80acc, 0x827a0); R+0x50 holds fl (0x809ec), R+0x148 the mask (0x80a24), R+0x168 pp
   (0x80aec), R+0x178 pod (0x82a9c), R+0x18 buflen (0x80ea8). The frame's shadow bytes at C2 and C3 are the
   prologue's again (every granule M01 brings into scope it puts back); at C4 .. C7 the granule 0x54 (hz, 0x82a60)
   is 0x04, and the epilogue resets it (0x83008). M01 writes the pp block, the frame objects [F+0x20, F+0x278),
   their shadow bytes [shF+4, shF+0x4f) and four runs of real-frame cells; M02 writes the pod block, hz, its shadow
   byte, asked[0], asked[1] and three runs of real-frame cells (pp's cell R+0x168 is not among them); M03 writes the
   buf block only, besides the side-stack frames its two callees take (class 1 for reac_rate_drivable_csv, class 2
   for check_csv), which are runtime-owned at its start. The real-frame bytes R+0x198 .. R+0x1a7 are the ones the
   code shadow-checks (pod_nearest 0x84100 .. 0x8410c at the out cell a0 = R+0x198 from 0x82dc0; 0x81668 .. 0x81674
   at parts[1] R+0x1a0). The globals are the 57 rows of asan_globals (0xa0a20, 0xe40 bytes; every odr_indicator is
   -1, no real ODR indicator); the strings are its 46 string rows (each a registered global of size length + 1);
   the cells are reac_rate_prop_parse's five doubles (image B tests two more bounds before its `fcvt.l.d`, `fld`
   0x84b64 and 0x84b74) and the 40 pointer cells of .data.rel.ro the code loads with `ld` (ent_build.vocab 0x9bdc0
   9, ent_headamp_key.odd_ch 0x9be40 14, ent_headamp_key.param 0x9bee0 8) together with the two code tables; the
   4-byte tables are closed_list 0x21520 (check_list, check_csv, and the harness's two inlined bit_of loops in M02
   at 0x82e78 / 0x82ec4) and reac_rate_drivable_csv.ordered 0x216a0, the 8-byte tables switch.table.check_code
   0x9bf40 (check_code) and reac_rate_refuse_code.codes 0x9bf80. The five .data.rel.ro tables are image A's at
   +0x300; every string address and every string's bytes are the same in the two images. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0f YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Rate RateCfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
Import ListNotations.
Local Open Scope Z_scope.

(* The frame's shadow bytes after the prologue (88 granules of the 704-byte frame), and at C4 .. C7, where hz
   (granule 0x54) is in scope. *)
Definition rate_B_shA : list Z :=
  [0xf1; 0xf1; 0xf1; 0xf1;
   0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8;
   0xf2; 0xf2; 0xf2; 0xf2;
   0xf8; 0xf8; 0xf8;
   0xf2; 0xf2; 0xf2; 0xf2; 0xf2;
   0xf8;
   0xf2;
   0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8;
   0xf2; 0xf2; 0xf2; 0xf2; 0xf2;
   0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8;
   0xf2; 0xf2; 0xf2; 0xf2; 0xf2;
   0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8;
   0xf2; 0xf2; 0xf2; 0xf2; 0xf2;
   0xf8;
   0xf3; 0xf3; 0xf3].
Definition rate_B_shB : list Z :=
  firstn 84 rate_B_shA ++ [0x04] ++ skipn 85 rate_B_shA.

(* The strings (address, text without the NUL): the 46 string globals of asan_globals. The comment on each row is
   the symbol name in image B's own table. *)
Definition rate_B_strs : list (Z * list Z) := [
  (0x20fa0, map (fun x : byte => bv_unsigned x) Rate.RATE_KEY) (* .str: "reac.cfg.rate" *);
  (0x20fc0, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 111; 108; 101]) (* .str.3: "reac.cfg.role" *);
  (0x20fe0, [114; 101; 97; 99; 46; 104; 101; 97; 100; 97; 109; 112; 46]) (* .str.4: "reac.headamp." *);
  (0x21000, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116; 101; 32]) (* .str.5: "reac.cfg.rate " *);
  (0x21020, [82; 69; 65; 67; 46; 99; 102; 103; 46; 114; 97; 116; 101]) (* .str.6: "REAC.cfg.rate" *);
  (0x21040, [115; 111; 109; 101; 46; 111; 116; 104; 101; 114; 46; 99; 111; 110; 116; 114; 111; 108]) (* .str.7: "some.other.control" *);
  (0x21080, [114; 101; 97; 99; 46; 104; 101; 97; 100; 97; 109; 112]) (* .str.8: "reac.headamp" *);
  (0x210a0, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 111; 108; 101; 46; 120]) (* .str.9: "reac.cfg.role.x" *);
  (0x210c0, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116]) (* .str.10: "reac.cfg.rat" *);
  (0x21200, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116; 101]) (* ent_build.s: "reac.cfg.rate" *);
  (0x21220, [45; 49]) (* .str.12: "-1" *);
  (0x21240, [43; 51]) (* .str.13: "+3" *);
  (0x21260, [32; 55]) (* .str.14: " 7" *);
  (0x21280, [48; 55]) (* .str.15: "07" *);
  (0x212a0, [57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57]) (* .str.16: "99999999999999999999" *);
  (0x212e0, []) (* .str.17: "" *);
  (0x21300, [120]) (* .str.18: "x" *);
  (0x21320, [51; 97]) (* .str.19: "3a" *);
  (0x21340, [45; 48]) (* .str.20: "-0" *);
  (0x21360, [9; 53]) (* .str.21: "	5" *);
  (0x21380, [52; 56]) (* .str.22: "48" *);
  (0x213a0, [52; 55]) (* .str.23: "47" *);
  (0x213c0, [48; 120; 49]) (* .str.24: "0x1" *);
  (0x213e0, [45; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57]) (* .str.25: "-99999999999999999999" *);
  (0x21420, [112; 104; 97; 110; 116; 111; 109]) (* .str.26: "phantom" *);
  (0x21440, [112; 97; 100]) (* .str.27: "pad" *);
  (0x21460, [115; 101; 110; 115]) (* .str.28: "sens" *);
  (0x21480, [80; 65; 68]) (* .str.29: "PAD" *);
  (0x214a0, [115; 101; 110; 115; 120]) (* .str.30: "sensx" *);
  (0x214c0, [112; 104; 97; 110; 116; 111; 109; 46; 120]) (* .str.31: "phantom.x" *);
  (0x214e0, [115; 101; 110; 115; 32]) (* .str.32: "sens " *);
  (0x21500, [46]) (* .str.33: "." *);
  (0x21540, rt_code_of_txt 1) (* .str.34: "not_closed" *);
  (0x21560, rt_code_of_txt 2) (* .str.35: "not_drivable" *);
  (0x21580, rt_code_of_txt 3) (* .str.36: "role_slave" *);
  (0x215a0, rt_code_of_txt 4) (* .str.37: "malformed" *);
  (0x215c0, rt_code_of_txt 0) (* .str.38: "none" *);
  (0x21600, rt_refuse_txt 0) (* .str: "none" *);
  (0x21620, rt_refuse_txt 1) (* .str.1: "not_closed" *);
  (0x21640, rt_refuse_txt 2) (* .str.2: "not_drivable" *);
  (0x21660, rt_refuse_txt 3) (* .str.3: "role_slave" *);
  (0x21680, rt_refuse_txt 4) (* .str.4: "malformed" *);
  (0x216c0, STR_FMT_SD) (* .str.5: "%s%d" *);
  (0x216e0, STR_COMMA) (* .str.6: "," *);
  (0x21700, STR_EMPTY) (* .str.7: "" *);
  (0x21720, map (fun x : byte => bv_unsigned x) Rate.RATE_KEY) (* .str.8: "reac.cfg.rate" *)
].
(* The 57 registered globals (address, size). The last five are image A's five .data.rel.ro tables at +0x300. *)
Definition rate_B_globs : list (Z * Z) := [
  (0x20fa0, 14); (0x20fc0, 14); (0x20fe0, 14); (0x21000, 15); (0x21020, 14); (0x21040, 19);
  (0x21080, 13); (0x210a0, 16); (0x210c0, 13); (0x210e0, 56); (0x21140, 84); (0x211c0, 16);
  (0x211e0, 16); (0x21200, 14); (0x21220, 3); (0x21240, 3); (0x21260, 3); (0x21280, 3);
  (0x212a0, 21); (0x212e0, 1); (0x21300, 2); (0x21320, 3); (0x21340, 3); (0x21360, 3);
  (0x21380, 3); (0x213a0, 3); (0x213c0, 4); (0x213e0, 22); (0x21420, 8); (0x21440, 4);
  (0x21460, 5); (0x21480, 4); (0x214a0, 6); (0x214c0, 10); (0x214e0, 6); (0x21500, 2);
  (0x21520, 12); (0x21540, 11); (0x21560, 13); (0x21580, 11); (0x215a0, 10); (0x215c0, 5);
  (0x21600, 5); (0x21620, 11); (0x21640, 13); (0x21660, 11); (0x21680, 10); (0x216a0, 12);
  (0x216c0, 5); (0x216e0, 2); (0x21700, 1); (0x21720, 14); (0x9bdc0, 72); (0x9be40, 112);
  (0x9bee0, 64); (0x9bf40, 32); (0x9bf80, 40)
].
(* The 8-byte read-only cells: reac_rate_prop_parse's five doubles (0.5 `fld` 0x84b30, -2^31 0x84b38, 2^31 0x84b50,
   and image B's two further bounds -(2^63 + 2048) 0x84b64 and 2^63 0x84b74, read on every path that reaches the
   conversion) and the pointer cells of .data.rel.ro (vocab 9, odd_ch 14, param 8, switch.table.check_code 4,
   reac_rate_refuse_code.codes 5). *)
Definition rate_B_cells : list (Z * Z) := [
  (0x10388, 0x3fe0000000000000); (0x103f0, 0xc1e0000000000000); (0x10338, 0x41e0000000000000);
  (0x10400, 0xc3e0000000000001); (0x10360, 0x43e0000000000000);
  (0x9bdc0, 0x20fa0); (0x9bdc8, 0x20fc0); (0x9bdd0, 0x20fe0); (0x9bdd8, 0x21000); (0x9bde0, 0x21020);
  (0x9bde8, 0x21040); (0x9bdf0, 0x21080); (0x9bdf8, 0x210a0); (0x9be00, 0x210c0);
  (0x9be40, 0x21220); (0x9be48, 0x21240); (0x9be50, 0x21260); (0x9be58, 0x21280);
  (0x9be60, 0x212a0); (0x9be68, 0x212e0); (0x9be70, 0x21300); (0x9be78, 0x21320);
  (0x9be80, 0x21340); (0x9be88, 0x21360); (0x9be90, 0x21380); (0x9be98, 0x213a0);
  (0x9bea0, 0x213c0); (0x9bea8, 0x213e0); (0x9bee0, 0x21420); (0x9bee8, 0x21440);
  (0x9bef0, 0x21460); (0x9bef8, 0x21480); (0x9bf00, 0x214a0); (0x9bf08, 0x212e0);
  (0x9bf10, 0x214c0); (0x9bf18, 0x214e0); (0x9bf40, 0x21540); (0x9bf48, 0x21560);
  (0x9bf50, 0x21580); (0x9bf58, 0x215a0); (0x9bf80, 0x21600); (0x9bf88, 0x21620);
  (0x9bf90, 0x21640); (0x9bf98, 0x21660); (0x9bfa0, 0x21680)
].
(* The tables read by instrumented loads. *)
Definition rate_B_i32 : list (Z * list Z) :=
  [(0x21520, RateCfg.closed_list); (0x216a0, RateCfg.closed_list)].
Definition rate_B_u64 : list (Z * list Z) :=
  [(0x9bf40, [0x21540; 0x21560; 0x21580; 0x215a0]); (0x9bf80, [0x21600; 0x21620; 0x21640; 0x21660; 0x21680])].

(* Register numbers: s0 = 8, s1 = 9, a0 = 10, s2 .. s11 = 18 .. 27. b4 and b6 are kept shifted left by 8. *)
Definition rate_B_L23_tl : list (rt_loc * rt_x) :=
  [(LReg 8, XS); (LReg 9, XR); (LReg 19, XShF); (LReg 20, XC SHADOW_OFF); (LReg 22, XLen);
   (LReg 24, XPp 0x4d18);
   (LCell XR 0x8, XPp 0x4008); (LCell XR 0x10, XF); (LCell XR 0x18, XBuflen);
   (LCell XR 0x30, XHb 6 8); (LCell XR 0x38, XHb 5 0); (LCell XR 0x40, XHb 4 8); (LCell XR 0x48, XHb 3 0);
   (LCell XR 0x50, XFl); (LCell XR 0x60, XF); (LCell XR 0xf8, XPpShr 0x4d14); (LCell XR 0x120, XC (-0x3ffd));
   (LCell XR 0x138, XPp 0x4d14); (LCell XR 0x148, XMask); (LCell XR 0x168, XPp 0)].
Definition rate_B_L23 (a0 : rt_x) : list (rt_loc * rt_x) := (LReg 10, a0) :: rate_B_L23_tl.
Definition rate_B_L56_tl : list (rt_loc * rt_x) :=
  [(LReg 8, XS); (LReg 9, XR); (LReg 19, XShF); (LReg 20, XBuflen); (LReg 22, XBl);
   (LCell XR 0x10, XF); (LCell XR 0x60, XF); (LCell XR 0x148, XMask); (LCell XR 0x168, XPp 0);
   (LCell XR 0x178, XPod)].
Definition rate_B_L56 (a0 : rt_x) : list (rt_loc * rt_x) := (LReg 10, a0) :: rate_B_L56_tl.

Definition rate_himg_B : rt_himg := {|
  hi_cid := 4;
  hi_c1 := 0x80ae4; hi_c2 := 0x82a2c; hi_c3 := 0x82a30; hi_c4 := 0x82f9c;
  hi_c5 := 0x82fac; hi_c6 := 0x82fb0; hi_c7 := 0x82fec;
  hi_rsz := 0x220;
  hi_L1 := [(LReg 10, XPp 0); (LReg 8, XS); (LReg 9, XR); (LReg 18, XSrc); (LReg 19, XShF);
            (LReg 20, XC SHADOW_OFF); (LReg 21, XC 19744); (LReg 22, XC 0x5000); (LReg 23, XLeft);
            (LReg 24, XF); (LReg 25, XF); (LReg 26, XBuflen);
            (LCell XR 0x30, XHb 6 8); (LCell XR 0x38, XHb 5 0); (LCell XR 0x40, XHb 4 8);
            (LCell XR 0x48, XHb 3 0); (LCell XR 0x50, XFl); (LCell XR 0x148, XMask)];
  hi_L2 := rate_B_L23 XLenNZ;
  hi_L3 := rate_B_L23 XPod;
  hi_L4 := [(LReg 8, XS); (LReg 9, XR); (LReg 19, XShF); (LCell XR 0x10, XF); (LCell XR 0x18, XBuflen);
            (LCell XR 0x60, XF); (LCell XR 0x148, XMask); (LCell XR 0x168, XPp 0); (LCell XR 0x178, XPod)];
  hi_L5 := rate_B_L56 XBl;
  hi_L6 := rate_B_L56 XBuf;
  hi_L7 := [(LReg 8, XS); (LReg 9, XR); (LReg 19, XShF); (LReg 21, XBuf); (LCell XR 0x10, XF);
            (LCell XR 0x60, XF); (LCell XR 0x168, XPp 0); (LCell XR 0x178, XPod)];
  hi_shA := rate_B_shA; hi_shB := rate_B_shB;
  hi_w1 := [(XF, 0x20, 0x258); (XShF, 4, 75); (XR, 0, 0x30); (XR, 0x58, 0xf0); (XR, 0x150, 0x30);
            (XR, 0x198, 0x20)];
  hi_w2 := [(XF, 0x2a0, 4); (XShF, 0x54, 1); (XR, 0x138, 0x10); (XR, 0x150, 0x18); (XR, 0x170, 0x10);
            (XR, 0x198, 8)];
  hi_w3 := [];
  hi_rz := [(0x198, 16)];
  hi_globs := rate_B_globs;
  hi_strs := rate_B_strs;
  hi_cells := rate_B_cells;
  hi_i32 := rate_B_i32;
  hi_u64 := rate_B_u64 |}.

(* check_csv's stack use in image B (`addi sp,sp,-192` 0x837c0, then `andi sp,sp,-32` 0x83800, and the bcmp
   wrapper's 2 ESTACK window, `jal` 0x83abc): the T at which image B's walks instantiate
   RtPgCSpec.rt_check_csv_specX. Image A's frame is 160 and its bound is stated in its own files. *)
Definition T_csv_STK_B : Z := 192 + 16 + 2 * ESTACK.

(* The frame's shadow has one byte per granule of the 704-byte frame, and the two patterns differ only at the
   granule M02 brings into scope. *)
Lemma rate_B_sh_len : length rate_B_shA = 88%nat /\ length rate_B_shB = 88%nat.
Proof. vm_compute. split; reflexivity. Qed.

(* The key literal the parse and the harness's strcmp read is Rate.RATE_KEY's text. *)
Lemma rate_B_key_text : map (fun x : byte => bv_unsigned x) Rate.RATE_KEY =
  [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116; 101].
Proof. vm_compute. reflexivity. Qed.

Print Assumptions rate_B_sh_len.
Print Assumptions rate_B_key_text.
