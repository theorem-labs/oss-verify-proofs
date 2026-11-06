(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/leptonica/bilateral_fuzzer/lib/O2/O2Reloc.v, with its module paths, module names and addresses changed; 131 of its 145 lines of code are new or changed and 282 lines of the source are left out. *)
(* reac-pw/fuzz_rate image A (fuzz_rate.asan, pinned sha256
   22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; symbols and the frame descriptor from the
   unstripped twin 0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3, whose loaded bytes differ only
   at the ELF header's section-table fields 0x10028 .. 0x1003e and the build-id note 0x102b8 .. 0x102cb, which no code
   reads): the record lib/A/RtPgCSpec.v's segment contracts rate_build_contract / rate_check_contract /
   rate_csv_contract read, filled with image A's values, each measured from the image's code and data.
   Statement data only: proves no function (kind: statement text).

   LLVMFuzzerTestOneInput 0x80714 (12156 bytes, 3039 instructions, one float instruction: `flw fa0` 0x82c78). Its
   prologue takes a real frame of 480 bytes below the entry sp S (`addi sp,sp,-480` 0x80714), keeps S in s0
   (0x80750) and the 32-aligned base R = (S - 480) & -32 in s1 and sp (0x80754, 0x80758), saves ra, s0 .. s11 at
   [S - 0x68, S) (0x8071c .. 0x8074c) and loads K (the runtime's shadow offset) into s2 through the GOT cell 0x9be70
   (0x80760 .. 0x80774); the frame for locals F is a side-stack frame of class 3 (`li a0,448` 0x80780,
   `jal __asan_stack_malloc_3` 0x80784; s8 = its result, s10 = F, spilled to R+0x18 and R+0x78 at 0x80d44 / 0x80d5c)
   holding t[96] at F+0x20, ch[24] at F+0xa0, r[4] at F+0xe0, e (104 bytes) at F+0xf0, hz at F+0x180, asked[0] at
   F+0x190 and asked[1] at F+0x1a0 (the frame descriptor string at 0x1d12e), with s4 = (F >> 3) + K (0x807c8,
   0x807f0) and the shadow bytes rate_A_shA written at 0x807f4 .. 0x808d8 (0xf1 left guard, 0xf8 out of scope,
   0xf2 middle guards, 0xf3 right guard). The cuts (the plain walk's RATE_BUILD / RATE_MALLOC2 / RATE_CHECK /
   RATE_CHECK_END / RATE_CSV / RATE_FREE):
   C1 0x809e0 `bnez a0` after malloc(pp) (jal 0x809dc, a0 = s5 = 19744 from 0x809d4 / 0x809d8);
   C2 0x828b4 `jal` malloc(pod) (a0 = len + (len == 0) from 0x828ac / 0x828b0); C3 0x828b8 `beqz a0`;
   C4 0x82e84 `ld s3,0x50(s1)` after check_code(reac_rate_refuse_code(4), 4) returned (jal 0x82e80);
   C5 0x82e94 `jal` malloc(buf) (a0 = buflen + (buflen == 0) from 0x82e8c / 0x82e90); C6 0x82e98 `beqz a0`;
   C7 0x82ed4 `mv a0,s5` after check_csv's return (jal 0x82ed0), before free(buf) 0x82ed8, free(pod) 0x82ee0 and
   free(pp) 0x82ee8. The live values at each cut are the ones every path reaching it sets and the code after it
   reads (measured from the listing and the ELF, with the instruction that sets each and the one that first reads
   it). The frame's shadow bytes at C2 and C3 are the prologue's again (every granule
   M01 brings into scope it puts back); at C4, C6 and C7 the granules 0x30 (hz, 0x828e4) and 0x32 / 0x34 (asked,
   0x82cc8 / 0x82ccc) are 0x04, and the epilogue resets them (0x82ef0 .. 0x82ef8). M01 writes the pp block, the
   frame objects [F+0x20, F+0x158), their shadow bytes and four runs of real-frame cells; M02 writes the pod block,
   hz, asked[0], asked[1], their three shadow bytes and three runs of real-frame cells; M03 writes the buf block
   only, besides the side-stack frames its two callees take (class 1 for reac_rate_drivable_csv, class 2 for
   check_csv), which are runtime-owned at its start. The real-frame cells R+0x158 and R+0x160 are the two the code
   shadow-checks (pod_nearest 0x83eb0 .. 0x83ebc; 0x8155c .. 0x81574). The globals are the 57 rows of asan_globals
   (0xa0720, 0xe40 bytes; every odr_indicator is -1); the strings are its 46 string rows (each a registered global
   of size length + 1); the cells are reac_rate_prop_parse's three doubles and the 31 pointer cells of .data.rel.ro
   the code loads with `ld` (ent_build.vocab 0x9bac0 9, ent_headamp_key.odd_ch 0x9bb40 14, ent_headamp_key.param
   0x9bbe0 8) together with the two code tables; the 4-byte tables are closed_list 0x21520 (check_list, check_csv,
   and the harness's two inlined bit_of loops in M02 at 0x82d5c / 0x82da8)
   and reac_rate_drivable_csv.ordered 0x216a0, the 8-byte tables switch.table.check_code 0x9bc40 (check_code) and
   reac_rate_refuse_code.codes 0x9bc80. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Rate RateCfg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
Import ListNotations.
Local Open Scope Z_scope.

(* The frame's shadow bytes after the prologue (56 granules of the 448-byte frame), and at C4 .. C7, where hz
   (granule 48) and asked[0] / asked[1] (50, 52) are in scope. *)
Definition rate_A_shA : list Z :=
  [0xf1; 0xf1; 0xf1; 0xf1;
   0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8;
   0xf2; 0xf2; 0xf2; 0xf2;
   0xf8; 0xf8; 0xf8;
   0xf2; 0xf2; 0xf2; 0xf2; 0xf2;
   0xf8;
   0xf2;
   0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8;
   0xf2; 0xf2; 0xf2; 0xf2; 0xf2;
   0xf8; 0xf2; 0xf8; 0xf2; 0xf8;
   0xf3; 0xf3; 0xf3].
Definition rate_A_shB : list Z :=
  firstn 48 rate_A_shA ++ [0x04; 0xf2; 0x04; 0xf2; 0x04] ++ skipn 53 rate_A_shA.

(* The strings (address, text without the NUL): the 46 string globals of asan_globals. *)
Definition rate_A_strs : list (Z * list Z) := [
  (0x20fa0, map (fun x : byte => bv_unsigned x) Rate.RATE_KEY) (* .str: "reac.cfg.rate" *);
  (0x20fc0, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 111; 108; 101]) (* .str.1: "reac.cfg.role" *);
  (0x20fe0, [114; 101; 97; 99; 46; 104; 101; 97; 100; 97; 109; 112; 46]) (* .str.2: "reac.headamp." *);
  (0x21000, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116; 101; 32]) (* .str.3: "reac.cfg.rate " *);
  (0x21020, [82; 69; 65; 67; 46; 99; 102; 103; 46; 114; 97; 116; 101]) (* .str.4: "REAC.cfg.rate" *);
  (0x21040, [115; 111; 109; 101; 46; 111; 116; 104; 101; 114; 46; 99; 111; 110; 116; 114; 111; 108]) (* .str.5: "some.other.control" *);
  (0x21080, [114; 101; 97; 99; 46; 104; 101; 97; 100; 97; 109; 112]) (* .str.6: "reac.headamp" *);
  (0x210a0, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 111; 108; 101; 46; 120]) (* .str.7: "reac.cfg.role.x" *);
  (0x210c0, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116]) (* .str.8: "reac.cfg.rat" *);
  (0x21200, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116; 101]) (* ent_build.s: "reac.cfg.rate" *);
  (0x21220, [45; 49]) (* .str.10: "-1" *);
  (0x21240, [43; 51]) (* .str.11: "+3" *);
  (0x21260, [32; 55]) (* .str.12: " 7" *);
  (0x21280, [48; 55]) (* .str.13: "07" *);
  (0x212a0, [57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57]) (* .str.14: "99999999999999999999" *);
  (0x212e0, []) (* .str.15: "" *);
  (0x21300, [120]) (* .str.16: "x" *);
  (0x21320, [51; 97]) (* .str.17: "3a" *);
  (0x21340, [45; 48]) (* .str.18: "-0" *);
  (0x21360, [9; 53]) (* .str.19: "	5" *);
  (0x21380, [52; 56]) (* .str.20: "48" *);
  (0x213a0, [52; 55]) (* .str.21: "47" *);
  (0x213c0, [48; 120; 49]) (* .str.22: "0x1" *);
  (0x213e0, [45; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57]) (* .str.23: "-99999999999999999999" *);
  (0x21420, [112; 104; 97; 110; 116; 111; 109]) (* .str.24: "phantom" *);
  (0x21440, [112; 97; 100]) (* .str.25: "pad" *);
  (0x21460, [115; 101; 110; 115]) (* .str.26: "sens" *);
  (0x21480, [80; 65; 68]) (* .str.27: "PAD" *);
  (0x214a0, [115; 101; 110; 115; 120]) (* .str.28: "sensx" *);
  (0x214c0, [112; 104; 97; 110; 116; 111; 109; 46; 120]) (* .str.29: "phantom.x" *);
  (0x214e0, [115; 101; 110; 115; 32]) (* .str.30: "sens " *);
  (0x21500, [46]) (* .str.31: "." *);
  (0x21540, rt_code_of_txt 1) (* .str.32: "not_closed" *);
  (0x21560, rt_code_of_txt 2) (* .str.33: "not_drivable" *);
  (0x21580, rt_code_of_txt 3) (* .str.34: "role_slave" *);
  (0x215a0, rt_code_of_txt 4) (* .str.35: "malformed" *);
  (0x215c0, rt_code_of_txt 0) (* .str.36: "none" *);
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
(* The 57 registered globals (address, size). *)
Definition rate_A_globs : list (Z * Z) := [
  (0x20fa0, 14); (0x20fc0, 14); (0x20fe0, 14); (0x21000, 15); (0x21020, 14); (0x21040, 19);
  (0x21080, 13); (0x210a0, 16); (0x210c0, 13); (0x210e0, 56); (0x21140, 84); (0x211c0, 16);
  (0x211e0, 16); (0x21200, 14); (0x21220, 3); (0x21240, 3); (0x21260, 3); (0x21280, 3);
  (0x212a0, 21); (0x212e0, 1); (0x21300, 2); (0x21320, 3); (0x21340, 3); (0x21360, 3);
  (0x21380, 3); (0x213a0, 3); (0x213c0, 4); (0x213e0, 22); (0x21420, 8); (0x21440, 4);
  (0x21460, 5); (0x21480, 4); (0x214a0, 6); (0x214c0, 10); (0x214e0, 6); (0x21500, 2);
  (0x21520, 12); (0x21540, 11); (0x21560, 13); (0x21580, 11); (0x215a0, 10); (0x215c0, 5);
  (0x21600, 5); (0x21620, 11); (0x21640, 13); (0x21660, 11); (0x21680, 10); (0x216a0, 12);
  (0x216c0, 5); (0x216e0, 2); (0x21700, 1); (0x21720, 14); (0x9bac0, 72); (0x9bb40, 112);
  (0x9bbe0, 64); (0x9bc40, 32); (0x9bc80, 40)
].
(* The 8-byte read-only cells: reac_rate_prop_parse's three doubles (0.5, -2^31, 2^31) and the pointer cells of
   .data.rel.ro (vocab 9, odd_ch 14, param 8, switch.table.check_code 4, reac_rate_refuse_code.codes 5). *)
Definition rate_A_cells : list (Z * Z) := [
  (0x10380, 0x3fe0000000000000); (0x103e8, 0xc1e0000000000000); (0x10338, 0x41e0000000000000); (0x9bac0, 0x20fa0);
  (0x9bac8, 0x20fc0); (0x9bad0, 0x20fe0); (0x9bad8, 0x21000); (0x9bae0, 0x21020);
  (0x9bae8, 0x21040); (0x9baf0, 0x21080); (0x9baf8, 0x210a0); (0x9bb00, 0x210c0);
  (0x9bb40, 0x21220); (0x9bb48, 0x21240); (0x9bb50, 0x21260); (0x9bb58, 0x21280);
  (0x9bb60, 0x212a0); (0x9bb68, 0x212e0); (0x9bb70, 0x21300); (0x9bb78, 0x21320);
  (0x9bb80, 0x21340); (0x9bb88, 0x21360); (0x9bb90, 0x21380); (0x9bb98, 0x213a0);
  (0x9bba0, 0x213c0); (0x9bba8, 0x213e0); (0x9bbe0, 0x21420); (0x9bbe8, 0x21440);
  (0x9bbf0, 0x21460); (0x9bbf8, 0x21480); (0x9bc00, 0x214a0); (0x9bc08, 0x212e0);
  (0x9bc10, 0x214c0); (0x9bc18, 0x214e0); (0x9bc40, 0x21540); (0x9bc48, 0x21560);
  (0x9bc50, 0x21580); (0x9bc58, 0x215a0); (0x9bc80, 0x21600); (0x9bc88, 0x21620);
  (0x9bc90, 0x21640); (0x9bc98, 0x21660); (0x9bca0, 0x21680)
].
(* The tables read by instrumented loads. *)
Definition rate_A_i32 : list (Z * list Z) :=
  [(0x21520, RateCfg.closed_list); (0x216a0, RateCfg.closed_list)].
Definition rate_A_u64 : list (Z * list Z) :=
  [(0x9bc40, [0x21540; 0x21560; 0x21580; 0x215a0]); (0x9bc80, [0x21600; 0x21620; 0x21640; 0x21660; 0x21680])].

(* Register numbers: s0 = 8, s1 = 9, a0 = 10, s2 .. s11 = 18 .. 27. b4 and b6 are kept shifted left by 8. *)
Definition rate_A_L23_tl : list (rt_loc * rt_x) :=
  [(LReg 8, XS); (LReg 9, XR); (LReg 18, XC SHADOW_OFF); (LReg 20, XShF); (LReg 23, XPp 0x4000);
   (LReg 25, XPp 0x4d18); (LReg 26, XLen); (LReg 27, XPp 0);
   (LCell XR 0x18, XF); (LCell XR 0x20, XHb 3 0); (LCell XR 0x38, XHb 6 8); (LCell XR 0x40, XHb 5 0);
   (LCell XR 0x48, XHb 4 8); (LCell XR 0x50, XBuflen); (LCell XR 0x58, XFl); (LCell XR 0x78, XF);
   (LCell XR 0xa8, XPpShr 0x4d14); (LCell XR 0xb8, XPp 0x4d14); (LCell XR 0xc0, XPp 0); (LCell XR 0x120, XMask)].
Definition rate_A_L23 (a0 : rt_x) : list (rt_loc * rt_x) := (LReg 10, a0) :: rate_A_L23_tl.
Definition rate_A_L56_tl : list (rt_loc * rt_x) :=
  [(LReg 8, XS); (LReg 9, XR); (LReg 19, XBuflen); (LReg 20, XShF); (LReg 23, XBl);
   (LCell XR 0x18, XF); (LCell XR 0x78, XF); (LCell XR 0xc0, XPp 0); (LCell XR 0x120, XMask);
   (LCell XR 0x138, XPod)].
Definition rate_A_L56 (a0 : rt_x) : list (rt_loc * rt_x) := (LReg 10, a0) :: rate_A_L56_tl.

Definition rate_himg_A : rt_himg := {|
  hi_cid := 3;
  hi_c1 := 0x809e0; hi_c2 := 0x828b4; hi_c3 := 0x828b8; hi_c4 := 0x82e84;
  hi_c5 := 0x82e94; hi_c6 := 0x82e98; hi_c7 := 0x82ed4;
  hi_rsz := 0x1e0;
  hi_L1 := [(LReg 10, XPp 0); (LReg 8, XS); (LReg 9, XR); (LReg 18, XC SHADOW_OFF); (LReg 19, XC 0x5000);
            (LReg 20, XShF); (LReg 21, XC 19744); (LReg 22, XLeft); (LReg 23, XHb 3 0); (LReg 24, XF);
            (LReg 25, XSrc); (LReg 26, XF);
            (LCell XR 0x38, XHb 6 8); (LCell XR 0x40, XHb 5 0); (LCell XR 0x48, XHb 4 8);
            (LCell XR 0x50, XBuflen); (LCell XR 0x58, XFl); (LCell XR 0x120, XMask)];
  hi_L2 := rate_A_L23 XLenNZ;
  hi_L3 := rate_A_L23 XPod;
  hi_L4 := [(LReg 8, XS); (LReg 9, XR); (LReg 20, XShF); (LCell XR 0x18, XF); (LCell XR 0x50, XBuflen);
            (LCell XR 0x78, XF); (LCell XR 0xc0, XPp 0); (LCell XR 0x120, XMask); (LCell XR 0x138, XPod)];
  hi_L5 := rate_A_L56 XBl;
  hi_L6 := rate_A_L56 XBuf;
  hi_L7 := [(LReg 8, XS); (LReg 9, XR); (LReg 20, XShF); (LReg 21, XBuf); (LCell XR 0x18, XF);
            (LCell XR 0x78, XF); (LCell XR 0xc0, XPp 0); (LCell XR 0x138, XPod)];
  hi_shA := rate_A_shA; hi_shB := rate_A_shB;
  hi_w1 := [(XF, 0x20, 0x138); (XShF, 4, 39); (XR, 0x10, 0x28); (XR, 0x60, 0xc0); (XR, 0x128, 0x18);
            (XR, 0x158, 0x20)];
  hi_w2 := [(XF, 0x180, 4); (XF, 0x190, 4); (XF, 0x1a0, 4); (XShF, 0x30, 1); (XShF, 0x32, 1); (XShF, 0x34, 1);
            (XR, 0x110, 0x10); (XR, 0x128, 0x18); (XR, 0x158, 8)];
  hi_w3 := [];
  hi_rz := [(0x158, 16)];
  hi_globs := rate_A_globs;
  hi_strs := rate_A_strs;
  hi_cells := rate_A_cells;
  hi_i32 := rate_A_i32;
  hi_u64 := rate_A_u64 |}.

(* The frame's shadow has one byte per granule of the 448-byte frame, and the two patterns differ only at the three
   granules M02 brings into scope. *)
Lemma rate_A_sh_len : length rate_A_shA = 56%nat /\ length rate_A_shB = 56%nat.
Proof. vm_compute. split; reflexivity. Qed.

(* The key literal the parse and the harness's strcmp read is Rate.RATE_KEY's text. *)
Lemma rate_A_key_text : map (fun x : byte => bv_unsigned x) Rate.RATE_KEY =
  [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116; 101].
Proof. vm_compute. reflexivity. Qed.