(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/Bz/B0Traps.v, with its numbers changed; 131 of its 139 lines of code are new or changed and 155 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgImgA.v at dd9ff534326; the same record
   filled with image B's values (fuzz_headamp.asan-ubsan), each measured on image B, none copied from image A. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; symbols from the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are byte-equal to the
   pin's except .note.gnu.build-id; every byte below is read from the pin): the record lib/A/HPgCSpec.v's five segment
   contracts read, filled with image B's values, each measured from the image's code and data. Statement data
   only: proves no function (kind: statement text).

   LLVMFuzzerTestOneInput 0x80c40 (12860 bytes, 3215 instructions). Its prologue takes a real frame of 0x220 bytes
   below the entry sp S (`addi sp,sp,-0x220` 0x80c40), saves ra, s0 .. s11 and fs0 .. fs3 at [S - 0x88, S)
   (0x80c48 .. 0x80c88), keeps S in s0 (0x80c8c) and the 32-aligned base R = sp & -32 in sp and s1 (0x80c90,
   0x80c94), and loads K (the runtime's shadow offset, the word at 0xa5238) into s11 through the GOT word 0x9c7f0
   (0x80ca8, 0x80cb0). The frame for locals F is a side-stack frame of class 4: the 4-byte option word 0xa5240 is read
   through the GOT word 0x9c848 (0x80ca4, 0x80cac) and, when it is nonzero, `addi a0,zero,0x3a0` + the class-4
   call at 0x80cbc / 0x80cc0 give F in s7 and s5 (0x80cc4, 0x80cd0; the real-stack arm 0x80cd8 .. 0x80cf0 is the
   other arm of that test); R + 0x170 := F (0x80cf4) and s3 = (F >> 3) + K (0x80d04, 0x80d30). The frame
   description at 0x1b958 lists eight objects: t[96] at F+0x20, ch[24] at F+0xa0, r[4] at F+0xe0, three e objects
   (104 bytes each, one per inlined builder scope) at F+0xf0, F+0x180 and F+0x210, res (12 bytes) at F+0x2a0 and x
   (struct expect, 136 bytes) at F+0x2c0; the prologue writes the 116 shadow bytes headamp_B_shA with the 116
   stores 0x80d34 .. 0x80f04 (0xf1 left guard, 0xf8 object out of scope, 0xf2 middle guards, 0xf3 right guard; the
   values constant-propagated from the `addi` before them). hd_seg_pre takes F as the side-stack frame the harness
   holds: the arm the option word and the class-4 call's nonzero result select (on the real-stack arm s7 = 0).

   The cuts (the plain walk's ENTRY, K13090, K140e4, K14118, K147e0, K1482c, RET at image B's addresses, with the
   allocator calls split out): C1 0x80fcc `bnez a0` after malloc(pp) (jal 0x80fc8, a0 = 19744 from 0x80fc0 ..
   0x80fc4); C2 0x82efc `jal` malloc(pod) (a0 = len + (len == 0) from 0x82ef4 .. 0x82ef8); C3 0x82f00 `beqz a0`;
   C4 0x82f34 `jal` malloc(out) (a0 = 3 cap + 3 from 0x82f24 .. 0x82f30); C5 0x82f38 `beqz a0`; C6 0x83900 `jal`
   malloc(first) (a0 = 3 max(rc, 0) + (it == 0) from 0x838e4 .. 0x838fc); C7 0x83904 `beqz a0`; C8 0x83920 after
   the __asan_memcpy that fills first (jal 0x8391c, skipped by 0x8390c when the size is 0); C9 0x83950 `mv a0,s7`
   after check_plain's return (jal 0x8394c), before the free(first) jal 0x83954. The live values at each cut are the
   ones every path reaching it sets and the code after it reads (measured by backward liveness and reaching
   definitions over the non-error blocks of the function's CFG, the jump table at 0x81948 with its nine targets):
   C1: a0 = pp (0x80fc8), s0 = S, s1 = R, s2 = the input cursor (0x80cb4 / 0x80f5c / 0x80fa0), s3 = (F >> 3) + K,
   s4 = 19744 (0x80fc0), s5 = 0x5000 (0x80fbc), s6 = the bytes left after the two harness bytes (0x80f54 /
   0x80f64 / 0x80f9c), s7 = F (0x80cc4), s8 = cap (0x80f58 / 0x80f68 / 0x80fb8), s11 = K, R+0x38 = 1 - the null flag
   (0x80f4c: seqz of the first input byte's bit 0; 0x80f70: 1 on the empty input), R+0x48 = F (0x80f10);
   C2 and C3: a0 = len + (len == 0) / pod, s2 = pp (0x82c14, from R+0x148), s3, s5 = len (0x82cb8 / 0x82ef0, the
   word at pp+0x4000 through R+0x138), s8 = pp+0x4d18 (0x82c70 .. 0x82c74), s11 = K, R+0x8 = pp+0x4008 (0x813b0),
   R+0x18 = F (0x81388), R+0x20 = cap (0x81384), R+0x38, R+0x48, R+0xe0 = (pp+0x4d14) >> 3 (0x813a4),
   R+0x108 = -16381 (0x810b4), R+0x120 = pp+0x4d14 (0x8139c), R+0x148 = pp (0x813a8);
   C4 and C5: a0 = 3 cap + 3 / out, s2 = 3 cap (0x82f28), s3, s4 = cap (0x82f08, `lbu` of R+0x20), s5 = 3 cap + 3
   (0x82f2c), s7 = 1 - the null flag (0x82f0c, from R+0x38), s8, s9 = pod (0x82f04), s11 = K, and the cells of C2
   but R+0x20 and R+0x38;
   C6 and C7: a0 = 3 max(rc, 0) + (it == 0) / first, s3, s4 = cap, s5 = F (0x82f44 / 0x83858, from R+0x48),
   s6 = out (0x82f3c), s9 = rc (0x82f9c), s10 = 3 max(rc, 0) (0x838f4), R+0x18 = F, R+0x140 = the parse's first
   argument (0x82f80: neg(1 - null) & pod, i.e. pod when the null flag is 0, else 0), R+0x148 = pp, R+0x150 =
   3 cap + 3 (0x82f50), R+0x158 = pod (0x82f78);
   C8: s3, s4, s5, s6, s7 = first (0x83908), s9, and the five cells of C6;
   C9: s3, s5 = F, s6 = out, s7 = first, R+0x18 = F, R+0x148 = pp, R+0x158 = pod;
   and at every cut s0 = S and s1 = R.
   The frame's shadow bytes at C2 .. C5 are the prologue's again (M01's 138 shadow stores bring granules 0x04 ..
   0x4e into scope with 0, r's partial granule 0x1c with 0x04 at 0x81a24, and put them back with 0xf8); at C6 .. C9
   the two res granules 0x54 and 0x55 are 0x00 and 0x04 (0x82f5c, 0x82f60) and the seventeen x granules 0x58 ..
   0x68, which the non-corrupt path brings into scope at 0x82fe0 .. 0x83020, are back at 0xf8 (0x838a0 .. 0x838e0;
   the corrupt path jumps from 0x82fd8 to 0x838e4 with them never in scope); the epilogue puts the res granules
   back at 0x83974 .. 0x83978.
   M01 writes the pp block, the frame objects [F+0x20, F+0x278), their shadow bytes and the real-frame cells
   [R, R+0x198) (its 45 s1-relative store offsets run 0x8 .. 0x190); M02 writes the pod block only; M03 writes the
   out block, res and x [F+0x2a0, F+0x348), their shadow granules [0x54, 0x69), the real-frame cells [R, R+0x160)
   (its 25 s1-relative store offsets run 0x88 .. 0x158) and the errno cell; M04a writes the first block only;
   M04b writes the out block and the errno cell. One instrumented check of this function reads the shadow of a
   real-frame cell: the 8-byte store of parts[1] at R+0x180 (pod.h:253, the store at 0x81b7c; parts[0 .. 3] are
   R+0x178 .. R+0x197) is checked at 0x81b58 .. 0x81b6c (`addi a2,s1,0x180; srli a2,a2,3; add a2,a2,s11;
   lbu a2,0(a2); beqz a2,+8; j 0x83c0c`); it is the only shadow load of the function whose address comes from s1,
   so the checked real-frame range list is [(0x180, 8)].
   The globals are the 43 rows of asan_globals (its own section at 0xa10a0, 0xac0 bytes; no descriptor has an ODR
   indicator). The strings are the 36 the harness, the parse and their callees read: the nine of ent_build.vocab,
   the fourteen of ent_headamp_key.odd_ch, the eight of ent_headamp_key.param (one of them, the empty string at
   0x21240, is also an odd_ch entry), ent_build.s at 0x21160, the dot at 0x21460, the harness's own
   "reac.headamp." at 0x20f40 (its strncmp literal, 0x83288, also vocab[2]) and the parse's four literals at
   0x214a0, 0x214c0, 0x214e0, 0x21500. The cells are the parse's four doubles (0.5 at 0x10380, 256.0 at 0x10340,
   the two float-cast bounds 0xc3e0000000000001 at 0x103f0 and 2^63 at 0x10358: fld 0x850b4, 0x850cc, 0x850dc,
   0x850ec), the harness's three division constants (0x10310 at 0x824a8, 0x10318 at 0x81cf8 and 0x8231c, 0x10408
   at 0x81860) and the 31 pointer cells of .data.rel.ro that the harness loads with `ld`, each after its shadow check
   (vocab 0x9c4e0 + 8 i for i < 9 at 0x8212c, odd_ch 0x9c560 + 8 k for k < 14 at 0x82368, param 0x9c600 + 8 k for
   k < 8 at 0x81b68), each the address of one of the strings above. The 8-byte constants the runtime's wrappers,
   musl and the allocator read inside their own code (e.g. 0x103f8 in the strtol wrapper at 0x47b1c, 0x10330 in
   __intscan at 0x94eb4) are not listed: hd_seg_pre's rom_view and arodata_okP give every read-only byte.
   The stack-guard cells musl's strtol reads through the strtol wrapper: the GOT word 0x9d478 (read at 0x9579c
   inside musl's __strtol_internal 0x95770) and the guard object __stack_chk_guard 0x5f8210, whose word it holds. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
Import ListNotations.
Local Open Scope Z_scope.

(* The frame's shadow bytes after the prologue (116 granules of the 0x3a0-byte request), and from C6 on. *)
Definition headamp_B_shA : list Z :=
  [241; 241; 241; 241; 248; 248; 248; 248; 248; 248; 248; 248; 248; 248; 248; 248;
   242; 242; 242; 242; 248; 248; 248; 242; 242; 242; 242; 242; 248; 242; 248; 248;
   248; 248; 248; 248; 248; 248; 248; 248; 248; 248; 248; 242; 242; 242; 242; 242;
   248; 248; 248; 248; 248; 248; 248; 248; 248; 248; 248; 248; 248; 242; 242; 242;
   242; 242; 248; 248; 248; 248; 248; 248; 248; 248; 248; 248; 248; 248; 248; 242;
   242; 242; 242; 242; 248; 248; 242; 242; 248; 248; 248; 248; 248; 248; 248; 248;
   248; 248; 248; 248; 248; 248; 248; 248; 248; 243; 243; 243; 243; 243; 243; 243;
   243; 243; 243; 243].
(* At C6 the two granules of res are in scope: 0x00 for its first eight bytes, 0x04 for its last four. *)
Definition headamp_B_shB : list Z := firstn 84 headamp_B_shA ++ [0; 4] ++ skipn 86 headamp_B_shA.

(* The strings (address, text without the NUL). *)
Definition headamp_B_strs : list (Z * list Z) := [
  (0x20f00, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116; 101]) (* reac.cfg.rate *);
  (0x20f20, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 111; 108; 101]) (* reac.cfg.role *);
  (0x20f40, [114; 101; 97; 99; 46; 104; 101; 97; 100; 97; 109; 112; 46]) (* reac.headamp. *);
  (0x20f60, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116; 101; 32]) (* reac.cfg.rate  *);
  (0x20f80, [82; 69; 65; 67; 46; 99; 102; 103; 46; 114; 97; 116; 101]) (* REAC.cfg.rate *);
  (0x20fa0, [115; 111; 109; 101; 46; 111; 116; 104; 101; 114; 46; 99; 111; 110; 116; 114; 111; 108]) (* some.other.control *);
  (0x20fe0, [114; 101; 97; 99; 46; 104; 101; 97; 100; 97; 109; 112]) (* reac.headamp *);
  (0x21000, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 111; 108; 101; 46; 120]) (* reac.cfg.role.x *);
  (0x21020, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116]) (* reac.cfg.rat *);
  (0x21160, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116; 101]) (* reac.cfg.rate *);
  (0x21180, [45; 49]) (* -1 *);
  (0x211a0, [43; 51]) (* +3 *);
  (0x211c0, [32; 55]) (*  7 *);
  (0x211e0, [48; 55]) (* 07 *);
  (0x21200, [57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57]) (* 99999999999999999999 *);
  (0x21240, []) (*  *);
  (0x21260, [120]) (* x *);
  (0x21280, [51; 97]) (* 3a *);
  (0x212a0, [45; 48]) (* -0 *);
  (0x212c0, [9; 53]) (* \t5 *);
  (0x212e0, [52; 56]) (* 48 *);
  (0x21300, [52; 55]) (* 47 *);
  (0x21320, [48; 120; 49]) (* 0x1 *);
  (0x21340, [45; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57]) (* -99999999999999999999 *);
  (0x21380, [112; 104; 97; 110; 116; 111; 109]) (* phantom *);
  (0x213a0, [112; 97; 100]) (* pad *);
  (0x213c0, [115; 101; 110; 115]) (* sens *);
  (0x213e0, [80; 65; 68]) (* PAD *);
  (0x21400, [115; 101; 110; 115; 120]) (* sensx *);
  (0x21420, [112; 104; 97; 110; 116; 111; 109; 46; 120]) (* phantom.x *);
  (0x21440, [115; 101; 110; 115; 32]) (* sens  *);
  (0x21460, [46]) (* . *);
  (0x214a0, [114; 101; 97; 99; 46; 104; 101; 97; 100; 97; 109; 112; 46]) (* reac.headamp. *);
  (0x214c0, [112; 104; 97; 110; 116; 111; 109]) (* phantom *);
  (0x214e0, [112; 97; 100]) (* pad *);
  (0x21500, [115; 101; 110; 115]) (* sens *)
].
(* The 43 registered globals (address, size). *)
Definition headamp_B_globs : list (Z * Z) := [
  (0x20f00, 14); (0x20f20, 14); (0x20f40, 14); (0x20f60, 15); (0x20f80, 14);
  (0x20fa0, 19); (0x20fe0, 13); (0x21000, 16); (0x21020, 13); (0x21040, 56);
  (0x210a0, 84); (0x21120, 16); (0x21140, 16); (0x21160, 14); (0x21180, 3);
  (0x211a0, 3); (0x211c0, 3); (0x211e0, 3); (0x21200, 21); (0x21240, 1);
  (0x21260, 2); (0x21280, 3); (0x212a0, 3); (0x212c0, 3); (0x212e0, 3);
  (0x21300, 3); (0x21320, 4); (0x21340, 22); (0x21380, 8); (0x213a0, 4);
  (0x213c0, 5); (0x213e0, 4); (0x21400, 6); (0x21420, 10); (0x21440, 6);
  (0x21460, 2); (0x214a0, 14); (0x214c0, 8); (0x214e0, 4); (0x21500, 5);
  (0x9c4e0, 72); (0x9c560, 112); (0x9c600, 64)
].
(* The read-only 8-byte cells the entry function and the parse load by address: the parse's four doubles, the
   harness's three division constants and the 31 pointer cells. *)
Definition headamp_B_cells : list (Z * Z) := [
  (0x10380, 0x3fe0000000000000); (0x10340, 0x4070000000000000); (0x103f0, 0xc3e0000000000001);
  (0x10358, 0x43e0000000000000); (0x10310, 0xc30c30c30c30c31); (0x10318, 0x124924924924924a);
  (0x10408, 0x7c1f07c1f07c1f1); (0x9c4e0, 0x20f00); (0x9c4e8, 0x20f20);
  (0x9c4f0, 0x20f40); (0x9c4f8, 0x20f60); (0x9c500, 0x20f80);
  (0x9c508, 0x20fa0); (0x9c510, 0x20fe0); (0x9c518, 0x21000);
  (0x9c520, 0x21020); (0x9c560, 0x21180); (0x9c568, 0x211a0);
  (0x9c570, 0x211c0); (0x9c578, 0x211e0); (0x9c580, 0x21200);
  (0x9c588, 0x21240); (0x9c590, 0x21260); (0x9c598, 0x21280);
  (0x9c5a0, 0x212a0); (0x9c5a8, 0x212c0); (0x9c5b0, 0x212e0);
  (0x9c5b8, 0x21300); (0x9c5c0, 0x21320); (0x9c5c8, 0x21340);
  (0x9c600, 0x21380); (0x9c608, 0x213a0); (0x9c610, 0x213c0);
  (0x9c618, 0x213e0); (0x9c620, 0x21400); (0x9c628, 0x21240);
  (0x9c630, 0x21420); (0x9c638, 0x21440)
].
(* The parse's four read-only doubles, in the order it loads them (fld 0x850b4, 0x850cc, 0x850dc, 0x850ec): 0.5,
   256.0, and the two bounds its float-cast check compares with before fcvt.l.d (0x850f8). *)
Definition headamp_B_dcs : list (Z * Z) :=
  [(0x10380, 0x3fe0000000000000); (0x10340, 0x4070000000000000);
   (0x103f0, 0xc3e0000000000001); (0x10358, 0x43e0000000000000)].

(* Register numbers: s0 = 8, s1 = 9, a0 = 10, s2 .. s11 = 18 .. 27. *)
Definition headamp_B_L23 (a0 : hd_x) : list (hd_loc * hd_x) :=
  [(LReg 10, a0); (LReg 8, XS); (LReg 9, XR); (LReg 18, XPp 0); (LReg 19, XShF); (LReg 21, XLen);
   (LReg 24, XPp 0x4d18); (LReg 27, XC SHADOW_OFF);
   (LCell XR 0x8, XPp 0x4008); (LCell XR 0x18, XF 0); (LCell XR 0x20, XCap); (LCell XR 0x38, XNotNull);
   (LCell XR 0x48, XF 0); (LCell XR 0xe0, XPpShr 0x4d14); (LCell XR 0x108, XC (-16381));
   (LCell XR 0x120, XPp 0x4d14); (LCell XR 0x148, XPp 0)].
Definition headamp_B_L45 (a0 : hd_x) : list (hd_loc * hd_x) :=
  [(LReg 10, a0); (LReg 8, XS); (LReg 9, XR); (LReg 18, XCap3); (LReg 19, XShF); (LReg 20, XCap);
   (LReg 21, XCap33); (LReg 23, XNotNull); (LReg 24, XPp 0x4d18); (LReg 25, XPod); (LReg 27, XC SHADOW_OFF);
   (LCell XR 0x8, XPp 0x4008); (LCell XR 0x18, XF 0); (LCell XR 0x48, XF 0); (LCell XR 0xe0, XPpShr 0x4d14);
   (LCell XR 0x108, XC (-16381)); (LCell XR 0x120, XPp 0x4d14); (LCell XR 0x148, XPp 0)].
Definition headamp_B_L67 (a0 : hd_x) : list (hd_loc * hd_x) :=
  [(LReg 10, a0); (LReg 8, XS); (LReg 9, XR); (LReg 19, XShF); (LReg 20, XCap); (LReg 21, XF 0);
   (LReg 22, XOut); (LReg 25, XRc); (LReg 26, XRc3);
   (LCell XR 0x18, XF 0); (LCell XR 0x140, XProps); (LCell XR 0x148, XPp 0); (LCell XR 0x150, XCap33);
   (LCell XR 0x158, XPod)].

Definition headamp_himg_B : hd_himg := {|
  hi_cid := 4;
  hi_c1 := 0x80fcc; hi_c2 := 0x82efc; hi_c3 := 0x82f00; hi_c4 := 0x82f34; hi_c5 := 0x82f38;
  hi_c6 := 0x83900; hi_c7 := 0x83904; hi_c8 := 0x83920; hi_c9 := 0x83950;
  hi_rsz := 0x220;
  hi_L1 := [(LReg 10, XPp 0); (LReg 8, XS); (LReg 9, XR); (LReg 18, XSrc); (LReg 19, XShF);
            (LReg 20, XC 19744); (LReg 21, XC 0x5000); (LReg 22, XLeft); (LReg 23, XF 0); (LReg 24, XCap);
            (LReg 27, XC SHADOW_OFF); (LCell XR 0x38, XNotNull); (LCell XR 0x48, XF 0)];
  hi_L2 := headamp_B_L23 XLenNZ;
  hi_L3 := headamp_B_L23 XPod;
  hi_L4 := headamp_B_L45 XCap33;
  hi_L5 := headamp_B_L45 XOut;
  hi_L6 := headamp_B_L67 XRc3NZ;
  hi_L7 := headamp_B_L67 XFirst;
  hi_L8 := [(LReg 8, XS); (LReg 9, XR); (LReg 19, XShF); (LReg 20, XCap); (LReg 21, XF 0); (LReg 22, XOut);
            (LReg 23, XFirst); (LReg 25, XRc);
            (LCell XR 0x18, XF 0); (LCell XR 0x140, XProps); (LCell XR 0x148, XPp 0); (LCell XR 0x150, XCap33);
            (LCell XR 0x158, XPod)];
  hi_L9 := [(LReg 8, XS); (LReg 9, XR); (LReg 19, XShF); (LReg 21, XF 0); (LReg 22, XOut); (LReg 23, XFirst);
            (LCell XR 0x18, XF 0); (LCell XR 0x148, XPp 0); (LCell XR 0x158, XPod)];
  hi_shA := headamp_B_shA; hi_shB := headamp_B_shB;
  hi_w1 := [(XF 0, 0x20, 0x258); (XShF, 0, 116); (XR, 0, 0x198)];
  hi_w2 := [];
  hi_w3 := [(XF 0, 0x2a0, 0xa8); (XShF, 0x54, 0x15); (XR, 0, 0x160)];
  hi_w4 := [];
  hi_w5 := [];
  hi_rz := [(0x180, 8)];
  hi_globs := headamp_B_globs;
  hi_strs := headamp_B_strs;
  hi_cells := headamp_B_cells;
  hi_akey := 0x214a0; hi_aph := 0x214c0; hi_apad := 0x214e0; hi_asens := 0x21500;
  hi_hkey := 0x20f40; hi_hph := 0x21380; hi_hpad := 0x213a0; hi_hsens := 0x213c0;
  hi_dcs := headamp_B_dcs;
  hi_gotw := 0x9d478; hi_guard := 0x5f8210 |}.

(* The pattern facts the frame lanes state about the two lists: 116 granules each, equal but at the two res
   granules. *)
Lemma headamp_B_sh_len : length headamp_B_shA = 116%nat /\ length headamp_B_shB = 116%nat.
Proof. split; reflexivity. Qed.
Lemma headamp_B_shB_res : nth 84 headamp_B_shB 0 = 0 /\ nth 85 headamp_B_shB 0 = 4 /\
  nth 84 headamp_B_shA 0 = 248 /\ nth 85 headamp_B_shA 0 = 248.
Proof. repeat split. Qed.
