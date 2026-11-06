(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/Bz/B0Traps.v, with its numbers changed; 131 of its 139 lines of code are new or changed and 155 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgImgA.v at dd9ff534326; the same record
   filled with image B's values (fuzz_headamp.asan-ubsan), each measured on image B, none copied from image A. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgImgB.v, with its module paths, module names, addresses and numbers changed; 89 of its 125 lines of code are new or changed and 103 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgImgA.v at 0de5d668c87; the same record for
   image B (fuzz_role.asan-ubsan), with every value re-measured on image B's own pinned bytes: the side-stack class,
   the four cut pcs, the real frame's size, the four cut lists, the frame's two shadow patterns, the two segments'
   write ranges, the checked real-frame range, the registered globals, the strings and the read-only cells. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; symbols, the globals table and the frame
   descriptor from the unstripped twin dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, whose
   loaded bytes are the pinned image's except the ELF header's section-table fields 0x10029 .. 0x1003e and the
   build-id note 0x102a8 .. 0x102cb, which no code reads): the record lib/A/RPgCSpec.v's segment contracts
   role_build_contract / role_check_contract read, filled with image B's values, each measured from the image's code
   and data. Statement data only: proves no function (kind: statement text).

   LLVMFuzzerTestOneInput 0x80020 (10848 bytes, 2712 instructions, one float instruction, the `flw fa0` 0x824c8).
   Its prologue takes a real frame of 0x200 bytes below the entry sp S (`addi sp,sp,-0x200` 0x80020, the probe store
   `sd zero,0(sp)` 0x80024), keeps S in s0 (0x8005c) and the 32-aligned base R = (S - 0x200) & -32 in s1 and sp
   (0x80060, 0x80064), saves ra, s0 .. s11 at [S - 0x68, S) (0x80028 .. 0x80058) and loads K (the runtime's shadow
   offset) into s11 through the GOT cell 0x9aad0, which holds 0xa3678 (0x8006c, 0x80078, 0x80080); the frame for
   locals F is a side-stack frame of class 4 (`li a0,704` 0x8008c, `jal __asan_stack_malloc_4` 0x80090, s7 = its
   result 0x80094, s10 = s7 0x800a0) holding t[96] at F+0x20, ch[24] at F+0xa0, r[4] at F+0xe0, e (104 bytes) at
   F+0xf0, e42 (104 bytes) at F+0x180, e62 (104 bytes) at F+0x210 and role (4 bytes) at F+0x2a0, with
   s3 = (F >> 3) + K (0x800d4, 0x80100) and the 0x58 shadow bytes role_B_shA written at 0x80104 .. 0x80264 (0xf1 left
   guard, 0xf8 out of scope, 0xf2 middle guards, 0xf3 right guard). The frame description at 0x18dd9 reads
   "7 32 96 7 t.i.i.i 160 24 8 ch.i.i.i 224 4 7 r.i.i.i 240 104 3 e.i 384 104 5 e42.i 528 104 5 e62.i 672 4 8
   role:147"; the frame header is F+0 = 0x41b58ab3, F+8 = 0x18dd9, F+0x10 = 0x80020 (0x800f0 .. 0x800f8).
   Image B keeps parts[4] on the real frame (R+0x178 .. R+0x197, stores 0x80e20, 0x80e48, 0x80e4c, 0x80e50) and the
   flag of the Float child at R+0x178 (0x823c4; pod_nearest's 8-byte out cell, a0 = R+0x178 at 0x824cc), not in the
   frame for locals. The cuts (the plain walk's ROLE_BUILD / ROLE_MALLOC2 / ROLE_CHECK / ROLE_FREE):
   C1 0x802c4 `bnez a0` after malloc(pp) (jal 0x802c0, a0 = s2 = 19744 from 0x802b8 / 0x802bc); C2 0x82164 `jal`
   malloc(pod) (a0 = len + (len == 0) from 0x8215c / 0x82160); C3 0x82168 `beqz a0`; C4 0x82570 `mv a0,s2` after
   check_code's return (jal 0x8256c), before the free(pod) jal 0x82574 and the free(pp) jal 0x8257c.
   The live values at each cut are the ones every path reaching it sets and the code after it reads (register or
   R-relative cell, with where it is set and where it is first read):
   C1: a0 = pp (0x802c0), s0 = S, s1 = R, s2 = 19744 (0x802b8, read 0x802d4), s3 = (F >> 3) + K (read 0x82194),
   s4 = src (0x80274 / 0x802b0, read 0x802e0), s5 = 0x5000 (0x802b4, read 0x80670), s6 = the bytes left
   (0x802a0 / 0x802a8, read 0x802dc), s7 = s10 = F (read 0x8066c / 0x80690), s11 = K (read 0x802f4),
   R+0x40 = fl (0x8029c / 0x802ac, read 0x82198);
   C2 and C3: a0 = len + (len == 0) / pod, s0 = S, s1 = R, s3, s7 = pp+0x4d18 (0x81ee4 / 0x81ee8, read 0x821b4),
   s8 = len (0x81f28 / 0x82158, read 0x82178), s11 = K (read 0x821b8), R+0x18 = pp+0x4008 (0x80694, read 0x821d4),
   R+0x20 = F (0x8066c, read 0x82588), R+0x38 = F (0x80690, read 0x82170), R+0x40 = fl,
   R+0xc0 = -0x3ffd (0x803ac, read 0x8223c), R+0xe8 = (pp+0x4d14) >> 3 (0x80688, read 0x82214),
   R+0x120 = pp+0x4d14 (0x80680, read 0x82230), R+0x140 = pp (0x802cc, read 0x82180);
   C4: s2 = pod (0x8216c), s0 = S, s1 = R, s3, s6 = pp (0x821cc / 0x823f8 / 0x82470, read 0x82578),
   s10 = F (0x82170 / 0x823f4 / 0x8246c, read 0x82594), R+0x20 = F (read 0x82588: the release reloads the
   side-stack result from that cell and reads the flag byte at its 0x3f8).
   The frame's shadow bytes at C2 and C3 are the prologue's again (every granule M01 brings into scope, it puts
   back: e at 0x8082c .. 0x80860, e62 at 0x8197c .. 0x819b4 and 0x81c94 .. 0x81cc8, t and ch at 0x80ee8 .. 0x80f20,
   r at 0x80dc4, e42 at 0x81c44 .. 0x81c78); at C4 the role granule 0x54 is 0x04 (0x82194), and the release resets
   it (0x82584). M01 writes the pp block, the frame objects [F+0x20, F+0x278), their shadow granules
   [shF+4, shF+0x4f) and the real-frame cells [R+0x10, R+0x40), [R+0x48, R+0x160) and the parts array
   [R+0x178, R+0x198); M02 writes the pod block, role [F+0x2a0, F+0x2a4), granule 0x54, and the real-frame cells
   [R+0x120, R+0x140) (R+0x120 := 0x4018 at 0x82260 and the strcmp spills 0x82384 .. 0x82394), [R+0x148, R+0x160)
   (the rest of those spills and rc at 0x821f4) and [R+0x178, R+0x180) (the flag, and pod_nearest's store).
   The real-frame bytes [R+0x178, R+0x188) are the ones the code shadow-checks (0x80e24 .. 0x80e3c before the parts
   stores, at R+0x180; pod_nearest 0x82fe8 .. 0x82ff4 at its out cell R+0x178).
   The globals are the 49 rows of asan_globals (its own section at 0x9f380, 0xc40 bytes; every odr_indicator is -1,
   so none has a real ODR indicator); the strings are the ones the harness's strlen / strcmp / memcpy calls and its
   callees read (each a registered global of size length + 1; 0x21160 is ent_build.s, the 14-byte source of case 9's
   memcpy at 0x8131c); the cells are reac_role_prop_parse's five doubles (0.5, -2^31, 2^31 and image B's two
   float-cast bounds), reac_role_refuse_code's two table entries, and the 31 pointer cells of .data.rel.ro the
   harness loads with `ld` (vocab[i] at 0x813e8: 0x9a7a0 + 8 i, 9 cells; odd_ch[k] at 0x81630: 0x9a820 + 8 k,
   14 cells; param[k] for case 0's parts at 0x80e34: 0x9a8c0 + 8 k, 8 cells), each the address of one of the strings
   above. Every string address is image A's at +0x40 and every .data.rel.ro table is image A's at +0x2a0; the texts,
   the sizes and the five doubles' values are the two images' own measurements, equal where this says equal. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
Import ListNotations.
Local Open Scope Z_scope.

(* The frame's shadow bytes after the prologue (88 granules of the 704-byte frame), and at C4. *)
Definition role_B_shA : list Z :=
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
Definition role_B_shB : list Z := firstn 84 role_B_shA ++ [0x04] ++ skipn 85 role_B_shA.

(* The strings (address, text without the NUL), the 49 registered globals (address, size) and the cells. *)
Definition role_B_strs : list (Z * list Z) := [
  (0x20f00, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116; 101]) (* reac.cfg.rate *);
  (0x20f20, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 111; 108; 101]) (* reac.cfg.role *);
  (0x20f40, [114; 101; 97; 99; 46; 104; 101; 97; 100; 97; 109; 112; 46]) (* reac.headamp. *);
  (0x20f60, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116; 101; 32]) (* reac.cfg.rate and a space *);
  (0x20f80, [82; 69; 65; 67; 46; 99; 102; 103; 46; 114; 97; 116; 101]) (* REAC.cfg.rate *);
  (0x20fa0, [115; 111; 109; 101; 46; 111; 116; 104; 101; 114; 46; 99; 111; 110; 116; 114; 111; 108]) (* some.other.control *);
  (0x20fe0, [114; 101; 97; 99; 46; 104; 101; 97; 100; 97; 109; 112]) (* reac.headamp *);
  (0x21000, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 111; 108; 101; 46; 120]) (* reac.cfg.role.x *);
  (0x21020, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116]) (* reac.cfg.rat *);
  (0x21160, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116; 101]) (* reac.cfg.rate, ent_build.s *);
  (0x21180, [45; 49]) (* -1 *);
  (0x211a0, [43; 51]) (* +3 *);
  (0x211c0, [32; 55]) (* space 7 *);
  (0x211e0, [48; 55]) (* 07 *);
  (0x21200, [57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57]) (* twenty 9s *);
  (0x21240, []) (* the empty string *);
  (0x21260, [120]) (* x *);
  (0x21280, [51; 97]) (* 3a *);
  (0x212a0, [45; 48]) (* -0 *);
  (0x212c0, [9; 53]) (* tab 5 *);
  (0x212e0, [52; 56]) (* 48 *);
  (0x21300, [52; 55]) (* 47 *);
  (0x21320, [48; 120; 49]) (* 0x1 *);
  (0x21340, [45; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57]) (* minus twenty 9s *);
  (0x21380, [112; 104; 97; 110; 116; 111; 109]) (* phantom *);
  (0x213a0, [112; 97; 100]) (* pad *);
  (0x213c0, [115; 101; 110; 115]) (* sens *);
  (0x213e0, [80; 65; 68]) (* PAD *);
  (0x21400, [115; 101; 110; 115; 120]) (* sensx *);
  (0x21420, [112; 104; 97; 110; 116; 111; 109; 46; 120]) (* phantom.x *);
  (0x21440, [115; 101; 110; 115; 32]) (* sens and a space *);
  (0x21460, [46]) (* a dot *);
  (0x215e0, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 111; 108; 101]) (* reac.cfg.role, the parse's key *);
  (0x214c0, [97; 112; 112; 108; 105; 101; 100]) (* applied, check_answer *);
  (0x21480, [114; 111; 108; 101; 95; 114; 101; 101; 115; 116; 97; 98; 108; 105; 115; 104; 95; 112; 101; 110; 100; 105; 110; 103]) (* role_reestablish_pending, check_answer *);
  (0x214e0, [110; 111; 110; 101]) (* none, check_code *);
  (0x21500, [109; 97; 108; 102; 111; 114; 109; 101; 100]) (* malformed, check_code *);
  (0x215c0, [97; 112; 112; 108; 105; 101; 100]) (* applied, apply_state *);
  (0x21580, [114; 111; 108; 101; 95; 114; 101; 101; 115; 116; 97; 98; 108; 105; 115; 104; 95; 112; 101; 110; 100; 105; 110; 103]) (* role_reestablish_pending, apply_state *);
  (0x21540, [110; 111; 110; 101]) (* none, refuse_code codes[0] *);
  (0x21560, [109; 97; 108; 102; 111; 114; 109; 101; 100]) (* malformed, refuse_code codes[1] *)
].
Definition role_B_globs : list (Z * Z) := [
  (0x20f00, 14); (0x20f20, 14); (0x20f40, 14); (0x20f60, 15); (0x20f80, 14); (0x20fa0, 19); (0x20fe0, 13);
  (0x21000, 16); (0x21020, 13); (0x21040, 56); (0x210a0, 84); (0x21120, 16); (0x21140, 16); (0x21160, 14);
  (0x21180, 3); (0x211a0, 3); (0x211c0, 3); (0x211e0, 3); (0x21200, 21); (0x21240, 1); (0x21260, 2);
  (0x21280, 3); (0x212a0, 3); (0x212c0, 3); (0x212e0, 3); (0x21300, 3); (0x21320, 4); (0x21340, 22);
  (0x21380, 8); (0x213a0, 4); (0x213c0, 5); (0x213e0, 4); (0x21400, 6); (0x21420, 10); (0x21440, 6);
  (0x21460, 2); (0x21480, 25); (0x214c0, 8); (0x214e0, 5); (0x21500, 10); (0x21540, 5); (0x21560, 10);
  (0x21580, 25); (0x215c0, 8); (0x215e0, 14); (0x9a7a0, 72); (0x9a820, 112); (0x9a8c0, 64); (0x9a920, 16)
].
(* The first five rows are the cells reac_role_prop_parse's float path reads (`fld` 0x83528, 0x83530, 0x83548,
   0x83558, 0x83568): 0.5, -2^31, 2^31 and the two bounds image B tests before its `fcvt.l.d`. *)
Definition role_B_cells : list (Z * Z) := [
  (0x10380, 0x3fe0000000000000); (0x103e8, 0xc1e0000000000000); (0x10330, 0x41e0000000000000);
  (0x103f8, 0xc3e0000000000001); (0x10358, 0x43e0000000000000);
  (0x9a920, 0x21540); (0x9a928, 0x21560);
  (0x9a7a0, 0x20f00); (0x9a7a8, 0x20f20); (0x9a7b0, 0x20f40); (0x9a7b8, 0x20f60); (0x9a7c0, 0x20f80);
  (0x9a7c8, 0x20fa0); (0x9a7d0, 0x20fe0); (0x9a7d8, 0x21000); (0x9a7e0, 0x21020);
  (0x9a820, 0x21180); (0x9a828, 0x211a0); (0x9a830, 0x211c0); (0x9a838, 0x211e0); (0x9a840, 0x21200);
  (0x9a848, 0x21240); (0x9a850, 0x21260); (0x9a858, 0x21280); (0x9a860, 0x212a0); (0x9a868, 0x212c0);
  (0x9a870, 0x212e0); (0x9a878, 0x21300); (0x9a880, 0x21320); (0x9a888, 0x21340);
  (0x9a8c0, 0x21380); (0x9a8c8, 0x213a0); (0x9a8d0, 0x213c0); (0x9a8d8, 0x213e0); (0x9a8e0, 0x21400);
  (0x9a8e8, 0x21240); (0x9a8f0, 0x21420); (0x9a8f8, 0x21440)
].

(* Register numbers: s0 = 8, s1 = 9, a0 = 10, s2 .. s11 = 18 .. 27. *)
Definition role_B_L23 (a0 : rl_x) : list (rl_loc * rl_x) :=
  [(LReg 10, a0); (LReg 8, XS); (LReg 9, XR); (LReg 19, XShF); (LReg 23, XPp 0x4d18); (LReg 24, XLen);
   (LReg 27, XC SHADOW_OFF);
   (LCell XR 0x18, XPp 0x4008); (LCell XR 0x20, XF); (LCell XR 0x38, XF); (LCell XR 0x40, XFl);
   (LCell XR 0xc0, XC (-0x3ffd)); (LCell XR 0xe8, XPpShr 0x4d14); (LCell XR 0x120, XPp 0x4d14);
   (LCell XR 0x140, XPp 0)].

Definition role_himg_B : rl_himg := {|
  hi_cid := 4;
  hi_c1 := 0x802c4; hi_c2 := 0x82164; hi_c3 := 0x82168; hi_c4 := 0x82570;
  hi_rsz := 0x200;
  hi_L1 := [(LReg 10, XPp 0); (LReg 8, XS); (LReg 9, XR); (LReg 18, XC 19744); (LReg 19, XShF);
            (LReg 20, XSrc); (LReg 21, XC 0x5000); (LReg 22, XLeft); (LReg 23, XF); (LReg 26, XF);
            (LReg 27, XC SHADOW_OFF); (LCell XR 0x40, XFl)];
  hi_L2 := role_B_L23 XLenNZ;
  hi_L3 := role_B_L23 XPod;
  hi_L4 := [(LReg 18, XPod); (LReg 8, XS); (LReg 9, XR); (LReg 19, XShF); (LReg 22, XPp 0); (LReg 26, XF);
            (LCell XR 0x20, XF)];
  hi_shA := role_B_shA; hi_shB := role_B_shB;
  hi_w1 := [(XF, 0x20, 0x258); (XShF, 4, 75); (XR, 0x10, 0x30); (XR, 0x48, 0x118); (XR, 0x178, 0x20)];
  hi_w2 := [(XF, 0x2a0, 4); (XShF, 0x54, 1); (XR, 0x120, 0x20); (XR, 0x148, 0x18); (XR, 0x178, 8)];
  hi_rz := [(0x178, 16)];
  hi_globs := role_B_globs;
  hi_strs := role_B_strs;
  hi_cells := role_B_cells |}.

(* The frame's shadow has one byte per granule of the 704-byte frame, and the two patterns differ only at the
   granule M02 brings into scope. *)
Lemma role_B_sh_len : length role_B_shA = 88%nat /\ length role_B_shB = 88%nat.
Proof. vm_compute. split; reflexivity. Qed.

(* The record's lists have the lengths the header states. *)
Lemma role_B_list_len :
  length role_B_strs = 41%nat /\ length role_B_globs = 49%nat /\ length role_B_cells = 38%nat /\
  length (hi_L1 role_himg_B) = 12%nat /\ length (hi_L2 role_himg_B) = 15%nat /\
  length (hi_L3 role_himg_B) = 15%nat /\ length (hi_L4 role_himg_B) = 7%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* The key literal the parse and the harness's strcmp read is Role.ROLE_KEY's text. *)
Lemma role_B_key_text : map (fun x : byte => bv_unsigned x) Role.ROLE_KEY =
  [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 111; 108; 101].
Proof. vm_compute. reflexivity. Qed.
