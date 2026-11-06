(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; symbols and bytes from the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose loaded sections are byte-equal to the
   pin's except .note.gnu.build-id): the record lib/A/HPgCSpec.v's five segment contracts read, filled with image A's values, each measured
   from the image's code and data. Statement data only: proves no function (kind: statement text).

   LLVMFuzzerTestOneInput 0x80bc0 (12924 bytes, 3231 instructions). Its prologue takes a real frame of 0x1e0 bytes
   below the entry sp S (`addi sp,sp,-0x1e0` 0x80bc0), saves ra, s0 .. s11 and fs0 .. fs2 at [S - 0x80, S)
   (0x80bc8 .. 0x80c04), keeps S in s0 (0x80c08) and the 32-aligned base R = sp & -32 in s1 and sp (0x80c0c,
   0x80c10), and loads K (the runtime's shadow offset) into s7 through the GOT word 0x9c370 (0x80c24, 0x80c2c).
   The frame for locals F is a side-stack frame of class 4: the option byte is read through the GOT word 0x9c3c8
   (0x80c20, 0x80c28) and, when it is nonzero, `addi a0,zero,0x280` + the class-4 call at 0x80c38 / 0x80c3c give F
   in s6 and s10 (the real-stack arm 0x80c54 .. 0x80c6c runs when the option byte is 0 or when the class-4 call
   returns 0, which the start-up state and the empty frame list exclude); R + 0x138 := F (0x80c70)
   and s3 = (F >> 3) + K (0x80c80, 0x80cac). The frame holds t[96] at F+0x20, ch[24] at F+0xa0, r[4] at F+0xe0,
   e (104 bytes) at F+0xf0, res (12 bytes) at F+0x180 and x (struct expect, 136 bytes) at F+0x1a0; the prologue
   writes the 80 shadow bytes headamp_A_shA at 0x80cb0 .. 0x80df0 (0xf1 left guard, 0xf8 object in scope, 0xf2
   middle guards, 0xf3 right guard).

   The cuts (the plain walk's ENTRY, K13044, K1404c, K14080, K14168, K141b4, RET at image A's addresses, with the
   allocator calls split out): C1 0x80e94 `bnez a0` after malloc(pp) (jal 0x80e90); C2 0x82e60 `jal` malloc(pod)
   (a0 = len + (len == 0) from 0x82e58 .. 0x82e5c); C3 0x82e64 `beqz a0`; C4 0x82e94 `jal` malloc(out) (a0 =
   3 cap + 3 from 0x82e84 .. 0x82e90); C5 0x82e98 `beqz a0`; C6 0x83740 `jal` malloc(first) (a0 = 3 max(rc, 0) +
   (it == 0) from 0x83724 .. 0x8373c); C7 0x83744 `beqz a0`; C8 0x83764 after the __asan_memcpy that fills first
   (jal 0x83760); C9 0x83794 `mv a0,s2` after check_plain's return (jal 0x83790), before the free(first) jal
   0x83798. The live values at each cut are the ones every path reaching it sets and the code after it reads
   (measured by backward liveness and reaching definitions over the non-error blocks of the function's CFG):
   C1: a0 = pp (0x80e90), s0 = S, s1 = R, s2 = 19744 (0x80e88), s3 = (F >> 3) + K, s4 = 0x5000 (0x80e84),
   s5 = the bytes left after the two harness bytes (0x80e2c / 0x80e40 / 0x80e64), s6 = s10 = F, s7 = K,
   s8 = cap (0x80e30 / 0x80e44 / 0x80e80), s11 = the input cursor (0x80c30 on the empty input, 0x80e34 / 0x80e68), R+0x40 = the null flag
   (0x80e24 / 0x80e3c);
   C2 and C3: a0 = len + (len == 0) / pod, s2 = pp+0x4d18 (0x82cd0 .. 0x82cd4), s3, s4 = pp (0x82e54),
   s5 = pp+0x4000 (0x80f30, reloaded 0x81b80 from R+0x98 which 0x812f0 wrote), s7 = K, s8 = len (0x82d0c / 0x82e50, both `ld s8,0(s5)`),
   s10 = F (0x82c8c), R+0x20 = F (0x81230), R+0x28 = cap (0x8122c), R+0x40 = the null flag, R+0x60 = F (0x8124c),
   R+0x90 = (pp+0x4d14) >> 3 (0x81248), R+0xa0 = pp+0x4d14 (0x81240), R+0xf0 = pp (0x80e9c);
   C4 and C5: a0 = 3 cap + 3 / out, s2, s3, s4 = 3 cap (0x82e88), s5, s6 = cap (0x82e6c), s7, s9 = pod (0x82e68),
   s10 = F, s11 = 3 cap + 3 (0x82e8c), and the cells of C2 but R+0x28;
   C6 and C7: a0 = 3 max(rc, 0) + (it == 0) / first, s3, s5 = 3 max(rc, 0) (0x83734), s6 = cap, s8 = out (0x82e9c),
   s9 = pod, s11 = rc (0x82ef0), R+0x20 = F, R+0x60 = F, R+0xf0 = pp, R+0x110 = the parse's first argument
   (0x82edc: pod when the null flag is 0, else 0), R+0x118 = 3 cap + 3 (0x82ea8);
   C8: s2 = first (0x83748), s3, s6, s8, s9, s10 = F (0x8374c), s11 = rc, and the four cells of C6;
   C9: s2 = first, s3, s8, s9, s10 = F, R+0x20 = F, R+0xf0 = pp;
   and at every cut s0 = S and s1 = R.
   The frame's shadow bytes at C2 .. C5 are the prologue's again (every granule M01 brings into scope it puts
   back); at C6 .. C9 the two res granules 0x30 and 0x31 are 0x00 and 0x04 (0x82eb8, 0x82ebc) and the seventeen x
   granules 0x34 .. 0x44, which the non-corrupt path brings into scope at 0x82f38 .. 0x82f78, are back at 0xf8
   (0x836dc .. 0x83720); the epilogue puts the res granules back at 0x837b4 .. 0x837bc.
   M01 writes the pp block, the frame objects [F+0x20, F+0x158), their shadow bytes and the real-frame cells
   [R, R+0x160) (its 36 s1-relative store offsets run 0x18 .. 0x158); M02 writes the pod block only; M03 writes
   the out block, res and x [F+0x180, F+0x228), their shadow granules [0x30, 0x45), the real-frame cells
   [R, R+0x120) and the errno cell; M04a writes the first block only; M04b writes the out block and the errno
   cell. One instrumented check of this function reads the shadow of a real-frame cell: the 8-byte store of
   parts[1] at R+0x148 (pod.h:253, the store at 0x81aa8) is checked at 0x81a84 .. 0x81a98 (`addi a2,s1,0x148;
   srli a2,a2,3; add a2,a2,s7; lbu a2,0(a2); beqz a2,+8; j 0x83aa0`); it is the only s1-relative check (role's
   twin is its pair at R+0x118), so the checked real-frame range list is [(0x148, 8)].
   The globals are the 43 rows of asan_globals (its own section at 0xa0c20, 0xac0 bytes; no descriptor has an ODR
   indicator). The strings are the 36 the harness, the parse and their callees read: the nine of ent_build.vocab,
   the fourteen of ent_headamp_key.odd_ch, the eight of ent_headamp_key.param (one of them, the empty string at
   0x21200, is also an odd_ch entry), ent_build.s at 0x21120, the dot at 0x21420, the harness's own
   "reac.headamp." at 0x20f00 (its strncmp literal, also vocab[2]) and the parse's four literals at 0x21460,
   0x21480, 0x214a0, 0x214c0. The cells are the parse's two doubles (0.5 at 0x10378 and 256.0 at 0x10340), the
   harness's three division constants (0x10310, 0x10318, 0x103f8) and the 31 pointer cells of .data.rel.ro that
   the harness loads with `ld` (vocab 0x9c060 + 8 i for i < 9, base at 0x81f9c; odd_ch 0x9c0e0 + 8 k for k < 14,
   base by `auipc a2,0x1a` alone at 0x820e0, the load at 0x82108 behind an instrumented check; param 0x9c180 + 8 k
   for k < 8, base at 0x81a40), each the address of one of the strings above. The nine words of the jump table at
   0x20e9c (read by `lw` at 0x8184c, target = word + 0x20e9c) are read-only image bytes read without a shadow
   check, which arodata_okP and rom_view give.
   The stack-guard cells musl's strtol reads through the strtol wrapper: the GOT word 0x9cff8 (read at 0x95324 inside
   musl's __strtol_internal 0x952f8) and the guard object __stack_chk_guard 0x5f7d90, whose word it holds. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
Import ListNotations.
Local Open Scope Z_scope.

(* The frame's shadow bytes after the prologue (80 granules of the 0x280-byte frame), and from C6 on. *)
Definition headamp_A_shA : list Z :=
  [241; 241; 241; 241; 248; 248; 248; 248; 248; 248; 248; 248; 248; 248; 248; 248;
   242; 242; 242; 242; 248; 248; 248; 242; 242; 242; 242; 242; 248; 242; 248; 248;
   248; 248; 248; 248; 248; 248; 248; 248; 248; 248; 248; 242; 242; 242; 242; 242;
   248; 248; 242; 242; 248; 248; 248; 248; 248; 248; 248; 248; 248; 248; 248; 248;
   248; 248; 248; 248; 248; 243; 243; 243; 243; 243; 243; 243; 243; 243; 243; 243].
(* At C6 the two granules of res are in scope: 0x00 for its first eight bytes, 0x04 for its last four. *)
Definition headamp_A_shB : list Z := firstn 48 headamp_A_shA ++ [0; 4] ++ skipn 50 headamp_A_shA.

(* The strings (address, text without the NUL). *)
Definition headamp_A_strs : list (Z * list Z) := [
  (0x20ec0, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116; 101]) (* reac.cfg.rate *);
  (0x20ee0, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 111; 108; 101]) (* reac.cfg.role *);
  (0x20f00, [114; 101; 97; 99; 46; 104; 101; 97; 100; 97; 109; 112; 46]) (* reac.headamp. *);
  (0x20f20, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116; 101; 32]) (* reac.cfg.rate  *);
  (0x20f40, [82; 69; 65; 67; 46; 99; 102; 103; 46; 114; 97; 116; 101]) (* REAC.cfg.rate *);
  (0x20f60, [115; 111; 109; 101; 46; 111; 116; 104; 101; 114; 46; 99; 111; 110; 116; 114; 111; 108]) (* some.other.control *);
  (0x20fa0, [114; 101; 97; 99; 46; 104; 101; 97; 100; 97; 109; 112]) (* reac.headamp *);
  (0x20fc0, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 111; 108; 101; 46; 120]) (* reac.cfg.role.x *);
  (0x20fe0, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116]) (* reac.cfg.rat *);
  (0x21120, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116; 101]) (* reac.cfg.rate *);
  (0x21140, [45; 49]) (* -1 *);
  (0x21160, [43; 51]) (* +3 *);
  (0x21180, [32; 55]) (*  7 *);
  (0x211a0, [48; 55]) (* 07 *);
  (0x211c0, [57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57]) (* 99999999999999999999 *);
  (0x21200, []) (*  *);
  (0x21220, [120]) (* x *);
  (0x21240, [51; 97]) (* 3a *);
  (0x21260, [45; 48]) (* -0 *);
  (0x21280, [9; 53]) (* \t5 *);
  (0x212a0, [52; 56]) (* 48 *);
  (0x212c0, [52; 55]) (* 47 *);
  (0x212e0, [48; 120; 49]) (* 0x1 *);
  (0x21300, [45; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57]) (* -99999999999999999999 *);
  (0x21340, [112; 104; 97; 110; 116; 111; 109]) (* phantom *);
  (0x21360, [112; 97; 100]) (* pad *);
  (0x21380, [115; 101; 110; 115]) (* sens *);
  (0x213a0, [80; 65; 68]) (* PAD *);
  (0x213c0, [115; 101; 110; 115; 120]) (* sensx *);
  (0x213e0, [112; 104; 97; 110; 116; 111; 109; 46; 120]) (* phantom.x *);
  (0x21400, [115; 101; 110; 115; 32]) (* sens  *);
  (0x21420, [46]) (* . *);
  (0x21460, [114; 101; 97; 99; 46; 104; 101; 97; 100; 97; 109; 112; 46]) (* reac.headamp. *);
  (0x21480, [112; 104; 97; 110; 116; 111; 109]) (* phantom *);
  (0x214a0, [112; 97; 100]) (* pad *);
  (0x214c0, [115; 101; 110; 115]) (* sens *)
].
(* The 43 registered globals (address, size). *)
Definition headamp_A_globs : list (Z * Z) := [
  (0x20ec0, 14); (0x20ee0, 14); (0x20f00, 14); (0x20f20, 15); (0x20f40, 14);
  (0x20f60, 19); (0x20fa0, 13); (0x20fc0, 16); (0x20fe0, 13); (0x21000, 56);
  (0x21060, 84); (0x210e0, 16); (0x21100, 16); (0x21120, 14); (0x21140, 3);
  (0x21160, 3); (0x21180, 3); (0x211a0, 3); (0x211c0, 21); (0x21200, 1);
  (0x21220, 2); (0x21240, 3); (0x21260, 3); (0x21280, 3); (0x212a0, 3);
  (0x212c0, 3); (0x212e0, 4); (0x21300, 22); (0x21340, 8); (0x21360, 4);
  (0x21380, 5); (0x213a0, 4); (0x213c0, 6); (0x213e0, 10); (0x21400, 6);
  (0x21420, 2); (0x21460, 14); (0x21480, 8); (0x214a0, 4); (0x214c0, 5);
  (0x9c060, 72); (0x9c0e0, 112); (0x9c180, 64)
].
(* The read-only 8-byte cells the segments and their callees load without a shadow check. *)
Definition headamp_A_cells : list (Z * Z) := [
  (0x10378, 0x3fe0000000000000); (0x10340, 0x4070000000000000); (0x10310, 0xc30c30c30c30c31);
  (0x10318, 0x124924924924924a); (0x103f8, 0x7c1f07c1f07c1f1); (0x9c060, 0x20ec0);
  (0x9c068, 0x20ee0); (0x9c070, 0x20f00); (0x9c078, 0x20f20);
  (0x9c080, 0x20f40); (0x9c088, 0x20f60); (0x9c090, 0x20fa0);
  (0x9c098, 0x20fc0); (0x9c0a0, 0x20fe0); (0x9c0e0, 0x21140);
  (0x9c0e8, 0x21160); (0x9c0f0, 0x21180); (0x9c0f8, 0x211a0);
  (0x9c100, 0x211c0); (0x9c108, 0x21200); (0x9c110, 0x21220);
  (0x9c118, 0x21240); (0x9c120, 0x21260); (0x9c128, 0x21280);
  (0x9c130, 0x212a0); (0x9c138, 0x212c0); (0x9c140, 0x212e0);
  (0x9c148, 0x21300); (0x9c180, 0x21340); (0x9c188, 0x21360);
  (0x9c190, 0x21380); (0x9c198, 0x213a0); (0x9c1a0, 0x213c0);
  (0x9c1a8, 0x21200); (0x9c1b0, 0x213e0); (0x9c1b8, 0x21400)
].
(* The parse's two read-only doubles: 0.5 at 0x10378 and 256.0 at 0x10340 (fld 0x84cbc / 0x84cd4). *)
Definition headamp_A_dcs : list (Z * Z) := [(0x10378, 0x3fe0000000000000); (0x10340, 0x4070000000000000)].

(* Register numbers: s0 = 8, s1 = 9, a0 = 10, s2 .. s11 = 18 .. 27. *)
Definition headamp_A_L23 (a0 : hd_x) : list (hd_loc * hd_x) :=
  [(LReg 10, a0); (LReg 8, XS); (LReg 9, XR); (LReg 18, XPp 0x4d18); (LReg 19, XShF); (LReg 20, XPp 0);
   (LReg 21, XPp 0x4000); (LReg 23, XC SHADOW_OFF); (LReg 24, XLen); (LReg 26, XF 0);
   (LCell XR 0x20, XF 0); (LCell XR 0x28, XCap); (LCell XR 0x40, XNull); (LCell XR 0x60, XF 0);
   (LCell XR 0x90, XPpShr 0x4d14); (LCell XR 0xa0, XPp 0x4d14); (LCell XR 0xf0, XPp 0)].
Definition headamp_A_L45 (a0 : hd_x) : list (hd_loc * hd_x) :=
  [(LReg 10, a0); (LReg 8, XS); (LReg 9, XR); (LReg 18, XPp 0x4d18); (LReg 19, XShF); (LReg 20, XCap3);
   (LReg 21, XPp 0x4000); (LReg 22, XCap); (LReg 23, XC SHADOW_OFF); (LReg 25, XPod); (LReg 26, XF 0);
   (LReg 27, XCap33);
   (LCell XR 0x20, XF 0); (LCell XR 0x40, XNull); (LCell XR 0x60, XF 0);
   (LCell XR 0x90, XPpShr 0x4d14); (LCell XR 0xa0, XPp 0x4d14); (LCell XR 0xf0, XPp 0)].
Definition headamp_A_L67 (a0 : hd_x) : list (hd_loc * hd_x) :=
  [(LReg 10, a0); (LReg 8, XS); (LReg 9, XR); (LReg 19, XShF); (LReg 21, XRc3); (LReg 22, XCap);
   (LReg 24, XOut); (LReg 25, XPod); (LReg 27, XRc);
   (LCell XR 0x20, XF 0); (LCell XR 0x60, XF 0); (LCell XR 0xf0, XPp 0);
   (LCell XR 0x110, XProps); (LCell XR 0x118, XCap33)].

Definition headamp_himg_A : hd_himg := {|
  hi_cid := 4;
  hi_c1 := 0x80e94; hi_c2 := 0x82e60; hi_c3 := 0x82e64; hi_c4 := 0x82e94; hi_c5 := 0x82e98;
  hi_c6 := 0x83740; hi_c7 := 0x83744; hi_c8 := 0x83764; hi_c9 := 0x83794;
  hi_rsz := 0x1e0;
  hi_L1 := [(LReg 10, XPp 0); (LReg 8, XS); (LReg 9, XR); (LReg 18, XC 19744); (LReg 19, XShF);
            (LReg 20, XC 0x5000); (LReg 21, XLeft); (LReg 22, XF 0); (LReg 23, XC SHADOW_OFF);
            (LReg 24, XCap); (LReg 26, XF 0); (LReg 27, XSrc); (LCell XR 0x40, XNull)];
  hi_L2 := headamp_A_L23 XLenNZ;
  hi_L3 := headamp_A_L23 XPod;
  hi_L4 := headamp_A_L45 XCap33;
  hi_L5 := headamp_A_L45 XOut;
  hi_L6 := headamp_A_L67 XRc3NZ;
  hi_L7 := headamp_A_L67 XFirst;
  hi_L8 := [(LReg 8, XS); (LReg 9, XR); (LReg 18, XFirst); (LReg 19, XShF); (LReg 22, XCap);
            (LReg 24, XOut); (LReg 25, XPod); (LReg 26, XF 0); (LReg 27, XRc);
            (LCell XR 0x20, XF 0); (LCell XR 0xf0, XPp 0); (LCell XR 0x110, XProps); (LCell XR 0x118, XCap33)];
  hi_L9 := [(LReg 8, XS); (LReg 9, XR); (LReg 18, XFirst); (LReg 19, XShF); (LReg 24, XOut); (LReg 25, XPod);
            (LReg 26, XF 0); (LCell XR 0x20, XF 0); (LCell XR 0xf0, XPp 0)];
  hi_shA := headamp_A_shA; hi_shB := headamp_A_shB;
  hi_w1 := [(XF 0, 0x20, 0x138); (XShF, 0, 80); (XR, 0, 0x160)];
  hi_w2 := [];
  hi_w3 := [(XF 0, 0x180, 0xa8); (XShF, 0x30, 0x15); (XR, 0, 0x120)];
  hi_w4 := [];
  hi_w5 := [];
  hi_rz := [(0x148, 8)];
  hi_globs := headamp_A_globs;
  hi_strs := headamp_A_strs;
  hi_cells := headamp_A_cells;
  hi_akey := 0x21460; hi_aph := 0x21480; hi_apad := 0x214a0; hi_asens := 0x214c0;
  hi_hkey := 0x20f00; hi_hph := 0x21340; hi_hpad := 0x21360; hi_hsens := 0x21380;
  hi_dcs := headamp_A_dcs;
  hi_gotw := 0x9cff8; hi_guard := 0x5f7d90 |}.

(* The texts the parse's four literals hold are the shared model's (Pod/Headamp.v). *)
Lemma headamp_A_key_text : hd_zbytes Headamp.HA_PREFIX =
  [114; 101; 97; 99; 46; 104; 101; 97; 100; 97; 109; 112; 46].
Proof. vm_compute. reflexivity. Qed.
Lemma headamp_A_param_texts :
  hd_zbytes Headamp.NAME_PHANTOM = [112; 104; 97; 110; 116; 111; 109] /\
  hd_zbytes Headamp.NAME_PAD = [112; 97; 100] /\
  hd_zbytes Headamp.NAME_SENS = [115; 101; 110; 115].
Proof. vm_compute. repeat split. Qed.
