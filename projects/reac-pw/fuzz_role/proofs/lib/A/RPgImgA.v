(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; symbols from the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6): the record lib/A/RPgCSpec.v's segment contracts
   role_build_contract / role_check_contract read, filled with image A's values, each measured from the image's code
   and data. Statement data only: proves no function (kind: statement text).

   LLVMFuzzerTestOneInput 0x7ff88 (11308 bytes). Its prologue takes a real frame of 0x1a0 bytes below the entry sp S
   (`addi sp,sp,-0x1a0` 0x7ff88), keeps S in s0 (0x7ffc4) and the 32-aligned base R = (S - 0x1a0) & -32 in s1 and sp
   (0x7ffc8, 0x7ffcc), saves ra, s0 .. s11 at [S - 0x68, S) and loads K (the runtime's shadow offset) into s7
   (0x7ffd4 .. 0x7ffe8); the frame for locals F is a side-stack frame of class 3 (`addi a0,zero,0x1a0` 0x7fff4,
   `jal __asan_stack_malloc_3` 0x7fff8; s6 = s9 = F, R+0x8 := F at 0x80528) holding t[96] at F+0x20, ch[24] at F+0xa0,
   r[4] at F+0xe0, e (104 bytes) at F+0xf0 and role at F+0x180, with s3 = (F >> 3) + K (0x8003c, 0x80068) and the
   shadow bytes role_A_shA written at 0x8006c .. 0x8013c (0xf1 left guard, 0xf8 out of scope, 0xf2 middle guards,
   0xf3 right guard). The cuts (the plain walk's ROLE_BUILD / ROLE_MALLOC2 / ROLE_CHECK / ROLE_FREE):
   C1 0x80194 `bnez a0` after malloc(pp) (jal 0x80190); C2 0x820c0 `jal` malloc(pod) (a0 = len + (len == 0) from
   0x820b4 .. 0x820bc); C3 0x820c4 `beqz a0`; C4 0x82478 `mv a0,s2` after check_code's return (jal 0x82474), before
   the free(pod) jal 0x8247c. The live values at each cut are the ones every path reaching it sets and the code after
   it reads (register or R-relative cell, with where it is set): C1: a0 = pp (0x80190), s2 = 19744 (0x80188),
   s3 = (F >> 3) + K, s4 = 0x5000 (0x80184), s5 = the bytes left (0x80170 / 0x8017c), s6 = s9 = F, s7 = K,
   R+0x30 = fl (0x80168 / 0x80180), R+0xc8 = src (0x7ffec / 0x80174); C2 and C3: a0 = len + (len == 0) / pod,
   s3, s5 = pp+0x4000 (0x80238 / 0x80e60), s7 = K, s8 = len (0x820b4 / 0x81f74), s9 = F (0x81ef4), s10 = pp+0x4d18
   (0x81f3c), s11 = pp, R+0x8 = F, R+0x28 = F (0x80524), R+0x30 = fl, R+0x68 = (pp+0x4d14) >> 3 (0x8053c),
   R+0x78 = pp+0x4d14 (0x80534), R+0x80 = pp (0x80540); C4: s2 = pod (0x820c8), s3, s9 = F, s11 = pp, R+0x8 = F;
   and at every cut s0 = S, s1 = R. The frame's shadow bytes at C2 are the prologue's again (every granule M01 brings
   into scope, it puts back: e at 0x81858 / 0x81c98, t and ch at 0x80e18 .. 0x80e50, r at 0x80d10); at C4 the role
   granule 0x30 is 0x04 (0x820ec), and the epilogue resets it (0x8248c). M01 writes the pp block, the frame objects
   [F+0x20, F+0x180), their shadow bytes and the real-frame cells [R, R+0x138); M02 writes the pod block, role
   [F+0x180, F+0x184), granule 0x30, the cells [R+0xd8, R+0x100) (spills around strcmp, 0x822b8 .. 0x822cc) and
   [R+0x118, R+0x120) (flag: 0x82300, and pod_nearest's store). The real-frame cells R+0x118 and R+0x120 are the
   two the code shadow-checks (0x80d64 .. 0x80d7c; pod_nearest 0x82dbc .. 0x82dc8). The globals are the 49 rows of
   asan_globals (its own section at 0x9f0e0, 0xc40 bytes; none has an ODR indicator); the strings are the ones the harness's
   strlen / strcmp / memcpy calls and its callees read (each a registered global of size length + 1; 0x21120 is
   ent_build.s, the 14-byte source of case 9's memcpy at 0x811ac); the cells are
   reac_role_prop_parse's three doubles (0.5, -2^31, 2^31), reac_role_refuse_code's two table entries, and the 31
   pointer cells of .data.rel.ro the harness loads with `ld` (vocab[i] at 0x81298: 0x9a500 + 8 i, 9 cells; odd_ch[k]
   at 0x813e8: 0x9a580 + 8 k, 14 cells; param[k] for case 0's parts at 0x80d74: 0x9a620 + 8 k, 8 cells), each the
   address of one of the strings above. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
Import ListNotations.
Local Open Scope Z_scope.

(* The frame's shadow bytes after the prologue (52 granules of the 0x1a0-byte frame), and at C4. *)
Definition role_A_shA : list Z :=
  [0xf1; 0xf1; 0xf1; 0xf1;
   0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8;
   0xf2; 0xf2; 0xf2; 0xf2;
   0xf8; 0xf8; 0xf8;
   0xf2; 0xf2; 0xf2; 0xf2; 0xf2;
   0xf8;
   0xf2;
   0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8; 0xf8;
   0xf2; 0xf2; 0xf2; 0xf2; 0xf2;
   0xf8;
   0xf3; 0xf3; 0xf3].
Definition role_A_shB : list Z := firstn 48 role_A_shA ++ [0x04] ++ skipn 49 role_A_shA.

(* The strings (address, text without the NUL), the 49 registered globals (address, size) and the cells. *)
Definition role_A_strs : list (Z * list Z) := [
  (0x20ec0, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116; 101]) (* reac.cfg.rate *);
  (0x20ee0, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 111; 108; 101]) (* reac.cfg.role *);
  (0x20f00, [114; 101; 97; 99; 46; 104; 101; 97; 100; 97; 109; 112; 46]) (* reac.headamp. *);
  (0x20f20, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116; 101; 32]) (* reac.cfg.rate and a space *);
  (0x20f40, [82; 69; 65; 67; 46; 99; 102; 103; 46; 114; 97; 116; 101]) (* REAC.cfg.rate *);
  (0x20f60, [115; 111; 109; 101; 46; 111; 116; 104; 101; 114; 46; 99; 111; 110; 116; 114; 111; 108]) (* some.other.control *);
  (0x20fa0, [114; 101; 97; 99; 46; 104; 101; 97; 100; 97; 109; 112]) (* reac.headamp *);
  (0x20fc0, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 111; 108; 101; 46; 120]) (* reac.cfg.role.x *);
  (0x20fe0, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116]) (* reac.cfg.rat *);
  (0x21120, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 97; 116; 101]) (* reac.cfg.rate, ent_build.s *);
  (0x21140, [45; 49]) (* -1 *);
  (0x21160, [43; 51]) (* +3 *);
  (0x21180, [32; 55]) (* space 7 *);
  (0x211a0, [48; 55]) (* 07 *);
  (0x211c0, [57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57]) (* twenty 9s *);
  (0x21200, []) (* the empty string *);
  (0x21220, [120]) (* x *);
  (0x21240, [51; 97]) (* 3a *);
  (0x21260, [45; 48]) (* -0 *);
  (0x21280, [9; 53]) (* tab 5 *);
  (0x212a0, [52; 56]) (* 48 *);
  (0x212c0, [52; 55]) (* 47 *);
  (0x212e0, [48; 120; 49]) (* 0x1 *);
  (0x21300, [45; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57; 57]) (* minus twenty 9s *);
  (0x21340, [112; 104; 97; 110; 116; 111; 109]) (* phantom *);
  (0x21360, [112; 97; 100]) (* pad *);
  (0x21380, [115; 101; 110; 115]) (* sens *);
  (0x213a0, [80; 65; 68]) (* PAD *);
  (0x213c0, [115; 101; 110; 115; 120]) (* sensx *);
  (0x213e0, [112; 104; 97; 110; 116; 111; 109; 46; 120]) (* phantom.x *);
  (0x21400, [115; 101; 110; 115; 32]) (* sens and a space *);
  (0x21420, [46]) (* a dot *);
  (0x215a0, [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 111; 108; 101]) (* reac.cfg.role, the parse's key *);
  (0x21480, [97; 112; 112; 108; 105; 101; 100]) (* applied, check_answer *);
  (0x21440, [114; 111; 108; 101; 95; 114; 101; 101; 115; 116; 97; 98; 108; 105; 115; 104; 95; 112; 101; 110; 100; 105; 110; 103]) (* role_reestablish_pending, check_answer *);
  (0x214a0, [110; 111; 110; 101]) (* none, check_code *);
  (0x214c0, [109; 97; 108; 102; 111; 114; 109; 101; 100]) (* malformed, check_code *);
  (0x21580, [97; 112; 112; 108; 105; 101; 100]) (* applied, apply_state *);
  (0x21540, [114; 111; 108; 101; 95; 114; 101; 101; 115; 116; 97; 98; 108; 105; 115; 104; 95; 112; 101; 110; 100; 105; 110; 103]) (* role_reestablish_pending, apply_state *);
  (0x21500, [110; 111; 110; 101]) (* none, refuse_code codes[0] *);
  (0x21520, [109; 97; 108; 102; 111; 114; 109; 101; 100]) (* malformed, refuse_code codes[1] *)
].
Definition role_A_globs : list (Z * Z) := [
  (0x20ec0, 14); (0x20ee0, 14); (0x20f00, 14); (0x20f20, 15); (0x20f40, 14); (0x20f60, 19); (0x20fa0, 13);
  (0x20fc0, 16); (0x20fe0, 13); (0x21000, 56); (0x21060, 84); (0x210e0, 16); (0x21100, 16); (0x21120, 14);
  (0x21140, 3); (0x21160, 3); (0x21180, 3); (0x211a0, 3); (0x211c0, 21); (0x21200, 1); (0x21220, 2);
  (0x21240, 3); (0x21260, 3); (0x21280, 3); (0x212a0, 3); (0x212c0, 3); (0x212e0, 4); (0x21300, 22);
  (0x21340, 8); (0x21360, 4); (0x21380, 5); (0x213a0, 4); (0x213c0, 6); (0x213e0, 10); (0x21400, 6);
  (0x21420, 2); (0x21440, 25); (0x21480, 8); (0x214a0, 5); (0x214c0, 10); (0x21500, 5); (0x21520, 10);
  (0x21540, 25); (0x21580, 8); (0x215a0, 14); (0x9a500, 72); (0x9a580, 112); (0x9a620, 64); (0x9a680, 16)
].
Definition role_A_cells : list (Z * Z) := [
  (0x10378, 0x3fe0000000000000); (0x103e0, 0xc1e0000000000000); (0x10330, 0x41e0000000000000);
  (0x9a680, 0x21500); (0x9a688, 0x21520);
  (0x9a500, 0x20ec0); (0x9a508, 0x20ee0); (0x9a510, 0x20f00); (0x9a518, 0x20f20); (0x9a520, 0x20f40);
  (0x9a528, 0x20f60); (0x9a530, 0x20fa0); (0x9a538, 0x20fc0); (0x9a540, 0x20fe0);
  (0x9a580, 0x21140); (0x9a588, 0x21160); (0x9a590, 0x21180); (0x9a598, 0x211a0); (0x9a5a0, 0x211c0);
  (0x9a5a8, 0x21200); (0x9a5b0, 0x21220); (0x9a5b8, 0x21240); (0x9a5c0, 0x21260); (0x9a5c8, 0x21280);
  (0x9a5d0, 0x212a0); (0x9a5d8, 0x212c0); (0x9a5e0, 0x212e0); (0x9a5e8, 0x21300);
  (0x9a620, 0x21340); (0x9a628, 0x21360); (0x9a630, 0x21380); (0x9a638, 0x213a0); (0x9a640, 0x213c0);
  (0x9a648, 0x21200); (0x9a650, 0x213e0); (0x9a658, 0x21400)
].

(* Register numbers: s0 = 8, s1 = 9, a0 = 10, s2 .. s11 = 18 .. 27. *)
Definition role_A_L23 (a0 : rl_x) : list (rl_loc * rl_x) :=
  [(LReg 10, a0); (LReg 8, XS); (LReg 9, XR); (LReg 19, XShF); (LReg 21, XPp 0x4000); (LReg 23, XC SHADOW_OFF);
   (LReg 24, XLen); (LReg 25, XF); (LReg 26, XPp 0x4d18); (LReg 27, XPp 0);
   (LCell XR 0x8, XF); (LCell XR 0x28, XF); (LCell XR 0x30, XFl); (LCell XR 0x68, XPpShr 0x4d14);
   (LCell XR 0x78, XPp 0x4d14); (LCell XR 0x80, XPp 0)].

Definition role_himg_A : rl_himg := {|
  hi_cid := 3;
  hi_c1 := 0x80194; hi_c2 := 0x820c0; hi_c3 := 0x820c4; hi_c4 := 0x82478;
  hi_rsz := 0x1a0;
  hi_L1 := [(LReg 10, XPp 0); (LReg 8, XS); (LReg 9, XR); (LReg 18, XC 19744); (LReg 19, XShF);
            (LReg 20, XC 0x5000); (LReg 21, XLeft); (LReg 22, XF); (LReg 23, XC SHADOW_OFF); (LReg 25, XF);
            (LCell XR 0x30, XFl); (LCell XR 0xc8, XSrc)];
  hi_L2 := role_A_L23 XLenNZ;
  hi_L3 := role_A_L23 XPod;
  hi_L4 := [(LReg 18, XPod); (LReg 8, XS); (LReg 9, XR); (LReg 19, XShF); (LReg 25, XF); (LReg 27, XPp 0);
            (LCell XR 0x8, XF)];
  hi_shA := role_A_shA; hi_shB := role_A_shB;
  hi_w1 := [(XF, 0x20, 0x160); (XShF, 0, 52); (XR, 0, 0x138)];
  hi_w2 := [(XF, 0x180, 4); (XShF, 0x30, 1); (XR, 0xd8, 0x28); (XR, 0x118, 8)];
  hi_rz := [(0x118, 16)];
  hi_globs := role_A_globs;
  hi_strs := role_A_strs;
  hi_cells := role_A_cells |}.

(* The key literal the parse and the harness's strcmp read is Role.ROLE_KEY's text. *)
Lemma role_A_key_text : map (fun x : byte => bv_unsigned x) Role.ROLE_KEY =
  [114; 101; 97; 99; 46; 99; 102; 103; 46; 114; 111; 108; 101].
Proof. vm_compute. reflexivity. Qed.
