(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v aj_intrin_at (lines 2155-2206) restated for image A's code with the callee's same_but_materialized kept as same_io in the post. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW8Call.v at 888d1ffb4c3 for reac-pw/fuzz_headamp image A: module paths changed, w_intrin_at renamed hd_intrin_at, role's RPgCfgChanges.cfg_segs_low replaced by HPgSteps.img_segs_low over headamp's segments; the two instances hd_memset_at / hd_memcpy_at are new. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgIntrin.v at 021dba8dbbd; hd_intrin_at renamed cb_intrin_at and stated over image B's segments (lib/AU/Img0U.v rsegs, lib/AU/HPgSteps.v img_segs_low, AR_laws from YG0q.AR_laws_ok), hd_memset_at / hd_memcpy_at renamed cb_memset_at / cb_memcpy_at with the entry pc made a parameter (image B's entries CB_ASAN_MEMSET 0x52228 and CB_ASAN_MEMCPY 0x51d8c stated as constants). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6cKit.v at 80bf14ccf11 (PART 1, a segment's start facts at a cut); rs_ -> cb_, restated over lib/AU/HPgSeg.v (hsu_pre, hsu_core, hsu_E1, hsu_in, hsu_fsh_at) at image B's record headamp_himg_B: the frame for locals of class 4 (1024 bytes, 128 shadow bytes), the 116-byte prologue pattern in place of role's 52, R + 0x220 in place of 0x1a0, image B's three write ranges of hi_w1, the image fact segs_low taken from lib/AU/HPgSteps.v img_segs_low instead of a Section hypothesis. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aBase.v at 80bf14ccf11 (w6_ctx, w6_caller_saved and Section seq only; w6_in as cb_in); w6_ -> cb_, the frame (4, pos) and R + 0x220 of image B, R's cells [R, R + 0x198), and the block post w6_post replaced by the shared layer's hdu_blk_postE (lib/AU/HPgSteps.v), rl_blk_post by hdu_blk_post. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6a.v at 80bf14ccf11 (its generic helpers only: the list tactics, the register and location-list lemmas, the geometry of a cut, the image's first write range, the suffix and cursor lemmas, pp's image length, the cut's geometry and context, the core step, the input kept, the block step and the side tactics); w6_ -> cb_, over lib/AU/HPgSeg.v at image B: w6_geo with image B's frame (1024 / 128 bytes, R + 0x220) and the conjuncts F mod 32 = 0 and in_app pp, its head- and tail-specific cell lemmas replaced by write-set-free disjointness lemmas, w6_in_kept and the side tactics generalised over the write set, cb_blkE_step added for a block that writes. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aHead.v at 80bf14ccf11 (w6h_div, w6h_sh_e, w6h_e_mod8, w6h_bounds, w6h_callee, w6h_val_kept, w6h_chunk0, w6h_region_nth, w6h_chunks); w6h_ -> cb_, the shadow and alignment lemmas generalised over the offset, the bounds at class 4 (1024 bytes, 128 shadow bytes) and e62's 104 bytes at F + 0x210. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW7bBase.v at f3898085bda (w7_post,
   w7_post_of_run), RPgW7bKit.v at f3898085bda (w7_kept, w7_hull, w7_ra_kept, w7_hull_kept, w7_strok, w7_strz and
   their lemmas), RPgCfgChanges.v at f3898085bda (kept_run), RPgW6aTail.v at f3898085bda (tl_byte, tl_val_of_chunk,
   tl_val_at), RPgW6aC2h.v at f3898085bda (c2_all256, c2_envz, c2_nz, c2_notin, c2_kio) and RPgW7bIter.v at
   f3898085bda (w7_cs_bv, w7_cs_out, w7_reg_eq), by way of lib/AU/HPgW6bC1k.v's and
   HPgW6bC1.v's hb1_* copies for reac-pw/fuzz_headamp's image B: moved here and renamed cb_* by the dedup, one copy
   kept for the equal helpers of 17 lib/AU files (HPgE0Base, HPgW7bBase, HPgW7bIter, HPgW6aTail, HPgW6aC2 and
   others); cb_val_at_rng is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgCaseB.v, with its module paths, module names, addresses and numbers changed; 137 of its 170 lines of code are new or changed and 1056 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6aBase.v at 8608e43486c0 for reac-pw/fuzz_rate's
   image A: module paths changed; the image is fuzz_rate.asan (images.Asan) instead of a lib/A/Img0 module; every pc,
   table address and frame cell is rate's (measured below); the registers are rate's (the cursor stays in s9, what is
   left of the input is the register s8, a5 holds what was left before the kind byte, s6 the sign-extended kind byte
   and later the shadow address the cases reload, s2 the shadow offset, s4 the frame's shadow base); the frame's
   shadow pattern has 56 bytes; the case tail writes no real-frame cell (in.n goes to s8); the post of a writing
   block and the chaining lemmas are RtPgSteps.v's rts_post / rts_post_seq / rts_blk_seq (not restated here). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6aBase.v at 98e12166692a for the same unit's
   image B (fuzz_rate.asan-ubsan): images.AsanUbsan and lib/AU/RtPgStepsB.v instead of images.Asan and RtPgSteps.v;
   every pc is image B's; the pod object is e62 at F + 0x210 (its address in s6 at C, in the cell R+0x150 for the
   cases) and the pod index cell is R+0x178; the frame is class 4 (1024 bytes, 88 prologue shadow bytes, e62's
   granules 66 .. 78) and the real frame 0x220 bytes; the cursor is s10 at C and s2 after the kind byte, what is left
   s9 at C and s6 / t1 after it, the shadow offset s4 and the frame's shadow base s3; the kind block also passes a
   pointer-overflow test (`bltu a6,s2`); the case heads end at the u32 block's start or at the tail's second pc
   (a4 = 4 already set), and the tail has four entries (two per case) and ends by reloading s2 from R+0x158. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgW6aBaseB.v at 265bf27a1874 for
   reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths changed (lib/AU/Img0.rsegs, lib/A/RPgBase and
   RPgCSpec, lib/AU/RPgSteps.v's rl_ names); every pc and table address is role B's; the real frame is 0x200 bytes;
   the pod index cell is R+0x150 and the address of e62 is the cell R+0x158 (the head reads it); in the pod loop the
   cursor is s8, what is left s2 and the trap tests' 1 is s4, the shadow offset s11; after the kind byte s8 and a6
   hold its address, s2 the cursor after it, t1 / s6 what is left before / after it and t2 = 10; the case heads load
   s6 := [R+0x130] (pp + 0x4000), case 3's head also a5 := [R+0x140] (pp); case 3's head ends past the reload of a5
   (0x818bc); the tail reads [R+0x140] and [R+0x158], leaves a5 = pp, a0 = &e62, t1 = in.n, a3 = the cursor. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the BLOCK STATEMENTS of the
   walk piece "ent_build A" of LLVMFuzzerTestOneInput (0x80020): the pod loop's head C (0x80b54) to the dispatch of
   ent_build's `switch (kind % 10)` (pod.h:279-281), and the cases 2 and 3 (pod.h:298-324) to the join J (0x818d8).
   Statement text only: no function is proved here (kind: segment lemma).

   WHY BLOCKS. The piece is cut at the points where the code calls something (the memset of e62 at 0x80b98, the
   fuzz_u32 read-ahead blocks of lib/AU/RPgSteps.v, the jump table block rl_jt_block of the same file) and at the
   tail of each case. Each block is stated over the machine state it starts from (its registers, the 8-byte frame
   cells it reads, the input bytes) in the shape of a callee contract, so that the blocks are proved independently and
   the piece is their chaining with SRr_bind:
     w6b_head  C 0x80b54 .. 0x80b98 + the memset call: k into [R+0x150], e62's 13 shadow granules := 0,
               e62 := 0^104 (its address read from [R+0x158]); returns at 0x80b9c.
     w6b_kind  0x80b9c .. the case entry: in.n = 0 goes to D0E 0x80c88; else the pointer-overflow test of the
               cursor (`bltu s4,s2` 0x80bac, s4 = 1), its instrumented check, the kind byte, kind % 10 (0xcd multiply,
               0x80bcc .. 0x80be0), case 9 to 0x812d4 by `bltu` 0x80bec, cases 0 .. 8 through rl_jt_block (0x80bf0).
     w6b_c2h   case 2's head 0x80f88: m = fuzz_u8; m odd stops at 0x81658 (the fuzz_u32 block's start), m even (or
               no byte) loads ints[(m >> 1) % 14] and stops at 0x81834.
     w6b_c3h   case 3's head 0x80ffc: m odd stops at 0x81694; else NaN (m = 0xfe), inf (m = 0xfc) or
               floats[(m >> 1) % 21], stopping at 0x818bc.
     w6b_tail  0x81830 / 0x81834 (case 2, type 4) and 0x818b4 / 0x818bc (case 3, type 6) .. J 0x818d8: e62.type,
               e62.size = 4, e62.body[0..4) := the value, t1 := in.n, a3 := the cursor, a5 := [R+0x140].
   THE REGISTERS (checked against the code): s1 = R (x9) the real frame's base, s3 = shadow_addr F (x19),
   s11 = SHADOW_OFF (x27); in the pod loop the cursor in.p is s8 (x24), in.n is s2 (x18) and s4 (x20) = 1 the left side
   of the pointer-overflow tests (0x809f0); after the kind read s8 = a6 (x16) = c - 1 is the kind byte's address,
   s2 = c the cursor after it, t1 (x6) the in.n of the kind read, s6 (x22) = in.n - 1 and t2 (x7) = 10. The cases
   reload s6 from [R+0x130] = pp + 0x4000 (case 3 also a5 from [R+0x140] = pp), and the tail reads e62's address
   F + 0x210 from [R+0x158]. *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Cursor Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================== the pcs ======================================== *)
Definition W6B_C : Z := 0x80b54.       (* `sd a1,0x150(s1)`: the pod loop's head *)
Definition W6B_MEMSET : Z := RL_MEMSET. (* checked_memset 0x51608, the `jal` target at 0x80b98 *)
Definition W6B_RET : Z := 0x80b9c.     (* after the memset of e62: `beqz s2` *)
Definition W6B_D0E : Z := 0x80c88.     (* case 0 with no input left (`beqz s2` 0x80b9c taken) *)
Definition W6B_D9 : Z := 0x812d4.      (* case 9 (`bltu a2,a1` 0x80bec taken) *)
Definition W6B_D2 : Z := 0x80f88.
Definition W6B_D3 : Z := 0x80ffc.
Definition W6B_U2 : Z := 0x81658.      (* case 2's fuzz_u32 block (RPgSteps rl_u32_block2) .. 0x81830 *)
Definition W6B_U3 : Z := 0x81694.      (* case 3's fuzz_u32 block (RPgSteps rl_u32_block3) .. 0x818b4 *)
Definition W6B_TA2 : Z := 0x81830.     (* case 2's tail from the u32 block: `li a4,4` *)
Definition W6B_TB2 : Z := 0x81834.     (* case 2's tail from its head: `ld a5,0x140(s1)`, a4 = 4 *)
Definition W6B_TA3 : Z := 0x818b4.     (* case 3's tail from the u32 block: `li a4,4` *)
Definition W6B_TB3 : Z := 0x818bc.     (* case 3's tail from its head: `ld a0,0x158(s1)`, a4 = 4, a5 = pp *)
Definition W6B_J : Z := 0x818d8.       (* the join: the capacity guard, then the call pod_write_ent(pp, e62) *)
(* the tables the cases read (registered globals, .rodata): ints[14] at 0x21040, floats[21] at 0x210a0 *)
Definition W6B_INTS : Z := 0x21040.
Definition W6B_FLOATS : Z := 0x210a0.

(* ======================================== the code table ========================================
   Every instruction word of [0x80b54, 0x81b98): the pod loop (the dispatch, the ten cases' fast paths with the
   fuzz_u32 read-ahead of cases 2 and 3, the join and the record's write) and the slow blocks of its checks (0x81a1c ..
   0x81b94). All 1041 words are 4 bytes long. 0x81b98 is SELI, the next piece. The `unimp` 0x82604 and the report
   calls past 0x82600 are never stepped. Precomputed once. *)
Definition W6B_TLO : Z := 0x80b54.
Definition W6B_TN : nat := 1041.
Definition w6b_tbl : ctable := Eval vm_compute in build_table rsegs W6B_TLO W6B_TN TEmpty.
Lemma w6b_tbl_ok : table_ok rsegs w6b_tbl.
Proof.
pose proof (build_table_ok0 rsegs W6B_TN W6B_TLO ltac:(unfold W6B_TLO; lia)) as H.
assert (E : build_table rsegs W6B_TLO W6B_TN TEmpty = w6b_tbl) by (vm_compute; reflexivity).
rewrite E in H. exact H.
Qed.

(* ======================================== the model's values ======================================== *)
(* kind % 10 as the code computes it (case 9 by the branch, cases 0 .. 8 by the table) *)
Definition w6b_case_pc (kd : Z) : Z := if kd mod 10 =? 9 then W6B_D9 else jt_tgt (kd mod 10).
(* the registers the kind block may write (t1, t2, a0, a1, a2, a3, a6, s2, s6) *)
Definition w6b_kind_clob : list (bv 5) := [6; 7; 10; 11; 12; 13; 16; 18; 22]%bv.
(* the registers a case head may write (a0 .. a5, s2, s6) *)
Definition w6b_head_clob : list (bv 5) := [10; 11; 12; 13; 14; 15; 18; 22]%bv.
(* the registers the tail may write (t1, a0, a3, a4, a5) *)
Definition w6b_tail_clob : list (bv 5) := [6; 10; 13; 14; 15]%bv.
(* case 2's int when m is even (ints[(m >> 1) % 14]; with no byte left m = 0 and ints[0]) *)
Definition w6b_int_even (m : Z) : Z := nth (Z.to_nat ((m / 2) mod 14)) Tables.ints 0.
(* case 3's bits when m is even: NaN, inf, or floats[(m >> 1) % 21] (Model.ent_build's case 3) *)
Definition w6b_float_even (m : Z) : Z :=
if m / 2 =? 127 then 0x7fc00000
else if m / 2 =? 126 then (if Z.testbit m 1 then 0xff800000 else 0x7f800000)
else nth (Z.to_nat ((m / 2) mod 21)) Tables.float_bits 0.
(* the tail's start pc: per case (c3), from the u32 block (a = true) or from the head (a = false, a4 = 4 set) *)
Definition w6b_tail_pc (c3 a : bool) : Z :=
if c3 then (if a then W6B_TA3 else W6B_TB3) else (if a then W6B_TA2 else W6B_TB2).

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation u8s l := (map (fun x : byte => bv_unsigned x) l).

(* ===================== the context every block runs in =====================
   The harness's journal from the segment's start (rl_seg_pre's first conjunct), the real frame [R, R + 0x200)
   (hi_rsz) inside the journal's stack window with the callees' stack below it, the frame for locals F = the
   side-stack frame (4, pos) the harness holds, and the read-only segments as in the image (rl_seg_pre's
   rom_view). *)
Definition w6b_ctx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (R F pos : Z) : Prop :=
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
R mod 16 = 0 /\ R + 0x200 <= sp0 /\ sp0 - STK <= R - T_SEG_STK /\
In (4, pos) own /\ F = frame_addr lyc 4 pos /\
rom_view rsegs W memc.

(* ===================== w6b_head: C 0x80b54 .. the memset of e62, back at 0x80b9c =====================
     0x80b54  sd a1,0x150(s1)                      [R+0x150] := k (the pod index)
     0x80b58 .. 0x80b88  13 x sb zero,o(s3)        shadow_addr F + 66 .. 78 := 0 (e62 in scope, pod.h:426), in the
                                                   order 70 71 72 73 66 67 68 69 74 75 76 77 78
     0x80b8c  a2 := 104; 0x80b90 ld a0,0x158(s1) (= F + 0x210); 0x80b94 a1 := 0
     0x80b98  jal checked_memset (0x51608)         e62 := 104 zero bytes (pod.h:279), returns a0 = F + 0x210
   The memset is the kernel's aintrin_realizes OSet (lib/Reusable/YG0d.v), a hypothesis of the proof. Wr: the
   callee's stack [R - ESTACK, R), the cell [R+0x150, R+0x158), the 13 granules and e62. *)
Definition w6b_head_wr (R F : Z) : Z -> Prop :=
fun a => (R - ESTACK <= a < R) \/ (R + 0x150 <= a < R + 0x158) \/
(shadow_addr F + 66 <= a < shadow_addr F + 79) \/ (F + 0x210 <= a < F + 0x278).
Definition w6b_head_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos kk : Z),
w6b_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 19 = w64 (shadow_addr F) ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 11 = w64 kk ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x158) 8 (F + 0x210) ->
SRr rsegs W (cfg_at rsegs W6B_C regs memc mdc)
(rl_wpost B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_RET rl_caller_saved (w6b_head_wr R F)
(fun W2 regs2 mem2 =>
getr regs2 10 = w64 (F + 0x210) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x150) 8 (kk mod 2 ^ 64) /\
(forall i, 0 <= i < 13 -> aview rsegs (w_H W2) mem2 (shadow_addr F + 66 + i) = Some 0) /\
(forall i, 0 <= i < 104 -> aview rsegs (w_H W2) mem2 (F + 0x210 + i) = Some 0))).

(* the input bytes r at cursor cur, as role_build_contract gives them (garr8, range_addressable, 0 < src,
   src + left <= 2 ^ 63, amem_range) and outside the callees' stack below R and the real frame's cells the blocks
   read or write, [R + 0x130, R + 0x160) (inside RPgImgA hi_w1's (XR, 0x48, 0x118); RPgSeg rs_in) *)
Definition w6b_in (W : world rsegs) (memc : word -> option byte) (R cur : Z) (r : list byte) : Prop :=
garr8 rsegs (mrestrict (w_H W) memc) cur (u8s r) /\
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur (Z.of_nat (length r)) /\
0 < cur /\ cur + Z.of_nat (length r) <= 2 ^ 63 /\ amem_range cur (Z.of_nat (length r)) /\
(forall a, cur <= a < cur + Z.of_nat (length r) ->
 ~ (R - T_SEG_STK <= a < R) /\ ~ (R + 0x130 <= a < R + 0x160)).

(* ===================== w6b_kind: 0x80b9c .. the case entry (no store) =====================
     0x80b9c  beqz s2 -> 0x80c88                    in.n = 0: kind = 0, case 0 with nothing read
     0x80ba0  t1 := s2; s2 := s8 + 1; t2 := 10; 0x80bac bltu s4,s2 -> 0x80bb4 (else 0x80bb0 j 0x82604: never,
              cur > 0 and s4 = 1)
     0x80bb4  a6 := s8; 0x80bb8 .. 0x80bc4 the instrumented check of s8 (slow block 0x81a1c, back to 0x80bc8)
     0x80bc8  lbu a0,0(a6); 0x80bcc .. 0x80be0 a1 := kind % 10 (a1 = (kind * 0xcd) >> 11, `mul t2`, `subw`,
              `zext.b`)
     0x80be4  s6 := t1 - 1; a2 := 8; 0x80bec bltu a2,a1 -> 0x812d4 (case 9)
     0x80bf0 .. 0x80c10  rl_jt_block (lib/AU/RPgSteps.v) to jt_tgt (kind % 10).
   The cursor is s8 = cur and the input left is r (s2 = |r|). On a case entry s2 = cur + 1, a6 = cur,
   t1 = |r'| + 1, s6 = |r'| and t2 = 10 (r = b :: r'); s8 is unchanged (the kind byte's address). *)
Definition w6b_kind_R (kd cur nl' : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 18 = w64 (cur + 1) /\ getr regs2 16 = w64 cur /\ getr regs2 6 = w64 (nl' + 1) /\
getr regs2 22 = w64 nl' /\ getr regs2 7 = w64 10 /\
(if kd mod 10 =? 9 then getr regs2 12 = w64 8
 else bv_unsigned (getr regs2 10) = (kd mod 256) * 2 ^ 56 /\ getr regs2 12 = w64 JT_A /\
      getr regs2 13 = w64 (sext8 kd)).
Definition w6b_kind_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos cur : Z) (r : list byte),
w6b_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 27 = w64 SHADOW_OFF -> getr regs 24 = w64 cur -> getr regs 18 = w64 (Z.of_nat (length r)) ->
getr regs 20 = w64 1 ->
w6b_in W memc R cur r ->
SRr rsegs W (cfg_at rsegs W6B_RET regs memc mdc)
(fun W2 c2 =>
 (r = [] /\
  rl_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_D0E [] (fun _ => True) W2 c2) \/
 (exists b r', r = b :: r' /\
  rl_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (w6b_case_pc (bv_unsigned b))
  w6b_kind_clob (w6b_kind_R (bv_unsigned b) cur (Z.of_nat (length r'))) W2 c2)).

(* ===================== w6b_c2h / w6b_c3h: a case's head (no store) =====================
   At the case entry (w6b_kind's post): s2 = c (the cursor after kind), s6 = |r| (in.n after kind), a6 = c - 1,
   t1 = |r| + 1 (in.n of the kind read), s4 = 1, [R+0x130] = v6, [R+0x140] = v5. m = fuzz_u8 r.
   case 2 (pod.h:298-303):
     0x80f88 beqz s6 -> 0x81364 (m = 0: a2 := 0, a1 := 0x21040, then the table load at 0x81370);
     0x80f8c .. 0x80f90 the pointer-overflow test of s2 (`bltu s4,a0`, other arm 0x80f94 `j 0x82604`); 0x80f98 ..
     0x80fa4 its instrumented check (slow block 0x81aa4); 0x80fa8 lbu a1 = m; a2 := t1 - 2; a3 := m & 1;
     s2 := a6 + 2; 0x80fb8 bnez a3 -> 0x81654 (m odd: s6 := [R+0x130], stop at 0x81658, exactly rl_u32_block2's
     premises: a2 = |r'|, s2 = c + 1, a6 = c - 1, t1 = |r'| + 2, s4 = 1, s11 = SHADOW_OFF);
     m even: 0x80fbc .. 0x80ff8 a1 := 0x21040 + 4 ((m >> 1) % 14) (mulhu by the constant at 0x10318; the
     out-of-range test `not a4,a1; bgeu a4,a3` 0x80fe8 / 0x80fec whose other arm 0x80ff0 is `j 0x82604`), then
     0x81370 .. 0x8138c: the instrumented check of the 4 bytes at a1 (slow block 0x81a60), s6 := [R+0x130],
     a4 := 4, `lw a1`; stop at 0x81834.
   case 3 (pod.h:304-324): 0x80ffc, the same read (m = 0: 0x81390 a2 := 0, a1 := 0x210a0, the table load at
     0x817a0; s6 := [R+0x130] and a5 := [R+0x140] inside the check of s2 at 0x81018 / 0x8101c); m odd: stop at
     0x81694; m = 0xfe: a1 := 0x7fc00000 (0x81760); m = 0xfc: a1 := 0x7f800000 (0x81048); both through 0x81764
     (a4 := 4) to 0x818bc; else 0x8176c .. 0x8179c a1 := 0x210a0 + 4 ((m >> 1) % 21) (mulhu by the constant at
     0x10310, the out-of-range test `not a4,a1; bltu a4,a3` 0x81794 / 0x81798 to 0x82604), 0x817a0 .. 0x817b8 the
     check of the 4 bytes (slow block 0x81b04, reached at floats[20]), s6 := [R+0x130], a4 := 4, `lw a1`;
     0x818b8 a5 := [R+0x140]; stop at 0x818bc.
   The value is given mod 2 ^ 32 (`lw` sign-extends; the tail stores its low 4 bytes). *)
Definition w6b_head_in (W : world rsegs) (memc : word -> option byte) (regs : bvmap 5 word) (R c v6 v5 : Z)
(r : list byte) : Prop :=
getr regs 9 = w64 R /\ getr regs 27 = w64 SHADOW_OFF /\ getr regs 18 = w64 c /\
getr regs 22 = w64 (Z.of_nat (length r)) /\ getr regs 16 = w64 (c - 1) /\
getr regs 6 = w64 (Z.of_nat (length r) + 1) /\ getr regs 20 = w64 1 /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 v6 /\ 0 <= v6 < 2 ^ 64 /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x140) 8 v5 /\ 0 <= v5 < 2 ^ 64 /\
0 < c - 1 /\ w6b_in W memc R c r.
Definition w6b_case_head_stmt (c3 : bool) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c v6 v5 : Z)
  (r : list byte),
w6b_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6b_head_in W memc regs R c v6 v5 r ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (if c3 then W6B_FLOATS else W6B_INTS) (if c3 then 84 else 56) ->
SRr rsegs W (cfg_at rsegs (if c3 then W6B_D3 else W6B_D2) regs memc mdc)
(fun W2 c2 =>
 let mv := fst (Cursor.fuzz_u8 r) in let r1 := snd (Cursor.fuzz_u8 r) in
 if Z.odd mv then
  rl_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if c3 then W6B_U3 else W6B_U2)
  w6b_head_clob
  (fun regs2 => getr regs2 12 = w64 (Z.of_nat (length r1)) /\ getr regs2 18 = w64 (c + 1) /\
     getr regs2 22 = w64 v6) W2 c2
 else
  rl_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if c3 then W6B_TB3 else W6B_TB2)
  w6b_head_clob
  (fun regs2 => (exists v, getr regs2 11 = w64 v /\
       v mod 2 ^ 32 = (if c3 then w6b_float_even mv else w6b_int_even mv) mod 2 ^ 32) /\
     getr regs2 14 = w64 4 /\
     getr regs2 12 = w64 (Z.of_nat (length r1)) /\
     getr regs2 18 = w64 (c + Z.of_nat (length r - length r1)) /\ getr regs2 22 = w64 v6 /\
     (if c3 then getr regs2 15 = w64 v5 else True)) W2 c2).
Definition w6b_c2h_stmt : Prop := w6b_case_head_stmt false.
Definition w6b_c3h_stmt : Prop := w6b_case_head_stmt true.

(* ===================== w6b_tail: 0x81830 / 0x81834 / 0x818b4 / 0x818bc .. J 0x818d8 =====================
     0x81830  li a4,4                                                     (case 2 from the u32 block)
     0x81834  ld a5,0x140(s1); ld a0,0x158(s1); sw a4,0(a0) (e62.type = POD_INT, a4 = 4); j 0x818c8
                                                                          (case 2 from its head)
     0x818b4  li a4,4; 0x818b8 ld a5,0x140(s1)                            (case 3 from the u32 block)
     0x818bc  ld a0,0x158(s1); li a3,6; sw a3,0(a0) (e62.type = POD_FLOAT) (case 3 from its head, a5 set)
     0x818c8  sw a4,4(a0) (e62.size = 4); sw a1,8(a0) (e62.body[0..4) = the value); t1 := a2 (in.n);
              a3 := s2 (the cursor)                                       -> J 0x818d8
   e62 = F + 0x210 lies in the frame (4, pos) the harness owns. *)
Definition w6b_tail_wr (F : Z) : Z -> Prop := fun a => F + 0x210 <= a < F + 0x21c.
Definition w6b_tail_stmt (c3 a : bool) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos n' v cn v5 : Z),
w6b_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 9 = w64 R ->
getr regs 11 = w64 v -> getr regs 12 = w64 n' -> getr regs 18 = w64 cn ->
(if a then True else getr regs 14 = w64 4) ->
(if c3 && negb a then getr regs 15 = w64 v5 else True) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x140) 8 v5 -> 0 <= v5 < 2 ^ 64 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x158) 8 (F + 0x210) ->
SRr rsegs W (cfg_at rsegs (w6b_tail_pc c3 a) regs memc mdc)
(rl_wpost B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_J w6b_tail_clob (w6b_tail_wr F)
(fun W2 regs2 mem2 =>
getr regs2 6 = w64 n' /\ getr regs2 13 = w64 cn /\ getr regs2 15 = w64 v5 /\
getr regs2 10 = w64 (F + 0x210) /\ getr regs2 14 = w64 4 /\
val_mem rsegs (mrestrict (w_H W2) mem2) (F + 0x210) 4 (if c3 then 6 else 4) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (F + 0x214) 4 4 /\
val_mem rsegs (mrestrict (w_H W2) mem2) (F + 0x218) 4 (v mod 2 ^ 32))).

End d.
End b.
