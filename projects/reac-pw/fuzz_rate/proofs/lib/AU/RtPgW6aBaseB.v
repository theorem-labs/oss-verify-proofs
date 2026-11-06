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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgCaseB.v, with its module paths, module names and numbers changed; 133 of its 164 lines of code are new or changed and 1058 lines of the source are left out. *)
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
(* reac-pw/fuzz_rate image B (fuzz_rate.asan-ubsan, pinned sha256
   c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; every address measured on the unstripped twin
   a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1, same loaded bytes): the BLOCK STATEMENTS of the
   walk piece "ent_build A" of LLVMFuzzerTestOneInput (0x8076c): the pod loop's head C (0x813a0) to the dispatch of
   ent_build's `switch (kind % 10)` (pod.h:279-281), and the cases 2 and 3 (pod.h:298-324) to the join J (0x820dc).
   Statement text only: no function is proved here (kind: segment lemma).

   WHY BLOCKS. The piece is cut at the points where the code calls something (the memset of e62 at 0x813e4, the
   fuzz_u32 read-ahead blocks of lib/AU/RtPgStepsB.v, the jump table block rtsb_jt_block of the same file) and at the
   tail of each case. Each block is stated over the machine state it starts from (its registers, the 8-byte frame
   cells it reads, the input bytes) in the shape of a callee contract, so that the blocks are proved independently and
   the piece is their chaining with SRr_bind:
     w6b_head  C 0x813a0 .. 0x813e4 + the memset call: k into [R+0x178], e62's 13 shadow granules := 0,
               e62 := 0^104; returns at 0x813e8.
     w6b_kind  0x813e8 .. the case entry: in.n = 0 goes to D0E 0x814d0; else the pointer-overflow test of the
               cursor, its instrumented check, the kind byte, kind % 10 (0xcd multiply, 0x81414 .. 0x8142c), case 9 to
               0x81a94 by `bltu` 0x81438, cases 0 .. 8 through rtsb_jt_block (0x8143c).
     w6b_c2h   case 2's head 0x817c4: m = fuzz_u8; m odd stops at 0x81e58 (the fuzz_u32 block's start), m even (or
               no byte) loads ints[(m >> 1) % 14] and stops at 0x8203c.
     w6b_c3h   case 3's head 0x81838: m odd stops at 0x81e94; else NaN (m = 0xfe), inf (m = 0xfc) or
               floats[(m >> 1) % 21], stopping at 0x820c0.
     w6b_tail  0x82038 / 0x8203c (case 2, type 4) and 0x820bc / 0x820c0 (case 3, type 6) .. J 0x820dc: e62.type,
               e62.size = 4, e62.body[0..4) := the value, t1 := in.n, s10 := the cursor, s2 := [R+0x158].
   THE REGISTERS (checked against the code): s1 = R (x9) the real frame's base, s3 = shadow_addr F (x19),
   s4 = SHADOW_OFF (x20); at C the cursor in.p is s10 (x26), in.n is s9 (x25) and s6 (x22) = F + 0x210 the address of
   e62; after the kind read s10 = c - 1 is the kind byte's address, s2 (x18) = c the cursor after it, t1 (x6) the in.n
   of the kind read, s6 = in.n - 1 and a6 (x16) = 1 the left side of the pointer-overflow tests. The cases reload s6
   from [R+0x150] = F + 0x210, and the tail reloads s2 from [R+0x158] = pp + 0x4000. *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Cursor Tables.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.A Require Import RtPgBase RtPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.AU Require Import RtPgStepsB.
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* image B's loaded segments; an abbreviation, so every statement names the image module's own term (as
   RtPgStepsB.v) *)
Local Abbreviation rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.

(* ======================================== the pcs ======================================== *)
Definition W6B_C : Z := 0x813a0.       (* `sd a1,0x178(s1)`: the pod loop's head *)
Definition W6B_MEMSET : Z := RTSB_MEMSET. (* __asan_memset 0x51d54, the `jal` target at 0x813e4 *)
Definition W6B_RET : Z := 0x813e8.     (* after the memset of e62: `beqz s9` *)
Definition W6B_D0E : Z := 0x814d0.     (* case 0 with no input left (`beqz s9` 0x813e8 taken) *)
Definition W6B_D9 : Z := 0x81a94.      (* case 9 (`bltu a2,a1` 0x81438 taken) *)
Definition W6B_D2 : Z := 0x817c4.
Definition W6B_D3 : Z := 0x81838.
Definition W6B_U2 : Z := 0x81e58.      (* case 2's fuzz_u32 block (RtPgStepsB rtsb_u32_block2) .. 0x82038 *)
Definition W6B_U3 : Z := 0x81e94.      (* case 3's fuzz_u32 block (RtPgStepsB rtsb_u32_block3) .. 0x820bc *)
Definition W6B_TA2 : Z := 0x82038.     (* case 2's tail from the u32 block: `li a4,4` *)
Definition W6B_TB2 : Z := 0x8203c.     (* case 2's tail from the table: `sw a4,0(s6)` (e62.type = 4), a4 = 4 *)
Definition W6B_TA3 : Z := 0x820bc.     (* case 3's tail from the u32 block: `li a4,4` *)
Definition W6B_TB3 : Z := 0x820c0.     (* case 3's tail from the table, NaN and inf: `li a0,6`, a4 = 4 *)
Definition W6B_J : Z := 0x820dc.       (* the join: the capacity guard, then the call pod_write_ent(pp, e62) *)
(* the tables the cases read (registered globals, .rodata): ints[14] at 0x210e0, floats[21] at 0x21140 *)
Definition W6B_INTS : Z := 0x210e0.
Definition W6B_FLOATS : Z := 0x21140.

(* ======================================== the code table ========================================
   Every instruction word of [0x813a0, 0x82398): the pod loop (the dispatch, the ten cases' fast paths, the join and
   the record's write, the out-of-line reads of the two fuzz_u32 sites) and the slow blocks of its checks (0x8221c ..
   0x82394). All 1022 words are 4 bytes long. 0x82398 is SELI, the next piece. The `unimp` 0x83098 and the report
   calls past 0x83000 are never stepped. Precomputed once. *)
Definition W6B_TLO : Z := 0x813a0.
Definition W6B_TN : nat := 1022.
Definition w6b_tbl : ctable := Eval vm_compute in build_table rsegs W6B_TLO W6B_TN TEmpty.
Lemma w6b_tbl_ok : table_ok rsegs w6b_tbl.
Proof.
pose proof (build_table_ok0 rsegs W6B_TN W6B_TLO ltac:(unfold W6B_TLO; lia)) as H.
assert (E : build_table rsegs W6B_TLO W6B_TN TEmpty = w6b_tbl) by (vm_compute; reflexivity).
rewrite E in H. exact H.
Qed.

(* ======================================== the model's values ======================================== *)
(* kind % 10 as the code computes it (case 9 by the branch, cases 0 .. 8 by the table) *)
Definition w6b_case_pc (kd : Z) : Z := if kd mod 10 =? 9 then W6B_D9 else jtb_tgt (kd mod 10).
(* the registers the kind block may write (a0, a1, a2, a3, a6, s2, t1, s6) *)
Definition w6b_kind_clob : list (bv 5) := [6; 10; 11; 12; 13; 16; 18; 22]%bv.
(* the registers a case head may write (a0 .. a5, s2, s6) *)
Definition w6b_head_clob : list (bv 5) := [10; 11; 12; 13; 14; 15; 18; 22]%bv.
(* the registers the tail may write (t1, a0, a4, s2, s10) *)
Definition w6b_tail_clob : list (bv 5) := [6; 10; 14; 18; 26]%bv.
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
Local Notation u8s l := (map (fun x : byte => bv_unsigned x) l).

(* ===================== the context every block runs in =====================
   The harness's journal from the segment's start (rt_seg_pre's first conjunct), the real frame [R, R + 0x220)
   (hi_rsz) inside the journal's stack window with the callees' stack below it, the frame for locals F = the
   side-stack frame (4, pos) the harness holds, and the read-only segments as in the image (rt_seg_pre's
   rom_view). *)
Definition w6b_ctx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (R F pos : Z) : Prop :=
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
R mod 16 = 0 /\ R + 0x220 <= sp0 /\ sp0 - STK <= R - T_SEG_STK /\
In (4, pos) own /\ F = frame_addr lyc 4 pos /\
rom_view rsegs W memc.

(* ===================== w6b_head: C 0x813a0 .. the memset of e62, back at 0x813e8 =====================
     0x813a0  sd a1,0x178(s1)                      [R+0x178] := k (the pod index)
     0x813a4 .. 0x813d4  13 x sb zero,o(s3)        shadow_addr F + 66 .. 78 := 0 (e62 in scope, pod.h:426), in the
                                                   order 70 71 72 73 66 67 68 69 74 75 76 77 78
     0x813d8  a2 := 104; 0x813dc a0 := s6 (= F + 0x210); 0x813e0 a1 := 0
     0x813e4  jal __asan_memset (0x51d54)          e62 := 104 zero bytes (pod.h:279), returns a0 = F + 0x210
   The memset is the kernel's aintrin_realizes OSet (lib/Reusable/YG0d.v), a hypothesis of the proof. Wr: the
   callee's stack [R - ESTACK, R), the cell [R+0x178, R+0x180), the 13 granules and e62. *)
Definition w6b_head_wr (R F : Z) : Z -> Prop :=
fun a => (R - ESTACK <= a < R) \/ (R + 0x178 <= a < R + 0x180) \/
(shadow_addr F + 66 <= a < shadow_addr F + 79) \/ (F + 0x210 <= a < F + 0x278).
Definition w6b_head_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos kk : Z),
w6b_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 2 = w64 R -> getr regs 9 = w64 R -> getr regs 19 = w64 (shadow_addr F) ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 11 = w64 kk ->
getr regs 22 = w64 (F + 0x210) ->
SRr rsegs W (cfg_at rsegs W6B_C regs memc mdc)
(rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_RET rtsb_caller_saved (w6b_head_wr R F)
(fun W2 regs2 mem2 =>
getr regs2 10 = w64 (F + 0x210) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x178) 8 (kk mod 2 ^ 64) /\
(forall i, 0 <= i < 13 -> aview rsegs (w_H W2) mem2 (shadow_addr F + 66 + i) = Some 0) /\
(forall i, 0 <= i < 104 -> aview rsegs (w_H W2) mem2 (F + 0x210 + i) = Some 0))).

(* the input bytes r at cursor cur, as rate_build_contract gives them (garr8, range_addressable, 0 < src,
   src + left <= 2 ^ 63, amem_range) and outside the callees' stack below R and the real frame's cells the blocks
   read or write, [R + 0x150, R + 0x180) (RtPgImgB hi_w1's (XR, 0x150, 0x30); RtPgSegB rsb_in) *)
Definition w6b_in (W : world rsegs) (memc : word -> option byte) (R cur : Z) (r : list byte) : Prop :=
garr8 rsegs (mrestrict (w_H W) memc) cur (u8s r) /\
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur (Z.of_nat (length r)) /\
0 < cur /\ cur + Z.of_nat (length r) <= 2 ^ 63 /\ amem_range cur (Z.of_nat (length r)) /\
(forall a, cur <= a < cur + Z.of_nat (length r) ->
 ~ (R - T_SEG_STK <= a < R) /\ ~ (R + 0x150 <= a < R + 0x180)).

(* ===================== w6b_kind: 0x813e8 .. the case entry (no store) =====================
     0x813e8  beqz s9 -> 0x814d0                    in.n = 0: kind = 0, case 0 with nothing read
     0x813ec  s2 := s10 + 1; a6 := 1; 0x813f4 bltu a6,s2 -> 0x813fc (else 0x813f8 j 0x83098: never, cur > 0)
     0x813fc  t1 := s9; 0x81400 .. 0x8140c the instrumented check of s10 (slow block 0x8221c, back to 0x81410)
     0x81410  lbu a0,0(s10); 0x81414 .. 0x8142c a1 := kind % 10 (a1 = (kind * 0xcd) >> 11, `subw`, `zext.b`)
     0x81430  s6 := t1 - 1; a2 := 8; 0x81438 bltu a2,a1 -> 0x81a94 (case 9)
     0x8143c .. 0x8145c  rtsb_jt_block (lib/AU/RtPgStepsB.v) to jtb_tgt (kind % 10).
   The cursor is s10 = cur and the input left is r (s9 = |r|). On a case entry s2 = cur + 1, a6 = 1,
   t1 = |r'| + 1 and s6 = |r'| (r = b :: r'); s10 is unchanged (the kind byte's address). *)
Definition w6b_kind_R (kd cur nl' : Z) (regs2 : bvmap 5 word) : Prop :=
getr regs2 18 = w64 (cur + 1) /\ getr regs2 16 = w64 1 /\ getr regs2 6 = w64 (nl' + 1) /\
getr regs2 22 = w64 nl' /\
(if kd mod 10 =? 9 then getr regs2 12 = w64 8
 else bv_unsigned (getr regs2 10) = (kd mod 256) * 2 ^ 56 /\ getr regs2 12 = w64 JTB_A /\
      getr regs2 13 = w64 (sext8 kd)).
Definition w6b_kind_stmt : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos cur : Z) (r : list byte),
w6b_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 20 = w64 SHADOW_OFF -> getr regs 26 = w64 cur -> getr regs 25 = w64 (Z.of_nat (length r)) ->
w6b_in W memc R cur r ->
SRr rsegs W (cfg_at rsegs W6B_RET regs memc mdc)
(fun W2 c2 =>
 (r = [] /\
  rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_D0E [] (fun _ => True) W2 c2) \/
 (exists b r', r = b :: r' /\
  rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (w6b_case_pc (bv_unsigned b))
  w6b_kind_clob (w6b_kind_R (bv_unsigned b) cur (Z.of_nat (length r'))) W2 c2)).

(* ===================== w6b_c2h / w6b_c3h: a case's head (no store) =====================
   At the case entry (w6b_kind's post): s2 = c (the cursor after kind), s6 = |r| (in.n after kind), s10 = c - 1,
   t1 = |r| + 1 (in.n of the kind read), a6 = 1, [R+0x150] = F + 0x210. m = fuzz_u8 r.
   case 2 (pod.h:298-303):
     0x817c4 beqz s6 -> 0x81b28 (m = 0: a2 := 0, a1 := 0x210e0, then the table load at 0x81b34);
     0x817c8 .. 0x817d0 the pointer-overflow test of s2; 0x817d4 .. 0x817e0 its instrumented check (slow block
     0x822a4); 0x817e4 lbu a1 = m; a2 := t1 - 2; a3 := m & 1; s2 := s10 + 2; 0x817f4 bnez a3 -> 0x81e54
     (m odd: s6 := [R+0x150], stop at 0x81e58, exactly rtsb_u32_block2's premises: a2 = |r'|, s2 = c + 1,
     s10 = c - 1, t1 = |r'| + 2, a6 = 1, s4 = SHADOW_OFF);
     m even: 0x817f8 .. 0x81830 a1 := 0x210e0 + 4 ((m >> 1) % 14) (mulhu by the constant at 0x10318; the
     out-of-range test `not a4,a1; bgeu a4,a3` 0x81824 / 0x81828 whose other arm is the `unimp`), then 0x81b34 ..
     0x81b50: the instrumented check of the 4 bytes at a1 (slow block 0x82260), s6 := [R+0x150], a4 := 4, `lw a1`;
     stop at 0x8203c.
   case 3 (pod.h:304-324): 0x81838, the same read (m = 0: 0x81b54 a2 := 0, a1 := 0x21140, the table load at
     0x81fa0; s6 := [R+0x150] inside the check of s2 at 0x81854); m odd: stop at 0x81e94; m = 0xfe: a1 := 0x7fc00000
     (0x81f60); m = 0xfc: a1 := 0x7f800000 (0x81880); both through 0x820bc (a4 := 4) to 0x820c0; else 0x81f68 ..
     0x81f9c a1 := 0x21140 + 4 ((m >> 1) % 21) (mulhu by the constant at 0x10310, the out-of-range test
     0x81f90 / 0x81f94), 0x81fa0 .. 0x81fbc the check of the 4 bytes (slow block 0x82304, reached at floats[20]),
     s6 := [R+0x150], a4 := 4, `lw a1`; stop at 0x820c0.
   The value is given mod 2 ^ 32 (`lw` sign-extends; the tail stores its low 4 bytes). *)
Definition w6b_head_in (W : world rsegs) (memc : word -> option byte) (regs : bvmap 5 word) (R F c : Z)
(r : list byte) : Prop :=
getr regs 9 = w64 R /\ getr regs 20 = w64 SHADOW_OFF /\ getr regs 18 = w64 c /\
getr regs 22 = w64 (Z.of_nat (length r)) /\ getr regs 26 = w64 (c - 1) /\
getr regs 6 = w64 (Z.of_nat (length r) + 1) /\ getr regs 16 = w64 1 /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x150) 8 (F + 0x210) /\ 0 <= F + 0x210 < 2 ^ 64 /\
0 < c - 1 /\ w6b_in W memc R c r.
Definition w6b_case_head_stmt (c3 : bool) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c : Z) (r : list byte),
w6b_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
w6b_head_in W memc regs R F c r ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (if c3 then W6B_FLOATS else W6B_INTS) (if c3 then 84 else 56) ->
SRr rsegs W (cfg_at rsegs (if c3 then W6B_D3 else W6B_D2) regs memc mdc)
(fun W2 c2 =>
 let mv := fst (Cursor.fuzz_u8 r) in let r1 := snd (Cursor.fuzz_u8 r) in
 if Z.odd mv then
  rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if c3 then W6B_U3 else W6B_U2)
  w6b_head_clob
  (fun regs2 => getr regs2 12 = w64 (Z.of_nat (length r1)) /\ getr regs2 18 = w64 (c + 1) /\
     getr regs2 22 = w64 (F + 0x210)) W2 c2
 else
  rtsb_blk_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc (if c3 then W6B_TB3 else W6B_TB2)
  w6b_head_clob
  (fun regs2 => (exists v, getr regs2 11 = w64 v /\
       v mod 2 ^ 32 = (if c3 then w6b_float_even mv else w6b_int_even mv) mod 2 ^ 32) /\
     getr regs2 14 = w64 4 /\
     getr regs2 12 = w64 (Z.of_nat (length r1)) /\
     getr regs2 18 = w64 (c + Z.of_nat (length r - length r1)) /\ getr regs2 22 = w64 (F + 0x210)) W2 c2).
Definition w6b_c2h_stmt : Prop := w6b_case_head_stmt false.
Definition w6b_c3h_stmt : Prop := w6b_case_head_stmt true.

(* ===================== w6b_tail: 0x82038 / 0x8203c / 0x820bc / 0x820c0 .. J 0x820dc =====================
     0x82038  li a4,4                                                      (case 2 from the u32 block)
     0x8203c  sw a4,0(s6) (e62.type = POD_INT); j 0x820c8                  (case 2 from its head, a4 = 4)
     0x820bc  li a4,4                                                      (case 3 from the u32 block)
     0x820c0  li a0,6; sw a0,0(s6) (e62.type = POD_FLOAT)                  (case 3 from its head, a4 = 4)
     0x820c8  sw a4,4(s6) (e62.size = 4); sw a1,8(s6) (e62.body[0..4) = the value); t1 := a2 (in.n);
              s10 := s2 (the cursor); 0x820d8 ld s2,0x158(s1) (&pp->len)  -> J 0x820dc
   e62 = F + 0x210 lies in the frame (4, pos) the harness owns. *)
Definition w6b_tail_wr (F : Z) : Z -> Prop := fun a => F + 0x210 <= a < F + 0x21c.
Definition w6b_tail_stmt (c3 a : bool) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos n' v cn pv : Z),
w6b_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
getr regs 9 = w64 R -> getr regs 22 = w64 (F + 0x210) ->
getr regs 11 = w64 v -> getr regs 12 = w64 n' -> getr regs 18 = w64 cn ->
(if a then True else getr regs 14 = w64 4) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x158) 8 pv -> 0 <= pv < 2 ^ 64 ->
SRr rsegs W (cfg_at rsegs (w6b_tail_pc c3 a) regs memc mdc)
(rtsb_post B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6B_J w6b_tail_clob (w6b_tail_wr F)
(fun W2 regs2 mem2 =>
getr regs2 6 = w64 n' /\ getr regs2 26 = w64 cn /\ getr regs2 18 = w64 pv /\
val_mem rsegs (mrestrict (w_H W2) mem2) (F + 0x210) 4 (if c3 then 6 else 4) /\
val_mem rsegs (mrestrict (w_H W2) mem2) (F + 0x214) 4 4 /\
val_mem rsegs (mrestrict (w_H W2) mem2) (F + 0x218) 4 (v mod 2 ^ 32))).

End d.
End b.
