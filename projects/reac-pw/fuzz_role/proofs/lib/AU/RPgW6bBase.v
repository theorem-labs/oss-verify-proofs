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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/AU/HPgCaseB.v, with its module paths, module names, addresses and numbers changed; 84 of its 117 lines of code are new or changed and 1056 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW6bBase.v at d1ed1a6d9011 for reac-pw/fuzz_rate's
   image A: module paths changed; the pcs, registers, real-frame cells, write set and image addresses are rate's
   (measured on fuzz_rate.asan); the block context, the input premise and the code table are lib/A/RtPgW6aBase.v's
   (w6_ctx, w6_in, w6_tbl), and the case entry adds the input's shadow hull and its distance from the frame's
   objects; the block post is RtPgSteps.rts_post. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/RtPgW6bBase.v and lib/A/RtPgW6aBase.v (its block
   context, input premise and code table) at 32f84792c2a6; for image B (fuzz_rate.asan-ubsan): every pc, register,
   real-frame cell, data address and the write set are image B's; the frame for locals is class 4 (1024 bytes) and
   the pod object is e62 at F + 0x210; the code table is this file's own (the four cases, their tails and their slow
   blocks); the block post is RtPgStepsB.rtsb_post. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/AU/RtPgW6bBaseB.v at a191d52e2a9a for
   reac-pw/fuzz_role's image B (fuzz_role.asan-ubsan): module paths changed (lib/AU/Img0.rsegs, lib/A/RPgBase and
   RPgCSpec, lib/AU/RPgSteps.v's rl_ names); every pc, register, real-frame cell, data address and the write set are
   role B's: the real frame is 0x200 bytes; at a case entry the kind byte's address is a6, the trap tests' 1 is s4
   and the shadow offset s11; the cells the cases read are [R+0x48], [R+0xf0], [R+0x110], [R+0x130], [R+0x140],
   [R+0x158]; case 1 spills to [R+0x58] and [R+0x118]; at J the cursor is a3, what is left t1, s6 = pp + 0x4000 and
   a5 = pp; ent_build.s is at 0x21160 and ent_build.vocab at 0x9a7a0. *)
(* reac-pw/fuzz_role image B (fuzz_role.asan-ubsan, pinned sha256
   b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; every address measured on the unstripped twin
   dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a, same loaded bytes): the BLOCK STATEMENTS of the
   walk piece "ent_build B" of LLVMFuzzerTestOneInput (0x80020): the cases 1, 4, 5 and 9 of ent_build's
   `switch (kind % 10)` (pod.h:285-296, 326-339, 367-377), each from its entry to the join J 0x818d8.
   Statement text only: no function is proved here (kind: segment lemma).

   ONE BLOCK PER CASE, so that a case is proved without the cut records of lib/AU/RPgSeg.v and the piece is the
   case's block between the two cut bridges (lib/AU/RPgEntBCut.v). Image B's code of the four cases (every UBSan test
   `bltu s4,t` / `bgeu t,o` whose other arm is the `unimp` 0x82604 is decided by the run's atom ranges; e62 =
   [F + 0x210, F + 0x278) is the pod; its address is the cell [R+0x158], its body's [R+0x110], body + 8 [R+0x48],
   the complement of the body's address [R+0xf0]):
     w6bb_c4  0x80f34 .. J: no byte left (`beqz s6` -> 0x81338: v = 0, t1 := 0, s6 := [R+0x130], a5 := [R+0x140]);
              else the T1 test of s2 + 1 (0x80f38 .. 0x80f40), the shadow check of s2 (NE-SLOW, slow block 0x81a98)
              with `ld s6,0x130(s1)`, `ld a5,0x140(s1)` between its load and its branch, v = fuzz_u8 % 3
              (`mul 0xab`, `srli 9`), t1 := t1 - 2, s2 := a6 + 2; 0x81348 .. 0x8135c e62.type = 2, e62.size = 4,
              e62.body[0..4) = v; 0x818d4 a3 := s2 (pod.h:326-330).
     w6bb_c5  0x8113c .. J: s10 := a3 (the kind byte, sign-extended); no byte left -> 0x814c4 (s8 := 0); else T1
              of s2 + 1, the check of s2 (slow block 0x81ad4) with `ld s4,0x110(s1)` (e62.body), b = fuzz_u8,
              s6 := t1 - 2, s2 := a6 + 2, s8 := b & 31, n = min(s8, s6); the T2 test `not a0,s2; bgeu a0,s8`
              (0x8117c .. 0x81184); memcpy(e62.body, s2, n) at 0x81194 (checked_memcpy 0x5116c); unless kind & 0x80
              (`bltz s10` 0x8119c) the T3 test of [R+0xf0] (= ~&e62.body) against n and the NUL at e62.body[n] (an
              uninstrumented store); a3 := s2 + n, t1 := s6 - n; e62.type = 8, e62.size = n + (kind < 128)
              (pod.h:336-337, 209-219); a5 := [R+0x140]; 0x814bc s6 := [R+0x130].
     w6bb_c9  0x812d4 .. J: e62.type = 14, e62.body[0..4) = 14, T3 of [R+0x110] against -5, e62.body[4..8) = 8, T3
              against -9, memcpy(e62.body + 8 = [R+0x48], s, 14) at 0x8131c (s = ent_build.s 0x21160, "reac.cfg.rate"
              and its NUL), e62.size = 24, t1 := s6, a3 := s2, s6 := [R+0x130], a5 := [R+0x140] (pod.h:369-375); no
              input byte is read.
     w6bb_c1  0x810d0 .. J: s10 := [R+0x110] (e62.body); no byte left -> 0x813b4 (i = 0, t1 := 0, a6 := s2); else
              T1, the check of s2 (slow block 0x81ac8), i = fuzz_u8 % 9 (`mul 0x39`, `srli 9`), the T2 test of
              &vocab + 8 i (0x81120 .. 0x81128), t1 := t1 - 2, a6 := a6 + 2; 0x813c8 [R+0x58] := a6 (the cursor),
              [R+0x118] := a3 (the kind byte); the checked 8-byte load of vocab[i] (EQ-J-NOSLOW, .data.rel.ro
              0x9a7a0); the strlen wrapper at 0x813f0 (0x41b60); l = min(len, 95); memcpy(e62.body, vocab[i], l) at
              0x81414; T3 of [R+0xf0] against l; the NUL; e62.type = 8, e62.size = l + 1; s6 := [R+0x130],
              t1 := s4 (what was left), a3 := [R+0x58]; with kind & 0x80 and len <= 93: a5 := [R+0x140], the T3
              tests and the two checked byte stores 'x', 0 at e62.body[l + 1], e62.body[l + 2] (slow blocks 0x81aec,
              0x81af8), e62.size = l + 3, s6 := [R+0x130]; else 0x81740 a5 := [R+0x140] (pod.h:286-294).
   THE STATE AT A CASE ENTRY (lib/AU/RPgW6aBase.v w6b_kind's post on the cut C's state, checked against the code):
   sp = s1 = R (x2, x9) the real frame's base, s11 = SHADOW_OFF (x27), s3 = shadow_addr F (x19), s2 = c (x18) the
   cursor after the kind byte, a6 = c - 1 (x16) the kind byte's address, s6 = |r| (x22) what is left after it,
   t1 = |r| + 1 (x6), s4 = 1 (x20) the left side of the T1 tests, a3 = the kind byte sign-extended (x13; not on case
   9: `bltu a2,a1` 0x80bec jumps before 0x80c0c); the cells the cases read: [R+0x48] = F + 0x220, [R+0xf0] =
   ~(F + 0x218), [R+0x110] = F + 0x218, [R+0x130] = pp + 0x4000, [R+0x140] = pp, [R+0x158] = F + 0x210; e62 = 104
   zero bytes with its 13 shadow granules 0 (in scope).
   THE STATE AT J (lib/AU/RPgSeg.v rs_cut_J): a3 = the cursor, t1 = what is left, s6 = pp + 0x4000, a5 = pp,
   e62 = Layout.ent_mem of the pod; the registers outside w6bb_clob as at the entry; every byte outside w6bb_wr as
   at the entry (the callees' stack below R, the cells [R+0x58, R+0x60) and [R+0x118, R+0x120), e62). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgBase RPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.AU Require Import RPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ======================================== the pcs ======================================== *)
Definition W6BB_D1 : Z := 0x810d0.     (* jt_tgt 1 *)
Definition W6BB_D4 : Z := 0x80f34.     (* jt_tgt 4 *)
Definition W6BB_D5 : Z := 0x8113c.     (* jt_tgt 5 *)
Definition W6BB_D9 : Z := 0x812d4.     (* case 9: `bltu a2,a1` 0x80bec taken *)
Definition W6BB_J : Z := 0x818d8.      (* the join: the capacity guard, then the call pod_write_ent(pp, e62) *)
(* the callees: checked_memcpy (cases 1, 5, 9) and the strlen wrapper (case 1) *)
Definition W6BB_MEMCPY : Z := RL_MEMCPY.
Definition W6BB_STRLEN : Z := RL_STRLEN.
(* the image's data the cases read: ent_build.s (case 9's memcpy source, 14 bytes, .rodata) and ent_build.vocab
   (nine 8-byte pointer cells in .data.rel.ro, each the address of one vocab string in .rodata) *)
Definition W6BB_S : Z := 0x21160.
Definition W6BB_VOCAB : Z := 0x9a7a0.
Definition w6bb_vptr (i : Z) : Z :=
  nth (Z.to_nat i) [0x20f00; 0x20f20; 0x20f40; 0x20f60; 0x20f80; 0x20fa0; 0x20fe0; 0x21000; 0x21020] 0.

(* ======================================== the code table ========================================
   Every instruction word of [0x80f34, 0x81b98): the entries of cases 4, 1, 5 and 9, their tails (0x81338 ..
   0x81360, 0x813b4 .. 0x814d8, 0x81584 .. 0x81594, 0x81740 .. 0x81744, 0x818d4), and the slow blocks of their checks
   (0x81a98 case 4, 0x81ac8 case 1, 0x81ad4 case 5, 0x81aec / 0x81af8 case 1's two byte stores). All 793 words are
   4 bytes long. The `unimp` 0x82604 and the report calls past 0x82600 are never stepped. Precomputed once. *)
Definition W6BB_TLO : Z := 0x80f34.
Definition W6BB_TN : nat := 793.
Definition w6bb_tbl : ctable := Eval vm_compute in build_table rsegs W6BB_TLO W6BB_TN TEmpty.
Lemma w6bb_tbl_ok : table_ok rsegs w6bb_tbl.
Proof.
pose proof (build_table_ok0 rsegs W6BB_TN W6BB_TLO ltac:(unfold W6BB_TLO; lia)) as H.
assert (E : build_table rsegs W6BB_TLO W6BB_TN TEmpty = w6bb_tbl) by (vm_compute; reflexivity).
rewrite E in H. exact H.
Qed.

(* the registers a case may change: a call's caller-saved set (RPgSteps.rl_caller_saved) and s2, s4, s6, s8,
   s10; the others (sp, gp, tp, s0, s1, s3, s5, s7, s9, s11 among them) are kept. a3, a5, s6 and t1 are written last
   by the cases: their values at J are in w6bb_J_R. *)
Definition w6bb_clob : list (bv 5) :=
  [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 18; 20; 22; 24; 26; 28; 29; 30; 31]%bv.
(* the bytes a case may change: its callees' stack below R, case 1's spill cells [R+0x58, R+0x60) (the cursor) and
   [R+0x118, R+0x120) (the kind byte), and e62 *)
Definition w6bb_wr (R F : Z) : Z -> Prop :=
  fun a => (R - T_SEG_STK <= a < R) \/ (R + 0x58 <= a < R + 0x60) \/ (R + 0x118 <= a < R + 0x120) \/
           (F + 0x210 <= a < F + 0x278).

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
Definition w6bb_ctx (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world rsegs)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (k : Z)
(lyc : alayout) (Sc : astate) (W : world rsegs) (memc : word -> option byte) (mdc : Model) (R F pos : Z) : Prop :=
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k /\
R mod 16 = 0 /\ R + 0x200 <= sp0 /\ sp0 - STK <= R - T_SEG_STK /\
In (4, pos) own /\ F = frame_addr lyc 4 pos /\
rom_view rsegs W memc.

(* the input bytes r at cursor cur, as role_build_contract gives them (garr8, range_addressable, its shadow hull,
   0 < src, src + left <= 2 ^ 63, amem_range) and outside the callees' stack below R, the real frame's cells the blocks
   read or write ([R + 0x48, R + 0x160): RPgImgA hi_w1's (XR, 0x48, 0x118); RPgSeg rs_in) and the frame's objects
   [F + 0x20, F + 0x278) (hi_w1's (XF, 0x20, 0x258); case 5 copies from the input into e62) *)
Definition w6bb_inp (W : world rsegs) (memc : word -> option byte) (R F cur : Z) (r : list byte) : Prop :=
garr8 rsegs (mrestrict (w_H W) memc) cur (u8s r) /\
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF cur (Z.of_nat (length r)) /\
0 < cur /\ cur + Z.of_nat (length r) <= 2 ^ 63 /\ amem_range cur (Z.of_nat (length r)) /\
(0 < Z.of_nat (length r) -> shadow_hull_vis (aview rsegs (w_H W) memc) cur (Z.of_nat (length r))) /\
(forall a, cur <= a < cur + Z.of_nat (length r) ->
 ~ (R - T_SEG_STK <= a < R) /\ ~ (R + 0x48 <= a < R + 0x160) /\ ~ (F + 0x20 <= a < F + 0x278)).

(* ===================== the state at a case entry =====================
   kd is the kind byte, c the cursor after it, r the input after it. *)
Definition w6bb_in (W : world rsegs) (memc : word -> option byte) (regs : bvmap 5 word) (R F c pp kd : Z)
(r : list byte) : Prop :=
getr regs 2 = w64 R /\ getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B) /\
getr regs 9 = w64 R /\ getr regs 27 = w64 SHADOW_OFF /\ getr regs 19 = w64 (shadow_addr F) /\
getr regs 18 = w64 c /\ getr regs 16 = w64 (c - 1) /\ getr regs 22 = w64 (Z.of_nat (length r)) /\
getr regs 6 = w64 (Z.of_nat (length r) + 1) /\ getr regs 20 = w64 1 /\
(kd mod 10 <> 9 -> getr regs 13 = w64 (kd - 256 * (kd / 128))) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x48) 8 (F + 0x220) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 (2 ^ 64 - 1 - (F + 0x218)) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x110) 8 (F + 0x218) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x130) 8 (pp + 0x4000) /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x140) 8 pp /\
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x158) 8 (F + 0x210) /\
0 <= kd < 256 /\ 4096 <= pp /\ pp + 0x4000 < 2 ^ 64 /\
4096 <= F /\ F + 1024 <= alloc_ceiling /\ F mod 32 = 0 /\ in_app F 1024 /\
(forall i, 0 <= i < 104 -> mbyte rsegs (mrestrict (w_H W) memc) (F + 0x210 + i) = Some (Z_to_bv 8 0)) /\
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF (F + 0x210) 104 /\
shadow_hull_vis (aview rsegs (w_H W) memc) (F + 0x210) 104 /\
0 < c - 1 /\ w6bb_inp W memc R F c r.

(* ===================== the state at J =====================
   rr = the kind byte :: r is the turn's input; (ed, r') = ent_build rr. *)
Definition w6bb_J_R (R F c pp : Z) (r rr : list byte) : world rsegs -> bvmap 5 word -> (word -> option byte) -> Prop :=
fun W2 regs2 mem2 =>
getr regs2 22 = w64 (pp + 0x4000) /\ getr regs2 15 = w64 pp /\
getr regs2 13 = w64 (c + Z.of_nat (length r) - Z.of_nat (length (snd (ent_build rr)))) /\
getr regs2 6 = w64 (Z.of_nat (length (snd (ent_build rr)))) /\
garr8 rsegs (mrestrict (w_H W2) mem2) (F + 0x210) (u8s (ent_mem (fst (ent_build rr)))).

(* ===================== the case block =====================
   P picks the case by kind % 10; X is what the case reads of the image besides the code. *)
Definition w6bb_case_stmt (pc : Z) (P : Z -> Prop) (X : world rsegs -> (word -> option byte) -> Prop) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) (R F pos c pp : Z)
  (b : byte) (r : list byte),
w6bb_ctx STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
P (bv_unsigned b) ->
w6bb_in W memc regs R F c pp (bv_unsigned b) r ->
X W memc ->
SRr rsegs W (cfg_at rsegs pc regs memc mdc)
(rl_wpost B MT STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6BB_J w6bb_clob (w6bb_wr R F)
  (w6bb_J_R R F c pp r (b :: r))).

(* case 9 reads ent_build.s (a registered global of 14 bytes, the text "reac.cfg.rate" and its NUL) *)
Definition w6bb_s_ok (W : world rsegs) (memc : word -> option byte) : Prop :=
rl_cstr rsegs (w_H W) memc W6BB_S (u8s S9).
(* case 1 reads vocab[i] (the registered table of 72 bytes) and the string it points to *)
Definition w6bb_vocab_ok (W : world rsegs) (memc : word -> option byte) : Prop :=
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6BB_VOCAB 72 /\
(forall i, 0 <= i < 9 ->
  val_mem rsegs (mrestrict (w_H W) memc) (W6BB_VOCAB + 8 * i) 8 (w6bb_vptr i) /\
  rl_cstr rsegs (w_H W) memc (w6bb_vptr i) (u8s (nth (Z.to_nat i) vocab []))).

Definition w6bb_c4_stmt : Prop := w6bb_case_stmt W6BB_D4 (fun kd => kd mod 10 = 4) (fun _ _ => True).
Definition w6bb_c5_stmt : Prop := w6bb_case_stmt W6BB_D5 (fun kd => kd mod 10 = 5) (fun _ _ => True).
Definition w6bb_c9_stmt : Prop := w6bb_case_stmt W6BB_D9 (fun kd => kd mod 10 = 9) w6bb_s_ok.
Definition w6bb_c1_stmt : Prop := w6bb_case_stmt W6BB_D1 (fun kd => kd mod 10 = 1) w6bb_vocab_ok.

End d.
End b.
