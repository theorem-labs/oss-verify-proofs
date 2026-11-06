(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* LLVMFuzzerTestOneInput_segX_crt1_geo: what a cut point of image B's LLVMFuzzerTestOneInput gives the footprint
   runs of lib/B/Prog/LLVMFuzzerTestOneInput_segX_crt1_runs.v: the numbers of the frame (c1e_geo), the stack
   window's presence (c1e_stk_present), each spill slot as an 8-byte load (c1e_slot_rd8), and the walk's footprint
   over the slot area, over a live block and over a block's shadow (c1e_rng_stk / c1e_rng_block / c1e_rng_shadow).
   Everything here is read off dec_b_core's journal and the allocator laws (lib/Reusable/YG0d.v AR_blocks_law and
   AR_shadow_law); nothing is image-specific but the segment list. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YM05 YK04 YA0i YA0n YP09.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YG0v YCbq YI00 YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Frame.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segX_crt1_fevt.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require LeafCgKit.
Import ListNotations.
Open Scope Z_scope.
Module LCK := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.LeafCgKit.

Section C1E.
Context {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws decodesegsB0 B.
Local Notation segs := decodesegsB0.
Local Notation RNGW W := (LCK.RNG_W (world segs) (@w_H segs) W).

(* The numbers of the frame at any cut point of the body. *)
Lemma c1e_geo : forall cx ly' S' W' regs' mem' md' k,
  @dec_b_core rc B cx ly' S' W' regs' mem' md' k ->
  0 < d_sp1 cx /\ d_sp0 cx - 240 <= d_sp1 cx <= d_sp0 cx - 224 /\ d_sp1 cx mod 32 = 0 /\
  d_sp0 cx mod 16 = 0 /\ @YM05.alloc_ceiling rc <= ly_stk_lo (d_ly cx) /\
  ly_stk_lo (d_ly cx) + DEC_LLVMF_STK <= d_sp0 cx /\ d_sp0 cx <= 2 ^ 47.
Proof.
  intros cx ly' S' W' regs' mem' md' k HC.
  destruct HC as (HJ & _ & _ & _ & _ & Hsp1 & Hsp32 & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
  destruct Hstatic as (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop).
  pose proof (@YM05.alloc_ceiling_val rc) as (Hac & _).
  assert (HS : DEC_LLVMF_STK = 32768) by reflexivity.
  repeat split; lia.
Qed.

(* The slot's stack window is present at every cut point (the journal's own clause). *)
Lemma c1e_stk_present : forall cx ly' S' W' regs' mem' md' k,
  @dec_b_core rc B cx ly' S' W' regs' mem' md' k ->
  forall a, d_sp0 cx - DEC_LLVMF_STK <= a < d_sp0 cx -> apresent (w_H W') mem' a.
Proof.
  intros cx ly' S' W' regs' mem' md' k HC a Ha.
  destruct HC as (HJ & _).
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  apply Hpres. exact Ha.
Qed.

(* The allocator state at a cut point. *)
Lemma c1e_ar : forall cx ly' S' W' regs' mem' md' k,
  @dec_b_core rc B cx ly' S' W' regs' mem' md' k -> AR segs B ly' S' W' mem' md'.
Proof.
  intros cx ly' S' W' regs' mem' md' k HC. destruct HC as (HJ & _).
  pose proof HJ as (HAR & _). exact HAR.
Qed.

(* A spill slot of the s1 area is an 8-byte load of the run. *)
Lemma c1e_slot_rd8 : forall cx ly' S' W' regs' mem' md' k off v,
  @dec_b_core rc B cx ly' S' W' regs' mem' md' k ->
  0 <= off -> off + 8 <= 224 ->
  dec_b_slot cx (aview segs (w_H W') mem') off v ->
  ov_read_bytes rsegs mem' (Z_to_bv 64 (d_sp1 cx + off)) 8 = Some (le8 (Z_to_bv 64 v)).
Proof.
  intros cx ly' S' W' regs' mem' md' k off v HC Ho1 Ho2 HS.
  pose proof (c1e_geo cx ly' S' W' regs' mem' md' k HC) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  pose proof (c1e_stk_present cx ly' S' W' regs' mem' md' k HC) as HP.
  pose proof (@YM05.alloc_ceiling_val rc) as (Hac & _).
  assert (HS32 : DEC_LLVMF_STK = 32768) by reflexivity.
  apply (c1f_rd8 W' mem' (d_sp1 cx + off) v); [lia | lia | |].
  - intros i Hi. apply (proj1 (HP (d_sp1 cx + off + i) ltac:(lia))).
  - apply (val_mem_of_rdword decodesegsB0 (w_H W') mem' (d_sp1 cx + off) v). exact HS.
Qed.

(* The walk's footprint holds the slot area. *)
Lemma c1e_rng_stk : forall cx ly' S' W' regs' mem' md' k lo len,
  @dec_b_core rc B cx ly' S' W' regs' mem' md' k ->
  d_sp0 cx - DEC_LLVMF_STK <= lo -> lo + len <= d_sp0 cx -> 0 <= len ->
  ExecF.rng (RNGW W') lo len.
Proof.
  intros cx ly' S' W' regs' mem' md' k lo len HC Hlo Hhi Hlen.
  pose proof (c1e_geo cx ly' S' W' regs' mem' md' k HC) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  pose proof (c1e_stk_present cx ly' S' W' regs' mem' md' k HC) as HP.
  pose proof (@YM05.alloc_ceiling_val rc) as (Hac & _).
  assert (HS32 : DEC_LLVMF_STK = 32768) by reflexivity.
  apply (c1f_rng_of_apresent W' mem' lo len); [lia | lia |].
  intros a Ha. apply HP. lia.
Qed.

(* The walk's footprint holds a live block of the allocator. *)
Lemma c1e_rng_block : forall ly S W mem md p n lo len,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  p <= lo -> lo + len <= p + req_size n -> 0 <= len ->
  ExecF.rng (RNGW W) lo len.
Proof.
  intros ly S W mem md p n lo len HAR Hin Hlo Hhi Hlen.
  pose proof (al_blocks _ _ LAWS ly S W mem md p n HAR Hin)
    as (Hm16 & Hp4096 & Hpc & Happ & Hpres & _).
  pose proof (@YM05.alloc_ceiling_val rc) as (Hac & _).
  apply (c1f_rng_of_apresent W mem lo len); [lia | lia |].
  intros a Ha. exact (proj1 (Hpres a ltac:(lia))).
Qed.

(* The walk's footprint holds the 8-aligned shadow-word cover of a live block: every byte of that cover is a
   byte cgif's reader answers (AR_shadow_law's shadow_hull_vis), so the world does not hide it. *)
Lemma c1e_rng_shadow : forall ly S W mem md p n,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) -> 0 < req_size n ->
  ExecF.rng (RNGW W) (shadow_addr p / 8 * 8)
    (shadow_addr (p + req_size n - 1) / 8 * 8 + 8 - shadow_addr p / 8 * 8).
Proof.
  intros ly S W mem md p n HAR Hin Hn.
  pose proof (al_shadow _ _ LAWS ly S W mem md p n HAR Hin) as (_ & Hhull).
  pose proof (al_blocks _ _ LAWS ly S W mem md p n HAR Hin)
    as (Hm16 & Hp4096 & Hpc & Happ & _ & _).
  pose proof (@YM05.alloc_ceiling_val rc) as (Hac & _).
  assert (Hsh1 : 0 <= shadow_addr p / 8 * 8).
  { unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos p 8 ltac:(lia)).
    pose proof (Z.div_pos (p / 8 + 2147450880) 8 ltac:(lia)). lia. }
  assert (Hsh2 : shadow_addr (p + req_size n - 1) / 8 * 8 + 8 <= 2 ^ 64).
  { unfold shadow_addr, SHADOW_OFF.
    assert (Hpd : (p + req_size n - 1) / 8 <= @YM05.alloc_ceiling rc) by (apply Z.div_le_upper_bound; lia).
    pose proof (Z.div_le_upper_bound ((p + req_size n - 1) / 8 + 2147450880) 8 (2 ^ 61) ltac:(lia) ltac:(lia)).
    lia. }
  apply (c1f_rng_of_vis_aview W mem _ _ Hsh1); [lia|].
  intros a Ha. apply Hhull. lia.
Qed.
End C1E.
