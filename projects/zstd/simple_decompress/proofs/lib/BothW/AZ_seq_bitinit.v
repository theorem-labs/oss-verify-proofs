(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OSSVerify.Proofs.zstd.simple_decompress.lib.BothW Require Import BImg RtCells ABase AZ_kit AZ_libc_iface AZ_huf_iface AZ_kx AZ_hufkit AZ_seq_bit_iface AZ_seq_bitinit1 AZ_seq_bitinit2 AZ_seq_bitinit3.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition bit_init_stmtG_at (ENTRY : Z) : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV BD SRC n lo : Z) (src junk : list byte),
  mem_inv bsegs m ->
  rw_cells bsegs m BD [CB 40 junk] -> BD mod 8 = 0 ->
  bytes_at bsegs m SRC src -> zlen src = n ->
  4096 <= BD -> BD + 40 < 2^47 -> 4096 <= SRC -> SRC + n < 2^47 ->
  (1 <= n -> BD + 40 <= SRC \/ SRC + n <= BD) ->       (* [comment removed for export] *)
  stk bsegs m lo SPV -> lo <= SPV - BITINIT_STACK_A -> SPV < 2^47 ->
  (BD + 40 <= lo \/ SPV <= BD) -> (SRC + n <= lo \/ SPV <= SRC) ->
  (* [comment removed for export] *)
  app_blk BD (BD + 40) -> aro RNG m BD 40 -> ahull RNG m BD 40 -> (1 <= n -> aro RNG m SRC n) ->
  art m -> astk RNG lo SPV ->
  evtF bsegs RNG (bit_init_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV BD SRC n lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BD) (Z_to_bv 64 SRC) (Z_to_bv 64 n) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom bsegs)).

Theorem seq_bit_init_proofG : bit_init_stmtG_at APZD_BITINIT.
Proof.
  unfold bit_init_stmtG_at, APZD_BITINIT.
  intros until junk. intros.
  destruct (Z_lt_le_dec n 2) as [L|L]; [eapply sbi_rest; try eassumption; lia|].
  destruct (Z_lt_le_dec 7 n) as [L'|L']; [eapply sbi_rest; try eassumption; lia|].
  destruct (Z_lt_le_dec n 5) as [L''|L'']; [eapply sbi_mid; try eassumption; lia|].
  eapply sbi_hi; try eassumption; lia.
Qed.

Theorem seq_bit_init_proofS : bit_init_stmtS_at APZD_BITINIT.
Proof.
  unfold bit_init_stmtS_at. intros until junk. intros MI HBD BD8 SB LEN B0 B1 S0 S1 DJ STK LOS SPB OSB OSS APB AROB AHB AROS.
  apply (seq_bit_init_proofG RNG ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV BD SRC n lo src junk);
    try assumption. all: intros _; first [exact DJ | exact AROS].
Qed.

(* [comment removed for export] *)
Theorem seq_bit_init_proofA : bit_init_stmtA_at APZD_BITINIT.
Proof.
  unfold bit_init_stmtA_at. intros until junk. intros MI HBD BD8 SB LEN B0 B1 S0 S1 _. revert MI HBD BD8 SB LEN B0 B1 S0 S1.
  exact (seq_bit_init_proofS RNG ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m SPV BD SRC n lo src junk).
Qed.
End CANSEC1.
