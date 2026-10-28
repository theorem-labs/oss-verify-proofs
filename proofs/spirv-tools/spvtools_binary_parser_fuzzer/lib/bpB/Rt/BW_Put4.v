(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BImage BZBridge BSysStep BSFModel BellsX BArr BacX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BothAllocModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocKit BllocRep BllocWalkKit BsDepotInv BW_MallocBase BW_Put1 BW_Enqueue1 BW_Put2 BW_Drain BllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Section HCW.
  Context {HCEIL : HeapCeil}.

  Variables (sp ra0 s0v s1v s2v s3v s4v s5v : word).
  Variables (gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo : Z) (T : list Z) (rest : list word) (jk : list byte).
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 2496 <= bv_unsigned sp.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis LR  : length rest = (255 - length T)%nat.
  Hypothesis NR  : (1 <= length T <= 30)%nat.

  Ltac trp H MU WM tac := first [ eapply rw_cells_transport in H | eapply u64arr_transport in H ]; [| exact MU| exact WM| cbn [disjoint_from cells_size csize length Nat.add Nat.mul app]; tac].

  Theorem put_after_recycle : forall (rax t0 t1 t2 x0 x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 t3 t4 t5 t6 : word) (m : mem) (U TH : Z),
    mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -2208) ->
    rw_cells asegs m (bv_unsigned sp + -2208) (put_frame sp s6 U TH) ->
    rw_cells asegs m (bv_unsigned sp + -2128) [C8 (wz (bv_unsigned sp + -2128 + 16)); C8 (wz (Z.of_nat (length T)))] ->
    u64arr asegs m (bv_unsigned sp + -2128 + 16) (map wz T ++ rest) ->
    rw_cells asegs m (bv_unsigned sp + -72) [C8 sp] ->
    rw_cells asegs m (bv_unsigned sp + -64) [CB 8 jk; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
    evt asegs (free_ret_post sp ra0 s0v s1v s2v s3v s4v s5v gp tp s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp t0 t1 t2 x0 x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9693c) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros U TH MI ST PFR ESO TRB TFB F4.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR. acb.
    unfold put_frame, OT_TQ, OT_CACHE, wz in *.

    do 8 step. step. step.
    release_frame PFR ST (bv_unsigned sp + -2128).
    step. do 7 step. step. step.
    apply evt_done. unfold free_ret_post. do 15 eexists. split; [reflexivity|]. eapply icpt_frame_release; eassumption.
  Qed.
End HCW.
