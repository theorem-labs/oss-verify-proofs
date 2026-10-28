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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocKit BllocRep BllocWalkKit BsDepotInv BW_MallocBase BllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.

Section Ret.
  Context {HCEIL : HeapCeil}.

  Variables (sp ra0 s0v s1v s2v s3v s4v s5v : word).

  Variables (x1 gp tp x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo U : Z) (T : list Z) (rest : list word) (jk : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 2496 <= bv_unsigned sp.
  Hypothesis SPT : bv_unsigned sp + 16 <= 2^47.
  Hypothesis UR : 1 <= U < 2^64.
  Hypothesis ST  : stk asegs m lo (bv_unsigned sp + -2144).
  Hypothesis FR  : rw_cells asegs m (bv_unsigned sp + -2144) [C8 sp; C8 (wz 0xba418)].
  Hypothesis ESO : rw_cells asegs m (bv_unsigned sp + -2128) [C8 (wz (bv_unsigned sp + -2128 + 16)); C8 (wz (Z.of_nat (length T)))].
  Hypothesis TRB : u64arr asegs m (bv_unsigned sp + -2128 + 16) (map wz T ++ rest).
  Hypothesis LR  : length rest = (255 - length T)%nat.
  Hypothesis NR  : (1 <= length T <= 30)%nat.
  Hypothesis TFB : rw_cells asegs m (bv_unsigned sp + -72) [C8 sp].
  Hypothesis F4  : rw_cells asegs m (bv_unsigned sp + -64) [CB 8 jk; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0].

  Definition malloc_ret_post : machine_state -> Prop := fun ms' =>
    ms' = MS (mkR ra0 sp gp tp x5 x6 x7 s0v s1v (wz U) x11 x12 x13 x14 x15 x16 x17 s2v s3v s4v s5v x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
             F (ret_pc ra0) fc None m (seg_rom asegs)
    /\ stk asegs m lo (bv_unsigned sp).

  Theorem malloc_ret :
    evt asegs malloc_ret_post
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 x8 x9 (wz U) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x9246c) fc None m (seg_rom asegs)).
  Proof.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    acb. unfold wz in *.

    step. if_cases K; zify_cond K.
    { exfalso. clear - K UR; try acb. rewrite ?unsigned_lit in K by lia. lia. }
    clear K.
    step. step. step. step.

    step. do 7 step. step. step.
    apply evt_done. split; [reflexivity|].

    pose proof (stk_of_rw_cells asegs _ _ _ FR) as K1. pose proof (stk_of_rw_cells asegs _ _ _ ESO) as K2.
    pose proof (stk_of_rw_cells asegs _ _ _ TFB) as K4. pose proof (stk_of_rw_cells asegs _ _ _ F4) as K5.
    pose proof (stk_of_rw_cells asegs _ _ _ (rw_cells_of_u8arr asegs _ _ _ (proj1 (u64arr_u8arr asegs _ _ _) TRB))) as K3.
    cbn [cells_size csize Nat.add] in K1, K2, K3, K4, K5.
    rewrite u64s_length, length_app, length_map, LR in K3.
    eapply stk_merge; [exact ST| |lia]. eapply stk_merge; [exact K1| |lia].
    replace (bv_unsigned sp + -2144 + Z.of_nat 16) with (bv_unsigned sp + -2128) by lia.
    eapply stk_merge; [exact K2| |lia]. replace (bv_unsigned sp + -2128 + Z.of_nat 16) with (bv_unsigned sp + -2128 + 16) by lia.
    eapply stk_merge; [exact K3| |lia].
    replace (bv_unsigned sp + -2128 + 16 + Z.of_nat (8 * (length T + (255 - length T)) + 0)) with (bv_unsigned sp + -72) by lia.
    eapply stk_merge; [exact K4| |lia]. replace (bv_unsigned sp + -72 + Z.of_nat 8) with (bv_unsigned sp + -64) by lia.
    replace (bv_unsigned sp) with (bv_unsigned sp + -64 + Z.of_nat 64) at 2 by lia. exact K5.
  Qed.
End Ret.
