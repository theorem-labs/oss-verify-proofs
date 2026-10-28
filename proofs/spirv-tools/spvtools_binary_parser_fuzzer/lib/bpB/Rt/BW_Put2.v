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
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BllocKit BllocRep BllocWalkKit BsDepotInv BW_MallocBase BW_Put1 BW_Enqueue1 BllocTacX.
Import ListNotations.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BllocStoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.
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

  Definition free_ret_post (m : mem) : machine_state -> Prop := fun ms' =>
    exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra0) fc None m (seg_rom asegs)
    /\ stk asegs m lo (bv_unsigned sp).

  Lemma icpt_frame_release : forall m,
    stk asegs m lo (bv_unsigned sp + -2128) ->
    rw_cells asegs m (bv_unsigned sp + -2128) [C8 (wz (bv_unsigned sp + -2128 + 16)); C8 (wz (Z.of_nat (length T)))] ->
    u64arr asegs m (bv_unsigned sp + -2128 + 16) (map wz T ++ rest) ->
    rw_cells asegs m (bv_unsigned sp + -72) [C8 sp] ->
    rw_cells asegs m (bv_unsigned sp + -64) [CB 8 jk; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
    stk asegs m lo (bv_unsigned sp).
  Proof.
    intros m ST ESO TRB TFB F4.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
    pose proof (stk_of_rw_cells asegs _ _ _ ESO) as K2.
    pose proof (stk_of_rw_cells asegs _ _ _ TFB) as K4. pose proof (stk_of_rw_cells asegs _ _ _ F4) as K5.
    pose proof (stk_of_rw_cells asegs _ _ _ (rw_cells_of_u8arr asegs _ _ _ (proj1 (u64arr_u8arr asegs _ _ _) TRB))) as K3.
    cbn [cells_size csize Nat.add] in K2, K3, K4, K5.
    rewrite u64s_length, length_app, length_map, LR in K3.
    eapply stk_merge; [exact ST| |lia].
    eapply stk_merge; [exact K2| |lia]. replace (bv_unsigned sp + -2128 + Z.of_nat 16) with (bv_unsigned sp + -2128 + 16) by lia.
    eapply stk_merge; [exact K3| |lia].
    replace (bv_unsigned sp + -2128 + 16 + Z.of_nat (8 * (length T + (255 - length T)) + 0)) with (bv_unsigned sp + -72) by lia.
    eapply stk_merge; [exact K4| |lia]. replace (bv_unsigned sp + -72 + Z.of_nat 8) with (bv_unsigned sp + -64) by lia.
    replace (bv_unsigned sp) with (bv_unsigned sp + -64 + Z.of_nat 64) at 2 by lia. exact K5.
  Qed.

  Section PutTail.
    Variables (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem).
    Variables (U size TH qcache : Z) (k f la qbytes : Z).
    Hypothesis MI : mem_inv asegs m.
    Hypothesis THR : hidden (akobj TH 4096 /\ TH + 4096 <= aceil).
    Hypothesis QCR : 0 <= qcache < 2^64. Hypothesis QB : 0 <= qbytes <= qcache.
    Hypothesis ST  : stk asegs m lo (bv_unsigned sp + -2208).
    Hypothesis PFR : rw_cells asegs m (bv_unsigned sp + -2208) (put_frame sp s6 U TH).
    Hypothesis TQ  : rw_cells asegs m (TH + OT_TQ) [C8 (wz k); C8 (wz f); C8 (wz la); C8 (wz qbytes)].
    Hypothesis ESO : rw_cells asegs m (bv_unsigned sp + -2128) [C8 (wz (bv_unsigned sp + -2128 + 16)); C8 (wz (Z.of_nat (length T)))].
    Hypothesis TRB : u64arr asegs m (bv_unsigned sp + -2128 + 16) (map wz T ++ rest).
    Hypothesis TFB : rw_cells asegs m (bv_unsigned sp + -72) [C8 sp].
    Hypothesis F4  : rw_cells asegs m (bv_unsigned sp + -64) [CB 8 jk; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0].

    Theorem put_tail :
      evt asegs (free_ret_post m)
        (MS (enq_regs sp gp tp s7 s8 s9 s10 s11 U size TH qcache t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
            F (Z_to_bv 64 0x96a04) fc None m (seg_rom asegs)).
    Proof.
      pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
      assert (BND : aceil <= lo /\ 4096 <= TH /\ TH + 4096 <= aceil) by (clear - LO THR; destruct THR as [THR']; unfold AHI_LO in *; aunf; lia).
    region_sides. name_bands.
      unfold enq_regs, put_frame, AINST, OI_Q, OT_TQ, OT_CACHE, wz in *.

      step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
      step.

      do 8 step. step. step.

      step. do 7 step. step. step.
      release_frame PFR ST (bv_unsigned sp + -2128).
      apply evt_done. unfold free_ret_post. do 15 eexists. split; [reflexivity|].
      eapply icpt_frame_release; eassumption.
    Qed.
  End PutTail.

  Section Null.
    Variables (x3 x4 x5 x12 x13 x14 x15 x16 x17 : word) (m : mem).
    Hypothesis MI : mem_inv asegs m.
    Hypothesis ST  : stk asegs m lo (bv_unsigned sp + -2128).
    Hypothesis ESO : rw_cells asegs m (bv_unsigned sp + -2128) [C8 (wz (bv_unsigned sp + -2128 + 16)); C8 (wz (Z.of_nat (length T)))].
    Hypothesis TRB : u64arr asegs m (bv_unsigned sp + -2128 + 16) (map wz T ++ rest).
    Hypothesis TFB : rw_cells asegs m (bv_unsigned sp + -72) [C8 sp].
    Hypothesis F4  : rw_cells asegs m (bv_unsigned sp + -64) [CB 8 jk; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra0].

    Theorem dealloc_null :
      evt asegs (fun ms' => exists m', free_ret_post m' ms' /\ munch [(lo, bv_unsigned sp + -2128)] m m' /\ wmono asegs m m' /\ mem_inv asegs m')
        (MS (mkR (wz 0xba2bc) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x3 x4 x5 sp (wz 0) (wz AINST) (wz 0) (wz 0) (wz 0)
                 (Z_to_bv 64 (bv_unsigned sp + -2128)) (wz 1) x12 x13 (wz 0xba24c) (wz 1)
                 (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81)) s6 s7 s8 s9 s10 s11 x14 x15 x16 x17)
            F (Z_to_bv 64 0x92188) fc None m (seg_rom asegs)).
    Proof.
      pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64)%Z in SPR.
      pose proof (munch_refl [(lo, bv_unsigned sp + -2128)] m) as MU. pose proof (wmono_refl asegs m) as WM.
      acb. unfold AINST, wz in *.

      step. carve_frame 64%nat ST. do 8 st1.
      step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
      do 8 step. step. step.
      release_frame FR ST (bv_unsigned sp + -2128).

      step. do 7 step. step. step.
      apply evt_done. eexists. split; [| split; [exact MU| split; [exact WM| assumption]]].
      unfold free_ret_post. do 15 eexists. split; [reflexivity|].
      eapply icpt_frame_release; eassumption.
    Qed.
  End Null.
End HCW.
