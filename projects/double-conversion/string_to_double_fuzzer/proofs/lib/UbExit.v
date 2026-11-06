(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic UbExitBase.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes Spec LibWritev UbStdioDefs UbStdioWrite.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec Ub_code_32468_33000 Ub_code_96000_97000 Ub_code_9b000_9c000 Ub_code_a7000_a8000 Ub_code_drv         .
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast LiaTier.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast2.


Module RefExit_run1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StepTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Hoare OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.WalkTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StreamSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MmapSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibAtomic OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbExitBase.



Import ListNotations.
Open Scope bv_scope.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).



Lemma rdn_wbytes_hit4 : forall segs m (a v : word),
  (bv_unsigned a + 4 <= 2^64)%Z ->
  rdn segs (wbytes m a (word_to_le_bytes 4 v)) a 4%nat = Some (word_to_le_bytes 4 v).
Proof.
  intros segs m a v Hnw.
  pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 v) m a) as H.
  rewrite length_N_to_le_bytes in H. apply H. exact Hnw.
Qed.

Ltac rdn_hit4 := apply rdn_wbytes_hit4; zsimp; lia.

Section FPW_1. Context {fx : PropExec.FPState}.

Definition mem_w1 (mem : word -> option byte) (sp ra s0 : word) (tid : Z) (code s1v s2v s3v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 0xe5280) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x967f0)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3v))
    (Z_to_bv 64 0xe5060) [Z_to_bv 8 1].

#[using="Type"] Lemma w1 : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0xe5280) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  
  rdn RSEGS mem (Z_to_bv 64 0xe52ab) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0xe5064) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0xe5070) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x9678c : word) mem rom)
                 (mkst regs' (0x96740 : word) (mem_w1 mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x967f4
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Matl Math.
  unfold mem_w1. eexists. split.
  - 
    stepn F_9678c D_9678c. rewrite Hsp. sp_renorm.
    
    stepST F_96790 D_96790 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_96794 D_96794 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    
    stepn F_96798 D_96798.
    stepn F_9679c D_9679c. rewrite Htp.
    
    stepLD F_967a0 D_967a0 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    
    stepn F_967a4 D_967a4.
    stepn F_967a8 D_967a8.
    
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_967ac | reflexivity | exact D_967ac
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_967b0 | reflexivity | exact D_967b0 | gres; cond_compute ] | ].
    norm_pc_r.
    
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_967b4 | reflexivity | exact D_967b4
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    
    stepb_ft F_967b8 D_967b8 ltac:(cond_compute).
    
    stepn F_967bc D_967bc.
    
    stepb_ft F_967c0 D_967c0 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    
    stepb_tk F_967c4 D_967c4 ltac:(cond_compute).
    
    stepn F_967e8 D_967e8. rewrite Ha0.
    
    stepn F_967ec D_967ec.
    
    stepn F_964e0 D_964e0. sp_renorm.
    stepST F_964e4 D_964e4 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x967f0) ltac:(sok_stack SOK).
    stepST F_964e8 D_964e8 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_964ec D_964ec (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_964f0 D_964f0 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_964f4 D_964f4 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    
    stepn F_964f8 D_964f8.
    stepn F_964fc D_964fc.
    stepn F_96500 D_96500.
    stepn F_96504 D_96504.
    
    stepn F_96508 D_96508.
    stepn F_a7a18 D_a7a18.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_a7a1c | reflexivity | exact D_a7a1c | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_a7a20 D_a7a20 ltac:(cond_compute).
    stepret F_a7c10 D_a7c10 (0x9650c : word) ltac:(bveq).
    
    stepLD8 F_9650c D_9650c (Z_to_bv 64 0).
    stepb_tk F_96510 D_96510 ltac:(cond_compute).
    
    stepn F_96580 D_96580.
    stepST F_96584 D_96584 (Z_to_bv 64 0xe5060) (Z_to_bv 64 1) ltac:(sok_data).
    stepn F_96588 D_96588.
    
    stepLD8 F_9658c D_9658c (Z_to_bv 64 0x967f0).
    stepLD8 F_96590 D_96590 code.
    stepLD8 F_96594 D_96594 (getr regs 9).
    stepLD8 F_96598 D_96598 (getr regs 18).
    stepLD8 F_9659c D_9659c (getr regs 19).
    stepn F_965a0 D_965a0. sp_renorm.
    
    stepn F_965a4 D_965a4.
    stepLD F_a7ca0 D_a7ca0 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_a7ca4 D_a7ca4 ltac:(cond_compute).
    stepret F_a7ca8 D_a7ca8 (0x967f0 : word) ltac:(bveq).
    
    stepn F_967f0 D_967f0.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.


Definition mem_w1o (mem : word -> option byte) (sp ra s0 : word) (tid : Z) (code s1v s2v s3v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 0xe5280) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x967f0)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3v))
    (Z_to_bv 64 0xe5068) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0xe5068) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0xe5068) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0xe5070) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0xe5060) [Z_to_bv 8 1].

#[using="Type"] Lemma w1o : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0xe5280) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  
  rdn RSEGS mem (Z_to_bv 64 0xe52ab) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0xe5064) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0xe5068) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn RSEGS mem (Z_to_bv 64 0xe5070) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe5078)) ->
  rdn RSEGS mem (Z_to_bv 64 0xe5078) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0xe5080) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x96738)) ->
  rdn RSEGS mem (Z_to_bv 64 0xe5180) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x32a5c)) ->
  rdn RSEGS mem (Z_to_bv 64 0xc35f4) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x9678c : word) mem rom)
                 (mkst regs' (0x96740 : word) (mem_w1o mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x967f4
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Matl Msl Mhd Mnx Mf0 Ma0 Mcb.
  unfold mem_w1o. eexists. split.
  - 
    stepn F_9678c D_9678c. rewrite Hsp. sp_renorm.
    
    stepST F_96790 D_96790 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_96794 D_96794 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    
    stepn F_96798 D_96798.
    stepn F_9679c D_9679c. rewrite Htp.
    
    stepLD F_967a0 D_967a0 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    
    stepn F_967a4 D_967a4.
    stepn F_967a8 D_967a8.
    
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_967ac | reflexivity | exact D_967ac
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_967b0 | reflexivity | exact D_967b0 | gres; cond_compute ] | ].
    norm_pc_r.
    
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_967b4 | reflexivity | exact D_967b4
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    
    stepb_ft F_967b8 D_967b8 ltac:(cond_compute).
    
    stepn F_967bc D_967bc.
    
    stepb_ft F_967c0 D_967c0 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    
    stepb_tk F_967c4 D_967c4 ltac:(cond_compute).
    
    stepn F_967e8 D_967e8. rewrite Ha0.
    
    stepn F_967ec D_967ec.
    
    stepn F_964e0 D_964e0. sp_renorm.
    stepST F_964e4 D_964e4 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x967f0) ltac:(sok_stack SOK).
    stepST F_964e8 D_964e8 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_964ec D_964ec (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_964f0 D_964f0 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_964f4 D_964f4 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    
    stepn F_964f8 D_964f8.
    stepn F_964fc D_964fc.
    stepn F_96500 D_96500.
    stepn F_96504 D_96504.
    
    stepn F_96508 D_96508.
    stepn F_a7a18 D_a7a18.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_a7a1c | reflexivity | exact D_a7a1c | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_a7a20 D_a7a20 ltac:(cond_compute).
    stepret F_a7c10 D_a7c10 (0x9650c : word) ltac:(bveq).
    
    
    stepLD8 F_9650c D_9650c (Z_to_bv 64 0xe5078).
    stepb_ft F_96510 D_96510 ltac:(cond_compute).
    stepLD F_96514 D_96514 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepn F_96518 D_96518.
    
    stepn F_96530 D_96530.
    stepST F_96534 D_96534 (Z_to_bv 64 0xe5068) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_96538 D_96538 ltac:(cond_compute).
    
    stepLD8 F_9653c D_9653c (Z_to_bv 64 0xe5078).
    stepn F_96540 D_96540.
    stepn F_96544 D_96544.
    stepLD8 F_96548 D_96548 (Z_to_bv 64 0x96738).
    stepLD8 F_9654c D_9654c (Z_to_bv 64 0x32a5c).
    
    stepn F_96550 D_96550.
    stepn F_96554 D_96554.
    stepLD F_a7ca0 D_a7ca0 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_a7ca4 D_a7ca4 ltac:(cond_compute).
    stepret F_a7ca8 D_a7ca8 (0x96558 : word) ltac:(bveq).
    
    stepn F_96558 D_96558.
    stepjr F_9655c D_9655c (Z_to_bv 64 0x96738) ltac:(gres; reflexivity). vnorm.
    stepjr F_96738 D_96738 (Z_to_bv 64 0x32a5c) ltac:(gres; reflexivity). vnorm.
    stepn F_32a5c D_32a5c.
    stepLBU F_32a60 D_32a60 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_32a64 D_32a64 ltac:(cond_compute).
    stepret F_32a68 D_32a68 (0x96560 : word) ltac:(bveq).
    
    stepn F_96560 D_96560.
    stepn F_96564 D_96564.
    stepn F_a7a18 D_a7a18.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_a7a1c | reflexivity | exact D_a7a1c | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_a7a20 D_a7a20 ltac:(cond_compute).
    stepret F_a7c10 D_a7c10 (0x96568 : word) ltac:(bveq).
    
    stepLD F_96568 D_96568 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_hit4) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepn F_9656c D_9656c.
    stepST F_96570 D_96570 (Z_to_bv 64 0xe5068) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_96574 D_96574 ltac:(cond_compute).
    
    stepLD8 F_96578 D_96578 (Z_to_bv 64 0xe5078).
    stepn F_9657c D_9657c.
    stepLD8 F_9651c D_9651c (Z_to_bv 64 0).
    
    stepn F_96520 D_96520.
    stepST F_96524 D_96524 (Z_to_bv 64 0xe5068) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_96528 D_96528 (Z_to_bv 64 0xe5070) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_9652c D_9652c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_96580 D_96580.
    stepST F_96584 D_96584 (Z_to_bv 64 0xe5060) (Z_to_bv 64 1) ltac:(sok_data).
    stepn F_96588 D_96588.
    (* [comment removed for export] *)
    stepLD8 F_9658c D_9658c (Z_to_bv 64 0x967f0).
    stepLD8 F_96590 D_96590 code.
    stepLD8 F_96594 D_96594 (getr regs 9).
    stepLD8 F_96598 D_96598 (getr regs 18).
    stepLD8 F_9659c D_9659c (getr regs 19).
    stepn F_965a0 D_965a0. sp_renorm.
    (* [comment removed for export] *)
    stepn F_965a4 D_965a4.
    stepLD F_a7ca0 D_a7ca0 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_a7ca4 D_a7ca4 ltac:(cond_compute).
    stepret F_a7ca8 D_a7ca8 (0x967f0 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_967f0 D_967f0.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.

(* [comment removed for export] *)
Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x967f4)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x96770)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0xacdf8)))
    (Z_to_bv 64 0xb35e8) [Z_to_bv 8 1].

#[using="Type"] Lemma w2 : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x967f4 -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0xb22b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xace00)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb22b8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xacdf8)) ->
  rdn RSEGS mem (Z_to_bv 64 0xacdf8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x325a4)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb35e8) 1%nat = Some [Z_to_bv 8 0] ->
  (* [comment removed for export] *)
  rdn RSEGS mem (Z_to_bv 64 0xb2168) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x965a8)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb2170) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb32d8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb32d8)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x96740 : word) mem rom)
                 (mkst regs' (0x9bc68 : word) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x967f8
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2. eexists. split.
  - (* [comment removed for export] *)
    stepn F_96740 D_96740. rewrite Hsp. sp_renorm.
    stepST F_96744 D_96744 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x967f4) ltac:(sok_stack SOK).
    stepST F_96748 D_96748 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_9674c D_9674c (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_96750 D_96750.
    stepn F_96754 D_96754.
    stepLD8 F_96758 D_96758 (Z_to_bv 64 0xace00).
    stepLD8 F_9675c D_9675c (Z_to_bv 64 0xacdf8).
    (* [comment removed for export] *)
    stepb_ft F_96760 D_96760 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_96764 D_96764 (Z_to_bv 64 0x325a4).
    stepn F_96768 D_96768.
    stepjr F_9676c D_9676c (Z_to_bv 64 0x325a4) ltac:(gres; reflexivity). vnorm.
    (* [comment removed for export] *)
    stepn F_325a4 D_325a4. sp_renorm.
    stepST F_325a8 D_325a8 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x96770) ltac:(sok_stack SOK).
    stepST F_325ac D_325ac (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0xacdf8) ltac:(sok_stack SOK).
    stepn F_325b0 D_325b0.
    stepn F_325b4 D_325b4.
    stepn F_325b8 D_325b8.
    (* [comment removed for export] *)
    stepLBU F_325bc D_325bc (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
    stepn F_325c0 D_325c0.
    stepb_tk F_325c4 D_325c4 ltac:(cond_compute).
    stepn F_325d0 D_325d0.
    stepn F_325d4 D_325d4.
    stepn F_325d8 D_325d8.
    (* [comment removed for export] *)
    stepST F_325dc D_325dc (Z_to_bv 64 0xb35e8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_325e0 D_325e0.
    stepLD8 F_325e4 D_325e4 (Z_to_bv 64 0x965a8).
    stepb_ft F_325e8 D_325e8 ltac:(cond_compute).
    stepn F_325ec D_325ec.
    stepn F_325f0 D_325f0.
    stepn F_325f4 D_325f4.
    stepLD8 F_325f8 D_325f8 (Z_to_bv 64 0xb32d8).
    stepn F_325fc D_325fc.
    stepret F_965a8 D_965a8 (0x32600 : word) ltac:(bveq).
    stepn F_32600 D_32600.
    (* [comment removed for export] *)
    stepn F_32604 D_32604.
    stepLD8 F_32608 D_32608 (Z_to_bv 64 0).
    stepb_tk F_3260c D_3260c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_32624 D_32624 (Z_to_bv 64 0x96770).
    stepLD8 F_32628 D_32628 (Z_to_bv 64 0xacdf8).
    stepn F_3262c D_3262c. sp_renorm.
    stepret F_32630 D_32630 (0x96770 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_96770 D_96770.
    stepb_ft F_96774 D_96774 ltac:(cond_compute).
    stepLD8 F_96778 D_96778 (Z_to_bv 64 0x967f4).
    stepLD8 F_9677c D_9677c code.
    stepLD8 F_96780 D_96780 s1v.
    stepn F_96784 D_96784. sp_renorm.
    (* [comment removed for export] *)
    stepn F_96788 D_96788.
    stepret F_9673c D_9673c (0x967f4 : word) ltac:(bveq).
    stepn F_967f4 D_967f4.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
End FPW_1.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefExit_run1.

(* [comment removed for export] *)
Module RefExit_run2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StepTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Hoare OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.WalkTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StreamSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MmapSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibAtomic OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbExitBase.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPW_2. Context {fx : PropExec.FPState}.


Definition mem_w3a (mem : word -> option byte) (sp code : word) :=
  wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x967f8)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x9bc78)))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

#[using="Type"] Lemma w3a : forall regs mem rom (sp code wp1 rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x967f8 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  file_clean mem 0xb3488 wp1 rp1 ->
  file_clean mem 0xb3398 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x9bc68 : word) mem rom)
                 (mkst regs' (0x9649c : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  intros regs mem rom sp code wp1 rp1 wp2 rp2 Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr)
         (F1l & F1wp & F1wb & F1rp & F1re) (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  unfold mem_w3a. eexists. split.
  - (* [comment removed for export] *)
    stepn F_9bc68 D_9bc68. rewrite Hsp. sp_renorm.
    stepST F_9bc6c D_9bc6c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x967f8) ltac:(sok_stack SOK).
    stepST F_9bc70 D_9bc70 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_9bc74 D_9bc74.
    stepn F_9bffc D_9bffc. sp_renorm.
    stepST F_9c000 D_9c000 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x9bc78) ltac:(sok_stack SOK).
    stepST F_9c004 D_9c004 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_9c008 D_9c008.
    stepn F_9c00c D_9c00c.
    stepn F_9c010 D_9c010.
    (* [comment removed for export] *)
    stepn F_9c014 D_9c014.
    stepn F_a7a18 D_a7a18.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_a7a1c | reflexivity | exact D_a7a1c | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_a7a20 D_a7a20 ltac:(cond_compute).
    stepret F_a7c10 D_a7c10 (0x9c018 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_9c018 D_9c018.
    stepLD8 F_9c01c D_9c01c (Z_to_bv 64 0x9bc78).
    stepLD8 F_9c020 D_9c020 code.
    stepn F_9c024 D_9c024. sp_renorm.
    stepret F_9c028 D_9c028 (0x9bc78 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_9bc78 D_9bc78 (Z_to_bv 64 0).
    stepb_ft F_9bc7c D_9bc7c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_9bc80 D_9bc80.
    stepLD8 F_9bc84 D_9bc84 (Z_to_bv 64 0).
    stepb_tk F_9bc88 D_9bc88 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_9bcdc D_9bcdc.
    stepLD8 F_9bce0 D_9bce0 (Z_to_bv 64 0xb3488).
    stepb_ft F_9bce4 D_9bce4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_9bce8 D_9bce8 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_9bcec D_9bcec ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_9bcf8 D_9bcf8 wp1.
    stepLD8 F_9bcfc D_9bcfc wp1.
    stepb_tk F_9bd00 D_9bd00 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_9bd18 D_9bd18 rp1.
    stepLD8 F_9bd1c D_9bd1c rp1.
    stepb_tk F_9bd20 D_9bd20 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_9bd38 D_9bd38.
    stepLD8 F_9bd3c D_9bd3c (Z_to_bv 64 0xb3398).
    stepb_ft F_9bd40 D_9bd40 ltac:(cond_compute).
    stepLD F_9bd44 D_9bd44 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_9bd48 D_9bd48 ltac:(cond_compute).
    stepLD8 F_9bd54 D_9bd54 wp2.
    stepLD8 F_9bd58 D_9bd58 wp2.
    stepb_tk F_9bd5c D_9bd5c ltac:(apply c_eq_refl).
    stepLD8 F_9bd74 D_9bd74 rp2.
    stepLD8 F_9bd78 D_9bd78 rp2.
    stepb_tk F_9bd7c D_9bd7c ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_9bdfc D_9bdfc (Z_to_bv 64 0x967f8).
    stepLD8 F_9be00 D_9be00 code.
    stepn F_9be04 D_9be04. sp_renorm.
    stepret F_9be08 D_9be08 (0x967f8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_967f8 D_967f8.
    stepn F_967fc D_967fc.
    stepn F_96494 D_96494.
    stepn F_96498 D_96498.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
End FPW_2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefExit_run2.

(* [comment removed for export] *)
Module RefExit_run3.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StepTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Hoare OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.WalkTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StreamSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MmapSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibAtomic OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbExitBase RefExit_run2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section FPW_3. Context {fx : PropExec.FPState}.

Definition stdout_dirty_hdr (mem : word -> option byte) (wb wp : Z) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 (0xb3488 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn RSEGS mem (Z_to_bv 64 (0xb3488 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
  /\ rdn RSEGS mem (Z_to_bv 64 (0xb3488 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
  /\ rdn RSEGS mem (Z_to_bv 64 (0xb3488 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x9c12c)).

#[using="Type"] Lemma w3b1 : forall regs mem rom (sp code : word) (wb wp : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x967f8 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  stdout_dirty_hdr mem wb wp ->
  (0 <= wb < 2^64)%Z -> (0 <= wp < 2^64)%Z -> wb <> wp ->
  exists regs',
    msteps RSEGS (mkst regs (0x9bc68 : word) mem rom)
                 (mkst regs' (0x9c12c : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = Z_to_bv 64 0xb3488
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 1 = Z_to_bv 64 0x9bd18
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32)
    /\ getr regs' 8 = Z_to_bv 64 0xb3488
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof.
  intros regs mem rom sp code wb wp Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr) (F1l & F1wp & F1wb & F1wr) WB WP NE.
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
  unfold mem_w3a. eexists. split.
  - (* [comment removed for export] *)
    stepn F_9bc68 D_9bc68. rewrite Hsp. sp_renorm.
    stepST F_9bc6c D_9bc6c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x967f8) ltac:(sok_stack SOK).
    stepST F_9bc70 D_9bc70 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_9bc74 D_9bc74.
    stepn F_9bffc D_9bffc. sp_renorm.
    stepST F_9c000 D_9c000 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x9bc78) ltac:(sok_stack SOK).
    stepST F_9c004 D_9c004 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_9c008 D_9c008.
    stepn F_9c00c D_9c00c.
    stepn F_9c010 D_9c010.
    (* [comment removed for export] *)
    stepn F_9c014 D_9c014.
    stepn F_a7a18 D_a7a18.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_a7a1c | reflexivity | exact D_a7a1c | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_a7a20 D_a7a20 ltac:(cond_compute).
    stepret F_a7c10 D_a7c10 (0x9c018 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_9c018 D_9c018.
    stepLD8 F_9c01c D_9c01c (Z_to_bv 64 0x9bc78).
    stepLD8 F_9c020 D_9c020 code.
    stepn F_9c024 D_9c024. sp_renorm.
    stepret F_9c028 D_9c028 (0x9bc78 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_9bc78 D_9bc78 (Z_to_bv 64 0).
    stepb_ft F_9bc7c D_9bc7c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_9bc80 D_9bc80.
    stepLD8 F_9bc84 D_9bc84 (Z_to_bv 64 0).
    stepb_tk F_9bc88 D_9bc88 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_9bcdc D_9bcdc.
    stepLD8 F_9bce0 D_9bce0 (Z_to_bv 64 0xb3488).
    stepb_ft F_9bce4 D_9bce4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_9bce8 D_9bce8 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_9bcec D_9bcec ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_9bcf8 D_9bcf8 (Z_to_bv 64 wp).
    stepLD8 F_9bcfc D_9bcfc (Z_to_bv 64 wb).
    stepb_ft F_9bd00 D_9bd00 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepLD8 F_9bd04 D_9bd04 (Z_to_bv 64 0x9c12c).
    stepn F_9bd08 D_9bd08.
    stepn F_9bd0c D_9bd0c.
    stepn F_9bd10 D_9bd10.
    stepjr F_9bd14 D_9bd14 (Z_to_bv 64 0x9c12c) ltac:(gres; reflexivity). vnorm.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma w3b2 : forall regs mem rom (sp code rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 32) -> getr regs 8 = Z_to_bv 64 0xb3488 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x967f8)) ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 code) ->
  rdn RSEGS mem (Z_to_bv 64 (0xb3488 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 (0xb3488 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 0xb3480) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb3398)) ->
  file_clean mem 0xb3398 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x9bd18 : word) mem rom)
                 (mkst regs' (0x9649c : word) mem rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr
         (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_9bd18 D_9bd18 rp1.
    stepLD8 F_9bd1c D_9bd1c rp1.
    stepb_tk F_9bd20 D_9bd20 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_9bd38 D_9bd38.
    stepLD8 F_9bd3c D_9bd3c (Z_to_bv 64 0xb3398).
    stepb_ft F_9bd40 D_9bd40 ltac:(cond_compute).
    stepLD F_9bd44 D_9bd44 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_9bd48 D_9bd48 ltac:(cond_compute).
    stepLD8 F_9bd54 D_9bd54 wp2.
    stepLD8 F_9bd58 D_9bd58 wp2.
    stepb_tk F_9bd5c D_9bd5c ltac:(apply c_eq_refl).
    stepLD8 F_9bd74 D_9bd74 rp2.
    stepLD8 F_9bd78 D_9bd78 rp2.
    stepb_tk F_9bd7c D_9bd7c ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_9bdfc D_9bdfc (Z_to_bv 64 0x967f8).
    stepLD8 F_9be00 D_9be00 code.
    stepn F_9be04 D_9be04. rewrite Hsp. sp_renorm.
    stepret F_9be08 D_9be08 (0x967f8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_967f8 D_967f8.
    stepn F_967fc D_967fc.
    stepn F_96494 D_96494.
    stepn F_96498 D_96498.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End FPW_3.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End RefExit_run3.

(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StepTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Hoare OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.WalkTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StreamSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MmapSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibAtomic OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ExitSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ShapeAlg OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Nodes OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Spec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibWritev OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbStdioDefs RefExit_run1 RefExit_run2 RefExit_run3 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbStdioWrite.RefStdioWrite_run1 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbStdioWrite.RefStdioWrite_run2 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.UbStdioWrite.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac zaddr_rec H := zaddr H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPW_4. Context {fx : PropExec.FPState}.


#[using="Type"] Theorem ref_exit_clean :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  file_clean mem 0xb3488 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x9678c : word) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wp1 rp1 EC F1 Hh Hlazy.
  destruct EC.
  (* [comment removed for export] *)
  destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct (w1 regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
    try assumption.
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
  (* [comment removed for export] *)
  destruct (w2 regs1 (mem_w1 mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) (seg_rom RSEGS) sp code (getr regs1 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  all: try (unfold mem_w1; first [store_ok_peel; exact ec_sok | rdn_solve]).
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  (* [comment removed for export] *)
  destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
  destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  destruct (w3a regs2 (mem_w2 (mem_w1 mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wp1 rp1 wp2 rp2)
    as (regs3 & RUN3 & R3a0 & R3a7 & R3sp); try assumption.
  1:{ unfold mem_w2, mem_w1; store_ok_peel; exact ec_sok. }
  1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2, mem_w1; rdn_solve. }
  1:{ repeat split; unfold mem_w2, mem_w1; zaddr_goal; rdn_solve. }
  1:{ repeat split; unfold mem_w2, mem_w1; zaddr_goal; rdn_solve. }
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  eapply rz_exit_at; [exact F_9649c | exact E_9649c | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Theorem ref_exit_flush :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  realizes RSEGS (mkCfg (mkst regs (0x9678c : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd.
  destruct EC. destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
  zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
  (* [comment removed for export] *)
  destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct (w1 regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
    try assumption.
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
  (* [comment removed for export] *)
  destruct (w2 regs1 (mem_w1 mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) (seg_rom RSEGS) sp code (getr regs1 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  all: try (unfold mem_w1; first [store_ok_peel; exact ec_sok | rdn_solve]).
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  (* [comment removed for export] *)
  destruct (w3b1 regs2 (mem_w2 (mem_w1 mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wb wp)
    as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
  1:{ unfold mem_w2, mem_w1; store_ok_peel; exact ec_sok. }
  1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2, mem_w1; rdn_solve. }
  1:{ repeat split; unfold mem_w2, mem_w1; zaddr_goal; rdn_solve. }
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0x9bd18) with (0x9bd18 : word) in R3ra by (apply bv_eq; reflexivity).
  unfold W. rewrite <- (app_nil_r pending).
  set (mem3 := mem_w3a (mem_w2 (mem_w1 mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9)) sp code).
  eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) 0xb3488 wb wp 1
            (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x9bd18 : word) pending []);
    [ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
    | lia | lia
    | (* [comment removed for export] *)
      subst mem3; unfold mem_w3a, mem_w2, mem_w1; sok_stack ec_sok
    | lia | lia
    | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a, mem_w2, mem_w1; zaddr_goal; rdn_solve
    | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a, mem_w2, mem_w1; rdn_solve
    | lia | exact Hfd | exact Hh | exact Hlazy
    | lia | lia | exact LEN
    | cbn [length]; u_norm; reflexivity
    | cbn [length]; lia
    | cbn [length]; lia
    | lia | u_norm; lia | u_norm; lia
    | subst mem3; unfold mem_w3a, mem_w2, mem_w1; repeat rdn_peel1; exact BYTES
    | reflexivity
    | apply ret_ok_even; reflexivity
    | apply t_emit_has_nil
    | ].
  intros regs4 mem4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
    rewrite R3s0 in Q8.
    destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
    zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
    destruct (w3b2 regs4 mem4 (seg_rom RSEGS) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
    all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
    1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
    eapply rz_exit_at; [exact F_9649c | exact E_9649c | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
  intros code fs. apply t_eq_sym. apply t_emit_nil_eq.
  unfold t_exit, t_emit. left. apply is_prefix_nil.
Qed.

#[using="Type"] Theorem ref_exit : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (0x9678c : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES).
  destruct CASES as [(-> & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd)].
  - eapply rz_conseq; [ | apply t_emit_nil_exit ].
    eapply ref_exit_clean; eassumption.
  - eapply ref_exit_flush; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Corollary ref_exit_Z : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x9678c) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros. replace (Z_to_bv 64 0x9678c) with (0x9678c : word) by (apply bv_eq; reflexivity).
  apply ref_exit; assumption.
Qed.

#[using="Type"] Theorem ref_exit1_clean :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
  exit_common1 regs mem sp tp code tid wp2 rp2 ->
  file_clean mem 0xb3488 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x9678c : word) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wp1 rp1 EC F1 Hh Hlazy.
  destruct EC.
  (* [comment removed for export] *)
  destruct ec1_glob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct (w1o regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
    try assumption.
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
  (* [comment removed for export] *)
  destruct (w2 regs1 (mem_w1o mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) (seg_rom RSEGS) sp code (getr regs1 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  all: try (unfold mem_w1o; first [store_ok_peel; exact ec1_sok | rdn_solve]).
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  (* [comment removed for export] *)
  destruct ec1_err as (F2l & F2wp & F2wb & F2rp & F2re).
  destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  destruct (w3a regs2 (mem_w2 (mem_w1o mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wp1 rp1 wp2 rp2)
    as (regs3 & RUN3 & R3a0 & R3a7 & R3sp); try assumption.
  1:{ unfold mem_w2, mem_w1o; store_ok_peel; exact ec1_sok. }
  1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2, mem_w1o; rdn_solve. }
  1:{ repeat split; unfold mem_w2, mem_w1o; zaddr_goal; rdn_solve. }
  1:{ repeat split; unfold mem_w2, mem_w1o; zaddr_goal; rdn_solve. }
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  eapply rz_exit_at; [exact F_9649c | exact E_9649c | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.

#[using="Type"] Theorem ref_exit1_flush :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_common1 regs mem sp tp code tid wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  realizes RSEGS (mkCfg (mkst regs (0x9678c : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd.
  destruct EC. destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
  zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
  (* [comment removed for export] *)
  destruct ec1_glob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct (w1o regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
    try assumption.
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
  (* [comment removed for export] *)
  destruct (w2 regs1 (mem_w1o mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) (seg_rom RSEGS) sp code (getr regs1 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  all: try (unfold mem_w1o; first [store_ok_peel; exact ec1_sok | rdn_solve]).
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  (* [comment removed for export] *)
  destruct (w3b1 regs2 (mem_w2 (mem_w1o mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wb wp)
    as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
  1:{ unfold mem_w2, mem_w1o; store_ok_peel; exact ec1_sok. }
  1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2, mem_w1o; rdn_solve. }
  1:{ repeat split; unfold mem_w2, mem_w1o; zaddr_goal; rdn_solve. }
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0x9bd18) with (0x9bd18 : word) in R3ra by (apply bv_eq; reflexivity).
  unfold W. rewrite <- (app_nil_r pending).
  set (mem3 := mem_w3a (mem_w2 (mem_w1o mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9)) sp code).
  eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) 0xb3488 wb wp 1
            (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x9bd18 : word) pending []);
    [ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
    | lia | lia
    | (* [comment removed for export] *)
      subst mem3; unfold mem_w3a, mem_w2, mem_w1o; sok_stack ec1_sok
    | lia | lia
    | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a, mem_w2, mem_w1o; zaddr_goal; rdn_solve
    | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a, mem_w2, mem_w1o; rdn_solve
    | lia | exact Hfd | exact Hh | exact Hlazy
    | lia | lia | exact LEN
    | cbn [length]; u_norm; reflexivity
    | cbn [length]; lia
    | cbn [length]; lia
    | lia | u_norm; lia | u_norm; lia
    | subst mem3; unfold mem_w3a, mem_w2, mem_w1o; repeat rdn_peel1; exact BYTES
    | reflexivity
    | apply ret_ok_even; reflexivity
    | apply t_emit_has_nil
    | ].
  intros regs4 mem4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
    rewrite R3s0 in Q8.
    destruct ec1_err as (F2l & F2wp & F2wb & F2rp & F2re).
    zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
    destruct (w3b2 regs4 mem4 (seg_rom RSEGS) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
    all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1o; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
    1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1o; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
    eapply rz_exit_at; [exact F_9649c | exact E_9649c | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.

#[using="Type"] Theorem ref_exit1 : forall regs mem model code pending,
  exit_pre1 regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (0x9678c : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES).
  destruct CASES as [(-> & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd)].
  - eapply rz_conseq; [ | apply t_emit_nil_exit ].
    eapply ref_exit1_clean; eassumption.
  - eapply ref_exit1_flush; eassumption.
Qed.

#[using="Type"] Corollary ref_exit1_Z : forall regs mem model code pending,
  exit_pre1 regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x9678c) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros. replace (Z_to_bv 64 0x9678c) with (0x9678c : word) by (apply bv_eq; reflexivity).
  apply ref_exit1; assumption.
Qed.
End FPW_4.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
