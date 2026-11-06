(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)



From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic RefExitBase.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes Spec LibWritev RefStdioDefs RefStdioWrite.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec Ref_code_323a8_33000 Ref_code_95000_96000 Ref_code_9b000_9c000 Ref_code_a7000_a8000 Ref_code_drv      .
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LiaFast LiaTier.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac Lia.lia ::= lia_fast2.


Module RefExit_run1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StepTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Hoare OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.WalkTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StreamSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MmapSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibAtomic OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefExitBase.



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
    (Z_to_bv 64 0xe4b80) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x960f8)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3v))
    (Z_to_bv 64 0xe4960) [Z_to_bv 8 1].

#[using="Type"] Lemma w1 : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0xe4b80) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  
  rdn RSEGS mem (Z_to_bv 64 0xe4bab) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0xe4964) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0xe4970) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x96094 : word) mem rom)
                 (mkst regs' (0x96048 : word) (mem_w1 mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x960fc
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Matl Math.
  unfold mem_w1. eexists. split.
  - 
    stepn F_96094 D_96094. rewrite Hsp. sp_renorm.
    
    stepST F_96098 D_96098 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_9609c D_9609c (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    
    stepn F_960a0 D_960a0.
    stepn F_960a4 D_960a4. rewrite Htp.
    
    stepLD F_960a8 D_960a8 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    
    stepn F_960ac D_960ac.
    stepn F_960b0 D_960b0.
    
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_960b4 | reflexivity | exact D_960b4
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_960b8 | reflexivity | exact D_960b8 | gres; cond_compute ] | ].
    norm_pc_r.
    
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_960bc | reflexivity | exact D_960bc
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    
    stepb_ft F_960c0 D_960c0 ltac:(cond_compute).
    
    stepn F_960c4 D_960c4.
    
    stepb_ft F_960c8 D_960c8 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    
    stepb_tk F_960cc D_960cc ltac:(cond_compute).
    
    stepn F_960f0 D_960f0. rewrite Ha0.
    
    stepn F_960f4 D_960f4.
    
    stepn F_95de8 D_95de8. sp_renorm.
    stepST F_95dec D_95dec (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x960f8) ltac:(sok_stack SOK).
    stepST F_95df0 D_95df0 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_95df4 D_95df4 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_95df8 D_95df8 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_95dfc D_95dfc (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    
    stepn F_95e00 D_95e00.
    stepn F_95e04 D_95e04.
    stepn F_95e08 D_95e08.
    stepn F_95e0c D_95e0c.
    
    stepn F_95e10 D_95e10.
    stepn F_a7320 D_a7320.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_a7324 | reflexivity | exact D_a7324 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_a7328 D_a7328 ltac:(cond_compute).
    stepret F_a7518 D_a7518 (0x95e14 : word) ltac:(bveq).
    
    stepLD8 F_95e14 D_95e14 (Z_to_bv 64 0).
    stepb_tk F_95e18 D_95e18 ltac:(cond_compute).
    
    stepn F_95e88 D_95e88.
    stepST F_95e8c D_95e8c (Z_to_bv 64 0xe4960) (Z_to_bv 64 1) ltac:(sok_data).
    stepn F_95e90 D_95e90.
    
    stepLD8 F_95e94 D_95e94 (Z_to_bv 64 0x960f8).
    stepLD8 F_95e98 D_95e98 code.
    stepLD8 F_95e9c D_95e9c (getr regs 9).
    stepLD8 F_95ea0 D_95ea0 (getr regs 18).
    stepLD8 F_95ea4 D_95ea4 (getr regs 19).
    stepn F_95ea8 D_95ea8. sp_renorm.
    
    stepn F_95eac D_95eac.
    stepLD F_a75a8 D_a75a8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_a75ac D_a75ac ltac:(cond_compute).
    stepret F_a75b0 D_a75b0 (0x960f8 : word) ltac:(bveq).
    
    stepn F_960f8 D_960f8.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.


Definition mem_w1o (mem : word -> option byte) (sp ra s0 : word) (tid : Z) (code s1v s2v s3v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 0xe4b80) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x960f8)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3v))
    (Z_to_bv 64 0xe4968) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0xe4968) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0xe4968) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0xe4970) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0xe4960) [Z_to_bv 8 1].

#[using="Type"] Lemma w1o : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0xe4b80) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  
  rdn RSEGS mem (Z_to_bv 64 0xe4bab) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0xe4964) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0xe4968) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn RSEGS mem (Z_to_bv 64 0xe4970) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe4978)) ->
  rdn RSEGS mem (Z_to_bv 64 0xe4978) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0xe4980) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x96040)) ->
  rdn RSEGS mem (Z_to_bv 64 0xe4a80) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x3299c)) ->
  rdn RSEGS mem (Z_to_bv 64 0xc2ef4) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x96094 : word) mem rom)
                 (mkst regs' (0x96048 : word) (mem_w1o mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x960fc
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Matl Msl Mhd Mnx Mf0 Ma0 Mcb.
  unfold mem_w1o. eexists. split.
  - 
    stepn F_96094 D_96094. rewrite Hsp. sp_renorm.
    
    stepST F_96098 D_96098 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_9609c D_9609c (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    
    stepn F_960a0 D_960a0.
    stepn F_960a4 D_960a4. rewrite Htp.
    
    stepLD F_960a8 D_960a8 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    
    stepn F_960ac D_960ac.
    stepn F_960b0 D_960b0.
    
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_960b4 | reflexivity | exact D_960b4
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_960b8 | reflexivity | exact D_960b8 | gres; cond_compute ] | ].
    norm_pc_r.
    
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_960bc | reflexivity | exact D_960bc
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    
    stepb_ft F_960c0 D_960c0 ltac:(cond_compute).
    
    stepn F_960c4 D_960c4.
    
    stepb_ft F_960c8 D_960c8 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    
    stepb_tk F_960cc D_960cc ltac:(cond_compute).
    
    stepn F_960f0 D_960f0. rewrite Ha0.
    
    stepn F_960f4 D_960f4.
    
    stepn F_95de8 D_95de8. sp_renorm.
    stepST F_95dec D_95dec (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x960f8) ltac:(sok_stack SOK).
    stepST F_95df0 D_95df0 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_95df4 D_95df4 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_95df8 D_95df8 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_95dfc D_95dfc (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    
    stepn F_95e00 D_95e00.
    stepn F_95e04 D_95e04.
    stepn F_95e08 D_95e08.
    stepn F_95e0c D_95e0c.
    
    stepn F_95e10 D_95e10.
    stepn F_a7320 D_a7320.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_a7324 | reflexivity | exact D_a7324 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_a7328 D_a7328 ltac:(cond_compute).
    stepret F_a7518 D_a7518 (0x95e14 : word) ltac:(bveq).
    
    
    stepLD8 F_95e14 D_95e14 (Z_to_bv 64 0xe4978).
    stepb_ft F_95e18 D_95e18 ltac:(cond_compute).
    stepLD F_95e1c D_95e1c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepn F_95e20 D_95e20.
    
    stepn F_95e38 D_95e38.
    stepST F_95e3c D_95e3c (Z_to_bv 64 0xe4968) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_95e40 D_95e40 ltac:(cond_compute).
    
    stepLD8 F_95e44 D_95e44 (Z_to_bv 64 0xe4978).
    stepn F_95e48 D_95e48.
    stepn F_95e4c D_95e4c.
    stepLD8 F_95e50 D_95e50 (Z_to_bv 64 0x96040).
    stepLD8 F_95e54 D_95e54 (Z_to_bv 64 0x3299c).
    
    stepn F_95e58 D_95e58.
    stepn F_95e5c D_95e5c.
    stepLD F_a75a8 D_a75a8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_a75ac D_a75ac ltac:(cond_compute).
    stepret F_a75b0 D_a75b0 (0x95e60 : word) ltac:(bveq).
    
    stepn F_95e60 D_95e60.
    stepjr F_95e64 D_95e64 (Z_to_bv 64 0x96040) ltac:(gres; reflexivity). vnorm.
    stepjr F_96040 D_96040 (Z_to_bv 64 0x3299c) ltac:(gres; reflexivity). vnorm.
    stepn F_3299c D_3299c.
    stepLBU F_329a0 D_329a0 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_329a4 D_329a4 ltac:(cond_compute).
    stepret F_329a8 D_329a8 (0x95e68 : word) ltac:(bveq).
    
    stepn F_95e68 D_95e68.
    stepn F_95e6c D_95e6c.
    stepn F_a7320 D_a7320.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_a7324 | reflexivity | exact D_a7324 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_a7328 D_a7328 ltac:(cond_compute).
    stepret F_a7518 D_a7518 (0x95e70 : word) ltac:(bveq).
    
    stepLD F_95e70 D_95e70 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_hit4) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepn F_95e74 D_95e74.
    stepST F_95e78 D_95e78 (Z_to_bv 64 0xe4968) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_95e7c D_95e7c ltac:(cond_compute).
    
    stepLD8 F_95e80 D_95e80 (Z_to_bv 64 0xe4978).
    stepn F_95e84 D_95e84.
    stepLD8 F_95e24 D_95e24 (Z_to_bv 64 0).
    
    stepn F_95e28 D_95e28.
    stepST F_95e2c D_95e2c (Z_to_bv 64 0xe4968) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_95e30 D_95e30 (Z_to_bv 64 0xe4970) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_95e34 D_95e34 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_95e88 D_95e88.
    stepST F_95e8c D_95e8c (Z_to_bv 64 0xe4960) (Z_to_bv 64 1) ltac:(sok_data).
    stepn F_95e90 D_95e90.
    (* [comment removed for export] *)
    stepLD8 F_95e94 D_95e94 (Z_to_bv 64 0x960f8).
    stepLD8 F_95e98 D_95e98 code.
    stepLD8 F_95e9c D_95e9c (getr regs 9).
    stepLD8 F_95ea0 D_95ea0 (getr regs 18).
    stepLD8 F_95ea4 D_95ea4 (getr regs 19).
    stepn F_95ea8 D_95ea8. sp_renorm.
    (* [comment removed for export] *)
    stepn F_95eac D_95eac.
    stepLD F_a75a8 D_a75a8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_a75ac D_a75ac ltac:(cond_compute).
    stepret F_a75b0 D_a75b0 (0x960f8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_960f8 D_960f8.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.

(* [comment removed for export] *)
Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x960fc)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x96078)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0xac700)))
    (Z_to_bv 64 0xb2ee8) [Z_to_bv 8 1].

#[using="Type"] Lemma w2 : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x960fc -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0xb1bb8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xac708)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb1bc0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xac700)) ->
  rdn RSEGS mem (Z_to_bv 64 0xac700) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x324e4)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb2ee8) 1%nat = Some [Z_to_bv 8 0] ->
  (* [comment removed for export] *)
  rdn RSEGS mem (Z_to_bv 64 0xb1a70) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x95eb0)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb1a78) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb2be0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb2be0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x96048 : word) mem rom)
                 (mkst regs' (0x9b570 : word) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x96100
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2. eexists. split.
  - (* [comment removed for export] *)
    stepn F_96048 D_96048. rewrite Hsp. sp_renorm.
    stepST F_9604c D_9604c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x960fc) ltac:(sok_stack SOK).
    stepST F_96050 D_96050 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_96054 D_96054 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_96058 D_96058.
    stepn F_9605c D_9605c.
    stepLD8 F_96060 D_96060 (Z_to_bv 64 0xac708).
    stepLD8 F_96064 D_96064 (Z_to_bv 64 0xac700).
    (* [comment removed for export] *)
    stepb_ft F_96068 D_96068 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_9606c D_9606c (Z_to_bv 64 0x324e4).
    stepn F_96070 D_96070.
    stepjr F_96074 D_96074 (Z_to_bv 64 0x324e4) ltac:(gres; reflexivity). vnorm.
    (* [comment removed for export] *)
    stepn F_324e4 D_324e4. sp_renorm.
    stepST F_324e8 D_324e8 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x96078) ltac:(sok_stack SOK).
    stepST F_324ec D_324ec (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0xac700) ltac:(sok_stack SOK).
    stepn F_324f0 D_324f0.
    stepn F_324f4 D_324f4.
    stepn F_324f8 D_324f8.
    (* [comment removed for export] *)
    stepLBU F_324fc D_324fc (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
    stepn F_32500 D_32500.
    stepb_tk F_32504 D_32504 ltac:(cond_compute).
    stepn F_32510 D_32510.
    stepn F_32514 D_32514.
    stepn F_32518 D_32518.
    (* [comment removed for export] *)
    stepST F_3251c D_3251c (Z_to_bv 64 0xb2ee8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_32520 D_32520.
    stepLD8 F_32524 D_32524 (Z_to_bv 64 0x95eb0).
    stepb_ft F_32528 D_32528 ltac:(cond_compute).
    stepn F_3252c D_3252c.
    stepn F_32530 D_32530.
    stepn F_32534 D_32534.
    stepLD8 F_32538 D_32538 (Z_to_bv 64 0xb2be0).
    stepn F_3253c D_3253c.
    stepret F_95eb0 D_95eb0 (0x32540 : word) ltac:(bveq).
    stepn F_32540 D_32540.
    (* [comment removed for export] *)
    stepn F_32544 D_32544.
    stepLD8 F_32548 D_32548 (Z_to_bv 64 0).
    stepb_tk F_3254c D_3254c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_32564 D_32564 (Z_to_bv 64 0x96078).
    stepLD8 F_32568 D_32568 (Z_to_bv 64 0xac700).
    stepn F_3256c D_3256c. sp_renorm.
    stepret F_32570 D_32570 (0x96078 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_96078 D_96078.
    stepb_ft F_9607c D_9607c ltac:(cond_compute).
    stepLD8 F_96080 D_96080 (Z_to_bv 64 0x960fc).
    stepLD8 F_96084 D_96084 code.
    stepLD8 F_96088 D_96088 s1v.
    stepn F_9608c D_9608c. sp_renorm.
    (* [comment removed for export] *)
    stepn F_96090 D_96090.
    stepret F_96044 D_96044 (0x960fc : word) ltac:(bveq).
    stepn F_960fc D_960fc.
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
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StepTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Hoare OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.WalkTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StreamSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MmapSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibAtomic OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefExitBase.
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
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x96100)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x9b580)))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

#[using="Type"] Lemma w3a : forall regs mem rom (sp code wp1 rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x96100 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  file_clean mem 0xb2d90 wp1 rp1 ->
  file_clean mem 0xb2ca0 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x9b570 : word) mem rom)
                 (mkst regs' (0x95da4 : word) (mem_w3a mem sp code) rom)
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
    stepn F_9b570 D_9b570. rewrite Hsp. sp_renorm.
    stepST F_9b574 D_9b574 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x96100) ltac:(sok_stack SOK).
    stepST F_9b578 D_9b578 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_9b57c D_9b57c.
    stepn F_9b904 D_9b904. sp_renorm.
    stepST F_9b908 D_9b908 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x9b580) ltac:(sok_stack SOK).
    stepST F_9b90c D_9b90c (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_9b910 D_9b910.
    stepn F_9b914 D_9b914.
    stepn F_9b918 D_9b918.
    (* [comment removed for export] *)
    stepn F_9b91c D_9b91c.
    stepn F_a7320 D_a7320.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_a7324 | reflexivity | exact D_a7324 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_a7328 D_a7328 ltac:(cond_compute).
    stepret F_a7518 D_a7518 (0x9b920 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_9b920 D_9b920.
    stepLD8 F_9b924 D_9b924 (Z_to_bv 64 0x9b580).
    stepLD8 F_9b928 D_9b928 code.
    stepn F_9b92c D_9b92c. sp_renorm.
    stepret F_9b930 D_9b930 (0x9b580 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_9b580 D_9b580 (Z_to_bv 64 0).
    stepb_ft F_9b584 D_9b584 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_9b588 D_9b588.
    stepLD8 F_9b58c D_9b58c (Z_to_bv 64 0).
    stepb_tk F_9b590 D_9b590 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_9b5e4 D_9b5e4.
    stepLD8 F_9b5e8 D_9b5e8 (Z_to_bv 64 0xb2d90).
    stepb_ft F_9b5ec D_9b5ec ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_9b5f0 D_9b5f0 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_9b5f4 D_9b5f4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_9b600 D_9b600 wp1.
    stepLD8 F_9b604 D_9b604 wp1.
    stepb_tk F_9b608 D_9b608 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_9b620 D_9b620 rp1.
    stepLD8 F_9b624 D_9b624 rp1.
    stepb_tk F_9b628 D_9b628 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_9b640 D_9b640.
    stepLD8 F_9b644 D_9b644 (Z_to_bv 64 0xb2ca0).
    stepb_ft F_9b648 D_9b648 ltac:(cond_compute).
    stepLD F_9b64c D_9b64c (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_9b650 D_9b650 ltac:(cond_compute).
    stepLD8 F_9b65c D_9b65c wp2.
    stepLD8 F_9b660 D_9b660 wp2.
    stepb_tk F_9b664 D_9b664 ltac:(apply c_eq_refl).
    stepLD8 F_9b67c D_9b67c rp2.
    stepLD8 F_9b680 D_9b680 rp2.
    stepb_tk F_9b684 D_9b684 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_9b704 D_9b704 (Z_to_bv 64 0x96100).
    stepLD8 F_9b708 D_9b708 code.
    stepn F_9b70c D_9b70c. sp_renorm.
    stepret F_9b710 D_9b710 (0x96100 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_96100 D_96100.
    stepn F_96104 D_96104.
    stepn F_95d9c D_95d9c.
    stepn F_95da0 D_95da0.
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
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StepTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Hoare OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.WalkTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StreamSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MmapSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibAtomic OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefExitBase RefExit_run2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section FPW_3. Context {fx : PropExec.FPState}.

Definition stdout_dirty_hdr (mem : word -> option byte) (wb wp : Z) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 (0xb2d90 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn RSEGS mem (Z_to_bv 64 (0xb2d90 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
  /\ rdn RSEGS mem (Z_to_bv 64 (0xb2d90 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
  /\ rdn RSEGS mem (Z_to_bv 64 (0xb2d90 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x9ba34)).

#[using="Type"] Lemma w3b1 : forall regs mem rom (sp code : word) (wb wp : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x96100 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  stdout_dirty_hdr mem wb wp ->
  (0 <= wb < 2^64)%Z -> (0 <= wp < 2^64)%Z -> wb <> wp ->
  exists regs',
    msteps RSEGS (mkst regs (0x9b570 : word) mem rom)
                 (mkst regs' (0x9ba34 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = Z_to_bv 64 0xb2d90
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 1 = Z_to_bv 64 0x9b620
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32)
    /\ getr regs' 8 = Z_to_bv 64 0xb2d90
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof.
  intros regs mem rom sp code wb wp Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr) (F1l & F1wp & F1wb & F1wr) WB WP NE.
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
  unfold mem_w3a. eexists. split.
  - (* [comment removed for export] *)
    stepn F_9b570 D_9b570. rewrite Hsp. sp_renorm.
    stepST F_9b574 D_9b574 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x96100) ltac:(sok_stack SOK).
    stepST F_9b578 D_9b578 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_9b57c D_9b57c.
    stepn F_9b904 D_9b904. sp_renorm.
    stepST F_9b908 D_9b908 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x9b580) ltac:(sok_stack SOK).
    stepST F_9b90c D_9b90c (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_9b910 D_9b910.
    stepn F_9b914 D_9b914.
    stepn F_9b918 D_9b918.
    (* [comment removed for export] *)
    stepn F_9b91c D_9b91c.
    stepn F_a7320 D_a7320.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_a7324 | reflexivity | exact D_a7324 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_a7328 D_a7328 ltac:(cond_compute).
    stepret F_a7518 D_a7518 (0x9b920 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_9b920 D_9b920.
    stepLD8 F_9b924 D_9b924 (Z_to_bv 64 0x9b580).
    stepLD8 F_9b928 D_9b928 code.
    stepn F_9b92c D_9b92c. sp_renorm.
    stepret F_9b930 D_9b930 (0x9b580 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_9b580 D_9b580 (Z_to_bv 64 0).
    stepb_ft F_9b584 D_9b584 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_9b588 D_9b588.
    stepLD8 F_9b58c D_9b58c (Z_to_bv 64 0).
    stepb_tk F_9b590 D_9b590 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_9b5e4 D_9b5e4.
    stepLD8 F_9b5e8 D_9b5e8 (Z_to_bv 64 0xb2d90).
    stepb_ft F_9b5ec D_9b5ec ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_9b5f0 D_9b5f0 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_9b5f4 D_9b5f4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_9b600 D_9b600 (Z_to_bv 64 wp).
    stepLD8 F_9b604 D_9b604 (Z_to_bv 64 wb).
    stepb_ft F_9b608 D_9b608 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepLD8 F_9b60c D_9b60c (Z_to_bv 64 0x9ba34).
    stepn F_9b610 D_9b610.
    stepn F_9b614 D_9b614.
    stepn F_9b618 D_9b618.
    stepjr F_9b61c D_9b61c (Z_to_bv 64 0x9ba34) ltac:(gres; reflexivity). vnorm.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma w3b2 : forall regs mem rom (sp code rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 32) -> getr regs 8 = Z_to_bv 64 0xb2d90 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x96100)) ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 code) ->
  rdn RSEGS mem (Z_to_bv 64 (0xb2d90 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 (0xb2d90 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 0xb2d88) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb2ca0)) ->
  file_clean mem 0xb2ca0 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x9b620 : word) mem rom)
                 (mkst regs' (0x95da4 : word) mem rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr
         (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_9b620 D_9b620 rp1.
    stepLD8 F_9b624 D_9b624 rp1.
    stepb_tk F_9b628 D_9b628 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_9b640 D_9b640.
    stepLD8 F_9b644 D_9b644 (Z_to_bv 64 0xb2ca0).
    stepb_ft F_9b648 D_9b648 ltac:(cond_compute).
    stepLD F_9b64c D_9b64c (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_9b650 D_9b650 ltac:(cond_compute).
    stepLD8 F_9b65c D_9b65c wp2.
    stepLD8 F_9b660 D_9b660 wp2.
    stepb_tk F_9b664 D_9b664 ltac:(apply c_eq_refl).
    stepLD8 F_9b67c D_9b67c rp2.
    stepLD8 F_9b680 D_9b680 rp2.
    stepb_tk F_9b684 D_9b684 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_9b704 D_9b704 (Z_to_bv 64 0x96100).
    stepLD8 F_9b708 D_9b708 code.
    stepn F_9b70c D_9b70c. rewrite Hsp. sp_renorm.
    stepret F_9b710 D_9b710 (0x96100 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_96100 D_96100.
    stepn F_96104 D_96104.
    stepn F_95d9c D_95d9c.
    stepn F_95da0 D_95da0.
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
Import OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.PropExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.CatSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.SeqExec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StepTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Hoare OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.WalkTac OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StoreOk OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.StreamSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.MmapSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibAtomic OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ExitSim OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.ShapeAlg OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Nodes OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.Spec OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.LibWritev OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefStdioDefs RefExit_run1 RefExit_run2 RefExit_run3 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefStdioWrite.RefStdioWrite_run1 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefStdioWrite.RefStdioWrite_run2 OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib.RefStdioWrite.
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
  file_clean mem 0xb2d90 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x96094 : word) mem (seg_rom RSEGS)) model)
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
  eapply rz_exit_at; [exact F_95da4 | exact E_95da4 | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
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
  realizes RSEGS (mkCfg (mkst regs (0x96094 : word) mem (seg_rom RSEGS)) model)
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
  replace (Z_to_bv 64 0x9b620) with (0x9b620 : word) in R3ra by (apply bv_eq; reflexivity).
  unfold W. rewrite <- (app_nil_r pending).
  set (mem3 := mem_w3a (mem_w2 (mem_w1 mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9)) sp code).
  eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) 0xb2d90 wb wp 1
            (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x9b620 : word) pending []);
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
    eapply rz_exit_at; [exact F_95da4 | exact E_95da4 | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
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
  realizes RSEGS (mkCfg (mkst regs (0x96094 : word) mem (seg_rom RSEGS)) model)
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
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x96094) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros. replace (Z_to_bv 64 0x96094) with (0x96094 : word) by (apply bv_eq; reflexivity).
  apply ref_exit; assumption.
Qed.

#[using="Type"] Theorem ref_exit1_clean :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
  exit_common1 regs mem sp tp code tid wp2 rp2 ->
  file_clean mem 0xb2d90 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x96094 : word) mem (seg_rom RSEGS)) model)
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
  eapply rz_exit_at; [exact F_95da4 | exact E_95da4 | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.

#[using="Type"] Theorem ref_exit1_flush :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_common1 regs mem sp tp code tid wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  realizes RSEGS (mkCfg (mkst regs (0x96094 : word) mem (seg_rom RSEGS)) model)
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
  replace (Z_to_bv 64 0x9b620) with (0x9b620 : word) in R3ra by (apply bv_eq; reflexivity).
  unfold W. rewrite <- (app_nil_r pending).
  set (mem3 := mem_w3a (mem_w2 (mem_w1o mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9)) sp code).
  eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) 0xb2d90 wb wp 1
            (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x9b620 : word) pending []);
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
    eapply rz_exit_at; [exact F_95da4 | exact E_95da4 | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.

#[using="Type"] Theorem ref_exit1 : forall regs mem model code pending,
  exit_pre1 regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (0x96094 : word) mem (seg_rom RSEGS)) model)
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
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x96094) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros. replace (Z_to_bv 64 0x96094) with (0x96094 : word) by (apply bv_eq; reflexivity).
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
(* [comment removed for export] *)
