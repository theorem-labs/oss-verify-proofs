(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes Spec LibWritev RefStdioDefs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require RefExitBase Ref_code_1293c_12d58 Ref_code_161c8_17084 Ref_code_12a40_1e480 Ref_code_1dbe0_1e5bc.
From Stdlib Require Zify.
Unset Nia Cache.  (* [comment removed for export] *)

Module RefExit_run1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StepTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.WalkTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibAtomic OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefExitBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ref_code_1293c_12d58 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ref_code_161c8_17084 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ref_code_1dbe0_1e5bc OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ref_code_12a40_1e480 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefStdioDefs.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
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
Lemma rdn_hit4 : forall segs m (a v : word),
  (bv_unsigned a + 4 <= 2^64)%Z ->
  rdn segs (wbytes m a (word_to_le_bytes 4 v)) a 4%nat = Some (word_to_le_bytes 4 v).
Proof.
  intros segs m a v Hnw.
  pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 v) m a) as H.
  rewrite length_N_to_le_bytes in H. apply H. exact Hnw.
Qed.


Definition mem_w1e (mem : word -> option byte) (sp ra s0 code s1 s2 s3 : word) (tid : Z) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 0x50c50) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x16ac4)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3))
    (Z_to_bv 64 0x50a30) [Z_to_bv 8 1].

Lemma w1e : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0x50c50) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x50c7b) 1%nat = Some [Z_to_bv 8 0] ->                              
  rdn RSEGS mem (Z_to_bv 64 0x50a34) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->        
  ax_empty mem ->
  exists regs',
    msteps RSEGS (mkst regs (0x16a60 : word) mem rom)
                 (mkst regs' (0x16a14 : word) (mem_w1e mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x16ac8
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Mlk
    Mhd.
  unfold ax_empty in Mhd.
  unfold mem_w1e. eexists. split.
  - 
    stepn F_16a60 D_16a60. rewrite Hsp. sp_renorm.
    stepST F_16a64 D_16a64 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_16a68 D_16a68 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    stepn F_16a6c D_16a6c.
    stepn F_16a70 D_16a70. rewrite Htp.
    stepLD F_16a74 D_16a74 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    stepn F_16a78 D_16a78.
    stepn F_16a7c D_16a7c.
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_16a80 | reflexivity | exact D_16a80
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_16a84 | reflexivity | exact D_16a84 | gres; cond_compute ] | ].
    norm_pc_r.
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_16a88 | reflexivity | exact D_16a88
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    stepb_ft F_16a8c D_16a8c ltac:(cond_compute).
    stepn F_16a90 D_16a90.
    stepb_ft F_16a94 D_16a94 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    stepb_tk F_16a98 D_16a98 ltac:(cond_compute).
    stepn F_16abc D_16abc. rewrite Ha0.
    stepn F_16ac0 D_16ac0.
    stepn F_1687c D_1687c. sp_renorm.
    stepST F_16880 D_16880 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x16ac4) ltac:(sok_stack SOK).
    stepST F_16884 D_16884 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_16888 D_16888 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_1688c D_1688c (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_16890 D_16890 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    stepn F_16894 D_16894.
    stepn F_16898 D_16898.
    stepn F_1689c D_1689c.
    stepn F_168a0 D_168a0.
    stepn F_168a4 D_168a4.
    stepn F_1e1ec D_1e1ec.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_1e1f0 | reflexivity | exact D_1e1f0 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_1e1f4 D_1e1f4 ltac:(cond_compute).
    stepret F_1e3e4 D_1e3e4 (0x168a8 : word) ltac:(bveq).
    stepLD8 F_168a8 D_168a8 (Z_to_bv 64 0).
    stepb_tk F_168ac D_168ac ltac:(cond_compute).
    stepn F_1691c D_1691c.
    stepST F_16920 D_16920 (Z_to_bv 64 0x50a30) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_16924 D_16924.
    stepLD8 F_16928 D_16928 (Z_to_bv 64 0x16ac4).
    stepLD8 F_1692c D_1692c code.
    stepLD8 F_16930 D_16930 (getr regs 9).
    stepLD8 F_16934 D_16934 (getr regs 18).
    stepLD8 F_16938 D_16938 (getr regs 19).
    stepn F_1693c D_1693c. sp_renorm.
    stepn F_16940 D_16940.
    stepLD F_1e474 D_1e474 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_1e478 D_1e478 ltac:(cond_compute).
    stepret F_1e47c D_1e47c (0x16ac4 : word) ltac:(bveq).
    stepn F_16ac4 D_16ac4.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.


Definition mem_w1x (mem : word -> option byte) (sp ra s0 code s1 s2 s3 : word) (tid : Z) :=
  wbytes (wbytes (wbytes (wbytes (wbytes
  (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 0x50c50) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x16ac4)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3))
    (Z_to_bv 64 0x50a38) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x50a38) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x50a38) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x50a40) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x50a30) [Z_to_bv 8 1].

Lemma w1x : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0x50c50) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x50c7b) 1%nat = Some [Z_to_bv 8 0] ->                              
  rdn RSEGS mem (Z_to_bv 64 0x50a34) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->        
  ax_one mem ->
  exists regs',
    msteps RSEGS (mkst regs (0x16a60 : word) mem rom)
                 (mkst regs' (0x16a14 : word) (mem_w1x mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x16ac8
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Mlk
    (Mhd & Msl & Mnx & Mf0 & Ma0 & Mcb).
  unfold mem_w1x. eexists. split.
  - 
    stepn F_16a60 D_16a60. rewrite Hsp. sp_renorm.
    stepST F_16a64 D_16a64 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_16a68 D_16a68 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    stepn F_16a6c D_16a6c.
    stepn F_16a70 D_16a70. rewrite Htp.
    stepLD F_16a74 D_16a74 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    stepn F_16a78 D_16a78.
    stepn F_16a7c D_16a7c.
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_16a80 | reflexivity | exact D_16a80
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_16a84 | reflexivity | exact D_16a84 | gres; cond_compute ] | ].
    norm_pc_r.
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_16a88 | reflexivity | exact D_16a88
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    stepb_ft F_16a8c D_16a8c ltac:(cond_compute).
    stepn F_16a90 D_16a90.
    stepb_ft F_16a94 D_16a94 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    stepb_tk F_16a98 D_16a98 ltac:(cond_compute).
    stepn F_16abc D_16abc. rewrite Ha0.
    stepn F_16ac0 D_16ac0.
    stepn F_1687c D_1687c. sp_renorm.
    stepST F_16880 D_16880 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x16ac4) ltac:(sok_stack SOK).
    stepST F_16884 D_16884 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_16888 D_16888 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_1688c D_1688c (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_16890 D_16890 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    stepn F_16894 D_16894.
    stepn F_16898 D_16898.
    stepn F_1689c D_1689c.
    stepn F_168a0 D_168a0.
    stepn F_168a4 D_168a4.
    stepn F_1e1ec D_1e1ec.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_1e1f0 | reflexivity | exact D_1e1f0 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_1e1f4 D_1e1f4 ltac:(cond_compute).
    stepret F_1e3e4 D_1e3e4 (0x168a8 : word) ltac:(bveq).
    stepLD8 F_168a8 D_168a8 (Z_to_bv 64 0x50a48).
    stepb_ft F_168ac D_168ac ltac:(cond_compute).
    stepLD F_168b0 D_168b0 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepn F_168b4 D_168b4.
    stepn F_168cc D_168cc.
    stepST F_168d0 D_168d0 (Z_to_bv 64 0x50a38) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_168d4 D_168d4 ltac:(cond_compute).
    stepLD8 F_168d8 D_168d8 (Z_to_bv 64 0x50a48).
    stepn F_168dc D_168dc.
    stepn F_168e0 D_168e0.
    stepLD8 F_168e4 D_168e4 (Z_to_bv 64 0x16a0c).
    stepLD8 F_168e8 D_168e8 (Z_to_bv 64 0x12eb0).
    stepn F_168ec D_168ec.
    stepn F_168f0 D_168f0.
    stepLD F_1e474 D_1e474 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_1e478 D_1e478 ltac:(cond_compute).
    stepret F_1e47c D_1e47c (0x168f4 : word) ltac:(bveq).
    stepn F_168f4 D_168f4.
    stepjr F_168f8 D_168f8 (Z_to_bv 64 0x16a0c) ltac:(gres; reflexivity). vnorm.
    stepjr F_16a0c D_16a0c (Z_to_bv 64 0x12eb0) ltac:(gres; reflexivity). vnorm.
    stepn F_12eb0 D_12eb0.
    stepLBU F_12eb4 D_12eb4 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_12eb8 D_12eb8 ltac:(cond_compute).
    stepret F_12ebc D_12ebc (0x168fc : word) ltac:(bveq).
    stepn F_168fc D_168fc.
    stepn F_16900 D_16900.
    stepn F_1e1ec D_1e1ec.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_1e1f0 | reflexivity | exact D_1e1f0 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_1e1f4 D_1e1f4 ltac:(cond_compute).
    stepret F_1e3e4 D_1e3e4 (0x16904 : word) ltac:(bveq).
    stepLD F_16904 D_16904 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; apply rdn_hit4; zsimp; lia) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepn F_16908 D_16908.
    stepST F_1690c D_1690c (Z_to_bv 64 0x50a38) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_16910 D_16910 ltac:(cond_compute).
    stepLD8 F_16914 D_16914 (Z_to_bv 64 0x50a48).
    stepn F_16918 D_16918.
    stepLD8 F_168b8 D_168b8 (Z_to_bv 64 0).
    stepn F_168bc D_168bc.
    stepST F_168c0 D_168c0 (Z_to_bv 64 0x50a38) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_168c4 D_168c4 (Z_to_bv 64 0x50a40) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_168c8 D_168c8 ltac:(cond_compute).
    stepn F_1691c D_1691c.
    stepST F_16920 D_16920 (Z_to_bv 64 0x50a30) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_16924 D_16924.
    stepLD8 F_16928 D_16928 (Z_to_bv 64 0x16ac4).
    stepLD8 F_1692c D_1692c code.
    stepLD8 F_16930 D_16930 (getr regs 9).
    stepLD8 F_16934 D_16934 (getr regs 18).
    stepLD8 F_16938 D_16938 (getr regs 19).
    stepn F_1693c D_1693c. sp_renorm.
    stepn F_16940 D_16940.
    stepLD F_1e474 D_1e474 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_1e478 D_1e478 ltac:(cond_compute).
    stepret F_1e47c D_1e47c (0x16ac4 : word) ltac:(bveq).
    stepn F_16ac4 D_16ac4.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.


(* [comment removed for export] *)
Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x16ac8)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x16a44)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x1f5c8)))
    (Z_to_bv 64 0x208d8) [Z_to_bv 8 1].

Lemma w2 : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x16ac8 -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x1f668) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1f5d0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1f670) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1f5c8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1f5c8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x129f8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x208d8) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x1f610) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x16944)) ->
  rdn RSEGS mem (Z_to_bv 64 0x1f618) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x20678) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x20678)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x16a14 : word) mem rom)
                 (mkst regs' (0x18dd8 : word) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x16acc
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2. eexists. split.
  - (* [comment removed for export] *)
    stepn F_16a14 D_16a14. rewrite Hsp. sp_renorm.
    stepST F_16a18 D_16a18 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x16ac8) ltac:(sok_stack SOK).
    stepST F_16a1c D_16a1c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_16a20 D_16a20 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_16a24 D_16a24.
    stepn F_16a28 D_16a28.
    stepLD8 F_16a2c D_16a2c (Z_to_bv 64 0x1f5d0).
    stepLD8 F_16a30 D_16a30 (Z_to_bv 64 0x1f5c8).
    (* [comment removed for export] *)
    stepb_ft F_16a34 D_16a34 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_16a38 D_16a38 (Z_to_bv 64 0x129f8).
    stepn F_16a3c D_16a3c.
    stepjr F_16a40 D_16a40 (Z_to_bv 64 0x129f8) ltac:(gres; reflexivity). vnorm.
    (* [comment removed for export] *)
    stepn F_129f8 D_129f8. sp_renorm.
    stepST F_129fc D_129fc (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x16a44) ltac:(sok_stack SOK).
    stepST F_12a00 D_12a00 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x1f5c8) ltac:(sok_stack SOK).
    stepn F_12a04 D_12a04.
    stepn F_12a08 D_12a08.
    stepn F_12a0c D_12a0c.
    (* [comment removed for export] *)
    stepLBU F_12a10 D_12a10 (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
    stepn F_12a14 D_12a14.
    stepb_tk F_12a18 D_12a18 ltac:(cond_compute).
    stepn F_12a24 D_12a24.
    stepn F_12a28 D_12a28.
    stepn F_12a2c D_12a2c.
    (* [comment removed for export] *)
    stepST F_12a30 D_12a30 (Z_to_bv 64 0x208d8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_12a34 D_12a34.
    stepLD8 F_12a38 D_12a38 (Z_to_bv 64 0x16944).
    stepb_ft F_12a3c D_12a3c ltac:(cond_compute).
    stepn F_12a40 D_12a40.
    stepn F_12a44 D_12a44.
    stepn F_12a48 D_12a48.
    stepLD8 F_12a4c D_12a4c (Z_to_bv 64 0x20678).
    stepn F_12a50 D_12a50.
    stepret F_16944 D_16944 (0x12a54 : word) ltac:(bveq).
    stepn F_12a54 D_12a54.
    (* [comment removed for export] *)
    stepn F_12a58 D_12a58.
    stepLD8 F_12a5c D_12a5c (Z_to_bv 64 0).
    stepb_tk F_12a60 D_12a60 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_12a78 D_12a78 (Z_to_bv 64 0x16a44).
    stepLD8 F_12a7c D_12a7c (Z_to_bv 64 0x1f5c8).
    stepn F_12a80 D_12a80. sp_renorm.
    stepret F_12a84 D_12a84 (0x16a44 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_16a44 D_16a44.
    stepb_ft F_16a48 D_16a48 ltac:(cond_compute).
    stepLD8 F_16a4c D_16a4c (Z_to_bv 64 0x16ac8).
    stepLD8 F_16a50 D_16a50 code.
    stepLD8 F_16a54 D_16a54 s1v.
    stepn F_16a58 D_16a58. sp_renorm.
    (* [comment removed for export] *)
    stepn F_16a5c D_16a5c.
    stepret F_16a10 D_16a10 (0x16ac8 : word) ltac:(bveq).
    stepn F_16ac8 D_16ac8.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End WithFP1.


(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End RefExit_run1.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Ref_code_183b0_19140 Ref_code_1dbe0_1e5bc.

Module RefExit_run2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StepTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.WalkTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibAtomic OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefExitBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ref_code_161c8_17084 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ref_code_183b0_19140 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ref_code_1dbe0_1e5bc.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithFP1. Context {FP : PropExec.FPState}.
Definition mem_w3a (mem : word -> option byte) (sp code : word) :=
  wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x16acc)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x18de8)))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

Lemma w3a : forall regs mem rom (sp code wp1 rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x16acc ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  file_clean mem 0x20790 wp1 rp1 ->
  file_clean mem 0x206a0 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x18dd8 : word) mem rom)
                 (mkst regs' (0x16868 : word) (mem_w3a mem sp code) rom)
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
    stepn F_18dd8 D_18dd8. rewrite Hsp. sp_renorm.
    stepST F_18ddc D_18ddc (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x16acc) ltac:(sok_stack SOK).
    stepST F_18de0 D_18de0 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_18de4 D_18de4.
    stepn F_18f7c D_18f7c. sp_renorm.
    stepST F_18f80 D_18f80 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x18de8) ltac:(sok_stack SOK).
    stepST F_18f84 D_18f84 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_18f88 D_18f88.
    stepn F_18f8c D_18f8c.
    stepn F_18f90 D_18f90.
    (* [comment removed for export] *)
    stepn F_18f94 D_18f94.
    stepn F_1e1ec D_1e1ec.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_1e1f0 | reflexivity | exact D_1e1f0 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_1e1f4 D_1e1f4 ltac:(cond_compute).
    stepret F_1e3e4 D_1e3e4 (0x18f98 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_18f98 D_18f98.
    stepLD8 F_18f9c D_18f9c (Z_to_bv 64 0x18de8).
    stepLD8 F_18fa0 D_18fa0 code.
    stepn F_18fa4 D_18fa4. sp_renorm.
    stepret F_18fa8 D_18fa8 (0x18de8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_18de8 D_18de8 (Z_to_bv 64 0).
    stepb_ft F_18dec D_18dec ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_18df0 D_18df0.
    stepLD8 F_18df4 D_18df4 (Z_to_bv 64 0).
    stepb_tk F_18df8 D_18df8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_18e4c D_18e4c.
    stepLD8 F_18e50 D_18e50 (Z_to_bv 64 0x20790).
    stepb_ft F_18e54 D_18e54 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_18e58 D_18e58 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_18e5c D_18e5c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_18e68 D_18e68 wp1.
    stepLD8 F_18e6c D_18e6c wp1.
    stepb_tk F_18e70 D_18e70 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_18e88 D_18e88 rp1.
    stepLD8 F_18e8c D_18e8c rp1.
    stepb_tk F_18e90 D_18e90 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_18ea8 D_18ea8.
    stepLD8 F_18eac D_18eac (Z_to_bv 64 0x206a0).
    stepb_ft F_18eb0 D_18eb0 ltac:(cond_compute).
    stepLD F_18eb4 D_18eb4 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_18eb8 D_18eb8 ltac:(cond_compute).
    stepLD8 F_18ec4 D_18ec4 wp2.
    stepLD8 F_18ec8 D_18ec8 wp2.
    stepb_tk F_18ecc D_18ecc ltac:(apply c_eq_refl).
    stepLD8 F_18ee4 D_18ee4 rp2.
    stepLD8 F_18ee8 D_18ee8 rp2.
    stepb_tk F_18eec D_18eec ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_18f6c D_18f6c (Z_to_bv 64 0x16acc).
    stepLD8 F_18f70 D_18f70 code.
    stepn F_18f74 D_18f74. sp_renorm.
    stepret F_18f78 D_18f78 (0x16acc : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_16acc D_16acc.
    stepn F_16ad0 D_16ad0.
    stepn F_16860 D_16860.
    stepn F_16864 D_16864.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End WithFP1.


(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End RefExit_run2.

Module RefExit_run3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StepTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.WalkTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibAtomic OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefExitBase RefExit_run2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ref_code_161c8_17084 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ref_code_183b0_19140 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ref_code_1dbe0_1e5bc.
Import Stdlib.micromega.Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section WithFP1. Context {FP : PropExec.FPState}.
Definition stdout_dirty_hdr (mem : word -> option byte) (wb wp : Z) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 (0x20790 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x20790 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x20790 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x20790 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x18fe8)).

Lemma w3b1 : forall regs mem rom (sp code : word) (wb wp : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x16acc ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  stdout_dirty_hdr mem wb wp ->
  (0 <= wb < 2^64)%Z -> (0 <= wp < 2^64)%Z -> wb <> wp ->
  exists regs',
    msteps RSEGS (mkst regs (0x18dd8 : word) mem rom)
                 (mkst regs' (0x18fe8 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = Z_to_bv 64 0x20790
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 1 = Z_to_bv 64 0x18e88
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32)
    /\ getr regs' 8 = Z_to_bv 64 0x20790
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof.
  intros regs mem rom sp code wb wp Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr) (F1l & F1wp & F1wb & F1wr) WB WP NE.
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
  unfold mem_w3a. eexists. split.
  - (* [comment removed for export] *)
    stepn F_18dd8 D_18dd8. rewrite Hsp. sp_renorm.
    stepST F_18ddc D_18ddc (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x16acc) ltac:(sok_stack SOK).
    stepST F_18de0 D_18de0 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_18de4 D_18de4.
    stepn F_18f7c D_18f7c. sp_renorm.
    stepST F_18f80 D_18f80 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x18de8) ltac:(sok_stack SOK).
    stepST F_18f84 D_18f84 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_18f88 D_18f88.
    stepn F_18f8c D_18f8c.
    stepn F_18f90 D_18f90.
    (* [comment removed for export] *)
    stepn F_18f94 D_18f94.
    stepn F_1e1ec D_1e1ec.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_1e1f0 | reflexivity | exact D_1e1f0 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_1e1f4 D_1e1f4 ltac:(cond_compute).
    stepret F_1e3e4 D_1e3e4 (0x18f98 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_18f98 D_18f98.
    stepLD8 F_18f9c D_18f9c (Z_to_bv 64 0x18de8).
    stepLD8 F_18fa0 D_18fa0 code.
    stepn F_18fa4 D_18fa4. sp_renorm.
    stepret F_18fa8 D_18fa8 (0x18de8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_18de8 D_18de8 (Z_to_bv 64 0).
    stepb_ft F_18dec D_18dec ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_18df0 D_18df0.
    stepLD8 F_18df4 D_18df4 (Z_to_bv 64 0).
    stepb_tk F_18df8 D_18df8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_18e4c D_18e4c.
    stepLD8 F_18e50 D_18e50 (Z_to_bv 64 0x20790).
    stepb_ft F_18e54 D_18e54 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_18e58 D_18e58 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_18e5c D_18e5c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_18e68 D_18e68 (Z_to_bv 64 wp).
    stepLD8 F_18e6c D_18e6c (Z_to_bv 64 wb).
    stepb_ft F_18e70 D_18e70 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepLD8 F_18e74 D_18e74 (Z_to_bv 64 0x18fe8).
    stepn F_18e78 D_18e78.
    stepn F_18e7c D_18e7c.
    stepn F_18e80 D_18e80.
    stepjr F_18e84 D_18e84 (Z_to_bv 64 0x18fe8) ltac:(gres; reflexivity). vnorm.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma w3b2 : forall regs mem rom (sp code rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 32) -> getr regs 8 = Z_to_bv 64 0x20790 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x16acc)) ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 code) ->
  rdn RSEGS mem (Z_to_bv 64 (0x20790 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 (0x20790 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 0x20788) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x206a0)) ->
  file_clean mem 0x206a0 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x18e88 : word) mem rom)
                 (mkst regs' (0x16868 : word) mem rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr
         (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_18e88 D_18e88 rp1.
    stepLD8 F_18e8c D_18e8c rp1.
    stepb_tk F_18e90 D_18e90 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_18ea8 D_18ea8.
    stepLD8 F_18eac D_18eac (Z_to_bv 64 0x206a0).
    stepb_ft F_18eb0 D_18eb0 ltac:(cond_compute).
    stepLD F_18eb4 D_18eb4 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_18eb8 D_18eb8 ltac:(cond_compute).
    stepLD8 F_18ec4 D_18ec4 wp2.
    stepLD8 F_18ec8 D_18ec8 wp2.
    stepb_tk F_18ecc D_18ecc ltac:(apply c_eq_refl).
    stepLD8 F_18ee4 D_18ee4 rp2.
    stepLD8 F_18ee8 D_18ee8 rp2.
    stepb_tk F_18eec D_18eec ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_18f6c D_18f6c (Z_to_bv 64 0x16acc).
    stepLD8 F_18f70 D_18f70 code.
    stepn F_18f74 D_18f74. rewrite Hsp. sp_renorm.
    stepret F_18f78 D_18f78 (0x16acc : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_16acc D_16acc.
    stepn F_16ad0 D_16ad0.
    stepn F_16860 D_16860.
    stepn F_16864 D_16864.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End WithFP1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End RefExit_run3.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require RefStdioWrite.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes Spec LibWritev RefStdioDefs. Import RefExit_run1. Import RefExit_run2. Import RefExit_run3. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require RefStdioWrite. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefStdioWrite.RefStdioWrite_run1. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require RefStdioWrite. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.RefStdioWrite.RefStdioWrite_run2. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import RefStdioWrite Ref_code_161c8_17084.
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac zaddr_rec H := zaddr H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithFP1. Context {FP : PropExec.FPState}.
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
Record exit_mid (regs1 : bvmap 5 word) (mem1 : word -> option byte) (sp code : word) (wp2 rp2 : word) : Prop := {
  em_sp   : getr regs1 2 = Z_to_bv 64 (bv_unsigned sp - 16);
  em_s0   : getr regs1 8 = code;
  em_ra   : getr regs1 1 = Z_to_bv 64 0x16ac8;
  em_splo : (4294967296 <= bv_unsigned sp - 144)%Z;
  em_sphi : (bv_unsigned sp <= 0x800000000000)%Z;
  em_sok  : store_ok RSEGS mem1 (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true;
  em_fe   : rdn RSEGS mem1 (Z_to_bv 64 0x1f668) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1f5d0));
  em_fs   : rdn RSEGS mem1 (Z_to_bv 64 0x1f670) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1f5c8));
  em_fa   : rdn RSEGS mem1 (Z_to_bv 64 0x1f5c8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x129f8));
  em_comp : rdn RSEGS mem1 (Z_to_bv 64 0x208d8) 1%nat = Some [Z_to_bv 8 0];
  em_g1   : rdn RSEGS mem1 (Z_to_bv 64 0x1f610) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x16944));
  em_g2   : rdn RSEGS mem1 (Z_to_bv 64 0x1f618) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  em_dso  : rdn RSEGS mem1 (Z_to_bv 64 0x20678) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x20678));
  em_glob : stdio_globals mem1;
  em_err  : file_clean mem1 0x206a0 wp2 rp2
}.

Lemma ref_exit_mid_clean :
  forall regs1 mem1 model (sp code : word) (wp2 rp2 wp1 rp1 : word),
  exit_mid regs1 mem1 sp code wp2 rp2 ->
  file_clean mem1 0x20790 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs1 (0x16a14 : word) mem1 (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs1 mem1 model sp code wp2 rp2 wp1 rp1 EM F1 Hh Hlazy.
  destruct EM as [Esp Es0 Era Esplo Esphi Esok Efe Efs Efa Ecomp Eg1 Eg2 Edso Eglob Eerr].
  destruct (w2 regs1 mem1 (seg_rom RSEGS) sp code (getr regs1 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  destruct Eglob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct Eerr as (F2l & F2wp & F2wb & F2rp & F2re).
  destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  destruct (w3a regs2 (mem_w2 mem1 sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wp1 rp1 wp2 rp2)
    as (regs3 & RUN3 & R3a0 & R3a7 & R3sp); try assumption.
  1:{ unfold mem_w2; store_ok_peel; exact Esok. }
  1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2; rdn_solve. }
  1:{ repeat split; unfold mem_w2; zaddr_goal; rdn_solve. }
  1:{ repeat split; unfold mem_w2; zaddr_goal; rdn_solve. }
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  eapply rz_exit_at; [exact F_16868 | exact E_16868 | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.

Lemma ref_exit_mid_flush :
  forall regs1 mem1 model (sp code : word) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_mid regs1 mem1 sp code wp2 rp2 ->
  stdout_pending mem1 wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  realizes RSEGS (mkCfg (mkst regs1 (0x16a14 : word) mem1 (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs1 mem1 model sp code wp2 rp2 wb wp bufp bufsz rp1 can pending EM SP Hh Hlazy Hfd.
  destruct EM as [Esp Es0 Era Esplo Esphi Esok Efe Efs Efa Ecomp Eg1 Eg2 Edso Eglob Eerr]. destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
  zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
  destruct (w2 regs1 mem1 (seg_rom RSEGS) sp code (getr regs1 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  destruct Eglob as (Gnl & Gofl & Gin & Gout & Gerr).
  destruct (w3b1 regs2 (mem_w2 mem1 sp code (getr regs1 9))
              (seg_rom RSEGS) sp code wb wp)
    as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
  1:{ unfold mem_w2; store_ok_peel; exact Esok. }
  1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2; rdn_solve. }
  1:{ repeat split; unfold mem_w2; zaddr_goal; rdn_solve. }
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  replace (Z_to_bv 64 0x18e88) with (0x18e88 : word) in R3ra by (apply bv_eq; reflexivity).
  unfold W. rewrite <- (app_nil_r pending).
  set (mem3 := mem_w3a (mem_w2 mem1 sp code (getr regs1 9)) sp code).
  eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) 0x20790 wb wp 1
            (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x18e88 : word) pending []);
    [ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
    | lia | lia
    | subst mem3; unfold mem_w3a, mem_w2; sok_stack Esok
    | lia | lia
    | split; subst mem3; unfold mem_w3a, mem_w2; zaddr_goal; rdn_solve
    | split; subst mem3; unfold mem_w3a, mem_w2; rdn_solve
    | lia | exact Hfd | exact Hh | exact Hlazy
    | lia | lia | exact LEN
    | cbn [length]; u_norm; reflexivity
    | cbn [length]; lia
    | cbn [length]; lia
    | lia | u_norm; lia | u_norm; lia
    | subst mem3; unfold mem_w3a, mem_w2; repeat rdn_peel1; exact BYTES
    | reflexivity
    | apply ret_ok_even; reflexivity
    | apply t_emit_has_nil
    | ].
  intros regs4 mem4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
    rewrite R3s0 in Q8.
    destruct Eerr as (F2l & F2wp & F2wb & F2rp & F2re).
    zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
    destruct (w3b2 regs4 mem4 (seg_rom RSEGS) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
    all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
    1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
    eapply rz_exit_at; [exact F_16868 | exact E_16868 | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.


Lemma ref_exit_w1 :
  forall regs mem rom (sp tp code : word) (tid : Z) (wp2 rp2 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  exists regs1 mem1,
    msteps RSEGS (mkst regs (0x16a60 : word) mem rom) (mkst regs1 (0x16a14 : word) mem1 rom)
    /\ exit_mid regs1 mem1 sp code wp2 rp2
    /\ (forall (a : word) n bs, rdn RSEGS mem a n = Some bs ->
          (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
          (bv_unsigned a + Z.of_nat n <= bv_unsigned sp - 56 \/ bv_unsigned sp <= bv_unsigned a)%Z ->
          (bv_unsigned a + Z.of_nat n <= 0x50a30 \/ 0x50a48 <= bv_unsigned a)%Z ->
          (bv_unsigned a + Z.of_nat n <= 0x50c50 \/ 0x50c54 <= bv_unsigned a)%Z ->
          rdn RSEGS mem1 a n = Some bs).
Proof.
  intros regs mem rom sp tp code tid wp2 rp2 EC.
  pose proof EC as EC0. destruct EC0.
  destruct ec_ax as [AXE | AXO].
  - destruct (w1e regs mem rom sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
      try assumption; try (destruct ec_glob as (Gnl & _); exact Gnl).
    exists regs1, (mem_w1e mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid).
    split; [exact RUN1|]. split.
    + destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr). destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
      zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
      constructor; try assumption; unfold mem_w1e;
        first [ store_ok_peel; exact ec_sok
              | rdn_solve
              | repeat split; zaddr_goal; rdn_solve ].
    + intros a n bs H Hnw D1 D2 D3. unfold mem_w1e. repeat rdn_peel1; first [exact H | zsimp; lia].
  - destruct (w1x regs mem rom sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
      try assumption; try (destruct ec_glob as (Gnl & _); exact Gnl).
    exists regs1, (mem_w1x mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid).
    split; [exact RUN1|]. split.
    + destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr). destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
      zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
      constructor; try assumption; unfold mem_w1x;
        first [ store_ok_peel; exact ec_sok
              | rdn_solve
              | repeat split; zaddr_goal; rdn_solve ].
    + intros a n bs H Hnw D1 D2 D3. unfold mem_w1x. repeat rdn_peel1; first [exact H | zsimp; lia].
Qed.

Theorem ref_exit_clean :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  file_clean mem 0x20790 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x16a60 : word) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wp1 rp1 EC F1 Hh Hlazy.
  destruct (ref_exit_w1 regs mem (seg_rom RSEGS) sp tp code tid wp2 rp2 EC) as (regs1 & mem1 & RUN1 & EM & FR).
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
  pose proof (ec_splo _ _ _ _ _ _ _ _ EC) as SPlo. pose proof (ec_sphi _ _ _ _ _ _ _ _ EC) as SPhi.
  eapply (ref_exit_mid_clean regs1 mem1 model sp code wp2 rp2 wp1 rp1 EM); [|exact Hh | exact Hlazy].
  destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  repeat split; (apply FR; [assumption | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
Qed.

Theorem ref_exit_flush :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  realizes RSEGS (mkCfg (mkst regs (0x16a60 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd.
  destruct (ref_exit_w1 regs mem (seg_rom RSEGS) sp tp code tid wp2 rp2 EC) as (regs1 & mem1 & RUN1 & EM & FR).
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
  pose proof (ec_splo _ _ _ _ _ _ _ _ EC) as SPlo. pose proof (ec_sphi _ _ _ _ _ _ _ _ EC) as SPhi.
  eapply (ref_exit_mid_flush regs1 mem1 model sp code wp2 rp2 wb wp bufp bufsz rp1 can pending EM);
    [|exact Hh | exact Hlazy | exact Hfd].
  destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
  zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
  constructor; try assumption;
    try (apply FR; [assumption | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]);
    try (split; (apply FR; [assumption | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia])).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
  intros code fs. apply t_eq_sym. apply t_emit_nil_eq.
  unfold t_exit, t_emit. left. apply is_prefix_nil.
Qed.

Theorem ref_exit : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (0x16a60 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES).
  destruct CASES as [(-> & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd)].
  - eapply rz_conseq; [ | apply t_emit_nil_exit ].
    eapply ref_exit_clean; eassumption.
  - eapply ref_exit_flush; eassumption.
Qed.

(* [comment removed for export] *)
Corollary ref_exit_Z : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x16a60) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros. replace (Z_to_bv 64 0x16a60) with (0x16a60 : word) by (apply bv_eq; reflexivity).
  apply ref_exit; assumption.
Qed.
End WithFP1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
