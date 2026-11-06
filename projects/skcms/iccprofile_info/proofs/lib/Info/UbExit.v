(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes Spec LibWritev UbStdioDefs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require UbExitBase Ub_code_1299c_12db8 Ub_code_1735c_17f20 Ub_code_12aa0_1ef7c Ub_code_1e6dc_1f0b8.
From Stdlib Require Zify.
Unset Nia Cache.  (* [comment removed for export] *)

Module UbExit_run1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StepTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.WalkTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibAtomic OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbExitBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_1299c_12db8 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_1735c_17f20 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_1e6dc_1f0b8 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_12aa0_1ef7c OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbStdioDefs.
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
    (Z_to_bv 64 0x51740) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x175c0)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3))
    (Z_to_bv 64 0x51520) [Z_to_bv 8 1].

Lemma w1e : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0x51740) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5176b) 1%nat = Some [Z_to_bv 8 0] ->                              
  rdn RSEGS mem (Z_to_bv 64 0x51524) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->        
  ax_empty mem ->
  exists regs',
    msteps RSEGS (mkst regs (0x1755c : word) mem rom)
                 (mkst regs' (0x17510 : word) (mem_w1e mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x175c4
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Mlk
    Mhd.
  unfold ax_empty in Mhd.
  unfold mem_w1e. eexists. split.
  - 
    stepn F_1755c D_1755c. rewrite Hsp. sp_renorm.
    stepST F_17560 D_17560 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_17564 D_17564 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    stepn F_17568 D_17568.
    stepn F_1756c D_1756c. rewrite Htp.
    stepLD F_17570 D_17570 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    stepn F_17574 D_17574.
    stepn F_17578 D_17578.
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_1757c | reflexivity | exact D_1757c
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_17580 | reflexivity | exact D_17580 | gres; cond_compute ] | ].
    norm_pc_r.
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_17584 | reflexivity | exact D_17584
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    stepb_ft F_17588 D_17588 ltac:(cond_compute).
    stepn F_1758c D_1758c.
    stepb_ft F_17590 D_17590 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    stepb_tk F_17594 D_17594 ltac:(cond_compute).
    stepn F_175b8 D_175b8. rewrite Ha0.
    stepn F_175bc D_175bc.
    stepn F_17378 D_17378. sp_renorm.
    stepST F_1737c D_1737c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x175c0) ltac:(sok_stack SOK).
    stepST F_17380 D_17380 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_17384 D_17384 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_17388 D_17388 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_1738c D_1738c (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    stepn F_17390 D_17390.
    stepn F_17394 D_17394.
    stepn F_17398 D_17398.
    stepn F_1739c D_1739c.
    stepn F_173a0 D_173a0.
    stepn F_1ece8 D_1ece8.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_1ecec | reflexivity | exact D_1ecec | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_1ecf0 D_1ecf0 ltac:(cond_compute).
    stepret F_1eee0 D_1eee0 (0x173a4 : word) ltac:(bveq).
    stepLD8 F_173a4 D_173a4 (Z_to_bv 64 0).
    stepb_tk F_173a8 D_173a8 ltac:(cond_compute).
    stepn F_17418 D_17418.
    stepST F_1741c D_1741c (Z_to_bv 64 0x51520) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_17420 D_17420.
    stepLD8 F_17424 D_17424 (Z_to_bv 64 0x175c0).
    stepLD8 F_17428 D_17428 code.
    stepLD8 F_1742c D_1742c (getr regs 9).
    stepLD8 F_17430 D_17430 (getr regs 18).
    stepLD8 F_17434 D_17434 (getr regs 19).
    stepn F_17438 D_17438. sp_renorm.
    stepn F_1743c D_1743c.
    stepLD F_1ef70 D_1ef70 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_1ef74 D_1ef74 ltac:(cond_compute).
    stepret F_1ef78 D_1ef78 (0x175c0 : word) ltac:(bveq).
    stepn F_175c0 D_175c0.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.


Definition mem_w1x (mem : word -> option byte) (sp ra s0 code s1 s2 s3 : word) (tid : Z) :=
  wbytes (wbytes (wbytes (wbytes (wbytes
  (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 0x51740) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x175c0)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3))
    (Z_to_bv 64 0x51528) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x51528) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x51528) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x51530) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x51520) [Z_to_bv 8 1].

Lemma w1x : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0x51740) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x5176b) 1%nat = Some [Z_to_bv 8 0] ->                              
  rdn RSEGS mem (Z_to_bv 64 0x51524) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->        
  ax_one mem ->
  exists regs',
    msteps RSEGS (mkst regs (0x1755c : word) mem rom)
                 (mkst regs' (0x17510 : word) (mem_w1x mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x175c4
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Mlk
    (Mhd & Msl & Mnx & Mf0 & Ma0 & Mcb).
  unfold mem_w1x. eexists. split.
  - 
    stepn F_1755c D_1755c. rewrite Hsp. sp_renorm.
    stepST F_17560 D_17560 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_17564 D_17564 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    stepn F_17568 D_17568.
    stepn F_1756c D_1756c. rewrite Htp.
    stepLD F_17570 D_17570 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    stepn F_17574 D_17574.
    stepn F_17578 D_17578.
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_1757c | reflexivity | exact D_1757c
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_17580 | reflexivity | exact D_17580 | gres; cond_compute ] | ].
    norm_pc_r.
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_17584 | reflexivity | exact D_17584
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    stepb_ft F_17588 D_17588 ltac:(cond_compute).
    stepn F_1758c D_1758c.
    stepb_ft F_17590 D_17590 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    stepb_tk F_17594 D_17594 ltac:(cond_compute).
    stepn F_175b8 D_175b8. rewrite Ha0.
    stepn F_175bc D_175bc.
    stepn F_17378 D_17378. sp_renorm.
    stepST F_1737c D_1737c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x175c0) ltac:(sok_stack SOK).
    stepST F_17380 D_17380 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_17384 D_17384 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_17388 D_17388 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_1738c D_1738c (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    stepn F_17390 D_17390.
    stepn F_17394 D_17394.
    stepn F_17398 D_17398.
    stepn F_1739c D_1739c.
    stepn F_173a0 D_173a0.
    stepn F_1ece8 D_1ece8.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_1ecec | reflexivity | exact D_1ecec | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_1ecf0 D_1ecf0 ltac:(cond_compute).
    stepret F_1eee0 D_1eee0 (0x173a4 : word) ltac:(bveq).
    stepLD8 F_173a4 D_173a4 (Z_to_bv 64 0x51538).
    stepb_ft F_173a8 D_173a8 ltac:(cond_compute).
    stepLD F_173ac D_173ac (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepn F_173b0 D_173b0.
    stepn F_173c8 D_173c8.
    stepST F_173cc D_173cc (Z_to_bv 64 0x51528) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_173d0 D_173d0 ltac:(cond_compute).
    stepLD8 F_173d4 D_173d4 (Z_to_bv 64 0x51538).
    stepn F_173d8 D_173d8.
    stepn F_173dc D_173dc.
    stepLD8 F_173e0 D_173e0 (Z_to_bv 64 0x17508).
    stepLD8 F_173e4 D_173e4 (Z_to_bv 64 0x12f10).
    stepn F_173e8 D_173e8.
    stepn F_173ec D_173ec.
    stepLD F_1ef70 D_1ef70 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_1ef74 D_1ef74 ltac:(cond_compute).
    stepret F_1ef78 D_1ef78 (0x173f0 : word) ltac:(bveq).
    stepn F_173f0 D_173f0.
    stepjr F_173f4 D_173f4 (Z_to_bv 64 0x17508) ltac:(gres; reflexivity). vnorm.
    stepjr F_17508 D_17508 (Z_to_bv 64 0x12f10) ltac:(gres; reflexivity). vnorm.
    stepn F_12f10 D_12f10.
    stepLBU F_12f14 D_12f14 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_12f18 D_12f18 ltac:(cond_compute).
    stepret F_12f1c D_12f1c (0x173f8 : word) ltac:(bveq).
    stepn F_173f8 D_173f8.
    stepn F_173fc D_173fc.
    stepn F_1ece8 D_1ece8.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_1ecec | reflexivity | exact D_1ecec | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_1ecf0 D_1ecf0 ltac:(cond_compute).
    stepret F_1eee0 D_1eee0 (0x17400 : word) ltac:(bveq).
    stepLD F_17400 D_17400 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; apply rdn_hit4; zsimp; lia) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepn F_17404 D_17404.
    stepST F_17408 D_17408 (Z_to_bv 64 0x51528) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_1740c D_1740c ltac:(cond_compute).
    stepLD8 F_17410 D_17410 (Z_to_bv 64 0x51538).
    stepn F_17414 D_17414.
    stepLD8 F_173b4 D_173b4 (Z_to_bv 64 0).
    stepn F_173b8 D_173b8.
    stepST F_173bc D_173bc (Z_to_bv 64 0x51528) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_173c0 D_173c0 (Z_to_bv 64 0x51530) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_173c4 D_173c4 ltac:(cond_compute).
    stepn F_17418 D_17418.
    stepST F_1741c D_1741c (Z_to_bv 64 0x51520) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_17420 D_17420.
    stepLD8 F_17424 D_17424 (Z_to_bv 64 0x175c0).
    stepLD8 F_17428 D_17428 code.
    stepLD8 F_1742c D_1742c (getr regs 9).
    stepLD8 F_17430 D_17430 (getr regs 18).
    stepLD8 F_17434 D_17434 (getr regs 19).
    stepn F_17438 D_17438. sp_renorm.
    stepn F_1743c D_1743c.
    stepLD F_1ef70 D_1ef70 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_1ef74 D_1ef74 ltac:(cond_compute).
    stepret F_1ef78 D_1ef78 (0x175c0 : word) ltac:(bveq).
    stepn F_175c0 D_175c0.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.


(* [comment removed for export] *)
Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x175c4)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x17540)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x200c0)))
    (Z_to_bv 64 0x213c8) [Z_to_bv 8 1].

Lemma w2 : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x175c4 -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x20160) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x200c8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x20168) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x200c0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x200c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12a58)) ->
  rdn RSEGS mem (Z_to_bv 64 0x213c8) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x20108) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x17440)) ->
  rdn RSEGS mem (Z_to_bv 64 0x20110) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x21170) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x21170)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x17510 : word) mem rom)
                 (mkst regs' (0x198d4 : word) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x175c8
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2. eexists. split.
  - (* [comment removed for export] *)
    stepn F_17510 D_17510. rewrite Hsp. sp_renorm.
    stepST F_17514 D_17514 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x175c4) ltac:(sok_stack SOK).
    stepST F_17518 D_17518 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_1751c D_1751c (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_17520 D_17520.
    stepn F_17524 D_17524.
    stepLD8 F_17528 D_17528 (Z_to_bv 64 0x200c8).
    stepLD8 F_1752c D_1752c (Z_to_bv 64 0x200c0).
    (* [comment removed for export] *)
    stepb_ft F_17530 D_17530 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_17534 D_17534 (Z_to_bv 64 0x12a58).
    stepn F_17538 D_17538.
    stepjr F_1753c D_1753c (Z_to_bv 64 0x12a58) ltac:(gres; reflexivity). vnorm.
    (* [comment removed for export] *)
    stepn F_12a58 D_12a58. sp_renorm.
    stepST F_12a5c D_12a5c (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x17540) ltac:(sok_stack SOK).
    stepST F_12a60 D_12a60 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x200c0) ltac:(sok_stack SOK).
    stepn F_12a64 D_12a64.
    stepn F_12a68 D_12a68.
    stepn F_12a6c D_12a6c.
    (* [comment removed for export] *)
    stepLBU F_12a70 D_12a70 (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
    stepn F_12a74 D_12a74.
    stepb_tk F_12a78 D_12a78 ltac:(cond_compute).
    stepn F_12a84 D_12a84.
    stepn F_12a88 D_12a88.
    stepn F_12a8c D_12a8c.
    (* [comment removed for export] *)
    stepST F_12a90 D_12a90 (Z_to_bv 64 0x213c8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_12a94 D_12a94.
    stepLD8 F_12a98 D_12a98 (Z_to_bv 64 0x17440).
    stepb_ft F_12a9c D_12a9c ltac:(cond_compute).
    stepn F_12aa0 D_12aa0.
    stepn F_12aa4 D_12aa4.
    stepn F_12aa8 D_12aa8.
    stepLD8 F_12aac D_12aac (Z_to_bv 64 0x21170).
    stepn F_12ab0 D_12ab0.
    stepret F_17440 D_17440 (0x12ab4 : word) ltac:(bveq).
    stepn F_12ab4 D_12ab4.
    (* [comment removed for export] *)
    stepn F_12ab8 D_12ab8.
    stepLD8 F_12abc D_12abc (Z_to_bv 64 0).
    stepb_tk F_12ac0 D_12ac0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_12ad8 D_12ad8 (Z_to_bv 64 0x17540).
    stepLD8 F_12adc D_12adc (Z_to_bv 64 0x200c0).
    stepn F_12ae0 D_12ae0. sp_renorm.
    stepret F_12ae4 D_12ae4 (0x17540 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_17540 D_17540.
    stepb_ft F_17544 D_17544 ltac:(cond_compute).
    stepLD8 F_17548 D_17548 (Z_to_bv 64 0x175c4).
    stepLD8 F_1754c D_1754c code.
    stepLD8 F_17550 D_17550 s1v.
    stepn F_17554 D_17554. sp_renorm.
    (* [comment removed for export] *)
    stepn F_17558 D_17558.
    stepret F_1750c D_1750c (0x175c4 : word) ltac:(bveq).
    stepn F_175c4 D_175c4.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End WithFP1.


(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End UbExit_run1.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Ub_code_198d4_19c3c Ub_code_1e6dc_1f0b8.

Module UbExit_run2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StepTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.WalkTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibAtomic OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbExitBase OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_1735c_17f20 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_198d4_19c3c OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_1e6dc_1f0b8.
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
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x175c8)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x198e4)))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

Lemma w3a : forall regs mem rom (sp code wp1 rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x175c8 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  file_clean mem 0x21288 wp1 rp1 ->
  file_clean mem 0x21198 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x198d4 : word) mem rom)
                 (mkst regs' (0x17364 : word) (mem_w3a mem sp code) rom)
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
    stepn F_198d4 D_198d4. rewrite Hsp. sp_renorm.
    stepST F_198d8 D_198d8 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x175c8) ltac:(sok_stack SOK).
    stepST F_198dc D_198dc (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_198e0 D_198e0.
    stepn F_19a78 D_19a78. sp_renorm.
    stepST F_19a7c D_19a7c (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x198e4) ltac:(sok_stack SOK).
    stepST F_19a80 D_19a80 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_19a84 D_19a84.
    stepn F_19a88 D_19a88.
    stepn F_19a8c D_19a8c.
    (* [comment removed for export] *)
    stepn F_19a90 D_19a90.
    stepn F_1ece8 D_1ece8.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_1ecec | reflexivity | exact D_1ecec | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_1ecf0 D_1ecf0 ltac:(cond_compute).
    stepret F_1eee0 D_1eee0 (0x19a94 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_19a94 D_19a94.
    stepLD8 F_19a98 D_19a98 (Z_to_bv 64 0x198e4).
    stepLD8 F_19a9c D_19a9c code.
    stepn F_19aa0 D_19aa0. sp_renorm.
    stepret F_19aa4 D_19aa4 (0x198e4 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_198e4 D_198e4 (Z_to_bv 64 0).
    stepb_ft F_198e8 D_198e8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_198ec D_198ec.
    stepLD8 F_198f0 D_198f0 (Z_to_bv 64 0).
    stepb_tk F_198f4 D_198f4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_19948 D_19948.
    stepLD8 F_1994c D_1994c (Z_to_bv 64 0x21288).
    stepb_ft F_19950 D_19950 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_19954 D_19954 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_19958 D_19958 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_19964 D_19964 wp1.
    stepLD8 F_19968 D_19968 wp1.
    stepb_tk F_1996c D_1996c ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_19984 D_19984 rp1.
    stepLD8 F_19988 D_19988 rp1.
    stepb_tk F_1998c D_1998c ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_199a4 D_199a4.
    stepLD8 F_199a8 D_199a8 (Z_to_bv 64 0x21198).
    stepb_ft F_199ac D_199ac ltac:(cond_compute).
    stepLD F_199b0 D_199b0 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_199b4 D_199b4 ltac:(cond_compute).
    stepLD8 F_199c0 D_199c0 wp2.
    stepLD8 F_199c4 D_199c4 wp2.
    stepb_tk F_199c8 D_199c8 ltac:(apply c_eq_refl).
    stepLD8 F_199e0 D_199e0 rp2.
    stepLD8 F_199e4 D_199e4 rp2.
    stepb_tk F_199e8 D_199e8 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_19a68 D_19a68 (Z_to_bv 64 0x175c8).
    stepLD8 F_19a6c D_19a6c code.
    stepn F_19a70 D_19a70. sp_renorm.
    stepret F_19a74 D_19a74 (0x175c8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_175c8 D_175c8.
    stepn F_175cc D_175cc.
    stepn F_1735c D_1735c.
    stepn F_17360 D_17360.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End WithFP1.


(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End UbExit_run2.

Module UbExit_run3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.skcms.iccprofile_info.images.Ubsan.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StepTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.WalkTac OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StreamSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.MmapSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibAtomic OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbExitBase UbExit_run2 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_1735c_17f20 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_198d4_19c3c OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Ub_code_1e6dc_1f0b8.
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
  rdn RSEGS mem (Z_to_bv 64 (0x21288 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x21288 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x21288 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x21288 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x19ae4)).

Lemma w3b1 : forall regs mem rom (sp code : word) (wb wp : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x175c8 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  stdout_dirty_hdr mem wb wp ->
  (0 <= wb < 2^64)%Z -> (0 <= wp < 2^64)%Z -> wb <> wp ->
  exists regs',
    msteps RSEGS (mkst regs (0x198d4 : word) mem rom)
                 (mkst regs' (0x19ae4 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = Z_to_bv 64 0x21288
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 1 = Z_to_bv 64 0x19984
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32)
    /\ getr regs' 8 = Z_to_bv 64 0x21288
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof.
  intros regs mem rom sp code wb wp Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr) (F1l & F1wp & F1wb & F1wr) WB WP NE.
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
  unfold mem_w3a. eexists. split.
  - (* [comment removed for export] *)
    stepn F_198d4 D_198d4. rewrite Hsp. sp_renorm.
    stepST F_198d8 D_198d8 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x175c8) ltac:(sok_stack SOK).
    stepST F_198dc D_198dc (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_198e0 D_198e0.
    stepn F_19a78 D_19a78. sp_renorm.
    stepST F_19a7c D_19a7c (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x198e4) ltac:(sok_stack SOK).
    stepST F_19a80 D_19a80 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_19a84 D_19a84.
    stepn F_19a88 D_19a88.
    stepn F_19a8c D_19a8c.
    (* [comment removed for export] *)
    stepn F_19a90 D_19a90.
    stepn F_1ece8 D_1ece8.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_1ecec | reflexivity | exact D_1ecec | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_1ecf0 D_1ecf0 ltac:(cond_compute).
    stepret F_1eee0 D_1eee0 (0x19a94 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_19a94 D_19a94.
    stepLD8 F_19a98 D_19a98 (Z_to_bv 64 0x198e4).
    stepLD8 F_19a9c D_19a9c code.
    stepn F_19aa0 D_19aa0. sp_renorm.
    stepret F_19aa4 D_19aa4 (0x198e4 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_198e4 D_198e4 (Z_to_bv 64 0).
    stepb_ft F_198e8 D_198e8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_198ec D_198ec.
    stepLD8 F_198f0 D_198f0 (Z_to_bv 64 0).
    stepb_tk F_198f4 D_198f4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_19948 D_19948.
    stepLD8 F_1994c D_1994c (Z_to_bv 64 0x21288).
    stepb_ft F_19950 D_19950 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_19954 D_19954 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_19958 D_19958 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_19964 D_19964 (Z_to_bv 64 wp).
    stepLD8 F_19968 D_19968 (Z_to_bv 64 wb).
    stepb_ft F_1996c D_1996c ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepLD8 F_19970 D_19970 (Z_to_bv 64 0x19ae4).
    stepn F_19974 D_19974.
    stepn F_19978 D_19978.
    stepn F_1997c D_1997c.
    stepjr F_19980 D_19980 (Z_to_bv 64 0x19ae4) ltac:(gres; reflexivity). vnorm.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma w3b2 : forall regs mem rom (sp code rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 32) -> getr regs 8 = Z_to_bv 64 0x21288 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x175c8)) ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 code) ->
  rdn RSEGS mem (Z_to_bv 64 (0x21288 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 (0x21288 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 0x21280) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x21198)) ->
  file_clean mem 0x21198 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x19984 : word) mem rom)
                 (mkst regs' (0x17364 : word) mem rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr
         (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_19984 D_19984 rp1.
    stepLD8 F_19988 D_19988 rp1.
    stepb_tk F_1998c D_1998c ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_199a4 D_199a4.
    stepLD8 F_199a8 D_199a8 (Z_to_bv 64 0x21198).
    stepb_ft F_199ac D_199ac ltac:(cond_compute).
    stepLD F_199b0 D_199b0 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_199b4 D_199b4 ltac:(cond_compute).
    stepLD8 F_199c0 D_199c0 wp2.
    stepLD8 F_199c4 D_199c4 wp2.
    stepb_tk F_199c8 D_199c8 ltac:(apply c_eq_refl).
    stepLD8 F_199e0 D_199e0 rp2.
    stepLD8 F_199e4 D_199e4 rp2.
    stepb_tk F_199e8 D_199e8 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_19a68 D_19a68 (Z_to_bv 64 0x175c8).
    stepLD8 F_19a6c D_19a6c code.
    stepn F_19a70 D_19a70. rewrite Hsp. sp_renorm.
    stepret F_19a74 D_19a74 (0x175c8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_175c8 D_175c8.
    stepn F_175cc D_175cc.
    stepn F_1735c D_1735c.
    stepn F_17360 D_17360.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.
End WithFP1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
End UbExit_run3.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require UbStdioWrite.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes Spec LibWritev UbStdioDefs. Import UbExit_run1. Import UbExit_run2. Import UbExit_run3. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require UbStdioWrite. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbStdioWrite.UbStdioWrite_run1. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require UbStdioWrite. Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.UbStdioWrite.UbStdioWrite_run2. From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import UbStdioWrite Ub_code_1735c_17f20.
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
  em_ra   : getr regs1 1 = Z_to_bv 64 0x175c4;
  em_splo : (4294967296 <= bv_unsigned sp - 144)%Z;
  em_sphi : (bv_unsigned sp <= 0x800000000000)%Z;
  em_sok  : store_ok RSEGS mem1 (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true;
  em_fe   : rdn RSEGS mem1 (Z_to_bv 64 0x20160) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x200c8));
  em_fs   : rdn RSEGS mem1 (Z_to_bv 64 0x20168) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x200c0));
  em_fa   : rdn RSEGS mem1 (Z_to_bv 64 0x200c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12a58));
  em_comp : rdn RSEGS mem1 (Z_to_bv 64 0x213c8) 1%nat = Some [Z_to_bv 8 0];
  em_g1   : rdn RSEGS mem1 (Z_to_bv 64 0x20108) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x17440));
  em_g2   : rdn RSEGS mem1 (Z_to_bv 64 0x20110) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  em_dso  : rdn RSEGS mem1 (Z_to_bv 64 0x21170) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x21170));
  em_glob : stdio_globals mem1;
  em_err  : file_clean mem1 0x21198 wp2 rp2
}.

Lemma ref_exit_mid_clean :
  forall regs1 mem1 model (sp code : word) (wp2 rp2 wp1 rp1 : word),
  exit_mid regs1 mem1 sp code wp2 rp2 ->
  file_clean mem1 0x21288 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs1 (0x17510 : word) mem1 (seg_rom RSEGS)) model)
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
  eapply rz_exit_at; [exact F_17364 | exact E_17364 | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.

Lemma ref_exit_mid_flush :
  forall regs1 mem1 model (sp code : word) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_mid regs1 mem1 sp code wp2 rp2 ->
  stdout_pending mem1 wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  realizes RSEGS (mkCfg (mkst regs1 (0x17510 : word) mem1 (seg_rom RSEGS)) model)
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
  replace (Z_to_bv 64 0x19984) with (0x19984 : word) in R3ra by (apply bv_eq; reflexivity).
  unfold W. rewrite <- (app_nil_r pending).
  set (mem3 := mem_w3a (mem_w2 mem1 sp code (getr regs1 9)) sp code).
  eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) 0x21288 wb wp 1
            (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x19984 : word) pending []);
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
    eapply rz_exit_at; [exact F_17364 | exact E_17364 | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.


Lemma ref_exit_w1 :
  forall regs mem rom (sp tp code : word) (tid : Z) (wp2 rp2 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  exists regs1 mem1,
    msteps RSEGS (mkst regs (0x1755c : word) mem rom) (mkst regs1 (0x17510 : word) mem1 rom)
    /\ exit_mid regs1 mem1 sp code wp2 rp2
    /\ (forall (a : word) n bs, rdn RSEGS mem a n = Some bs ->
          (bv_unsigned a + Z.of_nat n <= 2 ^ 64)%Z ->
          (bv_unsigned a + Z.of_nat n <= bv_unsigned sp - 56 \/ bv_unsigned sp <= bv_unsigned a)%Z ->
          (bv_unsigned a + Z.of_nat n <= 0x51520 \/ 0x51538 <= bv_unsigned a)%Z ->
          (bv_unsigned a + Z.of_nat n <= 0x51740 \/ 0x51744 <= bv_unsigned a)%Z ->
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
  file_clean mem 0x21288 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x1755c : word) mem (seg_rom RSEGS)) model)
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
  realizes RSEGS (mkCfg (mkst regs (0x1755c : word) mem (seg_rom RSEGS)) model)
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
  realizes RSEGS (mkCfg (mkst regs (0x1755c : word) mem (seg_rom RSEGS)) model)
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
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x1755c) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros. replace (Z_to_bv 64 0x1755c) with (0x1755c : word) by (apply bv_eq; reflexivity).
  apply ref_exit; assumption.
Qed.
End WithFP1.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].
