(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SumWalkTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require U.S0ExitBase.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require SumWalkTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require CatSim.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ShapeAlg Nodes Spec LibWritev U.S0StdioDefs U.S0StdioWrite.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec U.S0_code_1337c_1378c U.S0_code_1ed68_1f620 U.S0_code_20620_216f4 U.S0_code_216f4_226f4 U.S0_code_26728_26f04 U.S0_code_atexit          .
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require WalkHideSum.
Import WalkHideSum.OptIn.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require NatLitLia.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Module S7Exit_run1.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StepTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Hoare OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.WalkTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StreamSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SumWalkTac.LibAtomic OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ExitBase.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma rdn_wbytes_hit4 : forall segs m (a v : word),
  (bv_unsigned a + 4 <= 2^64)%Z ->
  rdn segs (wbytes m a (word_to_le_bytes 4 v)) a 4%nat = Some (word_to_le_bytes 4 v).
Proof.
  intros segs m a v Hnw.
  pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 v) m a) as H.
  rewrite length_N_to_le_bytes in H. apply H. exact Hnw.
Qed.

Ltac rdn_hit4 := apply rdn_wbytes_hit4; zsimp; lia.

Definition mem_w1e (mem : word -> option byte) (sp ra s0 code s1 s2 s3 : word) (tid : Z) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 0x64448) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x29224)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3))
    (Z_to_bv 64 0x64228) [Z_to_bv 8 1].

Definition mem_w1o (mem : word -> option byte) (sp ra s0 code s1 s2 s3 : word) (tid : Z) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 0x64448) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x29224)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3))
    (Z_to_bv 64 0x64230) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x64230) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x64230) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x64238) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x64228) [Z_to_bv 8 1].

Lemma w1e : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0x64448) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x64473) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x64238) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x6422c) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x291c0 : word) mem rom)
                 (mkst regs' (0x29174 : word) (mem_w1e mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x29228
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Mhd Mlk.
  unfold mem_w1e. eexists. split.
  - (* [comment removed for export] *)
    stepn F_1f478 D_1f478. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_1f47c D_1f47c (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_1f480 D_1f480 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_1f484 D_1f484.
    stepn F_1f488 D_1f488. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_1f48c D_1f48c (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_1f490 D_1f490.
    stepn F_1f494 D_1f494.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_1f498 | reflexivity | exact D_1f498
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_1f49c | reflexivity | exact D_1f49c | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_1f4a0 | reflexivity | exact D_1f4a0
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_1f4a4 D_1f4a4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_1f4a8 D_1f4a8.
    (* [comment removed for export] *)
    stepb_ft F_1f4ac D_1f4ac ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_1f4b0 D_1f4b0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_1f4d4 D_1f4d4. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_1f4d8 D_1f4d8.
    stepn F_n1f518 D_n1f518. sp_renorm.
    stepST F_n1f51c D_n1f51c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x29224) ltac:(sok_stack SOK).
    stepST F_n1f520 D_n1f520 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_n1f524 D_n1f524 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_n1f528 D_n1f528 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_n1f52c D_n1f52c (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    stepn F_n1f530 D_n1f530.
    stepn F_n1f534 D_n1f534.
    stepn F_n1f538 D_n1f538.
    stepn F_n1f53c D_n1f53c.
    stepn F_n1f540 D_n1f540.
    stepn F_26b40 D_26b40.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_26b44 | reflexivity | exact D_26b44 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_26b48 D_26b48 ltac:(cond_compute).
    stepret F_26d38 D_26d38 (0x29008 : word) ltac:(bveq).
    stepLD8 F_n1f544 D_n1f544 (Z_to_bv 64 0).
    stepb_tk F_n1f548 D_n1f548 ltac:(cond_compute).
    stepn F_n1f5b8 D_n1f5b8.
    stepST F_n1f5bc D_n1f5bc (Z_to_bv 64 0x64228) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_n1f5c0 D_n1f5c0.
    stepLD8 F_n1f5c4 D_n1f5c4 (Z_to_bv 64 0x29224).
    stepLD8 F_n1f5c8 D_n1f5c8 code.
    stepLD8 F_n1f5cc D_n1f5cc (getr regs 9).
    stepLD8 F_n1f5d0 D_n1f5d0 (getr regs 18).
    stepLD8 F_n1f5d4 D_n1f5d4 (getr regs 19).
    stepn F_n1f5d8 D_n1f5d8. sp_renorm.
    stepn F_n1f5dc D_n1f5dc.
    stepLD F_26dc8 D_26dc8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_26dcc D_26dcc ltac:(cond_compute).
    stepret F_26dd0 D_26dd0 (0x29224 : word) ltac:(bveq).
    stepn F_1f4dc D_1f4dc.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.

Lemma w1o : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0x64448) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x64473) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x6422c) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x64230) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn RSEGS mem (Z_to_bv 64 0x64238) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x64240)) ->
  rdn RSEGS mem (Z_to_bv 64 0x64240) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x64248) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2916c)) ->
  rdn RSEGS mem (Z_to_bv 64 0x64348) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x139a8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x440e4) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x291c0 : word) mem rom)
                 (mkst regs' (0x29174 : word) (mem_w1o mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x29228
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl
         Mlk Msl Mhd Mnx Mf0 Ma0 Mcb.
  unfold mem_w1o. eexists. split.
  - stepn F_1f478 D_1f478. rewrite Hsp. sp_renorm.
    stepST F_1f47c D_1f47c (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_1f480 D_1f480 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    stepn F_1f484 D_1f484.
    stepn F_1f488 D_1f488. rewrite Htp.
    stepLD F_1f48c D_1f48c (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    stepn F_1f490 D_1f490.
    stepn F_1f494 D_1f494.
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_1f498 | reflexivity | exact D_1f498
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_1f49c | reflexivity | exact D_1f49c | gres; cond_compute ] | ].
    norm_pc_r.
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_1f4a0 | reflexivity | exact D_1f4a0
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    stepb_ft F_1f4a4 D_1f4a4 ltac:(cond_compute).
    stepn F_1f4a8 D_1f4a8.
    stepb_ft F_1f4ac D_1f4ac ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    stepb_tk F_1f4b0 D_1f4b0 ltac:(cond_compute).
    stepn F_1f4d4 D_1f4d4. rewrite Ha0.
    stepn F_1f4d8 D_1f4d8.
    stepn F_n1f518 D_n1f518. sp_renorm.
    stepST F_n1f51c D_n1f51c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x29224) ltac:(sok_stack SOK).
    stepST F_n1f520 D_n1f520 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_n1f524 D_n1f524 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_n1f528 D_n1f528 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_n1f52c D_n1f52c (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    stepn F_n1f530 D_n1f530.
    stepn F_n1f534 D_n1f534.
    stepn F_n1f538 D_n1f538.
    stepn F_n1f53c D_n1f53c.
    stepn F_n1f540 D_n1f540.
    stepn F_26b40 D_26b40.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_26b44 | reflexivity | exact D_26b44 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_26b48 D_26b48 ltac:(cond_compute).
    stepret F_26d38 D_26d38 (0x29008 : word) ltac:(bveq).
    stepLD8 F_n1f544 D_n1f544 (Z_to_bv 64 0x64240).
    stepb_ft F_n1f548 D_n1f548 ltac:(cond_compute).
    stepLD F_n1f54c D_n1f54c (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepn F_n1f550 D_n1f550.
    stepn F_n1f568 D_n1f568.
    stepST F_n1f56c D_n1f56c (Z_to_bv 64 0x64230) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_n1f570 D_n1f570 ltac:(cond_compute).
    stepLD8 F_n1f574 D_n1f574 (Z_to_bv 64 0x64240).
    stepn F_n1f578 D_n1f578.
    stepn F_n1f57c D_n1f57c.
    stepLD8 F_n1f580 D_n1f580 (Z_to_bv 64 0x2916c).
    stepLD8 F_n1f584 D_n1f584 (Z_to_bv 64 0x139a8).
    stepn F_n1f588 D_n1f588.
    stepn F_n1f58c D_n1f58c.
    stepLD F_26dc8 D_26dc8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_26dcc D_26dcc ltac:(cond_compute).
    stepret F_26dd0 D_26dd0 (0x29054 : word) ltac:(bveq).
    stepn F_n1f590 D_n1f590.
    stepjr F_n1f594 D_n1f594 (Z_to_bv 64 0x2916c) ltac:(gres; reflexivity). vnorm.
    stepjr F_n1f6a8 D_n1f6a8 (Z_to_bv 64 0x139a8) ltac:(gres; reflexivity). vnorm.
    stepn F_n13970 D_n13970.
    stepLBU F_n13974 D_n13974 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_n13978 D_n13978 ltac:(cond_compute).
    stepret F_n1397c D_n1397c (0x2905c : word) ltac:(bveq).
    stepn F_n1f598 D_n1f598.
    stepn F_n1f59c D_n1f59c.
    stepn F_26b40 D_26b40.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_26b44 | reflexivity | exact D_26b44 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_26b48 D_26b48 ltac:(cond_compute).
    stepret F_26d38 D_26d38 (0x29064 : word) ltac:(bveq).
    stepLD F_n1f5a0 D_n1f5a0 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_hit4) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepn F_n1f5a4 D_n1f5a4.
    stepST F_n1f5a8 D_n1f5a8 (Z_to_bv 64 0x64230) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_n1f5ac D_n1f5ac ltac:(cond_compute).
    stepLD8 F_n1f5b0 D_n1f5b0 (Z_to_bv 64 0x64240).
    stepn F_n1f5b4 D_n1f5b4.
    stepLD8 F_n1f554 D_n1f554 (Z_to_bv 64 0).
    stepn F_n1f558 D_n1f558.
    stepST F_n1f55c D_n1f55c (Z_to_bv 64 0x64230) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_n1f560 D_n1f560 (Z_to_bv 64 0x64238) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_n1f564 D_n1f564 ltac:(cond_compute).
    stepn F_n1f5b8 D_n1f5b8.
    stepST F_n1f5bc D_n1f5bc (Z_to_bv 64 0x64228) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_n1f5c0 D_n1f5c0.
    stepLD8 F_n1f5c4 D_n1f5c4 (Z_to_bv 64 0x29224).
    stepLD8 F_n1f5c8 D_n1f5c8 code.
    stepLD8 F_n1f5cc D_n1f5cc (getr regs 9).
    stepLD8 F_n1f5d0 D_n1f5d0 (getr regs 18).
    stepLD8 F_n1f5d4 D_n1f5d4 (getr regs 19).
    stepn F_n1f5d8 D_n1f5d8. sp_renorm.
    stepn F_n1f5dc D_n1f5dc.
    stepLD F_26dc8 D_26dc8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_26dcc D_26dcc ltac:(cond_compute).
    stepret F_26dd0 D_26dd0 (0x29224 : word) ltac:(bveq).
    stepn F_1f4dc D_1f4dc.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.

(* [comment removed for export] *)
Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x29228)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x291a4)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x32090)))
    (Z_to_bv 64 0x340d8) [Z_to_bv 8 1].

Lemma w2 : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x29228 -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x32140) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x32098)) ->
  rdn RSEGS mem (Z_to_bv 64 0x32148) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x32090)) ->
  rdn RSEGS mem (Z_to_bv 64 0x32090) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x134f0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x340d8) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x320d8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x290a4)) ->
  rdn RSEGS mem (Z_to_bv 64 0x320e0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x33150) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x33150)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x29174 : word) mem rom)
                 (mkst regs' (0x2b570 : word) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x2922c
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2. eexists. split.
  - (* [comment removed for export] *)
    stepn F_1f42c D_1f42c. rewrite Hsp. sp_renorm.
    stepST F_1f430 D_1f430 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x29228) ltac:(sok_stack SOK).
    stepST F_1f434 D_1f434 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_1f438 D_1f438 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_1f43c D_1f43c.
    stepn F_1f440 D_1f440.
    stepLD8 F_1f444 D_1f444 (Z_to_bv 64 0x32098).
    stepLD8 F_1f448 D_1f448 (Z_to_bv 64 0x32090).
    (* [comment removed for export] *)
    stepb_ft F_1f44c D_1f44c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_1f450 D_1f450 (Z_to_bv 64 0x134f0).
    stepn F_1f454 D_1f454.
    stepjr F_1f458 D_1f458 (Z_to_bv 64 0x134f0) ltac:(gres; reflexivity). vnorm.
    (* [comment removed for export] *)
    stepn F_13438 D_13438. sp_renorm.
    stepST F_1343c D_1343c (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x291a4) ltac:(sok_stack SOK).
    stepST F_13440 D_13440 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x32090) ltac:(sok_stack SOK).
    stepn F_13444 D_13444.
    stepn F_13448 D_13448.
    stepn F_1344c D_1344c.
    (* [comment removed for export] *)
    stepLBU F_13450 D_13450 (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
    stepn F_13454 D_13454.
    stepb_tk F_13458 D_13458 ltac:(cond_compute).
    stepn F_13464 D_13464.
    stepn F_13468 D_13468.
    stepn F_1346c D_1346c.
    (* [comment removed for export] *)
    stepST F_13470 D_13470 (Z_to_bv 64 0x340d8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_13474 D_13474.
    stepLD8 F_13478 D_13478 (Z_to_bv 64 0x290a4).
    stepb_ft F_1347c D_1347c ltac:(cond_compute).
    stepn F_13480 D_13480.
    stepn F_13484 D_13484.
    stepn F_13488 D_13488.
    stepLD8 F_1348c D_1348c (Z_to_bv 64 0x33150).
    stepn F_13490 D_13490.
    stepret F_n1f5e0 D_n1f5e0 (0x1354c : word) ltac:(bveq).
    stepn F_13494 D_13494.
    (* [comment removed for export] *)
    stepn F_13498 D_13498.
    stepLD8 F_1349c D_1349c (Z_to_bv 64 0).
    stepb_tk F_134a0 D_134a0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_134b8 D_134b8 (Z_to_bv 64 0x291a4).
    stepLD8 F_134bc D_134bc (Z_to_bv 64 0x32090).
    stepn F_134c0 D_134c0. sp_renorm.
    stepret F_134c4 D_134c4 (0x291a4 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_1f45c D_1f45c.
    stepb_ft F_1f460 D_1f460 ltac:(cond_compute).
    stepLD8 F_1f464 D_1f464 (Z_to_bv 64 0x29228).
    stepLD8 F_1f468 D_1f468 code.
    stepLD8 F_1f46c D_1f46c s1v.
    stepn F_1f470 D_1f470. sp_renorm.
    (* [comment removed for export] *)
    stepn F_1f474 D_1f474.
    stepret F_1f428 D_1f428 (0x29228 : word) ltac:(bveq).
    stepn F_1f4e0 D_1f4e0.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S7Exit_run1.

(* [comment removed for export] *)
Module S7Exit_run2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StepTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Hoare OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.WalkTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StreamSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SumWalkTac.LibAtomic OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ExitBase.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition mem_w3a (mem : word -> option byte) (sp code : word) :=
  wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x2922c)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x2b580)))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

Lemma w3a : forall regs mem rom (sp code wp1 rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x2922c ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  file_clean mem 0x33f90 wp1 rp1 ->
  file_clean mem 0x33db0 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x2b570 : word) mem rom)
                 (mkst regs' (0x28fc8 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  (intros regs mem rom sp code wp1 rp1 wp2 rp2 Hsp Hs0 Hra SPlo SPhi SOK; cps_intros (Gnl & Gofl & Gin & Gout & Gerr & F0l & F0wp & F0wb & F0rp & F0re); cps_intros (F1l & F1wp & F1wb & F1rp & F1re); cps_intros (F2l & F2wp & F2wb & F2rp & F2re)).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  zaddr F0l; zaddr F0wp; zaddr F0wb; zaddr F0rp; zaddr F0re.
  unfold mem_w3a. eexists. split.
  - (* [comment removed for export] *)
    stepn F_21404 D_21404. rewrite Hsp. sp_renorm.
    stepST F_21408 D_21408 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x2922c) ltac:(sok_stack SOK).
    stepST F_2140c D_2140c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_21410 D_21410.
    stepn F_21a70 D_21a70. sp_renorm.
    stepST F_21a74 D_21a74 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x2b580) ltac:(sok_stack SOK).
    stepST F_21a78 D_21a78 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_21a7c D_21a7c.
    stepn F_21a80 D_21a80.
    stepn F_21a84 D_21a84.
    (* [comment removed for export] *)
    stepn F_21a88 D_21a88.
    stepn F_26b40 D_26b40.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_26b44 | reflexivity | exact D_26b44 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_26b48 D_26b48 ltac:(cond_compute).
    stepret F_26d38 D_26d38 (0x2bbf8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_21a8c D_21a8c.
    stepLD8 F_21a90 D_21a90 (Z_to_bv 64 0x2b580).
    stepLD8 F_21a94 D_21a94 code.
    stepn F_21a98 D_21a98. sp_renorm.
    stepret F_21a9c D_21a9c (0x2b580 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_21414 D_21414 (Z_to_bv 64 0).
    stepb_ft F_21418 D_21418 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_2141c D_2141c.
    stepLD8 F_21420 D_21420 (Z_to_bv 64 0x33ea0).
    stepb_ft F_21424 D_21424 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_21428 D_21428 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_2142c D_2142c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_21438 D_21438 (Z_to_bv 64 0).
    stepLD8 F_2143c D_2143c (Z_to_bv 64 0).
    stepb_tk F_21440 D_21440 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_21458 D_21458 (Z_to_bv 64 0).
    stepLD8 F_2145c D_2145c (Z_to_bv 64 0).
    stepb_tk F_21460 D_21460 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_21478 D_21478.
    stepLD8 F_2147c D_2147c (Z_to_bv 64 0x33f90).
    stepb_ft F_21480 D_21480 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_21484 D_21484 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_21488 D_21488 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_21494 D_21494 wp1.
    stepLD8 F_21498 D_21498 wp1.
    stepb_tk F_2149c D_2149c ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_214b4 D_214b4 rp1.
    stepLD8 F_214b8 D_214b8 rp1.
    stepb_tk F_214bc D_214bc ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_214d4 D_214d4.
    stepLD8 F_214d8 D_214d8 (Z_to_bv 64 0x33db0).
    stepb_ft F_214dc D_214dc ltac:(cond_compute).
    stepLD F_214e0 D_214e0 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_214e4 D_214e4 ltac:(cond_compute).
    stepLD8 F_214f0 D_214f0 wp2.
    stepLD8 F_214f4 D_214f4 wp2.
    stepb_tk F_214f8 D_214f8 ltac:(apply c_eq_refl).
    stepLD8 F_21510 D_21510 rp2.
    stepLD8 F_21514 D_21514 rp2.
    stepb_tk F_21518 D_21518 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_21598 D_21598 (Z_to_bv 64 0x2922c).
    stepLD8 F_2159c D_2159c code.
    stepn F_215a0 D_215a0. sp_renorm.
    stepret F_215a4 D_215a4 (0x2922c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_1f4e4 D_1f4e4.
    stepn F_1f4e8 D_1f4e8.
    stepn F_1f40c D_1f40c.
    stepn F_1f410 D_1f410.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S7Exit_run2.

(* [comment removed for export] *)
Module S7Exit_run3.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StepTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Hoare OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.WalkTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StreamSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SumWalkTac.LibAtomic OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0ExitBase S7Exit_run2.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition stdout_dirty_hdr (mem : word -> option byte) (wb wp : Z) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 (0x33f90 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x33f90 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x33f90 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
  /\ rdn RSEGS mem (Z_to_bv 64 (0x33f90 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2b114)).

Lemma w3b1 : forall regs mem rom (sp code : word) (wb wp : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x2922c ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  stdout_dirty_hdr mem wb wp ->
  (0 <= wb < 2^64)%Z -> (0 <= wp < 2^64)%Z -> wb <> wp ->
  exists regs',
    msteps RSEGS (mkst regs (0x2b570 : word) mem rom)
                 (mkst regs' (0x2b114 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = Z_to_bv 64 0x33f90
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 1 = Z_to_bv 64 0x2b620
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32)
    /\ getr regs' 8 = Z_to_bv 64 0x33f90
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof.
  (intros regs mem rom sp code wb wp Hsp Hs0 Hra SPlo SPhi SOK; cps_intros (Gnl & Gofl & Gin & Gout & Gerr & F0l & F0wp & F0wb & F0rp & F0re); cps_intros (F1l & F1wp & F1wb & F1wr); intros WB WP NE).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
  zaddr F0l; zaddr F0wp; zaddr F0wb; zaddr F0rp; zaddr F0re.
  unfold mem_w3a. eexists. split.
  - (* [comment removed for export] *)
    stepn F_21404 D_21404. rewrite Hsp. sp_renorm.
    stepST F_21408 D_21408 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x2922c) ltac:(sok_stack SOK).
    stepST F_2140c D_2140c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_21410 D_21410.
    stepn F_21a70 D_21a70. sp_renorm.
    stepST F_21a74 D_21a74 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x2b580) ltac:(sok_stack SOK).
    stepST F_21a78 D_21a78 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_21a7c D_21a7c.
    stepn F_21a80 D_21a80.
    stepn F_21a84 D_21a84.
    (* [comment removed for export] *)
    stepn F_21a88 D_21a88.
    stepn F_26b40 D_26b40.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_26b44 | reflexivity | exact D_26b44 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_26b48 D_26b48 ltac:(cond_compute).
    stepret F_26d38 D_26d38 (0x2bbf8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_21a8c D_21a8c.
    stepLD8 F_21a90 D_21a90 (Z_to_bv 64 0x2b580).
    stepLD8 F_21a94 D_21a94 code.
    stepn F_21a98 D_21a98. sp_renorm.
    stepret F_21a9c D_21a9c (0x2b580 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_21414 D_21414 (Z_to_bv 64 0).
    stepb_ft F_21418 D_21418 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_2141c D_2141c.
    stepLD8 F_21420 D_21420 (Z_to_bv 64 0x33ea0).
    stepb_ft F_21424 D_21424 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_21428 D_21428 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_2142c D_2142c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_21438 D_21438 (Z_to_bv 64 0).
    stepLD8 F_2143c D_2143c (Z_to_bv 64 0).
    stepb_tk F_21440 D_21440 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_21458 D_21458 (Z_to_bv 64 0).
    stepLD8 F_2145c D_2145c (Z_to_bv 64 0).
    stepb_tk F_21460 D_21460 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_21478 D_21478.
    stepLD8 F_2147c D_2147c (Z_to_bv 64 0x33f90).
    stepb_ft F_21480 D_21480 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_21484 D_21484 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_21488 D_21488 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_21494 D_21494 (Z_to_bv 64 wp).
    stepLD8 F_21498 D_21498 (Z_to_bv 64 wb).
    stepb_ft F_2149c D_2149c ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    stepLD8 F_214a0 D_214a0 (Z_to_bv 64 0x2b114).
    stepn F_214a4 D_214a4.
    stepn F_214a8 D_214a8.
    stepn F_214ac D_214ac.
    stepjr F_214b0 D_214b0 (Z_to_bv 64 0x2b114) ltac:(gres; reflexivity). vnorm.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Lemma w3b2 : forall regs mem rom (sp code rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 32) -> getr regs 8 = Z_to_bv 64 0x33f90 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2922c)) ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 code) ->
  rdn RSEGS mem (Z_to_bv 64 (0x33f90 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 (0x33f90 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn RSEGS mem (Z_to_bv 64 0x33e98) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x33db0)) ->
  file_clean mem 0x33db0 wp2 rp2 ->
  exists regs',
    msteps RSEGS (mkst regs (0x2b620 : word) mem rom)
                 (mkst regs' (0x28fc8 : word) mem rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  (intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr; cps_intros (F2l & F2wp & F2wb & F2rp & F2re)).
  zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  eexists. split.
  - (* [comment removed for export] *)
    stepLD8 F_214b4 D_214b4 rp1.
    stepLD8 F_214b8 D_214b8 rp1.
    stepb_tk F_214bc D_214bc ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepn F_214d4 D_214d4.
    stepLD8 F_214d8 D_214d8 (Z_to_bv 64 0x33db0).
    stepb_ft F_214dc D_214dc ltac:(cond_compute).
    stepLD F_214e0 D_214e0 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_214e4 D_214e4 ltac:(cond_compute).
    stepLD8 F_214f0 D_214f0 wp2.
    stepLD8 F_214f4 D_214f4 wp2.
    stepb_tk F_214f8 D_214f8 ltac:(apply c_eq_refl).
    stepLD8 F_21510 D_21510 rp2.
    stepLD8 F_21514 D_21514 rp2.
    stepb_tk F_21518 D_21518 ltac:(apply c_eq_refl).
    (* [comment removed for export] *)
    stepLD8 F_21598 D_21598 (Z_to_bv 64 0x2922c).
    stepLD8 F_2159c D_2159c code.
    stepn F_215a0 D_215a0. rewrite Hsp. sp_renorm.
    stepret F_215a4 D_215a4 (0x2922c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_1f4e4 D_1f4e4.
    stepn F_1f4e8 D_1f4e8.
    stepn F_1f40c D_1f40c.
    stepn F_1f410 D_1f410.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S7Exit_run3.

(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StepTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Hoare OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.WalkTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.StreamSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.MmapSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.SumWalkTac.LibAtomic OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.CatSim.ExitSim OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.LibWritev OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0StdioDefs S7Exit_run1 S7Exit_run2 S7Exit_run3 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0StdioWrite.S7StdioWrite_run1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0StdioWrite.S7StdioWrite_run2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.S0StdioWrite.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import ListNotations.
Local Ltac Lia.lia ::= NatLitLia.lia_natlit_goal.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac zaddr_rec H := zaddr H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record fini_pre (regs : bvmap 5 word) (mem : word -> option byte)
       (sp code : word) (wp2 rp2 : word) : Prop := {
  fp_sp   : getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16);
  fp_s0   : getr regs 8 = code;
  fp_ra   : getr regs 1 = Z_to_bv 64 0x29228;
  fp_splo : (4294967296 <= bv_unsigned sp - 144)%Z;
  fp_sphi : (bv_unsigned sp <= 0x800000000000)%Z;
  fp_sok  : store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true;
  fp_fe   : rdn RSEGS mem (Z_to_bv 64 0x32140) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x32098));
  fp_fs   : rdn RSEGS mem (Z_to_bv 64 0x32148) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x32090));
  fp_fa   : rdn RSEGS mem (Z_to_bv 64 0x32090) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x134f0));
  fp_comp : rdn RSEGS mem (Z_to_bv 64 0x340d8) 1%nat = Some [Z_to_bv 8 0];
  fp_g1   : rdn RSEGS mem (Z_to_bv 64 0x320d8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x290a4));
  fp_g2   : rdn RSEGS mem (Z_to_bv 64 0x320e0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  fp_dso  : rdn RSEGS mem (Z_to_bv 64 0x33150) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x33150));
  fp_glob : stdio_globals mem;
  fp_err  : file_clean mem 0x33db0 wp2 rp2
}.

Theorem ref_fini_clean :
  forall regs mem model (sp code : word) (wp2 rp2 wp1 rp1 : word),
  fini_pre regs mem sp code wp2 rp2 ->
  file_clean mem 0x33f90 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x29174 : word) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs mem model sp code wp2 rp2 wp1 rp1 FP F1 Hh Hlazy.
  destruct FP as [Fsp Fs0 Fra Fsplo Fsphi Fsok Ffe Ffs Ffa Fcomp Fg1 Fg2 Fdso Fglob Ferr].
  (* [comment removed for export] *)
  cps_destruct (w2 regs mem (seg_rom RSEGS) sp code (getr regs 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  (* [comment removed for export] *)
  cps_destruct Fglob as (Gnl & Gofl & Gin & Gout & Gerr & F0l & F0wp & F0wb & F0rp & F0re).
  cps_destruct Ferr as (F2l & F2wp & F2wb & F2rp & F2re).
  cps_destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  zaddr F0l; zaddr F0wp; zaddr F0wb; zaddr F0rp; zaddr F0re.
  cps_destruct (w3a regs2 (mem_w2 mem sp code (getr regs 9))
              (seg_rom RSEGS) sp code wp1 rp1 wp2 rp2)
    as (regs3 & RUN3 & R3a0 & R3a7 & R3sp); try assumption.
  1:{ unfold mem_w2; store_ok_peel; exact Fsok. }
  1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr|zaddr F0l|zaddr F0wp|zaddr F0wb|zaddr F0rp|zaddr F0re]; unfold mem_w2; rdn_solve. }
  1:{ repeat split; unfold mem_w2; zaddr_goal; rdn_solve. }
  1:{ repeat split; unfold mem_w2; zaddr_goal; rdn_solve. }
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  eapply rz_exit_at; [exact F_1f414 | exact E_1f414 | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.

Theorem ref_fini_flush :
  forall regs mem model (sp code : word) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  fini_pre regs mem sp code wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  realizes RSEGS (mkCfg (mkst regs (0x29174 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model sp code wp2 rp2 wb wp bufp bufsz rp1 can pending FP SP Hh Hlazy Hfd.
  destruct FP as [Fsp Fs0 Fra Fsplo Fsphi Fsok Ffe Ffs Ffa Fcomp Fg1 Fg2 Fdso Fglob Ferr].
  destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
  zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
  (* [comment removed for export] *)
  cps_destruct (w2 regs mem (seg_rom RSEGS) sp code (getr regs 9))
    as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
  (* [comment removed for export] *)
  cps_destruct Fglob as (Gnl & Gofl & Gin & Gout & Gerr & F0l & F0wp & F0wb & F0rp & F0re).
  cps_destruct (w3b1 regs2 (mem_w2 mem sp code (getr regs 9))
              (seg_rom RSEGS) sp code wb wp)
    as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
  1:{ unfold mem_w2; store_ok_peel; exact Fsok. }
  1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr|zaddr F0l|zaddr F0wp|zaddr F0wb|zaddr F0rp|zaddr F0re]; unfold mem_w2; rdn_solve. }
  1:{ repeat split; unfold mem_w2; zaddr_goal; rdn_solve. }
  eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0x2b620) with (0x2b620 : word) in R3ra by (apply bv_eq; reflexivity).
  unfold W. rewrite <- (app_nil_r pending).
  set (mem3 := mem_w3a (mem_w2 mem sp code (getr regs 9)) sp code).
  eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) 0x33f90 wb wp 1
            (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x2b620 : word) pending []);
    [ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
    | lia | lia
    | (* [comment removed for export] *)
      subst mem3; unfold mem_w3a, mem_w2; sok_stack Fsok
    | lia | lia
    | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a, mem_w2; zaddr_goal; rdn_solve
    | (* [comment removed for export] *) split; subst mem3; unfold mem_w3a, mem_w2; rdn_solve
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
    cps_destruct Ferr as (F2l & F2wp & F2wb & F2rp & F2re).
    zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  zaddr F0l; zaddr F0wp; zaddr F0wb; zaddr F0rp; zaddr F0re.
    cps_destruct (w3b2 regs4 mem4 (seg_rom RSEGS) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
    all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
    1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
    eapply rz_exit_at; [exact F_1f414 | exact E_1f414 | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.

Ltac fini_pre_of MW :=
  constructor;
  [ assumption | assumption | assumption | assumption | assumption
  | unfold MW; store_ok_peel; assumption
  | unfold MW; rdn_solve | unfold MW; rdn_solve | unfold MW; rdn_solve | unfold MW; rdn_solve
  | unfold MW; rdn_solve | unfold MW; rdn_solve | unfold MW; rdn_solve
  | repeat split; unfold MW; try zaddr_goal; rdn_solve
  | repeat split; unfold MW; zaddr_goal; rdn_solve ].

Ltac stdout_pending_of MW RANGE LEN PMAX BYTES :=
  constructor;
  [ unfold MW; zaddr_goal; rdn_solve | unfold MW; zaddr_goal; rdn_solve | unfold MW; zaddr_goal; rdn_solve
  | unfold MW; zaddr_goal; rdn_solve | unfold MW; zaddr_goal; rdn_solve | unfold MW; zaddr_goal; rdn_solve
  | unfold MW; zaddr_goal; rdn_solve | unfold MW; zaddr_goal; rdn_solve | unfold MW; zaddr_goal; rdn_solve
  | exact RANGE | exact LEN | exact PMAX
  | unfold MW; repeat rdn_peel1; exact BYTES
  | split; unfold MW; rdn_solve ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem ref_exit_clean :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  file_clean mem 0x33f90 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes RSEGS (mkCfg (mkst regs (0x291c0 : word) mem (seg_rom RSEGS)) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wp1 rp1 EC F1 Hh Hlazy.
  destruct EC.
  cps_destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr & F0l & F0wp & F0wb & F0rp & F0re).
  cps_destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
  cps_destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  zaddr F0l; zaddr F0wp; zaddr F0wb; zaddr F0rp; zaddr F0re.
  (* [comment removed for export] *)
  destruct ec_ax as [(Alk & Ahd) | (Alk & Asl & Ahd & Anx & Af0 & Aa0 & Acb)].
  - cps_destruct (w1e regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
      try assumption.
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
    eapply (ref_fini_clean regs1 _ model sp code wp2 rp2 wp1 rp1); [ fini_pre_of mem_w1e | | exact Hh | exact Hlazy ].
    repeat split; unfold mem_w1e; zaddr_goal; rdn_solve.
  - cps_destruct (w1o regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
      try assumption.
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
    eapply (ref_fini_clean regs1 _ model sp code wp2 rp2 wp1 rp1); [ fini_pre_of mem_w1o | | exact Hh | exact Hlazy ].
    repeat split; unfold mem_w1o; zaddr_goal; rdn_solve.
Qed.

Theorem ref_exit_flush :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  realizes RSEGS (mkCfg (mkst regs (0x291c0 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd.
  destruct EC. destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
  zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
  cps_destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr & F0l & F0wp & F0wb & F0rp & F0re).
  cps_destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  zaddr F0l; zaddr F0wp; zaddr F0wb; zaddr F0rp; zaddr F0re.
  (* [comment removed for export] *)
  destruct ec_ax as [(Alk & Ahd) | (Alk & Asl & Ahd & Anx & Af0 & Aa0 & Acb)].
  - cps_destruct (w1e regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
      try assumption.
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
    eapply (ref_fini_flush regs1 _ model sp code wp2 rp2 wb wp bufp bufsz rp1 can pending);
      [ fini_pre_of mem_w1e | stdout_pending_of mem_w1e RANGE LEN PMAX BYTES | exact Hh | exact Hlazy | exact Hfd ].
  - cps_destruct (w1o regs mem (seg_rom RSEGS) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
      try assumption.
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
    eapply (ref_fini_flush regs1 _ model sp code wp2 rp2 wb wp bufp bufsz rp1 can pending);
      [ fini_pre_of mem_w1o | stdout_pending_of mem_w1o RANGE LEN PMAX BYTES | exact Hh | exact Hlazy | exact Hfd ].
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
  realizes RSEGS (mkCfg (mkst regs (0x291c0 : word) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  (intros regs mem model code pending; cps_intros (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES)).
  destruct CASES as [(-> & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd)].
  - eapply rz_conseq; [ | apply t_emit_nil_exit ].
    eapply ref_exit_clean; eassumption.
  - eapply ref_exit_flush; eassumption.
Qed.

(* [comment removed for export] *)
Corollary ref_exit_Z : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes RSEGS (mkCfg (mkst regs (Z_to_bv 64 0x291c0) mem (seg_rom RSEGS)) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros. replace (Z_to_bv 64 0x291c0) with (0x291c0 : word) by (apply bv_eq; reflexivity).
  apply ref_exit; assumption.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
