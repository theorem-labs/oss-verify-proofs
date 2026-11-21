(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.World Require Import Tgt_checksum_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic U0ExitBase.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require LiaFast.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes Spec LibWritev U0StdioDefs U0StdioWrite.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import PropExec U0_code_13bc4_14000 U0_code_14000_15000 U0_code_15000_16000 U0_code_16000_17000 U0_code_17000_18000 U0_code_18000_19000 U0_code_1c000_1d000 U0_code_1d000_1d8c4.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.

Module S0Exit_run1.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.StepTac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Hoare OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.WalkTac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.StreamSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.MmapSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.LibAtomic OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.U0ExitBase.
Import OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.LiaFast.
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

Definition mem_w1 (mem : word -> option byte) (sp ra s0 : word) (tid : Z) :=
  wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 0x4ffe8) (word_to_le_bytes 4 (Z_to_bv 64 tid)).

Definition mem_foe (mem : word -> option byte) (sp code s1v s2v s3v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x15e6c)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3v).

Definition mem_w1U (mem : word -> option byte) (sp ra s0 : word) (tid : Z) (code s1v s2v s3v : word) :=
  wbytes (mem_foe (mem_w1 mem sp ra s0 tid) sp code s1v s2v s3v)
    (Z_to_bv 64 0x4fdc8) [Z_to_bv 8 1].

Definition mem_w1R (mem : word -> option byte) (sp ra s0 : word) (tid : Z) (code s1v s2v s3v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (mem_foe (mem_w1 mem sp ra s0 tid) sp code s1v s2v s3v)
    (Z_to_bv 64 0x4fdd0) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x4fdd0) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x4fdd0) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x4fdd8) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x4fdc8) [Z_to_bv 8 1].

Lemma w1U {RCa1 : RunCtx}  : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x4ffe8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x50013) 1%nat = Some [Z_to_bv 8 0] ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x4fdd8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x4fdcc) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x15e08 : word) mem rom)
                 (mkst regs' (0x15dbc : word) (mem_w1U mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x15e70
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Mhead Malk.
  unfold mem_w1U, mem_foe, mem_w1. eexists. split.
  -
    stepn F_15d68 D_15d68. rewrite Hsp. sp_renorm.
    stepST F_15d6c D_15d6c (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_15d70 D_15d70 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    stepn F_15d74 D_15d74.
    stepn F_15d78 D_15d78. rewrite Htp.
    stepLD F_15d7c D_15d7c (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    stepn F_15d80 D_15d80.
    stepn F_15d84 D_15d84.
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_15d88 | reflexivity | exact D_15d88
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_15d8c | reflexivity | exact D_15d8c | gres; cond_compute ] | ].
    norm_pc_r.
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_15d90 | reflexivity | exact D_15d90
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    stepb_ft F_15d94 D_15d94 ltac:(cond_compute).
    stepn F_15d98 D_15d98.
    stepb_ft F_15d9c D_15d9c ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    stepb_tk F_15da0 D_15da0 ltac:(cond_compute).
    stepn F_15dc4 D_15dc4. rewrite Ha0.
    stepn F_15dc8 D_15dc8.
    stepn F_15b84 D_15b84. sp_renorm.
    stepST F_15b88 D_15b88 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x15e6c) ltac:(sok_stack SOK).
    stepST F_15b8c D_15b8c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_15b90 D_15b90 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_15b94 D_15b94 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_15b98 D_15b98 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    stepn F_15b9c D_15b9c. stepn F_15ba0 D_15ba0. stepn F_15ba4 D_15ba4. stepn F_15ba8 D_15ba8. stepn F_15bac D_15bac.
    stepn F_1d4f4 D_1d4f4.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_1d4f8 | reflexivity | exact D_1d4f8 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_1d4fc D_1d4fc ltac:(cond_compute).
    stepret F_1d6ec D_1d6ec (0x15c50 : word) ltac:(bveq).
    stepLD8 F_15bb0 D_15bb0 (Z_to_bv 64 0).
    stepb_tk F_15bb4 D_15bb4 ltac:(cond_compute).
    stepn F_15c24 D_15c24.
    stepST F_15c28 D_15c28 (Z_to_bv 64 0x4fdc8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_15c2c D_15c2c.
    stepLD8 F_15c30 D_15c30 (Z_to_bv 64 0x15e6c).
    stepLD8 F_15c34 D_15c34 code.
    stepLD8 F_15c38 D_15c38 (getr regs 9).
    stepLD8 F_15c3c D_15c3c (getr regs 18).
    stepLD8 F_15c40 D_15c40 (getr regs 19).
    stepn F_15c44 D_15c44. sp_renorm.
    stepn F_15c48 D_15c48.
    stepLD F_1d77c D_1d77c (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepb_ft F_1d780 D_1d780 ltac:(cond_compute).
    stepret F_1d784 D_1d784 (0x15e6c : word) ltac:(bveq).
    stepn F_15dcc D_15dcc.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.

Lemma w1R {RCa1 : RunCtx}  : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x4ffe8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x50013) 1%nat = Some [Z_to_bv 8 0] ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x4fdd8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x4fde0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x4fdd0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x4fdcc) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x4fde0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x4fde8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x15db4)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x4fee8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x14198)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x2fc84) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x15e08 : word) mem rom)
                 (mkst regs' (0x15dbc : word) (mem_w1R mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x15e70
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Mhead Mslot Malk Mnext Mf0 Ma0 Mincb.
  unfold mem_w1R, mem_foe, mem_w1. eexists. split.
  -
    stepn F_15d68 D_15d68. rewrite Hsp. sp_renorm.
    stepST F_15d6c D_15d6c (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_15d70 D_15d70 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    stepn F_15d74 D_15d74.
    stepn F_15d78 D_15d78. rewrite Htp.
    stepLD F_15d7c D_15d7c (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    stepn F_15d80 D_15d80.
    stepn F_15d84 D_15d84.
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_15d88 | reflexivity | exact D_15d88
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_15d8c | reflexivity | exact D_15d8c | gres; cond_compute ] | ].
    norm_pc_r.
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_15d90 | reflexivity | exact D_15d90
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    stepb_ft F_15d94 D_15d94 ltac:(cond_compute).
    stepn F_15d98 D_15d98.
    stepb_ft F_15d9c D_15d9c ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    stepb_tk F_15da0 D_15da0 ltac:(cond_compute).
    stepn F_15dc4 D_15dc4. rewrite Ha0.
    stepn F_15dc8 D_15dc8.
    stepn F_15b84 D_15b84. sp_renorm.
    stepST F_15b88 D_15b88 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x15e6c) ltac:(sok_stack SOK).
    stepST F_15b8c D_15b8c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_15b90 D_15b90 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_15b94 D_15b94 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_15b98 D_15b98 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    stepn F_15b9c D_15b9c. stepn F_15ba0 D_15ba0. stepn F_15ba4 D_15ba4. stepn F_15ba8 D_15ba8. stepn F_15bac D_15bac.
    stepn F_1d4f4 D_1d4f4.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_1d4f8 | reflexivity | exact D_1d4f8 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_1d4fc D_1d4fc ltac:(cond_compute).
    stepret F_1d6ec D_1d6ec (0x15c50 : word) ltac:(bveq).
    stepLD8 F_15bb0 D_15bb0 (Z_to_bv 64 0x4fde0).
    stepb_ft F_15bb4 D_15bb4 ltac:(cond_compute).
    stepLD F_15bb8 D_15bb8 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 1) by lia.
    stepn F_15bbc D_15bbc.
    stepn F_15bd4 D_15bd4.
    stepST F_15bd8 D_15bd8 (Z_to_bv 64 0x4fdd0) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_15bdc D_15bdc ltac:(cond_compute).
    stepLD8 F_15be0 D_15be0 (Z_to_bv 64 0x4fde0).
    stepn F_15be4 D_15be4. stepn F_15be8 D_15be8.
    stepLD8 F_15bec D_15bec (Z_to_bv 64 0x15db4).
    stepLD8 F_15bf0 D_15bf0 (Z_to_bv 64 0x14198).
    stepn F_15bf4 D_15bf4. stepn F_15bf8 D_15bf8.
    stepLD F_1d77c D_1d77c (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepb_ft F_1d780 D_1d780 ltac:(cond_compute).
    stepret F_1d784 D_1d784 (0x15c9c : word) ltac:(bveq).
    stepn F_15bfc D_15bfc.
    stepjr F_15c00 D_15c00 (Z_to_bv 64 0x15db4) ltac:(gres; reflexivity). vnorm.
    stepjr F_15d14 D_15d14 (Z_to_bv 64 0x14198) ltac:(gres; reflexivity). vnorm.
    stepn F_14138 D_14138.
    stepLBU F_1413c D_1413c (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_14140 D_14140 ltac:(cond_compute).
    stepret F_14144 D_14144 (0x15ca4 : word) ltac:(bveq).
    stepn F_15c04 D_15c04. stepn F_15c08 D_15c08.
    stepn F_1d4f4 D_1d4f4.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_1d4f8 | reflexivity | exact D_1d4f8 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_1d4fc D_1d4fc ltac:(cond_compute).
    stepret F_1d6ec D_1d6ec (0x15cac : word) ltac:(bveq).
    stepLD F_15c0c D_15c0c (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; apply rdn_wbytes_hit4; u_norm; lia) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepn F_15c10 D_15c10.
    stepST F_15c14 D_15c14 (Z_to_bv 64 0x4fdd0) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_15c18 D_15c18 ltac:(cond_compute).
    stepLD8 F_15c1c D_15c1c (Z_to_bv 64 0x4fde0).
    stepn F_15c20 D_15c20.
    stepLD8 F_15bc0 D_15bc0 (Z_to_bv 64 0).
    stepn F_15bc4 D_15bc4.
    stepST F_15bc8 D_15bc8 (Z_to_bv 64 0x4fdd0) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_15bcc D_15bcc (Z_to_bv 64 0x4fdd8) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_15bd0 D_15bd0 ltac:(cond_compute).
    stepn F_15c24 D_15c24.
    stepST F_15c28 D_15c28 (Z_to_bv 64 0x4fdc8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_15c2c D_15c2c.
    stepLD8 F_15c30 D_15c30 (Z_to_bv 64 0x15e6c).
    stepLD8 F_15c34 D_15c34 code.
    stepLD8 F_15c38 D_15c38 (getr regs 9).
    stepLD8 F_15c3c D_15c3c (getr regs 18).
    stepLD8 F_15c40 D_15c40 (getr regs 19).
    stepn F_15c44 D_15c44. sp_renorm.
    stepn F_15c48 D_15c48.
    stepLD F_1d77c D_1d77c (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepb_ft F_1d780 D_1d780 ltac:(cond_compute).
    stepret F_1d784 D_1d784 (0x15e6c : word) ltac:(bveq).
    stepn F_15dcc D_15dcc.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.

Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x15e70)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x15dec)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x1e970)))
    (Z_to_bv 64 0x1fc78) [Z_to_bv 8 1].

Lemma w2 {RCa1 : RunCtx}  : forall regs mem rom (sp code s1v dso : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x15e70 -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x1ea10) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1e978)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x1ea18) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1e970)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x1e970) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13ce0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x1fc78) 1%nat = Some [Z_to_bv 8 0] ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x1e9b8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x15cec)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x1fa20) 8%nat = Some (word_to_le_bytes 8 dso) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x1e9c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x15dbc : word) mem rom)
                 (mkst regs' (0x18180 : word) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x15e74
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
  intros regs mem rom sp code s1v dso Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mdso Mg2.
  unfold mem_w2. eexists. split.
  -
    stepn F_15d1c D_15d1c. rewrite Hsp. sp_renorm.
    stepST F_15d20 D_15d20 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x15e70) ltac:(sok_stack SOK).
    stepST F_15d24 D_15d24 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_15d28 D_15d28 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    stepn F_15d2c D_15d2c.
    stepn F_15d30 D_15d30.
    stepLD8 F_15d34 D_15d34 (Z_to_bv 64 0x1e978).
    stepLD8 F_15d38 D_15d38 (Z_to_bv 64 0x1e970).
    stepb_ft F_15d3c D_15d3c ltac:(cond_compute).
    stepLD8 F_15d40 D_15d40 (Z_to_bv 64 0x13ce0).
    stepn F_15d44 D_15d44.
    stepjr F_15d48 D_15d48 (Z_to_bv 64 0x13ce0) ltac:(gres; reflexivity). vnorm.
    stepn F_13c80 D_13c80. sp_renorm.
    stepST F_13c84 D_13c84 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x15dec) ltac:(sok_stack SOK).
    stepST F_13c88 D_13c88 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x1e970) ltac:(sok_stack SOK).
    stepn F_13c8c D_13c8c.
    stepn F_13c90 D_13c90.
    stepn F_13c94 D_13c94.
    stepLBU F_13c98 D_13c98 (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
    stepn F_13c9c D_13c9c.
    stepb_tk F_13ca0 D_13ca0 ltac:(cond_compute).
    stepn F_13cac D_13cac.
    stepn F_13cb0 D_13cb0.
    stepn F_13cb4 D_13cb4.
    stepST F_13cb8 D_13cb8 (Z_to_bv 64 0x1fc78) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_13cbc D_13cbc.
    stepLD8 F_13cc0 D_13cc0 (Z_to_bv 64 0x15cec).
    stepb_ft F_13cc4 D_13cc4 ltac:(cond_compute).
    stepn F_13cc8 D_13cc8.
    stepn F_13ccc D_13ccc. stepn F_13cd0 D_13cd0.
    stepLD8 F_13cd4 D_13cd4 dso.
    stepn F_13cd8 D_13cd8.
    stepret F_15c4c D_15c4c (0x13d3c : word) ltac:(bveq).
    stepn F_13cdc D_13cdc.
    stepn F_13ce0 D_13ce0.
    stepLD8 F_13ce4 D_13ce4 (Z_to_bv 64 0).
    stepb_tk F_13ce8 D_13ce8 ltac:(cond_compute).
    stepLD8 F_13d00 D_13d00 (Z_to_bv 64 0x15dec).
    stepLD8 F_13d04 D_13d04 (Z_to_bv 64 0x1e970).
    stepn F_13d08 D_13d08. sp_renorm.
    stepret F_13d0c D_13d0c (0x15dec : word) ltac:(bveq).
    stepn F_15d4c D_15d4c.
    stepb_ft F_15d50 D_15d50 ltac:(cond_compute).
    stepLD8 F_15d54 D_15d54 (Z_to_bv 64 0x15e70).
    stepLD8 F_15d58 D_15d58 code.
    stepLD8 F_15d5c D_15d5c s1v.
    stepn F_15d60 D_15d60. sp_renorm.
    stepn F_15d64 D_15d64.
    stepret F_15d18 D_15d18 (0x15e70 : word) ltac:(bveq).
    stepn F_15dd0 D_15dd0.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S0Exit_run1.

Module S0Exit_run2.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.StepTac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Hoare OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.WalkTac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.StreamSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.MmapSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.LibAtomic OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.U0ExitBase.
Import OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.LiaFast.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition mem_w3a (mem : word -> option byte) (sp code : word) :=
  wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x15e74)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x18190)))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

Lemma w3a {RCa1 : RunCtx}  : forall regs mem rom (sp code wp1 rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x15e74 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  file_clean mem 0x1fb38 wp1 rp1 ->
  file_clean mem 0x1fa48 wp2 rp2 ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x18180 : word) mem rom)
                 (mkst regs' (0x15c10 : word) (mem_w3a mem sp code) rom)
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
  -
    stepn F_180e0 D_180e0. rewrite Hsp. sp_renorm.
    stepST F_180e4 D_180e4 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x15e74) ltac:(sok_stack SOK).
    stepST F_180e8 D_180e8 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepn F_180ec D_180ec.
    stepn F_18284 D_18284. sp_renorm.
    stepST F_18288 D_18288 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x18190) ltac:(sok_stack SOK).
    stepST F_1828c D_1828c (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_18290 D_18290.
    stepn F_18294 D_18294.
    stepn F_18298 D_18298.
    stepn F_1829c D_1829c.
    stepn F_1d4f4 D_1d4f4.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_1d4f8 | reflexivity | exact D_1d4f8 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_1d4fc D_1d4fc ltac:(cond_compute).
    stepret F_1d6ec D_1d6ec (0x18340 : word) ltac:(bveq).
    stepn F_182a0 D_182a0.
    stepLD8 F_182a4 D_182a4 (Z_to_bv 64 0x18190).
    stepLD8 F_182a8 D_182a8 code.
    stepn F_182ac D_182ac. sp_renorm.
    stepret F_182b0 D_182b0 (0x18190 : word) ltac:(bveq).
    stepLD8 F_180f0 D_180f0 (Z_to_bv 64 0).
    stepb_ft F_180f4 D_180f4 ltac:(cond_compute).
    stepn F_180f8 D_180f8.
    stepLD8 F_180fc D_180fc (Z_to_bv 64 0).
    stepb_tk F_18100 D_18100 ltac:(cond_compute).
    stepn F_18154 D_18154.
    stepLD8 F_18158 D_18158 (Z_to_bv 64 0x1fb38).
    stepb_ft F_1815c D_1815c ltac:(cond_compute).
    stepLD F_18160 D_18160 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_18164 D_18164 ltac:(cond_compute).
    stepLD8 F_18170 D_18170 wp1.
    stepLD8 F_18174 D_18174 wp1.
    stepb_tk F_18178 D_18178 ltac:(apply c_eq_refl).
    stepLD8 F_18190 D_18190 rp1.
    stepLD8 F_18194 D_18194 rp1.
    stepb_tk F_18198 D_18198 ltac:(apply c_eq_refl).
    stepn F_181b0 D_181b0.
    stepLD8 F_181b4 D_181b4 (Z_to_bv 64 0x1fa48).
    stepb_ft F_181b8 D_181b8 ltac:(cond_compute).
    stepLD F_181bc D_181bc (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_181c0 D_181c0 ltac:(cond_compute).
    stepLD8 F_181cc D_181cc wp2.
    stepLD8 F_181d0 D_181d0 wp2.
    stepb_tk F_181d4 D_181d4 ltac:(apply c_eq_refl).
    stepLD8 F_181ec D_181ec rp2.
    stepLD8 F_181f0 D_181f0 rp2.
    stepb_tk F_181f4 D_181f4 ltac:(apply c_eq_refl).
    stepLD8 F_18274 D_18274 (Z_to_bv 64 0x15e74).
    stepLD8 F_18278 D_18278 code.
    stepn F_1827c D_1827c. sp_renorm.
    stepret F_18280 D_18280 (0x15e74 : word) ltac:(bveq).
    stepn F_15dd4 D_15dd4.
    stepn F_15dd8 D_15dd8.
    stepn F_15b68 D_15b68.
    stepn F_15b6c D_15b6c.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S0Exit_run2.

Module S0Exit_run3.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.StepTac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Hoare OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.WalkTac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.StreamSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.MmapSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.LibAtomic OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.U0ExitBase S0Exit_run2.
Import OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.LiaFast.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition stdout_dirty_hdr {RCa1 : RunCtx}  (mem : word -> option byte) (wb wp : Z) : Prop :=
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x1fb38 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x1fb38 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
  /\ rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x1fb38 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
  /\ rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x1fb38 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x18390)).

Lemma w3b1 {RCa1 : RunCtx}  : forall regs mem rom (sp code : word) (wb wp : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x15e74 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  stdout_dirty_hdr mem wb wp ->
  (0 <= wb < 2^64)%Z -> (0 <= wp < 2^64)%Z -> wb <> wp ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x18180 : word) mem rom)
                 (mkst regs' (0x18390 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = Z_to_bv 64 0x1fb38
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 1 = Z_to_bv 64 0x18230
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32)
    /\ getr regs' 8 = Z_to_bv 64 0x1fb38
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof.
  intros regs mem rom sp code wb wp Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr) (F1l & F1wp & F1wb & F1wr) WB WP NE.
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
  unfold mem_w3a. eexists. split.
  -
    stepn F_180e0 D_180e0. rewrite Hsp. sp_renorm.
    stepST F_180e4 D_180e4 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x15e74) ltac:(sok_stack SOK).
    stepST F_180e8 D_180e8 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepn F_180ec D_180ec.
    stepn F_18284 D_18284. sp_renorm.
    stepST F_18288 D_18288 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x18190) ltac:(sok_stack SOK).
    stepST F_1828c D_1828c (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_18290 D_18290.
    stepn F_18294 D_18294.
    stepn F_18298 D_18298.
    stepn F_1829c D_1829c.
    stepn F_1d4f4 D_1d4f4.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_1d4f8 | reflexivity | exact D_1d4f8 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_1d4fc D_1d4fc ltac:(cond_compute).
    stepret F_1d6ec D_1d6ec (0x18340 : word) ltac:(bveq).
    stepn F_182a0 D_182a0.
    stepLD8 F_182a4 D_182a4 (Z_to_bv 64 0x18190).
    stepLD8 F_182a8 D_182a8 code.
    stepn F_182ac D_182ac. sp_renorm.
    stepret F_182b0 D_182b0 (0x18190 : word) ltac:(bveq).
    stepLD8 F_180f0 D_180f0 (Z_to_bv 64 0).
    stepb_ft F_180f4 D_180f4 ltac:(cond_compute).
    stepn F_180f8 D_180f8.
    stepLD8 F_180fc D_180fc (Z_to_bv 64 0).
    stepb_tk F_18100 D_18100 ltac:(cond_compute).
    stepn F_18154 D_18154.
    stepLD8 F_18158 D_18158 (Z_to_bv 64 0x1fb38).
    stepb_ft F_1815c D_1815c ltac:(cond_compute).
    stepLD F_18160 D_18160 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_18164 D_18164 ltac:(cond_compute).
    stepLD8 F_18170 D_18170 (Z_to_bv 64 wp).
    stepLD8 F_18174 D_18174 (Z_to_bv 64 wb).
    stepb_ft F_18178 D_18178 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    stepLD8 F_1817c D_1817c (Z_to_bv 64 0x18390).
    stepn F_18180 D_18180.
    stepn F_18184 D_18184.
    stepn F_18188 D_18188.
    stepjr F_1818c D_1818c (Z_to_bv 64 0x18390) ltac:(gres; reflexivity). vnorm.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Lemma w3b2 {RCa1 : RunCtx}  : forall regs mem rom (sp code rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 32) -> getr regs 8 = Z_to_bv 64 0x1fb38 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x15e74)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 code) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x1fb38 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x1fb38 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x1fb30) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1fa48)) ->
  file_clean mem 0x1fa48 wp2 rp2 ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x18230 : word) mem rom)
                 (mkst regs' (0x15c10 : word) mem rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr
         (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  eexists. split.
  -
    stepLD8 F_18190 D_18190 rp1.
    stepLD8 F_18194 D_18194 rp1.
    stepb_tk F_18198 D_18198 ltac:(apply c_eq_refl).
    stepn F_181b0 D_181b0.
    stepLD8 F_181b4 D_181b4 (Z_to_bv 64 0x1fa48).
    stepb_ft F_181b8 D_181b8 ltac:(cond_compute).
    stepLD F_181bc D_181bc (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_181c0 D_181c0 ltac:(cond_compute).
    stepLD8 F_181cc D_181cc wp2.
    stepLD8 F_181d0 D_181d0 wp2.
    stepb_tk F_181d4 D_181d4 ltac:(apply c_eq_refl).
    stepLD8 F_181ec D_181ec rp2.
    stepLD8 F_181f0 D_181f0 rp2.
    stepb_tk F_181f4 D_181f4 ltac:(apply c_eq_refl).
    stepLD8 F_18274 D_18274 (Z_to_bv 64 0x15e74).
    stepLD8 F_18278 D_18278 code.
    stepn F_1827c D_1827c. rewrite Hsp. sp_renorm.
    stepret F_18280 D_18280 (0x15e74 : word) ltac:(bveq).
    stepn F_15dd4 D_15dd4.
    stepn F_15dd8 D_15dd8.
    stepn F_15b68 D_15b68.
    stepn F_15b6c D_15b6c.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S0Exit_run3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.PropExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.CatExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.CatSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.StepTac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Hoare OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.WalkTac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.StreamSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.MmapSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.LibAtomic OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.ExitSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.ShapeAlg OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Nodes OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.Spec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.LibWritev OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.U0StdioDefs S0Exit_run1 S0Exit_run2 S0Exit_run3 OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.U0StdioWrite.S0StdioWrite_run1 OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.U0StdioWrite.S0StdioWrite_run2 OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.U0StdioWrite.
Import OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.LiaFast.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac zaddr_rec H := zaddr H.


Theorem ref_exit_clean {RCa1 : RunCtx}  :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  file_clean mem 0x1fb38 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs (0x15e08 : word) mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
           (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wp1 rp1 EC F1 Hh Hlazy.
  destruct EC. destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr). destruct ec_dso as [dso Mdso].
  destruct ec_atx as [(Ahead & Alock) | (Ahead & Aslot & Alock & Anext & Af0 & Aa0 & Aincb)].
  -
    destruct (w1U regs mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
      try assumption.
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
    destruct (w2 regs1 (mem_w1U mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp code (getr regs1 9) dso)
      as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
    all: try (unfold mem_w1U, mem_foe, mem_w1; first [store_ok_peel; exact ec_sok | rdn_solve]).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
    destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
    destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
    zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
    zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
    destruct (w3a regs2 (mem_w2 (mem_w1U mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9))
                (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp code wp1 rp1 wp2 rp2)
      as (regs3 & RUN3 & R3a0 & R3a7 & R3sp); try assumption.
    1:{ unfold mem_w2, mem_w1U, mem_foe, mem_w1; store_ok_peel; exact ec_sok. }
    1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2, mem_w1U, mem_foe, mem_w1; rdn_solve. }
    1:{ repeat split; unfold mem_w2, mem_w1U, mem_foe, mem_w1; zaddr_goal; rdn_solve. }
    1:{ repeat split; unfold mem_w2, mem_w1U, mem_foe, mem_w1; zaddr_goal; rdn_solve. }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
    eapply rz_exit_at; [exact F_15b70 | exact E_15b70 | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
  -
    destruct (w1R regs mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
      try assumption.
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
    destruct (w2 regs1 (mem_w1R mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp code (getr regs1 9) dso)
      as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
    all: try (unfold mem_w1R, mem_foe, mem_w1; first [store_ok_peel; exact ec_sok | rdn_solve]).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
    destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
    destruct F1 as (F1l & F1wp & F1wb & F1rp & F1re).
    zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1rp; zaddr F1re.
    zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
    destruct (w3a regs2 (mem_w2 (mem_w1R mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9))
                (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp code wp1 rp1 wp2 rp2)
      as (regs3 & RUN3 & R3a0 & R3a7 & R3sp); try assumption.
    1:{ unfold mem_w2, mem_w1R, mem_foe, mem_w1; store_ok_peel; exact ec_sok. }
    1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2, mem_w1R, mem_foe, mem_w1; rdn_solve. }
    1:{ repeat split; unfold mem_w2, mem_w1R, mem_foe, mem_w1; zaddr_goal; rdn_solve. }
    1:{ repeat split; unfold mem_w2, mem_w1R, mem_foe, mem_w1; zaddr_goal; rdn_solve. }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
    eapply rz_exit_at; [exact F_15b70 | exact E_15b70 | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.


Theorem ref_exit_flush {RCa1 : RunCtx}  :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  m_channel_reader model = true ->
  realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs (0x15e08 : word) mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model sp tp code tid wp2 rp2 wb wp bufp bufsz rp1 can pending EC SP Hh Hlazy Hfd Hrdr.
  destruct EC. destruct ec_glob as (Gnl & Gofl & Gin & Gout & Gerr). destruct ec_dso as [dso Mdso].
  destruct SP as [P1l P1wp P1wb P1wr P1buf P1bsz P1fd P1rp P1re RANGE LEN PMAX BYTES [Ggot Gcan]].
  zaddr P1l; zaddr P1wp; zaddr P1wb; zaddr P1wr; zaddr P1buf; zaddr P1bsz; zaddr P1fd; zaddr P1rp; zaddr P1re.
  destruct ec_atx as [(Ahead & Alock) | (Ahead & Aslot & Alock & Anext & Af0 & Aa0 & Aincb)].
  -
    destruct (w1U regs mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
      try assumption.
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
    destruct (w2 regs1 (mem_w1U mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp code (getr regs1 9) dso)
      as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
    all: try (unfold mem_w1U, mem_foe, mem_w1; first [store_ok_peel; exact ec_sok | rdn_solve]).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
    destruct (w3b1 regs2 (mem_w2 (mem_w1U mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9))
                (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp code wb wp)
      as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
    1:{ unfold mem_w2, mem_w1U, mem_foe, mem_w1; store_ok_peel; exact ec_sok. }
    1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2, mem_w1U, mem_foe, mem_w1; rdn_solve. }
    1:{ repeat split; unfold mem_w2, mem_w1U, mem_foe, mem_w1; zaddr_goal; rdn_solve. }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
    replace (Z_to_bv 64 0x18230) with (0x18230 : word) in R3ra by (apply bv_eq; reflexivity).
    unfold W. rewrite <- (app_nil_r pending).
    set (mem3 := mem_w3a (mem_w2 (mem_w1U mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9)) sp code).
    eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) 0x1fb38 wb wp 1
              (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x18230 : word) pending []);
      [ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
      | lia | lia
      |
        subst mem3; unfold mem_w3a, mem_w2, mem_w1U, mem_foe, mem_w1; sok_stack ec_sok
      | lia | lia
      | split; subst mem3; unfold mem_w3a, mem_w2, mem_w1U, mem_foe, mem_w1; zaddr_goal; rdn_solve
      | split; subst mem3; unfold mem_w3a, mem_w2, mem_w1U, mem_foe, mem_w1; rdn_solve
      | lia | exact Hfd | exact Hrdr | exact Hh | exact Hlazy
      | lia | lia | exact LEN
      | cbn [length]; u_norm; reflexivity
      | cbn [length]; lia
      | lia | u_norm; lia | u_norm; lia
      | unfold TASK_SIZE; lia | unfold TASK_SIZE; u_norm; lia
      | subst mem3; unfold mem_w3a, mem_w2, mem_w1U, mem_foe, mem_w1; repeat rdn_peel1; exact BYTES
      | reflexivity
      | apply ret_ok_even; reflexivity
      | apply t_emit_has_nil
      | ].
    intros regs4 mem4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
      rewrite R3s0 in Q8.
      destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
      zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
      destruct (w3b2 regs4 mem4 (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
      all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1U, mem_foe, mem_w1; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
      1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1U, mem_foe, mem_w1; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
      eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
      eapply rz_exit_at; [exact F_15b70 | exact E_15b70 | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
  -
    destruct (w1R regs mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1);
      try assumption.
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
    destruct (w2 regs1 (mem_w1R mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp code (getr regs1 9) dso)
      as (regs2 & RUN2 & R2sp & R2s0 & R2ra & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
    all: try (unfold mem_w1R, mem_foe, mem_w1; first [store_ok_peel; exact ec_sok | rdn_solve]).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
    destruct (w3b1 regs2 (mem_w2 (mem_w1R mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9))
                (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp code wb wp)
      as (regs3 & RUN3 & R3a0 & R3a1 & R3a2 & R3ra & R3sp & R3s0 & R3gp & R3tp); try assumption; try lia.
    1:{ unfold mem_w2, mem_w1R, mem_foe, mem_w1; store_ok_peel; exact ec_sok. }
    1:{ repeat split; [zaddr Gnl|zaddr Gofl|zaddr Gin|zaddr Gout|zaddr Gerr]; unfold mem_w2, mem_w1R, mem_foe, mem_w1; rdn_solve. }
    1:{ repeat split; unfold mem_w2, mem_w1R, mem_foe, mem_w1; zaddr_goal; rdn_solve. }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN3 |]. clear RUN3.
    replace (Z_to_bv 64 0x18230) with (0x18230 : word) in R3ra by (apply bv_eq; reflexivity).
    unfold W. rewrite <- (app_nil_r pending).
    set (mem3 := mem_w3a (mem_w2 (mem_w1R mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9)) sp code).
    eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) 0x1fb38 wb wp 1
              (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x18230 : word) pending []);
      [ exact R3sp | exact R3a0 | exact R3a1 | exact R3a2 | exact R3ra
      | lia | lia
      |
        subst mem3; unfold mem_w3a, mem_w2, mem_w1R, mem_foe, mem_w1; sok_stack ec_sok
      | lia | lia
      | split; subst mem3; unfold mem_w3a, mem_w2, mem_w1R, mem_foe, mem_w1; zaddr_goal; rdn_solve
      | split; subst mem3; unfold mem_w3a, mem_w2, mem_w1R, mem_foe, mem_w1; rdn_solve
      | lia | exact Hfd | exact Hrdr | exact Hh | exact Hlazy
      | lia | lia | exact LEN
      | cbn [length]; u_norm; reflexivity
      | cbn [length]; lia
      | lia | u_norm; lia | u_norm; lia
      | unfold TASK_SIZE; lia | unfold TASK_SIZE; u_norm; lia
      | subst mem3; unfold mem_w3a, mem_w2, mem_w1R, mem_foe, mem_w1; repeat rdn_peel1; exact BYTES
      | reflexivity
      | apply ret_ok_even; reflexivity
      | apply t_emit_has_nil
      | ].
    intros regs4 mem4 Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
      rewrite R3s0 in Q8.
      destruct ec_err as (F2l & F2wp & F2wb & F2rp & F2re).
      zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
      destruct (w3b2 regs4 mem4 (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb)) sp code rp1 wp2 rp2) as (regs5 & RUN5 & R5a0 & R5a7 & R5sp); try assumption.
      all: try (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1R, mem_foe, mem_w1; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]).
      1:{ repeat split; (eapply (sw_post_rdn _ _ _ _ _ _ _ _ _ POST); [subst mem3; unfold mem_w3a, mem_w2, mem_w1R, mem_foe, mem_w1; zaddr_goal; rdn_solve | zsimp; lia | zsimp; lia | zsimp; lia | zsimp; lia]). }
      eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN5 |]. clear RUN5.
      eapply rz_exit_at; [exact F_15b70 | exact E_15b70 | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.


Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
  intros code fs. apply t_eq_sym. apply t_emit_nil_eq.
  unfold t_exit, t_emit. left. apply is_prefix_nil.
Qed.

Theorem ref_exit {RCa1 : RunCtx}  : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs (0x15e08 : word) mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros regs mem model code pending (sp & tp & tid & wp2 & rp2 & EC & Hh & Hlazy & CASES).
  destruct CASES as [(-> & wp1 & rp1 & F1) | (wb & wp & bufp & bufsz & rp1 & can & SP & Hfd & Hrdr)].
  - eapply rz_conseq; [ | apply t_emit_nil_exit ].
    eapply ref_exit_clean; eassumption.
  - eapply ref_exit_flush; eassumption.
Qed.

Corollary ref_exit_Z {RCa1 : RunCtx}  : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs (Z_to_bv 64 0x15e08) mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros. replace (Z_to_bv 64 0x15e08) with (0x15e08 : word) by (apply bv_eq; reflexivity).
  apply ref_exit; assumption.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
