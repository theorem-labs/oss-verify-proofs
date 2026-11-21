(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic S0ExitBase.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require LiaFast.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes Spec LibWritev S0StdioDefs S0StdioWrite.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import PropExec S0_code_13ba4_14000 S0_code_14000_15000 S0_code_15000_16000 S0_code_17000_18000 S0_code_18000_19000 S0_code_1d000_1d640.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.

Module S0Exit_run1.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.StepTac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Hoare OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.WalkTac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.StreamSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.MmapSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.LibAtomic OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.S0ExitBase.
Import OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.LiaFast.
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
    (Z_to_bv 64 0x4fd68) (word_to_le_bytes 4 (Z_to_bv 64 tid)).

Definition mem_foe (mem : word -> option byte) (sp code s1v s2v s3v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x15be8)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3v).

Definition mem_w1U (mem : word -> option byte) (sp ra s0 : word) (tid : Z) (code s1v s2v s3v : word) :=
  wbytes (mem_foe (mem_w1 mem sp ra s0 tid) sp code s1v s2v s3v)
    (Z_to_bv 64 0x4fb48) [Z_to_bv 8 1].

Definition mem_w1R (mem : word -> option byte) (sp ra s0 : word) (tid : Z) (code s1v s2v s3v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (mem_foe (mem_w1 mem sp ra s0 tid) sp code s1v s2v s3v)
    (Z_to_bv 64 0x4fb50) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x4fb50) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x4fb50) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x4fb58) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x4fb48) [Z_to_bv 8 1].

Lemma w1U {RCa1 : RunCtx}  : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x4fd68) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x4fd93) 1%nat = Some [Z_to_bv 8 0] ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x4fb58) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x4fb4c) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x15b84 : word) mem rom)
                 (mkst regs' (0x15b38 : word) (mem_w1U mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x15bec
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Mhead Malk.
  unfold mem_w1U, mem_foe, mem_w1. eexists. split.
  -
    stepn F_15ae4 D_15ae4. rewrite Hsp. sp_renorm.
    stepST F_15ae8 D_15ae8 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_15aec D_15aec (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    stepn F_15af0 D_15af0.
    stepn F_15af4 D_15af4. rewrite Htp.
    stepLD F_15af8 D_15af8 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    stepn F_15afc D_15afc.
    stepn F_15b00 D_15b00.
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_15b04 | reflexivity | exact D_15b04
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_15b08 | reflexivity | exact D_15b08 | gres; cond_compute ] | ].
    norm_pc_r.
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_15b0c | reflexivity | exact D_15b0c
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    stepb_ft F_15b10 D_15b10 ltac:(cond_compute).
    stepn F_15b14 D_15b14.
    stepb_ft F_15b18 D_15b18 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    stepb_tk F_15b1c D_15b1c ltac:(cond_compute).
    stepn F_15b40 D_15b40. rewrite Ha0.
    stepn F_15b44 D_15b44.
    stepn F_15900 D_15900. sp_renorm.
    stepST F_15904 D_15904 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x15be8) ltac:(sok_stack SOK).
    stepST F_15908 D_15908 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_1590c D_1590c (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_15910 D_15910 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_15914 D_15914 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    stepn F_15918 D_15918. stepn F_1591c D_1591c. stepn F_15920 D_15920. stepn F_15924 D_15924. stepn F_15928 D_15928.
    stepn F_1d270 D_1d270.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_1d274 | reflexivity | exact D_1d274 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_1d278 D_1d278 ltac:(cond_compute).
    stepret F_1d468 D_1d468 (0x159cc : word) ltac:(bveq).
    stepLD8 F_1592c D_1592c (Z_to_bv 64 0).
    stepb_tk F_15930 D_15930 ltac:(cond_compute).
    stepn F_159a0 D_159a0.
    stepST F_159a4 D_159a4 (Z_to_bv 64 0x4fb48) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_159a8 D_159a8.
    stepLD8 F_159ac D_159ac (Z_to_bv 64 0x15be8).
    stepLD8 F_159b0 D_159b0 code.
    stepLD8 F_159b4 D_159b4 (getr regs 9).
    stepLD8 F_159b8 D_159b8 (getr regs 18).
    stepLD8 F_159bc D_159bc (getr regs 19).
    stepn F_159c0 D_159c0. sp_renorm.
    stepn F_159c4 D_159c4.
    stepLD F_1d4f8 D_1d4f8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepb_ft F_1d4fc D_1d4fc ltac:(cond_compute).
    stepret F_1d500 D_1d500 (0x15be8 : word) ltac:(bveq).
    stepn F_15b48 D_15b48.
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
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x4fd68) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x4fd93) 1%nat = Some [Z_to_bv 8 0] ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x4fb58) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x4fb60)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x4fb50) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x4fb4c) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x4fb60) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x4fb68) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x15b30)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x4fc68) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x14178)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x2fa04) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x15b84 : word) mem rom)
                 (mkst regs' (0x15b38 : word) (mem_w1R mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x15bec
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Mhead Mslot Malk Mnext Mf0 Ma0 Mincb.
  unfold mem_w1R, mem_foe, mem_w1. eexists. split.
  -
    stepn F_15ae4 D_15ae4. rewrite Hsp. sp_renorm.
    stepST F_15ae8 D_15ae8 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_15aec D_15aec (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    stepn F_15af0 D_15af0.
    stepn F_15af4 D_15af4. rewrite Htp.
    stepLD F_15af8 D_15af8 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    stepn F_15afc D_15afc.
    stepn F_15b00 D_15b00.
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_15b04 | reflexivity | exact D_15b04
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_15b08 | reflexivity | exact D_15b08 | gres; cond_compute ] | ].
    norm_pc_r.
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_15b0c | reflexivity | exact D_15b0c
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    stepb_ft F_15b10 D_15b10 ltac:(cond_compute).
    stepn F_15b14 D_15b14.
    stepb_ft F_15b18 D_15b18 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    stepb_tk F_15b1c D_15b1c ltac:(cond_compute).
    stepn F_15b40 D_15b40. rewrite Ha0.
    stepn F_15b44 D_15b44.
    stepn F_15900 D_15900. sp_renorm.
    stepST F_15904 D_15904 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x15be8) ltac:(sok_stack SOK).
    stepST F_15908 D_15908 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_1590c D_1590c (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_15910 D_15910 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_15914 D_15914 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    stepn F_15918 D_15918. stepn F_1591c D_1591c. stepn F_15920 D_15920. stepn F_15924 D_15924. stepn F_15928 D_15928.
    stepn F_1d270 D_1d270.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_1d274 | reflexivity | exact D_1d274 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_1d278 D_1d278 ltac:(cond_compute).
    stepret F_1d468 D_1d468 (0x159cc : word) ltac:(bveq).
    stepLD8 F_1592c D_1592c (Z_to_bv 64 0x4fb60).
    stepb_ft F_15930 D_15930 ltac:(cond_compute).
    stepLD F_15934 D_15934 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 1) by lia.
    stepn F_15938 D_15938.
    stepn F_15950 D_15950.
    stepST F_15954 D_15954 (Z_to_bv 64 0x4fb50) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_15958 D_15958 ltac:(cond_compute).
    stepLD8 F_1595c D_1595c (Z_to_bv 64 0x4fb60).
    stepn F_15960 D_15960. stepn F_15964 D_15964.
    stepLD8 F_15968 D_15968 (Z_to_bv 64 0x15b30).
    stepLD8 F_1596c D_1596c (Z_to_bv 64 0x14178).
    stepn F_15970 D_15970. stepn F_15974 D_15974.
    stepLD F_1d4f8 D_1d4f8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepb_ft F_1d4fc D_1d4fc ltac:(cond_compute).
    stepret F_1d500 D_1d500 (0x15a18 : word) ltac:(bveq).
    stepn F_15978 D_15978.
    stepjr F_1597c D_1597c (Z_to_bv 64 0x15b30) ltac:(gres; reflexivity). vnorm.
    stepjr F_15a90 D_15a90 (Z_to_bv 64 0x14178) ltac:(gres; reflexivity). vnorm.
    stepn F_14118 D_14118.
    stepLBU F_1411c D_1411c (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_14120 D_14120 ltac:(cond_compute).
    stepret F_14124 D_14124 (0x15a20 : word) ltac:(bveq).
    stepn F_15980 D_15980. stepn F_15984 D_15984.
    stepn F_1d270 D_1d270.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_1d274 | reflexivity | exact D_1d274 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_1d278 D_1d278 ltac:(cond_compute).
    stepret F_1d468 D_1d468 (0x15a28 : word) ltac:(bveq).
    stepLD F_15988 D_15988 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; apply rdn_wbytes_hit4; u_norm; lia) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepn F_1598c D_1598c.
    stepST F_15990 D_15990 (Z_to_bv 64 0x4fb50) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_15994 D_15994 ltac:(cond_compute).
    stepLD8 F_15998 D_15998 (Z_to_bv 64 0x4fb60).
    stepn F_1599c D_1599c.
    stepLD8 F_1593c D_1593c (Z_to_bv 64 0).
    stepn F_15940 D_15940.
    stepST F_15944 D_15944 (Z_to_bv 64 0x4fb50) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_15948 D_15948 (Z_to_bv 64 0x4fb58) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_1594c D_1594c ltac:(cond_compute).
    stepn F_159a0 D_159a0.
    stepST F_159a4 D_159a4 (Z_to_bv 64 0x4fb48) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_159a8 D_159a8.
    stepLD8 F_159ac D_159ac (Z_to_bv 64 0x15be8).
    stepLD8 F_159b0 D_159b0 code.
    stepLD8 F_159b4 D_159b4 (getr regs 9).
    stepLD8 F_159b8 D_159b8 (getr regs 18).
    stepLD8 F_159bc D_159bc (getr regs 19).
    stepn F_159c0 D_159c0. sp_renorm.
    stepn F_159c4 D_159c4.
    stepLD F_1d4f8 D_1d4f8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepb_ft F_1d4fc D_1d4fc ltac:(cond_compute).
    stepret F_1d500 D_1d500 (0x15be8 : word) ltac:(bveq).
    stepn F_15b48 D_15b48.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.

Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x15bec)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x15b68)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x1e6e8)))
    (Z_to_bv 64 0x1f9f8) [Z_to_bv 8 1].

Lemma w2 {RCa1 : RunCtx}  : forall regs mem rom (sp code s1v dso : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x15bec -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x1e788) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1e6f0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x1e790) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1e6e8)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x1e6e8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13cc0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x1f9f8) 1%nat = Some [Z_to_bv 8 0] ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x1e730) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x15a68)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x1f798) 8%nat = Some (word_to_le_bytes 8 dso) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x1e738) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x15b38 : word) mem rom)
                 (mkst regs' (0x17efc : word) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x15bf0
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
  intros regs mem rom sp code s1v dso Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mdso Mg2.
  unfold mem_w2. eexists. split.
  -
    stepn F_15a98 D_15a98. rewrite Hsp. sp_renorm.
    stepST F_15a9c D_15a9c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x15bec) ltac:(sok_stack SOK).
    stepST F_15aa0 D_15aa0 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_15aa4 D_15aa4 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    stepn F_15aa8 D_15aa8.
    stepn F_15aac D_15aac.
    stepLD8 F_15ab0 D_15ab0 (Z_to_bv 64 0x1e6f0).
    stepLD8 F_15ab4 D_15ab4 (Z_to_bv 64 0x1e6e8).
    stepb_ft F_15ab8 D_15ab8 ltac:(cond_compute).
    stepLD8 F_15abc D_15abc (Z_to_bv 64 0x13cc0).
    stepn F_15ac0 D_15ac0.
    stepjr F_15ac4 D_15ac4 (Z_to_bv 64 0x13cc0) ltac:(gres; reflexivity). vnorm.
    stepn F_13c60 D_13c60. sp_renorm.
    stepST F_13c64 D_13c64 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x15b68) ltac:(sok_stack SOK).
    stepST F_13c68 D_13c68 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x1e6e8) ltac:(sok_stack SOK).
    stepn F_13c6c D_13c6c.
    stepn F_13c70 D_13c70.
    stepn F_13c74 D_13c74.
    stepLBU F_13c78 D_13c78 (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
    stepn F_13c7c D_13c7c.
    stepb_tk F_13c80 D_13c80 ltac:(cond_compute).
    stepn F_13c8c D_13c8c.
    stepn F_13c90 D_13c90.
    stepn F_13c94 D_13c94.
    stepST F_13c98 D_13c98 (Z_to_bv 64 0x1f9f8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_13c9c D_13c9c.
    stepLD8 F_13ca0 D_13ca0 (Z_to_bv 64 0x15a68).
    stepb_ft F_13ca4 D_13ca4 ltac:(cond_compute).
    stepn F_13ca8 D_13ca8.
    stepn F_13cac D_13cac. stepn F_13cb0 D_13cb0.
    stepLD8 F_13cb4 D_13cb4 dso.
    stepn F_13cb8 D_13cb8.
    stepret F_159c8 D_159c8 (0x13d1c : word) ltac:(bveq).
    stepn F_13cbc D_13cbc.
    stepn F_13cc0 D_13cc0.
    stepLD8 F_13cc4 D_13cc4 (Z_to_bv 64 0).
    stepb_tk F_13cc8 D_13cc8 ltac:(cond_compute).
    stepLD8 F_13ce0 D_13ce0 (Z_to_bv 64 0x15b68).
    stepLD8 F_13ce4 D_13ce4 (Z_to_bv 64 0x1e6e8).
    stepn F_13ce8 D_13ce8. sp_renorm.
    stepret F_13cec D_13cec (0x15b68 : word) ltac:(bveq).
    stepn F_15ac8 D_15ac8.
    stepb_ft F_15acc D_15acc ltac:(cond_compute).
    stepLD8 F_15ad0 D_15ad0 (Z_to_bv 64 0x15bec).
    stepLD8 F_15ad4 D_15ad4 code.
    stepLD8 F_15ad8 D_15ad8 s1v.
    stepn F_15adc D_15adc. sp_renorm.
    stepn F_15ae0 D_15ae0.
    stepret F_15a94 D_15a94 (0x15bec : word) ltac:(bveq).
    stepn F_15b4c D_15b4c.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S0Exit_run1.

Module S0Exit_run2.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.StepTac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Hoare OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.WalkTac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.StreamSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.MmapSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.LibAtomic OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.S0ExitBase.
Import OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.LiaFast.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition mem_w3a (mem : word -> option byte) (sp code : word) :=
  wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x15bf0)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x17f0c)))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

Lemma w3a {RCa1 : RunCtx}  : forall regs mem rom (sp code wp1 rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x15bf0 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  file_clean mem 0x1f8b0 wp1 rp1 ->
  file_clean mem 0x1f7c0 wp2 rp2 ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x17efc : word) mem rom)
                 (mkst regs' (0x1598c : word) (mem_w3a mem sp code) rom)
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
    stepn F_17e5c D_17e5c. rewrite Hsp. sp_renorm.
    stepST F_17e60 D_17e60 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x15bf0) ltac:(sok_stack SOK).
    stepST F_17e64 D_17e64 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepn F_17e68 D_17e68.
    stepn F_18000 D_18000. sp_renorm.
    stepST F_18004 D_18004 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x17f0c) ltac:(sok_stack SOK).
    stepST F_18008 D_18008 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_1800c D_1800c.
    stepn F_18010 D_18010.
    stepn F_18014 D_18014.
    stepn F_18018 D_18018.
    stepn F_1d270 D_1d270.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_1d274 | reflexivity | exact D_1d274 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_1d278 D_1d278 ltac:(cond_compute).
    stepret F_1d468 D_1d468 (0x180bc : word) ltac:(bveq).
    stepn F_1801c D_1801c.
    stepLD8 F_18020 D_18020 (Z_to_bv 64 0x17f0c).
    stepLD8 F_18024 D_18024 code.
    stepn F_18028 D_18028. sp_renorm.
    stepret F_1802c D_1802c (0x17f0c : word) ltac:(bveq).
    stepLD8 F_17e6c D_17e6c (Z_to_bv 64 0).
    stepb_ft F_17e70 D_17e70 ltac:(cond_compute).
    stepn F_17e74 D_17e74.
    stepLD8 F_17e78 D_17e78 (Z_to_bv 64 0).
    stepb_tk F_17e7c D_17e7c ltac:(cond_compute).
    stepn F_17ed0 D_17ed0.
    stepLD8 F_17ed4 D_17ed4 (Z_to_bv 64 0x1f8b0).
    stepb_ft F_17ed8 D_17ed8 ltac:(cond_compute).
    stepLD F_17edc D_17edc (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_17ee0 D_17ee0 ltac:(cond_compute).
    stepLD8 F_17eec D_17eec wp1.
    stepLD8 F_17ef0 D_17ef0 wp1.
    stepb_tk F_17ef4 D_17ef4 ltac:(apply c_eq_refl).
    stepLD8 F_17f0c D_17f0c rp1.
    stepLD8 F_17f10 D_17f10 rp1.
    stepb_tk F_17f14 D_17f14 ltac:(apply c_eq_refl).
    stepn F_17f2c D_17f2c.
    stepLD8 F_17f30 D_17f30 (Z_to_bv 64 0x1f7c0).
    stepb_ft F_17f34 D_17f34 ltac:(cond_compute).
    stepLD F_17f38 D_17f38 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_17f3c D_17f3c ltac:(cond_compute).
    stepLD8 F_17f48 D_17f48 wp2.
    stepLD8 F_17f4c D_17f4c wp2.
    stepb_tk F_17f50 D_17f50 ltac:(apply c_eq_refl).
    stepLD8 F_17f68 D_17f68 rp2.
    stepLD8 F_17f6c D_17f6c rp2.
    stepb_tk F_17f70 D_17f70 ltac:(apply c_eq_refl).
    stepLD8 F_17ff0 D_17ff0 (Z_to_bv 64 0x15bf0).
    stepLD8 F_17ff4 D_17ff4 code.
    stepn F_17ff8 D_17ff8. sp_renorm.
    stepret F_17ffc D_17ffc (0x15bf0 : word) ltac:(bveq).
    stepn F_15b50 D_15b50.
    stepn F_15b54 D_15b54.
    stepn F_158e4 D_158e4.
    stepn F_158e8 D_158e8.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S0Exit_run2.

Module S0Exit_run3.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.StepTac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Hoare OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.WalkTac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.StreamSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.MmapSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.LibAtomic OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.S0ExitBase S0Exit_run2.
Import OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.LiaFast.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition stdout_dirty_hdr {RCa1 : RunCtx}  (mem : word -> option byte) (wb wp : Z) : Prop :=
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x1f8b0 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x1f8b0 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
  /\ rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x1f8b0 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
  /\ rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x1f8b0 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1810c)).

Lemma w3b1 {RCa1 : RunCtx}  : forall regs mem rom (sp code : word) (wb wp : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x15bf0 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  stdout_dirty_hdr mem wb wp ->
  (0 <= wb < 2^64)%Z -> (0 <= wp < 2^64)%Z -> wb <> wp ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x17efc : word) mem rom)
                 (mkst regs' (0x1810c : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = Z_to_bv 64 0x1f8b0
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 1 = Z_to_bv 64 0x17fac
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32)
    /\ getr regs' 8 = Z_to_bv 64 0x1f8b0
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof.
  intros regs mem rom sp code wb wp Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr) (F1l & F1wp & F1wb & F1wr) WB WP NE.
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
  unfold mem_w3a. eexists. split.
  -
    stepn F_17e5c D_17e5c. rewrite Hsp. sp_renorm.
    stepST F_17e60 D_17e60 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x15bf0) ltac:(sok_stack SOK).
    stepST F_17e64 D_17e64 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepn F_17e68 D_17e68.
    stepn F_18000 D_18000. sp_renorm.
    stepST F_18004 D_18004 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x17f0c) ltac:(sok_stack SOK).
    stepST F_18008 D_18008 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_1800c D_1800c.
    stepn F_18010 D_18010.
    stepn F_18014 D_18014.
    stepn F_18018 D_18018.
    stepn F_1d270 D_1d270.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_1d274 | reflexivity | exact D_1d274 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_1d278 D_1d278 ltac:(cond_compute).
    stepret F_1d468 D_1d468 (0x180bc : word) ltac:(bveq).
    stepn F_1801c D_1801c.
    stepLD8 F_18020 D_18020 (Z_to_bv 64 0x17f0c).
    stepLD8 F_18024 D_18024 code.
    stepn F_18028 D_18028. sp_renorm.
    stepret F_1802c D_1802c (0x17f0c : word) ltac:(bveq).
    stepLD8 F_17e6c D_17e6c (Z_to_bv 64 0).
    stepb_ft F_17e70 D_17e70 ltac:(cond_compute).
    stepn F_17e74 D_17e74.
    stepLD8 F_17e78 D_17e78 (Z_to_bv 64 0).
    stepb_tk F_17e7c D_17e7c ltac:(cond_compute).
    stepn F_17ed0 D_17ed0.
    stepLD8 F_17ed4 D_17ed4 (Z_to_bv 64 0x1f8b0).
    stepb_ft F_17ed8 D_17ed8 ltac:(cond_compute).
    stepLD F_17edc D_17edc (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_17ee0 D_17ee0 ltac:(cond_compute).
    stepLD8 F_17eec D_17eec (Z_to_bv 64 wp).
    stepLD8 F_17ef0 D_17ef0 (Z_to_bv 64 wb).
    stepb_ft F_17ef4 D_17ef4 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    stepLD8 F_17ef8 D_17ef8 (Z_to_bv 64 0x1810c).
    stepn F_17efc D_17efc.
    stepn F_17f00 D_17f00.
    stepn F_17f04 D_17f04.
    stepjr F_17f08 D_17f08 (Z_to_bv 64 0x1810c) ltac:(gres; reflexivity). vnorm.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Lemma w3b2 {RCa1 : RunCtx}  : forall regs mem rom (sp code rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 32) -> getr regs 8 = Z_to_bv 64 0x1f8b0 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x15bf0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 code) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x1f8b0 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x1f8b0 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x1f8a8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1f7c0)) ->
  file_clean mem 0x1f7c0 wp2 rp2 ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x17fac : word) mem rom)
                 (mkst regs' (0x1598c : word) mem rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr
         (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  eexists. split.
  -
    stepLD8 F_17f0c D_17f0c rp1.
    stepLD8 F_17f10 D_17f10 rp1.
    stepb_tk F_17f14 D_17f14 ltac:(apply c_eq_refl).
    stepn F_17f2c D_17f2c.
    stepLD8 F_17f30 D_17f30 (Z_to_bv 64 0x1f7c0).
    stepb_ft F_17f34 D_17f34 ltac:(cond_compute).
    stepLD F_17f38 D_17f38 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_17f3c D_17f3c ltac:(cond_compute).
    stepLD8 F_17f48 D_17f48 wp2.
    stepLD8 F_17f4c D_17f4c wp2.
    stepb_tk F_17f50 D_17f50 ltac:(apply c_eq_refl).
    stepLD8 F_17f68 D_17f68 rp2.
    stepLD8 F_17f6c D_17f6c rp2.
    stepb_tk F_17f70 D_17f70 ltac:(apply c_eq_refl).
    stepLD8 F_17ff0 D_17ff0 (Z_to_bv 64 0x15bf0).
    stepLD8 F_17ff4 D_17ff4 code.
    stepn F_17ff8 D_17ff8. rewrite Hsp. sp_renorm.
    stepret F_17ffc D_17ffc (0x15bf0 : word) ltac:(bveq).
    stepn F_15b50 D_15b50.
    stepn F_15b54 D_15b54.
    stepn F_158e4 D_158e4.
    stepn F_158e8 D_158e8.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S0Exit_run3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.StepTac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Hoare OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.WalkTac OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.StreamSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.MmapSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.LibAtomic OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.ExitSim OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.ShapeAlg OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Nodes OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Spec OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.LibWritev OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.S0StdioDefs S0Exit_run1 S0Exit_run2 S0Exit_run3 OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.S0StdioWrite.S0StdioWrite_run1 OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.S0StdioWrite.S0StdioWrite_run2 OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.S0StdioWrite.
Import OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.LiaFast.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac zaddr_rec H := zaddr H.


Theorem ref_exit_clean {RCa1 : RunCtx}  :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  file_clean mem 0x1f8b0 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs (0x15b84 : word) mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
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
    eapply rz_exit_at; [exact F_158ec | exact E_158ec | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
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
    eapply rz_exit_at; [exact F_158ec | exact E_158ec | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.


Theorem ref_exit_flush {RCa1 : RunCtx}  :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  m_channel_reader model = true ->
  realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs (0x15b84 : word) mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
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
    replace (Z_to_bv 64 0x17fac) with (0x17fac : word) in R3ra by (apply bv_eq; reflexivity).
    unfold W. rewrite <- (app_nil_r pending).
    set (mem3 := mem_w3a (mem_w2 (mem_w1U mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9)) sp code).
    eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) 0x1f8b0 wb wp 1
              (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x17fac : word) pending []);
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
      eapply rz_exit_at; [exact F_158ec | exact E_158ec | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
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
    replace (Z_to_bv 64 0x17fac) with (0x17fac : word) in R3ra by (apply bv_eq; reflexivity).
    unfold W. rewrite <- (app_nil_r pending).
    set (mem3 := mem_w3a (mem_w2 (mem_w1R mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9)) sp code).
    eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) 0x1f8b0 wb wp 1
              (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x17fac : word) pending []);
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
      eapply rz_exit_at; [exact F_158ec | exact E_158ec | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.


Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
  intros code fs. apply t_eq_sym. apply t_emit_nil_eq.
  unfold t_exit, t_emit. left. apply is_prefix_nil.
Qed.

Theorem ref_exit {RCa1 : RunCtx}  : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs (0x15b84 : word) mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
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
  realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs (Z_to_bv 64 0x15b84) mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros. replace (Z_to_bv 64 0x15b84) with (0x15b84 : word) by (apply bv_eq; reflexivity).
  apply ref_exit; assumption.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
