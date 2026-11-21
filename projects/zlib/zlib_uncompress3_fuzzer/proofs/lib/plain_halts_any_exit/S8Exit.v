(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_zlib_uncompress3_fuzzer_repro.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic S8ExitBase.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes Spec LibWritev S8StdioDefs S8StdioWrite.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit Require Import PropExec S8_code_146ec_15000 S8_code_18000_19000 S8_code_19000_1a000 S8_code_1a000_1b000 S8_code_1b000_1c000 S8_code_20000_20a98.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.

Module S0Exit_run1.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.StepTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Hoare OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.WalkTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.StreamSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.MmapSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.LibAtomic OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.S8ExitBase.
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
    (Z_to_bv 64 0x93240) (word_to_le_bytes 4 (Z_to_bv 64 tid)).

Definition mem_foe (mem : word -> option byte) (sp code s1v s2v s3v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x19188)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3v).

Definition mem_w1U (mem : word -> option byte) (sp ra s0 : word) (tid : Z) (code s1v s2v s3v : word) :=
  wbytes (mem_foe (mem_w1 mem sp ra s0 tid) sp code s1v s2v s3v)
    (Z_to_bv 64 0x93020) [Z_to_bv 8 1].

Definition mem_w1R (mem : word -> option byte) (sp ra s0 : word) (tid : Z) (code s1v s2v s3v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (mem_foe (mem_w1 mem sp ra s0 tid) sp code s1v s2v s3v)
    (Z_to_bv 64 0x93028) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x93028) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x93028) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x93030) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x93020) [Z_to_bv 8 1].

Lemma w1U {RCa1 : RunCtx}  : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x93240) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x9326b) 1%nat = Some [Z_to_bv 8 0] ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x93030) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x93024) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x19124 : word) mem rom)
                 (mkst regs' (0x190d8 : word) (mem_w1U mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x1918c
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Mhead Malk.
  unfold mem_w1U, mem_foe, mem_w1. eexists. split.
  -
    stepn F_18ff4 D_18ff4. rewrite Hsp. sp_renorm.
    stepST F_18ff8 D_18ff8 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_18ffc D_18ffc (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    stepn F_19000 D_19000.
    stepn F_19004 D_19004. rewrite Htp.
    stepLD F_19008 D_19008 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    stepn F_1900c D_1900c.
    stepn F_19010 D_19010.
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_19014 | reflexivity | exact D_19014
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_19018 | reflexivity | exact D_19018 | gres; cond_compute ] | ].
    norm_pc_r.
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_1901c | reflexivity | exact D_1901c
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    stepb_ft F_19020 D_19020 ltac:(cond_compute).
    stepn F_19024 D_19024.
    stepb_ft F_19028 D_19028 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    stepb_tk F_1902c D_1902c ltac:(cond_compute).
    stepn F_19050 D_19050. rewrite Ha0.
    stepn F_19054 D_19054.
    stepn F_18e10 D_18e10. sp_renorm.
    stepST F_18e14 D_18e14 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x19188) ltac:(sok_stack SOK).
    stepST F_18e18 D_18e18 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_18e1c D_18e1c (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_18e20 D_18e20 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_18e24 D_18e24 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    stepn F_18e28 D_18e28. stepn F_18e2c D_18e2c. stepn F_18e30 D_18e30. stepn F_18e34 D_18e34. stepn F_18e38 D_18e38.
    stepn F_206c8 D_206c8.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_206cc | reflexivity | exact D_206cc | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_206d0 D_206d0 ltac:(cond_compute).
    stepret F_208c0 D_208c0 (0x18f6c : word) ltac:(bveq).
    stepLD8 F_18e3c D_18e3c (Z_to_bv 64 0).
    stepb_tk F_18e40 D_18e40 ltac:(cond_compute).
    stepn F_18eb0 D_18eb0.
    stepST F_18eb4 D_18eb4 (Z_to_bv 64 0x93020) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_18eb8 D_18eb8.
    stepLD8 F_18ebc D_18ebc (Z_to_bv 64 0x19188).
    stepLD8 F_18ec0 D_18ec0 code.
    stepLD8 F_18ec4 D_18ec4 (getr regs 9).
    stepLD8 F_18ec8 D_18ec8 (getr regs 18).
    stepLD8 F_18ecc D_18ecc (getr regs 19).
    stepn F_18ed0 D_18ed0. sp_renorm.
    stepn F_18ed4 D_18ed4.
    stepLD F_20950 D_20950 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepb_ft F_20954 D_20954 ltac:(cond_compute).
    stepret F_20958 D_20958 (0x19188 : word) ltac:(bveq).
    stepn F_19058 D_19058.
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
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x93240) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x9326b) 1%nat = Some [Z_to_bv 8 0] ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x93030) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x93038)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x93028) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x93024) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x93038) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x93040) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x190d0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x93140) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x14cfc)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x32ee4) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x19124 : word) mem rom)
                 (mkst regs' (0x190d8 : word) (mem_w1R mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x1918c
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Mhead Mslot Malk Mnext Mf0 Ma0 Mincb.
  unfold mem_w1R, mem_foe, mem_w1. eexists. split.
  -
    stepn F_18ff4 D_18ff4. rewrite Hsp. sp_renorm.
    stepST F_18ff8 D_18ff8 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_18ffc D_18ffc (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    stepn F_19000 D_19000.
    stepn F_19004 D_19004. rewrite Htp.
    stepLD F_19008 D_19008 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    stepn F_1900c D_1900c.
    stepn F_19010 D_19010.
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_19014 | reflexivity | exact D_19014
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_19018 | reflexivity | exact D_19018 | gres; cond_compute ] | ].
    norm_pc_r.
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_1901c | reflexivity | exact D_1901c
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    stepb_ft F_19020 D_19020 ltac:(cond_compute).
    stepn F_19024 D_19024.
    stepb_ft F_19028 D_19028 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    stepb_tk F_1902c D_1902c ltac:(cond_compute).
    stepn F_19050 D_19050. rewrite Ha0.
    stepn F_19054 D_19054.
    stepn F_18e10 D_18e10. sp_renorm.
    stepST F_18e14 D_18e14 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x19188) ltac:(sok_stack SOK).
    stepST F_18e18 D_18e18 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_18e1c D_18e1c (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_18e20 D_18e20 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_18e24 D_18e24 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    stepn F_18e28 D_18e28. stepn F_18e2c D_18e2c. stepn F_18e30 D_18e30. stepn F_18e34 D_18e34. stepn F_18e38 D_18e38.
    stepn F_206c8 D_206c8.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_206cc | reflexivity | exact D_206cc | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_206d0 D_206d0 ltac:(cond_compute).
    stepret F_208c0 D_208c0 (0x18f6c : word) ltac:(bveq).
    stepLD8 F_18e3c D_18e3c (Z_to_bv 64 0x93038).
    stepb_ft F_18e40 D_18e40 ltac:(cond_compute).
    stepLD F_18e44 D_18e44 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 1) by lia.
    stepn F_18e48 D_18e48.
    stepn F_18e60 D_18e60.
    stepST F_18e64 D_18e64 (Z_to_bv 64 0x93028) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_18e68 D_18e68 ltac:(cond_compute).
    stepLD8 F_18e6c D_18e6c (Z_to_bv 64 0x93038).
    stepn F_18e70 D_18e70. stepn F_18e74 D_18e74.
    stepLD8 F_18e78 D_18e78 (Z_to_bv 64 0x190d0).
    stepLD8 F_18e7c D_18e7c (Z_to_bv 64 0x14cfc).
    stepn F_18e80 D_18e80. stepn F_18e84 D_18e84.
    stepLD F_20950 D_20950 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepb_ft F_20954 D_20954 ltac:(cond_compute).
    stepret F_20958 D_20958 (0x18fb8 : word) ltac:(bveq).
    stepn F_18e88 D_18e88.
    stepjr F_18e8c D_18e8c (Z_to_bv 64 0x190d0) ltac:(gres; reflexivity). vnorm.
    stepjr F_18fa0 D_18fa0 (Z_to_bv 64 0x14cfc) ltac:(gres; reflexivity). vnorm.
    stepn F_14c60 D_14c60.
    stepLBU F_14c64 D_14c64 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_14c68 D_14c68 ltac:(cond_compute).
    stepret F_14c6c D_14c6c (0x18fc0 : word) ltac:(bveq).
    stepn F_18e90 D_18e90. stepn F_18e94 D_18e94.
    stepn F_206c8 D_206c8.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_206cc | reflexivity | exact D_206cc | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_206d0 D_206d0 ltac:(cond_compute).
    stepret F_208c0 D_208c0 (0x18fc8 : word) ltac:(bveq).
    stepLD F_18e98 D_18e98 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; apply rdn_wbytes_hit4; u_norm; lia) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepn F_18e9c D_18e9c.
    stepST F_18ea0 D_18ea0 (Z_to_bv 64 0x93028) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_18ea4 D_18ea4 ltac:(cond_compute).
    stepLD8 F_18ea8 D_18ea8 (Z_to_bv 64 0x93038).
    stepn F_18eac D_18eac.
    stepLD8 F_18e4c D_18e4c (Z_to_bv 64 0).
    stepn F_18e50 D_18e50.
    stepST F_18e54 D_18e54 (Z_to_bv 64 0x93028) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_18e58 D_18e58 (Z_to_bv 64 0x93030) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_18e5c D_18e5c ltac:(cond_compute).
    stepn F_18eb0 D_18eb0.
    stepST F_18eb4 D_18eb4 (Z_to_bv 64 0x93020) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_18eb8 D_18eb8.
    stepLD8 F_18ebc D_18ebc (Z_to_bv 64 0x19188).
    stepLD8 F_18ec0 D_18ec0 code.
    stepLD8 F_18ec4 D_18ec4 (getr regs 9).
    stepLD8 F_18ec8 D_18ec8 (getr regs 18).
    stepLD8 F_18ecc D_18ecc (getr regs 19).
    stepn F_18ed0 D_18ed0. sp_renorm.
    stepn F_18ed4 D_18ed4.
    stepLD F_20950 D_20950 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepb_ft F_20954 D_20954 ltac:(cond_compute).
    stepret F_20958 D_20958 (0x19188 : word) ltac:(bveq).
    stepn F_19058 D_19058.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.

Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x1918c)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x19108)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x21bd0)))
    (Z_to_bv 64 0x22ed8) [Z_to_bv 8 1].

Lemma w2 {RCa1 : RunCtx}  : forall regs mem rom (sp code s1v dso : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x1918c -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x21c70) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x21bd8)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x21c78) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x21bd0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x21bd0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x14844)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22ed8) 1%nat = Some [Z_to_bv 8 0] ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x21c18) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x19008)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22c80) 8%nat = Some (word_to_le_bytes 8 dso) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x21c20) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x190d8 : word) mem rom)
                 (mkst regs' (0x1b3e4 : word) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x19190
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
  intros regs mem rom sp code s1v dso Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mdso Mg2.
  unfold mem_w2. eexists. split.
  -
    stepn F_18fa8 D_18fa8. rewrite Hsp. sp_renorm.
    stepST F_18fac D_18fac (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x1918c) ltac:(sok_stack SOK).
    stepST F_18fb0 D_18fb0 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_18fb4 D_18fb4 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    stepn F_18fb8 D_18fb8.
    stepn F_18fbc D_18fbc.
    stepLD8 F_18fc0 D_18fc0 (Z_to_bv 64 0x21bd8).
    stepLD8 F_18fc4 D_18fc4 (Z_to_bv 64 0x21bd0).
    stepb_ft F_18fc8 D_18fc8 ltac:(cond_compute).
    stepLD8 F_18fcc D_18fcc (Z_to_bv 64 0x14844).
    stepn F_18fd0 D_18fd0.
    stepjr F_18fd4 D_18fd4 (Z_to_bv 64 0x14844) ltac:(gres; reflexivity). vnorm.
    stepn F_147a8 D_147a8. sp_renorm.
    stepST F_147ac D_147ac (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x19108) ltac:(sok_stack SOK).
    stepST F_147b0 D_147b0 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x21bd0) ltac:(sok_stack SOK).
    stepn F_147b4 D_147b4.
    stepn F_147b8 D_147b8.
    stepn F_147bc D_147bc.
    stepLBU F_147c0 D_147c0 (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
    stepn F_147c4 D_147c4.
    stepb_tk F_147c8 D_147c8 ltac:(cond_compute).
    stepn F_147d4 D_147d4.
    stepn F_147d8 D_147d8.
    stepn F_147dc D_147dc.
    stepST F_147e0 D_147e0 (Z_to_bv 64 0x22ed8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_147e4 D_147e4.
    stepLD8 F_147e8 D_147e8 (Z_to_bv 64 0x19008).
    stepb_ft F_147ec D_147ec ltac:(cond_compute).
    stepn F_147f0 D_147f0.
    stepn F_147f4 D_147f4. stepn F_147f8 D_147f8.
    stepLD8 F_147fc D_147fc dso.
    stepn F_14800 D_14800.
    stepret F_18ed8 D_18ed8 (0x148a0 : word) ltac:(bveq).
    stepn F_14804 D_14804.
    stepn F_14808 D_14808.
    stepLD8 F_1480c D_1480c (Z_to_bv 64 0).
    stepb_tk F_14810 D_14810 ltac:(cond_compute).
    stepLD8 F_14828 D_14828 (Z_to_bv 64 0x19108).
    stepLD8 F_1482c D_1482c (Z_to_bv 64 0x21bd0).
    stepn F_14830 D_14830. sp_renorm.
    stepret F_14834 D_14834 (0x19108 : word) ltac:(bveq).
    stepn F_18fd8 D_18fd8.
    stepb_ft F_18fdc D_18fdc ltac:(cond_compute).
    stepLD8 F_18fe0 D_18fe0 (Z_to_bv 64 0x1918c).
    stepLD8 F_18fe4 D_18fe4 code.
    stepLD8 F_18fe8 D_18fe8 s1v.
    stepn F_18fec D_18fec. sp_renorm.
    stepn F_18ff0 D_18ff0.
    stepret F_18fa4 D_18fa4 (0x1918c : word) ltac:(bveq).
    stepn F_1905c D_1905c.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S0Exit_run1.

Module S0Exit_run2.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.StepTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Hoare OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.WalkTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.StreamSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.MmapSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.LibAtomic OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.S8ExitBase.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition mem_w3a (mem : word -> option byte) (sp code : word) :=
  wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x19190)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x1b3f4)))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

Lemma w3a {RCa1 : RunCtx}  : forall regs mem rom (sp code wp1 rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x19190 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  file_clean mem 0x22d98 wp1 rp1 ->
  file_clean mem 0x22ca8 wp2 rp2 ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1b3e4 : word) mem rom)
                 (mkst regs' (0x191a0 : word) (mem_w3a mem sp code) rom)
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
    stepn F_1b2b4 D_1b2b4. rewrite Hsp. sp_renorm.
    stepST F_1b2b8 D_1b2b8 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x19190) ltac:(sok_stack SOK).
    stepST F_1b2bc D_1b2bc (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepn F_1b2c0 D_1b2c0.
    stepn F_1b458 D_1b458. sp_renorm.
    stepST F_1b45c D_1b45c (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x1b3f4) ltac:(sok_stack SOK).
    stepST F_1b460 D_1b460 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_1b464 D_1b464.
    stepn F_1b468 D_1b468.
    stepn F_1b46c D_1b46c.
    stepn F_1b470 D_1b470.
    stepn F_206c8 D_206c8.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_206cc | reflexivity | exact D_206cc | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_206d0 D_206d0 ltac:(cond_compute).
    stepret F_208c0 D_208c0 (0x1b5a4 : word) ltac:(bveq).
    stepn F_1b474 D_1b474.
    stepLD8 F_1b478 D_1b478 (Z_to_bv 64 0x1b3f4).
    stepLD8 F_1b47c D_1b47c code.
    stepn F_1b480 D_1b480. sp_renorm.
    stepret F_1b484 D_1b484 (0x1b3f4 : word) ltac:(bveq).
    stepLD8 F_1b2c4 D_1b2c4 (Z_to_bv 64 0).
    stepb_ft F_1b2c8 D_1b2c8 ltac:(cond_compute).
    stepn F_1b2cc D_1b2cc.
    stepLD8 F_1b2d0 D_1b2d0 (Z_to_bv 64 0).
    stepb_tk F_1b2d4 D_1b2d4 ltac:(cond_compute).
    stepn F_1b328 D_1b328.
    stepLD8 F_1b32c D_1b32c (Z_to_bv 64 0x22d98).
    stepb_ft F_1b330 D_1b330 ltac:(cond_compute).
    stepLD F_1b334 D_1b334 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_1b338 D_1b338 ltac:(cond_compute).
    stepLD8 F_1b344 D_1b344 wp1.
    stepLD8 F_1b348 D_1b348 wp1.
    stepb_tk F_1b34c D_1b34c ltac:(apply c_eq_refl).
    stepLD8 F_1b364 D_1b364 rp1.
    stepLD8 F_1b368 D_1b368 rp1.
    stepb_tk F_1b36c D_1b36c ltac:(apply c_eq_refl).
    stepn F_1b384 D_1b384.
    stepLD8 F_1b388 D_1b388 (Z_to_bv 64 0x22ca8).
    stepb_ft F_1b38c D_1b38c ltac:(cond_compute).
    stepLD F_1b390 D_1b390 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_1b394 D_1b394 ltac:(cond_compute).
    stepLD8 F_1b3a0 D_1b3a0 wp2.
    stepLD8 F_1b3a4 D_1b3a4 wp2.
    stepb_tk F_1b3a8 D_1b3a8 ltac:(apply c_eq_refl).
    stepLD8 F_1b3c0 D_1b3c0 rp2.
    stepLD8 F_1b3c4 D_1b3c4 rp2.
    stepb_tk F_1b3c8 D_1b3c8 ltac:(apply c_eq_refl).
    stepLD8 F_1b448 D_1b448 (Z_to_bv 64 0x19190).
    stepLD8 F_1b44c D_1b44c code.
    stepn F_1b450 D_1b450. sp_renorm.
    stepret F_1b454 D_1b454 (0x19190 : word) ltac:(bveq).
    stepn F_19060 D_19060.
    stepn F_19064 D_19064.
    stepn F_19068 D_19068.
    stepn F_1906c D_1906c.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S0Exit_run2.

Module S0Exit_run3.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.StepTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Hoare OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.WalkTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.StreamSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.MmapSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.LibAtomic OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.S8ExitBase S0Exit_run2.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition stdout_dirty_hdr {RCa1 : RunCtx}  (mem : word -> option byte) (wb wp : Z) : Prop :=
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x22d98 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x22d98 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
  /\ rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x22d98 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
  /\ rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x22d98 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1b5f4)).

Lemma w3b1 {RCa1 : RunCtx}  : forall regs mem rom (sp code : word) (wb wp : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x19190 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  stdout_dirty_hdr mem wb wp ->
  (0 <= wb < 2^64)%Z -> (0 <= wp < 2^64)%Z -> wb <> wp ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1b3e4 : word) mem rom)
                 (mkst regs' (0x1b5f4 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = Z_to_bv 64 0x22d98
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 1 = Z_to_bv 64 0x1b494
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32)
    /\ getr regs' 8 = Z_to_bv 64 0x22d98
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof.
  intros regs mem rom sp code wb wp Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr) (F1l & F1wp & F1wb & F1wr) WB WP NE.
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
  unfold mem_w3a. eexists. split.
  -
    stepn F_1b2b4 D_1b2b4. rewrite Hsp. sp_renorm.
    stepST F_1b2b8 D_1b2b8 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x19190) ltac:(sok_stack SOK).
    stepST F_1b2bc D_1b2bc (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepn F_1b2c0 D_1b2c0.
    stepn F_1b458 D_1b458. sp_renorm.
    stepST F_1b45c D_1b45c (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x1b3f4) ltac:(sok_stack SOK).
    stepST F_1b460 D_1b460 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_1b464 D_1b464.
    stepn F_1b468 D_1b468.
    stepn F_1b46c D_1b46c.
    stepn F_1b470 D_1b470.
    stepn F_206c8 D_206c8.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_206cc | reflexivity | exact D_206cc | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_206d0 D_206d0 ltac:(cond_compute).
    stepret F_208c0 D_208c0 (0x1b5a4 : word) ltac:(bveq).
    stepn F_1b474 D_1b474.
    stepLD8 F_1b478 D_1b478 (Z_to_bv 64 0x1b3f4).
    stepLD8 F_1b47c D_1b47c code.
    stepn F_1b480 D_1b480. sp_renorm.
    stepret F_1b484 D_1b484 (0x1b3f4 : word) ltac:(bveq).
    stepLD8 F_1b2c4 D_1b2c4 (Z_to_bv 64 0).
    stepb_ft F_1b2c8 D_1b2c8 ltac:(cond_compute).
    stepn F_1b2cc D_1b2cc.
    stepLD8 F_1b2d0 D_1b2d0 (Z_to_bv 64 0).
    stepb_tk F_1b2d4 D_1b2d4 ltac:(cond_compute).
    stepn F_1b328 D_1b328.
    stepLD8 F_1b32c D_1b32c (Z_to_bv 64 0x22d98).
    stepb_ft F_1b330 D_1b330 ltac:(cond_compute).
    stepLD F_1b334 D_1b334 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_1b338 D_1b338 ltac:(cond_compute).
    stepLD8 F_1b344 D_1b344 (Z_to_bv 64 wp).
    stepLD8 F_1b348 D_1b348 (Z_to_bv 64 wb).
    stepb_ft F_1b34c D_1b34c ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    stepLD8 F_1b350 D_1b350 (Z_to_bv 64 0x1b5f4).
    stepn F_1b354 D_1b354.
    stepn F_1b358 D_1b358.
    stepn F_1b35c D_1b35c.
    stepjr F_1b360 D_1b360 (Z_to_bv 64 0x1b5f4) ltac:(gres; reflexivity). vnorm.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Lemma w3b2 {RCa1 : RunCtx}  : forall regs mem rom (sp code rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 32) -> getr regs 8 = Z_to_bv 64 0x22d98 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x19190)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 code) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x22d98 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x22d98 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22d90) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x22ca8)) ->
  file_clean mem 0x22ca8 wp2 rp2 ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1b494 : word) mem rom)
                 (mkst regs' (0x191a0 : word) mem rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr
         (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  eexists. split.
  -
    stepLD8 F_1b364 D_1b364 rp1.
    stepLD8 F_1b368 D_1b368 rp1.
    stepb_tk F_1b36c D_1b36c ltac:(apply c_eq_refl).
    stepn F_1b384 D_1b384.
    stepLD8 F_1b388 D_1b388 (Z_to_bv 64 0x22ca8).
    stepb_ft F_1b38c D_1b38c ltac:(cond_compute).
    stepLD F_1b390 D_1b390 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_1b394 D_1b394 ltac:(cond_compute).
    stepLD8 F_1b3a0 D_1b3a0 wp2.
    stepLD8 F_1b3a4 D_1b3a4 wp2.
    stepb_tk F_1b3a8 D_1b3a8 ltac:(apply c_eq_refl).
    stepLD8 F_1b3c0 D_1b3c0 rp2.
    stepLD8 F_1b3c4 D_1b3c4 rp2.
    stepb_tk F_1b3c8 D_1b3c8 ltac:(apply c_eq_refl).
    stepLD8 F_1b448 D_1b448 (Z_to_bv 64 0x19190).
    stepLD8 F_1b44c D_1b44c code.
    stepn F_1b450 D_1b450. rewrite Hsp. sp_renorm.
    stepret F_1b454 D_1b454 (0x19190 : word) ltac:(bveq).
    stepn F_19060 D_19060.
    stepn F_19064 D_19064.
    stepn F_19068 D_19068.
    stepn F_1906c D_1906c.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S0Exit_run3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.StepTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Hoare OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.WalkTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.StreamSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.MmapSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.LibAtomic OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.ExitSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.ShapeAlg OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Nodes OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.Spec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.LibWritev OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.S8StdioDefs S0Exit_run1 S0Exit_run2 S0Exit_run3 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.S8StdioWrite.S0StdioWrite_run1 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.S8StdioWrite.S0StdioWrite_run2 OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.plain_halts_any_exit.S8StdioWrite.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac zaddr_rec H := zaddr H.


Theorem ref_exit_clean {RCa1 : RunCtx}  :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  file_clean mem 0x22d98 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs (0x19124 : word) mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
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
    eapply rz_exit_at; [exact F_19070 | exact E_19070 | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
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
    eapply rz_exit_at; [exact F_19070 | exact E_19070 | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.


Theorem ref_exit_flush {RCa1 : RunCtx}  :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  m_channel_reader model = true ->
  realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs (0x19124 : word) mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
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
    replace (Z_to_bv 64 0x1b494) with (0x1b494 : word) in R3ra by (apply bv_eq; reflexivity).
    unfold W. rewrite <- (app_nil_r pending).
    set (mem3 := mem_w3a (mem_w2 (mem_w1U mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9)) sp code).
    eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) 0x22d98 wb wp 1
              (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x1b494 : word) pending []);
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
      eapply rz_exit_at; [exact F_19070 | exact E_19070 | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
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
    replace (Z_to_bv 64 0x1b494) with (0x1b494 : word) in R3ra by (apply bv_eq; reflexivity).
    unfold W. rewrite <- (app_nil_r pending).
    set (mem3 := mem_w3a (mem_w2 (mem_w1R mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9)) sp code).
    eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) 0x22d98 wb wp 1
              (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x1b494 : word) pending []);
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
      eapply rz_exit_at; [exact F_19070 | exact E_19070 | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.


Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
  intros code fs. apply t_eq_sym. apply t_emit_nil_eq.
  unfold t_exit, t_emit. left. apply is_prefix_nil.
Qed.

Theorem ref_exit {RCa1 : RunCtx}  : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs (0x19124 : word) mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
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
  realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs (Z_to_bv 64 0x19124) mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros. replace (Z_to_bv 64 0x19124) with (0x19124 : word) by (apply bv_eq; reflexivity).
  apply ref_exit; assumption.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
