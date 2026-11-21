(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress2_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic U7ExitBase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require LiaFast.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes Spec LibWritev U7StdioDefs U7StdioWrite.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec U7_code_14708_15000 U7_code_19000_1a000 U7_code_1a000_1b000 U7_code_1b000_1c000 U7_code_1c000_1d000 U7_code_21000_21d00.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.

Module S0Exit_run1.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Hoare OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.WalkTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StreamSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.MmapSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.LibAtomic OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.U7ExitBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.LiaFast.
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
    (Z_to_bv 64 0x944d0) (word_to_le_bytes 4 (Z_to_bv 64 tid)).

Definition mem_foe (mem : word -> option byte) (sp code s1v s2v s3v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x1a40c)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3v).

Definition mem_w1U (mem : word -> option byte) (sp ra s0 : word) (tid : Z) (code s1v s2v s3v : word) :=
  wbytes (mem_foe (mem_w1 mem sp ra s0 tid) sp code s1v s2v s3v)
    (Z_to_bv 64 0x942b0) [Z_to_bv 8 1].

Definition mem_w1R (mem : word -> option byte) (sp ra s0 : word) (tid : Z) (code s1v s2v s3v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (mem_foe (mem_w1 mem sp ra s0 tid) sp code s1v s2v s3v)
    (Z_to_bv 64 0x942b8) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x942b8) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x942b8) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x942c0) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x942b0) [Z_to_bv 8 1].

Lemma w1U {RCa1 : RunCtx}  : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x944d0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x944fb) 1%nat = Some [Z_to_bv 8 0] ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x942c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x942b4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1a3a8 : word) mem rom)
                 (mkst regs' (0x1a35c : word) (mem_w1U mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x1a410
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Mhead Malk.
  unfold mem_w1U, mem_foe, mem_w1. eexists. split.
  -
    stepn F_1a25c D_1a25c. rewrite Hsp. sp_renorm.
    stepST F_1a260 D_1a260 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_1a264 D_1a264 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    stepn F_1a268 D_1a268.
    stepn F_1a26c D_1a26c. rewrite Htp.
    stepLD F_1a270 D_1a270 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    stepn F_1a274 D_1a274.
    stepn F_1a278 D_1a278.
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_1a27c | reflexivity | exact D_1a27c
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_1a280 | reflexivity | exact D_1a280 | gres; cond_compute ] | ].
    norm_pc_r.
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_1a284 | reflexivity | exact D_1a284
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    stepb_ft F_1a288 D_1a288 ltac:(cond_compute).
    stepn F_1a28c D_1a28c.
    stepb_ft F_1a290 D_1a290 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    stepb_tk F_1a294 D_1a294 ltac:(cond_compute).
    stepn F_1a2b8 D_1a2b8. rewrite Ha0.
    stepn F_1a2bc D_1a2bc.
    stepn F_1a078 D_1a078. sp_renorm.
    stepST F_1a07c D_1a07c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x1a40c) ltac:(sok_stack SOK).
    stepST F_1a080 D_1a080 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_1a084 D_1a084 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_1a088 D_1a088 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_1a08c D_1a08c (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    stepn F_1a090 D_1a090. stepn F_1a094 D_1a094. stepn F_1a098 D_1a098. stepn F_1a09c D_1a09c. stepn F_1a0a0 D_1a0a0.
    stepn F_21930 D_21930.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_21934 | reflexivity | exact D_21934 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_21938 D_21938 ltac:(cond_compute).
    stepret F_21b28 D_21b28 (0x1a1f0 : word) ltac:(bveq).
    stepLD8 F_1a0a4 D_1a0a4 (Z_to_bv 64 0).
    stepb_tk F_1a0a8 D_1a0a8 ltac:(cond_compute).
    stepn F_1a118 D_1a118.
    stepST F_1a11c D_1a11c (Z_to_bv 64 0x942b0) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_1a120 D_1a120.
    stepLD8 F_1a124 D_1a124 (Z_to_bv 64 0x1a40c).
    stepLD8 F_1a128 D_1a128 code.
    stepLD8 F_1a12c D_1a12c (getr regs 9).
    stepLD8 F_1a130 D_1a130 (getr regs 18).
    stepLD8 F_1a134 D_1a134 (getr regs 19).
    stepn F_1a138 D_1a138. sp_renorm.
    stepn F_1a13c D_1a13c.
    stepLD F_21bb8 D_21bb8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepb_ft F_21bbc D_21bbc ltac:(cond_compute).
    stepret F_21bc0 D_21bc0 (0x1a40c : word) ltac:(bveq).
    stepn F_1a2c0 D_1a2c0.
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
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x944d0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x944fb) 1%nat = Some [Z_to_bv 8 0] ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x942c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x942c8)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x942b8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x942b4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x942c8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x942d0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1a354)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x943d0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x14d24)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x34174) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1a3a8 : word) mem rom)
                 (mkst regs' (0x1a35c : word) (mem_w1R mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x1a410
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Mhead Mslot Malk Mnext Mf0 Ma0 Mincb.
  unfold mem_w1R, mem_foe, mem_w1. eexists. split.
  -
    stepn F_1a25c D_1a25c. rewrite Hsp. sp_renorm.
    stepST F_1a260 D_1a260 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_1a264 D_1a264 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    stepn F_1a268 D_1a268.
    stepn F_1a26c D_1a26c. rewrite Htp.
    stepLD F_1a270 D_1a270 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    stepn F_1a274 D_1a274.
    stepn F_1a278 D_1a278.
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_1a27c | reflexivity | exact D_1a27c
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_1a280 | reflexivity | exact D_1a280 | gres; cond_compute ] | ].
    norm_pc_r.
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_1a284 | reflexivity | exact D_1a284
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    stepb_ft F_1a288 D_1a288 ltac:(cond_compute).
    stepn F_1a28c D_1a28c.
    stepb_ft F_1a290 D_1a290 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    stepb_tk F_1a294 D_1a294 ltac:(cond_compute).
    stepn F_1a2b8 D_1a2b8. rewrite Ha0.
    stepn F_1a2bc D_1a2bc.
    stepn F_1a078 D_1a078. sp_renorm.
    stepST F_1a07c D_1a07c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x1a40c) ltac:(sok_stack SOK).
    stepST F_1a080 D_1a080 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_1a084 D_1a084 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_1a088 D_1a088 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_1a08c D_1a08c (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    stepn F_1a090 D_1a090. stepn F_1a094 D_1a094. stepn F_1a098 D_1a098. stepn F_1a09c D_1a09c. stepn F_1a0a0 D_1a0a0.
    stepn F_21930 D_21930.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_21934 | reflexivity | exact D_21934 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_21938 D_21938 ltac:(cond_compute).
    stepret F_21b28 D_21b28 (0x1a1f0 : word) ltac:(bveq).
    stepLD8 F_1a0a4 D_1a0a4 (Z_to_bv 64 0x942c8).
    stepb_ft F_1a0a8 D_1a0a8 ltac:(cond_compute).
    stepLD F_1a0ac D_1a0ac (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 1) by lia.
    stepn F_1a0b0 D_1a0b0.
    stepn F_1a0c8 D_1a0c8.
    stepST F_1a0cc D_1a0cc (Z_to_bv 64 0x942b8) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_1a0d0 D_1a0d0 ltac:(cond_compute).
    stepLD8 F_1a0d4 D_1a0d4 (Z_to_bv 64 0x942c8).
    stepn F_1a0d8 D_1a0d8. stepn F_1a0dc D_1a0dc.
    stepLD8 F_1a0e0 D_1a0e0 (Z_to_bv 64 0x1a354).
    stepLD8 F_1a0e4 D_1a0e4 (Z_to_bv 64 0x14d24).
    stepn F_1a0e8 D_1a0e8. stepn F_1a0ec D_1a0ec.
    stepLD F_21bb8 D_21bb8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepb_ft F_21bbc D_21bbc ltac:(cond_compute).
    stepret F_21bc0 D_21bc0 (0x1a23c : word) ltac:(bveq).
    stepn F_1a0f0 D_1a0f0.
    stepjr F_1a0f4 D_1a0f4 (Z_to_bv 64 0x1a354) ltac:(gres; reflexivity). vnorm.
    stepjr F_1a208 D_1a208 (Z_to_bv 64 0x14d24) ltac:(gres; reflexivity). vnorm.
    stepn F_14c7c D_14c7c.
    stepLBU F_14c80 D_14c80 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_14c84 D_14c84 ltac:(cond_compute).
    stepret F_14c88 D_14c88 (0x1a244 : word) ltac:(bveq).
    stepn F_1a0f8 D_1a0f8. stepn F_1a0fc D_1a0fc.
    stepn F_21930 D_21930.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_21934 | reflexivity | exact D_21934 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_21938 D_21938 ltac:(cond_compute).
    stepret F_21b28 D_21b28 (0x1a24c : word) ltac:(bveq).
    stepLD F_1a100 D_1a100 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; apply rdn_wbytes_hit4; u_norm; lia) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepn F_1a104 D_1a104.
    stepST F_1a108 D_1a108 (Z_to_bv 64 0x942b8) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_1a10c D_1a10c ltac:(cond_compute).
    stepLD8 F_1a110 D_1a110 (Z_to_bv 64 0x942c8).
    stepn F_1a114 D_1a114.
    stepLD8 F_1a0b4 D_1a0b4 (Z_to_bv 64 0).
    stepn F_1a0b8 D_1a0b8.
    stepST F_1a0bc D_1a0bc (Z_to_bv 64 0x942b8) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_1a0c0 D_1a0c0 (Z_to_bv 64 0x942c0) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_1a0c4 D_1a0c4 ltac:(cond_compute).
    stepn F_1a118 D_1a118.
    stepST F_1a11c D_1a11c (Z_to_bv 64 0x942b0) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_1a120 D_1a120.
    stepLD8 F_1a124 D_1a124 (Z_to_bv 64 0x1a40c).
    stepLD8 F_1a128 D_1a128 code.
    stepLD8 F_1a12c D_1a12c (getr regs 9).
    stepLD8 F_1a130 D_1a130 (getr regs 18).
    stepLD8 F_1a134 D_1a134 (getr regs 19).
    stepn F_1a138 D_1a138. sp_renorm.
    stepn F_1a13c D_1a13c.
    stepLD F_21bb8 D_21bb8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepb_ft F_21bbc D_21bbc ltac:(cond_compute).
    stepret F_21bc0 D_21bc0 (0x1a40c : word) ltac:(bveq).
    stepn F_1a2c0 D_1a2c0.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.

Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x1a410)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x1a38c)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x22e58)))
    (Z_to_bv 64 0x24168) [Z_to_bv 8 1].

Lemma w2 {RCa1 : RunCtx}  : forall regs mem rom (sp code s1v dso : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x1a410 -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22ef8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x22e60)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22f00) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x22e58)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22e58) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1486c)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x24168) 1%nat = Some [Z_to_bv 8 0] ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22ea0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1a28c)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x23f08) 8%nat = Some (word_to_le_bytes 8 dso) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x22ea8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1a35c : word) mem rom)
                 (mkst regs' (0x1c668 : word) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x1a414
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
  intros regs mem rom sp code s1v dso Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mdso Mg2.
  unfold mem_w2. eexists. split.
  -
    stepn F_1a210 D_1a210. rewrite Hsp. sp_renorm.
    stepST F_1a214 D_1a214 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x1a410) ltac:(sok_stack SOK).
    stepST F_1a218 D_1a218 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_1a21c D_1a21c (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    stepn F_1a220 D_1a220.
    stepn F_1a224 D_1a224.
    stepLD8 F_1a228 D_1a228 (Z_to_bv 64 0x22e60).
    stepLD8 F_1a22c D_1a22c (Z_to_bv 64 0x22e58).
    stepb_ft F_1a230 D_1a230 ltac:(cond_compute).
    stepLD8 F_1a234 D_1a234 (Z_to_bv 64 0x1486c).
    stepn F_1a238 D_1a238.
    stepjr F_1a23c D_1a23c (Z_to_bv 64 0x1486c) ltac:(gres; reflexivity). vnorm.
    stepn F_147c4 D_147c4. sp_renorm.
    stepST F_147c8 D_147c8 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x1a38c) ltac:(sok_stack SOK).
    stepST F_147cc D_147cc (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x22e58) ltac:(sok_stack SOK).
    stepn F_147d0 D_147d0.
    stepn F_147d4 D_147d4.
    stepn F_147d8 D_147d8.
    stepLBU F_147dc D_147dc (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
    stepn F_147e0 D_147e0.
    stepb_tk F_147e4 D_147e4 ltac:(cond_compute).
    stepn F_147f0 D_147f0.
    stepn F_147f4 D_147f4.
    stepn F_147f8 D_147f8.
    stepST F_147fc D_147fc (Z_to_bv 64 0x24168) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_14800 D_14800.
    stepLD8 F_14804 D_14804 (Z_to_bv 64 0x1a28c).
    stepb_ft F_14808 D_14808 ltac:(cond_compute).
    stepn F_1480c D_1480c.
    stepn F_14810 D_14810. stepn F_14814 D_14814.
    stepLD8 F_14818 D_14818 dso.
    stepn F_1481c D_1481c.
    stepret F_1a140 D_1a140 (0x148c8 : word) ltac:(bveq).
    stepn F_14820 D_14820.
    stepn F_14824 D_14824.
    stepLD8 F_14828 D_14828 (Z_to_bv 64 0).
    stepb_tk F_1482c D_1482c ltac:(cond_compute).
    stepLD8 F_14844 D_14844 (Z_to_bv 64 0x1a38c).
    stepLD8 F_14848 D_14848 (Z_to_bv 64 0x22e58).
    stepn F_1484c D_1484c. sp_renorm.
    stepret F_14850 D_14850 (0x1a38c : word) ltac:(bveq).
    stepn F_1a240 D_1a240.
    stepb_ft F_1a244 D_1a244 ltac:(cond_compute).
    stepLD8 F_1a248 D_1a248 (Z_to_bv 64 0x1a410).
    stepLD8 F_1a24c D_1a24c code.
    stepLD8 F_1a250 D_1a250 s1v.
    stepn F_1a254 D_1a254. sp_renorm.
    stepn F_1a258 D_1a258.
    stepret F_1a20c D_1a20c (0x1a410 : word) ltac:(bveq).
    stepn F_1a2c4 D_1a2c4.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S0Exit_run1.

Module S0Exit_run2.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Hoare OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.WalkTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StreamSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.MmapSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.LibAtomic OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.U7ExitBase.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.LiaFast.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition mem_w3a (mem : word -> option byte) (sp code : word) :=
  wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x1a414)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 (Z_to_bv 64 0x1c678)))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 code).

Lemma w3a {RCa1 : RunCtx}  : forall regs mem rom (sp code wp1 rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x1a414 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  file_clean mem 0x24020 wp1 rp1 ->
  file_clean mem 0x23f30 wp2 rp2 ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1c668 : word) mem rom)
                 (mkst regs' (0x1a424 : word) (mem_w3a mem sp code) rom)
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
    stepn F_1c51c D_1c51c. rewrite Hsp. sp_renorm.
    stepST F_1c520 D_1c520 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x1a414) ltac:(sok_stack SOK).
    stepST F_1c524 D_1c524 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepn F_1c528 D_1c528.
    stepn F_1c6c0 D_1c6c0. sp_renorm.
    stepST F_1c6c4 D_1c6c4 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x1c678) ltac:(sok_stack SOK).
    stepST F_1c6c8 D_1c6c8 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_1c6cc D_1c6cc.
    stepn F_1c6d0 D_1c6d0.
    stepn F_1c6d4 D_1c6d4.
    stepn F_1c6d8 D_1c6d8.
    stepn F_21930 D_21930.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_21934 | reflexivity | exact D_21934 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_21938 D_21938 ltac:(cond_compute).
    stepret F_21b28 D_21b28 (0x1c828 : word) ltac:(bveq).
    stepn F_1c6dc D_1c6dc.
    stepLD8 F_1c6e0 D_1c6e0 (Z_to_bv 64 0x1c678).
    stepLD8 F_1c6e4 D_1c6e4 code.
    stepn F_1c6e8 D_1c6e8. sp_renorm.
    stepret F_1c6ec D_1c6ec (0x1c678 : word) ltac:(bveq).
    stepLD8 F_1c52c D_1c52c (Z_to_bv 64 0).
    stepb_ft F_1c530 D_1c530 ltac:(cond_compute).
    stepn F_1c534 D_1c534.
    stepLD8 F_1c538 D_1c538 (Z_to_bv 64 0).
    stepb_tk F_1c53c D_1c53c ltac:(cond_compute).
    stepn F_1c590 D_1c590.
    stepLD8 F_1c594 D_1c594 (Z_to_bv 64 0x24020).
    stepb_ft F_1c598 D_1c598 ltac:(cond_compute).
    stepLD F_1c59c D_1c59c (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_1c5a0 D_1c5a0 ltac:(cond_compute).
    stepLD8 F_1c5ac D_1c5ac wp1.
    stepLD8 F_1c5b0 D_1c5b0 wp1.
    stepb_tk F_1c5b4 D_1c5b4 ltac:(apply c_eq_refl).
    stepLD8 F_1c5cc D_1c5cc rp1.
    stepLD8 F_1c5d0 D_1c5d0 rp1.
    stepb_tk F_1c5d4 D_1c5d4 ltac:(apply c_eq_refl).
    stepn F_1c5ec D_1c5ec.
    stepLD8 F_1c5f0 D_1c5f0 (Z_to_bv 64 0x23f30).
    stepb_ft F_1c5f4 D_1c5f4 ltac:(cond_compute).
    stepLD F_1c5f8 D_1c5f8 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_1c5fc D_1c5fc ltac:(cond_compute).
    stepLD8 F_1c608 D_1c608 wp2.
    stepLD8 F_1c60c D_1c60c wp2.
    stepb_tk F_1c610 D_1c610 ltac:(apply c_eq_refl).
    stepLD8 F_1c628 D_1c628 rp2.
    stepLD8 F_1c62c D_1c62c rp2.
    stepb_tk F_1c630 D_1c630 ltac:(apply c_eq_refl).
    stepLD8 F_1c6b0 D_1c6b0 (Z_to_bv 64 0x1a414).
    stepLD8 F_1c6b4 D_1c6b4 code.
    stepn F_1c6b8 D_1c6b8. sp_renorm.
    stepret F_1c6bc D_1c6bc (0x1a414 : word) ltac:(bveq).
    stepn F_1a2c8 D_1a2c8.
    stepn F_1a2cc D_1a2cc.
    stepn F_1a2d0 D_1a2d0.
    stepn F_1a2d4 D_1a2d4.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S0Exit_run2.

Module S0Exit_run3.
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Hoare OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.WalkTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StreamSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.MmapSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.LibAtomic OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.U7ExitBase S0Exit_run2.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.LiaFast.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition stdout_dirty_hdr {RCa1 : RunCtx}  (mem : word -> option byte) (wb wp : Z) : Prop :=
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x24020 + 140)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295))
  /\ rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x24020 + 40)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wp))
  /\ rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x24020 + 56)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))
  /\ rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x24020 + 72)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1c878)).

Lemma w3b1 {RCa1 : RunCtx}  : forall regs mem rom (sp code : word) (wb wp : Z),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x1a414 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  stdio_globals mem ->
  stdout_dirty_hdr mem wb wp ->
  (0 <= wb < 2^64)%Z -> (0 <= wp < 2^64)%Z -> wb <> wp ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1c668 : word) mem rom)
                 (mkst regs' (0x1c878 : word) (mem_w3a mem sp code) rom)
    /\ getr regs' 10 = Z_to_bv 64 0x24020
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 12 = Z_to_bv 64 0
    /\ getr regs' 1 = Z_to_bv 64 0x1c718
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 32)
    /\ getr regs' 8 = Z_to_bv 64 0x24020
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4.
Proof.
  intros regs mem rom sp code wb wp Hsp Hs0 Hra SPlo SPhi SOK
         (Gnl & Gofl & Gin & Gout & Gerr) (F1l & F1wp & F1wb & F1wr) WB WP NE.
  zaddr F1l; zaddr F1wp; zaddr F1wb; zaddr F1wr.
  unfold mem_w3a. eexists. split.
  -
    stepn F_1c51c D_1c51c. rewrite Hsp. sp_renorm.
    stepST F_1c520 D_1c520 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x1a414) ltac:(sok_stack SOK).
    stepST F_1c524 D_1c524 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepn F_1c528 D_1c528.
    stepn F_1c6c0 D_1c6c0. sp_renorm.
    stepST F_1c6c4 D_1c6c4 (Z_to_bv 64 (bv_unsigned sp - 40)) (Z_to_bv 64 0x1c678) ltac:(sok_stack SOK).
    stepST F_1c6c8 D_1c6c8 (Z_to_bv 64 (bv_unsigned sp - 48)) code ltac:(sok_stack SOK).
    stepn F_1c6cc D_1c6cc.
    stepn F_1c6d0 D_1c6d0.
    stepn F_1c6d4 D_1c6d4.
    stepn F_1c6d8 D_1c6d8.
    stepn F_21930 D_21930.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_21934 | reflexivity | exact D_21934 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_21938 D_21938 ltac:(cond_compute).
    stepret F_21b28 D_21b28 (0x1c828 : word) ltac:(bveq).
    stepn F_1c6dc D_1c6dc.
    stepLD8 F_1c6e0 D_1c6e0 (Z_to_bv 64 0x1c678).
    stepLD8 F_1c6e4 D_1c6e4 code.
    stepn F_1c6e8 D_1c6e8. sp_renorm.
    stepret F_1c6ec D_1c6ec (0x1c678 : word) ltac:(bveq).
    stepLD8 F_1c52c D_1c52c (Z_to_bv 64 0).
    stepb_ft F_1c530 D_1c530 ltac:(cond_compute).
    stepn F_1c534 D_1c534.
    stepLD8 F_1c538 D_1c538 (Z_to_bv 64 0).
    stepb_tk F_1c53c D_1c53c ltac:(cond_compute).
    stepn F_1c590 D_1c590.
    stepLD8 F_1c594 D_1c594 (Z_to_bv 64 0x24020).
    stepb_ft F_1c598 D_1c598 ltac:(cond_compute).
    stepLD F_1c59c D_1c59c (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_1c5a0 D_1c5a0 ltac:(cond_compute).
    stepLD8 F_1c5ac D_1c5ac (Z_to_bv 64 wp).
    stepLD8 F_1c5b0 D_1c5b0 (Z_to_bv 64 wb).
    stepb_ft F_1c5b4 D_1c5b4 ltac:(rewrite c_eq_Z by lia; apply Z.eqb_neq; lia).
    stepLD8 F_1c5b8 D_1c5b8 (Z_to_bv 64 0x1c878).
    stepn F_1c5bc D_1c5bc.
    stepn F_1c5c0 D_1c5c0.
    stepn F_1c5c4 D_1c5c4.
    stepjr F_1c5c8 D_1c5c8 (Z_to_bv 64 0x1c878) ltac:(gres; reflexivity). vnorm.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Lemma w3b2 {RCa1 : RunCtx}  : forall regs mem rom (sp code rp1 wp2 rp2 : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 32) -> getr regs 8 = Z_to_bv 64 0x24020 ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 24)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1a414)) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 32)) 8%nat = Some (word_to_le_bytes 8 code) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x24020 + 8)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (0x24020 + 16)) 8%nat = Some (word_to_le_bytes 8 rp1) ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 0x24018) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x23f30)) ->
  file_clean mem 0x23f30 wp2 rp2 ->
  exists regs',
    msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x1c718 : word) mem rom)
                 (mkst regs' (0x1a424 : word) mem rom)
    /\ getr regs' 10 = code
    /\ getr regs' 17 = Z_to_bv 64 94
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16).
Proof.
  intros regs mem rom sp code rp1 wp2 rp2 Hsp Hs0 SPlo SPhi M24 M32 F1rp F1re Gerr
         (F2l & F2wp & F2wb & F2rp & F2re).
  zaddr F1rp; zaddr F1re. zaddr F2l; zaddr F2wp; zaddr F2wb; zaddr F2rp; zaddr F2re.
  eexists. split.
  -
    stepLD8 F_1c5cc D_1c5cc rp1.
    stepLD8 F_1c5d0 D_1c5d0 rp1.
    stepb_tk F_1c5d4 D_1c5d4 ltac:(apply c_eq_refl).
    stepn F_1c5ec D_1c5ec.
    stepLD8 F_1c5f0 D_1c5f0 (Z_to_bv 64 0x23f30).
    stepb_ft F_1c5f4 D_1c5f4 ltac:(cond_compute).
    stepLD F_1c5f8 D_1c5f8 (word_to_le_bytes 4 (Z_to_bv 64 4294967295)) (Z_to_bv 64 4294967295)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_tk F_1c5fc D_1c5fc ltac:(cond_compute).
    stepLD8 F_1c608 D_1c608 wp2.
    stepLD8 F_1c60c D_1c60c wp2.
    stepb_tk F_1c610 D_1c610 ltac:(apply c_eq_refl).
    stepLD8 F_1c628 D_1c628 rp2.
    stepLD8 F_1c62c D_1c62c rp2.
    stepb_tk F_1c630 D_1c630 ltac:(apply c_eq_refl).
    stepLD8 F_1c6b0 D_1c6b0 (Z_to_bv 64 0x1a414).
    stepLD8 F_1c6b4 D_1c6b4 code.
    stepn F_1c6b8 D_1c6b8. rewrite Hsp. sp_renorm.
    stepret F_1c6bc D_1c6bc (0x1a414 : word) ltac:(bveq).
    stepn F_1a2c8 D_1a2c8.
    stepn F_1a2cc D_1a2cc.
    stepn F_1a2d0 D_1a2d0.
    stepn F_1a2d4 D_1a2d4.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End S0Exit_run3.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Hoare OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.WalkTac OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.StreamSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.MmapSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.LibAtomic OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.ExitSim OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.ShapeAlg OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Nodes OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.LibWritev OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.U7StdioDefs S0Exit_run1 S0Exit_run2 S0Exit_run3 OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.U7StdioWrite.S0StdioWrite_run1 OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.U7StdioWrite.S0StdioWrite_run2 OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.U7StdioWrite.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.LiaFast.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac zaddr_rec H := zaddr H.


Theorem ref_exit_clean {RCa1 : RunCtx}  :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 wp1 rp1 : word),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  file_clean mem 0x24020 wp1 rp1 ->
  m_halted model = None -> m_vm_lazy model = [] ->
  realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs (0x1a3a8 : word) mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
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
    eapply rz_exit_at; [exact F_1a2d8 | exact E_1a2d8 | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
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
    eapply rz_exit_at; [exact F_1a2d8 | exact E_1a2d8 | exact Hh | exact Hlazy | left; exact R3a7 | exact R3a0].
Qed.


Theorem ref_exit_flush {RCa1 : RunCtx}  :
  forall regs mem model (sp tp code : word) (tid : Z) (wp2 rp2 : word)
         (wb wp : Z) (bufp bufsz rp1 can : word) (pending : list byte),
  exit_common regs mem sp tp code tid wp2 rp2 ->
  stdout_pending mem wb wp bufp bufsz rp1 can pending ->
  m_halted model = None -> m_vm_lazy model = [] ->
  fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  m_channel_reader model = true ->
  realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs (0x1a3a8 : word) mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
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
    replace (Z_to_bv 64 0x1c718) with (0x1c718 : word) in R3ra by (apply bv_eq; reflexivity).
    unfold W. rewrite <- (app_nil_r pending).
    set (mem3 := mem_w3a (mem_w2 (mem_w1U mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9)) sp code).
    eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) 0x24020 wb wp 1
              (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x1c718 : word) pending []);
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
      eapply rz_exit_at; [exact F_1a2d8 | exact E_1a2d8 | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
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
    replace (Z_to_bv 64 0x1c718) with (0x1c718 : word) in R3ra by (apply bv_eq; reflexivity).
    unfold W. rewrite <- (app_nil_r pending).
    set (mem3 := mem_w3a (mem_w2 (mem_w1R mem sp (getr regs 1) (getr regs 8) tid code (getr regs 9) (getr regs 18) (getr regs 19)) sp code (getr regs1 9)) sp code).
    eapply (ref_stdio_write regs3 mem3 model (bv_unsigned sp - 32) 0x24020 wb wp 1
              (Z_to_bv 64 0) (Z_to_bv 64 0) bufp bufsz can (0x1c718 : word) pending []);
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
      eapply rz_exit_at; [exact F_1a2d8 | exact E_1a2d8 | exact Hh | exact Hlazy | left; exact R5a7 | exact R5a0].
Qed.


Lemma t_emit_nil_exit : forall code fs, t_eq (t_exit code fs) (t_emit [] (t_exit code fs)).
Proof.
  intros code fs. apply t_eq_sym. apply t_emit_nil_eq.
  unfold t_exit, t_emit. left. apply is_prefix_nil.
Qed.

Theorem ref_exit {RCa1 : RunCtx}  : forall regs mem model code pending,
  exit_pre regs mem model code pending ->
  realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs (0x1a3a8 : word) mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
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
  realizes (run_segments RSEGS rc_inp rc_sp rc_mb) (mkCfg (mkst regs (Z_to_bv 64 0x1a3a8) mem (seg_rom (run_segments RSEGS rc_inp rc_sp rc_mb))) model)
           (t_emit (W 1 pending) (t_exit (bv_and code (Z_to_bv 64 255)) (m_fs model))).
Proof.
  intros. replace (Z_to_bv 64 0x1a3a8) with (0x1a3a8 : word) by (apply bv_eq; reflexivity).
  apply ref_exit; assumption.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
