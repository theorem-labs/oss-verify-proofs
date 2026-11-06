(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import LibAtomic RefExitBase Ref_code_1b104_1c2fc Ref_code_235f0_2427c Ref_code_exitx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition atexit_one (mem : word -> option byte) : Prop :=
  rdn RSEGS mem (Z_to_bv 64 0x56808) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x56810))
  /\ rdn RSEGS mem (Z_to_bv 64 0x56800) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1))
  /\ rdn RSEGS mem (Z_to_bv 64 0x56810) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn RSEGS mem (Z_to_bv 64 0x56818) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1baa4))
  /\ rdn RSEGS mem (Z_to_bv 64 0x56918) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13e08))
  /\ rdn RSEGS mem (Z_to_bv 64 0x36694) 1%nat = Some [Z_to_bv 8 0].

(* [comment removed for export] *)
Lemma rdn_hit4 : forall segs m (a v : word),
  (bv_unsigned a + 4 <= 2^64)%Z ->
  rdn segs (wbytes m a (word_to_le_bytes 4 v)) a 4%nat = Some (word_to_le_bytes 4 v).
Proof.
  intros segs m a v Hnw.
  pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 v) m a) as H.
  rewrite length_N_to_le_bytes in H. apply H. exact Hnw.
Qed.

(* [comment removed for export] *)
Definition mem_w1x (mem : word -> option byte) (sp ra s0 code s1 s2 s3 : word) (tid : Z) :=
  wbytes (wbytes (wbytes (wbytes (wbytes
  (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 0x56a18) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x1bb5c)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3))
    (Z_to_bv 64 0x56800) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x56800) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x56800) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x56808) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x567f8) [Z_to_bv 8 1].

Lemma w1x : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0x56a18) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x56a3b) 1%nat = Some [Z_to_bv 8 0] ->                              (* [comment removed for export] *)
  rdn RSEGS mem (Z_to_bv 64 0x567fc) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->        (* [comment removed for export] *)
  atexit_one mem ->
  exists regs',
    msteps RSEGS (mkst regs (0x1baf8 : word) mem rom)
                 (mkst regs' (0x1baac : word) (mem_w1x mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x1bb60
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Mlk
    (Mhd & Msl & Mnx & Mf0 & Ma0 & Mcb).
  unfold mem_w1x. eexists. split.
  - (* [comment removed for export] *)
    stepn F_1baf8 D_1baf8. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_1bafc D_1bafc (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_1bb00 D_1bb00 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_1bb04 D_1bb04.
    stepn F_1bb08 D_1bb08. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_1bb0c D_1bb0c (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_1bb10 D_1bb10.
    stepn F_1bb14 D_1bb14.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_1bb18 | reflexivity | exact D_1bb18
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_1bb1c | reflexivity | exact D_1bb1c | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_1bb20 | reflexivity | exact D_1bb20
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_1bb24 D_1bb24 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_1bb28 D_1bb28.
    (* [comment removed for export] *)
    stepb_ft F_1bb2c D_1bb2c ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_1bb30 D_1bb30 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_1bb54 D_1bb54. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_1bb58 D_1bb58.
    (* [comment removed for export] *)
    stepn F_1b914 D_1b914. sp_renorm.
    stepST F_1b918 D_1b918 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x1bb5c) ltac:(sok_stack SOK).
    stepST F_1b91c D_1b91c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_1b920 D_1b920 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_1b924 D_1b924 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_1b928 D_1b928 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_1b92c D_1b92c.
    stepn F_1b930 D_1b930.
    stepn F_1b934 D_1b934.
    stepn F_1b938 D_1b938.
    (* [comment removed for export] *)
    stepn F_1b93c D_1b93c.
    stepn F_23d80 D_23d80.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_23d84 | reflexivity | exact D_23d84 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_23d88 D_23d88 ltac:(cond_compute).
    stepret F_23f78 D_23f78 (0x1b940 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_1b940 D_1b940 (Z_to_bv 64 0x56810).
    stepb_ft F_1b944 D_1b944 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_1b948 D_1b948 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepn F_1b94c D_1b94c.
    (* [comment removed for export] *)
    stepn F_1b964 D_1b964.
    stepST F_1b968 D_1b968 (Z_to_bv 64 0x56800) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_1b96c D_1b96c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_1b970 D_1b970 (Z_to_bv 64 0x56810).
    stepn F_1b974 D_1b974.
    stepn F_1b978 D_1b978.
    stepLD8 F_1b97c D_1b97c (Z_to_bv 64 0x1baa4).
    stepLD8 F_1b980 D_1b980 (Z_to_bv 64 0x13e08).
    (* [comment removed for export] *)
    stepn F_1b984 D_1b984.
    stepn F_1b988 D_1b988.
    stepLD F_24008 D_24008 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_2400c D_2400c ltac:(cond_compute).
    stepret F_24010 D_24010 (0x1b98c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_1b98c D_1b98c.
    stepjr F_1b990 D_1b990 (Z_to_bv 64 0x1baa4) ltac:(gres; reflexivity). vnorm.
    stepjr F_1baa4 D_1baa4 (Z_to_bv 64 0x13e08) ltac:(gres; reflexivity). vnorm.
    (* [comment removed for export] *)
    stepn F_13e08 D_13e08.
    stepLBU F_13e0c D_13e0c (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_13e10 D_13e10 ltac:(cond_compute).
    stepret F_13e14 D_13e14 (0x1b994 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_1b994 D_1b994.
    stepn F_1b998 D_1b998.
    stepn F_23d80 D_23d80.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_23d84 | reflexivity | exact D_23d84 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_23d88 D_23d88 ltac:(cond_compute).
    stepret F_23f78 D_23f78 (0x1b99c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD F_1b99c D_1b99c (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; apply rdn_hit4; zsimp; lia) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepn F_1b9a0 D_1b9a0.
    stepST F_1b9a4 D_1b9a4 (Z_to_bv 64 0x56800) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_1b9a8 D_1b9a8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_1b9ac D_1b9ac (Z_to_bv 64 0x56810).
    stepn F_1b9b0 D_1b9b0.
    stepLD8 F_1b950 D_1b950 (Z_to_bv 64 0).
    stepn F_1b954 D_1b954.
    stepST F_1b958 D_1b958 (Z_to_bv 64 0x56800) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_1b95c D_1b95c (Z_to_bv 64 0x56808) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_1b960 D_1b960 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_1b9b4 D_1b9b4.
    stepST F_1b9b8 D_1b9b8 (Z_to_bv 64 0x567f8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_1b9bc D_1b9bc.
    stepLD8 F_1b9c0 D_1b9c0 (Z_to_bv 64 0x1bb5c).
    stepLD8 F_1b9c4 D_1b9c4 code.
    stepLD8 F_1b9c8 D_1b9c8 (getr regs 9).
    stepLD8 F_1b9cc D_1b9cc (getr regs 18).
    stepLD8 F_1b9d0 D_1b9d0 (getr regs 19).
    stepn F_1b9d4 D_1b9d4. sp_renorm.
    (* [comment removed for export] *)
    stepn F_1b9d8 D_1b9d8.
    stepLD F_24008 D_24008 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_2400c D_2400c ltac:(cond_compute).
    stepret F_24010 D_24010 (0x1bb5c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_1bb5c D_1bb5c.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
