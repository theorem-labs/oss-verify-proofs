(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import LibAtomic UbExitBase Ub_code_1b104_1c2fc Ub_code_235f0_245f0 Ub_code_exitx.
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
  rdn RSEGS mem (Z_to_bv 64 0x56cb8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x56cc0))
  /\ rdn RSEGS mem (Z_to_bv 64 0x56cb0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1))
  /\ rdn RSEGS mem (Z_to_bv 64 0x56cc0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
  /\ rdn RSEGS mem (Z_to_bv 64 0x56cc8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1bf4c))
  /\ rdn RSEGS mem (Z_to_bv 64 0x56dc8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13ee8))
  /\ rdn RSEGS mem (Z_to_bv 64 0x36b44) 1%nat = Some [Z_to_bv 8 0].

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
    (Z_to_bv 64 0x56ec8) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x1c004)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3))
    (Z_to_bv 64 0x56cb0) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x56cb0) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x56cb0) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x56cb8) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x56ca8) [Z_to_bv 8 1].

Lemma w1x : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0x56ec8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x56eeb) 1%nat = Some [Z_to_bv 8 0] ->                              (* [comment removed for export] *)
  rdn RSEGS mem (Z_to_bv 64 0x56cac) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->        (* [comment removed for export] *)
  atexit_one mem ->
  exists regs',
    msteps RSEGS (mkst regs (0x1bfa0 : word) mem rom)
                 (mkst regs' (0x1bf54 : word) (mem_w1x mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x1c008
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Mlk
    (Mhd & Msl & Mnx & Mf0 & Ma0 & Mcb).
  unfold mem_w1x. eexists. split.
  - (* [comment removed for export] *)
    stepn F_1bfa0 D_1bfa0. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_1bfa4 D_1bfa4 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_1bfa8 D_1bfa8 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_1bfac D_1bfac.
    stepn F_1bfb0 D_1bfb0. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_1bfb4 D_1bfb4 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_1bfb8 D_1bfb8.
    stepn F_1bfbc D_1bfbc.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_1bfc0 | reflexivity | exact D_1bfc0
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_1bfc4 | reflexivity | exact D_1bfc4 | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_1bfc8 | reflexivity | exact D_1bfc8
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_1bfcc D_1bfcc ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_1bfd0 D_1bfd0.
    (* [comment removed for export] *)
    stepb_ft F_1bfd4 D_1bfd4 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_1bfd8 D_1bfd8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_1bffc D_1bffc. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_1c000 D_1c000.
    (* [comment removed for export] *)
    stepn F_1bdbc D_1bdbc. sp_renorm.
    stepST F_1bdc0 D_1bdc0 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x1c004) ltac:(sok_stack SOK).
    stepST F_1bdc4 D_1bdc4 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_1bdc8 D_1bdc8 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_1bdcc D_1bdcc (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_1bdd0 D_1bdd0 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_1bdd4 D_1bdd4.
    stepn F_1bdd8 D_1bdd8.
    stepn F_1bddc D_1bddc.
    stepn F_1bde0 D_1bde0.
    (* [comment removed for export] *)
    stepn F_1bde4 D_1bde4.
    stepn F_24228 D_24228.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_2422c | reflexivity | exact D_2422c | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_24230 D_24230 ltac:(cond_compute).
    stepret F_24420 D_24420 (0x1bde8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_1bde8 D_1bde8 (Z_to_bv 64 0x56cc0).
    stepb_ft F_1bdec D_1bdec ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_1bdf0 D_1bdf0 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepn F_1bdf4 D_1bdf4.
    (* [comment removed for export] *)
    stepn F_1be0c D_1be0c.
    stepST F_1be10 D_1be10 (Z_to_bv 64 0x56cb0) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_1be14 D_1be14 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_1be18 D_1be18 (Z_to_bv 64 0x56cc0).
    stepn F_1be1c D_1be1c.
    stepn F_1be20 D_1be20.
    stepLD8 F_1be24 D_1be24 (Z_to_bv 64 0x1bf4c).
    stepLD8 F_1be28 D_1be28 (Z_to_bv 64 0x13ee8).
    (* [comment removed for export] *)
    stepn F_1be2c D_1be2c.
    stepn F_1be30 D_1be30.
    stepLD F_244b0 D_244b0 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_244b4 D_244b4 ltac:(cond_compute).
    stepret F_244b8 D_244b8 (0x1be34 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_1be34 D_1be34.
    stepjr F_1be38 D_1be38 (Z_to_bv 64 0x1bf4c) ltac:(gres; reflexivity). vnorm.
    stepjr F_1bf4c D_1bf4c (Z_to_bv 64 0x13ee8) ltac:(gres; reflexivity). vnorm.
    (* [comment removed for export] *)
    stepn F_13ee8 D_13ee8.
    stepLBU F_13eec D_13eec (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_13ef0 D_13ef0 ltac:(cond_compute).
    stepret F_13ef4 D_13ef4 (0x1be3c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_1be3c D_1be3c.
    stepn F_1be40 D_1be40.
    stepn F_24228 D_24228.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_2422c | reflexivity | exact D_2422c | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_24230 D_24230 ltac:(cond_compute).
    stepret F_24420 D_24420 (0x1be44 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD F_1be44 D_1be44 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; apply rdn_hit4; zsimp; lia) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepn F_1be48 D_1be48.
    stepST F_1be4c D_1be4c (Z_to_bv 64 0x56cb0) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_1be50 D_1be50 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_1be54 D_1be54 (Z_to_bv 64 0x56cc0).
    stepn F_1be58 D_1be58.
    stepLD8 F_1bdf8 D_1bdf8 (Z_to_bv 64 0).
    stepn F_1bdfc D_1bdfc.
    stepST F_1be00 D_1be00 (Z_to_bv 64 0x56cb0) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_1be04 D_1be04 (Z_to_bv 64 0x56cb8) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_1be08 D_1be08 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_1be5c D_1be5c.
    stepST F_1be60 D_1be60 (Z_to_bv 64 0x56ca8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_1be64 D_1be64.
    stepLD8 F_1be68 D_1be68 (Z_to_bv 64 0x1c004).
    stepLD8 F_1be6c D_1be6c code.
    stepLD8 F_1be70 D_1be70 (getr regs 9).
    stepLD8 F_1be74 D_1be74 (getr regs 18).
    stepLD8 F_1be78 D_1be78 (getr regs 19).
    stepn F_1be7c D_1be7c. sp_renorm.
    (* [comment removed for export] *)
    stepn F_1be80 D_1be80.
    stepLD F_244b0 D_244b0 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_244b4 D_244b4 ltac:(cond_compute).
    stepret F_244b8 D_244b8 (0x1c004 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_1c004 D_1c004.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
