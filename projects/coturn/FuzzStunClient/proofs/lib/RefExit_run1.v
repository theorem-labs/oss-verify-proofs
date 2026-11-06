(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import LibAtomic RefExitBase Ref_code_13894_14104 Ref_code_1b104_1c2fc Ref_code_1d2fc_1e5f0 Ref_code_235f0_2427c.
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
Definition mem_w1 (mem : word -> option byte) (sp ra s0 code s1 s2 s3 : word) (tid : Z) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 0x56a18) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x1bb5c)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3))
    (Z_to_bv 64 0x567f8) [Z_to_bv 8 1].

Lemma w1 : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0x56a18) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x56a3b) 1%nat = Some [Z_to_bv 8 0] ->                              (* [comment removed for export] *)
  rdn RSEGS mem (Z_to_bv 64 0x56808) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->        (* [comment removed for export] *)
  rdn RSEGS mem (Z_to_bv 64 0x567fc) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->        (* [comment removed for export] *)
  exists regs',
    msteps RSEGS (mkst regs (0x1baf8 : word) mem rom)
                 (mkst regs' (0x1baac : word) (mem_w1 mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x1bb60
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Mhd Mlk.
  unfold mem_w1. eexists. split.
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
    stepLD8 F_1b940 D_1b940 (Z_to_bv 64 0).
    stepb_tk F_1b944 D_1b944 ltac:(cond_compute).
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
Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x1bb60)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x1badc)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x25288)))
    (Z_to_bv 64 0x26688) [Z_to_bv 8 1].

Lemma w2 : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x1bb60 -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x25328) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x25290)) ->
  rdn RSEGS mem (Z_to_bv 64 0x25330) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x25288)) ->
  rdn RSEGS mem (Z_to_bv 64 0x25288) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x13950)) ->
  rdn RSEGS mem (Z_to_bv 64 0x26688) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x252d0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1b9dc)) ->   (* [comment removed for export] *)
  rdn RSEGS mem (Z_to_bv 64 0x252d8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x26338) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x26338)) ->   (* [comment removed for export] *)
  exists regs',
    msteps RSEGS (mkst regs (0x1baac : word) mem rom)
                 (mkst regs' (0x1dd84 : word) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x1bb64
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2 Mdso.
  unfold mem_w2. eexists. split.
  - (* [comment removed for export] *)
    stepn F_1baac D_1baac. rewrite Hsp. sp_renorm.
    stepST F_1bab0 D_1bab0 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x1bb60) ltac:(sok_stack SOK).
    stepST F_1bab4 D_1bab4 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_1bab8 D_1bab8 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_1babc D_1babc.
    stepn F_1bac0 D_1bac0.
    stepLD8 F_1bac4 D_1bac4 (Z_to_bv 64 0x25290).
    stepLD8 F_1bac8 D_1bac8 (Z_to_bv 64 0x25288).
    (* [comment removed for export] *)
    stepb_ft F_1bacc D_1bacc ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_1bad0 D_1bad0 (Z_to_bv 64 0x13950).
    stepn F_1bad4 D_1bad4.
    stepjr F_1bad8 D_1bad8 (Z_to_bv 64 0x13950) ltac:(gres; reflexivity). vnorm.
    (* [comment removed for export] *)
    stepn F_13950 D_13950. sp_renorm.
    stepST F_13954 D_13954 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x1badc) ltac:(sok_stack SOK).
    stepST F_13958 D_13958 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x25288) ltac:(sok_stack SOK).
    stepn F_1395c D_1395c.
    stepn F_13960 D_13960.
    stepn F_13964 D_13964.
    (* [comment removed for export] *)
    stepLBU F_13968 D_13968 (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
    stepn F_1396c D_1396c.
    stepb_tk F_13970 D_13970 ltac:(cond_compute).
    stepn F_1397c D_1397c.
    stepn F_13980 D_13980.
    stepn F_13984 D_13984.
    (* [comment removed for export] *)
    stepST F_13988 D_13988 (Z_to_bv 64 0x26688) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_1398c D_1398c.
    stepLD8 F_13990 D_13990 (Z_to_bv 64 0x1b9dc).
    stepb_ft F_13994 D_13994 ltac:(cond_compute).
    stepn F_13998 D_13998.
    stepn F_1399c D_1399c.
    stepn F_139a0 D_139a0.
    stepLD8 F_139a4 D_139a4 (Z_to_bv 64 0x26338).
    stepn F_139a8 D_139a8.
    stepret F_1b9dc D_1b9dc (0x139ac : word) ltac:(bveq).
    stepn F_139ac D_139ac.
    (* [comment removed for export] *)
    stepn F_139b0 D_139b0.
    stepLD8 F_139b4 D_139b4 (Z_to_bv 64 0).
    stepb_tk F_139b8 D_139b8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_139d0 D_139d0 (Z_to_bv 64 0x1badc).
    stepLD8 F_139d4 D_139d4 (Z_to_bv 64 0x25288).
    stepn F_139d8 D_139d8. sp_renorm.
    stepret F_139dc D_139dc (0x1badc : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_1badc D_1badc.
    stepb_ft F_1bae0 D_1bae0 ltac:(cond_compute).
    stepLD8 F_1bae4 D_1bae4 (Z_to_bv 64 0x1bb60).
    stepLD8 F_1bae8 D_1bae8 code.
    stepLD8 F_1baec D_1baec s1v.
    stepn F_1baf0 D_1baf0. sp_renorm.
    (* [comment removed for export] *)
    stepn F_1baf4 D_1baf4.
    stepret F_1baa8 D_1baa8 (0x1bb60 : word) ltac:(bveq).
    stepn F_1bb60 D_1bb60.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
