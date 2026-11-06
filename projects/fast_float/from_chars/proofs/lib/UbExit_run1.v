(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec CatSim SeqExec StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require WalkTac StoreOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require WalkTac.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare OSSVerify.Proofs.fast_float.from_chars.lib.Common.WalkTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.StreamSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.MmapSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.WalkTac.LibAtomic.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import UbExitBase UbStdioDefs.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import Ub_code_22780_228cc Ub_code_22cf4_22d24 Ub_code_5233c_52dd8 Ub_code_558d8_56250 Ub_code_60914_60c38.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section WithFP1.
Context {fx : FPState}.
Definition mem_w1 (mem : word -> option byte) (sp ra s0 : word) (tid : Z) :=
  wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 0x97bf8) (word_to_le_bytes 4 (Z_to_bv 64 tid)).

#[using="Type"] Lemma w1 : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0x97bf8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x52be0 : word) mem rom)
                 (mkst regs' (0x529fc : word) (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x52c44
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock.
  unfold mem_w1. eexists. split.
  - (* [comment removed for export] *)
    stepn F_52be0 D_52be0. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_52be4 D_52be4 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_52be8 D_52be8 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_52bec D_52bec.
    stepn F_52bf0 D_52bf0. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_52bf4 D_52bf4 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_52bf8 D_52bf8.
    stepn F_52bfc D_52bfc.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_52c00 | reflexivity | exact D_52c00
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_52c04 | reflexivity | exact D_52c04 | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_52c08 | reflexivity | exact D_52c08
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_52c0c D_52c0c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_52c10 D_52c10.
    (* [comment removed for export] *)
    stepb_ft F_52c14 D_52c14 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_52c18 D_52c18 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_52c3c D_52c3c. rewrite Ha0.
    stepn F_52c40 D_52c40.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mem_wF0 (mem : word -> option byte) (sp code s1v s2v s3v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x52c44)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3v))
    (Z_to_bv 64 0x979d8) [Z_to_bv 8 1].

#[using="Type"] Lemma wF0 : forall regs mem rom (sp code s1v s2v s3v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x52c44 -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x97c23) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x979e8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x979dc) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x529fc : word) mem rom)
                 (mkst regs' (0x52c44 : word) (mem_wF0 mem sp code s1v s2v s3v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs mem rom sp code s1v s2v s3v Hsp Hs0 Hra Hs1 Hs2 Hs3 SPlo SPhi SOK Mnl Mhead Malock.
  unfold mem_wF0. eexists. split.
  - (* [comment removed for export] *)
    stepn F_529fc D_529fc. rewrite Hsp. sp_renorm.
    stepST F_52a00 D_52a00 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x52c44) ltac:(sok_stack SOK).
    stepST F_52a04 D_52a04 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_52a08 D_52a08 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    stepST F_52a0c D_52a0c (Z_to_bv 64 (bv_unsigned sp - 48)) s2v ltac:(sok_stack SOK).
    stepST F_52a10 D_52a10 (Z_to_bv 64 (bv_unsigned sp - 56)) s3v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_52a14 D_52a14.
    stepn F_52a18 D_52a18.
    stepn F_52a1c D_52a1c.
    stepn F_52a20 D_52a20.
    (* [comment removed for export] *)
    stepn F_52a24 D_52a24.
    stepn F_60914 D_60914.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_60918 | reflexivity | exact D_60918 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_6091c D_6091c ltac:(cond_compute).
    stepret F_60b0c D_60b0c (0x52a28 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_52a28 D_52a28 (Z_to_bv 64 0).
    stepb_tk F_52a2c D_52a2c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_52a9c D_52a9c.
    stepST F_52aa0 D_52aa0 (Z_to_bv 64 0x979d8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_52aa4 D_52aa4.
    (* [comment removed for export] *)
    stepLD8 F_52aa8 D_52aa8 (Z_to_bv 64 0x52c44).
    stepLD8 F_52aac D_52aac code.
    stepLD8 F_52ab0 D_52ab0 s1v.
    stepLD8 F_52ab4 D_52ab4 s2v.
    stepLD8 F_52ab8 D_52ab8 s3v.
    stepn F_52abc D_52abc. sp_renorm.
    stepn F_52ac0 D_52ac0.
    (* [comment removed for export] *)
    stepLD F_60b9c D_60b9c (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepb_ft F_60ba0 D_60ba0 ltac:(cond_compute).
    stepret F_60ba4 D_60ba4 (0x52c44 : word) ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.


(* [comment removed for export] *)
Definition mem_wF1 (mem : word -> option byte) (sp code s1v s2v s3v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x52c44)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3v))
    (Z_to_bv 64 0x979e0) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x979e0) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x979e0) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x979e8) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x979d8) [Z_to_bv 8 1].

#[using="Type"] Lemma wF1 : forall regs mem rom (sp code s1v s2v s3v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x52c44 -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x97c23) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x979dc) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x979e8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x979f0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x979e0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn RSEGS mem (Z_to_bv 64 0x979f8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x52b8c)) ->
  rdn RSEGS mem (Z_to_bv 64 0x97af8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x22cf4)) ->
  rdn RSEGS mem (Z_to_bv 64 0x979f0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x76e24) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x529fc : word) mem rom)
                 (mkst regs' (0x52c44 : word) (mem_wF1 mem sp code s1v s2v s3v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs mem rom sp code s1v s2v s3v Hsp Hs0 Hra Hs1 Hs2 Hs3 SPlo SPhi SOK Mnl Malock Mhead Mslot Mf0 Ma0 Mnext Mcb.
  unfold mem_wF1. eexists. split.
  - (* [comment removed for export] *)
    stepn F_529fc D_529fc. rewrite Hsp. sp_renorm.
    stepST F_52a00 D_52a00 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x52c44) ltac:(sok_stack SOK).
    stepST F_52a04 D_52a04 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_52a08 D_52a08 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    stepST F_52a0c D_52a0c (Z_to_bv 64 (bv_unsigned sp - 48)) s2v ltac:(sok_stack SOK).
    stepST F_52a10 D_52a10 (Z_to_bv 64 (bv_unsigned sp - 56)) s3v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_52a14 D_52a14.
    stepn F_52a18 D_52a18.
    stepn F_52a1c D_52a1c.
    stepn F_52a20 D_52a20.
    (* [comment removed for export] *)
    stepn F_52a24 D_52a24.
    stepn F_60914 D_60914.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_60918 | reflexivity | exact D_60918 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_6091c D_6091c ltac:(cond_compute).
    stepret F_60b0c D_60b0c (0x52a28 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_52a28 D_52a28 (Z_to_bv 64 0x979f0).
    stepb_ft F_52a2c D_52a2c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_52a30 D_52a30 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 1) by lia.
    stepn F_52a34 D_52a34.
    (* [comment removed for export] *)
    stepn F_52a4c D_52a4c.
    stepST F_52a50 D_52a50 (Z_to_bv 64 0x979e0) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_52a54 D_52a54 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_52a58 D_52a58 (Z_to_bv 64 0x979f0).
    stepn F_52a5c D_52a5c.
    stepn F_52a60 D_52a60.
    stepLD8 F_52a64 D_52a64 (Z_to_bv 64 0x52b8c).
    stepLD8 F_52a68 D_52a68 (Z_to_bv 64 0x22cf4).
    stepn F_52a6c D_52a6c.
    (* [comment removed for export] *)
    stepn F_52a70 D_52a70.
    stepLD F_60b9c D_60b9c (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepb_ft F_60ba0 D_60ba0 ltac:(cond_compute).
    stepret F_60ba4 D_60ba4 (0x52a74 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_52a74 D_52a74.
    stepjr F_52a78 D_52a78 (Z_to_bv 64 0x52b8c) ltac:(gres; reflexivity). vnorm.
    stepjr F_52b8c D_52b8c (Z_to_bv 64 0x22cf4) ltac:(gres; reflexivity). vnorm.
    (* [comment removed for export] *)
    stepn F_22cf4 D_22cf4.
    stepLBU F_22cf8 D_22cf8 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_22cfc D_22cfc ltac:(cond_compute).
    stepret F_22d00 D_22d00 (0x52a7c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_52a7c D_52a7c.
    stepn F_52a80 D_52a80.
    stepn F_60914 D_60914.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_60918 | reflexivity | exact D_60918 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_6091c D_6091c ltac:(cond_compute).
    stepret F_60b0c D_60b0c (0x52a84 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD F_52a84 D_52a84 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solvew) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepn F_52a88 D_52a88.
    stepST F_52a8c D_52a8c (Z_to_bv 64 0x979e0) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_52a90 D_52a90 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_52a94 D_52a94 (Z_to_bv 64 0x979f0).
    stepn F_52a98 D_52a98.
    stepLD8 F_52a38 D_52a38 (Z_to_bv 64 0).
    (* [comment removed for export] *)
    stepn F_52a3c D_52a3c.
    stepST F_52a40 D_52a40 (Z_to_bv 64 0x979e0) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_52a44 D_52a44 (Z_to_bv 64 0x979e8) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_52a48 D_52a48 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_52a9c D_52a9c.
    stepST F_52aa0 D_52aa0 (Z_to_bv 64 0x979d8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_52aa4 D_52aa4.
    (* [comment removed for export] *)
    stepLD8 F_52aa8 D_52aa8 (Z_to_bv 64 0x52c44).
    stepLD8 F_52aac D_52aac code.
    stepLD8 F_52ab0 D_52ab0 s1v.
    stepLD8 F_52ab4 D_52ab4 s2v.
    stepLD8 F_52ab8 D_52ab8 s3v.
    stepn F_52abc D_52abc. sp_renorm.
    stepn F_52ac0 D_52ac0.
    (* [comment removed for export] *)
    stepLD F_60b9c D_60b9c (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepb_ft F_60ba0 D_60ba0 ltac:(cond_compute).
    stepret F_60ba4 D_60ba4 (0x52c44 : word) ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.


(* [comment removed for export] *)
Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x52c48)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x52bc4)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x628d0)))
    (Z_to_bv 64 0x66e18) [Z_to_bv 8 1].

#[using="Type"] Lemma w2 : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x65b60) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x628d8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x65b68) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x628d0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x628d0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2283c)) ->
  rdn RSEGS mem (Z_to_bv 64 0x66e18) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x65a48) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x52ac4)) ->
  rdn RSEGS mem (Z_to_bv 64 0x65a50) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x52c44 : word) mem rom)
                 (mkst regs' (0x559a8 : word) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x52c4c
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs mem rom sp code s1v Hsp Hs0 Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2.
  (* [comment removed for export] *)
  destruct (rdn_dso (mem_w2 mem sp code s1v)) as (dbs & Hdso & Hlen). unfold mem_w2 in Hdso.
  unfold mem_w2. eexists. split.
  - (* [comment removed for export] *)
    stepn F_52c44 D_52c44.
    stepn F_52b94 D_52b94. rewrite Hsp. sp_renorm.
    stepST F_52b98 D_52b98 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x52c48) ltac:(sok_stack SOK).
    stepST F_52b9c D_52b9c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_52ba0 D_52ba0 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_52ba4 D_52ba4.
    stepn F_52ba8 D_52ba8.
    stepLD8 F_52bac D_52bac (Z_to_bv 64 0x628d8).
    stepLD8 F_52bb0 D_52bb0 (Z_to_bv 64 0x628d0).
    (* [comment removed for export] *)
    stepb_ft F_52bb4 D_52bb4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_52bb8 D_52bb8 (Z_to_bv 64 0x2283c).
    stepn F_52bbc D_52bbc.
    stepjr F_52bc0 D_52bc0 (Z_to_bv 64 0x2283c) ltac:(gres; reflexivity). vnorm.
    (* [comment removed for export] *)
    stepn F_2283c D_2283c. sp_renorm.
    stepST F_22840 D_22840 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x52bc4) ltac:(sok_stack SOK).
    stepST F_22844 D_22844 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x628d0) ltac:(sok_stack SOK).
    stepn F_22848 D_22848.
    (* [comment removed for export] *)
    stepn F_2284c D_2284c.
    stepn F_22850 D_22850.
    stepLBU F_22854 D_22854 (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
    stepn F_22858 D_22858.
    stepb_tk F_2285c D_2285c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_22868 D_22868.
    stepn F_2286c D_2286c.
    stepn F_22870 D_22870.
    stepST F_22874 D_22874 (Z_to_bv 64 0x66e18) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_22878 D_22878.
    stepLD8 F_2287c D_2287c (Z_to_bv 64 0x52ac4).
    stepb_ft F_22880 D_22880 ltac:(cond_compute).
    stepn F_22884 D_22884.
    (* [comment removed for export] *)
    stepn F_22888 D_22888.
    stepn F_2288c D_2288c.
    stepLD F_22890 D_22890 dbs (Z_to_bv 64 (bytes_le_to_Z dbs))
      ltac:(addr_norm; exact Hdso)
      ltac:(symmetry; apply u_Z2bv; [apply bytes_le_to_Z_nonneg | pose proof (bytes_le_to_Z_bound dbs) as Hbd; rewrite Hlen in Hbd; exact Hbd]).
    (* [comment removed for export] *)
    stepn F_22894 D_22894.
    stepret F_52ac4 D_52ac4 (0x22898 : word) ltac:(bveq).
    stepn F_22898 D_22898.
    (* [comment removed for export] *)
    stepn F_2289c D_2289c.
    stepLD8 F_228a0 D_228a0 (Z_to_bv 64 0).
    stepb_tk F_228a4 D_228a4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_228bc D_228bc (Z_to_bv 64 0x52bc4).
    stepLD8 F_228c0 D_228c0 (Z_to_bv 64 0x628d0).
    stepn F_228c4 D_228c4. sp_renorm.
    stepret F_228c8 D_228c8 (0x52bc4 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_52bc4 D_52bc4.
    stepb_ft F_52bc8 D_52bc8 ltac:(cond_compute).
    stepLD8 F_52bcc D_52bcc (Z_to_bv 64 0x52c48).
    stepLD8 F_52bd0 D_52bd0 code.
    stepLD8 F_52bd4 D_52bd4 s1v.
    stepn F_52bd8 D_52bd8. sp_renorm.
    (* [comment removed for export] *)
    stepn F_52bdc D_52bdc.
    stepret F_52b90 D_52b90 (0x52c48 : word) ltac:(bveq).
    stepn F_52c48 D_52c48.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xrel (sp : word) (mem mem' : word -> option byte) : Prop :=
  mem_grows mem mem' /\
  forall a : word, ~ (bv_unsigned sp - 144 <= bv_unsigned a < bv_unsigned sp)%Z ->
                   ~ (0x979d8 <= bv_unsigned a < 0x979f0)%Z ->
                   ~ (0x97bf8 <= bv_unsigned a < 0x97bfc)%Z -> mem' a = mem a.

#[using="Type"] Lemma wbytes_out : forall bs m (a x : word),
  (bv_unsigned a + Z.of_nat (length bs) <= 2^64)%Z ->
  ~ (bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs))%Z ->
  wbytes m a bs x = m x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros bs m a x Hnw Hx.
  destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned a)) as [Hl|Hg].
  - apply wbytes_below; assumption.
  - apply wbytes_above. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma xrel_rdn : forall sp mem mem' (z : Z) n bs,
  xrel sp mem mem' -> rdn RSEGS mem (Z_to_bv 64 z) n = Some bs ->
  (0 <= z)%Z -> (z + Z.of_nat n <= 2^64)%Z ->
  (z + Z.of_nat n <= bv_unsigned sp - 144 \/ bv_unsigned sp <= z)%Z ->
  (z + Z.of_nat n <= 0x979d8 \/ 0x979f0 <= z)%Z ->
  (z + Z.of_nat n <= 0x97bf8 \/ 0x97bfc <= z)%Z ->
  rdn RSEGS mem' (Z_to_bv 64 z) n = Some bs.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros sp mem mem' z n bs [_ HX] H Hz Hn D1 D2 D3.
  destruct n as [|n]; [cbn [rdn] in H |- *; exact H|].
  assert (Hz' : (z < 2^64)%Z) by lia.
  rewrite (rdn_ext RSEGS (S n) mem' mem (Z_to_bv 64 z)); [exact H | u_norm; lia |].
  intros x Hx. revert Hx. u_norm. intros Hx. apply HX; lia.
Qed.

#[using="Type"] Lemma xrel_sok : forall sp mem mem' a n, xrel sp mem mem' ->
  store_ok RSEGS mem a n = true -> store_ok RSEGS mem' a n = true.
Proof. LiaFast.lf_pins LiaFast.u0. intros sp mem mem' a n [HG _] H. exact (store_ok_mono _ _ _ _ _ HG H). Qed.

Ltac xrel_grows := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
Ltac xrel_out := repeat (rewrite wbytes_out; [ | zsimp; lia | zsimp; lia ]); reflexivity.

#[using="Type"] Lemma wF0_xrel : forall mem (sp ra s0 code s1v s2v s3v : word) (tid : Z),
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z -> (0 < tid < 2147483648)%Z ->
  xrel sp mem (mem_wF0 (mem_w1 mem sp ra s0 tid) sp code s1v s2v s3v).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem sp ra s0 code s1v s2v s3v tid SPlo SPhi TID. unfold mem_wF0, mem_w1. split.
  - xrel_grows.
  - intros a H1 H2 H3. pose proof (u64_range a). xrel_out.
Qed.

#[using="Type"] Lemma wF1_xrel : forall mem (sp ra s0 code s1v s2v s3v : word) (tid : Z),
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z -> (0 < tid < 2147483648)%Z ->
  xrel sp mem (mem_wF1 (mem_w1 mem sp ra s0 tid) sp code s1v s2v s3v).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem sp ra s0 code s1v s2v s3v tid SPlo SPhi TID. unfold mem_wF1, mem_w1. split.
  - xrel_grows.
  - intros a H1 H2 H3. pose proof (u64_range a). xrel_out.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma w1F : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0x97bf8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x97c23) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x979dc) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  (atx_idle mem \/ atx_reg mem) ->
  exists regs' mem',
    msteps RSEGS (mkst regs (0x52be0 : word) mem rom) (mkst regs' (0x52c44 : word) mem' rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 9 = getr regs 9
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3
    /\ xrel sp mem mem'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Malock ATX.
  destruct (w1 regs mem rom sp tp code tid) as (regs1 & RUN1 & R1sp & R1s0 & R1ra & R1tp & R1gp & R1s1 & R1s2 & R1s3); try assumption.
  assert (SOK1 : store_ok RSEGS (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true)
    by (unfold mem_w1; store_ok_peel; exact SOK).
  destruct ATX as [AI | (ARh & ARs & ARf & ARa & ARn & ARc)].
  - (* [comment removed for export] *)
    unfold atx_idle in AI.
    destruct (wF0 regs1 (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) rom sp code (getr regs1 9) (getr regs1 18) (getr regs1 19))
      as (regs2 & RUN2 & R2sp & R2s0 & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
    all: try (unfold mem_w1; rdn_solve).
    exists regs2, (mem_wF0 (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) sp code (getr regs1 9) (getr regs1 18) (getr regs1 19)).
    split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|].
    rewrite R1s1 in R2s1. rewrite R1tp in R2tp. rewrite R1gp in R2gp.
    split; [exact R2sp|]. split; [exact R2s0|]. split; [exact R2s1|]. split; [exact R2tp|]. split; [exact R2gp|].
    apply wF0_xrel; assumption.
  - (* [comment removed for export] *)
    destruct (wF1 regs1 (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) rom sp code (getr regs1 9) (getr regs1 18) (getr regs1 19))
      as (regs2 & RUN2 & R2sp & R2s0 & R2s1 & R2tp & R2gp); try assumption; try reflexivity.
    all: try (unfold mem_w1; rdn_solve).
    exists regs2, (mem_wF1 (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) sp code (getr regs1 9) (getr regs1 18) (getr regs1 19)).
    split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|].
    rewrite R1s1 in R2s1. rewrite R1tp in R2tp. rewrite R1gp in R2gp.
    split; [exact R2sp|]. split; [exact R2s0|]. split; [exact R2s1|]. split; [exact R2tp|]. split; [exact R2gp|].
    apply wF1_xrel; assumption.
Qed.

End WithFP1.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
