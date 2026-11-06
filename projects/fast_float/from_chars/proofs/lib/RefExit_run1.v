(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec CatExec CatSim SeqExec StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require WalkTac StoreOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require WalkTac.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare OSSVerify.Proofs.fast_float.from_chars.lib.Common.WalkTac OSSVerify.Proofs.fast_float.from_chars.lib.Common.StoreOk OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.StreamSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.MmapSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.WalkTac.LibAtomic.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import RefExitBase RefStdioDefs.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import Ref_code_224ec_22638 Ref_code_22a60_22a90 Ref_code_50584_51020 Ref_code_53b20_54498 Ref_code_5eb5c_5ee80.
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
    (Z_to_bv 64 0x95e38) (word_to_le_bytes 4 (Z_to_bv 64 tid)).

#[using="Type"] Lemma w1 : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0x95e38) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x50e28 : word) mem rom)
                 (mkst regs' (0x50c44 : word) (mem_w1 mem sp (getr regs 1) (getr regs 8) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x50e8c
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9
    /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock.
  unfold mem_w1. eexists. split.
  - (* [comment removed for export] *)
    stepn F_50e28 D_50e28. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_50e2c D_50e2c (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_50e30 D_50e30 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_50e34 D_50e34.
    stepn F_50e38 D_50e38. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_50e3c D_50e3c (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_50e40 D_50e40.
    stepn F_50e44 D_50e44.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_50e48 | reflexivity | exact D_50e48
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_50e4c | reflexivity | exact D_50e4c | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_50e50 | reflexivity | exact D_50e50
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_50e54 D_50e54 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_50e58 D_50e58.
    (* [comment removed for export] *)
    stepb_ft F_50e5c D_50e5c ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_50e60 D_50e60 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_50e84 D_50e84. rewrite Ha0.
    stepn F_50e88 D_50e88.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mem_wF0 (mem : word -> option byte) (sp code s1v s2v s3v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x50e8c)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3v))
    (Z_to_bv 64 0x95c18) [Z_to_bv 8 1].

#[using="Type"] Lemma wF0 : forall regs mem rom (sp code s1v s2v s3v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x50e8c -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x95e63) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x95c28) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x95c1c) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x50c44 : word) mem rom)
                 (mkst regs' (0x50e8c : word) (mem_wF0 mem sp code s1v s2v s3v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs mem rom sp code s1v s2v s3v Hsp Hs0 Hra Hs1 Hs2 Hs3 SPlo SPhi SOK Mnl Mhead Malock.
  unfold mem_wF0. eexists. split.
  - (* [comment removed for export] *)
    stepn F_50c44 D_50c44. rewrite Hsp. sp_renorm.
    stepST F_50c48 D_50c48 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x50e8c) ltac:(sok_stack SOK).
    stepST F_50c4c D_50c4c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_50c50 D_50c50 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    stepST F_50c54 D_50c54 (Z_to_bv 64 (bv_unsigned sp - 48)) s2v ltac:(sok_stack SOK).
    stepST F_50c58 D_50c58 (Z_to_bv 64 (bv_unsigned sp - 56)) s3v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_50c5c D_50c5c.
    stepn F_50c60 D_50c60.
    stepn F_50c64 D_50c64.
    stepn F_50c68 D_50c68.
    (* [comment removed for export] *)
    stepn F_50c6c D_50c6c.
    stepn F_5eb5c D_5eb5c.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_5eb60 | reflexivity | exact D_5eb60 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_5eb64 D_5eb64 ltac:(cond_compute).
    stepret F_5ed54 D_5ed54 (0x50c70 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_50c70 D_50c70 (Z_to_bv 64 0).
    stepb_tk F_50c74 D_50c74 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_50ce4 D_50ce4.
    stepST F_50ce8 D_50ce8 (Z_to_bv 64 0x95c18) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_50cec D_50cec.
    (* [comment removed for export] *)
    stepLD8 F_50cf0 D_50cf0 (Z_to_bv 64 0x50e8c).
    stepLD8 F_50cf4 D_50cf4 code.
    stepLD8 F_50cf8 D_50cf8 s1v.
    stepLD8 F_50cfc D_50cfc s2v.
    stepLD8 F_50d00 D_50d00 s3v.
    stepn F_50d04 D_50d04. sp_renorm.
    stepn F_50d08 D_50d08.
    (* [comment removed for export] *)
    stepLD F_5ede4 D_5ede4 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepb_ft F_5ede8 D_5ede8 ltac:(cond_compute).
    stepret F_5edec D_5edec (0x50e8c : word) ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.


(* [comment removed for export] *)
Definition mem_wF1 (mem : word -> option byte) (sp code s1v s2v s3v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x50e8c)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3v))
    (Z_to_bv 64 0x95c20) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x95c20) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x95c20) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x95c28) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x95c18) [Z_to_bv 8 1].

#[using="Type"] Lemma wF1 : forall regs mem rom (sp code s1v s2v s3v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x50e8c -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x95e63) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x95c1c) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x95c28) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x95c30)) ->
  rdn RSEGS mem (Z_to_bv 64 0x95c20) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn RSEGS mem (Z_to_bv 64 0x95c38) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x50dd4)) ->
  rdn RSEGS mem (Z_to_bv 64 0x95d38) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x22a60)) ->
  rdn RSEGS mem (Z_to_bv 64 0x95c30) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x75064) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x50c44 : word) mem rom)
                 (mkst regs' (0x50e8c : word) (mem_wF1 mem sp code s1v s2v s3v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs mem rom sp code s1v s2v s3v Hsp Hs0 Hra Hs1 Hs2 Hs3 SPlo SPhi SOK Mnl Malock Mhead Mslot Mf0 Ma0 Mnext Mcb.
  unfold mem_wF1. eexists. split.
  - (* [comment removed for export] *)
    stepn F_50c44 D_50c44. rewrite Hsp. sp_renorm.
    stepST F_50c48 D_50c48 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x50e8c) ltac:(sok_stack SOK).
    stepST F_50c4c D_50c4c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_50c50 D_50c50 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    stepST F_50c54 D_50c54 (Z_to_bv 64 (bv_unsigned sp - 48)) s2v ltac:(sok_stack SOK).
    stepST F_50c58 D_50c58 (Z_to_bv 64 (bv_unsigned sp - 56)) s3v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_50c5c D_50c5c.
    stepn F_50c60 D_50c60.
    stepn F_50c64 D_50c64.
    stepn F_50c68 D_50c68.
    (* [comment removed for export] *)
    stepn F_50c6c D_50c6c.
    stepn F_5eb5c D_5eb5c.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_5eb60 | reflexivity | exact D_5eb60 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_5eb64 D_5eb64 ltac:(cond_compute).
    stepret F_5ed54 D_5ed54 (0x50c70 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_50c70 D_50c70 (Z_to_bv 64 0x95c30).
    stepb_ft F_50c74 D_50c74 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_50c78 D_50c78 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 1) by lia.
    stepn F_50c7c D_50c7c.
    (* [comment removed for export] *)
    stepn F_50c94 D_50c94.
    stepST F_50c98 D_50c98 (Z_to_bv 64 0x95c20) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_50c9c D_50c9c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_50ca0 D_50ca0 (Z_to_bv 64 0x95c30).
    stepn F_50ca4 D_50ca4.
    stepn F_50ca8 D_50ca8.
    stepLD8 F_50cac D_50cac (Z_to_bv 64 0x50dd4).
    stepLD8 F_50cb0 D_50cb0 (Z_to_bv 64 0x22a60).
    stepn F_50cb4 D_50cb4.
    (* [comment removed for export] *)
    stepn F_50cb8 D_50cb8.
    stepLD F_5ede4 D_5ede4 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepb_ft F_5ede8 D_5ede8 ltac:(cond_compute).
    stepret F_5edec D_5edec (0x50cbc : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_50cbc D_50cbc.
    stepjr F_50cc0 D_50cc0 (Z_to_bv 64 0x50dd4) ltac:(gres; reflexivity). vnorm.
    stepjr F_50dd4 D_50dd4 (Z_to_bv 64 0x22a60) ltac:(gres; reflexivity). vnorm.
    (* [comment removed for export] *)
    stepn F_22a60 D_22a60.
    stepLBU F_22a64 D_22a64 (Z_to_bv 8 0) ltac:(addr_norm; rdn_solve).
    stepb_ft F_22a68 D_22a68 ltac:(cond_compute).
    stepret F_22a6c D_22a6c (0x50cc4 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_50cc4 D_50cc4.
    stepn F_50cc8 D_50cc8.
    stepn F_5eb5c D_5eb5c.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_5eb60 | reflexivity | exact D_5eb60 | gres; imm_norm; addr_norm; rdn_solve]
      | step_simpl]; vnorm.
    stepb_tk F_5eb64 D_5eb64 ltac:(cond_compute).
    stepret F_5ed54 D_5ed54 (0x50ccc : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD F_50ccc D_50ccc (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solvew) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepn F_50cd0 D_50cd0.
    stepST F_50cd4 D_50cd4 (Z_to_bv 64 0x95c20) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_50cd8 D_50cd8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_50cdc D_50cdc (Z_to_bv 64 0x95c30).
    stepn F_50ce0 D_50ce0.
    stepLD8 F_50c80 D_50c80 (Z_to_bv 64 0).
    (* [comment removed for export] *)
    stepn F_50c84 D_50c84.
    stepST F_50c88 D_50c88 (Z_to_bv 64 0x95c20) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_50c8c D_50c8c (Z_to_bv 64 0x95c28) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_50c90 D_50c90 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_50ce4 D_50ce4.
    stepST F_50ce8 D_50ce8 (Z_to_bv 64 0x95c18) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    stepn F_50cec D_50cec.
    (* [comment removed for export] *)
    stepLD8 F_50cf0 D_50cf0 (Z_to_bv 64 0x50e8c).
    stepLD8 F_50cf4 D_50cf4 code.
    stepLD8 F_50cf8 D_50cf8 s1v.
    stepLD8 F_50cfc D_50cfc s2v.
    stepLD8 F_50d00 D_50d00 s3v.
    stepn F_50d04 D_50d04. sp_renorm.
    stepn F_50d08 D_50d08.
    (* [comment removed for export] *)
    stepLD F_5ede4 D_5ede4 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepb_ft F_5ede8 D_5ede8 ltac:(cond_compute).
    stepret F_5edec D_5edec (0x50e8c : word) ltac:(bveq).
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.


(* [comment removed for export] *)
Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x50e90)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x50e0c)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x60b18)))
    (Z_to_bv 64 0x65058) [Z_to_bv 8 1].

#[using="Type"] Lemma w2 : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x63da8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x60b20)) ->
  rdn RSEGS mem (Z_to_bv 64 0x63db0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x60b18)) ->
  rdn RSEGS mem (Z_to_bv 64 0x60b18) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x225a8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x65058) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x63c90) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x50d0c)) ->
  rdn RSEGS mem (Z_to_bv 64 0x63c98) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x50e8c : word) mem rom)
                 (mkst regs' (0x53bf0 : word) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x50e94
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros regs mem rom sp code s1v Hsp Hs0 Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mg2.
  (* [comment removed for export] *)
  destruct (rdn_dso (mem_w2 mem sp code s1v)) as (dbs & Hdso & Hlen). unfold mem_w2 in Hdso.
  unfold mem_w2. eexists. split.
  - (* [comment removed for export] *)
    stepn F_50e8c D_50e8c.
    stepn F_50ddc D_50ddc. rewrite Hsp. sp_renorm.
    stepST F_50de0 D_50de0 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x50e90) ltac:(sok_stack SOK).
    stepST F_50de4 D_50de4 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_50de8 D_50de8 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_50dec D_50dec.
    stepn F_50df0 D_50df0.
    stepLD8 F_50df4 D_50df4 (Z_to_bv 64 0x60b20).
    stepLD8 F_50df8 D_50df8 (Z_to_bv 64 0x60b18).
    (* [comment removed for export] *)
    stepb_ft F_50dfc D_50dfc ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_50e00 D_50e00 (Z_to_bv 64 0x225a8).
    stepn F_50e04 D_50e04.
    stepjr F_50e08 D_50e08 (Z_to_bv 64 0x225a8) ltac:(gres; reflexivity). vnorm.
    (* [comment removed for export] *)
    stepn F_225a8 D_225a8. sp_renorm.
    stepST F_225ac D_225ac (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x50e0c) ltac:(sok_stack SOK).
    stepST F_225b0 D_225b0 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x60b18) ltac:(sok_stack SOK).
    stepn F_225b4 D_225b4.
    (* [comment removed for export] *)
    stepn F_225b8 D_225b8.
    stepn F_225bc D_225bc.
    stepLBU F_225c0 D_225c0 (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
    stepn F_225c4 D_225c4.
    stepb_tk F_225c8 D_225c8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_225d4 D_225d4.
    stepn F_225d8 D_225d8.
    stepn F_225dc D_225dc.
    stepST F_225e0 D_225e0 (Z_to_bv 64 0x65058) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_225e4 D_225e4.
    stepLD8 F_225e8 D_225e8 (Z_to_bv 64 0x50d0c).
    stepb_ft F_225ec D_225ec ltac:(cond_compute).
    stepn F_225f0 D_225f0.
    (* [comment removed for export] *)
    stepn F_225f4 D_225f4.
    stepn F_225f8 D_225f8.
    stepLD F_225fc D_225fc dbs (Z_to_bv 64 (bytes_le_to_Z dbs))
      ltac:(addr_norm; exact Hdso)
      ltac:(symmetry; apply u_Z2bv; [apply bytes_le_to_Z_nonneg | pose proof (bytes_le_to_Z_bound dbs) as Hbd; rewrite Hlen in Hbd; exact Hbd]).
    (* [comment removed for export] *)
    stepn F_22600 D_22600.
    stepret F_50d0c D_50d0c (0x22604 : word) ltac:(bveq).
    stepn F_22604 D_22604.
    (* [comment removed for export] *)
    stepn F_22608 D_22608.
    stepLD8 F_2260c D_2260c (Z_to_bv 64 0).
    stepb_tk F_22610 D_22610 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_22628 D_22628 (Z_to_bv 64 0x50e0c).
    stepLD8 F_2262c D_2262c (Z_to_bv 64 0x60b18).
    stepn F_22630 D_22630. sp_renorm.
    stepret F_22634 D_22634 (0x50e0c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_50e0c D_50e0c.
    stepb_ft F_50e10 D_50e10 ltac:(cond_compute).
    stepLD8 F_50e14 D_50e14 (Z_to_bv 64 0x50e90).
    stepLD8 F_50e18 D_50e18 code.
    stepLD8 F_50e1c D_50e1c s1v.
    stepn F_50e20 D_50e20. sp_renorm.
    (* [comment removed for export] *)
    stepn F_50e24 D_50e24.
    stepret F_50dd8 D_50dd8 (0x50e90 : word) ltac:(bveq).
    stepn F_50e90 D_50e90.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xrel (sp : word) (mem mem' : word -> option byte) : Prop :=
  mem_grows mem mem' /\
  forall a : word, ~ (bv_unsigned sp - 144 <= bv_unsigned a < bv_unsigned sp)%Z ->
                   ~ (0x95c18 <= bv_unsigned a < 0x95c30)%Z ->
                   ~ (0x95e38 <= bv_unsigned a < 0x95e3c)%Z -> mem' a = mem a.

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
  (z + Z.of_nat n <= 0x95c18 \/ 0x95c30 <= z)%Z ->
  (z + Z.of_nat n <= 0x95e38 \/ 0x95e3c <= z)%Z ->
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
  rdn RSEGS mem (Z_to_bv 64 0x95e38) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x95e63) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x95c1c) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  (atx_idle mem \/ atx_reg mem) ->
  exists regs' mem',
    msteps RSEGS (mkst regs (0x50e28 : word) mem rom) (mkst regs' (0x50e8c : word) mem' rom)
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
