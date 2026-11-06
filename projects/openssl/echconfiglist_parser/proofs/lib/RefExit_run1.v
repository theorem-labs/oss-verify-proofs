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
From OSSVerify.openssl.echconfiglist_parser.images Require Import Plain.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic
  RefExitBase Ref_code_26e688_26f1d8 Ref_code_272890_273818 Ref_code_27a50c_27aa1c Ref_code_dd71c_ddd74 Ref_code_ea6c8_ea79c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rdn_wbytes_hit4 : forall segs m (a v : word),
  (bv_unsigned a + 4 <= 2^64)%Z ->
  rdn segs (wbytes m a (word_to_le_bytes 4 v)) a 4%nat = Some (word_to_le_bytes 4 v).
Proof.
  intros segs m a v Hnw.
  pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 v) m a) as H.
  rewrite length_N_to_le_bytes in H. apply H. exact Hnw.
Qed.

(* [comment removed for export] *)
Definition mem_w1_core (mem : word -> option byte) (sp ra s0 code s1 s2 s3 : word) (tid : Z) :=
  wbytes (wbytes (wbytes (wbytes (wbytes
  (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 0x30f6e8) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x26f0e8)))  (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))                  (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3).

(* [comment removed for export] *)
Definition mem_w1 (mem : word -> option byte) (sp ra s0 code s1 s2 s3 : word) (tid : Z) :=
  wbytes (mem_w1_core mem sp ra s0 code s1 s2 s3 tid)
    (Z_to_bv 64 0x30f4c8) [Z_to_bv 8 1].                                          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition mem_w1b (mem : word -> option byte) (sp ra s0 code s1 s2 s3 : word) (tid : Z) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (mem_w1_core mem sp ra s0 code s1 s2 s3 tid)
    (Z_to_bv 64 0x30f4d0) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x30f4d0) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x30f4d0) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x30f4d8) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x30f4c8) [Z_to_bv 8 1].

Definition mem_w1x (ax : bool) := if ax then mem_w1b else mem_w1.

Lemma w1 : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0x30f6e8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  (* [comment removed for export] *)
  rdn RSEGS mem (Z_to_bv 64 0x30f70b) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x30f4cc) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x30f4d8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x26f084 : word) mem rom)
                 (mkst regs' (0x26f038 : word) (mem_w1 mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x26f0ec
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Maxl Maxh.
  unfold mem_w1, mem_w1_core. eexists. split.
  - (* [comment removed for export] *)
    stepn F_26f048 D_26f048. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_26f04c D_26f04c (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_26f050 D_26f050 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_26f054 D_26f054.
    stepn F_26f058 D_26f058. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_26f05c D_26f05c (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_26f060 D_26f060.
    stepn F_26f064 D_26f064.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_26f068 | reflexivity | exact D_26f068
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_26f06c | reflexivity | exact D_26f06c | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_26f070 | reflexivity | exact D_26f070
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_26f074 D_26f074 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_26f078 D_26f078.
    (* [comment removed for export] *)
    stepb_ft F_26f07c D_26f07c ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_26f080 D_26f080 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_26f0a4 D_26f0a4. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_26f0a8 D_26f0a8.
    (* [comment removed for export] *)
    stepn F_26ee64 D_26ee64. sp_renorm.
    stepST F_26ee68 D_26ee68 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x26f0e8) ltac:(sok_stack SOK).
    stepST F_26ee6c D_26ee6c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_26ee70 D_26ee70 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_26ee74 D_26ee74 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_26ee78 D_26ee78 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_26ee7c D_26ee7c.
    stepn F_26ee80 D_26ee80.
    stepn F_26ee84 D_26ee84.
    stepn F_26ee88 D_26ee88.
    stepn F_26ee8c D_26ee8c.
    (* [comment removed for export] *)
    stepn F_27a720 D_27a720.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_27a724 | reflexivity | exact D_27a724 | gres; imm_norm; addr_norm; rdn_by Mnl]
      | step_simpl]; vnorm.
    stepb_tk F_27a728 D_27a728 ltac:(cond_compute).
    stepret F_27a918 D_27a918 (0x26eecc : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_26ee90 D_26ee90 (Z_to_bv 64 0).
    stepb_tk F_26ee94 D_26ee94 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_26ef04 D_26ef04.
    stepST F_26ef08 D_26ef08 (Z_to_bv 64 0x30f4c8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_26ef0c D_26ef0c.
    stepLD8 F_26ef10 D_26ef10 (Z_to_bv 64 0x26f0e8).
    stepLD8 F_26ef14 D_26ef14 code.
    stepLD8 F_26ef18 D_26ef18 (getr regs 9).
    stepLD8 F_26ef1c D_26ef1c (getr regs 18).
    stepLD8 F_26ef20 D_26ef20 (getr regs 19).
    stepn F_26ef24 D_26ef24. sp_renorm.
    stepn F_26ef28 D_26ef28.
    (* [comment removed for export] *)
    stepLD F_27a9a8 D_27a9a8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(rewrite v_addi_0; rdn_by Maxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_27a9ac D_27a9ac ltac:(cond_compute).
    stepret F_27a9b0 D_27a9b0 (0x26f0e8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_26f0ac D_26f0ac.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.

Lemma w1b : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0x30f6e8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  (* [comment removed for export] *)
  rdn RSEGS mem (Z_to_bv 64 0x30f70b) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x30f4cc) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  atexit_cells mem true ->
  exists regs',
    msteps RSEGS (mkst regs (0x26f084 : word) mem rom)
                 (mkst regs' (0x26f038 : word) (mem_w1b mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x26f0ec
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Maxl (Maxh & Mslot & Mnext & Mf0 & Ma0 & Mcb).
  unfold mem_w1b, mem_w1_core. eexists. split.
  - (* [comment removed for export] *)
    stepn F_26f048 D_26f048. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_26f04c D_26f04c (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_26f050 D_26f050 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_26f054 D_26f054.
    stepn F_26f058 D_26f058. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_26f05c D_26f05c (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_26f060 D_26f060.
    stepn F_26f064 D_26f064.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_26f068 | reflexivity | exact D_26f068
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_26f06c | reflexivity | exact D_26f06c | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_26f070 | reflexivity | exact D_26f070
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_26f074 D_26f074 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_26f078 D_26f078.
    (* [comment removed for export] *)
    stepb_ft F_26f07c D_26f07c ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_26f080 D_26f080 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_26f0a4 D_26f0a4. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_26f0a8 D_26f0a8.
    (* [comment removed for export] *)
    stepn F_26ee64 D_26ee64. sp_renorm.
    stepST F_26ee68 D_26ee68 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x26f0e8) ltac:(sok_stack SOK).
    stepST F_26ee6c D_26ee6c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_26ee70 D_26ee70 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_26ee74 D_26ee74 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_26ee78 D_26ee78 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_26ee7c D_26ee7c.
    stepn F_26ee80 D_26ee80.
    stepn F_26ee84 D_26ee84.
    stepn F_26ee88 D_26ee88.
    stepn F_26ee8c D_26ee8c.
    (* [comment removed for export] *)
    stepn F_27a720 D_27a720.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_27a724 | reflexivity | exact D_27a724 | gres; imm_norm; addr_norm; rdn_by Mnl]
      | step_simpl]; vnorm.
    stepb_tk F_27a728 D_27a728 ltac:(cond_compute).
    stepret F_27a918 D_27a918 (0x26eecc : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_26ee90 D_26ee90 (Z_to_bv 64 0x30f4e0).
    stepb_ft F_26ee94 D_26ee94 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_26ee98 D_26ee98 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
      ltac:(addr_norm; rdn_by Mslot) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepn F_26ee9c D_26ee9c.
    (* [comment removed for export] *)
    stepn F_26eeb4 D_26eeb4.
    stepST F_26eeb8 D_26eeb8 (Z_to_bv 64 0x30f4d0) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_26eebc D_26eebc ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_26eec0 D_26eec0 (Z_to_bv 64 0x30f4e0).
    stepn F_26eec4 D_26eec4.
    stepn F_26eec8 D_26eec8.
    stepLD8 F_26eecc D_26eecc (Z_to_bv 64 0x26f030).
    stepLD8 F_26eed0 D_26eed0 (Z_to_bv 64 0xddd28).
    (* [comment removed for export] *)
    stepn F_26eed4 D_26eed4.
    stepn F_26eed8 D_26eed8.
    stepLD F_27a9a8 D_27a9a8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(rewrite v_addi_0; rdn_by Maxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_27a9ac D_27a9ac ltac:(cond_compute).
    stepret F_27a9b0 D_27a9b0 (0x26ef18 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_26eedc D_26eedc.
    stepjr F_26eee0 D_26eee0 (Z_to_bv 64 0x26f030) ltac:(gres; first [reflexivity | bveq]). vnorm.
    stepret F_26eff4 D_26eff4 (0xddd28 : word) ltac:(first [reflexivity | bveq]).
    (* [comment removed for export] *)
    stepn F_ddce0 D_ddce0.
    stepLBU F_ddce4 D_ddce4 (Z_to_bv 8 0) ltac:(addr_norm; rdn_by Mcb).
    stepb_ft F_ddce8 D_ddce8 ltac:(cond_compute).
    stepret F_ddcec D_ddcec (0x26ef20 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_26eee4 D_26eee4.
    stepn F_26eee8 D_26eee8.
    stepn F_27a720 D_27a720.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_27a724 | reflexivity | exact D_27a724 | gres; imm_norm; addr_norm; rdn_by Mnl]
      | step_simpl]; vnorm.
    stepb_tk F_27a728 D_27a728 ltac:(cond_compute).
    stepret F_27a918 D_27a918 (0x26ef28 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD F_26eeec D_26eeec (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; apply rdn_wbytes_hit4; u_norm; lia) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepn F_26eef0 D_26eef0.
    stepST F_26eef4 D_26eef4 (Z_to_bv 64 0x30f4d0) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_26eef8 D_26eef8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_26eefc D_26eefc (Z_to_bv 64 0x30f4e0).
    stepn F_26ef00 D_26ef00.
    stepLD8 F_26eea0 D_26eea0 (Z_to_bv 64 0).
    stepn F_26eea4 D_26eea4.
    stepST F_26eea8 D_26eea8 (Z_to_bv 64 0x30f4d0) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_26eeac D_26eeac (Z_to_bv 64 0x30f4d8) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_26eeb0 D_26eeb0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_26ef04 D_26ef04.
    stepST F_26ef08 D_26ef08 (Z_to_bv 64 0x30f4c8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_26ef0c D_26ef0c.
    stepLD8 F_26ef10 D_26ef10 (Z_to_bv 64 0x26f0e8).
    stepLD8 F_26ef14 D_26ef14 code.
    stepLD8 F_26ef18 D_26ef18 (getr regs 9).
    stepLD8 F_26ef1c D_26ef1c (getr regs 18).
    stepLD8 F_26ef20 D_26ef20 (getr regs 19).
    stepn F_26ef24 D_26ef24. sp_renorm.
    stepn F_26ef28 D_26ef28.
    (* [comment removed for export] *)
    stepLD F_27a9a8 D_27a9a8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(rewrite v_addi_0; rdn_by Maxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_27a9ac D_27a9ac ltac:(cond_compute).
    stepret F_27a9b0 D_27a9b0 (0x26f0e8 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_26f0ac D_26f0ac.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.


(* [comment removed for export] *)
Lemma w1x : forall (ax : bool) regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0x30f6e8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x30f70b) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x30f4cc) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  atexit_cells mem ax ->
  exists regs',
    msteps RSEGS (mkst regs (0x26f084 : word) mem rom)
                 (mkst regs' (0x26f038 : word) (mem_w1x ax mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x26f0ec
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros ax; destruct ax; intros; cbn [mem_w1x]; [eapply w1b | eapply w1]; eassumption.
Qed.

(* [comment removed for export] *)
Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes
  (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x26f0ec)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x26f068)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x27efc8)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp - 72)) (word_to_le_bytes 8 (Z_to_bv 64 0x27efd0)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x26f068)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x27efc8)))   (* [comment removed for export] *)
    (Z_to_bv 64 0x2dc8f8) [Z_to_bv 8 1].

Lemma w2 : forall regs mem rom (sp code s1v : word) (bi : bv 8),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x26f0ec -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x2db150) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x27efd8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x2db158) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x27efc8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x27efc8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xdd824)) ->
  rdn RSEGS mem (Z_to_bv 64 0x2dc8f8) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x2dab50) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x26ef68)) ->
  rdn RSEGS mem (Z_to_bv 64 0x2dc160) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2dc160)) ->
  rdn RSEGS mem (Z_to_bv 64 0x2dab58) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  (* [comment removed for export] *)
  rdn RSEGS mem (Z_to_bv 64 0x27efd0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xea710)) ->
  rdn RSEGS mem (Z_to_bv 64 0x2ecb38) 1%nat = Some [bi] ->
  rdn RSEGS mem (Z_to_bv 64 0x2ecb3c) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x26f038 : word) mem rom)
                 (mkst regs' (0x2728cc : word) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x26f0f0
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
  intros regs mem rom sp code s1v bi Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mdso Mg2 Mfa1 Mbi Mdgc.
  pose proof (u8_range bi) as Hbi.
  unfold mem_w2.
  (* [comment removed for export] *)
  destruct (Z.eq_dec (bv_unsigned bi) 0) as [Hbi0 | Hbi1].
  - assert (Ebi : bi = Z_to_bv 8 0) by (apply bv_eq; rewrite Hbi0; reflexivity). subst bi.
    eexists. split.
    + (* [comment removed for export] *)
      stepn F_26effc D_26effc. rewrite Hsp. sp_renorm.
      stepST F_26f000 D_26f000 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x26f0ec) ltac:(sok_stack SOK).
      stepST F_26f004 D_26f004 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
      stepST F_26f008 D_26f008 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
      (* [comment removed for export] *)
      stepn F_26f00c D_26f00c.
      stepn F_26f010 D_26f010.
      stepLD8 F_26f014 D_26f014 (Z_to_bv 64 0x27efd8).
      stepLD8 F_26f018 D_26f018 (Z_to_bv 64 0x27efc8).
      (* [comment removed for export] *)
      stepb_ft F_26f01c D_26f01c ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD8 F_26f020 D_26f020 (Z_to_bv 64 0xea710).
      stepn F_26f024 D_26f024.
      stepjr F_26f028 D_26f028 (Z_to_bv 64 0xea710) ltac:(gres; reflexivity). vnorm.
      (* [comment removed for export] *)
      stepn F_ea6c8 D_ea6c8. sp_renorm.
      stepST F_ea6cc D_ea6cc (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x26f068) ltac:(sok_stack SOK).
      stepST F_ea6d0 D_ea6d0 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x27efc8) ltac:(sok_stack SOK).
      stepST F_ea6d4 D_ea6d4 (Z_to_bv 64 (bv_unsigned sp - 72)) (Z_to_bv 64 0x27efd0) ltac:(sok_stack SOK).
      stepn F_ea6d8 D_ea6d8.
      (* [comment removed for export] *)
      stepn F_ea6dc D_ea6dc.
      stepn F_ea6e0 D_ea6e0.
      stepLBU F_ea6e4 D_ea6e4 (Z_to_bv 8 0) ltac:(addr_norm; rdn_by Mbi).
      stepb_tk F_ea6e8 D_ea6e8 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD8 F_ea788 D_ea788 (Z_to_bv 64 0x26f068).
      stepLD8 F_ea78c D_ea78c (Z_to_bv 64 0x27efc8).
      stepLD8 F_ea790 D_ea790 (Z_to_bv 64 0x27efd0).
      stepn F_ea794 D_ea794. sp_renorm.
      stepret F_ea798 D_ea798 (0x26f068 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepn F_26f02c D_26f02c.
      stepb_tk F_26f030 D_26f030 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD8 F_26f020 D_26f020 (Z_to_bv 64 0xdd824).
      stepn F_26f024 D_26f024.
      stepjr F_26f028 D_26f028 (Z_to_bv 64 0xdd824) ltac:(gres; reflexivity). vnorm.
      (* [comment removed for export] *)
      stepn F_dd7dc D_dd7dc. sp_renorm.
      stepST F_dd7e0 D_dd7e0 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x26f068) ltac:(sok_stack SOK).
      stepST F_dd7e4 D_dd7e4 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x27efc8) ltac:(sok_stack SOK).
      stepn F_dd7e8 D_dd7e8.
      stepn F_dd7ec D_dd7ec.
      stepn F_dd7f0 D_dd7f0.
      (* [comment removed for export] *)
      stepLBU F_dd7f4 D_dd7f4 (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
      stepn F_dd7f8 D_dd7f8.
      stepb_tk F_dd7fc D_dd7fc ltac:(cond_compute).
      stepn F_dd808 D_dd808.
      stepn F_dd80c D_dd80c.
      stepn F_dd810 D_dd810.
      (* [comment removed for export] *)
      stepST F_dd814 D_dd814 (Z_to_bv 64 0x2dc8f8) (Z_to_bv 64 1) ltac:(sok_data).
      change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
      (* [comment removed for export] *)
      stepn F_dd818 D_dd818.
      stepLD8 F_dd81c D_dd81c (Z_to_bv 64 0x26ef68).
      stepb_ft F_dd820 D_dd820 ltac:(cond_compute).
      stepn F_dd824 D_dd824.
      stepn F_dd828 D_dd828.
      stepn F_dd82c D_dd82c.
      stepLD8 F_dd830 D_dd830 (Z_to_bv 64 0x2dc160).
      stepn F_dd834 D_dd834.   (* [comment removed for export] *)
      stepjr F_dd838 D_dd838 (0x26e87c : word) ltac:(gres; first [reflexivity | bveq]). vnorm.   (* [comment removed for export] *)
      stepret F_26ef2c D_26ef2c (0xdd884 : word) ltac:(bveq).
      stepn F_dd83c D_dd83c.
      (* [comment removed for export] *)
      stepn F_dd840 D_dd840.
      stepLD8 F_dd844 D_dd844 (Z_to_bv 64 0).
      stepb_tk F_dd848 D_dd848 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD8 F_dd860 D_dd860 (Z_to_bv 64 0x26f068).
      stepLD8 F_dd864 D_dd864 (Z_to_bv 64 0x27efc8).
      stepn F_dd868 D_dd868. sp_renorm.
      stepret F_dd86c D_dd86c (0x26f068 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepn F_26f02c D_26f02c.
      stepb_ft F_26f030 D_26f030 ltac:(cond_compute).
      stepLD8 F_26f034 D_26f034 (Z_to_bv 64 0x26f0ec).
      stepLD8 F_26f038 D_26f038 code.
      stepLD8 F_26f03c D_26f03c s1v.
      stepn F_26f040 D_26f040. sp_renorm.
      (* [comment removed for export] *)
      stepn F_26f044 D_26f044.
      stepret F_26eff8 D_26eff8 (0x26f0ec : word) ltac:(bveq).
      stepn F_26f0b0 D_26f0b0.
      apply mst_refl.
    + repeat split; gres; try reflexivity.
  - eexists. split.
    + (* [comment removed for export] *)
      stepn F_26effc D_26effc. rewrite Hsp. sp_renorm.
      stepST F_26f000 D_26f000 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x26f0ec) ltac:(sok_stack SOK).
      stepST F_26f004 D_26f004 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
      stepST F_26f008 D_26f008 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
      stepn F_26f00c D_26f00c.
      stepn F_26f010 D_26f010.
      stepLD8 F_26f014 D_26f014 (Z_to_bv 64 0x27efd8).
      stepLD8 F_26f018 D_26f018 (Z_to_bv 64 0x27efc8).
      stepb_ft F_26f01c D_26f01c ltac:(cond_compute).
      stepLD8 F_26f020 D_26f020 (Z_to_bv 64 0xea710).
      stepn F_26f024 D_26f024.
      stepjr F_26f028 D_26f028 (Z_to_bv 64 0xea710) ltac:(gres; reflexivity). vnorm.
      stepn F_ea6c8 D_ea6c8. sp_renorm.
      stepST F_ea6cc D_ea6cc (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x26f068) ltac:(sok_stack SOK).
      stepST F_ea6d0 D_ea6d0 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x27efc8) ltac:(sok_stack SOK).
      stepST F_ea6d4 D_ea6d4 (Z_to_bv 64 (bv_unsigned sp - 72)) (Z_to_bv 64 0x27efd0) ltac:(sok_stack SOK).
      stepn F_ea6d8 D_ea6d8.
      stepn F_ea6dc D_ea6dc.
      stepn F_ea6e0 D_ea6e0.
      (* [comment removed for export] *)
      stepLBU F_ea6e4 D_ea6e4 bi ltac:(addr_norm; rdn_by Mbi).
      stepb_ft F_ea6e8 D_ea6e8 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
      (* [comment removed for export] *)
      stepLBU F_ea6ec D_ea6ec (Z_to_bv 8 0) ltac:(addr_norm; rdn_by Mdgc).
      stepn F_ea6f0 D_ea6f0.
      stepb_tk F_ea6f4 D_ea6f4 ltac:(cond_compute).
      stepLD8 F_ea788 D_ea788 (Z_to_bv 64 0x26f068).
      stepLD8 F_ea78c D_ea78c (Z_to_bv 64 0x27efc8).
      stepLD8 F_ea790 D_ea790 (Z_to_bv 64 0x27efd0).
      stepn F_ea794 D_ea794. sp_renorm.
      stepret F_ea798 D_ea798 (0x26f068 : word) ltac:(bveq).
      stepn F_26f02c D_26f02c.
      stepb_tk F_26f030 D_26f030 ltac:(cond_compute).
      stepLD8 F_26f020 D_26f020 (Z_to_bv 64 0xdd824).
      stepn F_26f024 D_26f024.
      stepjr F_26f028 D_26f028 (Z_to_bv 64 0xdd824) ltac:(gres; reflexivity). vnorm.
      (* [comment removed for export] *)
      stepn F_dd7dc D_dd7dc. sp_renorm.
      stepST F_dd7e0 D_dd7e0 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x26f068) ltac:(sok_stack SOK).
      stepST F_dd7e4 D_dd7e4 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x27efc8) ltac:(sok_stack SOK).
      stepn F_dd7e8 D_dd7e8.
      stepn F_dd7ec D_dd7ec.
      stepn F_dd7f0 D_dd7f0.
      (* [comment removed for export] *)
      stepLBU F_dd7f4 D_dd7f4 (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
      stepn F_dd7f8 D_dd7f8.
      stepb_tk F_dd7fc D_dd7fc ltac:(cond_compute).
      stepn F_dd808 D_dd808.
      stepn F_dd80c D_dd80c.
      stepn F_dd810 D_dd810.
      (* [comment removed for export] *)
      stepST F_dd814 D_dd814 (Z_to_bv 64 0x2dc8f8) (Z_to_bv 64 1) ltac:(sok_data).
      change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
      (* [comment removed for export] *)
      stepn F_dd818 D_dd818.
      stepLD8 F_dd81c D_dd81c (Z_to_bv 64 0x26ef68).
      stepb_ft F_dd820 D_dd820 ltac:(cond_compute).
      stepn F_dd824 D_dd824.
      stepn F_dd828 D_dd828.
      stepn F_dd82c D_dd82c.
      stepLD8 F_dd830 D_dd830 (Z_to_bv 64 0x2dc160).
      stepn F_dd834 D_dd834.   (* [comment removed for export] *)
      stepjr F_dd838 D_dd838 (0x26e87c : word) ltac:(gres; first [reflexivity | bveq]). vnorm.   (* [comment removed for export] *)
      stepret F_26ef2c D_26ef2c (0xdd884 : word) ltac:(bveq).
      stepn F_dd83c D_dd83c.
      (* [comment removed for export] *)
      stepn F_dd840 D_dd840.
      stepLD8 F_dd844 D_dd844 (Z_to_bv 64 0).
      stepb_tk F_dd848 D_dd848 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD8 F_dd860 D_dd860 (Z_to_bv 64 0x26f068).
      stepLD8 F_dd864 D_dd864 (Z_to_bv 64 0x27efc8).
      stepn F_dd868 D_dd868. sp_renorm.
      stepret F_dd86c D_dd86c (0x26f068 : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepn F_26f02c D_26f02c.
      stepb_ft F_26f030 D_26f030 ltac:(cond_compute).
      stepLD8 F_26f034 D_26f034 (Z_to_bv 64 0x26f0ec).
      stepLD8 F_26f038 D_26f038 code.
      stepLD8 F_26f03c D_26f03c s1v.
      stepn F_26f040 D_26f040. sp_renorm.
      (* [comment removed for export] *)
      stepn F_26f044 D_26f044.
      stepret F_26eff8 D_26eff8 (0x26f0ec : word) ltac:(bveq).
      stepn F_26f0b0 D_26f0b0.
      apply mst_refl.
    + repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
