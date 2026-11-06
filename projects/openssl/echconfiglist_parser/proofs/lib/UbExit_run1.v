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
From OSSVerify.openssl.echconfiglist_parser.images Require Import Ubsan.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic UbExitBase Ub_code_2b52bc_2b5e0c Ub_code_2b94c4_2ba44c Ub_code_2c1140_2c1650 Ub_code_e214c_e27a4 Ub_code_f12c0_f1394.
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
    (Z_to_bv 64 0x356308) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x2b5d1c)))  (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))                  (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3).

(* [comment removed for export] *)
Definition mem_w1 (mem : word -> option byte) (sp ra s0 code s1 s2 s3 : word) (tid : Z) :=
  wbytes (mem_w1_core mem sp ra s0 code s1 s2 s3 tid)
    (Z_to_bv 64 0x3560e8) [Z_to_bv 8 1].                                          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition mem_w1b (mem : word -> option byte) (sp ra s0 code s1 s2 s3 : word) (tid : Z) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (mem_w1_core mem sp ra s0 code s1 s2 s3 tid)
    (Z_to_bv 64 0x3560f0) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x3560f0) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))
    (Z_to_bv 64 0x3560f0) (word_to_le_bytes 4 (Z_to_bv 64 32)))
    (Z_to_bv 64 0x3560f8) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 0x3560e8) [Z_to_bv 8 1].

Definition mem_w1x (ax : bool) := if ax then mem_w1b else mem_w1.

Lemma w1 : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0x356308) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  (* [comment removed for export] *)
  rdn RSEGS mem (Z_to_bv 64 0x35632b) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x3560ec) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x3560f8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x2b5cb8 : word) mem rom)
                 (mkst regs' (0x2b5c6c : word) (mem_w1 mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x2b5d20
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Maxl Maxh.
  unfold mem_w1, mem_w1_core. eexists. split.
  - (* [comment removed for export] *)
    stepn F_2b5c7c D_2b5c7c. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_2b5c80 D_2b5c80 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_2b5c84 D_2b5c84 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_2b5c88 D_2b5c88.
    stepn F_2b5c8c D_2b5c8c. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_2b5c90 D_2b5c90 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_2b5c94 D_2b5c94.
    stepn F_2b5c98 D_2b5c98.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_2b5c9c | reflexivity | exact D_2b5c9c
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_2b5ca0 | reflexivity | exact D_2b5ca0 | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_2b5ca4 | reflexivity | exact D_2b5ca4
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_2b5ca8 D_2b5ca8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_2b5cac D_2b5cac.
    (* [comment removed for export] *)
    stepb_ft F_2b5cb0 D_2b5cb0 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_2b5cb4 D_2b5cb4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_2b5cd8 D_2b5cd8. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_2b5cdc D_2b5cdc.
    (* [comment removed for export] *)
    stepn F_2b5a98 D_2b5a98. sp_renorm.
    stepST F_2b5a9c D_2b5a9c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x2b5d1c) ltac:(sok_stack SOK).
    stepST F_2b5aa0 D_2b5aa0 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_2b5aa4 D_2b5aa4 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_2b5aa8 D_2b5aa8 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_2b5aac D_2b5aac (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_2b5ab0 D_2b5ab0.
    stepn F_2b5ab4 D_2b5ab4.
    stepn F_2b5ab8 D_2b5ab8.
    stepn F_2b5abc D_2b5abc.
    stepn F_2b5ac0 D_2b5ac0.
    (* [comment removed for export] *)
    stepn F_2c1354 D_2c1354.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_2c1358 | reflexivity | exact D_2c1358 | gres; imm_norm; addr_norm; rdn_by Mnl]
      | step_simpl]; vnorm.
    stepb_tk F_2c135c D_2c135c ltac:(cond_compute).
    stepret F_2c154c D_2c154c (0x2b5b00 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_2b5ac4 D_2b5ac4 (Z_to_bv 64 0).
    stepb_tk F_2b5ac8 D_2b5ac8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_2b5b38 D_2b5b38.
    stepST F_2b5b3c D_2b5b3c (Z_to_bv 64 0x3560e8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_2b5b40 D_2b5b40.
    stepLD8 F_2b5b44 D_2b5b44 (Z_to_bv 64 0x2b5d1c).
    stepLD8 F_2b5b48 D_2b5b48 code.
    stepLD8 F_2b5b4c D_2b5b4c (getr regs 9).
    stepLD8 F_2b5b50 D_2b5b50 (getr regs 18).
    stepLD8 F_2b5b54 D_2b5b54 (getr regs 19).
    stepn F_2b5b58 D_2b5b58. sp_renorm.
    stepn F_2b5b5c D_2b5b5c.
    (* [comment removed for export] *)
    stepLD F_2c15dc D_2c15dc (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(rewrite v_addi_0; rdn_by Maxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_2c15e0 D_2c15e0 ltac:(cond_compute).
    stepret F_2c15e4 D_2c15e4 (0x2b5d1c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_2b5ce0 D_2b5ce0.
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
  rdn RSEGS mem (Z_to_bv 64 0x356308) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  (* [comment removed for export] *)
  rdn RSEGS mem (Z_to_bv 64 0x35632b) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x3560ec) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  atexit_cells mem true ->
  exists regs',
    msteps RSEGS (mkst regs (0x2b5cb8 : word) mem rom)
                 (mkst regs' (0x2b5c6c : word) (mem_w1b mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x2b5d20
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Maxl (Maxh & Mslot & Mnext & Mf0 & Ma0 & Mcb).
  unfold mem_w1b, mem_w1_core. eexists. split.
  - (* [comment removed for export] *)
    stepn F_2b5c7c D_2b5c7c. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_2b5c80 D_2b5c80 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_2b5c84 D_2b5c84 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_2b5c88 D_2b5c88.
    stepn F_2b5c8c D_2b5c8c. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_2b5c90 D_2b5c90 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_2b5c94 D_2b5c94.
    stepn F_2b5c98 D_2b5c98.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_2b5c9c | reflexivity | exact D_2b5c9c
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_2b5ca0 | reflexivity | exact D_2b5ca0 | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_2b5ca4 | reflexivity | exact D_2b5ca4
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_2b5ca8 D_2b5ca8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_2b5cac D_2b5cac.
    (* [comment removed for export] *)
    stepb_ft F_2b5cb0 D_2b5cb0 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_2b5cb4 D_2b5cb4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_2b5cd8 D_2b5cd8. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_2b5cdc D_2b5cdc.
    (* [comment removed for export] *)
    stepn F_2b5a98 D_2b5a98. sp_renorm.
    stepST F_2b5a9c D_2b5a9c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x2b5d1c) ltac:(sok_stack SOK).
    stepST F_2b5aa0 D_2b5aa0 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_2b5aa4 D_2b5aa4 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_2b5aa8 D_2b5aa8 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_2b5aac D_2b5aac (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_2b5ab0 D_2b5ab0.
    stepn F_2b5ab4 D_2b5ab4.
    stepn F_2b5ab8 D_2b5ab8.
    stepn F_2b5abc D_2b5abc.
    stepn F_2b5ac0 D_2b5ac0.
    (* [comment removed for export] *)
    stepn F_2c1354 D_2c1354.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_2c1358 | reflexivity | exact D_2c1358 | gres; imm_norm; addr_norm; rdn_by Mnl]
      | step_simpl]; vnorm.
    stepb_tk F_2c135c D_2c135c ltac:(cond_compute).
    stepret F_2c154c D_2c154c (0x2b5b00 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_2b5ac4 D_2b5ac4 (Z_to_bv 64 0x356100).
    stepb_ft F_2b5ac8 D_2b5ac8 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_2b5acc D_2b5acc (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
      ltac:(addr_norm; rdn_by Mslot) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepn F_2b5ad0 D_2b5ad0.
    (* [comment removed for export] *)
    stepn F_2b5ae8 D_2b5ae8.
    stepST F_2b5aec D_2b5aec (Z_to_bv 64 0x3560f0) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_2b5af0 D_2b5af0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_2b5af4 D_2b5af4 (Z_to_bv 64 0x356100).
    stepn F_2b5af8 D_2b5af8.
    stepn F_2b5afc D_2b5afc.
    stepLD8 F_2b5b00 D_2b5b00 (Z_to_bv 64 0x2b5c64).
    stepLD8 F_2b5b04 D_2b5b04 (Z_to_bv 64 0xe2758).
    (* [comment removed for export] *)
    stepn F_2b5b08 D_2b5b08.
    stepn F_2b5b0c D_2b5b0c.
    stepLD F_2c15dc D_2c15dc (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(rewrite v_addi_0; rdn_by Maxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_2c15e0 D_2c15e0 ltac:(cond_compute).
    stepret F_2c15e4 D_2c15e4 (0x2b5b4c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_2b5b10 D_2b5b10.
    stepjr F_2b5b14 D_2b5b14 (Z_to_bv 64 0x2b5c64) ltac:(gres; first [reflexivity | bveq]). vnorm.
    stepret F_2b5c28 D_2b5c28 (0xe2758 : word) ltac:(first [reflexivity | bveq]).
    (* [comment removed for export] *)
    stepn F_e2710 D_e2710.
    stepLBU F_e2714 D_e2714 (Z_to_bv 8 0) ltac:(addr_norm; rdn_by Mcb).
    stepb_ft F_e2718 D_e2718 ltac:(cond_compute).
    stepret F_e271c D_e271c (0x2b5b54 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_2b5b18 D_2b5b18.
    stepn F_2b5b1c D_2b5b1c.
    stepn F_2c1354 D_2c1354.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_2c1358 | reflexivity | exact D_2c1358 | gres; imm_norm; addr_norm; rdn_by Mnl]
      | step_simpl]; vnorm.
    stepb_tk F_2c135c D_2c135c ltac:(cond_compute).
    stepret F_2c154c D_2c154c (0x2b5b5c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD F_2b5b20 D_2b5b20 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; apply rdn_wbytes_hit4; u_norm; lia) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepn F_2b5b24 D_2b5b24.
    stepST F_2b5b28 D_2b5b28 (Z_to_bv 64 0x3560f0) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_2b5b2c D_2b5b2c ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_2b5b30 D_2b5b30 (Z_to_bv 64 0x356100).
    stepn F_2b5b34 D_2b5b34.
    stepLD8 F_2b5ad4 D_2b5ad4 (Z_to_bv 64 0).
    stepn F_2b5ad8 D_2b5ad8.
    stepST F_2b5adc D_2b5adc (Z_to_bv 64 0x3560f0) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_2b5ae0 D_2b5ae0 (Z_to_bv 64 0x3560f8) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_2b5ae4 D_2b5ae4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_2b5b38 D_2b5b38.
    stepST F_2b5b3c D_2b5b3c (Z_to_bv 64 0x3560e8) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_2b5b40 D_2b5b40.
    stepLD8 F_2b5b44 D_2b5b44 (Z_to_bv 64 0x2b5d1c).
    stepLD8 F_2b5b48 D_2b5b48 code.
    stepLD8 F_2b5b4c D_2b5b4c (getr regs 9).
    stepLD8 F_2b5b50 D_2b5b50 (getr regs 18).
    stepLD8 F_2b5b54 D_2b5b54 (getr regs 19).
    stepn F_2b5b58 D_2b5b58. sp_renorm.
    stepn F_2b5b5c D_2b5b5c.
    (* [comment removed for export] *)
    stepLD F_2c15dc D_2c15dc (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(rewrite v_addi_0; rdn_by Maxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_2c15e0 D_2c15e0 ltac:(cond_compute).
    stepret F_2c15e4 D_2c15e4 (0x2b5d1c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_2b5ce0 D_2b5ce0.
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
  rdn RSEGS mem (Z_to_bv 64 0x356308) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x35632b) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x3560ec) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  atexit_cells mem ax ->
  exists regs',
    msteps RSEGS (mkst regs (0x2b5cb8 : word) mem rom)
                 (mkst regs' (0x2b5c6c : word) (mem_w1x ax mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x2b5d20
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros ax; destruct ax; intros; cbn [mem_w1x]; [eapply w1b | eapply w1]; eassumption.
Qed.

(* [comment removed for export] *)
Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes
  (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x2b5d20)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x2b5c9c)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x2c5c00)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp - 72)) (word_to_le_bytes 8 (Z_to_bv 64 0x2c5c08)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x2b5c9c)))   (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x2c5c00)))   (* [comment removed for export] *)
    (Z_to_bv 64 0x323518) [Z_to_bv 8 1].

Lemma w2 : forall regs mem rom (sp code s1v : word) (bi : bv 8),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x2b5d20 -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x321bc8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2c5c10)) ->
  rdn RSEGS mem (Z_to_bv 64 0x321bd0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2c5c00)) ->
  rdn RSEGS mem (Z_to_bv 64 0x2c5c00) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe2254)) ->
  rdn RSEGS mem (Z_to_bv 64 0x323518) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x3215d8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2b5b9c)) ->
  rdn RSEGS mem (Z_to_bv 64 0x322bd8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x322bd8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x3215e0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  (* [comment removed for export] *)
  rdn RSEGS mem (Z_to_bv 64 0x2c5c08) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xf1308)) ->
  rdn RSEGS mem (Z_to_bv 64 0x333758) 1%nat = Some [bi] ->
  rdn RSEGS mem (Z_to_bv 64 0x33375c) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x2b5c6c : word) mem rom)
                 (mkst regs' (0x2b9500 : word) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x2b5d24
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
      stepn F_2b5c30 D_2b5c30. rewrite Hsp. sp_renorm.
      stepST F_2b5c34 D_2b5c34 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x2b5d20) ltac:(sok_stack SOK).
      stepST F_2b5c38 D_2b5c38 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
      stepST F_2b5c3c D_2b5c3c (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
      (* [comment removed for export] *)
      stepn F_2b5c40 D_2b5c40.
      stepn F_2b5c44 D_2b5c44.
      stepLD8 F_2b5c48 D_2b5c48 (Z_to_bv 64 0x2c5c10).
      stepLD8 F_2b5c4c D_2b5c4c (Z_to_bv 64 0x2c5c00).
      (* [comment removed for export] *)
      stepb_ft F_2b5c50 D_2b5c50 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD8 F_2b5c54 D_2b5c54 (Z_to_bv 64 0xf1308).
      stepn F_2b5c58 D_2b5c58.
      stepjr F_2b5c5c D_2b5c5c (Z_to_bv 64 0xf1308) ltac:(gres; reflexivity). vnorm.
      (* [comment removed for export] *)
      stepn F_f12c0 D_f12c0. sp_renorm.
      stepST F_f12c4 D_f12c4 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x2b5c9c) ltac:(sok_stack SOK).
      stepST F_f12c8 D_f12c8 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x2c5c00) ltac:(sok_stack SOK).
      stepST F_f12cc D_f12cc (Z_to_bv 64 (bv_unsigned sp - 72)) (Z_to_bv 64 0x2c5c08) ltac:(sok_stack SOK).
      stepn F_f12d0 D_f12d0.
      (* [comment removed for export] *)
      stepn F_f12d4 D_f12d4.
      stepn F_f12d8 D_f12d8.
      stepLBU F_f12dc D_f12dc (Z_to_bv 8 0) ltac:(addr_norm; rdn_by Mbi).
      stepb_tk F_f12e0 D_f12e0 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD8 F_f1380 D_f1380 (Z_to_bv 64 0x2b5c9c).
      stepLD8 F_f1384 D_f1384 (Z_to_bv 64 0x2c5c00).
      stepLD8 F_f1388 D_f1388 (Z_to_bv 64 0x2c5c08).
      stepn F_f138c D_f138c. sp_renorm.
      stepret F_f1390 D_f1390 (0x2b5c9c : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepn F_2b5c60 D_2b5c60.
      stepb_tk F_2b5c64 D_2b5c64 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD8 F_2b5c54 D_2b5c54 (Z_to_bv 64 0xe2254).
      stepn F_2b5c58 D_2b5c58.
      stepjr F_2b5c5c D_2b5c5c (Z_to_bv 64 0xe2254) ltac:(gres; reflexivity). vnorm.
      (* [comment removed for export] *)
      stepn F_e220c D_e220c. sp_renorm.
      stepST F_e2210 D_e2210 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x2b5c9c) ltac:(sok_stack SOK).
      stepST F_e2214 D_e2214 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x2c5c00) ltac:(sok_stack SOK).
      stepn F_e2218 D_e2218.
      stepn F_e221c D_e221c.
      stepn F_e2220 D_e2220.
      (* [comment removed for export] *)
      stepLBU F_e2224 D_e2224 (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
      stepn F_e2228 D_e2228.
      stepb_tk F_e222c D_e222c ltac:(cond_compute).
      stepn F_e2238 D_e2238.
      stepn F_e223c D_e223c.
      stepn F_e2240 D_e2240.
      (* [comment removed for export] *)
      stepST F_e2244 D_e2244 (Z_to_bv 64 0x323518) (Z_to_bv 64 1) ltac:(sok_data).
      change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
      (* [comment removed for export] *)
      stepn F_e2248 D_e2248.
      stepLD8 F_e224c D_e224c (Z_to_bv 64 0x2b5b9c).
      stepb_ft F_e2250 D_e2250 ltac:(cond_compute).
      stepn F_e2254 D_e2254.
      stepn F_e2258 D_e2258.
      stepn F_e225c D_e225c.
      stepLD8 F_e2260 D_e2260 (Z_to_bv 64 0x322bd8).
      stepn F_e2264 D_e2264.   (* [comment removed for export] *)
      stepjr F_e2268 D_e2268 (0x2b62ac : word) ltac:(gres; first [reflexivity | bveq]). vnorm.   (* [comment removed for export] *)
      stepret F_2b5b60 D_2b5b60 (0xe22b4 : word) ltac:(bveq).
      stepn F_e226c D_e226c.
      (* [comment removed for export] *)
      stepn F_e2270 D_e2270.
      stepLD8 F_e2274 D_e2274 (Z_to_bv 64 0).
      stepb_tk F_e2278 D_e2278 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD8 F_e2290 D_e2290 (Z_to_bv 64 0x2b5c9c).
      stepLD8 F_e2294 D_e2294 (Z_to_bv 64 0x2c5c00).
      stepn F_e2298 D_e2298. sp_renorm.
      stepret F_e229c D_e229c (0x2b5c9c : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepn F_2b5c60 D_2b5c60.
      stepb_ft F_2b5c64 D_2b5c64 ltac:(cond_compute).
      stepLD8 F_2b5c68 D_2b5c68 (Z_to_bv 64 0x2b5d20).
      stepLD8 F_2b5c6c D_2b5c6c code.
      stepLD8 F_2b5c70 D_2b5c70 s1v.
      stepn F_2b5c74 D_2b5c74. sp_renorm.
      (* [comment removed for export] *)
      stepn F_2b5c78 D_2b5c78.
      stepret F_2b5c2c D_2b5c2c (0x2b5d20 : word) ltac:(bveq).
      stepn F_2b5ce4 D_2b5ce4.
      apply mst_refl.
    + repeat split; gres; try reflexivity.
  - eexists. split.
    + (* [comment removed for export] *)
      stepn F_2b5c30 D_2b5c30. rewrite Hsp. sp_renorm.
      stepST F_2b5c34 D_2b5c34 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x2b5d20) ltac:(sok_stack SOK).
      stepST F_2b5c38 D_2b5c38 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
      stepST F_2b5c3c D_2b5c3c (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
      stepn F_2b5c40 D_2b5c40.
      stepn F_2b5c44 D_2b5c44.
      stepLD8 F_2b5c48 D_2b5c48 (Z_to_bv 64 0x2c5c10).
      stepLD8 F_2b5c4c D_2b5c4c (Z_to_bv 64 0x2c5c00).
      stepb_ft F_2b5c50 D_2b5c50 ltac:(cond_compute).
      stepLD8 F_2b5c54 D_2b5c54 (Z_to_bv 64 0xf1308).
      stepn F_2b5c58 D_2b5c58.
      stepjr F_2b5c5c D_2b5c5c (Z_to_bv 64 0xf1308) ltac:(gres; reflexivity). vnorm.
      stepn F_f12c0 D_f12c0. sp_renorm.
      stepST F_f12c4 D_f12c4 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x2b5c9c) ltac:(sok_stack SOK).
      stepST F_f12c8 D_f12c8 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x2c5c00) ltac:(sok_stack SOK).
      stepST F_f12cc D_f12cc (Z_to_bv 64 (bv_unsigned sp - 72)) (Z_to_bv 64 0x2c5c08) ltac:(sok_stack SOK).
      stepn F_f12d0 D_f12d0.
      stepn F_f12d4 D_f12d4.
      stepn F_f12d8 D_f12d8.
      (* [comment removed for export] *)
      stepLBU F_f12dc D_f12dc bi ltac:(addr_norm; rdn_by Mbi).
      stepb_ft F_f12e0 D_f12e0 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
      (* [comment removed for export] *)
      stepLBU F_f12e4 D_f12e4 (Z_to_bv 8 0) ltac:(addr_norm; rdn_by Mdgc).
      stepn F_f12e8 D_f12e8.
      stepb_tk F_f12ec D_f12ec ltac:(cond_compute).
      stepLD8 F_f1380 D_f1380 (Z_to_bv 64 0x2b5c9c).
      stepLD8 F_f1384 D_f1384 (Z_to_bv 64 0x2c5c00).
      stepLD8 F_f1388 D_f1388 (Z_to_bv 64 0x2c5c08).
      stepn F_f138c D_f138c. sp_renorm.
      stepret F_f1390 D_f1390 (0x2b5c9c : word) ltac:(bveq).
      stepn F_2b5c60 D_2b5c60.
      stepb_tk F_2b5c64 D_2b5c64 ltac:(cond_compute).
      stepLD8 F_2b5c54 D_2b5c54 (Z_to_bv 64 0xe2254).
      stepn F_2b5c58 D_2b5c58.
      stepjr F_2b5c5c D_2b5c5c (Z_to_bv 64 0xe2254) ltac:(gres; reflexivity). vnorm.
      (* [comment removed for export] *)
      stepn F_e220c D_e220c. sp_renorm.
      stepST F_e2210 D_e2210 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x2b5c9c) ltac:(sok_stack SOK).
      stepST F_e2214 D_e2214 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x2c5c00) ltac:(sok_stack SOK).
      stepn F_e2218 D_e2218.
      stepn F_e221c D_e221c.
      stepn F_e2220 D_e2220.
      (* [comment removed for export] *)
      stepLBU F_e2224 D_e2224 (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
      stepn F_e2228 D_e2228.
      stepb_tk F_e222c D_e222c ltac:(cond_compute).
      stepn F_e2238 D_e2238.
      stepn F_e223c D_e223c.
      stepn F_e2240 D_e2240.
      (* [comment removed for export] *)
      stepST F_e2244 D_e2244 (Z_to_bv 64 0x323518) (Z_to_bv 64 1) ltac:(sok_data).
      change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
      (* [comment removed for export] *)
      stepn F_e2248 D_e2248.
      stepLD8 F_e224c D_e224c (Z_to_bv 64 0x2b5b9c).
      stepb_ft F_e2250 D_e2250 ltac:(cond_compute).
      stepn F_e2254 D_e2254.
      stepn F_e2258 D_e2258.
      stepn F_e225c D_e225c.
      stepLD8 F_e2260 D_e2260 (Z_to_bv 64 0x322bd8).
      stepn F_e2264 D_e2264.   (* [comment removed for export] *)
      stepjr F_e2268 D_e2268 (0x2b62ac : word) ltac:(gres; first [reflexivity | bveq]). vnorm.   (* [comment removed for export] *)
      stepret F_2b5b60 D_2b5b60 (0xe22b4 : word) ltac:(bveq).
      stepn F_e226c D_e226c.
      (* [comment removed for export] *)
      stepn F_e2270 D_e2270.
      stepLD8 F_e2274 D_e2274 (Z_to_bv 64 0).
      stepb_tk F_e2278 D_e2278 ltac:(cond_compute).
      (* [comment removed for export] *)
      stepLD8 F_e2290 D_e2290 (Z_to_bv 64 0x2b5c9c).
      stepLD8 F_e2294 D_e2294 (Z_to_bv 64 0x2c5c00).
      stepn F_e2298 D_e2298. sp_renorm.
      stepret F_e229c D_e229c (0x2b5c9c : word) ltac:(bveq).
      (* [comment removed for export] *)
      stepn F_2b5c60 D_2b5c60.
      stepb_ft F_2b5c64 D_2b5c64 ltac:(cond_compute).
      stepLD8 F_2b5c68 D_2b5c68 (Z_to_bv 64 0x2b5d20).
      stepLD8 F_2b5c6c D_2b5c6c code.
      stepLD8 F_2b5c70 D_2b5c70 s1v.
      stepn F_2b5c74 D_2b5c74. sp_renorm.
      (* [comment removed for export] *)
      stepn F_2b5c78 D_2b5c78.
      stepret F_2b5c2c D_2b5c2c (0x2b5d20 : word) ltac:(bveq).
      stepn F_2b5ce4 D_2b5ce4.
      apply mst_refl.
    + repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
