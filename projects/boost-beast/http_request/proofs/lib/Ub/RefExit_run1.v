(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Ubsan.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic Ub_code_2b9a0_2bf8c Ub_code_6b4a8_6bc18 Ub_code_79f8c_7a2d4.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ub Require Import RefExitBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition mem_w1 (mem : word -> option byte) (sp ra s0 code s1 s2 s3 : word) (tid : Z) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
  (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 0xb6be0) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x6bc08)))  (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))                  (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3))
    (Z_to_bv 64 0xb69c0) [Z_to_bv 8 1].

Lemma w1 : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb6be0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  (* [comment removed for export] *)
  rdn RSEGS mem (Z_to_bv 64 0xb6c03) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0xb69c4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb69d0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x6bba4 : word) mem rom)
                 (mkst regs' (0x6bb58 : word) (mem_w1 mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x6bc0c
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Maxl Maxh.
  unfold mem_w1. eexists. split.
  - (* [comment removed for export] *)
    stepn F_6bba4 D_6bba4. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_6bba8 D_6bba8 (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_6bbac D_6bbac (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_6bbb0 D_6bbb0.
    stepn F_6bbb4 D_6bbb4. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_6bbb8 D_6bbb8 (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_6bbbc D_6bbbc.
    stepn F_6bbc0 D_6bbc0.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_6bbc4 | reflexivity | exact D_6bbc4
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_6bbc8 | reflexivity | exact D_6bbc8 | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_6bbcc | reflexivity | exact D_6bbcc
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_6bbd0 D_6bbd0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_6bbd4 D_6bbd4.
    (* [comment removed for export] *)
    stepb_ft F_6bbd8 D_6bbd8 ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_6bbdc D_6bbdc ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_6bc00 D_6bc00. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_6bc04 D_6bc04.
    (* [comment removed for export] *)
    stepn F_6b9c0 D_6b9c0. sp_renorm.
    stepST F_6b9c4 D_6b9c4 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x6bc08) ltac:(sok_stack SOK).
    stepST F_6b9c8 D_6b9c8 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_6b9cc D_6b9cc (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_6b9d0 D_6b9d0 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_6b9d4 D_6b9d4 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_6b9d8 D_6b9d8.
    stepn F_6b9dc D_6b9dc.
    stepn F_6b9e0 D_6b9e0.
    stepn F_6b9e4 D_6b9e4.
    stepn F_6b9e8 D_6b9e8.
    (* [comment removed for export] *)
    stepn F_79f8c D_79f8c.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_79f90 | reflexivity | exact D_79f90 | gres; imm_norm; addr_norm; rdn_by Mnl]
      | step_simpl]; vnorm.
    stepb_tk F_79f94 D_79f94 ltac:(cond_compute).
    stepret F_7a184 D_7a184 (0x6b9ec : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD8 F_6b9ec D_6b9ec (Z_to_bv 64 0).
    stepb_tk F_6b9f0 D_6b9f0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_6ba60 D_6ba60.
    stepST F_6ba64 D_6ba64 (Z_to_bv 64 0xb69c0) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_6ba68 D_6ba68.
    stepLD8 F_6ba6c D_6ba6c (Z_to_bv 64 0x6bc08).
    stepLD8 F_6ba70 D_6ba70 code.
    stepLD8 F_6ba74 D_6ba74 (getr regs 9).
    stepLD8 F_6ba78 D_6ba78 (getr regs 18).
    stepLD8 F_6ba7c D_6ba7c (getr regs 19).
    stepn F_6ba80 D_6ba80. sp_renorm.
    stepn F_6ba84 D_6ba84.
    (* [comment removed for export] *)
    stepLD F_7a214 D_7a214 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(rewrite v_addi_0; rdn_by Maxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_7a218 D_7a218 ltac:(cond_compute).
    stepret F_7a21c D_7a21c (0x6bc08 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_6bc08 D_6bc08.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.

(* [comment removed for export] *)
Definition mem_w2 (mem : word -> option byte) (sp code s1v : word) :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x6bc0c)))
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1v))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 (Z_to_bv 64 0x6bb88)))
    (Z_to_bv 64 (bv_unsigned sp - 64)) (word_to_le_bytes 8 (Z_to_bv 64 0x7e4a0)))
    (Z_to_bv 64 0x84f88) [Z_to_bv 8 1].

Lemma w2 : forall regs mem rom (sp code s1v : word),
  getr regs 2 = Z_to_bv 64 (bv_unsigned sp - 16) -> getr regs 8 = code ->
  getr regs 1 = Z_to_bv 64 0x6bc0c -> getr regs 9 = s1v ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  rdn RSEGS mem (Z_to_bv 64 0x83b60) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7e4a8)) ->
  rdn RSEGS mem (Z_to_bv 64 0x83b68) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7e4a0)) ->
  rdn RSEGS mem (Z_to_bv 64 0x7e4a0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2ba5c)) ->
  rdn RSEGS mem (Z_to_bv 64 0x84f88) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0x83a28) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6ba88)) ->
  rdn RSEGS mem (Z_to_bv 64 0x84b70) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x84b70)) ->
  rdn RSEGS mem (Z_to_bv 64 0x83a30) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  exists regs',
    msteps RSEGS (mkst regs (0x6bb58 : word) mem rom)
                 (mkst regs' (0x6ee94 : word) (mem_w2 mem sp code s1v) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x6bc10
    /\ getr regs' 9 = s1v
    /\ getr regs' 4 = getr regs 4 /\ getr regs' 3 = getr regs 3.
Proof.
  intros regs mem rom sp code s1v Hsp Hs0 Hra Hs1 SPlo SPhi SOK Mfe Mfs Mfa Mcomp Mg1 Mdso Mg2.
  unfold mem_w2. eexists. split.
  - (* [comment removed for export] *)
    stepn F_6bb58 D_6bb58. rewrite Hsp. sp_renorm.
    stepST F_6bb5c D_6bb5c (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x6bc0c) ltac:(sok_stack SOK).
    stepST F_6bb60 D_6bb60 (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_6bb64 D_6bb64 (Z_to_bv 64 (bv_unsigned sp - 40)) s1v ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_6bb68 D_6bb68.
    stepn F_6bb6c D_6bb6c.
    stepLD8 F_6bb70 D_6bb70 (Z_to_bv 64 0x7e4a8).
    stepLD8 F_6bb74 D_6bb74 (Z_to_bv 64 0x7e4a0).
    (* [comment removed for export] *)
    stepb_ft F_6bb78 D_6bb78 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_6bb7c D_6bb7c (Z_to_bv 64 0x2ba5c).
    stepn F_6bb80 D_6bb80.
    stepjr F_6bb84 D_6bb84 (Z_to_bv 64 0x2ba5c) ltac:(gres; reflexivity). vnorm.
    (* [comment removed for export] *)
    stepn F_2ba5c D_2ba5c. sp_renorm.
    stepST F_2ba60 D_2ba60 (Z_to_bv 64 (bv_unsigned sp - 56)) (Z_to_bv 64 0x6bb88) ltac:(sok_stack SOK).
    stepST F_2ba64 D_2ba64 (Z_to_bv 64 (bv_unsigned sp - 64)) (Z_to_bv 64 0x7e4a0) ltac:(sok_stack SOK).
    stepn F_2ba68 D_2ba68.
    stepn F_2ba6c D_2ba6c.
    stepn F_2ba70 D_2ba70.
    (* [comment removed for export] *)
    stepLBU F_2ba74 D_2ba74 (Z_to_bv 8 0) ltac:(rewrite v_addi_0; rdn_by Mcomp).
    stepn F_2ba78 D_2ba78.
    stepb_tk F_2ba7c D_2ba7c ltac:(cond_compute).
    stepn F_2ba88 D_2ba88.
    stepn F_2ba8c D_2ba8c.
    stepn F_2ba90 D_2ba90.
    (* [comment removed for export] *)
    stepST F_2ba94 D_2ba94 (Z_to_bv 64 0x84f88) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_2ba98 D_2ba98.
    stepLD8 F_2ba9c D_2ba9c (Z_to_bv 64 0x6ba88).
    stepb_ft F_2baa0 D_2baa0 ltac:(cond_compute).
    stepn F_2baa4 D_2baa4.
    stepn F_2baa8 D_2baa8.
    stepn F_2baac D_2baac.
    stepLD8 F_2bab0 D_2bab0 (Z_to_bv 64 0x84b70).
    stepn F_2bab4 D_2bab4.
    stepret F_6ba88 D_6ba88 (0x2bab8 : word) ltac:(bveq).
    stepn F_2bab8 D_2bab8.
    (* [comment removed for export] *)
    stepn F_2babc D_2babc.
    stepLD8 F_2bac0 D_2bac0 (Z_to_bv 64 0).
    stepb_tk F_2bac4 D_2bac4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_2badc D_2badc (Z_to_bv 64 0x6bb88).
    stepLD8 F_2bae0 D_2bae0 (Z_to_bv 64 0x7e4a0).
    stepn F_2bae4 D_2bae4. sp_renorm.
    stepret F_2bae8 D_2bae8 (0x6bb88 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_6bb88 D_6bb88.
    stepb_ft F_6bb8c D_6bb8c ltac:(cond_compute).
    stepLD8 F_6bb90 D_6bb90 (Z_to_bv 64 0x6bc0c).
    stepLD8 F_6bb94 D_6bb94 code.
    stepLD8 F_6bb98 D_6bb98 s1v.
    stepn F_6bb9c D_6bb9c. sp_renorm.
    (* [comment removed for export] *)
    stepn F_6bba0 D_6bba0.
    stepret F_6bb54 D_6bb54 (0x6bc0c : word) ltac:(bveq).
    stepn F_6bc0c D_6bc0c.
    apply mst_refl.
  - repeat split; gres; try reflexivity.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
