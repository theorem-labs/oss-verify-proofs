(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic
  RefExitBase Ref_code_2ab1c_2b108 Ref_code_6717c_678ec Ref_code_75c60_75fa8    .
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

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
Definition mem_w1x (mem : word -> option byte) (sp ra s0 code s1 s2 s3 : word) (tid : Z) :=
  wbytes (wbytes (wbytes (wbytes (wbytes
  (wbytes (wbytes (wbytes (wbytes (wbytes
  (wbytes (wbytes (wbytes mem
    (Z_to_bv 64 (bv_unsigned sp - 8)) (word_to_le_bytes 8 ra))
    (Z_to_bv 64 (bv_unsigned sp - 16)) (word_to_le_bytes 8 s0))
    (Z_to_bv 64 0xb28c0) (word_to_le_bytes 4 (Z_to_bv 64 tid)))
    (Z_to_bv 64 (bv_unsigned sp - 24)) (word_to_le_bytes 8 (Z_to_bv 64 0x678dc)))  (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp - 32)) (word_to_le_bytes 8 code))                  (* [comment removed for export] *)
    (Z_to_bv 64 (bv_unsigned sp - 40)) (word_to_le_bytes 8 s1))
    (Z_to_bv 64 (bv_unsigned sp - 48)) (word_to_le_bytes 8 s2))
    (Z_to_bv 64 (bv_unsigned sp - 56)) (word_to_le_bytes 8 s3))
    (Z_to_bv 64 0xb26a8) (word_to_le_bytes 4 (Z_to_bv 64 0)))                     (* [comment removed for export] *)
    (Z_to_bv 64 0xb26a8) (word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)))  (* [comment removed for export] *)
    (Z_to_bv 64 0xb26a8) (word_to_le_bytes 4 (Z_to_bv 64 32)))                    (* [comment removed for export] *)
    (Z_to_bv 64 0xb26b0) (word_to_le_bytes 8 (Z_to_bv 64 0)))                     (* [comment removed for export] *)
    (Z_to_bv 64 0xb26a0) [Z_to_bv 8 1].                                          (* [comment removed for export] *)

Lemma w1x : forall regs mem rom (sp tp code : word) (tid : Z),
  getr regs 2 = sp -> getr regs 4 = tp -> getr regs 10 = code ->
  (4294967296 <= bv_unsigned sp - 144)%Z -> (bv_unsigned sp <= 0x800000000000)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 144)) 144%nat = true ->
  (168 <= bv_unsigned tp)%Z -> (bv_unsigned tp <= 4294967296)%Z ->
  (0 < tid < 2147483648)%Z ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned tp - 168)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 tid)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb28c0) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb28e3) 1%nat = Some [Z_to_bv 8 0] ->
  rdn RSEGS mem (Z_to_bv 64 0xb26a4) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
  (* [comment removed for export] *)
  rdn RSEGS mem (Z_to_bv 64 0xb26b0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0xb26b8)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb26a8) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb26b8) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb26c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x67824)) ->
  rdn RSEGS mem (Z_to_bv 64 0xb27c0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x2b090)) ->
  rdn RSEGS mem (Z_to_bv 64 0x90c74) 1%nat = Some [Z_to_bv 8 0] ->
  exists regs',
    msteps RSEGS (mkst regs (0x67878 : word) mem rom)
                 (mkst regs' (0x6782c : word) (mem_w1x mem sp (getr regs 1) (getr regs 8) code (getr regs 9) (getr regs 18) (getr regs 19) tid) rom)
    /\ getr regs' 2 = Z_to_bv 64 (bv_unsigned sp - 16)
    /\ getr regs' 8 = code
    /\ getr regs' 1 = Z_to_bv 64 0x678e0
    /\ getr regs' 4 = tp /\ getr regs' 3 = getr regs 3 /\ getr regs' 9 = getr regs 9.
Proof.
  intros regs mem rom sp tp code tid Hsp Htp Ha0 SPlo SPhi SOK TPlo TPhi TID Mtid Mlock Mnl Maxl Mhead Mslot Mnext Mf0 Marg Mincb.
  unfold mem_w1x. eexists. split.
  - (* [comment removed for export] *)
    stepn F_67878 D_67878. rewrite Hsp. sp_renorm.
    (* [comment removed for export] *)
    stepST F_6787c D_6787c (Z_to_bv 64 (bv_unsigned sp - 8)) (getr regs 1) ltac:(sok_stack SOK).
    stepST F_67880 D_67880 (Z_to_bv 64 (bv_unsigned sp - 16)) (getr regs 8) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_67884 D_67884.
    stepn F_67888 D_67888. rewrite Htp.
    (* [comment removed for export] *)
    stepLD F_6788c D_6788c (word_to_le_bytes 4 (Z_to_bv 64 tid)) (Z_to_bv 64 tid)
      ltac:(change (v_addi tp (-168)) with (Z_to_bv 64 (bv_unsigned tp - 168)); rdn_by Mtid)
      ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    rewrite (v_lw_small tid) by lia.
    (* [comment removed for export] *)
    stepn F_67890 D_67890.
    stepn F_67894 D_67894.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_lr_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
        [ exact F_67898 | reflexivity | exact D_67898
        | gres; u_norm; reflexivity
        | gres; rdn_by Mlock
        | apply bytes_le_to_Z_4; u_norm; lia ]
      | ].
    reduce_bv_eqb_ifs; norm_pc_r; vnorm.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_bne_ft_r; [exact F_6789c | reflexivity | exact D_6789c | gres; cond_compute ] | ].
    norm_pc_r.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity
      | eapply step_sc_w_ok; [exact F_678a0 | reflexivity | exact D_678a0
        | gres; u_norm; reflexivity | gres; reflexivity | gres; sok_data ] | ].
    step_simpl; vnorm.
    (* [comment removed for export] *)
    stepb_ft F_678a4 D_678a4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_678a8 D_678a8.
    (* [comment removed for export] *)
    stepb_ft F_678ac D_678ac ltac:(unfold c_eq, bv_eqb; apply Z.eqb_neq; u_norm; lia).
    (* [comment removed for export] *)
    stepb_tk F_678b0 D_678b0 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepn F_678d4 D_678d4. rewrite Ha0.
    (* [comment removed for export] *)
    stepn F_678d8 D_678d8.
    (* [comment removed for export] *)
    stepn F_67694 D_67694. sp_renorm.
    stepST F_67698 D_67698 (Z_to_bv 64 (bv_unsigned sp - 24)) (Z_to_bv 64 0x678dc) ltac:(sok_stack SOK).
    stepST F_6769c D_6769c (Z_to_bv 64 (bv_unsigned sp - 32)) code ltac:(sok_stack SOK).
    stepST F_676a0 D_676a0 (Z_to_bv 64 (bv_unsigned sp - 40)) (getr regs 9) ltac:(sok_stack SOK).
    stepST F_676a4 D_676a4 (Z_to_bv 64 (bv_unsigned sp - 48)) (getr regs 18) ltac:(sok_stack SOK).
    stepST F_676a8 D_676a8 (Z_to_bv 64 (bv_unsigned sp - 56)) (getr regs 19) ltac:(sok_stack SOK).
    (* [comment removed for export] *)
    stepn F_676ac D_676ac.
    stepn F_676b0 D_676b0.
    stepn F_676b4 D_676b4.
    stepn F_676b8 D_676b8.
    stepn F_676bc D_676bc.
    (* [comment removed for export] *)
    stepn F_75c60 D_75c60.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_75c64 | reflexivity | exact D_75c64 | gres; imm_norm; addr_norm; rdn_by Mnl]
      | step_simpl]; vnorm.
    stepb_tk F_75c68 D_75c68 ltac:(cond_compute).
    stepret F_75e58 D_75e58 (0x676c0 : word) ltac:(bveq).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepLD8 F_676c0 D_676c0 (Z_to_bv 64 0xb26b8).
    stepb_ft F_676c4 D_676c4 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD F_676c8 D_676c8 (word_to_le_bytes 4 (Z_to_bv 64 1)) (Z_to_bv 64 1)
      ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 1) by lia.
    stepn F_676cc D_676cc.
    (* [comment removed for export] *)
    stepn F_676e4 D_676e4.
    stepST F_676e8 D_676e8 (Z_to_bv 64 0xb26a8) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_ft F_676ec D_676ec ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_676f0 D_676f0 (Z_to_bv 64 0xb26b8).
    stepn F_676f4 D_676f4.
    stepn F_676f8 D_676f8.
    stepLD8 F_676fc D_676fc (Z_to_bv 64 0x67824).
    stepLD8 F_67700 D_67700 (Z_to_bv 64 0x2b090).
    (* [comment removed for export] *)
    stepn F_67704 D_67704.
    stepn F_67708 D_67708.
    stepLD F_75ee8 D_75ee8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(rewrite v_addi_0; rdn_by Maxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_75eec D_75eec ltac:(cond_compute).
    stepret F_75ef0 D_75ef0 (0x6770c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_6770c D_6770c.
    stepjr F_67710 D_67710 (0x67824 : word) ltac:(gres; bveq).
    (* [comment removed for export] *)
    stepjr F_67824 D_67824 (0x2b090 : word) ltac:(gres; bveq).
    (* [comment removed for export] *)
    stepn F_2b090 D_2b090.
    stepLBU F_2b094 D_2b094 (Z_to_bv 8 0) ltac:(addr_norm; rdn_by Mincb).
    stepb_ft F_2b098 D_2b098 ltac:(cond_compute).
    stepret F_2b09c D_2b09c (0x67714 : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_67714 D_67714.
    stepn F_67718 D_67718.
    stepn F_75c60 D_75c60.
    chain_step; [reflexivity
      | eapply step_lb with (b := Z_to_bv 8 0);
        [exact F_75c64 | reflexivity | exact D_75c64 | gres; imm_norm; addr_norm; rdn_by Mnl]
      | step_simpl]; vnorm.
    stepb_tk F_75c68 D_75c68 ltac:(cond_compute).
    stepret F_75e58 D_75e58 (0x6771c : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepLD F_6771c D_6771c (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(addr_norm; apply rdn_wbytes_hit4; u_norm; lia) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    try rewrite (v_lw_small 0) by lia.
    stepn F_67720 D_67720.
    stepST F_67724 D_67724 (Z_to_bv 64 0xb26a8) (Z_to_bv 64 18446744073709551615) ltac:(sok_data).
    stepb_ft F_67728 D_67728 ltac:(cond_compute).
    (* [comment removed for export] *)
    stepLD8 F_6772c D_6772c (Z_to_bv 64 0xb26b8).
    stepn F_67730 D_67730.
    (* [comment removed for export] *)
    stepLD8 F_676d0 D_676d0 (Z_to_bv 64 0).
    stepn F_676d4 D_676d4.
    stepST F_676d8 D_676d8 (Z_to_bv 64 0xb26a8) (Z_to_bv 64 32) ltac:(sok_data).
    stepST F_676dc D_676dc (Z_to_bv 64 0xb26b0) (Z_to_bv 64 0) ltac:(sok_data).
    stepb_tk F_676e0 D_676e0 ltac:(cond_compute).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    stepn F_67734 D_67734.
    stepST F_67738 D_67738 (Z_to_bv 64 0xb26a0) (Z_to_bv 64 1) ltac:(sok_data).
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (Z_to_bv 8 1).
    (* [comment removed for export] *)
    stepn F_6773c D_6773c.
    stepLD8 F_67740 D_67740 (Z_to_bv 64 0x678dc).
    stepLD8 F_67744 D_67744 code.
    stepLD8 F_67748 D_67748 (getr regs 9).
    stepLD8 F_6774c D_6774c (getr regs 18).
    stepLD8 F_67750 D_67750 (getr regs 19).
    stepn F_67754 D_67754. sp_renorm.
    stepn F_67758 D_67758.
    (* [comment removed for export] *)
    stepLD F_75ee8 D_75ee8 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
      ltac:(rewrite v_addi_0; rdn_by Maxl) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
    stepb_ft F_75eec D_75eec ltac:(cond_compute).
    stepret F_75ef0 D_75ef0 (0x678dc : word) ltac:(bveq).
    (* [comment removed for export] *)
    stepn F_678dc D_678dc.
    apply mst_refl.
  - repeat split; gres; try reflexivity. exact Htp.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
