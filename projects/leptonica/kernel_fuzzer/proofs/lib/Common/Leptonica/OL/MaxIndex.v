(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Reloc Require Import RelocKitOL RelocTacOL CanonImgOL RCodeOL_23720_24000 RCodeOL_24000_24fe0.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Musl Require Import MuslTac.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := rl_segs.

Section VPORT.
Context {fx : FPState} {RLOC : Reloc} {RCODE : RelocCode RLOC} {RSITES : RelocSites RLOC} {RCODEF : RelocCodeOL RLOC} {RSITESF : RelocSitesOL RLOC} {RLEPT : RelocLept RLOC} {RIMGF : RelocImgOL RLOC}.   (* [comment removed for export] *)


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma wr_readable_s16 : wr_readable SEGS.
Proof. exact rl_wr_readable. Qed.

Section MI.
  (* [comment removed for export] *)
  Variable M : word -> option byte.          (* [comment removed for export] *)
  Variable rom : word -> option byte.
  Variables pix pmax w h d wpl data sp : Z.
  Variables ra s0v s1v s2v s3v s4v s5v : word.   (* [comment removed for export] *)

  Hypothesis Hpix : (1 <= pix /\ pix + 64 <= 2 ^ 64)%Z.
  Hypothesis Hpmax : (1 <= pmax /\ pmax + 4 <= 2 ^ 64)%Z.
  Hypothesis Rw : (0 <= w < 2 ^ 32)%Z.
  Hypothesis Rh : (0 <= h < 2 ^ 32)%Z.
  Hypothesis Rd : (0 <= d < 2 ^ 32)%Z.
  Hypothesis Rwpl : (0 <= wpl < 2 ^ 32)%Z.
  Hypothesis Hw : (1 <= w <= 20000)%Z.
  Hypothesis Hh : (1 <= h <= 20000)%Z.
  Hypothesis Hd : (d = 1 \/ d = 2 \/ d = 4 \/ d = 8)%Z.
  Hypothesis Hwpl : (wpl = (w * d + 31) / 32)%Z.
  Hypothesis Hdata : (4 <= data /\ data < 2 ^ 64)%Z.
  Hypothesis Hdal : (data mod 4 = 0)%Z.
  Hypothesis Hsp : (144 <= sp /\ sp < 2 ^ 64)%Z.
  Hypothesis Hra : ret_ok ra.
  (* [comment removed for export] *)
  Hypothesis Cw : rdn SEGS M (Z_to_bv 64 pix) 4 = Some (Z_to_le_bytes 4 w).
  Hypothesis Ch : rdn SEGS M (Z_to_bv 64 (pix + 4)) 4 = Some (Z_to_le_bytes 4 h).
  Hypothesis Cd : rdn SEGS M (Z_to_bv 64 (pix + 8)) 4 = Some (Z_to_le_bytes 4 d).
  Hypothesis Cwpl : rdn SEGS M (Z_to_bv 64 (pix + 16)) 4 = Some (Z_to_le_bytes 4 wpl).
  Hypothesis Cdata : rdn SEGS M (Z_to_bv 64 (pix + 56)) 8 = Some (Z_to_le_bytes 8 data).
  (* [comment removed for export] *)
  Hypothesis HR : (data + 4 * (wpl * h) <= 2 ^ 64)%Z.
  Hypothesis RR : exists bs, rdn SEGS M (Z_to_bv 64 data) (Z.to_nat (4 * (wpl * h))) = Some bs.
  (* [comment removed for export] *)
  Hypothesis SOKp : store_ok SEGS M (Z_to_bv 64 pmax) 4 = true.
  Hypothesis AP : (pmax + 4 <= pix \/ pix + 64 <= pmax)%Z.
  Hypothesis FPM : (pmax + 4 <= sp - 144 \/ sp <= pmax)%Z.
  (* [comment removed for export] *)
  Hypothesis SOKf : store_ok SEGS M (Z_to_bv 64 (sp - 144)) 144 = true.
  Hypothesis FP : (pix + 64 <= sp - 144 \/ sp <= pix)%Z.

  (* [comment removed for export] *)
  Ltac nodisj := try clear FP; try clear FPM; try clear AP.

  (* [comment removed for export] *)
  Lemma wpl_bounds : (0 <= wpl <= 5001 /\ w * d <= 32 * wpl /\ 32 * wpl <= w * d + 31)%Z.
  Proof.
    nodisj. clear RR HR Cwpl Rwpl.
    assert (Hwd : (1 <= w * d <= 20000 * 8)%Z) by (destruct Hd as [->|[->|[->| ->]]]; lia).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    subst wpl. split; [|split].
    - split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; lia.
    - pose proof (Z.div_mod (w * d + 31) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (w * d + 31) 32 ltac:(lia)). lia.
    - pose proof (Z.div_mod (w * d + 31) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (w * d + 31) 32 ltac:(lia)). lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  (* [comment removed for export] *)
  Definition MA : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
      (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (sp - 16)) (word_to_le_bytes 8 s0v))
      (Z_to_bv 64 (sp - 24)) (word_to_le_bytes 8 s1v))
      (Z_to_bv 64 (sp - 32)) (word_to_le_bytes 8 s2v))
      (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 8 s3v))
      (Z_to_bv 64 (sp - 48)) (word_to_le_bytes 8 s4v))
      (Z_to_bv 64 (sp - 56)) (word_to_le_bytes 8 s5v).
  (* [comment removed for export] *)
  Definition MB : word -> option byte :=
    wbytes MA (Z_to_bv 64 pmax) (word_to_le_bytes 4 (Z_to_bv 64 0)).
  (* [comment removed for export] *)
  Definition MC : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes MB
      (Z_to_bv 64 (sp - 60)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 64)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 68)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 60)) (word_to_le_bytes 4 (Z_to_bv 64 w)))
      (Z_to_bv 64 (sp - 64)) (word_to_le_bytes 4 (Z_to_bv 64 h)))
      (Z_to_bv 64 (sp - 68)) (word_to_le_bytes 4 (Z_to_bv 64 d)).

  (* [comment removed for export] *)
  Lemma sok_frame : forall m k (n : nat), mem_grows M m -> (Z.of_nat n <= k <= 144)%Z ->
    store_ok SEGS m (Z_to_bv 64 (sp - k)) n = true.
  Proof.
    intros m k n Hg Hk. nodisj. eapply store_ok_mono; [exact Hg|].
    destruct n as [|n']; [reflexivity|].
    eapply (store_ok_sub SEGS M (Z_to_bv 64 (sp - 144)) _ 144%nat); [ | exact SOKf | | ];
      rewrite ?u_Z2bv by lia; lia.
  Qed.

  Lemma sok_pmax : forall m, mem_grows M m -> store_ok SEGS m (Z_to_bv 64 pmax) 4 = true.
  Proof. intros m Hg. nodisj. eapply store_ok_mono; [exact Hg | exact SOKp]. Qed.

  Ltac grows := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
  Lemma MA_grows : mem_grows M MA. Proof. nodisj. unfold MA. grows. Qed.
  Lemma MB_grows : mem_grows M MB. Proof. nodisj. unfold MB, MA. grows. Qed.
  Lemma MC_grows : mem_grows M MC. Proof. nodisj. unfold MC, MB, MA. grows. Qed.

  (* [comment removed for export] *)
  Ltac sokf := apply sok_frame; [ unfold MC, MB, MA; grows | cbn; lia ].

  (* [comment removed for export] *)
  Ltac peelf := unfold MC, MB, MA;
    repeat (rewrite rdn_wbytes_out_Z by (zlen; rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).

  (* [comment removed for export] *)
  Ltac stf F D k v := stepST F D (Z_to_bv 64 (sp - k)) v ltac:(sokf).
  (* [comment removed for export] *)
  Ltac ldpix F D z C :=
    stepLD F D (Z_to_le_bytes 4 z) (Z_to_bv 64 z)
      ltac:(unfold v_addi; unorm; rewrite ?Z.add_0_r; peelf; exact C)
      ltac:(apply lez4; lia);
    rewrite (v_lw_small z) by lia.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mi_A : forall regs,
    getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 sp ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v ->
    getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 pmax ->
    exists regs',
      msteps SEGS (mkst regs (rl dOL_246d4 0x246d4) M rom) (mkst regs' (rl dOL_246d4 0x2471c) MC rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 80) /\ getr regs' 9 = Z_to_bv 64 pix /\ getr regs' 18 = Z_to_bv 64 pmax
      /\ regs_agree (fun r : reg => In r [1; 2; 9; 10; 11; 12; 13; 14; 18]%list) regs regs'.
  Proof.
    intros regs H1 H2 H8 H9 H18 H19 H20 H21 H10 H11. clear RR.
    pose proof (u64_range ra) as Hrar.
    eexists. split.
    - zv F_246d4 D_246d4 (Z_to_bv 64 (sp - 80)).           (* [comment removed for export] *)
      stf F_246d8 D_246d8 8%Z ra.                             (* [comment removed for export] *)
      stf F_246dc D_246dc 16%Z s0v.                           (* [comment removed for export] *)
      stf F_246e0 D_246e0 24%Z s1v.                           (* [comment removed for export] *)
      stf F_246e4 D_246e4 32%Z s2v.                           (* [comment removed for export] *)
      stf F_246e8 D_246e8 40%Z s3v.                           (* [comment removed for export] *)
      stf F_246ec D_246ec 48%Z s4v.                           (* [comment removed for export] *)
      stf F_246f0 D_246f0 56%Z s5v.                           (* [comment removed for export] *)
      fold MA.
      stepb_ft F_246f4 D_246f4 ltac:(condZ).                (* [comment removed for export] *)
      zv F_246f8 D_246f8 (Z_to_bv 64 pix).                  (* [comment removed for export] *)
      stepST F_246fc D_246fc (Z_to_bv 64 pmax) (Z_to_bv 64 0) ltac:(apply sok_pmax; unfold MA; grows).  (* [comment removed for export] *)
      fold MB.
      stepb_ft F_24700 D_24700 ltac:(condZ).                (* [comment removed for export] *)
      zv F_24704 D_24704 (Z_to_bv 64 pmax).                 (* [comment removed for export] *)
      zv F_24708 D_24708 (Z_to_bv 64 (sp - 60)).           (* [comment removed for export] *)
      zv F_2470c D_2470c (Z_to_bv 64 (sp - 64)).           (* [comment removed for export] *)
      zv F_24710 D_24710 (Z_to_bv 64 (sp - 68)).           (* [comment removed for export] *)
      zv F_24714 D_24714 (Z_to_bv 64 pix).                  (* [comment removed for export] *)
      sn F_24718 D_24718.                                   (* [comment removed for export] *)
      (* [comment removed for export] *)
      stepb_ft F_23cf0 D_23cf0 ltac:(condZ).                (* [comment removed for export] *)
      stf F_23cf4 D_23cf4 60%Z (Z_to_bv 64 0).                (* [comment removed for export] *)
      stepb_ft F_23cf8 D_23cf8 ltac:(condZ).                (* [comment removed for export] *)
      stf F_23cfc D_23cfc 64%Z (Z_to_bv 64 0).                (* [comment removed for export] *)
      stepb_ft F_23d00 D_23d00 ltac:(condZ).                (* [comment removed for export] *)
      stf F_23d04 D_23d04 68%Z (Z_to_bv 64 0).                (* [comment removed for export] *)
      stepb_ft F_23d08 D_23d08 ltac:(condZ).                (* [comment removed for export] *)
      stepb_ft F_23d0c D_23d0c ltac:(condZ).                (* [comment removed for export] *)
      ldpix F_23d10 D_23d10 w Cw.                           (* [comment removed for export] *)
      stf F_23d14 D_23d14 60%Z (Z_to_bv 64 w).                (* [comment removed for export] *)
      stepb_ft F_23d18 D_23d18 ltac:(condZ).                (* [comment removed for export] *)
      ldpix F_23d1c D_23d1c h Ch.                           (* [comment removed for export] *)
      stf F_23d20 D_23d20 64%Z (Z_to_bv 64 h).                (* [comment removed for export] *)
      sn F_23d24 D_23d24.                                   (* [comment removed for export] *)
      stepb_ft F_23d28 D_23d28 ltac:(condZ).                (* [comment removed for export] *)
      ldpix F_23d2c D_23d2c d Cd.                           (* [comment removed for export] *)
      stf F_23d30 D_23d30 68%Z (Z_to_bv 64 d).                (* [comment removed for export] *)
      sn F_23d34 D_23d34.                                   (* [comment removed for export] *)
      stepretF F_23d38 D_23d38 F_2471c. (* [comment removed for export] *)
      fold MC.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Ltac ldf F D k z :=
    stepLD F D (word_to_le_bytes 4 (Z_to_bv 64 z)) (Z_to_bv 64 z)
      ltac:(unfold MC, MB, MA; rdn_addr (sp - k)%Z; rdn_chain)
      ltac:(apply bytes_le_to_Z_4; unorm; lia);
    try rewrite (v_lw_small z) by lia.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mi_B : forall regs,
    getr regs 2 = Z_to_bv 64 (sp - 80) -> getr regs 9 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (rl dOL_246d4 0x2471c) MC rom) (mkst regs' (rl dOL_246d4 0x24754) MC rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 80) /\ getr regs' 10 = Z_to_bv 64 data /\ getr regs' 8 = Z_to_bv 64 wpl
      /\ getr regs' 5 = Z_to_bv 64 d /\ getr regs' 11 = Z_to_bv 64 1
      /\ regs_agree (fun r : reg => In r [1; 5; 8; 10; 11]%list) regs regs'.
  Proof.
    intros regs H2 H9. clear RR.
    pose proof wpl_bounds as (Hwpl1 & _ & _).
    eexists. split.
    - ldf F_2471c D_2471c 68%Z d.                           (* [comment removed for export] *)
      sn F_24720 D_24720.                                   (* [comment removed for export] *)
      stepb_ft F_24724 D_24724 ltac:(condZ).                (* [comment removed for export] *)
      sn F_24728 D_24728.                                   (* [comment removed for export] *)
      sn F_2472c D_2472c.                                   (* [comment removed for export] *)
      sn F_24730 D_24730.                                   (* [comment removed for export] *)
      stepb_ft F_24734 D_24734 ltac:(pin; rewrite (depth_mask_278 d Hd); reflexivity).   (* [comment removed for export] *)
      zv F_24738 D_24738 (Z_to_bv 64 pix).                  (* [comment removed for export] *)
      sn F_2473c D_2473c.                                   (* [comment removed for export] *)
      stepb_ft F_23be4 D_23be4 ltac:(condZ).                (* [comment removed for export] *)
      ldpix F_23be8 D_23be8 wpl Cwpl.                       (* [comment removed for export] *)
      stepretF F_23bec D_23bec F_24740. (* [comment removed for export] *)
      zv F_24740 D_24740 (Z_to_bv 64 wpl).                  (* [comment removed for export] *)
      zv F_24744 D_24744 (Z_to_bv 64 pix).                  (* [comment removed for export] *)
      sn F_24748 D_24748.                                   (* [comment removed for export] *)
      stepb_ft F_23ed4 D_23ed4 ltac:(condZ).                (* [comment removed for export] *)
      stepLD F_23ed8 D_23ed8 (Z_to_le_bytes 8 data) (Z_to_bv 64 data)
        ltac:(unfold v_addi; unorm; peelf; exact Cdata)
        ltac:(apply lez8; lia).                             (* [comment removed for export] *)
      stepretF F_23edc D_23edc F_2474c. (* [comment removed for export] *)
      ldf F_2474c D_2474c 68%Z d.                           (* [comment removed for export] *)
      sn F_24750 D_24750.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Ltac zvw F D v := stepiv F D v ltac:(gres; pin; imm_norm; rewrite ?v_addi_0; rewrite ?zbv_addiw_small by lia;
                                       rewrite ?zbv_addi, ?zbv_add, ?zbv_sub, ?zbv_mul; first [reflexivity | f_equal; lia]).
  Ltac zvs F D v := stepiv F D v ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
  (* [comment removed for export] *)
  Ltac condE := pin; rewrite c_eq_Z by lia; first [ apply Z.eqb_eq | apply Z.eqb_neq ]; lia.
  (* [comment removed for export] *)
  Ltac fixv v tac :=
    lazymatch goal with |- msteps _ (mkst (regupd _ _ ?x) _ _ _) _ => replace x with v by (symmetry; tac) end.

  (* [comment removed for export] *)
  Definition LInv (regs : bvmap 5 word) (t1v a6v : word) : Prop :=
    getr regs 2 = Z_to_bv 64 (sp - 80) /\ getr regs 10 = Z_to_bv 64 data /\ getr regs 11 = Z_to_bv 64 h /\
    getr regs 13 = Z_to_bv 64 d /\ getr regs 14 = Z_to_bv 64 (4 * wpl) /\ getr regs 15 = Z_to_bv 64 2 /\
    getr regs 16 = a6v /\ getr regs 17 = Z_to_bv 64 4 /\ getr regs 6 = t1v /\ getr regs 7 = Z_to_bv 64 w /\
    getr regs 28 = Z_to_bv 64 (data + w) /\ getr regs 29 = Z_to_bv 64 8 /\ getr regs 5 = Z_to_bv 64 pmax /\
    getr regs 8 = Z_to_bv 64 wpl.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mi_D : forall regs, (d <> 1)%Z ->
    getr regs 2 = Z_to_bv 64 (sp - 80) -> getr regs 10 = Z_to_bv 64 data -> getr regs 8 = Z_to_bv 64 wpl ->
    getr regs 5 = Z_to_bv 64 d -> getr regs 11 = Z_to_bv 64 1 -> getr regs 18 = Z_to_bv 64 pmax ->
    exists regs' t1v a6v,
      msteps SEGS (mkst regs (rl dOL_246d4 0x24754) MC rom) (mkst regs' (rl dOL_246d4 0x24830) MC rom)
      /\ LInv regs' t1v a6v
      /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 30 = Z_to_bv 64 (data + 4 * wpl * 0) /\ getr regs' 31 = Z_to_bv 64 0
      /\ regs_agree (fun r : reg => In r [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs Hd1 H2 H10 H8 H5 H11 H18. clear RR.
    pose proof wpl_bounds as (Hwpl1 & _ & _).
    eexists. eexists. eexists. split; [|split].
    - stepb_tk F_24754 D_24754 ltac:(condZ).                (* [comment removed for export] *)
      ldf F_247ec D_247ec 64%Z h.                           (* [comment removed for export] *)
      stepb_ft F_247f0 D_247f0 ltac:(condZ).                (* [comment removed for export] *)
      sn F_247f4 D_247f4.                                   (* [comment removed for export] *)
      sn F_247f8 D_247f8.                                   (* [comment removed for export] *)
      zvw F_247fc D_247fc (Z_to_bv 64 d).                   (* [comment removed for export] *)
      sn F_24800 D_24800.                                   (* [comment removed for export] *)
      ldf F_24804 D_24804 60%Z w.                           (* [comment removed for export] *)
      zvs F_24808 D_24808 (Z_to_bv 64 (4 * wpl)).           (* [comment removed for export] *)
      sn F_2480c D_2480c.                                   (* [comment removed for export] *)
      sn F_24810 D_24810.                                   (* [comment removed for export] *)
      sn F_24814 D_24814.                                   (* [comment removed for export] *)
      sn F_24818 D_24818.                                   (* [comment removed for export] *)
      zvw F_2481c D_2481c (Z_to_bv 64 w).                   (* [comment removed for export] *)
      zvw F_24820 D_24820 (Z_to_bv 64 (data + w)).          (* [comment removed for export] *)
      sn F_24824 D_24824.                                   (* [comment removed for export] *)
      zvw F_24828 D_24828 (Z_to_bv 64 (data + 4 * wpl * 0)).   (* [comment removed for export] *)
      zvw F_2482c D_2482c (Z_to_bv 64 pmax).                (* [comment removed for export] *)
      apply mst_refl.
    - unfold LInv. repeat split; gres; pin; reflexivity.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  Lemma row_base_al4 : forall i, ((data + 4 * wpl * i) mod 4 = 0)%Z.
  Proof.
    intros i. nodisj. clear RR. replace (data + 4 * wpl * i)%Z with (data + (wpl * i) * 4)%Z by lia.
    rewrite Z_mod_plus_full. exact Hdal.
  Qed.

  Lemma row_in_raster : forall i, (0 <= i < h)%Z -> (4 * wpl * i + 4 * wpl <= 4 * (wpl * h))%Z.
  Proof.
    intros i Hi. nodisj. clear RR. pose proof wpl_bounds as (Hwpl1 & _).
    assert (wpl * (i + 1) <= wpl * h)%Z by (apply Z.mul_le_mono_nonneg_l; lia). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma byte8_at : forall i p, (d = 8)%Z -> (0 <= i < h)%Z ->
    (data + 4 * wpl * i <= p < data + 4 * wpl * i + w)%Z ->
    exists f b, v_xori (Z_to_bv 64 p) 3 = Z_to_bv 64 f /\ (data <= f /\ f + 1 <= data + 4 * (wpl * h))%Z
                /\ rdn SEGS MC (Z_to_bv 64 f) 1 = Some [b].
  Proof.
    intros i p Hd8 Hi Hp. nodisj.
    pose proof wpl_bounds as (Hwpl1 & Hwd & _). rewrite Hd8 in Hwd.
    pose proof (row_in_raster i Hi) as Hrow.
    pose proof (flip3_bounds (data + 4 * wpl * i) wpl p (row_base_al4 i) ltac:(lia)) as Hf.
    set (f := (p - p mod 4 + (3 - p mod 4))%Z) in *.
    exists f.
    destruct RR as [rbs Hrbs].
    destruct (rdn_sub_grows SEGS M MC data (Z.to_nat (4 * (wpl * h))) rbs (f - data) 1
                ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) Hrbs MC_grows ltac:(lia) ltac:(rewrite Z2Nat.id by lia; cbn; lia))
      as (bs & Hbs & Lbs).
    destruct bs as [|b [|]]; try discriminate Lbs.
    exists b. split; [|split; [lia|]].
    - apply zbv_xori3. lia.
    - replace (data + (f - data))%Z with f in Hbs by lia. exact Hbs.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  (* [comment removed for export] *)
  Lemma mi_b8 : forall regs i p (mx : word), (d = 8)%Z -> (0 <= i < h)%Z ->
    (data + 4 * wpl * i <= p < data + 4 * wpl * i + w)%Z ->
    getr regs 18 = Z_to_bv 64 p -> getr regs 31 = mx -> (bv_unsigned mx <= 255)%Z ->
    exists regs' (mx' : word),
      msteps SEGS (mkst regs (rl dOL_246d4 0x24864) MC rom) (mkst regs' (rl dOL_246d4 0x2485c) MC rom)
      /\ getr regs' 31 = mx' /\ (bv_unsigned mx' <= 255)%Z /\ getr regs' 18 = Z_to_bv 64 p
      /\ regs_agree (fun r : reg => In r [19; 31]%list) regs regs'.
  Proof.
    intros regs i p mx Hd8 Hi Hp H18 H31 Hmx. nodisj.
    destruct (byte8_at i p Hd8 Hi Hp) as (f & b & Hxf & Hf & Hb). clear RR.
    pose proof (u_byte64 b) as Hbr.
    destruct (c_lts (Z_to_bv 64 (bv_unsigned b)) mx) eqn:Hc.
    - (* [comment removed for export] *)
      eexists. exists mx. split.
      + stepiv F_24864 D_24864 (Z_to_bv 64 f) ltac:(gres; pin; imm_norm; exact Hxf).   (* [comment removed for export] *)
        stepLBU F_24868 D_24868 b ltac:(rdn_addr f; exact Hb).                           (* [comment removed for export] *)
        stepb_tk F_2486c D_2486c ltac:(pin; exact Hc).                                    (* [comment removed for export] *)
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity; try assumption. solve_regs_agree.
    - (* [comment removed for export] *)
      eexists. exists (Z_to_bv 64 (bv_unsigned b)). split.
      + stepiv F_24864 D_24864 (Z_to_bv 64 f) ltac:(gres; pin; imm_norm; exact Hxf).   (* [comment removed for export] *)
        stepLBU F_24868 D_24868 b ltac:(rdn_addr f; exact Hb).                           (* [comment removed for export] *)
        stepb_ft F_2486c D_2486c ltac:(pin; exact Hc).                                    (* [comment removed for export] *)
        zvw F_24870 D_24870 (Z_to_bv 64 (bv_unsigned b)).                                (* [comment removed for export] *)
        sn F_24874 D_24874.                                                               (* [comment removed for export] *)
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity; try lia. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma mi_L8 : forall k regs i p (mx : word), (d = 8)%Z -> (0 <= i < h)%Z ->
    (Z.of_nat k = data + 4 * wpl * i + w - 1 - p)%Z -> (data + 4 * wpl * i <= p)%Z ->
    getr regs 9 = Z_to_bv 64 (data + w + 4 * wpl * i) -> getr regs 18 = Z_to_bv 64 p -> getr regs 31 = mx ->
    (bv_unsigned mx <= 255)%Z ->
    exists regs' (mx' : word),
      msteps SEGS (mkst regs (rl dOL_246d4 0x24864) MC rom) (mkst regs' (rl dOL_246d4 0x24918) MC rom)
      /\ getr regs' 31 = mx' /\ (bv_unsigned mx' <= 255)%Z
      /\ regs_agree (fun r : reg => In r [18; 19; 31]%list) regs regs'.
  Proof.
    nodisj. pose proof wpl_bounds as (Hwpl1 & Hwd & _).
    induction k as [|k IH]; intros regs i p mx Hd8 Hi Hk Hp H9 H18 H31 Hmx;
      destruct (mi_b8 regs i p mx Hd8 Hi ltac:(lia) H18 H31 Hmx) as (r1 & mx1 & S1 & R31 & Hmx1 & R18 & AG1);
      pose proof (AG1 9 ltac:(notin_list)) as R9; rewrite H9 in R9;
      pose proof (row_in_raster i Hi) as Hrow; rewrite Hd8 in Hwd.
    - (* [comment removed for export] *)
      eexists. exists mx1. split; [|split; [|split; [exact Hmx1|]]].
      + eapply msteps_trans; [exact S1|].
        zvw F_2485c D_2485c (Z_to_bv 64 (p + 1)).            (* [comment removed for export] *)
        stepb_tk F_24860 D_24860 ltac:(condP).                (* [comment removed for export] *)
        apply mst_refl.
      + gres. exact R31.
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - assert (S2 : exists r2, msteps SEGS (mkst r1 (rl dOL_246d4 0x2485c) MC rom) (mkst r2 (rl dOL_246d4 0x24864) MC rom)
                              /\ getr r2 9 = Z_to_bv 64 (data + w + 4 * wpl * i) /\ getr r2 18 = Z_to_bv 64 (p + 1)
                              /\ getr r2 31 = mx1 /\ regs_agree (fun r : reg => In r [18]%list) r1 r2).
      { eexists. split.
        - zvw F_2485c D_2485c (Z_to_bv 64 (p + 1)).          (* [comment removed for export] *)
          stepb_ft F_24860 D_24860 ltac:(condP).              (* [comment removed for export] *)
          apply mst_refl.
        - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
      destruct S2 as (r2 & S2 & Q9 & Q18 & Q31 & AG2).
      destruct (IH r2 i (p + 1)%Z mx1 Hd8 Hi ltac:(lia) ltac:(lia) Q9 Q18 Q31 Hmx1) as (r3 & mx3 & S3 & T31 & Hmx3 & AG3).
      exists r3, mx3. split; [|split; [exact T31 | split; [exact Hmx3|]]].
      + eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2 | exact S3].
      + eapply regs_agree_trans; [regs_agree_weaken AG1|].
        eapply regs_agree_trans; [regs_agree_weaken AG2 | exact AG3].
  Qed.

  (* [comment removed for export] *)
  Definition maxval : Z := (2 ^ d - 1)%Z.
  Lemma maxval_ge : (1 <= maxval <= 255)%Z.
  Proof. nodisj. clear RR. unfold maxval. destruct Hd as [->|[->|[->| ->]]]; cbn; lia. Qed.

  (* [comment removed for export] *)
  Lemma mi_R8 : forall regs t1v a6v i (mx : word), (d = 8)%Z -> (0 <= i < h)%Z ->
    LInv regs t1v a6v -> getr regs 12 = Z_to_bv 64 i -> getr regs 30 = Z_to_bv 64 (data + 4 * wpl * i) ->
    getr regs 31 = mx -> (bv_unsigned mx <= maxval)%Z ->
    exists regs' (mx' : word),
      msteps SEGS (mkst regs (rl dOL_246d4 0x2483c) MC rom) (mkst regs' (rl dOL_246d4 0x24918) MC rom)
      /\ getr regs' 31 = mx' /\ (bv_unsigned mx' <= maxval)%Z
      /\ regs_agree (fun r : reg => In r [9; 18; 19; 20; 21; 31]%list) regs regs'.
  Proof.
    intros regs t1v a6v i mx Hd8 Hi HL H12 H30 H31 Hmx. nodisj.
    destruct HL as (I2 & I10 & I11 & I13 & I14 & I15 & I16 & I17 & I6 & I7 & I28 & I29 & I5 & I8).
    pose proof wpl_bounds as (Hwpl1 & Hwd & _). rewrite Hd8 in Hwd.
    pose proof (row_in_raster i Hi) as Hrow.
    assert (Hmv : maxval = 255%Z) by (unfold maxval; rewrite Hd8; reflexivity). rewrite Hmv in Hmx |- *.
    assert (S1 : exists r1, msteps SEGS (mkst regs (rl dOL_246d4 0x2483c) MC rom) (mkst r1 (rl dOL_246d4 0x24864) MC rom)
                            /\ getr r1 9 = Z_to_bv 64 (data + w + 4 * wpl * i) /\ getr r1 18 = Z_to_bv 64 (data + 4 * wpl * i)
                            /\ getr r1 31 = mx /\ regs_agree (fun r : reg => In r [9; 18]%list) regs r1).
    { eexists. split.
      - stepb_ft F_2483c D_2483c ltac:(condZ).              (* [comment removed for export] *)
        stepb_ft F_24840 D_24840 ltac:(condZ).              (* [comment removed for export] *)
        stepb_ft F_24844 D_24844 ltac:(condZ).              (* [comment removed for export] *)
        stepb_ft F_24848 D_24848 ltac:(condZ).              (* [comment removed for export] *)
        zvw F_2484c D_2484c (Z_to_bv 64 (4 * wpl * i)).     (* [comment removed for export] *)
        zvw F_24850 D_24850 (Z_to_bv 64 (data + w + 4 * wpl * i)).   (* [comment removed for export] *)
        zvw F_24854 D_24854 (Z_to_bv 64 (data + 4 * wpl * i)).       (* [comment removed for export] *)
        sn F_24858 D_24858.                                 (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
    destruct S1 as (r1 & S1 & Q9 & Q18 & Q31 & AG1).
    destruct (mi_L8 (Z.to_nat (w - 1)) r1 i (data + 4 * wpl * i)%Z mx Hd8 Hi ltac:(lia) ltac:(lia) Q9 Q18 Q31 Hmx)
      as (r2 & mx2 & S2 & T31 & Hmx2 & AG2).
    exists r2, mx2. split; [|split; [exact T31 | split; [exact Hmx2|]]].
    - eapply msteps_trans; [exact S1 | exact S2].
    - eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma word_at : forall i q, (0 <= i < h)%Z -> (0 <= q < wpl)%Z ->
    exists bs, rdn SEGS MC (Z_to_bv 64 (data + 4 * wpl * i + 4 * q)) 4 = Some bs /\ length bs = 4%nat.
  Proof.
    intros i q Hi Hq. nodisj. pose proof (row_in_raster i Hi) as Hrow.
    destruct RR as [rbs Hrbs].
    destruct (rdn_sub_grows SEGS M MC data (Z.to_nat (4 * (wpl * h))) rbs (4 * wpl * i + 4 * q) 4
                ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) Hrbs MC_grows ltac:(lia) ltac:(rewrite Z2Nat.id by lia; cbn; lia))
      as (bs & Hbs & Lbs).
    exists bs. rewrite Z.add_assoc in Hbs. exact (conj Hbs Lbs).
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma qbit_word : forall j, (d = 4)%Z -> (0 <= j < w)%Z -> (0 <= j / 8 < wpl)%Z.
  Proof.
    intros j Hd4 Hj. nodisj. clear RR. pose proof wpl_bounds as (_ & Hwd & _). rewrite Hd4 in Hwd.
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
  Qed.
  Lemma dibit_word : forall j, (d = 2)%Z -> (0 <= j < w)%Z -> (0 <= j / 16 < wpl)%Z.
  Proof.
    intros j Hd2 Hj. nodisj. clear RR. pose proof wpl_bounds as (_ & Hwd & _). rewrite Hd2 in Hwd.
    split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  (* [comment removed for export] *)
  Lemma mi_w4 : forall regs i j (s2w mx : word), (d = 4)%Z -> (0 <= i < h)%Z -> (0 <= j < w)%Z ->
    getr regs 9 = Z_to_bv 64 (data + 4 * wpl * i) -> getr regs 19 = Z_to_bv 64 j -> getr regs 18 = s2w ->
    getr regs 20 = mx -> getr regs 31 = mx ->
    exists regs' (v : word),
      msteps SEGS (mkst regs (rl dOL_246d4 0x2489c) MC rom) (mkst regs' (rl dOL_246d4 0x248bc) MC rom)
      /\ getr regs' 31 = v /\ (bv_unsigned v <= 15)%Z
      /\ getr regs' 9 = Z_to_bv 64 (data + 4 * wpl * i) /\ getr regs' 19 = Z_to_bv 64 j /\ getr regs' 18 = s2w
      /\ getr regs' 20 = mx
      /\ regs_agree (fun r : reg => In r [21; 31]%list) regs regs'.
  Proof.
    intros regs i j s2w mx Hd4 Hi Hj H9 H19 H18 H20 H31. nodisj.
    pose proof (qbit_word j Hd4 Hj) as Hq. pose proof (row_in_raster i Hi) as Hrow.
    destruct (word_at i (j / 8) Hi Hq) as (bs & Hbs & Lbs). clear RR.
    eexists. eexists. split; [|split; [|split]].
    - sn F_2489c D_2489c.                                   (* [comment removed for export] *)
      fixv (Z_to_bv 64 (j / 8)) ltac:(change (2 ^ 3)%Z with 8%Z; apply zbv_srliw_small; lia).
      zvs F_248a0 D_248a0 (Z_to_bv 64 (4 * (j / 8))).       (* [comment removed for export] *)
      zvw F_248a4 D_248a4 (Z_to_bv 64 (data + 4 * wpl * i + 4 * (j / 8))).   (* [comment removed for export] *)
      stepLD F_248a8 D_248a8 bs (Z_to_bv 64 (bytes_le_to_Z bs))
        ltac:(rdn_addr (data + 4 * wpl * i + 4 * (j / 8))%Z; exact Hbs)
        ltac:(symmetry; apply u_lez4; exact Lbs).          (* [comment removed for export] *)
      sn F_248ac D_248ac.                                   (* [comment removed for export] *)
      sn F_248b0 D_248b0.                                   (* [comment removed for export] *)
      sn F_248b4 D_248b4.                                   (* [comment removed for export] *)
      sn F_248b8 D_248b8.                                   (* [comment removed for export] *)
      apply mst_refl.
    - gres. reflexivity.
    - apply u_andi_15.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma mi_b4 : forall regs i j (s2w mx : word), (d = 4)%Z -> (0 <= i < h)%Z -> (0 <= j < w)%Z ->
    getr regs 9 = Z_to_bv 64 (data + 4 * wpl * i) -> getr regs 19 = Z_to_bv 64 j -> getr regs 18 = s2w ->
    getr regs 20 = mx -> getr regs 31 = mx -> (bv_unsigned mx <= 15)%Z ->
    exists regs' (mx' : word),
      msteps SEGS (mkst regs (rl dOL_246d4 0x2489c) MC rom) (mkst regs' (rl dOL_246d4 0x24898) MC rom)
      /\ getr regs' 31 = mx' /\ getr regs' 20 = mx' /\ (bv_unsigned mx' <= 15)%Z
      /\ getr regs' 9 = Z_to_bv 64 (data + 4 * wpl * i) /\ getr regs' 19 = Z_to_bv 64 (j + 1)
      /\ regs_agree (fun r : reg => In r [18; 19; 20; 21; 31]%list) regs regs'.
  Proof.
    intros regs i j s2w mx Hd4 Hi Hj H9 H19 H18 H20 H31 Hmx. nodisj.
    destruct (mi_w4 regs i j s2w mx Hd4 Hi Hj H9 H19 H18 H20 H31) as (r1 & v & S1 & Q31 & Hv & Q9 & Q19 & Q18 & Q20 & AG1).
    pose proof (u64_range v) as Hvr. pose proof (u64_range mx) as Hmxr.
    destruct (c_lts mx v) eqn:Hc.
    - (* [comment removed for export] *)
      eexists. exists v. split.
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_248bc D_248bc ltac:(pin; exact Hc).      (* [comment removed for export] *)
        zvw F_2488c D_2488c (Z_to_bv 64 (j + 1)).           (* [comment removed for export] *)
        sn F_24890 D_24890.                                 (* [comment removed for export] *)
        zvw F_24894 D_24894 v.                              (* [comment removed for export] *)
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity; try assumption.
        eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - (* [comment removed for export] *)
      eexists. exists mx. split.
      + eapply msteps_trans; [exact S1|].
        stepb_ft F_248bc D_248bc ltac:(pin; exact Hc).      (* [comment removed for export] *)
        zvw F_248c0 D_248c0 mx.                             (* [comment removed for export] *)
        sn F_248c4 D_248c4.                                 (* [comment removed for export] *)
        zvw F_2488c D_2488c (Z_to_bv 64 (j + 1)).           (* [comment removed for export] *)
        sn F_24890 D_24890.                                 (* [comment removed for export] *)
        zvw F_24894 D_24894 mx.                             (* [comment removed for export] *)
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity; try assumption.
        eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma mi_L4 : forall k regs i j (s2w mx : word), (d = 4)%Z -> (0 <= i < h)%Z ->
    (Z.of_nat k = w - 1 - j)%Z -> (0 <= j)%Z ->
    getr regs 7 = Z_to_bv 64 w ->
    getr regs 9 = Z_to_bv 64 (data + 4 * wpl * i) -> getr regs 19 = Z_to_bv 64 j -> getr regs 18 = s2w ->
    getr regs 20 = mx -> getr regs 31 = mx -> (bv_unsigned mx <= 15)%Z ->
    exists regs' (mx' : word),
      msteps SEGS (mkst regs (rl dOL_246d4 0x2489c) MC rom) (mkst regs' (rl dOL_246d4 0x24918) MC rom)
      /\ getr regs' 31 = mx' /\ (bv_unsigned mx' <= 15)%Z
      /\ regs_agree (fun r : reg => In r [18; 19; 20; 21; 31]%list) regs regs'.
  Proof.
    nodisj.
    induction k as [|k IH]; intros regs i j s2w mx Hd4 Hi Hk Hj H7 H9 H19 H18 H20 H31 Hmx;
      destruct (mi_b4 regs i j s2w mx Hd4 Hi ltac:(lia) H9 H19 H18 H20 H31 Hmx)
        as (r1 & mx1 & S1 & R31 & R20 & Hmx1 & R9 & R19 & AG1);
      pose proof (AG1 7 ltac:(notin_list)) as R7; rewrite H7 in R7.
    - (* [comment removed for export] *)
      eexists. exists mx1. split; [|split; [exact R31 | split; [exact Hmx1|]]].
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_24898 D_24898 ltac:(condZ).                (* [comment removed for export] *)
        apply mst_refl.
      + exact AG1.
    - assert (S2 : msteps SEGS (mkst r1 (rl dOL_246d4 0x24898) MC rom) (mkst r1 (rl dOL_246d4 0x2489c) MC rom)).
      { stepb_ft F_24898 D_24898 ltac:(condZ).                (* [comment removed for export] *)
        apply mst_refl. }
      destruct (IH r1 i (j + 1)%Z (getr r1 18) mx1 Hd4 Hi ltac:(lia) ltac:(lia) R7 R9 R19 eq_refl R20 R31 Hmx1)
        as (r3 & mx3 & S3 & T31 & Hmx3 & AG3).
      exists r3, mx3. split; [|split; [exact T31 | split; [exact Hmx3|]]].
      + eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2 | exact S3].
      + eapply regs_agree_trans; [exact AG1 | exact AG3].
  Qed.

  (* [comment removed for export] *)
  Lemma mi_R4 : forall regs t1v a6v i (mx : word), (d = 4)%Z -> (0 <= i < h)%Z ->
    LInv regs t1v a6v -> getr regs 12 = Z_to_bv 64 i -> getr regs 9 = Z_to_bv 64 (data + 4 * wpl * i) ->
    getr regs 31 = mx -> (bv_unsigned mx <= maxval)%Z ->
    exists regs' (mx' : word),
      msteps SEGS (mkst regs (rl dOL_246d4 0x2483c) MC rom) (mkst regs' (rl dOL_246d4 0x24918) MC rom)
      /\ getr regs' 31 = mx' /\ (bv_unsigned mx' <= maxval)%Z
      /\ regs_agree (fun r : reg => In r [9; 18; 19; 20; 21; 31]%list) regs regs'.
  Proof.
    intros regs t1v a6v i mx Hd4 Hi HL H12 H9 H31 Hmx. nodisj.
    destruct HL as (I2 & I10 & I11 & I13 & I14 & I15 & I16 & I17 & I6 & I7 & I28 & I29 & I5 & I8).
    assert (Hmv : maxval = 15%Z) by (unfold maxval; rewrite Hd4; reflexivity). rewrite Hmv in Hmx |- *.
    assert (S1 : exists r1, msteps SEGS (mkst regs (rl dOL_246d4 0x2483c) MC rom) (mkst r1 (rl dOL_246d4 0x2489c) MC rom)
                            /\ getr r1 7 = Z_to_bv 64 w /\ getr r1 9 = Z_to_bv 64 (data + 4 * wpl * i)
                            /\ getr r1 19 = Z_to_bv 64 0 /\ getr r1 20 = mx /\ getr r1 31 = mx
                            /\ regs_agree (fun r : reg => In r [18; 19; 20]%list) regs r1).
    { eexists. split.
      - stepb_ft F_2483c D_2483c ltac:(condZ).              (* [comment removed for export] *)
        stepb_tk F_24840 D_24840 ltac:(condZ).              (* [comment removed for export] *)
        stepb_ft F_24878 D_24878 ltac:(condZ).              (* [comment removed for export] *)
        sn F_2487c D_2487c.                                 (* [comment removed for export] *)
        sn F_24880 D_24880.                                 (* [comment removed for export] *)
        zvw F_24884 D_24884 mx.                             (* [comment removed for export] *)
        sn F_24888 D_24888.                                 (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
    destruct S1 as (r1 & S1 & Q7 & Q9 & Q19 & Q20 & Q31 & AG1).
    destruct (mi_L4 (Z.to_nat (w - 1)) r1 i 0 (getr r1 18) mx Hd4 Hi ltac:(lia) ltac:(lia) Q7 Q9 Q19 eq_refl Q20 Q31 Hmx)
      as (r2 & mx2 & S2 & T31 & Hmx2 & AG2).
    exists r2, mx2. split; [|split; [exact T31 | split; [exact Hmx2|]]].
    - eapply msteps_trans; [exact S1 | exact S2].
    - eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
  Qed.

  (* [comment removed for export] *)
  Lemma mi_w2 : forall regs i j (s2w mx : word), (d = 2)%Z -> (0 <= i < h)%Z -> (0 <= j < w)%Z ->
    getr regs 9 = Z_to_bv 64 (data + 4 * wpl * i) -> getr regs 19 = Z_to_bv 64 j -> getr regs 18 = s2w ->
    getr regs 20 = mx -> getr regs 31 = mx ->
    exists regs' (v : word),
      msteps SEGS (mkst regs (rl dOL_246d4 0x248ec) MC rom) (mkst regs' (rl dOL_246d4 0x2490c) MC rom)
      /\ getr regs' 31 = v /\ (bv_unsigned v <= 3)%Z
      /\ getr regs' 9 = Z_to_bv 64 (data + 4 * wpl * i) /\ getr regs' 19 = Z_to_bv 64 j /\ getr regs' 18 = s2w
      /\ getr regs' 20 = mx
      /\ regs_agree (fun r : reg => In r [21; 31]%list) regs regs'.
  Proof.
    intros regs i j s2w mx Hd2 Hi Hj H9 H19 H18 H20 H31. nodisj.
    pose proof (dibit_word j Hd2 Hj) as Hq. pose proof (row_in_raster i Hi) as Hrow.
    destruct (word_at i (j / 16) Hi Hq) as (bs & Hbs & Lbs). clear RR.
    eexists. eexists. split; [|split; [|split]].
    - sn F_248ec D_248ec.                                   (* [comment removed for export] *)
      fixv (Z_to_bv 64 (j / 16)) ltac:(change (2 ^ 4)%Z with 16%Z; apply zbv_srliw_small; lia).
      zvs F_248f0 D_248f0 (Z_to_bv 64 (4 * (j / 16))).       (* [comment removed for export] *)
      zvw F_248f4 D_248f4 (Z_to_bv 64 (data + 4 * wpl * i + 4 * (j / 16))).   (* [comment removed for export] *)
      stepLD F_248f8 D_248f8 bs (Z_to_bv 64 (bytes_le_to_Z bs))
        ltac:(rdn_addr (data + 4 * wpl * i + 4 * (j / 16))%Z; exact Hbs)
        ltac:(symmetry; apply u_lez4; exact Lbs).          (* [comment removed for export] *)
      sn F_248fc D_248fc.                                   (* [comment removed for export] *)
      sn F_24900 D_24900.                                   (* [comment removed for export] *)
      sn F_24904 D_24904.                                   (* [comment removed for export] *)
      sn F_24908 D_24908.                                   (* [comment removed for export] *)
      apply mst_refl.
    - gres. reflexivity.
    - apply u_andi_3.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma mi_b2 : forall regs i j (s2w mx : word), (d = 2)%Z -> (0 <= i < h)%Z -> (0 <= j < w)%Z ->
    getr regs 9 = Z_to_bv 64 (data + 4 * wpl * i) -> getr regs 19 = Z_to_bv 64 j -> getr regs 18 = s2w ->
    getr regs 20 = mx -> getr regs 31 = mx -> (bv_unsigned mx <= 3)%Z ->
    exists regs' (mx' : word),
      msteps SEGS (mkst regs (rl dOL_246d4 0x248ec) MC rom) (mkst regs' (rl dOL_246d4 0x248e8) MC rom)
      /\ getr regs' 31 = mx' /\ getr regs' 20 = mx' /\ (bv_unsigned mx' <= 3)%Z
      /\ getr regs' 9 = Z_to_bv 64 (data + 4 * wpl * i) /\ getr regs' 19 = Z_to_bv 64 (j + 1)
      /\ regs_agree (fun r : reg => In r [18; 19; 20; 21; 31]%list) regs regs'.
  Proof.
    intros regs i j s2w mx Hd2 Hi Hj H9 H19 H18 H20 H31 Hmx. nodisj.
    destruct (mi_w2 regs i j s2w mx Hd2 Hi Hj H9 H19 H18 H20 H31) as (r1 & v & S1 & Q31 & Hv & Q9 & Q19 & Q18 & Q20 & AG1).
    pose proof (u64_range v) as Hvr. pose proof (u64_range mx) as Hmxr.
    destruct (c_lts mx v) eqn:Hc.
    - (* [comment removed for export] *)
      eexists. exists v. split.
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_2490c D_2490c ltac:(pin; exact Hc).      (* [comment removed for export] *)
        zvw F_248dc D_248dc (Z_to_bv 64 (j + 1)).           (* [comment removed for export] *)
        sn F_248e0 D_248e0.                                 (* [comment removed for export] *)
        zvw F_248e4 D_248e4 v.                              (* [comment removed for export] *)
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity; try assumption.
        eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - (* [comment removed for export] *)
      eexists. exists mx. split.
      + eapply msteps_trans; [exact S1|].
        stepb_ft F_2490c D_2490c ltac:(pin; exact Hc).      (* [comment removed for export] *)
        zvw F_24910 D_24910 mx.                             (* [comment removed for export] *)
        sn F_24914 D_24914.                                 (* [comment removed for export] *)
        zvw F_248dc D_248dc (Z_to_bv 64 (j + 1)).           (* [comment removed for export] *)
        sn F_248e0 D_248e0.                                 (* [comment removed for export] *)
        zvw F_248e4 D_248e4 mx.                             (* [comment removed for export] *)
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity; try assumption.
        eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma mi_L2 : forall k regs i j (s2w mx : word), (d = 2)%Z -> (0 <= i < h)%Z ->
    (Z.of_nat k = w - 1 - j)%Z -> (0 <= j)%Z ->
    getr regs 7 = Z_to_bv 64 w ->
    getr regs 9 = Z_to_bv 64 (data + 4 * wpl * i) -> getr regs 19 = Z_to_bv 64 j -> getr regs 18 = s2w ->
    getr regs 20 = mx -> getr regs 31 = mx -> (bv_unsigned mx <= 3)%Z ->
    exists regs' (mx' : word),
      msteps SEGS (mkst regs (rl dOL_246d4 0x248ec) MC rom) (mkst regs' (rl dOL_246d4 0x24918) MC rom)
      /\ getr regs' 31 = mx' /\ (bv_unsigned mx' <= 3)%Z
      /\ regs_agree (fun r : reg => In r [18; 19; 20; 21; 31]%list) regs regs'.
  Proof.
    nodisj.
    induction k as [|k IH]; intros regs i j s2w mx Hd2 Hi Hk Hj H7 H9 H19 H18 H20 H31 Hmx;
      destruct (mi_b2 regs i j s2w mx Hd2 Hi ltac:(lia) H9 H19 H18 H20 H31 Hmx)
        as (r1 & mx1 & S1 & R31 & R20 & Hmx1 & R9 & R19 & AG1);
      pose proof (AG1 7 ltac:(notin_list)) as R7; rewrite H7 in R7.
    - (* [comment removed for export] *)
      eexists. exists mx1. split; [|split; [exact R31 | split; [exact Hmx1|]]].
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_248e8 D_248e8 ltac:(condZ).                (* [comment removed for export] *)
        apply mst_refl.
      + exact AG1.
    - assert (S2 : msteps SEGS (mkst r1 (rl dOL_246d4 0x248e8) MC rom) (mkst r1 (rl dOL_246d4 0x248ec) MC rom)).
      { stepb_ft F_248e8 D_248e8 ltac:(condZ).                (* [comment removed for export] *)
        apply mst_refl. }
      destruct (IH r1 i (j + 1)%Z (getr r1 18) mx1 Hd2 Hi ltac:(lia) ltac:(lia) R7 R9 R19 eq_refl R20 R31 Hmx1)
        as (r3 & mx3 & S3 & T31 & Hmx3 & AG3).
      exists r3, mx3. split; [|split; [exact T31 | split; [exact Hmx3|]]].
      + eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2 | exact S3].
      + eapply regs_agree_trans; [exact AG1 | exact AG3].
  Qed.

  (* [comment removed for export] *)
  Lemma mi_R2 : forall regs t1v a6v i (mx : word), (d = 2)%Z -> (0 <= i < h)%Z ->
    LInv regs t1v a6v -> getr regs 12 = Z_to_bv 64 i -> getr regs 9 = Z_to_bv 64 (data + 4 * wpl * i) ->
    getr regs 31 = mx -> (bv_unsigned mx <= maxval)%Z ->
    exists regs' (mx' : word),
      msteps SEGS (mkst regs (rl dOL_246d4 0x2483c) MC rom) (mkst regs' (rl dOL_246d4 0x24918) MC rom)
      /\ getr regs' 31 = mx' /\ (bv_unsigned mx' <= maxval)%Z
      /\ regs_agree (fun r : reg => In r [9; 18; 19; 20; 21; 31]%list) regs regs'.
  Proof.
    intros regs t1v a6v i mx Hd2 Hi HL H12 H9 H31 Hmx. nodisj.
    destruct HL as (I2 & I10 & I11 & I13 & I14 & I15 & I16 & I17 & I6 & I7 & I28 & I29 & I5 & I8).
    assert (Hmv : maxval = 3%Z) by (unfold maxval; rewrite Hd2; reflexivity). rewrite Hmv in Hmx |- *.
    assert (S1 : exists r1, msteps SEGS (mkst regs (rl dOL_246d4 0x2483c) MC rom) (mkst r1 (rl dOL_246d4 0x248ec) MC rom)
                            /\ getr r1 7 = Z_to_bv 64 w /\ getr r1 9 = Z_to_bv 64 (data + 4 * wpl * i)
                            /\ getr r1 19 = Z_to_bv 64 0 /\ getr r1 20 = mx /\ getr r1 31 = mx
                            /\ regs_agree (fun r : reg => In r [18; 19; 20]%list) regs r1).
    { eexists. split.
      - stepb_tk F_2483c D_2483c ltac:(condZ).              (* [comment removed for export] *)
        stepb_ft F_248c8 D_248c8 ltac:(condZ).              (* [comment removed for export] *)
        sn F_248cc D_248cc.                                 (* [comment removed for export] *)
        sn F_248d0 D_248d0.                                 (* [comment removed for export] *)
        zvw F_248d4 D_248d4 mx.                             (* [comment removed for export] *)
        sn F_248d8 D_248d8.                                 (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
    destruct S1 as (r1 & S1 & Q7 & Q9 & Q19 & Q20 & Q31 & AG1).
    destruct (mi_L2 (Z.to_nat (w - 1)) r1 i 0 (getr r1 18) mx Hd2 Hi ltac:(lia) ltac:(lia) Q7 Q9 Q19 eq_refl Q20 Q31 Hmx)
      as (r2 & mx2 & S2 & T31 & Hmx2 & AG2).
    exists r2, mx2. split; [|split; [exact T31 | split; [exact Hmx2|]]].
    - eapply msteps_trans; [exact S1 | exact S2].
    - eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
  Qed.

  (* [comment removed for export] *)
  Lemma mi_row : forall regs t1v a6v i (mx : word), (d <> 1)%Z -> (0 <= i < h)%Z ->
    LInv regs t1v a6v -> getr regs 12 = Z_to_bv 64 i -> getr regs 30 = Z_to_bv 64 (data + 4 * wpl * i) ->
    getr regs 31 = mx -> (bv_unsigned mx <= maxval)%Z ->
    exists regs' (mx' : word),
      msteps SEGS (mkst regs (rl dOL_246d4 0x24830) MC rom) (mkst regs' (rl dOL_246d4 0x24918) MC rom)
      /\ getr regs' 31 = mx' /\ (bv_unsigned mx' <= maxval)%Z
      /\ LInv regs' t1v a6v /\ getr regs' 12 = Z_to_bv 64 i /\ getr regs' 30 = Z_to_bv 64 (data + 4 * wpl * i)
      /\ regs_agree (fun r : reg => In r [9; 18; 19; 20; 21; 31]%list) regs regs'.
  Proof.
    intros regs t1v a6v i mx Hd1 Hi HL H12 H30 H31 Hmx. nodisj.
    pose proof HL as (I2 & I10 & I11 & I13 & I14 & I15 & I16 & I17 & I6 & I7 & I28 & I29 & I5 & I8).
    assert (S1 : exists r1, msteps SEGS (mkst regs (rl dOL_246d4 0x24830) MC rom) (mkst r1 (rl dOL_246d4 0x2483c) MC rom)
                            /\ getr r1 9 = Z_to_bv 64 (data + 4 * wpl * i) /\ regs_agree (fun r : reg => In r [9]%list) regs r1).
    { eexists. split.
      - zvw F_24830 D_24830 (Z_to_bv 64 (i * wpl)).         (* [comment removed for export] *)
        zvs F_24834 D_24834 (Z_to_bv 64 (4 * wpl * i)).     (* [comment removed for export] *)
        zvw F_24838 D_24838 (Z_to_bv 64 (data + 4 * wpl * i)).   (* [comment removed for export] *)
        apply mst_refl.
      - split; [gres; reflexivity | solve_regs_agree]. }
    destruct S1 as (r1 & S1 & Q9 & AG1).
    assert (HL1 : LInv r1 t1v a6v).
    { unfold LInv. rewrite !AG1 by notin_list. exact HL. }
    pose proof (AG1 12 ltac:(notin_list)) as Q12. rewrite H12 in Q12.
    pose proof (AG1 30 ltac:(notin_list)) as Q30. rewrite H30 in Q30.
    pose proof (AG1 31 ltac:(notin_list)) as Q31. rewrite H31 in Q31.
    assert (S2 : exists r2 (mx' : word),
      msteps SEGS (mkst r1 (rl dOL_246d4 0x2483c) MC rom) (mkst r2 (rl dOL_246d4 0x24918) MC rom)
      /\ getr r2 31 = mx' /\ (bv_unsigned mx' <= maxval)%Z
      /\ regs_agree (fun r : reg => In r [9; 18; 19; 20; 21; 31]%list) r1 r2).
    { destruct Hd as [Hd0|[Hd2|[Hd4|Hd8]]]; [lia| | |].
      - exact (mi_R2 r1 t1v a6v i mx Hd2 Hi HL1 Q12 Q9 Q31 Hmx).
      - exact (mi_R4 r1 t1v a6v i mx Hd4 Hi HL1 Q12 Q9 Q31 Hmx).
      - exact (mi_R8 r1 t1v a6v i mx Hd8 Hi HL1 Q12 Q30 Q31 Hmx). }
    destruct S2 as (r2 & mx2 & S2 & T31 & Hmx2 & AG2).
    exists r2, mx2. split; [|split; [exact T31 | split; [exact Hmx2 | split; [|split; [|split]]]]].
    - eapply msteps_trans; [exact S1 | exact S2].
    - unfold LInv. rewrite !AG2 by notin_list. exact HL1.
    - rewrite AG2 by notin_list. exact Q12.
    - rewrite AG2 by notin_list. exact Q30.
    - eapply regs_agree_trans; [regs_agree_weaken AG1 | exact AG2].
  Qed.

  (* [comment removed for export] *)
  Lemma mi_loop : forall k regs t1v a6v i (mx : word), (d <> 1)%Z ->
    (Z.of_nat k = h - 1 - i)%Z -> (0 <= i)%Z ->
    LInv regs t1v a6v -> getr regs 12 = Z_to_bv 64 i -> getr regs 30 = Z_to_bv 64 (data + 4 * wpl * i) ->
    getr regs 31 = mx -> (bv_unsigned mx <= maxval)%Z ->
    exists regs' (mx' : word),
      msteps SEGS (mkst regs (rl dOL_246d4 0x24830) MC rom) (mkst regs' (rl dOL_246d4 0x24970) MC rom)
      /\ getr regs' 31 = mx' /\ (bv_unsigned mx' <= maxval)%Z
      /\ getr regs' 2 = Z_to_bv 64 (sp - 80) /\ getr regs' 5 = Z_to_bv 64 pmax
      /\ regs_agree (fun r : reg => In r [9; 12; 18; 19; 20; 21; 30; 31]%list) regs regs'.
  Proof.
    nodisj.
    induction k as [|k IH]; intros regs t1v a6v i mx Hd1 Hk Hi HL H12 H30 H31 Hmx;
      destruct (mi_row regs t1v a6v i mx Hd1 ltac:(lia) HL H12 H30 H31 Hmx)
        as (r1 & mx1 & S1 & R31 & Hmx1 & HL1 & R12 & R30 & AG1);
      pose proof HL1 as (I2 & I10 & I11 & I13 & I14 & I15 & I16 & I17 & I6 & I7 & I28 & I29 & I5 & I8).
    - (* [comment removed for export] *)
      destruct (c_eq (v_xor mx1 t1v) a6v) eqn:Hc.
      + eexists. exists mx1. split.
        * eapply msteps_trans; [exact S1|].
          sn F_24918 D_24918.                               (* [comment removed for export] *)
          stepb_tk F_2491c D_2491c ltac:(pin; exact Hc).    (* [comment removed for export] *)
          apply mst_refl.
        * repeat split; gres; pin; try reflexivity; try assumption.
          eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
      + eexists. exists mx1. split.
        * eapply msteps_trans; [exact S1|].
          sn F_24918 D_24918.                               (* [comment removed for export] *)
          stepb_ft F_2491c D_2491c ltac:(pin; exact Hc).    (* [comment removed for export] *)
          zvw F_24920 D_24920 (Z_to_bv 64 (i + 1)).         (* [comment removed for export] *)
          zvw F_24924 D_24924 (Z_to_bv 64 (data + 4 * wpl * (i + 1))).   (* [comment removed for export] *)
          stepb_ft F_24928 D_24928 ltac:(condZ).            (* [comment removed for export] *)
          sn F_2492c D_2492c.                               (* [comment removed for export] *)
          apply mst_refl.
        * repeat split; gres; pin; try reflexivity; try assumption.
          eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - destruct (c_eq (v_xor mx1 t1v) a6v) eqn:Hc.
      + (* [comment removed for export] *)
        eexists. exists mx1. split.
        * eapply msteps_trans; [exact S1|].
          sn F_24918 D_24918.                               (* [comment removed for export] *)
          stepb_tk F_2491c D_2491c ltac:(pin; exact Hc).    (* [comment removed for export] *)
          apply mst_refl.
        * repeat split; gres; pin; try reflexivity; try assumption.
          eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
      + assert (S2 : exists r2, msteps SEGS (mkst r1 (rl dOL_246d4 0x24918) MC rom) (mkst r2 (rl dOL_246d4 0x24830) MC rom)
                                /\ LInv r2 t1v a6v /\ getr r2 12 = Z_to_bv 64 (i + 1)
                                /\ getr r2 30 = Z_to_bv 64 (data + 4 * wpl * (i + 1)) /\ getr r2 31 = mx1
                                /\ regs_agree (fun r : reg => In r [9; 12; 30]%list) r1 r2).
        { eexists. split; [|split].
          - sn F_24918 D_24918.                             (* [comment removed for export] *)
            stepb_ft F_2491c D_2491c ltac:(pin; exact Hc).  (* [comment removed for export] *)
            zvw F_24920 D_24920 (Z_to_bv 64 (i + 1)).       (* [comment removed for export] *)
            zvw F_24924 D_24924 (Z_to_bv 64 (data + 4 * wpl * (i + 1))).   (* [comment removed for export] *)
            stepb_tk F_24928 D_24928 ltac:(condZ).          (* [comment removed for export] *)
            apply mst_refl.
          - unfold LInv. repeat split; gres; pin; reflexivity.
          - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
        destruct S2 as (r2 & S2 & HL2 & Q12 & Q30 & Q31 & AG2).
        destruct (IH r2 t1v a6v (i + 1)%Z mx1 Hd1 ltac:(lia) ltac:(lia) HL2 Q12 Q30 Q31 Hmx1)
          as (r3 & mx3 & S3 & T31 & Hmx3 & T2 & T5 & AG3).
        exists r3, mx3. split; [|split; [exact T31 | split; [exact Hmx3 | split; [exact T2 | split; [exact T5|]]]]].
        * eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2 | exact S3].
        * eapply regs_agree_trans; [regs_agree_weaken AG1|].
          eapply regs_agree_trans; [regs_agree_weaken AG2 | exact AG3].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition MF (Mx : word -> option byte) (mx : word) : word -> option byte :=
    wbytes Mx (Z_to_bv 64 pmax) (word_to_le_bytes 4 mx).

  (* [comment removed for export] *)
  Lemma mi_F : forall regs Mx (mx : word), mem_grows M Mx ->
    getr regs 5 = Z_to_bv 64 pmax -> getr regs 31 = mx ->
    exists regs',
      msteps SEGS (mkst regs (rl dOL_246d4 0x24970) Mx rom) (mkst regs' (rl dOL_246d4 0x24978) (MF Mx mx) rom)
      /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r : reg => In r [10]%list) regs regs'.
  Proof.
    intros regs Mx mx HG H5 H31. nodisj. clear RR.
    eexists. split.
    - sn F_24970 D_24970.                                   (* [comment removed for export] *)
      stepST F_24974 D_24974 (Z_to_bv 64 pmax) mx ltac:(apply sok_pmax; exact HG).   (* [comment removed for export] *)
      fold (MF Mx mx).
      apply mst_refl.
    - split; [gres; reflexivity | solve_regs_agree].
  Qed.

  (* [comment removed for export] *)
  Definition FrameSame (Mx : word -> option byte) : Prop :=
    forall x : word, (sp - 56 <= bv_unsigned x < sp)%Z -> Mx x = MA x.

  Lemma FS_wbytes : forall Mx (a : Z) bs, FrameSame Mx ->
    (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
    (a + Z.of_nat (length bs) <= sp - 56 \/ sp <= a)%Z ->
    FrameSame (wbytes Mx (Z_to_bv 64 a) bs).
  Proof.
    intros Mx a bs HF Ha Hnw Hapart x Hx. nodisj. clear RR.
    destruct bs as [|b0 bs']; [exact (HF x Hx)|].
    cbn [length] in *. rewrite wbytes_outside by (cbn [length]; rewrite u_Z2bv by lia; lia). exact (HF x Hx).
  Qed.

  Lemma FS_MA : FrameSame MA.
  Proof. intros x Hx. reflexivity. Qed.

  Lemma FS_MC : FrameSame MC.
  Proof.
    clear RR AP FP. unfold MC, MB.
    do 7 (apply FS_wbytes; [| lia | zlen; lia | zlen; lia]). apply FS_MA.
  Qed.

  Lemma FS_MF : forall Mx mx, FrameSame Mx -> FrameSame (MF Mx mx).
  Proof. intros Mx mx HF. clear RR AP FP. unfold MF. apply FS_wbytes; [exact HF | lia | zlen; lia | zlen; lia]. Qed.

  (* [comment removed for export] *)
  Lemma FS_rdn : forall Mx k (n : nat) bs,
    FrameSame Mx -> (Z.of_nat n <= k <= 56)%Z ->
    rdn SEGS MA (Z_to_bv 64 (sp - k)) n = Some bs -> rdn SEGS Mx (Z_to_bv 64 (sp - k)) n = Some bs.
  Proof.
    intros Mx k n bs HF Hk HM. nodisj. clear RR. rewrite <- HM. apply rdn_ext; rewrite u_Z2bv by lia; [lia|].
    intros x Hx. apply HF. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mi_E : forall regs Mx,
    FrameSame Mx -> getr regs 2 = Z_to_bv 64 (sp - 80) ->
    exists regs',
      msteps SEGS (mkst regs (rl dOL_246d4 0x24978) Mx rom) (mkst regs' ra Mx rom)
      /\ getr regs' 10 = getr regs 10 /\ getr regs' 1 = ra /\ getr regs' 2 = Z_to_bv 64 sp
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v
      /\ regs_agree (fun x : reg => In x [1; 2; 8; 9; 18; 19; 20; 21]%list) regs regs'.
  Proof.
    intros regs Mx HF H2. nodisj. clear RR.
    pose proof (u64_range ra). pose proof (u64_range s0v). pose proof (u64_range s1v). pose proof (u64_range s2v).
    pose proof (u64_range s3v). pose proof (u64_range s4v). pose proof (u64_range s5v).
    eexists. split.
    - stepLD F_24978 D_24978 (word_to_le_bytes 8 ra) ra
        ltac:(rdn_addr (sp - 8)%Z; apply (FS_rdn Mx 8 8); [exact HF | cbn; lia | unfold MA; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_2497c D_2497c (word_to_le_bytes 8 s0v) s0v
        ltac:(rdn_addr (sp - 16)%Z; apply (FS_rdn Mx 16 8); [exact HF | cbn; lia | unfold MA; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_24980 D_24980 (word_to_le_bytes 8 s1v) s1v
        ltac:(rdn_addr (sp - 24)%Z; apply (FS_rdn Mx 24 8); [exact HF | cbn; lia | unfold MA; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_24984 D_24984 (word_to_le_bytes 8 s2v) s2v
        ltac:(rdn_addr (sp - 32)%Z; apply (FS_rdn Mx 32 8); [exact HF | cbn; lia | unfold MA; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_24988 D_24988 (word_to_le_bytes 8 s3v) s3v
        ltac:(rdn_addr (sp - 40)%Z; apply (FS_rdn Mx 40 8); [exact HF | cbn; lia | unfold MA; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_2498c D_2498c (word_to_le_bytes 8 s4v) s4v
        ltac:(rdn_addr (sp - 48)%Z; apply (FS_rdn Mx 48 8); [exact HF | cbn; lia | unfold MA; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_24990 D_24990 (word_to_le_bytes 8 s5v) s5v
        ltac:(rdn_addr (sp - 56)%Z; apply (FS_rdn Mx 56 8); [exact HF | cbn; lia | unfold MA; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      zvw F_24994 D_24994 (Z_to_bv 64 sp).                  (* [comment removed for export] *)
      stepret F_24998 D_24998 ra ltac:(reflexivity).        (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mi_run248 : forall regs, (d <> 1)%Z ->
    getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 sp ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v ->
    getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 pmax ->
    exists regs' (mx : word),
      msteps SEGS (mkst regs (rl dOL_246d4 0x246d4) M rom) (mkst regs' ra (MF MC mx) rom)
      /\ (bv_unsigned mx <= maxval)%Z
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 sp
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v
      /\ regs_agree (fun x : reg => In x [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs Hd1 H1 H2 H8 H9 H18 H19 H20 H21 H10 H11.
    pose proof maxval_ge as Hmv.
    destruct (mi_A regs H1 H2 H8 H9 H18 H19 H20 H21 H10 H11) as (r1 & S1 & A2 & A9 & A18 & AG1).
    destruct (mi_B r1 A2 A9) as (r2 & S2 & B2 & B10 & B8 & B5 & B11 & AG2).
    pose proof (AG2 18 ltac:(notin_list)) as B18. rewrite A18 in B18.
    destruct (mi_D r2 Hd1 B2 B10 B8 B5 B11 B18) as (r3 & t1v & a6v & S3 & HL3 & C12 & C30 & C31 & AG3).
    destruct (mi_loop (Z.to_nat (h - 1)) r3 t1v a6v 0 (Z_to_bv 64 0) Hd1 ltac:(lia) ltac:(lia) HL3 C12 C30 C31
                ltac:(change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia))
      as (r4 & mx & S4 & D31 & Hmx & D2 & D5 & AG4).
    destruct (mi_F r4 MC mx MC_grows D5 D31) as (r5 & S5 & E10 & AG5).
    pose proof (AG5 2 ltac:(notin_list)) as E2. rewrite D2 in E2.
    destruct (mi_E r5 (MF MC mx) (FS_MF MC mx FS_MC) E2) as (r6 & S6 & G10 & G1 & G2 & G8 & G9 & G18 & G19 & G20 & G21 & AG6).
    rewrite E10 in G10.
    exists r6, mx. split.
    - eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|]. eapply msteps_trans; [exact S3|].
      eapply msteps_trans; [exact S4|]. eapply msteps_trans; [exact S5 | exact S6].
    - split; [exact Hmx|]. repeat split; try assumption.
      eapply regs_agree_trans; [regs_agree_weaken AG1|].
      eapply regs_agree_trans; [regs_agree_weaken AG2|].
      eapply regs_agree_trans; [regs_agree_weaken AG3|].
      eapply regs_agree_trans; [regs_agree_weaken AG4|].
      eapply regs_agree_trans; [regs_agree_weaken AG5|]. regs_agree_weaken AG6.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition MZ : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes MC
      (Z_to_bv 64 (sp - 88)) (word_to_le_bytes 8 (rl dOL_246d4 0x24764)))
      (Z_to_bv 64 (sp - 96)) (word_to_le_bytes 8 (Z_to_bv 64 wpl)))
      (Z_to_bv 64 (sp - 104)) (word_to_le_bytes 8 (Z_to_bv 64 pix)))
      (Z_to_bv 64 (sp - 112)) (word_to_le_bytes 8 (Z_to_bv 64 pmax)))
      (Z_to_bv 64 (sp - 120)) (word_to_le_bytes 8 s3v))
      (Z_to_bv 64 (sp - 128)) (word_to_le_bytes 8 s4v))
      (Z_to_bv 64 (sp - 136)) (word_to_le_bytes 8 s5v).
  Definition MZ1 : word -> option byte := wbytes MZ (Z_to_bv 64 (sp - 72)) (word_to_le_bytes 4 (Z_to_bv 64 1)).
  Definition MZ0 : word -> option byte := wbytes MZ1 (Z_to_bv 64 (sp - 72)) (word_to_le_bytes 4 (Z_to_bv 64 0)).

  Lemma MZ1_grows : mem_grows M MZ1. Proof. nodisj. unfold MZ1, MZ, MC, MB, MA. grows. Qed.
  Lemma MZ0_grows : mem_grows M MZ0. Proof. nodisj. unfold MZ0. eapply mem_grows_trans; [apply MZ1_grows | apply wbytes_grows]. Qed.

  Ltac sokz := apply sok_frame; [ unfold MZ0, MZ1, MZ, MC, MB, MA; grows | cbn; lia ].
  Ltac stz F D k v := stepST F D (Z_to_bv 64 (sp - k)) v ltac:(sokz).
  Ltac peelz := unfold MZ0, MZ1, MZ, MC, MB, MA;
    repeat (rewrite rdn_wbytes_out_Z by (zlen; rewrite ?length_Z_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)).
  Ltac ldpixz F D z C :=
    stepLD F D (Z_to_le_bytes 4 z) (Z_to_bv 64 z)
      ltac:(unfold v_addi; unorm; rewrite ?Z.add_0_r; peelz; exact C)
      ltac:(apply lez4; lia);
    rewrite (v_lw_small z) by lia.

  (* [comment removed for export] *)
  Lemma mi_Z1 : forall regs, (d = 1)%Z ->
    getr regs 2 = Z_to_bv 64 (sp - 80) -> getr regs 8 = Z_to_bv 64 wpl -> getr regs 5 = Z_to_bv 64 d ->
    getr regs 11 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 pix -> getr regs 18 = Z_to_bv 64 pmax ->
    getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    exists regs',
      msteps SEGS (mkst regs (rl dOL_246d4 0x24754) MC rom) (mkst regs' (rl dOL_2499c 0x24a0c) MZ1 rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 144) /\ getr regs' 19 = Z_to_bv 64 w /\ getr regs' 20 = Z_to_bv 64 d
      /\ getr regs' 8 = Z_to_bv 64 h /\ getr regs' 9 = Z_to_bv 64 wpl /\ getr regs' 10 = Z_to_bv 64 data
      /\ getr regs' 18 = Z_to_bv 64 pix /\ getr regs' 21 = Z_to_bv 64 (sp - 72)
      /\ regs_agree (fun r : reg => In r [1; 2; 8; 9; 10; 11; 18; 19; 20; 21]%list) regs regs'.
  Proof.
    intros regs Hd1 H2 H8 H5 H11 H9 H18 H19 H20 H21. clear RR.
    pose proof wpl_bounds as (Hwpl1 & _ & _).
    pose proof (u64_range s3v). pose proof (u64_range s4v). pose proof (u64_range s5v).
    eexists. split.
    - stepb_ft F_24754 D_24754 ltac:(condZ).                (* [comment removed for export] *)
      zvw F_24758 D_24758 (Z_to_bv 64 (sp - 72)).          (* [comment removed for export] *)
      zvw F_2475c D_2475c (Z_to_bv 64 pix).                 (* [comment removed for export] *)
      sn F_24760 D_24760.                                   (* [comment removed for export] *)
      (* [comment removed for export] *)
      zvw F_2499c D_2499c (Z_to_bv 64 (sp - 144)).          (* [comment removed for export] *)
      stz F_249a0 D_249a0 88%Z (rl dOL_246d4 0x24764).              (* [comment removed for export] *)
      stz F_249a4 D_249a4 96%Z (Z_to_bv 64 wpl).             (* [comment removed for export] *)
      stz F_249a8 D_249a8 104%Z (Z_to_bv 64 pix).            (* [comment removed for export] *)
      stz F_249ac D_249ac 112%Z (Z_to_bv 64 pmax).           (* [comment removed for export] *)
      stz F_249b0 D_249b0 120%Z s3v.                          (* [comment removed for export] *)
      stz F_249b4 D_249b4 128%Z s4v.                          (* [comment removed for export] *)
      stz F_249b8 D_249b8 136%Z s5v.                          (* [comment removed for export] *)
      fold MZ.
      stepb_ft F_249bc D_249bc ltac:(condZ).                (* [comment removed for export] *)
      zvw F_249c0 D_249c0 (Z_to_bv 64 pix).                 (* [comment removed for export] *)
      sn F_249c4 D_249c4.                                   (* [comment removed for export] *)
      stz F_249c8 D_249c8 72%Z (Z_to_bv 64 1).                (* [comment removed for export] *)
      fold MZ1.
      stepb_ft F_249cc D_249cc ltac:(condZ).                (* [comment removed for export] *)
      zvw F_249d0 D_249d0 (Z_to_bv 64 (sp - 72)).          (* [comment removed for export] *)
      zvw F_249d4 D_249d4 (Z_to_bv 64 pix).                 (* [comment removed for export] *)
      sn F_249d8 D_249d8.                                   (* [comment removed for export] *)
      stepb_ft F_23f14 D_23f14 ltac:(condZ).                (* [comment removed for export] *)
      stepLD F_23f18 D_23f18 (Z_to_le_bytes 4 w) (Z_to_bv 64 w)
        ltac:(unfold v_addi; unorm; rewrite ?Z.add_0_r; peelz; exact Cw)
        ltac:(apply lez4; lia).                             (* [comment removed for export] *)
      rewrite (v_lw_small w) by lia.
      stepretF F_23f1c D_23f1c F_249dc.
      zvw F_249dc D_249dc (Z_to_bv 64 w).                   (* [comment removed for export] *)
      zvw F_249e0 D_249e0 (Z_to_bv 64 pix).                 (* [comment removed for export] *)
      sn F_249e4 D_249e4.                                   (* [comment removed for export] *)
      stepb_ft F_23e94 D_23e94 ltac:(condZ).                (* [comment removed for export] *)
      ldpixz F_23e98 D_23e98 d Cd.                          (* [comment removed for export] *)
      stepretF F_23e9c D_23e9c F_249e8.
      zvw F_249e8 D_249e8 (Z_to_bv 64 d).                   (* [comment removed for export] *)
      zvw F_249ec D_249ec (Z_to_bv 64 pix).                 (* [comment removed for export] *)
      sn F_249f0 D_249f0.                                   (* [comment removed for export] *)
      stepb_ft F_23e54 D_23e54 ltac:(condZ).                (* [comment removed for export] *)
      ldpixz F_23e58 D_23e58 h Ch.                          (* [comment removed for export] *)
      stepretF F_23e5c D_23e5c F_249f4.
      zvw F_249f4 D_249f4 (Z_to_bv 64 h).                   (* [comment removed for export] *)
      zvw F_249f8 D_249f8 (Z_to_bv 64 pix).                 (* [comment removed for export] *)
      sn F_249fc D_249fc.                                   (* [comment removed for export] *)
      stepb_ft F_23be4 D_23be4 ltac:(condZ).                (* [comment removed for export] *)
      ldpixz F_23be8 D_23be8 wpl Cwpl.                      (* [comment removed for export] *)
      stepretF F_23bec D_23bec F_24a00.
      zvw F_24a00 D_24a00 (Z_to_bv 64 wpl).                 (* [comment removed for export] *)
      zvw F_24a04 D_24a04 (Z_to_bv 64 pix).                 (* [comment removed for export] *)
      sn F_24a08 D_24a08.                                   (* [comment removed for export] *)
      stepb_ft F_23ed4 D_23ed4 ltac:(condZ).                (* [comment removed for export] *)
      stepLD F_23ed8 D_23ed8 (Z_to_le_bytes 8 data) (Z_to_bv 64 data)
        ltac:(unfold v_addi; unorm; peelz; exact Cdata)
        ltac:(apply lez8; lia).                             (* [comment removed for export] *)
      stepretF F_23edc D_23edc F_24a0c.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  (* [comment removed for export] *)
  Lemma fw_facts : (d = 1)%Z ->
    (0 <= w / 32 <= wpl /\ 0 <= w mod 32 < 32 /\ w = 32 * (w / 32) + w mod 32
     /\ (w mod 32 <> 0 -> w / 32 < wpl) /\ (w < 32 <-> w / 32 = 0))%Z.
  Proof.
    intros Hd1. nodisj. clear RR. pose proof wpl_bounds as (Hwpl1 & Hwd & Hwd2). rewrite Hd1 in Hwd, Hwd2.
    pose proof (Z.div_mod w 32 ltac:(lia)). pose proof (Z.mod_pos_bound w 32 ltac:(lia)). nia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  (* [comment removed for export] *)
  Definition ZInv (regs : bvmap 5 word) : Prop :=
    getr regs 2 = Z_to_bv 64 (sp - 144) /\ getr regs 10 = Z_to_bv 64 data /\ getr regs 9 = Z_to_bv 64 wpl /\
    getr regs 12 = Z_to_bv 64 w /\ getr regs 13 = Z_to_bv 64 32 /\ getr regs 14 = Z_to_bv 64 (w mod 32) /\
    getr regs 15 = Z_to_bv 64 (w / 32) /\ getr regs 16 = Z_to_bv 64 (32 - w mod 32) /\ getr regs 8 = Z_to_bv 64 h /\
    getr regs 21 = Z_to_bv 64 (sp - 72) /\ getr regs 18 = Z_to_bv 64 pix.

  (* [comment removed for export] *)
  Lemma mi_Z2 : forall regs, (d = 1)%Z ->
    getr regs 2 = Z_to_bv 64 (sp - 144) -> getr regs 19 = Z_to_bv 64 w -> getr regs 20 = Z_to_bv 64 d ->
    getr regs 8 = Z_to_bv 64 h -> getr regs 9 = Z_to_bv 64 wpl -> getr regs 10 = Z_to_bv 64 data ->
    getr regs 18 = Z_to_bv 64 pix -> getr regs 21 = Z_to_bv 64 (sp - 72) ->
    exists regs',
      msteps SEGS (mkst regs (rl dOL_2499c 0x24a0c) MZ1 rom) (mkst regs' (rl dOL_2499c 0x24a34) MZ1 rom)
      /\ ZInv regs' /\ getr regs' 11 = Z_to_bv 64 0
      /\ regs_agree (fun r : reg => In r [11; 12; 13; 14; 15; 16]%list) regs regs'.
  Proof.
    intros regs Hd1 H2 H19 H20 H8 H9 H10 H18 H21. clear RR. nodisj.
    pose proof (fw_facts Hd1) as (Hfw & Hmod & Hdm & _ & _).
    eexists. split; [|split].
    - stepb_ft F_24a0c D_24a0c ltac:(condZ).                (* [comment removed for export] *)
      sn F_24a10 D_24a10.                                   (* [comment removed for export] *)
      sn F_24a14 D_24a14.                                   (* [comment removed for export] *)
      fixv (Z_to_bv 64 w) ltac:(rewrite Hd1; rewrite zbv_mulw_small by lia; f_equal; lia).
      sn F_24a18 D_24a18.                                   (* [comment removed for export] *)
      sn F_24a1c D_24a1c.                                   (* [comment removed for export] *)
      fixv (Z_to_bv 64 0) ltac:(rewrite zbv_sraiw_small by lia; f_equal; apply Z.div_small;
                                change (2 ^ 31)%Z with 2147483648%Z; lia).
      stepiv F_24a20 D_24a20 (Z_to_bv 64 (w mod 32))
        ltac:(gres; pin; imm_norm; rewrite andi_31; unorm; reflexivity).   (* [comment removed for export] *)
      sn F_24a24 D_24a24.                                   (* [comment removed for export] *)
      zvw F_24a28 D_24a28 (Z_to_bv 64 w).                   (* [comment removed for export] *)
      sn F_24a2c D_24a2c.                                   (* [comment removed for export] *)
      fixv (Z_to_bv 64 (w / 32)) ltac:(rewrite zbv_sraiw_small by lia; change (2 ^ 5)%Z with 32%Z; reflexivity).
      zvw F_24a30 D_24a30 (Z_to_bv 64 (32 - w mod 32)).    (* [comment removed for export] *)
      apply mst_refl.
    - unfold ZInv. repeat split; gres; pin; reflexivity.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma word_at_z : forall i q, (0 <= i < h)%Z -> (0 <= q < wpl)%Z ->
    exists bs, rdn SEGS MZ1 (Z_to_bv 64 (data + 4 * wpl * i + 4 * q)) 4 = Some bs /\ length bs = 4%nat.
  Proof.
    intros i q Hi Hq. nodisj. pose proof (row_in_raster i Hi) as Hrow.
    destruct RR as [rbs Hrbs].
    destruct (rdn_sub_grows SEGS M MZ1 data (Z.to_nat (4 * (wpl * h))) rbs (4 * wpl * i + 4 * q) 4
                ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) Hrbs MZ1_grows ltac:(lia) ltac:(rewrite Z2Nat.id by lia; cbn; lia))
      as (bs & Hbs & Lbs).
    exists bs. rewrite Z.add_assoc in Hbs. exact (conj Hbs Lbs).
  Qed.

  (* [comment removed for export] *)
  Lemma mi_ZL : forall k regs i q, (d = 1)%Z -> (0 <= i < h)%Z ->
    (Z.of_nat k = w / 32 - 1 - q)%Z -> (0 <= q)%Z ->
    ZInv regs -> getr regs 11 = Z_to_bv 64 i ->
    getr regs 17 = Z_to_bv 64 (data + 4 * wpl * i + 4 * q) -> getr regs 5 = Z_to_bv 64 (w / 32 - q) ->
    exists regs',
      regs_agree (fun r : reg => In r [5; 6; 17]%list) regs regs'
      /\ ( (msteps SEGS (mkst regs (rl dOL_2499c 0x24a48) MZ1 rom) (mkst regs' (rl dOL_2499c 0x24a5c) MZ1 rom)
            /\ getr regs' 17 = Z_to_bv 64 (data + 4 * wpl * i + 4 * (w / 32)))
           \/ msteps SEGS (mkst regs (rl dOL_2499c 0x24a48) MZ1 rom) (mkst regs' (rl dOL_2499c 0x24af0) MZ1 rom) ).
  Proof.
    nodisj. intros k. pose proof (fun Hd1 => fw_facts Hd1) as HF.
    induction k as [|k IH]; intros regs i q Hd1 Hi Hk Hq HZ H11 H17 H5;
      destruct (HF Hd1) as (Hfw & Hmod & Hdm & _ & _);
      pose proof (row_in_raster i Hi) as Hrow;
      destruct (word_at_z i q Hi ltac:(lia)) as (bs & Hbs & Lbs);
      destruct (c_eq (v_lw (Z_to_bv 64 (bytes_le_to_Z bs))) (Z_to_bv 64 0)) eqn:Hc.
    - (* [comment removed for export] *)
      eexists. split; [|left; split].
      2:{ stepLD F_24a48 D_24a48 bs (Z_to_bv 64 (bytes_le_to_Z bs))
            ltac:(rdn_addr (data + 4 * wpl * i + 4 * q)%Z; exact Hbs)
            ltac:(symmetry; apply u_lez4; exact Lbs).      (* [comment removed for export] *)
          stepb_ft F_24a4c D_24a4c ltac:(pin; exact Hc).    (* [comment removed for export] *)
          zvw F_24a50 D_24a50 (Z_to_bv 64 (w / 32 - q - 1)). (* [comment removed for export] *)
          zvw F_24a54 D_24a54 (Z_to_bv 64 (data + 4 * wpl * i + 4 * (w / 32))).   (* [comment removed for export] *)
          stepb_ft F_24a58 D_24a58 ltac:(condZ).            (* [comment removed for export] *)
          apply mst_refl. }
      + solve_regs_agree.
      + gres. reflexivity.
    - (* [comment removed for export] *)
      eexists. split; [|right].
      2:{ stepLD F_24a48 D_24a48 bs (Z_to_bv 64 (bytes_le_to_Z bs))
            ltac:(rdn_addr (data + 4 * wpl * i + 4 * q)%Z; exact Hbs)
            ltac:(symmetry; apply u_lez4; exact Lbs).      (* [comment removed for export] *)
          stepb_tk F_24a4c D_24a4c ltac:(pin; exact Hc).    (* [comment removed for export] *)
          apply mst_refl. }
      solve_regs_agree.
    - (* [comment removed for export] *)
      assert (S1 : exists r1, msteps SEGS (mkst regs (rl dOL_2499c 0x24a48) MZ1 rom) (mkst r1 (rl dOL_2499c 0x24a48) MZ1 rom)
                              /\ ZInv r1 /\ getr r1 11 = Z_to_bv 64 i
                              /\ getr r1 17 = Z_to_bv 64 (data + 4 * wpl * i + 4 * (q + 1))
                              /\ getr r1 5 = Z_to_bv 64 (w / 32 - (q + 1))
                              /\ regs_agree (fun r : reg => In r [5; 6; 17]%list) regs r1).
      { destruct HZ as (I2 & I10 & I9 & I12 & I13 & I14 & I15 & I16 & I8 & I21 & I18).
        eexists. split; [|split; [|split; [|split; [|split]]]].
        - stepLD F_24a48 D_24a48 bs (Z_to_bv 64 (bytes_le_to_Z bs))
            ltac:(rdn_addr (data + 4 * wpl * i + 4 * q)%Z; exact Hbs)
            ltac:(symmetry; apply u_lez4; exact Lbs).      (* [comment removed for export] *)
          stepb_ft F_24a4c D_24a4c ltac:(pin; exact Hc).    (* [comment removed for export] *)
          zvw F_24a50 D_24a50 (Z_to_bv 64 (w / 32 - (q + 1))).   (* [comment removed for export] *)
          zvw F_24a54 D_24a54 (Z_to_bv 64 (data + 4 * wpl * i + 4 * (q + 1))).   (* [comment removed for export] *)
          stepb_tk F_24a58 D_24a58 ltac:(condZ).            (* [comment removed for export] *)
          apply mst_refl.
        - unfold ZInv. repeat split; gres; pin; reflexivity.
        - gres. pin. reflexivity.
        - gres. reflexivity.
        - gres. reflexivity.
        - solve_regs_agree. }
      destruct S1 as (r1 & S1 & HZ1 & Q11 & Q17 & Q5 & AG1).
      destruct (IH r1 i (q + 1)%Z Hd1 Hi ltac:(lia) ltac:(lia) HZ1 Q11 Q17 Q5) as (r2 & AG2 & POST).
      exists r2. split; [eapply regs_agree_trans; [exact AG1 | exact AG2]|].
      destruct POST as [[S2 R17]|S2].
      + left. split; [|exact R17]. eapply msteps_trans; [exact S1 | exact S2].
      + right. eapply msteps_trans; [exact S1 | exact S2].
    - (* [comment removed for export] *)
      eexists. split; [|right].
      2:{ stepLD F_24a48 D_24a48 bs (Z_to_bv 64 (bytes_le_to_Z bs))
            ltac:(rdn_addr (data + 4 * wpl * i + 4 * q)%Z; exact Hbs)
            ltac:(symmetry; apply u_lez4; exact Lbs).      (* [comment removed for export] *)
          stepb_tk F_24a4c D_24a4c ltac:(pin; exact Hc).    (* [comment removed for export] *)
          apply mst_refl. }
      solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma mi_Zrow : forall regs i, (d = 1)%Z -> (0 <= i < h)%Z ->
    ZInv regs -> getr regs 11 = Z_to_bv 64 i ->
    exists regs',
      regs_agree (fun r : reg => In r [5; 6; 17]%list) regs regs'
      /\ ( msteps SEGS (mkst regs (rl dOL_2499c 0x24a34) MZ1 rom) (mkst regs' (rl dOL_2499c 0x24a6c) MZ1 rom)
           \/ msteps SEGS (mkst regs (rl dOL_2499c 0x24a34) MZ1 rom) (mkst regs' (rl dOL_2499c 0x24af0) MZ1 rom) ).
  Proof.
    intros regs i Hd1 Hi HZ H11. nodisj.
    pose proof (fw_facts Hd1) as (Hfw & Hmod & Hdm & Htail & Hsmall).
    pose proof (row_in_raster i Hi) as Hrow.
    pose proof HZ as (I2 & I10 & I9 & I12 & I13 & I14 & I15 & I16 & I8 & I21 & I18).
    (* [comment removed for export] *)
    assert (S1 : exists r1, msteps SEGS (mkst regs (rl dOL_2499c 0x24a34) MZ1 rom) (mkst r1 (rl dOL_2499c 0x24a40) MZ1 rom)
                            /\ ZInv r1 /\ getr r1 11 = Z_to_bv 64 i /\ getr r1 17 = Z_to_bv 64 (data + 4 * wpl * i + 4 * 0)
                            /\ regs_agree (fun r : reg => In r [17]%list) regs r1).
    { eexists. split; [|split; [|split; [|split]]].
      - zvw F_24a34 D_24a34 (Z_to_bv 64 (i * wpl)).         (* [comment removed for export] *)
        zvs F_24a38 D_24a38 (Z_to_bv 64 (4 * wpl * i)).     (* [comment removed for export] *)
        zvw F_24a3c D_24a3c (Z_to_bv 64 (data + 4 * wpl * i + 4 * 0)).   (* [comment removed for export] *)
        apply mst_refl.
      - unfold ZInv. repeat split; gres; pin; reflexivity.
      - gres. exact H11.
      - gres. reflexivity.
      - solve_regs_agree. }
    destruct S1 as (r1 & S1 & HZ1 & Q11 & Q17 & AG1).
    pose proof HZ1 as (J2 & J10 & J9 & J12 & J13 & J14 & J15 & J16 & J8 & J21 & J18).
    (* [comment removed for export] *)
    assert (S2 : exists r2, regs_agree (fun r : reg => In r [5; 6; 17]%list) r1 r2
              /\ ( (msteps SEGS (mkst r1 (rl dOL_2499c 0x24a40) MZ1 rom) (mkst r2 (rl dOL_2499c 0x24a5c) MZ1 rom)
                    /\ getr r2 17 = Z_to_bv 64 (data + 4 * wpl * i + 4 * (w / 32)))
                   \/ msteps SEGS (mkst r1 (rl dOL_2499c 0x24a40) MZ1 rom) (mkst r2 (rl dOL_2499c 0x24af0) MZ1 rom) )).
    { destruct (Z.lt_ge_cases w 32) as [Hw32|Hw32].
      - (* [comment removed for export] *)
        exists r1. split; [apply regs_agree_refl | left]. split.
        + stepb_tk F_24a40 D_24a40 ltac:(condZ).            (* [comment removed for export] *)
          apply mst_refl.
        + rewrite Q17. f_equal. f_equal. lia.
      - assert (S2a : exists r2, msteps SEGS (mkst r1 (rl dOL_2499c 0x24a40) MZ1 rom) (mkst r2 (rl dOL_2499c 0x24a48) MZ1 rom)
                                 /\ ZInv r2 /\ getr r2 11 = Z_to_bv 64 i /\ getr r2 17 = Z_to_bv 64 (data + 4 * wpl * i + 4 * 0)
                                 /\ getr r2 5 = Z_to_bv 64 (w / 32 - 0)
                                 /\ regs_agree (fun r : reg => In r [5]%list) r1 r2).
        { eexists. split; [|split; [|split; [|split; [|split]]]].
          - stepb_ft F_24a40 D_24a40 ltac:(condZ).          (* [comment removed for export] *)
            zvw F_24a44 D_24a44 (Z_to_bv 64 (w / 32 - 0)).  (* [comment removed for export] *)
            apply mst_refl.
          - unfold ZInv. repeat split; gres; pin; reflexivity.
          - gres. exact Q11.
          - gres. exact Q17.
          - gres. reflexivity.
          - solve_regs_agree. }
        destruct S2a as (r2 & S2a & HZ2 & T11 & T17 & T5 & AG2).
        destruct (mi_ZL (Z.to_nat (w / 32 - 1)) r2 i 0 Hd1 Hi ltac:(lia) ltac:(lia) HZ2 T11 T17 T5) as (r3 & AG3 & POST).
        exists r3. split; [eapply regs_agree_trans; [regs_agree_weaken AG2 | exact AG3]|].
        destruct POST as [[S3 R17]|S3].
        + left. split; [|exact R17]. eapply msteps_trans; [exact S2a | exact S3].
        + right. eapply msteps_trans; [exact S2a | exact S3]. }
    destruct S2 as (r2 & AG2 & POST).
    assert (HZ2 : ZInv r2) by (unfold ZInv; rewrite !AG2 by notin_list; exact HZ1).
    pose proof HZ2 as (K2 & K10 & K9 & K12 & K13 & K14 & K15 & K16 & K8 & K21 & K18).
    destruct POST as [[S2 R17]|S2].
    2:{ (* [comment removed for export] *)
        exists r2. split; [eapply regs_agree_trans; [regs_agree_weaken AG1 | exact AG2] | right].
        eapply msteps_trans; [exact S1 | exact S2]. }
    (* [comment removed for export] *)
    destruct (Z.eq_dec (w mod 32) 0) as [Hr0|Hr0].
    - (* [comment removed for export] *)
      exists r2. split; [eapply regs_agree_trans; [regs_agree_weaken AG1 | exact AG2] | left].
      eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|].
      stepb_tk F_24a5c D_24a5c ltac:(condE).                (* [comment removed for export] *)
      apply mst_refl.
    - pose proof (Htail Hr0) as Hfw2.
      destruct (word_at_z i (w / 32) Hi ltac:(lia)) as (bs & Hbs & Lbs).
      (* [comment removed for export] *)
      assert (S3 : exists r3 (v : word), msteps SEGS (mkst r2 (rl dOL_2499c 0x24a5c) MZ1 rom) (mkst r3 (rl dOL_2499c 0x24a68) MZ1 rom)
                                  /\ getr r3 17 = v /\ regs_agree (fun r : reg => In r [17]%list) r2 r3).
      { eexists. eexists. split; [|split].
        - stepb_ft F_24a5c D_24a5c ltac:(condE).            (* [comment removed for export] *)
          stepLD F_24a60 D_24a60 bs (Z_to_bv 64 (bytes_le_to_Z bs))
            ltac:(rdn_addr (data + 4 * wpl * i + 4 * (w / 32))%Z; exact Hbs)
            ltac:(symmetry; apply u_lez4; exact Lbs).      (* [comment removed for export] *)
          sn F_24a64 D_24a64.                               (* [comment removed for export] *)
          apply mst_refl.
        - gres. reflexivity.
        - solve_regs_agree. }
      destruct S3 as (r3 & v & S3 & R17v & AG3).
      destruct (c_eq v (Z_to_bv 64 0)) eqn:Hc.
      + (* [comment removed for export] *)
        exists r3. split; [eapply regs_agree_trans; [regs_agree_weaken AG1 | eapply regs_agree_trans; [exact AG2 | regs_agree_weaken AG3]] | left].
        eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|]. eapply msteps_trans; [exact S3|].
        stepb_ft F_24a68 D_24a68 ltac:(pin; exact Hc).      (* [comment removed for export] *)
        apply mst_refl.
      + exists r3. split; [eapply regs_agree_trans; [regs_agree_weaken AG1 | eapply regs_agree_trans; [exact AG2 | regs_agree_weaken AG3]] | right].
        eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|]. eapply msteps_trans; [exact S3|].
        stepb_tk F_24a68 D_24a68 ltac:(pin; exact Hc).      (* [comment removed for export] *)
        apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma mi_Zloop : forall k regs i, (d = 1)%Z -> (Z.of_nat k = h - 1 - i)%Z -> (0 <= i)%Z ->
    ZInv regs -> getr regs 11 = Z_to_bv 64 i ->
    exists regs',
      regs_agree (fun r : reg => In r [5; 6; 11; 17]%list) regs regs'
      /\ ( msteps SEGS (mkst regs (rl dOL_2499c 0x24a34) MZ1 rom) (mkst regs' (rl dOL_2499c 0x24a74) MZ1 rom)
           \/ msteps SEGS (mkst regs (rl dOL_2499c 0x24a34) MZ1 rom) (mkst regs' (rl dOL_2499c 0x24af0) MZ1 rom) ).
  Proof.
    nodisj.
    induction k as [|k IH]; intros regs i Hd1 Hk Hi HZ H11;
      destruct (mi_Zrow regs i Hd1 ltac:(lia) HZ H11) as (r1 & AG1 & POST);
      (assert (HZ1 : ZInv r1) by (unfold ZInv; rewrite !AG1 by notin_list; exact HZ));
      pose proof HZ1 as (J2 & J10 & J9 & J12 & J13 & J14 & J15 & J16 & J8 & J21 & J18);
      (pose proof (AG1 11 ltac:(notin_list)) as Q11); rewrite H11 in Q11;
      (destruct POST as [S1|S1];
       [| exists r1; split; [regs_agree_weaken AG1 | right; exact S1]]).
    - (* [comment removed for export] *)
      eexists. split; [|left].
      2:{ eapply msteps_trans; [exact S1|].
          zvw F_24a6c D_24a6c (Z_to_bv 64 (i + 1)).         (* [comment removed for export] *)
          stepb_ft F_24a70 D_24a70 ltac:(condZ).            (* [comment removed for export] *)
          apply mst_refl. }
      eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - assert (S2 : exists r2, msteps SEGS (mkst r1 (rl dOL_2499c 0x24a6c) MZ1 rom) (mkst r2 (rl dOL_2499c 0x24a34) MZ1 rom)
                              /\ ZInv r2 /\ getr r2 11 = Z_to_bv 64 (i + 1)
                              /\ regs_agree (fun r : reg => In r [11]%list) r1 r2).
      { eexists. split; [|split; [|split]].
        - zvw F_24a6c D_24a6c (Z_to_bv 64 (i + 1)).         (* [comment removed for export] *)
          stepb_tk F_24a70 D_24a70 ltac:(condZ).            (* [comment removed for export] *)
          apply mst_refl.
        - unfold ZInv. repeat split; gres; pin; reflexivity.
        - gres. reflexivity.
        - solve_regs_agree. }
      destruct S2 as (r2 & S2 & HZ2 & Q11' & AG2).
      destruct (IH r2 (i + 1)%Z Hd1 ltac:(lia) ltac:(lia) HZ2 Q11') as (r3 & AG3 & POST).
      exists r3. split.
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2 | exact AG3].
      + destruct POST as [S3|S3].
        * left. eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2 | exact S3].
        * right. eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2 | exact S3].
  Qed.

  (* [comment removed for export] *)
  Definition ZFS (Mx : word -> option byte) : Prop :=
    forall x : word, (sp - 136 <= bv_unsigned x < sp - 80)%Z -> Mx x = MZ x.

  Lemma ZFS_MZ1 : ZFS MZ1.
  Proof.
    intros x Hx. nodisj. clear RR. unfold MZ1.
    rewrite wbytes_outside by (zlen; rewrite u_Z2bv by lia; lia). reflexivity.
  Qed.
  Lemma ZFS_MZ0 : ZFS MZ0.
  Proof.
    intros x Hx. nodisj. clear RR. unfold MZ0, MZ1.
    rewrite !wbytes_outside by (zlen; rewrite u_Z2bv by lia; lia). reflexivity.
  Qed.

  Lemma ZFS_rdn : forall Mx k (n : nat) bs,
    ZFS Mx -> (80 + Z.of_nat n <= k <= 136)%Z ->
    rdn SEGS MZ (Z_to_bv 64 (sp - k)) n = Some bs -> rdn SEGS Mx (Z_to_bv 64 (sp - k)) n = Some bs.
  Proof.
    intros Mx k n bs HF Hk HM. nodisj. clear RR. rewrite <- HM. apply rdn_ext; rewrite u_Z2bv by lia; [lia|].
    intros x Hx. apply HF. lia.
  Qed.

  Lemma FS_MZ1 : FrameSame MZ1.
  Proof.
    clear RR AP FP. unfold MZ1, MZ.
    (* [comment removed for export] *)
    do 8 (apply FS_wbytes; [| lia | zlen; lia | zlen; lia]). apply FS_MC.
  Qed.
  Lemma FS_MZ0 : FrameSame MZ0.
  Proof. clear RR AP FP. unfold MZ0. apply FS_wbytes; [apply FS_MZ1 | lia | zlen; lia | zlen; lia]. Qed.

  (* [comment removed for export] *)
  Lemma mi_ZE : forall regs Mx,
    ZFS Mx -> getr regs 2 = Z_to_bv 64 (sp - 144) ->
    exists regs',
      msteps SEGS (mkst regs (rl dOL_2499c 0x24b00) Mx rom) (mkst regs' (rl dOL_246d4 0x24764) Mx rom)
      /\ getr regs' 10 = getr regs 10 /\ getr regs' 2 = Z_to_bv 64 (sp - 80)
      /\ getr regs' 8 = Z_to_bv 64 wpl /\ getr regs' 9 = Z_to_bv 64 pix /\ getr regs' 18 = Z_to_bv 64 pmax
      /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v
      /\ regs_agree (fun x : reg => In x [1; 2; 8; 9; 18; 19; 20; 21]%list) regs regs'.
  Proof.
    intros regs Mx HF H2. nodisj. clear RR.
    pose proof (u64_range s3v). pose proof (u64_range s4v). pose proof (u64_range s5v).
    eexists. split.
    - stepLD F_24b00 D_24b00 (word_to_le_bytes 8 (rl dOL_246d4 0x24764)) (rl dOL_246d4 0x24764)
        ltac:(rdn_addr (sp - 88)%Z; apply (ZFS_rdn Mx 88 8); [exact HF | cbn; lia | unfold MZ; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_24b04 D_24b04 (word_to_le_bytes 8 (Z_to_bv 64 wpl)) (Z_to_bv 64 wpl)
        ltac:(rdn_addr (sp - 96)%Z; apply (ZFS_rdn Mx 96 8); [exact HF | cbn; lia | unfold MZ; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_24b08 D_24b08 (word_to_le_bytes 8 (Z_to_bv 64 pix)) (Z_to_bv 64 pix)
        ltac:(rdn_addr (sp - 104)%Z; apply (ZFS_rdn Mx 104 8); [exact HF | cbn; lia | unfold MZ; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_24b0c D_24b0c (word_to_le_bytes 8 (Z_to_bv 64 pmax)) (Z_to_bv 64 pmax)
        ltac:(rdn_addr (sp - 112)%Z; apply (ZFS_rdn Mx 112 8); [exact HF | cbn; lia | unfold MZ; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_24b10 D_24b10 (word_to_le_bytes 8 s3v) s3v
        ltac:(rdn_addr (sp - 120)%Z; apply (ZFS_rdn Mx 120 8); [exact HF | cbn; lia | unfold MZ; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_24b14 D_24b14 (word_to_le_bytes 8 s4v) s4v
        ltac:(rdn_addr (sp - 128)%Z; apply (ZFS_rdn Mx 128 8); [exact HF | cbn; lia | unfold MZ; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_24b18 D_24b18 (word_to_le_bytes 8 s5v) s5v
        ltac:(rdn_addr (sp - 136)%Z; apply (ZFS_rdn Mx 136 8); [exact HF | cbn; lia | unfold MZ; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      zvw F_24b1c D_24b1c (Z_to_bv 64 (sp - 80)).           (* [comment removed for export] *)
      stepretF F_24b20 D_24b20 F_24764. (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma mi_ZX1 : forall regs, getr regs 2 = Z_to_bv 64 (sp - 144) ->
    exists regs',
      msteps SEGS (mkst regs (rl dOL_2499c 0x24a74) MZ1 rom) (mkst regs' (rl dOL_246d4 0x24764) MZ1 rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 80) /\ getr regs' 18 = Z_to_bv 64 pmax
      /\ getr regs' 8 = Z_to_bv 64 wpl /\ getr regs' 9 = Z_to_bv 64 pix
      /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v
      /\ regs_agree (fun x : reg => In x [1; 2; 8; 9; 10; 18; 19; 20; 21]%list) regs regs'.
  Proof.
    intros regs H2. nodisj. clear RR.
    destruct (mi_ZE (regupd regs 10 (Z_to_bv 64 0)) MZ1 ZFS_MZ1 ltac:(gres; exact H2))
      as (r1 & S1 & E10 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & AG1).
    exists r1. split.
    - sn F_24a74 D_24a74.                                   (* [comment removed for export] *)
      sn F_24a78 D_24a78.                                   (* [comment removed for export] *)
      exact S1.
    - repeat split; try assumption.
      eapply regs_agree_trans; [|regs_agree_weaken AG1]. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma mi_ZX0 : forall regs, getr regs 2 = Z_to_bv 64 (sp - 144) -> getr regs 21 = Z_to_bv 64 (sp - 72) ->
    exists regs',
      msteps SEGS (mkst regs (rl dOL_2499c 0x24af0) MZ1 rom) (mkst regs' (rl dOL_246d4 0x24764) MZ0 rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 80) /\ getr regs' 18 = Z_to_bv 64 pmax
      /\ getr regs' 8 = Z_to_bv 64 wpl /\ getr regs' 9 = Z_to_bv 64 pix
      /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v
      /\ regs_agree (fun x : reg => In x [1; 2; 8; 9; 10; 18; 19; 20; 21]%list) regs regs'.
  Proof.
    intros regs H2 H21. nodisj. clear RR.
    destruct (mi_ZE (regupd regs 10 (Z_to_bv 64 0)) MZ0 ZFS_MZ0 ltac:(gres; exact H2))
      as (r1 & S1 & E10 & E2 & E8 & E9 & E18 & E19 & E20 & E21 & AG1).
    exists r1. split.
    - sn F_24af0 D_24af0.                                   (* [comment removed for export] *)
      stz F_24af4 D_24af4 72%Z (Z_to_bv 64 0).                (* [comment removed for export] *)
      fold MZ0.
      sn F_24af8 D_24af8.                                   (* [comment removed for export] *)
      exact S1.
    - repeat split; try assumption.
      eapply regs_agree_trans; [|regs_agree_weaken AG1]. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma mi_C : forall regs Mx (e : Z), (e = 0 \/ e = 1)%Z -> mem_grows M Mx ->
    rdn SEGS Mx (Z_to_bv 64 (sp - 72)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 e)) ->
    getr regs 2 = Z_to_bv 64 (sp - 80) -> getr regs 18 = Z_to_bv 64 pmax ->
    exists regs',
      msteps SEGS (mkst regs (rl dOL_246d4 0x24764) Mx rom) (mkst regs' (rl dOL_246d4 0x24978) (MF Mx (Z_to_bv 64 (1 - e))) rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 (sp - 80)
      /\ regs_agree (fun x : reg => In x [10; 11]%list) regs regs'.
  Proof.
    intros regs Mx e He HG Hrd H2 H18. nodisj. clear RR.
    eexists. split.
    - sn F_24764 D_24764.                                   (* [comment removed for export] *)
      stepLD F_24768 D_24768 (word_to_le_bytes 4 (Z_to_bv 64 e)) (Z_to_bv 64 e)
        ltac:(rdn_addr (sp - 72)%Z; exact Hrd)
        ltac:(apply bytes_le_to_Z_4; unorm; lia).          (* [comment removed for export] *)
      rewrite (v_lw_small e) by lia.
      stepiv F_2476c D_2476c (Z_to_bv 64 (1 - e))
        ltac:(gres; pin; imm_norm; rewrite zbv_seqz by lia; destruct He as [-> | ->]; reflexivity).   (* [comment removed for export] *)
      stepST F_24770 D_24770 (Z_to_bv 64 pmax) (Z_to_bv 64 (1 - e)) ltac:(apply sok_pmax; exact HG).   (* [comment removed for export] *)
      fold (MF Mx (Z_to_bv 64 (1 - e))).
      sn F_24774 D_24774.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mi_run1 : forall regs, (d = 1)%Z ->
    getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 sp ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v ->
    getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 pmax ->
    exists regs' Mx (e : Z),
      msteps SEGS (mkst regs (rl dOL_246d4 0x246d4) M rom) (mkst regs' ra (MF Mx (Z_to_bv 64 (1 - e))) rom)
      /\ (Mx = MZ1 \/ Mx = MZ0) /\ (e = 0 \/ e = 1)%Z
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 sp
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v
      /\ regs_agree (fun x : reg => In x [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs Hd1 H1 H2 H8 H9 H18 H19 H20 H21 H10 H11.
    destruct (mi_A regs H1 H2 H8 H9 H18 H19 H20 H21 H10 H11) as (r1 & S1 & A2 & A9 & A18 & AG1).
    pose proof (AG1 19 ltac:(notin_list)) as A19. rewrite H19 in A19.
    pose proof (AG1 20 ltac:(notin_list)) as A20. rewrite H20 in A20.
    pose proof (AG1 21 ltac:(notin_list)) as A21. rewrite H21 in A21.
    destruct (mi_B r1 A2 A9) as (r2 & S2 & B2 & B10 & B8 & B5 & B11 & AG2).
    pose proof (AG2 9 ltac:(notin_list)) as B9. rewrite A9 in B9.
    pose proof (AG2 18 ltac:(notin_list)) as B18. rewrite A18 in B18.
    pose proof (AG2 19 ltac:(notin_list)) as B19. rewrite A19 in B19.
    pose proof (AG2 20 ltac:(notin_list)) as B20. rewrite A20 in B20.
    pose proof (AG2 21 ltac:(notin_list)) as B21. rewrite A21 in B21.
    destruct (mi_Z1 r2 Hd1 B2 B8 B5 B11 B9 B18 B19 B20 B21) as (r3 & S3 & C2 & C19 & C20 & C8 & C9 & C10 & C18 & C21 & AG3).
    destruct (mi_Z2 r3 Hd1 C2 C19 C20 C8 C9 C10 C18 C21) as (r4 & S4 & HZ4 & D11 & AG4).
    destruct (mi_Zloop (Z.to_nat (h - 1)) r4 0 Hd1 ltac:(lia) ltac:(lia) HZ4 D11) as (r5 & AG5 & POST).
    assert (HZ5 : ZInv r5) by (unfold ZInv; rewrite !AG5 by notin_list; exact HZ4).
    destruct HZ5 as (E2 & _ & _ & _ & _ & _ & _ & _ & _ & E21 & _).
    destruct POST as [S5|S5].
    - (* [comment removed for export] *)
      destruct (mi_ZX1 r5 E2) as (r6 & S6 & F2 & F18 & F8 & F9 & F19 & F20 & F21 & AG6).
      assert (Hrd : rdn SEGS MZ1 (Z_to_bv 64 (sp - 72)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1))).
      { clear AP FP S1 S2 S3 S4 S5 S6. unfold MZ1. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
      destruct (mi_C r6 MZ1 1 ltac:(lia) MZ1_grows Hrd F2 F18) as (r7 & S7 & G10 & G2 & AG7).
      destruct (mi_E r7 (MF MZ1 (Z_to_bv 64 (1 - 1))) (FS_MF _ _ FS_MZ1) G2)
        as (r8 & S8 & K10 & K1 & K2 & K8 & K9 & K18 & K19 & K20 & K21 & AG8).
      rewrite G10 in K10.
      exists r8, MZ1, 1%Z. split.
      + eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|]. eapply msteps_trans; [exact S3|].
        eapply msteps_trans; [exact S4|]. eapply msteps_trans; [exact S5|]. eapply msteps_trans; [exact S6|].
        eapply msteps_trans; [exact S7 | exact S8].
      + split; [left; reflexivity|]. split; [lia|]. repeat split; try assumption.
        eapply regs_agree_trans; [regs_agree_weaken AG1|].
        eapply regs_agree_trans; [regs_agree_weaken AG2|].
        eapply regs_agree_trans; [regs_agree_weaken AG3|].
        eapply regs_agree_trans; [regs_agree_weaken AG4|].
        eapply regs_agree_trans; [regs_agree_weaken AG5|].
        eapply regs_agree_trans; [regs_agree_weaken AG6|].
        eapply regs_agree_trans; [regs_agree_weaken AG7|]. regs_agree_weaken AG8.
    - (* [comment removed for export] *)
      destruct (mi_ZX0 r5 E2 E21) as (r6 & S6 & F2 & F18 & F8 & F9 & F19 & F20 & F21 & AG6).
      assert (Hrd : rdn SEGS MZ0 (Z_to_bv 64 (sp - 72)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))).
      { clear AP FP S1 S2 S3 S4 S5 S6. unfold MZ0. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
      destruct (mi_C r6 MZ0 0 ltac:(lia) MZ0_grows Hrd F2 F18) as (r7 & S7 & G10 & G2 & AG7).
      destruct (mi_E r7 (MF MZ0 (Z_to_bv 64 (1 - 0))) (FS_MF _ _ FS_MZ0) G2)
        as (r8 & S8 & K10 & K1 & K2 & K8 & K9 & K18 & K19 & K20 & K21 & AG8).
      rewrite G10 in K10.
      exists r8, MZ0, 0%Z. split.
      + eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|]. eapply msteps_trans; [exact S3|].
        eapply msteps_trans; [exact S4|]. eapply msteps_trans; [exact S5|]. eapply msteps_trans; [exact S6|].
        eapply msteps_trans; [exact S7 | exact S8].
      + split; [right; reflexivity|]. split; [lia|]. repeat split; try assumption.
        eapply regs_agree_trans; [regs_agree_weaken AG1|].
        eapply regs_agree_trans; [regs_agree_weaken AG2|].
        eapply regs_agree_trans; [regs_agree_weaken AG3|].
        eapply regs_agree_trans; [regs_agree_weaken AG4|].
        eapply regs_agree_trans; [regs_agree_weaken AG5|].
        eapply regs_agree_trans; [regs_agree_weaken AG6|].
        eapply regs_agree_trans; [regs_agree_weaken AG7|]. regs_agree_weaken AG8.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma MC_outside : forall x : word,
    (bv_unsigned x < sp - 144 \/ sp <= bv_unsigned x)%Z -> (bv_unsigned x < pmax \/ pmax + 4 <= bv_unsigned x)%Z ->
    MC x = M x.
  Proof.
    intros x Hx Hp. clear RR AP FP FPM. unfold MC, MB, MA.
    rewrite !wbytes_outside by (zlen; rewrite ?u_Z2bv by lia; lia). reflexivity.
  Qed.
  Lemma MZ1_outside : forall x : word,
    (bv_unsigned x < sp - 144 \/ sp <= bv_unsigned x)%Z -> (bv_unsigned x < pmax \/ pmax + 4 <= bv_unsigned x)%Z ->
    MZ1 x = M x.
  Proof.
    intros x Hx Hp. pose proof (MC_outside x Hx Hp) as HC. clear RR AP FP FPM. unfold MZ1, MZ.
    rewrite !wbytes_outside by (zlen; rewrite ?u_Z2bv by lia; lia). exact HC.
  Qed.
  Lemma MZ0_outside : forall x : word,
    (bv_unsigned x < sp - 144 \/ sp <= bv_unsigned x)%Z -> (bv_unsigned x < pmax \/ pmax + 4 <= bv_unsigned x)%Z ->
    MZ0 x = M x.
  Proof.
    intros x Hx Hp. pose proof (MZ1_outside x Hx Hp) as HC. clear RR AP FP FPM. unfold MZ0.
    rewrite wbytes_outside by (zlen; rewrite ?u_Z2bv by lia; lia). exact HC.
  Qed.
  Lemma MF_outside : forall Mx mx (x : word),
    Mx x = M x -> (bv_unsigned x < pmax \/ pmax + 4 <= bv_unsigned x)%Z -> MF Mx mx x = M x.
  Proof.
    intros Mx mx x HMx Hp. clear RR AP FP FPM. unfold MF.
    rewrite wbytes_outside by (zlen; rewrite ?u_Z2bv by lia; lia). exact HMx.
  Qed.
  Lemma MF_cell : forall Mx mx,
    rdn SEGS (MF Mx mx) (Z_to_bv 64 pmax) 4 = Some (Z_to_le_bytes 4 (bv_unsigned mx)).
  Proof.
    intros Mx mx. clear RR AP FP FPM. unfold MF. rewrite rdn_wbytes_hit4 by (rewrite u_Z2bv by lia; lia). reflexivity.
  Qed.
  Lemma MF_grows : forall Mx mx, mem_grows M Mx -> mem_grows M (MF Mx mx).
  Proof. intros Mx mx HG. unfold MF. eapply mem_grows_trans; [exact HG | apply wbytes_grows]. Qed.

  (* [comment removed for export] *)
  Definition PostMem (M' : word -> option byte) (mi : Z) : Prop :=
    (forall x : word, (bv_unsigned x < sp - 144 \/ sp <= bv_unsigned x)%Z ->
                      (bv_unsigned x < pmax \/ pmax + 4 <= bv_unsigned x)%Z -> M' x = M x)
    /\ mem_grows M M'
    /\ rdn SEGS M' (Z_to_bv 64 pmax) 4 = Some (Z_to_le_bytes 4 mi)
    /\ (0 <= mi <= 255)%Z.

  (* [comment removed for export] *)
  Theorem maxindex_run : forall regs,
    getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 sp ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v ->
    getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 pmax ->
    exists regs' M' (mi : Z),
      msteps SEGS (mkst regs (rl dOL_246d4 0x246d4) M rom) (mkst regs' ra M' rom)
      /\ PostMem M' mi
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 sp
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v
      /\ regs_agree (fun x : reg => In x [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs H1 H2 H8 H9 H18 H19 H20 H21 H10 H11.
    destruct (Z.eq_dec d 1) as [Hd1|Hd1].
    - destruct (mi_run1 regs Hd1 H1 H2 H8 H9 H18 H19 H20 H21 H10 H11)
        as (r' & Mx & e & RUN & HMx & He & Q10 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & AG).
      exists r', (MF Mx (Z_to_bv 64 (1 - e))), (1 - e)%Z. split; [exact RUN|]. split; [|repeat split; assumption].
      split; [|split; [|split]].
      + intros x Hx Hp. apply MF_outside; [|exact Hp].
        destruct HMx as [-> | ->]; [apply MZ1_outside | apply MZ0_outside]; assumption.
      + apply MF_grows. destruct HMx as [-> | ->]; [apply MZ1_grows | apply MZ0_grows].
      + rewrite MF_cell. rewrite u_Z2bv by lia. reflexivity.
      + lia.
    - destruct (mi_run248 regs Hd1 H1 H2 H8 H9 H18 H19 H20 H21 H10 H11)
        as (r' & mx & RUN & Hmx & Q10 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & AG).
      pose proof maxval_ge. pose proof (u64_range mx).
      exists r', (MF MC mx), (bv_unsigned mx). split; [exact RUN|]. split; [|repeat split; assumption].
      split; [|split; [|split]].
      + intros x Hx Hp. apply MF_outside; [|exact Hp]. apply MC_outside; assumption.
      + apply MF_grows. apply MC_grows.
      + apply MF_cell.
      + lia.
  Qed.

End MI.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Theorem maxindex_contract : SSP.sum_contract SEGS (SSP.spec_maxindex (0x246d4 + dOL_246d4) 144).
Proof.
  apply SSP.sum_contract_in7_out1; [reflexivity | reflexivity |].
  intros pix pmax w h d wpl data R M rom PRE.
  unfold SSP.spec_maxindex in PRE. SSP.spec_unfold_in PRE.
  destruct PRE as (ITEMS & EFF & FR & RET).
  destruct ITEMS as ((H10 & _) & Hpix & _ & (H11 & _) & Hpmax & (_ & _ & (Rw & Cw)) & Hw & (_ & _ & (Rh & Ch)) & Hh
                     & (_ & _ & (Rd & Cd)) & Hd & (_ & _ & (Rwpl & Cwpl)) & Hwpl & (_ & F56 & (Rdata & Cdata)) & Hdata & (_ & Hdal)
                     & ((FRS & RR) & HRS & (Fpm & SOKp) & (_ & Hpal) & AP & (_ & SP16) & _)).
  destruct EFF as (_ & (Fsp & _ & Fsp2) & SOKf & _ & Fpm2 & _).
  destruct FR as ((F0 & F4 & F8 & F16 & F56' & FRR & FPM & _) & _).
  cbn [Z.of_nat Z.add] in F0, F4, F8, F16, F56', FPM.
  change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z in Rw, Rh, Rd, Rwpl.
  unfold SSP.flatZ in F56, FRS, Fpm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in F56.
  set (sp := bv_unsigned (getr R 2)) in *.
  assert (FP : (pix + 64 <= sp - 144 \/ sp <= pix)%Z) by (clear FRR FPM AP; lia).
  clear F0 F4 F8 F16 F56' FRR.
  assert (H2 : getr R 2 = Z_to_bv 64 sp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (u64_range (getr R 2)) as Hsp. fold sp in Hsp.
  rewrite Z.add_0_r in Cw.
  assert (Hd' : (d = 1 \/ d = 2 \/ d = 4 \/ d = 8)%Z) by (generalize Hd; clear; cbn; intuition lia).
  assert (Hdata4 : (4 <= data /\ data < 2 ^ 64)%Z) by (clear FPM AP FP; lia).
  unfold SSP.spec_maxindex. SSP.spec_unfold.
  destruct (maxindex_run M rom pix pmax w h d wpl data sp (getr R 1) (getr R 8) (getr R 9) (getr R 18)
              (getr R 19) (getr R 20) (getr R 21)
              ltac:(clear FPM AP FP; lia) ltac:(clear FPM AP FP; lia) Rw Rh Rd Rwpl Hw Hh Hd' Hwpl Hdata4 Hdal
              ltac:(clear FPM AP FP; lia) RET Cw Ch Cd Cwpl Cdata ltac:(clear FPM AP FP; lia) RR SOKp AP FPM SOKf FP
              R eq_refl H2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl H10 H11)
    as (R' & M' & mi & RUN & (PO & PG & PC & Pmi) & A10 & A2 & A8 & A9 & A18 & A19 & A20 & A21 & AG).
  exists mi, R', M'.
  split; [exact RUN|].
  split.
  { rewrite <- H2 in A2. repeat split; try assumption; apply AG; notin_list. }
  split; [exact A10|].
  split.
  { intros x (Hx1 & Hx2 & _). apply PO; [exact Hx1 | cbn [Z.of_nat Z.add] in Hx2; lia]. }
  split; [exact PG|].
  split.
  { split; [exact I|]. split; [|exact I].
    split; [change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z; lia|].
    rewrite Z.add_0_r. change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z. rewrite Z.mod_small by lia. exact PC. }
  split; [exact Pmi | exact I].
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

End VPORT.
