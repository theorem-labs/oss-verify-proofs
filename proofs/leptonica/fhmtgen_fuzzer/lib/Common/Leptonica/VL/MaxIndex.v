(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import StartupTac RefMemcpyLib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Reloc Require Import RelocKitVL RelocTacVL CanonImgVL RCodeVL_237d4_24000 RCodeVL_24000_25000 RCodeVL_25000_25620.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Musl Require Import MuslTac.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation SEGS := rl_segs.

Section VPORT.
Context {fx : FPState} {RLOC : Reloc} {RCODE : RelocCode RLOC} {RSITES : RelocSites RLOC} {RCODEF : RelocCodeVL RLOC} {RSITESF : RelocSitesVL RLOC} {RLEPT : RelocLept RLOC} {RIMGF : RelocImgVL RLOC}.   (* [comment removed for export] *)


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma wr_readable_u16 : wr_readable SEGS.
Proof. exact rl_wr_readable. Qed.

Section MI.
  (* [comment removed for export] *)
  Variable M : word -> option byte.          (* [comment removed for export] *)
  Variable rom : word -> option byte.
  Variables pix pmax w h d wpl data sp : Z.
  Variables ra s0v s1v s2v s3v s4v s5v s6v : word.   (* [comment removed for export] *)

  Hypothesis Hpix : (1 <= pix /\ pix + 64 <= 2 ^ 64)%Z.
  Hypothesis Hpixal : (pix mod 8 = 0)%Z.
  Hypothesis Hpmax : (1 <= pmax /\ pmax + 4 <= 2 ^ 64)%Z.
  Hypothesis Hpal : (pmax mod 4 = 0)%Z.
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
  Hypothesis Hsp : (128 <= sp /\ sp < 2 ^ 64)%Z.
  Hypothesis Hsp16 : (sp mod 16 = 0)%Z.
  Hypothesis Hra : ret_ok ra.
  (* [comment removed for export] *)
  Hypothesis Cw : rdn SEGS M (Z_to_bv 64 pix) 4 = Some (Z_to_le_bytes 4 w).
  Hypothesis Ch : rdn SEGS M (Z_to_bv 64 (pix + 4)) 4 = Some (Z_to_le_bytes 4 h).
  Hypothesis Cd : rdn SEGS M (Z_to_bv 64 (pix + 8)) 4 = Some (Z_to_le_bytes 4 d).
  Hypothesis Cwpl : rdn SEGS M (Z_to_bv 64 (pix + 16)) 4 = Some (Z_to_le_bytes 4 wpl).
  Hypothesis Cdata : rdn SEGS M (Z_to_bv 64 (pix + 56)) 8 = Some (Z_to_le_bytes 8 data).
  (* [comment removed for export] *)
  Hypothesis HR : (data + 4 * (wpl * h) <= 2 ^ 64 - 1)%Z.
  Hypothesis RR : exists bs, rdn SEGS M (Z_to_bv 64 data) (Z.to_nat (4 * (wpl * h))) = Some bs.
  (* [comment removed for export] *)
  Hypothesis SOKp : store_ok SEGS M (Z_to_bv 64 pmax) 4 = true.
  Hypothesis AP : (pmax + 4 <= pix \/ pix + 64 <= pmax)%Z.
  Hypothesis FPM : (pmax + 4 <= sp - 128 \/ sp <= pmax)%Z.
  (* [comment removed for export] *)
  Hypothesis SOKf : store_ok SEGS M (Z_to_bv 64 (sp - 128)) 128 = true.
  Hypothesis FP : (pix + 64 <= sp - 128 \/ sp <= pix)%Z.

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

  Lemma wplh_bound : (0 <= wpl * h <= 5001 * 20000)%Z.
  Proof. nodisj. clear RR. pose proof wpl_bounds as (Hwpl1 & _). nia. Qed.

  (* [comment removed for export] *)
  Lemma slots_al4 : ((sp - 68) mod 4 = 0 /\ (sp - 72) mod 4 = 0 /\ (sp - 76) mod 4 = 0 /\ (sp - 80) mod 4 = 0)%Z.
  Proof. nodisj. clear RR. repeat split; (apply sp_slot_al4; [exact Hsp16 | reflexivity]). Qed.

  (* [comment removed for export] *)
  Definition MA : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
      (Z_to_bv 64 (sp - 8)) (word_to_le_bytes 8 ra))
      (Z_to_bv 64 (sp - 16)) (word_to_le_bytes 8 s0v))
      (Z_to_bv 64 (sp - 24)) (word_to_le_bytes 8 s1v))
      (Z_to_bv 64 (sp - 32)) (word_to_le_bytes 8 s2v))
      (Z_to_bv 64 (sp - 40)) (word_to_le_bytes 8 s3v))
      (Z_to_bv 64 (sp - 48)) (word_to_le_bytes 8 s4v))
      (Z_to_bv 64 (sp - 56)) (word_to_le_bytes 8 s5v))
      (Z_to_bv 64 (sp - 64)) (word_to_le_bytes 8 s6v).
  (* [comment removed for export] *)
  Definition MB : word -> option byte :=
    wbytes MA (Z_to_bv 64 pmax) (word_to_le_bytes 4 (Z_to_bv 64 0)).
  (* [comment removed for export] *)
  Definition MC : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes MB
      (Z_to_bv 64 (sp - 68)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 72)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 76)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
      (Z_to_bv 64 (sp - 68)) (word_to_le_bytes 4 (Z_to_bv 64 w)))
      (Z_to_bv 64 (sp - 72)) (word_to_le_bytes 4 (Z_to_bv 64 h)))
      (Z_to_bv 64 (sp - 76)) (word_to_le_bytes 4 (Z_to_bv 64 d)).

  (* [comment removed for export] *)
  Lemma sok_frame : forall m k (n : nat), mem_grows M m -> (Z.of_nat n <= k <= 128)%Z ->
    store_ok SEGS m (Z_to_bv 64 (sp - k)) n = true.
  Proof.
    intros m k n Hg Hk. nodisj. eapply store_ok_mono; [exact Hg|].
    destruct n as [|n']; [reflexivity|].
    eapply (store_ok_sub SEGS M (Z_to_bv 64 (sp - 128)) _ 128%nat); [ | exact SOKf | | ];
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
  Ltac ldpix F D z C :=
    stepLD F D (Z_to_le_bytes 4 z) (Z_to_bv 64 z)
      ltac:(unfold v_addi; unorm; rewrite ?Z.add_0_r; peelf; exact C)
      ltac:(apply lez4; lia);
    rewrite (v_lw_small z) by lia.

  (* [comment removed for export] *)
  Ltac zvw F D v := stepiv F D v ltac:(gres; pin; imm_norm; rewrite ?v_addi_0; rewrite ?zbv_addiw_small by lia;
                                       rewrite ?zbv_addi, ?zbv_add, ?zbv_sub, ?zbv_mul; first [reflexivity | f_equal; lia]).
  Ltac zvs F D v := stepiv F D v ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
  (* [comment removed for export] *)
  Ltac zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM; unorm; rewrite EQ; reflexivity).
  (* [comment removed for export] *)
  Ltac condE := pin; rewrite c_eq_Z by lia; first [ apply Z.eqb_eq | apply Z.eqb_neq ]; lia.
  (* [comment removed for export] *)
  Ltac condR := pin; first [ apply c_eq_refl | vm_compute; reflexivity ].
  (* [comment removed for export] *)
  Ltac fixv v tac :=
    lazymatch goal with |- msteps _ (mkst (regupd _ _ ?x) _ _ _) _ => replace x with v by (symmetry; tac) end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mi_A : forall regs,
    getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 sp ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v ->
    getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v -> getr regs 22 = s6v ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 pmax ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_24b70 0x24b70) M rom) (mkst regs' (rl dVL_24b70 0x24bc4) MC rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 80) /\ getr regs' 9 = Z_to_bv 64 pix /\ getr regs' 18 = Z_to_bv 64 pmax
      /\ regs_agree (fun r : reg => In r [1; 2; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18]%list) regs regs'.
  Proof.
    intros regs H1 H2 H8 H9 H18 H19 H20 H21 H22 H10 H11. clear RR.
    pose proof (u64_range ra) as Hrar.
    pose proof slots_al4 as (A68 & A72 & A76 & A80).
    eexists. split.
    - zvw F_24b70 D_24b70 (Z_to_bv 64 (sp - 80)).          (* [comment removed for export] *)
      stf F_24b74 D_24b74 8%Z ra.                             (* [comment removed for export] *)
      stf F_24b78 D_24b78 16%Z s0v.                           (* [comment removed for export] *)
      stf F_24b7c D_24b7c 24%Z s1v.                           (* [comment removed for export] *)
      stf F_24b80 D_24b80 32%Z s2v.                           (* [comment removed for export] *)
      stf F_24b84 D_24b84 40%Z s3v.                           (* [comment removed for export] *)
      stf F_24b88 D_24b88 48%Z s4v.                           (* [comment removed for export] *)
      stf F_24b8c D_24b8c 56%Z s5v.                           (* [comment removed for export] *)
      stf F_24b90 D_24b90 64%Z s6v.                           (* [comment removed for export] *)
      fold MA.
      stepb_ft F_24b94 D_24b94 ltac:(condZ).                (* [comment removed for export] *)
      zvw F_24b98 D_24b98 (Z_to_bv 64 pix).                 (* [comment removed for export] *)
      zand F_24b9c D_24b9c andi_3 Hpal.                     (* [comment removed for export] *)
      stepb_ft F_24ba0 D_24ba0 ltac:(condR).                (* [comment removed for export] *)
      stepST F_24ba4 D_24ba4 (Z_to_bv 64 pmax) (Z_to_bv 64 0) ltac:(apply sok_pmax; unfold MA; grows).  (* [comment removed for export] *)
      fold MB.
      stepb_ft F_24ba8 D_24ba8 ltac:(condZ).                (* [comment removed for export] *)
      zvw F_24bac D_24bac (Z_to_bv 64 pmax).                (* [comment removed for export] *)
      zvw F_24bb0 D_24bb0 (Z_to_bv 64 (sp - 68)).          (* [comment removed for export] *)
      zvw F_24bb4 D_24bb4 (Z_to_bv 64 (sp - 72)).          (* [comment removed for export] *)
      zvw F_24bb8 D_24bb8 (Z_to_bv 64 (sp - 76)).          (* [comment removed for export] *)
      zvw F_24bbc D_24bbc (Z_to_bv 64 pix).                 (* [comment removed for export] *)
      sn F_24bc0 D_24bc0.                                   (* [comment removed for export] *)
      (* [comment removed for export] *)
      zand F_23e10 D_23e10 andi_3 A68.                      (* [comment removed for export] *)
      stepb_ft F_23e14 D_23e14 ltac:(condZ).                (* [comment removed for export] *)
      stepb_ft F_23e18 D_23e18 ltac:(condR).                (* [comment removed for export] *)
      stf F_23e1c D_23e1c 68%Z (Z_to_bv 64 0).                (* [comment removed for export] *)
      zand F_23e20 D_23e20 andi_3 A72.                      (* [comment removed for export] *)
      stepb_ft F_23e24 D_23e24 ltac:(condZ).                (* [comment removed for export] *)
      stepb_ft F_23e28 D_23e28 ltac:(condR).                (* [comment removed for export] *)
      stf F_23e2c D_23e2c 72%Z (Z_to_bv 64 0).                (* [comment removed for export] *)
      zand F_23e30 D_23e30 andi_3 A76.                      (* [comment removed for export] *)
      stepb_ft F_23e34 D_23e34 ltac:(condZ).                (* [comment removed for export] *)
      stepb_ft F_23e38 D_23e38 ltac:(condR).                (* [comment removed for export] *)
      stf F_23e3c D_23e3c 76%Z (Z_to_bv 64 0).                (* [comment removed for export] *)
      stepb_ft F_23e40 D_23e40 ltac:(condZ).                (* [comment removed for export] *)
      zand F_23e44 D_23e44 andi_7 Hpixal.                   (* [comment removed for export] *)
      stepb_ft F_23e48 D_23e48 ltac:(condZ).                (* [comment removed for export] *)
      sn F_23e4c D_23e4c.                                   (* [comment removed for export] *)
      stepb_ft F_23e50 D_23e50 ltac:(condR).                (* [comment removed for export] *)
      ldpix F_23e54 D_23e54 w Cw.                           (* [comment removed for export] *)
      stf F_23e58 D_23e58 68%Z (Z_to_bv 64 w).                (* [comment removed for export] *)
      stepb_ft F_23e5c D_23e5c ltac:(condZ).                (* [comment removed for export] *)
      sn F_23e60 D_23e60.                                   (* [comment removed for export] *)
      stepb_ft F_23e64 D_23e64 ltac:(condR).                (* [comment removed for export] *)
      ldpix F_23e68 D_23e68 h Ch.                           (* [comment removed for export] *)
      stf F_23e6c D_23e6c 72%Z (Z_to_bv 64 h).                (* [comment removed for export] *)
      stepb_ft F_23e70 D_23e70 ltac:(condZ).                (* [comment removed for export] *)
      sn F_23e74 D_23e74.                                   (* [comment removed for export] *)
      stepb_ft F_23e78 D_23e78 ltac:(condR).                (* [comment removed for export] *)
      ldpix F_23e7c D_23e7c d Cd.                           (* [comment removed for export] *)
      stf F_23e80 D_23e80 76%Z (Z_to_bv 64 d).                (* [comment removed for export] *)
      sn F_23e84 D_23e84.                                   (* [comment removed for export] *)
      stepretF F_23e88 D_23e88 F_24bc4. (* [comment removed for export] *)
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
      msteps SEGS (mkst regs (rl dVL_24b70 0x24bc4) MC rom) (mkst regs' (rl dVL_24b70 0x24c04) MC rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 80) /\ getr regs' 10 = Z_to_bv 64 data /\ getr regs' 8 = Z_to_bv 64 wpl
      /\ getr regs' 11 = Z_to_bv 64 d /\ getr regs' 12 = Z_to_bv 64 1
      /\ regs_agree (fun r : reg => In r [1; 8; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs H2 H9. clear RR.
    pose proof wpl_bounds as (Hwpl1 & _ & _).
    eexists. split.
    - ldf F_24bc4 D_24bc4 76%Z d.                           (* [comment removed for export] *)
      sn F_24bc8 D_24bc8.                                   (* [comment removed for export] *)
      stepb_ft F_24bcc D_24bcc ltac:(condZ).                (* [comment removed for export] *)
      sn F_24bd0 D_24bd0.                                   (* [comment removed for export] *)
      sn F_24bd4 D_24bd4.                                   (* [comment removed for export] *)
      sn F_24bd8 D_24bd8.                                   (* [comment removed for export] *)
      stepb_ft F_24bdc D_24bdc ltac:(pin; rewrite (depth_mask_278 d Hd); reflexivity).   (* [comment removed for export] *)
      zvw F_24be0 D_24be0 (Z_to_bv 64 pix).                 (* [comment removed for export] *)
      sn F_24be4 D_24be4.                                   (* [comment removed for export] *)
      stepb_ft F_23ce4 D_23ce4 ltac:(condZ).                (* [comment removed for export] *)
      zand F_23ce8 D_23ce8 andi_7 Hpixal.                   (* [comment removed for export] *)
      stepb_ft F_23cec D_23cec ltac:(condR).                (* [comment removed for export] *)
      ldpix F_23cf0 D_23cf0 wpl Cwpl.                       (* [comment removed for export] *)
      stepretF F_23cf4 D_23cf4 F_24be8. (* [comment removed for export] *)
      zvw F_24be8 D_24be8 (Z_to_bv 64 wpl).                 (* [comment removed for export] *)
      zvw F_24bec D_24bec (Z_to_bv 64 pix).                 (* [comment removed for export] *)
      sn F_24bf0 D_24bf0.                                   (* [comment removed for export] *)
      stepb_ft F_241e4 D_241e4 ltac:(condZ).                (* [comment removed for export] *)
      zand F_241e8 D_241e8 andi_7 Hpixal.                   (* [comment removed for export] *)
      stepb_ft F_241ec D_241ec ltac:(condR).                (* [comment removed for export] *)
      stepLD F_241f0 D_241f0 (Z_to_le_bytes 8 data) (Z_to_bv 64 data)
        ltac:(unfold v_addi; unorm; peelf; exact Cdata)
        ltac:(apply lez8; lia).                             (* [comment removed for export] *)
      stepretF F_241f4 D_241f4 F_24bf4. (* [comment removed for export] *)
      ldf F_24bf4 D_24bf4 76%Z d.                           (* [comment removed for export] *)
      sn F_24bf8 D_24bf8.                                   (* [comment removed for export] *)
      stepb_ft F_24bfc D_24bfc ltac:(condZ).                (* [comment removed for export] *)
      sn F_24c00 D_24c00.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Definition LInv (regs : bvmap 5 word) (t4v t0v : word) : Prop :=
    getr regs 2 = Z_to_bv 64 (sp - 80) /\ getr regs 10 = Z_to_bv 64 data /\ getr regs 12 = Z_to_bv 64 h /\
    getr regs 11 = Z_to_bv 64 d /\ getr regs 15 = Z_to_bv 64 w /\ getr regs 16 = Z_to_bv 64 1 /\
    getr regs 17 = Z_to_bv 64 2 /\ getr regs 5 = t0v /\ getr regs 6 = Z_to_bv 64 4 /\ getr regs 28 = Z_to_bv 64 8 /\
    getr regs 29 = t4v /\ getr regs 30 = Z_to_bv 64 w /\ getr regs 31 = Z_to_bv 64 3 /\ getr regs 7 = Z_to_bv 64 pmax /\
    getr regs 8 = Z_to_bv 64 wpl.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mi_D : forall regs, (d <> 1)%Z ->
    getr regs 2 = Z_to_bv 64 (sp - 80) -> getr regs 10 = Z_to_bv 64 data -> getr regs 8 = Z_to_bv 64 wpl ->
    getr regs 11 = Z_to_bv 64 d -> getr regs 12 = Z_to_bv 64 1 -> getr regs 18 = Z_to_bv 64 pmax ->
    exists regs' t4v t0v,
      msteps SEGS (mkst regs (rl dVL_24b70 0x24c04) MC rom) (mkst regs' (rl dVL_24b70 0x24ce0) MC rom)
      /\ LInv regs' t4v t0v
      /\ getr regs' 13 = Z_to_bv 64 (wpl * 0) /\ getr regs' 14 = Z_to_bv 64 0 /\ getr regs' 9 = Z_to_bv 64 0
      /\ regs_agree (fun r : reg => In r [5; 6; 7; 9; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs Hd1 H2 H10 H8 H11 H12 H18. clear RR.
    pose proof wpl_bounds as (Hwpl1 & _ & _).
    eexists. eexists. eexists. split; [|split].
    - stepb_tk F_24c04 D_24c04 ltac:(condZ).                (* [comment removed for export] *)
      ldf F_24ca0 D_24ca0 72%Z h.                           (* [comment removed for export] *)
      stepb_ft F_24ca4 D_24ca4 ltac:(condZ).                (* [comment removed for export] *)
      sn F_24ca8 D_24ca8.                                   (* [comment removed for export] *)
      fixv (Z_to_bv 64 (wpl * 0)) ltac:(f_equal; lia).
      sn F_24cac D_24cac.                                   (* [comment removed for export] *)
      sn F_24cb0 D_24cb0.                                   (* [comment removed for export] *)
      sn F_24cb4 D_24cb4.                                   (* [comment removed for export] *)
      ldf F_24cb8 D_24cb8 68%Z w.                           (* [comment removed for export] *)
      sn F_24cbc D_24cbc.                                   (* [comment removed for export] *)
      fixv (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).
      sn F_24cc0 D_24cc0.                                   (* [comment removed for export] *)
      sn F_24cc4 D_24cc4.                                   (* [comment removed for export] *)
      sn F_24cc8 D_24cc8.                                   (* [comment removed for export] *)
      sn F_24ccc D_24ccc.                                   (* [comment removed for export] *)
      sn F_24cd0 D_24cd0.                                   (* [comment removed for export] *)
      zvw F_24cd4 D_24cd4 (Z_to_bv 64 w).                   (* [comment removed for export] *)
      sn F_24cd8 D_24cd8.                                   (* [comment removed for export] *)
      zvw F_24cdc D_24cdc (Z_to_bv 64 pmax).                (* [comment removed for export] *)
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
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma row_in_raster : forall i, (0 <= i < h)%Z -> (0 <= 4 * wpl * i /\ 4 * wpl * i + 4 * wpl <= 4 * (wpl * h))%Z.
  Proof.
    intros i Hi. nodisj. clear RR. pose proof wpl_bounds as (Hwpl1 & _).
    assert (wpl * (i + 1) <= wpl * h)%Z by (apply Z.mul_le_mono_nonneg_l; lia). lia.
  Qed.

  (* [comment removed for export] *)
  Definition maxval : Z := (2 ^ d - 1)%Z.
  Lemma maxval_ge : (1 <= maxval <= 255)%Z.
  Proof. nodisj. clear RR. unfold maxval. destruct Hd as [->|[->|[->| ->]]]; cbn; lia. Qed.

  (* [comment removed for export] *)
  Lemma mi_rowP : forall regs t4v t0v i (mx : word), (0 <= i < h)%Z ->
    LInv regs t4v t0v -> getr regs 13 = Z_to_bv 64 (wpl * i) -> getr regs 14 = Z_to_bv 64 i -> getr regs 9 = mx ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_24b70 0x24ce0) MC rom) (mkst regs' (rl dVL_24b70 0x24d14) MC rom)
      /\ LInv regs' t4v t0v /\ getr regs' 13 = Z_to_bv 64 (wpl * i) /\ getr regs' 14 = Z_to_bv 64 i /\ getr regs' 9 = mx
      /\ getr regs' 18 = Z_to_bv 64 (data + 4 * wpl * i)
      /\ regs_agree (fun r : reg => In r [18; 19; 20]%list) regs regs'.
  Proof.
    intros regs t4v t0v i mx Hi HL H13 H14 H9. nodisj. clear RR.
    pose proof HL as (I2 & I10 & I12 & I11 & I15 & I16 & I17 & I5 & I6 & I28 & I29 & I30 & I31 & I7 & I8).
    pose proof (row_in_raster i Hi) as Hrow. pose proof wplh_bound as Hwh.
    eexists. split; [|split; [|split; [|split; [|split; [|split]]]]].
    - zvw F_24ce0 D_24ce0 (Z_to_bv 64 (wpl * i)).         (* [comment removed for export] *)
      sn F_24ce4 D_24ce4.                                   (* [comment removed for export] *)
      fixv (Z_to_bv 64 (wpl * i)) ltac:(rewrite zbv_mulw_small by lia; f_equal; lia).
      stepb_ft F_24ce8 D_24ce8 ltac:(condR).                (* [comment removed for export] *)
      zvw F_24cec D_24cec (Z_to_bv 64 (wpl * i)).         (* [comment removed for export] *)
      zvs F_24cf0 D_24cf0 (Z_to_bv 64 (4 * wpl * i)).       (* [comment removed for export] *)
      zvw F_24cf4 D_24cf4 (Z_to_bv 64 (data + 4 * wpl * i)).   (* [comment removed for export] *)
      stepiv F_24cf8 D_24cf8 (Z_to_bv 64 0)
        ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia). (* [comment removed for export] *)
      stepb_ft F_24cfc D_24cfc ltac:(condR).                (* [comment removed for export] *)
      sn F_24d00 D_24d00.                                   (* [comment removed for export] *)
      fixv (Z_to_bv 64 0) ltac:(apply zbv_sltu_ge; lia).
      sn F_24d04 D_24d04.                                   (* [comment removed for export] *)
      fixv (Z_to_bv 64 0) ltac:(apply zbv_slti0; lia).
      sn F_24d08 D_24d08.                                   (* [comment removed for export] *)
      sn F_24d0c D_24d0c.                                   (* [comment removed for export] *)
      stepb_ft F_24d10 D_24d10 ltac:(condR).                (* [comment removed for export] *)
      apply mst_refl.
    - unfold LInv. repeat split; gres; pin; reflexivity.
    - gres. exact H13.
    - gres. exact H14.
    - gres. exact H9.
    - gres. reflexivity.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
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
    getr regs 18 = Z_to_bv 64 (data + 4 * wpl * i) -> getr regs 16 = Z_to_bv 64 1 -> getr regs 31 = Z_to_bv 64 3 ->
    getr regs 21 = Z_to_bv 64 p -> getr regs 19 = Z_to_bv 64 p -> getr regs 9 = mx -> (bv_unsigned mx <= 255)%Z ->
    exists regs' (mx' : word),
      msteps SEGS (mkst regs (rl dVL_24b70 0x24d48) MC rom) (mkst regs' (rl dVL_24b70 0x24d38) MC rom)
      /\ getr regs' 9 = mx' /\ (bv_unsigned mx' <= 255)%Z
      /\ regs_agree (fun r : reg => In r [9; 22]%list) regs regs'.
  Proof.
    intros regs i p mx Hd8 Hi Hp H18 H16 H31 H21 H19 H9 Hmx. nodisj.
    pose proof wpl_bounds as (Hwpl1 & Hwd & _). rewrite Hd8 in Hwd.
    pose proof (row_in_raster i Hi) as Hrow.
    destruct (byte8_at i p Hd8 Hi Hp) as (f & b & Hxf & Hf & Hb). clear RR.
    pose proof (u_byte64 b) as Hbr.
    assert (S1 : exists r1, msteps SEGS (mkst regs (rl dVL_24b70 0x24d48) MC rom) (mkst r1 (rl dVL_24b70 0x24d64) MC rom)
                            /\ getr r1 22 = Z_to_bv 64 (bv_unsigned b) /\ getr r1 9 = mx
                            /\ regs_agree (fun r : reg => In r [22]%list) regs r1).
    { eexists. split; [|split; [|split]].
      - stepb_ft F_24d48 D_24d48 ltac:(condZ).              (* [comment removed for export] *)
        stepiv F_24d4c D_24d4c (Z_to_bv 64 0)
          ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).   (* [comment removed for export] *)
        sn F_24d50 D_24d50.                                 (* [comment removed for export] *)
        stepb_ft F_24d54 D_24d54 ltac:(condR).              (* [comment removed for export] *)
        stepb_ft F_24d58 D_24d58 ltac:(condE).              (* [comment removed for export] *)
        stepiv F_24d5c D_24d5c (Z_to_bv 64 f) ltac:(gres; pin; imm_norm; exact Hxf).   (* [comment removed for export] *)
        stepLBU F_24d60 D_24d60 b ltac:(rdn_addr f; exact Hb).                           (* [comment removed for export] *)
        apply mst_refl.
      - gres. reflexivity.
      - gres. exact H9.
      - solve_regs_agree. }
    destruct S1 as (r1 & S1 & Q22 & Q9 & AG1).
    destruct (c_lts (Z_to_bv 64 (bv_unsigned b)) mx) eqn:Hc.
    - (* [comment removed for export] *)
      exists r1, mx. split; [|split; [exact Q9 | split; [exact Hmx | regs_agree_weaken AG1]]].
      eapply msteps_trans; [exact S1|].
      stepb_tk F_24d64 D_24d64 ltac:(pin; exact Hc).        (* [comment removed for export] *)
      apply mst_refl.
    - (* [comment removed for export] *)
      eexists. exists (Z_to_bv 64 (bv_unsigned b)). split; [|split; [|split; [lia|]]].
      + eapply msteps_trans; [exact S1|].
        stepb_ft F_24d64 D_24d64 ltac:(pin; exact Hc).      (* [comment removed for export] *)
        zvw F_24d68 D_24d68 (Z_to_bv 64 (bv_unsigned b)).  (* [comment removed for export] *)
        sn F_24d6c D_24d6c.                                 (* [comment removed for export] *)
        apply mst_refl.
      + gres. reflexivity.
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma mi_L8 : forall k regs i p (mx : word), (d = 8)%Z -> (0 <= i < h)%Z ->
    (Z.of_nat k = data + 4 * wpl * i + w - 1 - p)%Z -> (data + 4 * wpl * i <= p)%Z ->
    getr regs 18 = Z_to_bv 64 (data + 4 * wpl * i) -> getr regs 16 = Z_to_bv 64 1 -> getr regs 31 = Z_to_bv 64 3 ->
    getr regs 21 = Z_to_bv 64 p -> getr regs 19 = Z_to_bv 64 p -> getr regs 20 = Z_to_bv 64 (Z.of_nat k + 1) ->
    getr regs 9 = mx -> (bv_unsigned mx <= 255)%Z ->
    exists regs' (mx' : word),
      msteps SEGS (mkst regs (rl dVL_24b70 0x24d48) MC rom) (mkst regs' (rl dVL_24b70 0x24e48) MC rom)
      /\ getr regs' 9 = mx' /\ (bv_unsigned mx' <= 255)%Z
      /\ regs_agree (fun r : reg => In r [9; 19; 20; 21; 22]%list) regs regs'.
  Proof.
    nodisj. pose proof wpl_bounds as (Hwpl1 & Hwd & _).
    induction k as [|k IH]; intros regs i p mx Hd8 Hi Hk Hp H18 H16 H31 H21 H19 H20 H9 Hmx;
      destruct (mi_b8 regs i p mx Hd8 Hi ltac:(lia) H18 H16 H31 H21 H19 H9 Hmx) as (r1 & mx1 & S1 & R9 & Hmx1 & AG1);
      pose proof (AG1 21 ltac:(notin_list)) as R21; rewrite H21 in R21;
      pose proof (AG1 19 ltac:(notin_list)) as R19; rewrite H19 in R19;
      pose proof (AG1 20 ltac:(notin_list)) as R20; rewrite H20 in R20;
      pose proof (row_in_raster i Hi) as Hrow; rewrite Hd8 in Hwd.
    - (* [comment removed for export] *)
      eexists. exists mx1. split; [|split; [|split; [exact Hmx1|]]].
      + eapply msteps_trans; [exact S1|].
        zvw F_24d38 D_24d38 (Z_to_bv 64 (p + 1)).            (* [comment removed for export] *)
        zvw F_24d3c D_24d3c (Z_to_bv 64 0).                  (* [comment removed for export] *)
        zvw F_24d40 D_24d40 (Z_to_bv 64 (p + 1)).            (* [comment removed for export] *)
        stepb_tk F_24d44 D_24d44 ltac:(condR).                (* [comment removed for export] *)
        apply mst_refl.
      + gres. exact R9.
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - assert (S2 : exists r2, msteps SEGS (mkst r1 (rl dVL_24b70 0x24d38) MC rom) (mkst r2 (rl dVL_24b70 0x24d48) MC rom)
                              /\ getr r2 18 = Z_to_bv 64 (data + 4 * wpl * i) /\ getr r2 16 = Z_to_bv 64 1
                              /\ getr r2 31 = Z_to_bv 64 3 /\ getr r2 21 = Z_to_bv 64 (p + 1) /\ getr r2 19 = Z_to_bv 64 (p + 1)
                              /\ getr r2 20 = Z_to_bv 64 (Z.of_nat k + 1) /\ getr r2 9 = mx1
                              /\ regs_agree (fun r : reg => In r [19; 20; 21]%list) r1 r2).
      { eexists. split.
        - zvw F_24d38 D_24d38 (Z_to_bv 64 (p + 1)).          (* [comment removed for export] *)
          zvw F_24d3c D_24d3c (Z_to_bv 64 (Z.of_nat k + 1)). (* [comment removed for export] *)
          zvw F_24d40 D_24d40 (Z_to_bv 64 (p + 1)).          (* [comment removed for export] *)
          stepb_ft F_24d44 D_24d44 ltac:(condE).              (* [comment removed for export] *)
          apply mst_refl.
        - repeat split; gres; pin; try reflexivity; try (rewrite AG1 by notin_list; assumption). solve_regs_agree. }
      destruct S2 as (r2 & S2 & Q18 & Q16 & Q31 & Q21 & Q19 & Q20 & Q9 & AG2).
      destruct (IH r2 i (p + 1)%Z mx1 Hd8 Hi ltac:(lia) ltac:(lia) Q18 Q16 Q31 Q21 Q19 Q20 Q9 Hmx1)
        as (r3 & mx3 & S3 & T9 & Hmx3 & AG3).
      exists r3, mx3. split; [|split; [exact T9 | split; [exact Hmx3|]]].
      + eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2 | exact S3].
      + eapply regs_agree_trans; [regs_agree_weaken AG1|].
        eapply regs_agree_trans; [regs_agree_weaken AG2 | exact AG3].
  Qed.

  (* [comment removed for export] *)
  Lemma mi_R8 : forall regs t4v t0v i (mx : word), (d = 8)%Z -> (0 <= i < h)%Z ->
    LInv regs t4v t0v -> getr regs 13 = Z_to_bv 64 (wpl * i) -> getr regs 18 = Z_to_bv 64 (data + 4 * wpl * i) ->
    getr regs 9 = mx -> (bv_unsigned mx <= maxval)%Z ->
    exists regs' (mx' : word),
      msteps SEGS (mkst regs (rl dVL_24b70 0x24d14) MC rom) (mkst regs' (rl dVL_24b70 0x24e48) MC rom)
      /\ getr regs' 9 = mx' /\ (bv_unsigned mx' <= maxval)%Z
      /\ regs_agree (fun r : reg => In r [9; 19; 20; 21; 22]%list) regs regs'.
  Proof.
    intros regs t4v t0v i mx Hd8 Hi HL H13 H18 H9 Hmx. nodisj.
    destruct HL as (I2 & I10 & I12 & I11 & I15 & I16 & I17 & I5 & I6 & I28 & I29 & I30 & I31 & I7 & I8).
    pose proof wpl_bounds as (Hwpl1 & Hwd & _). rewrite Hd8 in Hwd.
    pose proof (row_in_raster i Hi) as Hrow.
    assert (Hmv : maxval = 255%Z) by (unfold maxval; rewrite Hd8; reflexivity). rewrite Hmv in Hmx |- *.
    assert (S1 : exists r1, msteps SEGS (mkst regs (rl dVL_24b70 0x24d14) MC rom) (mkst r1 (rl dVL_24b70 0x24d48) MC rom)
                            /\ getr r1 18 = Z_to_bv 64 (data + 4 * wpl * i) /\ getr r1 16 = Z_to_bv 64 1
                            /\ getr r1 31 = Z_to_bv 64 3 /\ getr r1 21 = Z_to_bv 64 (data + 4 * wpl * i)
                            /\ getr r1 19 = Z_to_bv 64 (data + 4 * wpl * i) /\ getr r1 20 = Z_to_bv 64 (Z.of_nat (Z.to_nat (w - 1)) + 1)
                            /\ getr r1 9 = mx
                            /\ regs_agree (fun r : reg => In r [19; 20; 21]%list) regs r1).
    { eexists. split.
      - stepb_ft F_24d14 D_24d14 ltac:(condZ).              (* [comment removed for export] *)
        stepb_ft F_24d18 D_24d18 ltac:(condZ).              (* [comment removed for export] *)
        stepb_ft F_24d1c D_24d1c ltac:(condZ).              (* [comment removed for export] *)
        zvs F_24d20 D_24d20 (Z_to_bv 64 (4 * wpl * i)).     (* [comment removed for export] *)
        zvw F_24d24 D_24d24 (Z_to_bv 64 (data + 4 * wpl * i)).   (* [comment removed for export] *)
        zvw F_24d28 D_24d28 (Z_to_bv 64 (Z.of_nat (Z.to_nat (w - 1)) + 1)).   (* [comment removed for export] *)
        zvw F_24d2c D_24d2c (Z_to_bv 64 (data + 4 * wpl * i)).   (* [comment removed for export] *)
        stepb_tk F_24d30 D_24d30 ltac:(condZ).              (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
    destruct S1 as (r1 & S1 & Q18 & Q16 & Q31 & Q21 & Q19 & Q20 & Q9 & AG1).
    destruct (mi_L8 (Z.to_nat (w - 1)) r1 i (data + 4 * wpl * i)%Z mx Hd8 Hi ltac:(lia) ltac:(lia) Q18 Q16 Q31 Q21 Q19 Q20 Q9 Hmx)
      as (r2 & mx2 & S2 & T9 & Hmx2 & AG2).
    exists r2, mx2. split; [|split; [exact T9 | split; [exact Hmx2|]]].
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
  Lemma mi_w4 : forall regs i j (s3w mx : word), (d = 4)%Z -> (0 <= i < h)%Z -> (0 <= j < w)%Z ->
    getr regs 18 = Z_to_bv 64 (data + 4 * wpl * i) -> getr regs 16 = Z_to_bv 64 1 -> getr regs 10 = Z_to_bv 64 data ->
    getr regs 20 = Z_to_bv 64 j -> getr regs 19 = s3w -> getr regs 21 = mx ->
    exists regs' (v : word),
      msteps SEGS (mkst regs (rl dVL_24b70 0x24d94) MC rom) (mkst regs' (rl dVL_24b70 0x24dd0) MC rom)
      /\ getr regs' 9 = v /\ (bv_unsigned v <= 15)%Z
      /\ getr regs' 18 = Z_to_bv 64 (data + 4 * wpl * i) /\ getr regs' 20 = Z_to_bv 64 j /\ getr regs' 19 = s3w
      /\ getr regs' 21 = mx
      /\ regs_agree (fun r : reg => In r [9; 22]%list) regs regs'.
  Proof.
    intros regs i j s3w mx Hd4 Hi Hj H18 H16 H10 H20 H19 H21. nodisj.
    pose proof (qbit_word j Hd4 Hj) as Hq. pose proof (row_in_raster i Hi) as Hrow.
    destruct (word_at i (j / 8) Hi Hq) as (bs & Hbs & Lbs). clear RR.
    pose proof (word_addr_al4 data wpl i (j / 8) Hdal) as Hal.
    eexists. eexists. split; [|split; [|split]].
    - sn F_24d94 D_24d94.                                   (* [comment removed for export] *)
      fixv (Z_to_bv 64 (j / 8)) ltac:(change (2 ^ 3)%Z with 8%Z; apply zbv_srliw_small; lia).
      zvs F_24d98 D_24d98 (Z_to_bv 64 (4 * (j / 8))).       (* [comment removed for export] *)
      zvw F_24d9c D_24d9c (Z_to_bv 64 (data + 4 * wpl * i + 4 * (j / 8))).   (* [comment removed for export] *)
      stepb_ft F_24da0 D_24da0 ltac:(condZ).                (* [comment removed for export] *)
      stepiv F_24da4 D_24da4 (Z_to_bv 64 0)
        ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia). (* [comment removed for export] *)
      sn F_24da8 D_24da8.                                   (* [comment removed for export] *)
      stepb_ft F_24dac D_24dac ltac:(condR).                (* [comment removed for export] *)
      stepb_ft F_24db0 D_24db0 ltac:(condZ).                (* [comment removed for export] *)
      zand F_24db4 D_24db4 andi_3 Hal.                      (* [comment removed for export] *)
      stepb_ft F_24db8 D_24db8 ltac:(condR).                (* [comment removed for export] *)
      stepLD F_24dbc D_24dbc bs (Z_to_bv 64 (bytes_le_to_Z bs))
        ltac:(rdn_addr (data + 4 * wpl * i + 4 * (j / 8))%Z; exact Hbs)
        ltac:(symmetry; apply u_lez4; exact Lbs).          (* [comment removed for export] *)
      sn F_24dc0 D_24dc0.                                   (* [comment removed for export] *)
      sn F_24dc4 D_24dc4.                                   (* [comment removed for export] *)
      sn F_24dc8 D_24dc8.                                   (* [comment removed for export] *)
      sn F_24dcc D_24dcc.                                   (* [comment removed for export] *)
      apply mst_refl.
    - gres. reflexivity.
    - apply u_andi_15.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma mi_b4 : forall regs i j (s3w mx : word), (d = 4)%Z -> (0 <= i < h)%Z -> (0 <= j < w)%Z ->
    getr regs 18 = Z_to_bv 64 (data + 4 * wpl * i) -> getr regs 16 = Z_to_bv 64 1 -> getr regs 10 = Z_to_bv 64 data ->
    getr regs 20 = Z_to_bv 64 j -> getr regs 19 = s3w -> getr regs 21 = mx -> (bv_unsigned mx <= 15)%Z ->
    exists regs' (mx' : word),
      msteps SEGS (mkst regs (rl dVL_24b70 0x24d94) MC rom) (mkst regs' (rl dVL_24b70 0x24d90) MC rom)
      /\ getr regs' 9 = mx' /\ getr regs' 21 = mx' /\ (bv_unsigned mx' <= 15)%Z
      /\ getr regs' 18 = Z_to_bv 64 (data + 4 * wpl * i) /\ getr regs' 20 = Z_to_bv 64 (j + 1)
      /\ regs_agree (fun r : reg => In r [9; 19; 20; 21; 22]%list) regs regs'.
  Proof.
    intros regs i j s3w mx Hd4 Hi Hj H18 H16 H10 H20 H19 H21 Hmx. nodisj.
    destruct (mi_w4 regs i j s3w mx Hd4 Hi Hj H18 H16 H10 H20 H19 H21) as (r1 & v & S1 & Q9 & Hv & Q18 & Q20 & Q19 & Q21 & AG1).
    pose proof (u64_range v) as Hvr. pose proof (u64_range mx) as Hmxr.
    destruct (c_lts mx v) eqn:Hc.
    - (* [comment removed for export] *)
      eexists. exists v. split.
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_24dd0 D_24dd0 ltac:(pin; exact Hc).      (* [comment removed for export] *)
        zvw F_24d84 D_24d84 (Z_to_bv 64 (j + 1)).           (* [comment removed for export] *)
        sn F_24d88 D_24d88.                                 (* [comment removed for export] *)
        zvw F_24d8c D_24d8c v.                              (* [comment removed for export] *)
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity; try assumption.
        eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - (* [comment removed for export] *)
      eexists. exists mx. split.
      + eapply msteps_trans; [exact S1|].
        stepb_ft F_24dd0 D_24dd0 ltac:(pin; exact Hc).      (* [comment removed for export] *)
        zvw F_24dd4 D_24dd4 mx.                             (* [comment removed for export] *)
        sn F_24dd8 D_24dd8.                                 (* [comment removed for export] *)
        zvw F_24d84 D_24d84 (Z_to_bv 64 (j + 1)).           (* [comment removed for export] *)
        sn F_24d88 D_24d88.                                 (* [comment removed for export] *)
        zvw F_24d8c D_24d8c mx.                             (* [comment removed for export] *)
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity; try assumption.
        eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma mi_L4 : forall k regs i j (s3w mx : word), (d = 4)%Z -> (0 <= i < h)%Z ->
    (Z.of_nat k = w - 1 - j)%Z -> (0 <= j)%Z ->
    getr regs 30 = Z_to_bv 64 w ->
    getr regs 18 = Z_to_bv 64 (data + 4 * wpl * i) -> getr regs 16 = Z_to_bv 64 1 -> getr regs 10 = Z_to_bv 64 data ->
    getr regs 20 = Z_to_bv 64 j -> getr regs 19 = s3w -> getr regs 21 = mx -> (bv_unsigned mx <= 15)%Z ->
    exists regs' (mx' : word),
      msteps SEGS (mkst regs (rl dVL_24b70 0x24d94) MC rom) (mkst regs' (rl dVL_24b70 0x24e48) MC rom)
      /\ getr regs' 9 = mx' /\ (bv_unsigned mx' <= 15)%Z
      /\ regs_agree (fun r : reg => In r [9; 19; 20; 21; 22]%list) regs regs'.
  Proof.
    nodisj.
    induction k as [|k IH]; intros regs i j s3w mx Hd4 Hi Hk Hj H30 H18 H16 H10 H20 H19 H21 Hmx;
      destruct (mi_b4 regs i j s3w mx Hd4 Hi ltac:(lia) H18 H16 H10 H20 H19 H21 Hmx)
        as (r1 & mx1 & S1 & R9 & R21 & Hmx1 & R18 & R20 & AG1);
      pose proof (AG1 30 ltac:(notin_list)) as R30; rewrite H30 in R30;
      pose proof (AG1 16 ltac:(notin_list)) as R16; rewrite H16 in R16;
      pose proof (AG1 10 ltac:(notin_list)) as R10; rewrite H10 in R10.
    - (* [comment removed for export] *)
      eexists. exists mx1. split; [|split; [exact R9 | split; [exact Hmx1|]]].
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_24d90 D_24d90 ltac:(condZ).                (* [comment removed for export] *)
        apply mst_refl.
      + exact AG1.
    - assert (S2 : msteps SEGS (mkst r1 (rl dVL_24b70 0x24d90) MC rom) (mkst r1 (rl dVL_24b70 0x24d94) MC rom)).
      { stepb_ft F_24d90 D_24d90 ltac:(condZ).                (* [comment removed for export] *)
        apply mst_refl. }
      destruct (IH r1 i (j + 1)%Z (getr r1 19) mx1 Hd4 Hi ltac:(lia) ltac:(lia) R30 R18 R16 R10 R20 eq_refl R21 Hmx1)
        as (r3 & mx3 & S3 & T9 & Hmx3 & AG3).
      exists r3, mx3. split; [|split; [exact T9 | split; [exact Hmx3|]]].
      + eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2 | exact S3].
      + eapply regs_agree_trans; [exact AG1 | exact AG3].
  Qed.

  (* [comment removed for export] *)
  Lemma mi_R4 : forall regs t4v t0v i (mx : word), (d = 4)%Z -> (0 <= i < h)%Z ->
    LInv regs t4v t0v -> getr regs 13 = Z_to_bv 64 (wpl * i) -> getr regs 18 = Z_to_bv 64 (data + 4 * wpl * i) ->
    getr regs 9 = mx -> (bv_unsigned mx <= maxval)%Z ->
    exists regs' (mx' : word),
      msteps SEGS (mkst regs (rl dVL_24b70 0x24d14) MC rom) (mkst regs' (rl dVL_24b70 0x24e48) MC rom)
      /\ getr regs' 9 = mx' /\ (bv_unsigned mx' <= maxval)%Z
      /\ regs_agree (fun r : reg => In r [9; 19; 20; 21; 22]%list) regs regs'.
  Proof.
    intros regs t4v t0v i mx Hd4 Hi HL H13 H18 H9 Hmx. nodisj.
    destruct HL as (I2 & I10 & I12 & I11 & I15 & I16 & I17 & I5 & I6 & I28 & I29 & I30 & I31 & I7 & I8).
    assert (Hmv : maxval = 15%Z) by (unfold maxval; rewrite Hd4; reflexivity). rewrite Hmv in Hmx |- *.
    assert (S1 : exists r1, msteps SEGS (mkst regs (rl dVL_24b70 0x24d14) MC rom) (mkst r1 (rl dVL_24b70 0x24d94) MC rom)
                            /\ getr r1 30 = Z_to_bv 64 w /\ getr r1 18 = Z_to_bv 64 (data + 4 * wpl * i)
                            /\ getr r1 16 = Z_to_bv 64 1 /\ getr r1 10 = Z_to_bv 64 data
                            /\ getr r1 20 = Z_to_bv 64 0 /\ getr r1 21 = mx
                            /\ regs_agree (fun r : reg => In r [19; 20; 21]%list) regs r1).
    { eexists. split.
      - stepb_ft F_24d14 D_24d14 ltac:(condZ).              (* [comment removed for export] *)
        stepb_tk F_24d18 D_24d18 ltac:(condZ).              (* [comment removed for export] *)
        stepb_ft F_24d70 D_24d70 ltac:(condZ).              (* [comment removed for export] *)
        sn F_24d74 D_24d74.                                 (* [comment removed for export] *)
        sn F_24d78 D_24d78.                                 (* [comment removed for export] *)
        zvw F_24d7c D_24d7c mx.                             (* [comment removed for export] *)
        sn F_24d80 D_24d80.                                 (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
    destruct S1 as (r1 & S1 & Q30 & Q18 & Q16 & Q10 & Q20 & Q21 & AG1).
    destruct (mi_L4 (Z.to_nat (w - 1)) r1 i 0 (getr r1 19) mx Hd4 Hi ltac:(lia) ltac:(lia) Q30 Q18 Q16 Q10 Q20 eq_refl Q21 Hmx)
      as (r2 & mx2 & S2 & T9 & Hmx2 & AG2).
    exists r2, mx2. split; [|split; [exact T9 | split; [exact Hmx2|]]].
    - eapply msteps_trans; [exact S1 | exact S2].
    - eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mi_w2 : forall regs i j (s3w mx : word), (d = 2)%Z -> (0 <= i < h)%Z -> (0 <= j < w)%Z ->
    getr regs 18 = Z_to_bv 64 (data + 4 * wpl * i) -> getr regs 16 = Z_to_bv 64 1 -> getr regs 10 = Z_to_bv 64 data ->
    getr regs 20 = Z_to_bv 64 j -> getr regs 19 = s3w -> getr regs 21 = mx ->
    exists regs' (v : word),
      msteps SEGS (mkst regs (rl dVL_24b70 0x24e00) MC rom) (mkst regs' (rl dVL_24b70 0x24e3c) MC rom)
      /\ getr regs' 9 = v /\ (bv_unsigned v <= 3)%Z
      /\ getr regs' 18 = Z_to_bv 64 (data + 4 * wpl * i) /\ getr regs' 20 = Z_to_bv 64 j /\ getr regs' 19 = s3w
      /\ getr regs' 21 = mx
      /\ regs_agree (fun r : reg => In r [9; 22]%list) regs regs'.
  Proof.
    intros regs i j s3w mx Hd2 Hi Hj H18 H16 H10 H20 H19 H21. nodisj.
    pose proof (dibit_word j Hd2 Hj) as Hq. pose proof (row_in_raster i Hi) as Hrow.
    destruct (word_at i (j / 16) Hi Hq) as (bs & Hbs & Lbs). clear RR.
    pose proof (word_addr_al4 data wpl i (j / 16) Hdal) as Hal.
    eexists. eexists. split; [|split; [|split]].
    - sn F_24e00 D_24e00.                                   (* [comment removed for export] *)
      fixv (Z_to_bv 64 (j / 16)) ltac:(change (2 ^ 4)%Z with 16%Z; apply zbv_srliw_small; lia).
      zvs F_24e04 D_24e04 (Z_to_bv 64 (4 * (j / 16))).       (* [comment removed for export] *)
      zvw F_24e08 D_24e08 (Z_to_bv 64 (data + 4 * wpl * i + 4 * (j / 16))).   (* [comment removed for export] *)
      stepb_ft F_24e0c D_24e0c ltac:(condZ).                (* [comment removed for export] *)
      stepiv F_24e10 D_24e10 (Z_to_bv 64 0)
        ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia). (* [comment removed for export] *)
      sn F_24e14 D_24e14.                                   (* [comment removed for export] *)
      stepb_ft F_24e18 D_24e18 ltac:(condR).                (* [comment removed for export] *)
      stepb_ft F_24e1c D_24e1c ltac:(condZ).                (* [comment removed for export] *)
      zand F_24e20 D_24e20 andi_3 Hal.                      (* [comment removed for export] *)
      stepb_ft F_24e24 D_24e24 ltac:(condR).                (* [comment removed for export] *)
      stepLD F_24e28 D_24e28 bs (Z_to_bv 64 (bytes_le_to_Z bs))
        ltac:(rdn_addr (data + 4 * wpl * i + 4 * (j / 16))%Z; exact Hbs)
        ltac:(symmetry; apply u_lez4; exact Lbs).          (* [comment removed for export] *)
      sn F_24e2c D_24e2c.                                   (* [comment removed for export] *)
      sn F_24e30 D_24e30.                                   (* [comment removed for export] *)
      sn F_24e34 D_24e34.                                   (* [comment removed for export] *)
      sn F_24e38 D_24e38.                                   (* [comment removed for export] *)
      apply mst_refl.
    - gres. reflexivity.
    - apply u_andi_3.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma mi_b2 : forall regs i j (s3w mx : word), (d = 2)%Z -> (0 <= i < h)%Z -> (0 <= j < w)%Z ->
    getr regs 18 = Z_to_bv 64 (data + 4 * wpl * i) -> getr regs 16 = Z_to_bv 64 1 -> getr regs 10 = Z_to_bv 64 data ->
    getr regs 20 = Z_to_bv 64 j -> getr regs 19 = s3w -> getr regs 21 = mx -> (bv_unsigned mx <= 3)%Z ->
    exists regs' (mx' : word),
      msteps SEGS (mkst regs (rl dVL_24b70 0x24e00) MC rom) (mkst regs' (rl dVL_24b70 0x24dfc) MC rom)
      /\ getr regs' 9 = mx' /\ getr regs' 21 = mx' /\ (bv_unsigned mx' <= 3)%Z
      /\ getr regs' 18 = Z_to_bv 64 (data + 4 * wpl * i) /\ getr regs' 20 = Z_to_bv 64 (j + 1)
      /\ regs_agree (fun r : reg => In r [9; 19; 20; 21; 22]%list) regs regs'.
  Proof.
    intros regs i j s3w mx Hd2 Hi Hj H18 H16 H10 H20 H19 H21 Hmx. nodisj.
    destruct (mi_w2 regs i j s3w mx Hd2 Hi Hj H18 H16 H10 H20 H19 H21) as (r1 & v & S1 & Q9 & Hv & Q18 & Q20 & Q19 & Q21 & AG1).
    pose proof (u64_range v) as Hvr. pose proof (u64_range mx) as Hmxr.
    destruct (c_lts mx v) eqn:Hc.
    - (* [comment removed for export] *)
      eexists. exists v. split.
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_24e3c D_24e3c ltac:(pin; exact Hc).      (* [comment removed for export] *)
        zvw F_24df0 D_24df0 (Z_to_bv 64 (j + 1)).           (* [comment removed for export] *)
        sn F_24df4 D_24df4.                                 (* [comment removed for export] *)
        zvw F_24df8 D_24df8 v.                              (* [comment removed for export] *)
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity; try assumption.
        eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - (* [comment removed for export] *)
      eexists. exists mx. split.
      + eapply msteps_trans; [exact S1|].
        stepb_ft F_24e3c D_24e3c ltac:(pin; exact Hc).      (* [comment removed for export] *)
        zvw F_24e40 D_24e40 mx.                             (* [comment removed for export] *)
        sn F_24e44 D_24e44.                                 (* [comment removed for export] *)
        zvw F_24df0 D_24df0 (Z_to_bv 64 (j + 1)).           (* [comment removed for export] *)
        sn F_24df4 D_24df4.                                 (* [comment removed for export] *)
        zvw F_24df8 D_24df8 mx.                             (* [comment removed for export] *)
        apply mst_refl.
      + repeat split; gres; pin; try reflexivity; try assumption.
        eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma mi_L2 : forall k regs i j (s3w mx : word), (d = 2)%Z -> (0 <= i < h)%Z ->
    (Z.of_nat k = w - 1 - j)%Z -> (0 <= j)%Z ->
    getr regs 30 = Z_to_bv 64 w ->
    getr regs 18 = Z_to_bv 64 (data + 4 * wpl * i) -> getr regs 16 = Z_to_bv 64 1 -> getr regs 10 = Z_to_bv 64 data ->
    getr regs 20 = Z_to_bv 64 j -> getr regs 19 = s3w -> getr regs 21 = mx -> (bv_unsigned mx <= 3)%Z ->
    exists regs' (mx' : word),
      msteps SEGS (mkst regs (rl dVL_24b70 0x24e00) MC rom) (mkst regs' (rl dVL_24b70 0x24e48) MC rom)
      /\ getr regs' 9 = mx' /\ (bv_unsigned mx' <= 3)%Z
      /\ regs_agree (fun r : reg => In r [9; 19; 20; 21; 22]%list) regs regs'.
  Proof.
    nodisj.
    induction k as [|k IH]; intros regs i j s3w mx Hd2 Hi Hk Hj H30 H18 H16 H10 H20 H19 H21 Hmx;
      destruct (mi_b2 regs i j s3w mx Hd2 Hi ltac:(lia) H18 H16 H10 H20 H19 H21 Hmx)
        as (r1 & mx1 & S1 & R9 & R21 & Hmx1 & R18 & R20 & AG1);
      pose proof (AG1 30 ltac:(notin_list)) as R30; rewrite H30 in R30;
      pose proof (AG1 16 ltac:(notin_list)) as R16; rewrite H16 in R16;
      pose proof (AG1 10 ltac:(notin_list)) as R10; rewrite H10 in R10.
    - (* [comment removed for export] *)
      eexists. exists mx1. split; [|split; [exact R9 | split; [exact Hmx1|]]].
      + eapply msteps_trans; [exact S1|].
        stepb_tk F_24dfc D_24dfc ltac:(condZ).                (* [comment removed for export] *)
        apply mst_refl.
      + exact AG1.
    - assert (S2 : msteps SEGS (mkst r1 (rl dVL_24b70 0x24dfc) MC rom) (mkst r1 (rl dVL_24b70 0x24e00) MC rom)).
      { stepb_ft F_24dfc D_24dfc ltac:(condZ).                (* [comment removed for export] *)
        apply mst_refl. }
      destruct (IH r1 i (j + 1)%Z (getr r1 19) mx1 Hd2 Hi ltac:(lia) ltac:(lia) R30 R18 R16 R10 R20 eq_refl R21 Hmx1)
        as (r3 & mx3 & S3 & T9 & Hmx3 & AG3).
      exists r3, mx3. split; [|split; [exact T9 | split; [exact Hmx3|]]].
      + eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2 | exact S3].
      + eapply regs_agree_trans; [exact AG1 | exact AG3].
  Qed.

  (* [comment removed for export] *)
  Lemma mi_R2 : forall regs t4v t0v i (mx : word), (d = 2)%Z -> (0 <= i < h)%Z ->
    LInv regs t4v t0v -> getr regs 13 = Z_to_bv 64 (wpl * i) -> getr regs 18 = Z_to_bv 64 (data + 4 * wpl * i) ->
    getr regs 9 = mx -> (bv_unsigned mx <= maxval)%Z ->
    exists regs' (mx' : word),
      msteps SEGS (mkst regs (rl dVL_24b70 0x24d14) MC rom) (mkst regs' (rl dVL_24b70 0x24e48) MC rom)
      /\ getr regs' 9 = mx' /\ (bv_unsigned mx' <= maxval)%Z
      /\ regs_agree (fun r : reg => In r [9; 19; 20; 21; 22]%list) regs regs'.
  Proof.
    intros regs t4v t0v i mx Hd2 Hi HL H13 H18 H9 Hmx. nodisj.
    destruct HL as (I2 & I10 & I12 & I11 & I15 & I16 & I17 & I5 & I6 & I28 & I29 & I30 & I31 & I7 & I8).
    assert (Hmv : maxval = 3%Z) by (unfold maxval; rewrite Hd2; reflexivity). rewrite Hmv in Hmx |- *.
    assert (S1 : exists r1, msteps SEGS (mkst regs (rl dVL_24b70 0x24d14) MC rom) (mkst r1 (rl dVL_24b70 0x24e00) MC rom)
                            /\ getr r1 30 = Z_to_bv 64 w /\ getr r1 18 = Z_to_bv 64 (data + 4 * wpl * i)
                            /\ getr r1 16 = Z_to_bv 64 1 /\ getr r1 10 = Z_to_bv 64 data
                            /\ getr r1 20 = Z_to_bv 64 0 /\ getr r1 21 = mx
                            /\ regs_agree (fun r : reg => In r [19; 20; 21]%list) regs r1).
    { eexists. split.
      - stepb_tk F_24d14 D_24d14 ltac:(condZ).              (* [comment removed for export] *)
        stepb_ft F_24ddc D_24ddc ltac:(condZ).              (* [comment removed for export] *)
        sn F_24de0 D_24de0.                                 (* [comment removed for export] *)
        sn F_24de4 D_24de4.                                 (* [comment removed for export] *)
        zvw F_24de8 D_24de8 mx.                             (* [comment removed for export] *)
        sn F_24dec D_24dec.                                 (* [comment removed for export] *)
        apply mst_refl.
      - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
    destruct S1 as (r1 & S1 & Q30 & Q18 & Q16 & Q10 & Q20 & Q21 & AG1).
    destruct (mi_L2 (Z.to_nat (w - 1)) r1 i 0 (getr r1 19) mx Hd2 Hi ltac:(lia) ltac:(lia) Q30 Q18 Q16 Q10 Q20 eq_refl Q21 Hmx)
      as (r2 & mx2 & S2 & T9 & Hmx2 & AG2).
    exists r2, mx2. split; [|split; [exact T9 | split; [exact Hmx2|]]].
    - eapply msteps_trans; [exact S1 | exact S2].
    - eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
  Qed.

  (* [comment removed for export] *)
  Lemma mi_row : forall regs t4v t0v i (mx : word), (d <> 1)%Z -> (0 <= i < h)%Z ->
    LInv regs t4v t0v -> getr regs 13 = Z_to_bv 64 (wpl * i) -> getr regs 14 = Z_to_bv 64 i ->
    getr regs 9 = mx -> (bv_unsigned mx <= maxval)%Z ->
    exists regs' (mx' : word),
      msteps SEGS (mkst regs (rl dVL_24b70 0x24ce0) MC rom) (mkst regs' (rl dVL_24b70 0x24e48) MC rom)
      /\ getr regs' 9 = mx' /\ (bv_unsigned mx' <= maxval)%Z
      /\ LInv regs' t4v t0v /\ getr regs' 13 = Z_to_bv 64 (wpl * i) /\ getr regs' 14 = Z_to_bv 64 i
      /\ regs_agree (fun r : reg => In r [9; 18; 19; 20; 21; 22]%list) regs regs'.
  Proof.
    intros regs t4v t0v i mx Hd1 Hi HL H13 H14 H9 Hmx. nodisj.
    destruct (mi_rowP regs t4v t0v i mx Hi HL H13 H14 H9) as (r1 & S1 & HL1 & Q13 & Q14 & Q9 & Q18 & AG1).
    assert (S2 : exists r2 (mx' : word),
      msteps SEGS (mkst r1 (rl dVL_24b70 0x24d14) MC rom) (mkst r2 (rl dVL_24b70 0x24e48) MC rom)
      /\ getr r2 9 = mx' /\ (bv_unsigned mx' <= maxval)%Z
      /\ regs_agree (fun r : reg => In r [9; 19; 20; 21; 22]%list) r1 r2).
    { destruct Hd as [Hd0|[Hd2|[Hd4|Hd8]]]; [lia| | |].
      - exact (mi_R2 r1 t4v t0v i mx Hd2 Hi HL1 Q13 Q18 Q9 Hmx).
      - exact (mi_R4 r1 t4v t0v i mx Hd4 Hi HL1 Q13 Q18 Q9 Hmx).
      - exact (mi_R8 r1 t4v t0v i mx Hd8 Hi HL1 Q13 Q18 Q9 Hmx). }
    destruct S2 as (r2 & mx2 & S2 & T9 & Hmx2 & AG2).
    exists r2, mx2. split; [|split; [exact T9 | split; [exact Hmx2 | split; [|split; [|split]]]]].
    - eapply msteps_trans; [exact S1 | exact S2].
    - unfold LInv. rewrite !AG2 by notin_list. exact HL1.
    - rewrite AG2 by notin_list. exact Q13.
    - rewrite AG2 by notin_list. exact Q14.
    - eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
  Qed.

  (* [comment removed for export] *)
  Lemma mi_loop : forall k regs t4v t0v i (mx : word), (d <> 1)%Z ->
    (Z.of_nat k = h - 1 - i)%Z -> (0 <= i)%Z ->
    LInv regs t4v t0v -> getr regs 13 = Z_to_bv 64 (wpl * i) -> getr regs 14 = Z_to_bv 64 i ->
    getr regs 9 = mx -> (bv_unsigned mx <= maxval)%Z ->
    exists regs' (mx' : word),
      msteps SEGS (mkst regs (rl dVL_24b70 0x24ce0) MC rom) (mkst regs' (rl dVL_24b70 0x24ea0) MC rom)
      /\ getr regs' 9 = mx' /\ (bv_unsigned mx' <= maxval)%Z
      /\ getr regs' 2 = Z_to_bv 64 (sp - 80) /\ getr regs' 7 = Z_to_bv 64 pmax
      /\ regs_agree (fun r : reg => In r [9; 13; 14; 18; 19; 20; 21; 22]%list) regs regs'.
  Proof.
    nodisj. pose proof wplh_bound as Hwh. pose proof wpl_bounds as (Hwpl1 & _ & _).
    induction k as [|k IH]; intros regs t4v t0v i mx Hd1 Hk Hi HL H13 H14 H9 Hmx;
      destruct (mi_row regs t4v t0v i mx Hd1 ltac:(lia) HL H13 H14 H9 Hmx)
        as (r1 & mx1 & S1 & R9 & Hmx1 & HL1 & R13 & R14 & AG1);
      pose proof HL1 as (I2 & I10 & I12 & I11 & I15 & I16 & I17 & I5 & I6 & I28 & I29 & I30 & I31 & I7 & I8);
      pose proof (row_in_raster i ltac:(lia)) as Hrow.
    - (* [comment removed for export] *)
      destruct (c_eq (v_xor mx1 t4v) t0v) eqn:Hc.
      + eexists. exists mx1. split.
        * eapply msteps_trans; [exact S1|].
          sn F_24e48 D_24e48.                               (* [comment removed for export] *)
          stepb_tk F_24e4c D_24e4c ltac:(pin; exact Hc).    (* [comment removed for export] *)
          apply mst_refl.
        * repeat split; gres; pin; try reflexivity; try assumption.
          eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
      + eexists. exists mx1. split.
        * eapply msteps_trans; [exact S1|].
          sn F_24e48 D_24e48.                               (* [comment removed for export] *)
          stepb_ft F_24e4c D_24e4c ltac:(pin; exact Hc).    (* [comment removed for export] *)
          zvw F_24e50 D_24e50 (Z_to_bv 64 (i + 1)).         (* [comment removed for export] *)
          sn F_24e54 D_24e54.                               (* [comment removed for export] *)
          fixv (Z_to_bv 64 (wpl * (i + 1))) ltac:(rewrite zbv_addw_small by lia; f_equal; lia).
          stepb_ft F_24e58 D_24e58 ltac:(condZ).            (* [comment removed for export] *)
          sn F_24e5c D_24e5c.                               (* [comment removed for export] *)
          apply mst_refl.
        * repeat split; gres; pin; try reflexivity; try assumption.
          eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - destruct (c_eq (v_xor mx1 t4v) t0v) eqn:Hc.
      + (* [comment removed for export] *)
        eexists. exists mx1. split.
        * eapply msteps_trans; [exact S1|].
          sn F_24e48 D_24e48.                               (* [comment removed for export] *)
          stepb_tk F_24e4c D_24e4c ltac:(pin; exact Hc).    (* [comment removed for export] *)
          apply mst_refl.
        * repeat split; gres; pin; try reflexivity; try assumption.
          eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
      + assert (S2 : exists r2, msteps SEGS (mkst r1 (rl dVL_24b70 0x24e48) MC rom) (mkst r2 (rl dVL_24b70 0x24ce0) MC rom)
                                /\ LInv r2 t4v t0v /\ getr r2 13 = Z_to_bv 64 (wpl * (i + 1)) /\ getr r2 14 = Z_to_bv 64 (i + 1)
                                /\ getr r2 9 = mx1
                                /\ regs_agree (fun r : reg => In r [13; 14; 18]%list) r1 r2).
        { eexists. split; [|split].
          - sn F_24e48 D_24e48.                             (* [comment removed for export] *)
            stepb_ft F_24e4c D_24e4c ltac:(pin; exact Hc).  (* [comment removed for export] *)
            zvw F_24e50 D_24e50 (Z_to_bv 64 (i + 1)).       (* [comment removed for export] *)
            sn F_24e54 D_24e54.                             (* [comment removed for export] *)
            fixv (Z_to_bv 64 (wpl * (i + 1))) ltac:(rewrite zbv_addw_small by lia; f_equal; lia).
            stepb_tk F_24e58 D_24e58 ltac:(condZ).          (* [comment removed for export] *)
            apply mst_refl.
          - unfold LInv. repeat split; gres; pin; reflexivity.
          - repeat split; gres; pin; try reflexivity. solve_regs_agree. }
        destruct S2 as (r2 & S2 & HL2 & Q13 & Q14 & Q9 & AG2).
        destruct (IH r2 t4v t0v (i + 1)%Z mx1 Hd1 ltac:(lia) ltac:(lia) HL2 Q13 Q14 Q9 Hmx1)
          as (r3 & mx3 & S3 & T9 & Hmx3 & T2 & T7 & AG3).
        exists r3, mx3. split; [|split; [exact T9 | split; [exact Hmx3 | split; [exact T2 | split; [exact T7|]]]]].
        * eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2 | exact S3].
        * eapply regs_agree_trans; [regs_agree_weaken AG1|].
          eapply regs_agree_trans; [regs_agree_weaken AG2 | exact AG3].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition MF (Mx : word -> option byte) (mx : word) : word -> option byte :=
    wbytes Mx (Z_to_bv 64 pmax) (word_to_le_bytes 4 mx).

  (* [comment removed for export] *)
  Lemma mi_F : forall regs Mx (mx : word), mem_grows M Mx ->
    getr regs 7 = Z_to_bv 64 pmax -> getr regs 9 = mx ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_24b70 0x24ea0) Mx rom) (mkst regs' (rl dVL_24b70 0x24ea8) (MF Mx mx) rom)
      /\ getr regs' 10 = Z_to_bv 64 0
      /\ regs_agree (fun r : reg => In r [10]%list) regs regs'.
  Proof.
    intros regs Mx mx HG H7 H9. nodisj. clear RR.
    eexists. split.
    - sn F_24ea0 D_24ea0.                                   (* [comment removed for export] *)
      stepST F_24ea4 D_24ea4 (Z_to_bv 64 pmax) mx ltac:(apply sok_pmax; exact HG).   (* [comment removed for export] *)
      fold (MF Mx mx).
      apply mst_refl.
    - split; [gres; reflexivity | solve_regs_agree].
  Qed.

  (* [comment removed for export] *)
  Definition FrameSame (Mx : word -> option byte) : Prop :=
    forall x : word, (sp - 64 <= bv_unsigned x < sp)%Z -> Mx x = MA x.

  Lemma FS_wbytes : forall Mx (a : Z) bs, FrameSame Mx ->
    (0 <= a)%Z -> (a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
    (a + Z.of_nat (length bs) <= sp - 64 \/ sp <= a)%Z ->
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

  Lemma FS_rdn : forall Mx k (n : nat) bs,
    FrameSame Mx -> (Z.of_nat n <= k <= 64)%Z ->
    rdn SEGS MA (Z_to_bv 64 (sp - k)) n = Some bs -> rdn SEGS Mx (Z_to_bv 64 (sp - k)) n = Some bs.
  Proof.
    intros Mx k n bs HF Hk HM. nodisj. clear RR. rewrite <- HM. apply rdn_ext; rewrite u_Z2bv by lia; [lia|].
    intros x Hx. apply HF. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mi_E : forall regs Mx,
    FrameSame Mx -> getr regs 2 = Z_to_bv 64 (sp - 80) ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_24b70 0x24ea8) Mx rom) (mkst regs' ra Mx rom)
      /\ getr regs' 10 = getr regs 10 /\ getr regs' 1 = ra /\ getr regs' 2 = Z_to_bv 64 sp
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v
      /\ regs_agree (fun x : reg => In x [1; 2; 8; 9; 18; 19; 20; 21; 22]%list) regs regs'.
  Proof.
    intros regs Mx HF H2. nodisj. clear RR.
    pose proof (u64_range ra). pose proof (u64_range s0v). pose proof (u64_range s1v). pose proof (u64_range s2v).
    pose proof (u64_range s3v). pose proof (u64_range s4v). pose proof (u64_range s5v). pose proof (u64_range s6v).
    eexists. split.
    - stepLD F_24ea8 D_24ea8 (word_to_le_bytes 8 ra) ra
        ltac:(rdn_addr (sp - 8)%Z; apply (FS_rdn Mx 8 8); [exact HF | cbn; lia | unfold MA; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_24eac D_24eac (word_to_le_bytes 8 s0v) s0v
        ltac:(rdn_addr (sp - 16)%Z; apply (FS_rdn Mx 16 8); [exact HF | cbn; lia | unfold MA; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_24eb0 D_24eb0 (word_to_le_bytes 8 s1v) s1v
        ltac:(rdn_addr (sp - 24)%Z; apply (FS_rdn Mx 24 8); [exact HF | cbn; lia | unfold MA; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_24eb4 D_24eb4 (word_to_le_bytes 8 s2v) s2v
        ltac:(rdn_addr (sp - 32)%Z; apply (FS_rdn Mx 32 8); [exact HF | cbn; lia | unfold MA; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_24eb8 D_24eb8 (word_to_le_bytes 8 s3v) s3v
        ltac:(rdn_addr (sp - 40)%Z; apply (FS_rdn Mx 40 8); [exact HF | cbn; lia | unfold MA; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_24ebc D_24ebc (word_to_le_bytes 8 s4v) s4v
        ltac:(rdn_addr (sp - 48)%Z; apply (FS_rdn Mx 48 8); [exact HF | cbn; lia | unfold MA; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_24ec0 D_24ec0 (word_to_le_bytes 8 s5v) s5v
        ltac:(rdn_addr (sp - 56)%Z; apply (FS_rdn Mx 56 8); [exact HF | cbn; lia | unfold MA; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_24ec4 D_24ec4 (word_to_le_bytes 8 s6v) s6v
        ltac:(rdn_addr (sp - 64)%Z; apply (FS_rdn Mx 64 8); [exact HF | cbn; lia | unfold MA; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      zvw F_24ec8 D_24ec8 (Z_to_bv 64 sp).                  (* [comment removed for export] *)
      stepret F_24ecc D_24ecc ra ltac:(reflexivity).        (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mi_run248 : forall regs, (d <> 1)%Z ->
    getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 sp ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v ->
    getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v -> getr regs 22 = s6v ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 pmax ->
    exists regs' (mx : word),
      msteps SEGS (mkst regs (rl dVL_24b70 0x24b70) M rom) (mkst regs' ra (MF MC mx) rom)
      /\ (bv_unsigned mx <= maxval)%Z
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 sp
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v
      /\ regs_agree (fun x : reg => In x [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs Hd1 H1 H2 H8 H9 H18 H19 H20 H21 H22 H10 H11.
    pose proof maxval_ge as Hmv.
    destruct (mi_A regs H1 H2 H8 H9 H18 H19 H20 H21 H22 H10 H11) as (r1 & S1 & A2 & A9 & A18 & AG1).
    destruct (mi_B r1 A2 A9) as (r2 & S2 & B2 & B10 & B8 & B11 & B12 & AG2).
    pose proof (AG2 18 ltac:(notin_list)) as B18. rewrite A18 in B18.
    destruct (mi_D r2 Hd1 B2 B10 B8 B11 B12 B18) as (r3 & t4v & t0v & S3 & HL3 & C13 & C14 & C9 & AG3).
    destruct (mi_loop (Z.to_nat (h - 1)) r3 t4v t0v 0 (Z_to_bv 64 0) Hd1 ltac:(lia) ltac:(lia) HL3 C13 C14 C9
                ltac:(change (bv_unsigned (Z_to_bv 64 0)) with 0%Z; lia))
      as (r4 & mx & S4 & D9 & Hmx & D2 & D7 & AG4).
    destruct (mi_F r4 MC mx MC_grows D7 D9) as (r5 & S5 & E10 & AG5).
    pose proof (AG5 2 ltac:(notin_list)) as E2. rewrite D2 in E2.
    destruct (mi_E r5 (MF MC mx) (FS_MF MC mx FS_MC) E2) as (r6 & S6 & G10 & G1 & G2 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & AG6).
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
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes MC
      (Z_to_bv 64 (sp - 88)) (word_to_le_bytes 8 (rl dVL_24b70 0x24c14)))
      (Z_to_bv 64 (sp - 96)) (word_to_le_bytes 8 (Z_to_bv 64 wpl)))
      (Z_to_bv 64 (sp - 104)) (word_to_le_bytes 8 (Z_to_bv 64 pix)))
      (Z_to_bv 64 (sp - 112)) (word_to_le_bytes 8 (Z_to_bv 64 pmax)))
      (Z_to_bv 64 (sp - 120)) (word_to_le_bytes 8 s3v))
      (Z_to_bv 64 (sp - 128)) (word_to_le_bytes 8 s4v).
  Definition MZ1 : word -> option byte := wbytes MZ (Z_to_bv 64 (sp - 80)) (word_to_le_bytes 4 (Z_to_bv 64 1)).
  Definition MZ0 : word -> option byte := wbytes MZ1 (Z_to_bv 64 (sp - 80)) (word_to_le_bytes 4 (Z_to_bv 64 0)).

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
    getr regs 2 = Z_to_bv 64 (sp - 80) -> getr regs 8 = Z_to_bv 64 wpl -> getr regs 11 = Z_to_bv 64 d ->
    getr regs 12 = Z_to_bv 64 1 -> getr regs 9 = Z_to_bv 64 pix -> getr regs 18 = Z_to_bv 64 pmax ->
    getr regs 19 = s3v -> getr regs 20 = s4v ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_24b70 0x24c04) MC rom) (mkst regs' (rl dVL_24ed4 0x24f50) MZ1 rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 128) /\ getr regs' 8 = Z_to_bv 64 (sp - 80) /\ getr regs' 19 = Z_to_bv 64 pix
      /\ getr regs' 20 = Z_to_bv 64 w /\ getr regs' 9 = Z_to_bv 64 h /\ getr regs' 18 = Z_to_bv 64 wpl
      /\ getr regs' 10 = Z_to_bv 64 data
      /\ regs_agree (fun r : reg => In r [1; 2; 8; 9; 10; 11; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs Hd1 H2 H8 H11 H12 H9 H18 H19 H20. clear RR.
    pose proof wpl_bounds as (Hwpl1 & _ & _).
    pose proof slots_al4 as (A68 & A72 & A76 & A80).
    pose proof (u64_range s3v). pose proof (u64_range s4v).
    eexists. split.
    - stepb_ft F_24c04 D_24c04 ltac:(condZ).                (* [comment removed for export] *)
      zvw F_24c08 D_24c08 (Z_to_bv 64 (sp - 80)).          (* [comment removed for export] *)
      zvw F_24c0c D_24c0c (Z_to_bv 64 pix).                 (* [comment removed for export] *)
      sn F_24c10 D_24c10.                                   (* [comment removed for export] *)
      (* [comment removed for export] *)
      zvw F_24ed4 D_24ed4 (Z_to_bv 64 (sp - 128)).          (* [comment removed for export] *)
      stz F_24ed8 D_24ed8 88%Z (rl dVL_24b70 0x24c14).          (* [comment removed for export] *)
      stz F_24edc D_24edc 96%Z (Z_to_bv 64 wpl).             (* [comment removed for export] *)
      stz F_24ee0 D_24ee0 104%Z (Z_to_bv 64 pix).            (* [comment removed for export] *)
      stz F_24ee4 D_24ee4 112%Z (Z_to_bv 64 pmax).           (* [comment removed for export] *)
      stz F_24ee8 D_24ee8 120%Z s3v.                          (* [comment removed for export] *)
      stz F_24eec D_24eec 128%Z s4v.                          (* [comment removed for export] *)
      fold MZ.
      stepb_ft F_24ef0 D_24ef0 ltac:(condZ).                (* [comment removed for export] *)
      zvw F_24ef4 D_24ef4 (Z_to_bv 64 (sp - 80)).          (* [comment removed for export] *)
      zvw F_24ef8 D_24ef8 (Z_to_bv 64 pix).                 (* [comment removed for export] *)
      zand F_24efc D_24efc andi_3 A80.                      (* [comment removed for export] *)
      stepb_ft F_24f00 D_24f00 ltac:(condR).                (* [comment removed for export] *)
      sn F_24f04 D_24f04.                                   (* [comment removed for export] *)
      stz F_24f08 D_24f08 80%Z (Z_to_bv 64 1).                (* [comment removed for export] *)
      fold MZ1.
      stepb_ft F_24f0c D_24f0c ltac:(condZ).                (* [comment removed for export] *)
      zvw F_24f10 D_24f10 (Z_to_bv 64 pix).                 (* [comment removed for export] *)
      sn F_24f14 D_24f14.                                   (* [comment removed for export] *)
      stepb_ft F_24230 D_24230 ltac:(condZ).                (* [comment removed for export] *)
      zand F_24234 D_24234 andi_7 Hpixal.                   (* [comment removed for export] *)
      stepb_ft F_24238 D_24238 ltac:(condR).                (* [comment removed for export] *)
      stepLD F_2423c D_2423c (Z_to_le_bytes 4 w) (Z_to_bv 64 w)
        ltac:(unfold v_addi; unorm; rewrite ?Z.add_0_r; peelz; exact Cw)
        ltac:(apply lez4; lia).                             (* [comment removed for export] *)
      rewrite (v_lw_small w) by lia.
      stepretF F_24240 D_24240 F_24f18.
      zvw F_24f18 D_24f18 (Z_to_bv 64 w).                   (* [comment removed for export] *)
      zvw F_24f1c D_24f1c (Z_to_bv 64 pix).                 (* [comment removed for export] *)
      sn F_24f20 D_24f20.                                   (* [comment removed for export] *)
      stepb_ft F_24198 D_24198 ltac:(condZ).                (* [comment removed for export] *)
      zand F_2419c D_2419c andi_7 Hpixal.                   (* [comment removed for export] *)
      stepb_ft F_241a0 D_241a0 ltac:(condR).                (* [comment removed for export] *)
      ldpixz F_241a4 D_241a4 d Cd.                          (* [comment removed for export] *)
      stepretF F_241a8 D_241a8 F_24f24.
      stepiv F_24f24 D_24f24 (Z_to_bv 64 w)
        ltac:(gres; pin; imm_norm; rewrite zbv_mul; rewrite Hd1; f_equal; lia).   (* [comment removed for export] *)
      sn F_24f28 D_24f28.                                   (* [comment removed for export] *)
      fixv (Z_to_bv 64 w) ltac:(rewrite Hd1; rewrite zbv_mulw_small by lia; f_equal; lia).
      stepb_ft F_24f2c D_24f2c ltac:(condR).                (* [comment removed for export] *)
      zvw F_24f30 D_24f30 (Z_to_bv 64 pix).                 (* [comment removed for export] *)
      sn F_24f34 D_24f34.                                   (* [comment removed for export] *)
      stepb_ft F_2414c D_2414c ltac:(condZ).                (* [comment removed for export] *)
      zand F_24150 D_24150 andi_7 Hpixal.                   (* [comment removed for export] *)
      stepb_ft F_24154 D_24154 ltac:(condR).                (* [comment removed for export] *)
      ldpixz F_24158 D_24158 h Ch.                          (* [comment removed for export] *)
      stepretF F_2415c D_2415c F_24f38.
      zvw F_24f38 D_24f38 (Z_to_bv 64 h).                   (* [comment removed for export] *)
      zvw F_24f3c D_24f3c (Z_to_bv 64 pix).                 (* [comment removed for export] *)
      sn F_24f40 D_24f40.                                   (* [comment removed for export] *)
      stepb_ft F_23ce4 D_23ce4 ltac:(condZ).                (* [comment removed for export] *)
      zand F_23ce8 D_23ce8 andi_7 Hpixal.                   (* [comment removed for export] *)
      stepb_ft F_23cec D_23cec ltac:(condR).                (* [comment removed for export] *)
      ldpixz F_23cf0 D_23cf0 wpl Cwpl.                      (* [comment removed for export] *)
      stepretF F_23cf4 D_23cf4 F_24f44.
      zvw F_24f44 D_24f44 (Z_to_bv 64 wpl).                 (* [comment removed for export] *)
      zvw F_24f48 D_24f48 (Z_to_bv 64 pix).                 (* [comment removed for export] *)
      sn F_24f4c D_24f4c.                                   (* [comment removed for export] *)
      stepb_ft F_241e4 D_241e4 ltac:(condZ).                (* [comment removed for export] *)
      zand F_241e8 D_241e8 andi_7 Hpixal.                   (* [comment removed for export] *)
      stepb_ft F_241ec D_241ec ltac:(condR).                (* [comment removed for export] *)
      stepLD F_241f0 D_241f0 (Z_to_le_bytes 8 data) (Z_to_bv 64 data)
        ltac:(unfold v_addi; unorm; peelz; exact Cdata)
        ltac:(apply lez8; lia).                             (* [comment removed for export] *)
      stepretF F_241f4 D_241f4 F_24f50.
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
    getr regs 2 = Z_to_bv 64 (sp - 128) /\ getr regs 10 = Z_to_bv 64 data /\ getr regs 18 = Z_to_bv 64 wpl /\
    getr regs 13 = Z_to_bv 64 w /\ getr regs 14 = Z_to_bv 64 (w mod 32) /\ getr regs 15 = Z_to_bv 64 32 /\
    getr regs 16 = Z_to_bv 64 0 /\ getr regs 17 = Z_to_bv 64 1 /\ getr regs 5 = Z_to_bv 64 (32 - w mod 32) /\
    getr regs 6 = Z_to_bv 64 (w / 32) /\ getr regs 7 = Z_to_bv 64 5 /\ getr regs 9 = Z_to_bv 64 h /\
    getr regs 8 = Z_to_bv 64 (sp - 80) /\ getr regs 19 = Z_to_bv 64 pix.

  (* [comment removed for export] *)
  Lemma mi_Z2 : forall regs, (d = 1)%Z ->
    getr regs 2 = Z_to_bv 64 (sp - 128) -> getr regs 8 = Z_to_bv 64 (sp - 80) -> getr regs 19 = Z_to_bv 64 pix ->
    getr regs 20 = Z_to_bv 64 w -> getr regs 9 = Z_to_bv 64 h -> getr regs 18 = Z_to_bv 64 wpl ->
    getr regs 10 = Z_to_bv 64 data ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_24ed4 0x24f50) MZ1 rom) (mkst regs' (rl dVL_24ed4 0x24f88) MZ1 rom)
      /\ ZInv regs' /\ getr regs' 11 = Z_to_bv 64 (wpl * 0) /\ getr regs' 12 = Z_to_bv 64 0
      /\ regs_agree (fun r : reg => In r [5; 6; 7; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
  Proof.
    intros regs Hd1 H2 H8 H19 H20 H9 H18 H10. clear RR. nodisj.
    pose proof (fw_facts Hd1) as (Hfw & Hmod & Hdm & _ & _).
    eexists. split; [|split; [|split; [|split]]].
    - stepb_ft F_24f50 D_24f50 ltac:(condZ).                (* [comment removed for export] *)
      sn F_24f54 D_24f54.                                   (* [comment removed for export] *)
      fixv (Z_to_bv 64 (wpl * 0)) ltac:(f_equal; lia).
      sn F_24f58 D_24f58.                                   (* [comment removed for export] *)
      zvw F_24f5c D_24f5c (Z_to_bv 64 w).                   (* [comment removed for export] *)
      sn F_24f60 D_24f60.                                   (* [comment removed for export] *)
      fixv (Z_to_bv 64 0) ltac:(rewrite zbv_sraiw_small by lia; f_equal; apply Z.div_small;
                                change (2 ^ 31)%Z with 2147483648%Z; lia).
      stepiv F_24f64 D_24f64 (Z_to_bv 64 (w mod 32))
        ltac:(gres; pin; imm_norm; rewrite andi_31; unorm; reflexivity).   (* [comment removed for export] *)
      sn F_24f68 D_24f68.                                   (* [comment removed for export] *)
      zand F_24f6c D_24f6c andi_3 Hdal.                     (* [comment removed for export] *)
      sn F_24f70 D_24f70.                                   (* [comment removed for export] *)
      fixv (Z_to_bv 64 1) ltac:(apply zbv_snez; lia).
      sn F_24f74 D_24f74.                                   (* [comment removed for export] *)
      zvw F_24f78 D_24f78 (Z_to_bv 64 (32 - w mod 32)).    (* [comment removed for export] *)
      zvw F_24f7c D_24f7c (Z_to_bv 64 w).                   (* [comment removed for export] *)
      sn F_24f80 D_24f80.                                   (* [comment removed for export] *)
      fixv (Z_to_bv 64 (w / 32)) ltac:(rewrite zbv_sraiw_small by lia; change (2 ^ 5)%Z with 32%Z; reflexivity).
      sn F_24f84 D_24f84.                                   (* [comment removed for export] *)
      apply mst_refl.
    - unfold ZInv. repeat split; gres; pin; reflexivity.
    - gres. reflexivity.
    - gres. reflexivity.
    - solve_regs_agree.
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
    ZInv regs -> getr regs 11 = Z_to_bv 64 (wpl * i) -> getr regs 12 = Z_to_bv 64 i ->
    getr regs 28 = Z_to_bv 64 (data + 4 * wpl * i + 4 * q) -> getr regs 29 = Z_to_bv 64 (data + 4 * wpl * i + 4 * q) ->
    getr regs 30 = Z_to_bv 64 (w / 32 - q) ->
    exists regs',
      regs_agree (fun r : reg => In r [28; 29; 30; 31]%list) regs regs'
      /\ ( (msteps SEGS (mkst regs (rl dVL_24ed4 0x24fcc) MZ1 rom) (mkst regs' (rl dVL_24ed4 0x24ff0) MZ1 rom)
            /\ getr regs' 28 = Z_to_bv 64 (data + 4 * wpl * i + 4 * (w / 32)))
           \/ msteps SEGS (mkst regs (rl dVL_24ed4 0x24fcc) MZ1 rom) (mkst regs' (rl dVL_24ed4 0x25090) MZ1 rom) ).
  Proof.
    nodisj. intros k. pose proof (fun Hd1 => fw_facts Hd1) as HF.
    induction k as [|k IH]; intros regs i q Hd1 Hi Hk Hq HZ H11 H12 H28 H29 H30;
      destruct (HF Hd1) as (Hfw & Hmod & Hdm & _ & _);
      pose proof (row_in_raster i Hi) as Hrow;
      destruct (word_at_z i q Hi ltac:(lia)) as (bs & Hbs & Lbs);
      pose proof HZ as (I2 & I10 & I18 & I13 & I14 & I15 & I16 & I17 & I5 & I6 & I7 & I9 & I8 & I19);
      (* [comment removed for export] *)
      (assert (S0 : exists r0 (v : word), msteps SEGS (mkst regs (rl dVL_24ed4 0x24fcc) MZ1 rom) (mkst r0 (rl dVL_24ed4 0x24fe0) MZ1 rom)
                 /\ getr r0 31 = v /\ getr r0 29 = Z_to_bv 64 (data + 4 * wpl * i + 4 * (q + 1))
                 /\ regs_agree (fun r : reg => In r [29; 31]%list) regs r0)
         by (eexists; eexists; split;
             [ zvw F_24fcc D_24fcc (Z_to_bv 64 (data + 4 * wpl * i + 4 * (q + 1)));   (* [comment removed for export] *)
               stepb_ft F_24fd0 D_24fd0 ltac:(condZ);           (* [comment removed for export] *)
               stepb_ft F_24fd4 D_24fd4 ltac:(condE);           (* [comment removed for export] *)
               stepb_ft F_24fd8 D_24fd8 ltac:(condR);           (* [comment removed for export] *)
               stepLD F_24fdc D_24fdc bs (Z_to_bv 64 (bytes_le_to_Z bs))
                 ltac:(rdn_addr (data + 4 * wpl * i + 4 * q)%Z; exact Hbs)
                 ltac:(symmetry; apply u_lez4; exact Lbs);     (* [comment removed for export] *)
               apply mst_refl
             | split; [gres; reflexivity | split; [gres; reflexivity | solve_regs_agree]] ]));
      destruct S0 as (r0 & v & S0 & P31 & P29 & AG0);
      pose proof (AG0 28 ltac:(notin_list)) as P28; rewrite H28 in P28;
      pose proof (AG0 30 ltac:(notin_list)) as P30; rewrite H30 in P30;
      destruct (c_eq v (Z_to_bv 64 0)) eqn:Hc.
    - (* [comment removed for export] *)
      eexists. split; [|left; split].
      2:{ eapply msteps_trans; [exact S0|].
          stepb_ft F_24fe0 D_24fe0 ltac:(pin; exact Hc).    (* [comment removed for export] *)
          zvw F_24fe4 D_24fe4 (Z_to_bv 64 (w / 32 - q - 1)). (* [comment removed for export] *)
          zvw F_24fe8 D_24fe8 (Z_to_bv 64 (data + 4 * wpl * i + 4 * (w / 32))).   (* [comment removed for export] *)
          stepb_ft F_24fec D_24fec ltac:(condZ).            (* [comment removed for export] *)
          apply mst_refl. }
      + eapply regs_agree_trans; [regs_agree_weaken AG0|]. solve_regs_agree.
      + gres. reflexivity.
    - (* [comment removed for export] *)
      eexists. split; [|right].
      2:{ eapply msteps_trans; [exact S0|].
          stepb_tk F_24fe0 D_24fe0 ltac:(pin; exact Hc).    (* [comment removed for export] *)
          apply mst_refl. }
      regs_agree_weaken AG0.
    - (* [comment removed for export] *)
      assert (S1 : exists r1, msteps SEGS (mkst r0 (rl dVL_24ed4 0x24fe0) MZ1 rom) (mkst r1 (rl dVL_24ed4 0x24fcc) MZ1 rom)
                              /\ ZInv r1 /\ getr r1 11 = Z_to_bv 64 (wpl * i) /\ getr r1 12 = Z_to_bv 64 i
                              /\ getr r1 28 = Z_to_bv 64 (data + 4 * wpl * i + 4 * (q + 1))
                              /\ getr r1 29 = Z_to_bv 64 (data + 4 * wpl * i + 4 * (q + 1))
                              /\ getr r1 30 = Z_to_bv 64 (w / 32 - (q + 1))
                              /\ regs_agree (fun r : reg => In r [28; 30]%list) r0 r1).
      { eexists. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
        - stepb_ft F_24fe0 D_24fe0 ltac:(pin; exact Hc).    (* [comment removed for export] *)
          zvw F_24fe4 D_24fe4 (Z_to_bv 64 (w / 32 - (q + 1))).   (* [comment removed for export] *)
          zvw F_24fe8 D_24fe8 (Z_to_bv 64 (data + 4 * wpl * i + 4 * (q + 1))).   (* [comment removed for export] *)
          stepb_tk F_24fec D_24fec ltac:(condZ).            (* [comment removed for export] *)
          apply mst_refl.
        - unfold ZInv. repeat split; gres; rewrite ?AG0 by notin_list; pin; reflexivity.
        - gres. rewrite AG0 by notin_list. exact H11.
        - gres. rewrite AG0 by notin_list. exact H12.
        - gres. reflexivity.
        - gres. exact P29.
        - gres. reflexivity.
        - solve_regs_agree. }
      destruct S1 as (r1 & S1 & HZ1 & Q11 & Q12 & Q28 & Q29 & Q30 & AG1).
      destruct (IH r1 i (q + 1)%Z Hd1 Hi ltac:(lia) ltac:(lia) HZ1 Q11 Q12 Q28 Q29 Q30) as (r2 & AG2 & POST).
      exists r2. split; [eapply regs_agree_trans; [regs_agree_weaken AG0 | eapply regs_agree_trans; [regs_agree_weaken AG1 | exact AG2]]|].
      destruct POST as [[S2 R28]|S2].
      + left. split; [|exact R28]. eapply msteps_trans; [exact S0|]. eapply msteps_trans; [exact S1 | exact S2].
      + right. eapply msteps_trans; [exact S0|]. eapply msteps_trans; [exact S1 | exact S2].
    - (* [comment removed for export] *)
      eexists. split; [|right].
      2:{ eapply msteps_trans; [exact S0|].
          stepb_tk F_24fe0 D_24fe0 ltac:(pin; exact Hc).    (* [comment removed for export] *)
          apply mst_refl. }
      regs_agree_weaken AG0.
  Qed.

  (* [comment removed for export] *)
  Lemma mi_Zrow : forall regs i, (d = 1)%Z -> (0 <= i < h)%Z ->
    ZInv regs -> getr regs 11 = Z_to_bv 64 (wpl * i) -> getr regs 12 = Z_to_bv 64 i ->
    exists regs',
      regs_agree (fun r : reg => In r [28; 29; 30; 31]%list) regs regs'
      /\ ( msteps SEGS (mkst regs (rl dVL_24ed4 0x24f88) MZ1 rom) (mkst regs' (rl dVL_24ed4 0x2500c) MZ1 rom)
           \/ msteps SEGS (mkst regs (rl dVL_24ed4 0x24f88) MZ1 rom) (mkst regs' (rl dVL_24ed4 0x25090) MZ1 rom) ).
  Proof.
    intros regs i Hd1 Hi HZ H11 H12. nodisj.
    pose proof (fw_facts Hd1) as (Hfw & Hmod & Hdm & Htail & Hsmall).
    pose proof (row_in_raster i Hi) as Hrow. pose proof wplh_bound as Hwh.
    pose proof HZ as (I2 & I10 & I18 & I13 & I14 & I15 & I16 & I17 & I5 & I6 & I7 & I9 & I8 & I19).
    (* [comment removed for export] *)
    assert (S1 : exists r1, msteps SEGS (mkst regs (rl dVL_24ed4 0x24f88) MZ1 rom) (mkst r1 (rl dVL_24ed4 0x24fbc) MZ1 rom)
                            /\ ZInv r1 /\ getr r1 11 = Z_to_bv 64 (wpl * i) /\ getr r1 12 = Z_to_bv 64 i
                            /\ getr r1 28 = Z_to_bv 64 (data + 4 * wpl * i + 4 * 0)
                            /\ regs_agree (fun r : reg => In r [28; 29; 30]%list) regs r1).
    { eexists. split; [|split; [|split; [|split; [|split]]]].
      - zvw F_24f88 D_24f88 (Z_to_bv 64 (wpl * i)).         (* [comment removed for export] *)
        sn F_24f8c D_24f8c.                                 (* [comment removed for export] *)
        fixv (Z_to_bv 64 (wpl * i)) ltac:(rewrite zbv_mulw_small by lia; f_equal; lia).
        stepb_ft F_24f90 D_24f90 ltac:(condR).              (* [comment removed for export] *)
        zvw F_24f94 D_24f94 (Z_to_bv 64 (wpl * i)).         (* [comment removed for export] *)
        zvs F_24f98 D_24f98 (Z_to_bv 64 (4 * wpl * i)).     (* [comment removed for export] *)
        zvw F_24f9c D_24f9c (Z_to_bv 64 (data + 4 * wpl * i + 4 * 0)).   (* [comment removed for export] *)
        stepiv F_24fa0 D_24fa0 (Z_to_bv 64 0)
          ltac:(gres; pin; imm_norm; apply zbv_seqz_nz; lia).   (* [comment removed for export] *)
        stepb_ft F_24fa4 D_24fa4 ltac:(condR).              (* [comment removed for export] *)
        sn F_24fa8 D_24fa8.                                 (* [comment removed for export] *)
        fixv (Z_to_bv 64 0) ltac:(apply zbv_sltu_ge; lia).
        sn F_24fac D_24fac.                                 (* [comment removed for export] *)
        fixv (Z_to_bv 64 0) ltac:(apply zbv_slti0; lia).
        sn F_24fb0 D_24fb0.                                 (* [comment removed for export] *)
        sn F_24fb4 D_24fb4.                                 (* [comment removed for export] *)
        stepb_ft F_24fb8 D_24fb8 ltac:(condR).              (* [comment removed for export] *)
        apply mst_refl.
      - unfold ZInv. repeat split; gres; pin; reflexivity.
      - gres. exact H11.
      - gres. exact H12.
      - gres. reflexivity.
      - solve_regs_agree. }
    destruct S1 as (r1 & S1 & HZ1 & Q11 & Q12 & Q28 & AG1).
    pose proof HZ1 as (J2 & J10 & J18 & J13 & J14 & J15 & J16 & J17 & J5 & J6 & J7 & J9 & J8 & J19).
    (* [comment removed for export] *)
    assert (S2 : exists r2, regs_agree (fun r : reg => In r [28; 29; 30; 31]%list) r1 r2
              /\ ( (msteps SEGS (mkst r1 (rl dVL_24ed4 0x24fbc) MZ1 rom) (mkst r2 (rl dVL_24ed4 0x24ff0) MZ1 rom)
                    /\ getr r2 28 = Z_to_bv 64 (data + 4 * wpl * i + 4 * (w / 32)))
                   \/ msteps SEGS (mkst r1 (rl dVL_24ed4 0x24fbc) MZ1 rom) (mkst r2 (rl dVL_24ed4 0x25090) MZ1 rom) )).
    { destruct (Z.lt_ge_cases w 32) as [Hw32|Hw32].
      - (* [comment removed for export] *)
        exists r1. split; [apply regs_agree_refl | left]. split.
        + stepb_tk F_24fbc D_24fbc ltac:(condZ).            (* [comment removed for export] *)
          apply mst_refl.
        + rewrite Q28. f_equal. f_equal. lia.
      - assert (S2a : exists r2, msteps SEGS (mkst r1 (rl dVL_24ed4 0x24fbc) MZ1 rom) (mkst r2 (rl dVL_24ed4 0x24fcc) MZ1 rom)
                                 /\ ZInv r2 /\ getr r2 11 = Z_to_bv 64 (wpl * i) /\ getr r2 12 = Z_to_bv 64 i
                                 /\ getr r2 28 = Z_to_bv 64 (data + 4 * wpl * i + 4 * 0)
                                 /\ getr r2 29 = Z_to_bv 64 (data + 4 * wpl * i + 4 * 0)
                                 /\ getr r2 30 = Z_to_bv 64 (w / 32 - 0)
                                 /\ regs_agree (fun r : reg => In r [29; 30]%list) r1 r2).
        { eexists. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
          - stepb_ft F_24fbc D_24fbc ltac:(condZ).          (* [comment removed for export] *)
            zvs F_24fc0 D_24fc0 (Z_to_bv 64 (4 * wpl * i)). (* [comment removed for export] *)
            zvw F_24fc4 D_24fc4 (Z_to_bv 64 (data + 4 * wpl * i + 4 * 0)).   (* [comment removed for export] *)
            zvw F_24fc8 D_24fc8 (Z_to_bv 64 (w / 32 - 0)).  (* [comment removed for export] *)
            apply mst_refl.
          - unfold ZInv. repeat split; gres; pin; reflexivity.
          - gres. exact Q11.
          - gres. exact Q12.
          - gres. exact Q28.
          - gres. reflexivity.
          - gres. reflexivity.
          - solve_regs_agree. }
        destruct S2a as (r2 & S2a & HZ2 & T11 & T12 & T28 & T29 & T30 & AG2).
        destruct (mi_ZL (Z.to_nat (w / 32 - 1)) r2 i 0 Hd1 Hi ltac:(lia) ltac:(lia) HZ2 T11 T12 T28 T29 T30) as (r3 & AG3 & POST).
        exists r3. split; [eapply regs_agree_trans; [regs_agree_weaken AG2 | exact AG3]|].
        destruct POST as [[S3 R28]|S3].
        + left. split; [|exact R28]. eapply msteps_trans; [exact S2a | exact S3].
        + right. eapply msteps_trans; [exact S2a | exact S3]. }
    destruct S2 as (r2 & AG2 & POST).
    assert (HZ2 : ZInv r2) by (unfold ZInv; rewrite !AG2 by notin_list; exact HZ1).
    pose proof HZ2 as (K2 & K10 & K18 & K13 & K14 & K15 & K16 & K17 & K5 & K6 & K7 & K9 & K8 & K19).
    destruct POST as [[S2 R28]|S2].
    2:{ (* [comment removed for export] *)
        exists r2. split; [eapply regs_agree_trans; [regs_agree_weaken AG1 | exact AG2] | right].
        eapply msteps_trans; [exact S1 | exact S2]. }
    (* [comment removed for export] *)
    destruct (Z.eq_dec (w mod 32) 0) as [Hr0|Hr0].
    - (* [comment removed for export] *)
      exists r2. split; [eapply regs_agree_trans; [regs_agree_weaken AG1 | exact AG2] | left].
      eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|].
      stepb_tk F_24ff0 D_24ff0 ltac:(condE).                (* [comment removed for export] *)
      apply mst_refl.
    - pose proof (Htail Hr0) as Hfw2.
      destruct (word_at_z i (w / 32) Hi ltac:(lia)) as (bs & Hbs & Lbs).
      pose proof (word_addr_al4 data wpl i (w / 32) Hdal) as Hal.
      (* [comment removed for export] *)
      assert (S3 : exists r3 (v : word), msteps SEGS (mkst r2 (rl dVL_24ed4 0x24ff0) MZ1 rom) (mkst r3 (rl dVL_24ed4 0x25008) MZ1 rom)
                                  /\ getr r3 28 = v /\ regs_agree (fun r : reg => In r [28; 29]%list) r2 r3).
      { eexists. eexists. split; [|split].
        - stepb_ft F_24ff0 D_24ff0 ltac:(condE).            (* [comment removed for export] *)
          stepb_ft F_24ff4 D_24ff4 ltac:(condE).            (* [comment removed for export] *)
          zand F_24ff8 D_24ff8 andi_3 Hal.                  (* [comment removed for export] *)
          stepb_ft F_24ffc D_24ffc ltac:(condR).            (* [comment removed for export] *)
          stepLD F_25000 D_25000 bs (Z_to_bv 64 (bytes_le_to_Z bs))
            ltac:(rdn_addr (data + 4 * wpl * i + 4 * (w / 32))%Z; exact Hbs)
            ltac:(symmetry; apply u_lez4; exact Lbs).      (* [comment removed for export] *)
          sn F_25004 D_25004.                               (* [comment removed for export] *)
          apply mst_refl.
        - gres. reflexivity.
        - solve_regs_agree. }
      destruct S3 as (r3 & v & S3 & R28v & AG3).
      destruct (c_eq v (Z_to_bv 64 0)) eqn:Hc.
      + (* [comment removed for export] *)
        exists r3. split; [eapply regs_agree_trans; [regs_agree_weaken AG1 | eapply regs_agree_trans; [exact AG2 | regs_agree_weaken AG3]] | left].
        eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|]. eapply msteps_trans; [exact S3|].
        stepb_ft F_25008 D_25008 ltac:(pin; exact Hc).      (* [comment removed for export] *)
        apply mst_refl.
      + exists r3. split; [eapply regs_agree_trans; [regs_agree_weaken AG1 | eapply regs_agree_trans; [exact AG2 | regs_agree_weaken AG3]] | right].
        eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2|]. eapply msteps_trans; [exact S3|].
        stepb_tk F_25008 D_25008 ltac:(pin; exact Hc).      (* [comment removed for export] *)
        apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma mi_Zloop : forall k regs i, (d = 1)%Z -> (Z.of_nat k = h - 1 - i)%Z -> (0 <= i)%Z ->
    ZInv regs -> getr regs 11 = Z_to_bv 64 (wpl * i) -> getr regs 12 = Z_to_bv 64 i ->
    exists regs',
      regs_agree (fun r : reg => In r [11; 12; 28; 29; 30; 31]%list) regs regs'
      /\ ( msteps SEGS (mkst regs (rl dVL_24ed4 0x24f88) MZ1 rom) (mkst regs' (rl dVL_24ed4 0x25018) MZ1 rom)
           \/ msteps SEGS (mkst regs (rl dVL_24ed4 0x24f88) MZ1 rom) (mkst regs' (rl dVL_24ed4 0x25090) MZ1 rom) ).
  Proof.
    nodisj. pose proof wplh_bound as Hwh. pose proof wpl_bounds as (Hwpl1 & _ & _).
    induction k as [|k IH]; intros regs i Hd1 Hk Hi HZ H11 H12;
      destruct (mi_Zrow regs i Hd1 ltac:(lia) HZ H11 H12) as (r1 & AG1 & POST);
      (assert (HZ1 : ZInv r1) by (unfold ZInv; rewrite !AG1 by notin_list; exact HZ));
      pose proof HZ1 as (J2 & J10 & J18 & J13 & J14 & J15 & J16 & J17 & J5 & J6 & J7 & J9 & J8 & J19);
      (pose proof (AG1 11 ltac:(notin_list)) as Q11); rewrite H11 in Q11;
      (pose proof (AG1 12 ltac:(notin_list)) as Q12); rewrite H12 in Q12;
      pose proof (row_in_raster i ltac:(lia)) as Hrow;
      (destruct POST as [S1|S1];
       [| exists r1; split; [regs_agree_weaken AG1 | right; exact S1]]).
    - (* [comment removed for export] *)
      eexists. split; [|left].
      2:{ eapply msteps_trans; [exact S1|].
          zvw F_2500c D_2500c (Z_to_bv 64 (i + 1)).         (* [comment removed for export] *)
          sn F_25010 D_25010.                               (* [comment removed for export] *)
          fixv (Z_to_bv 64 (wpl * (i + 1))) ltac:(rewrite zbv_addw_small by lia; f_equal; lia).
          stepb_ft F_25014 D_25014 ltac:(condZ).            (* [comment removed for export] *)
          apply mst_refl. }
      eapply regs_agree_trans; [regs_agree_weaken AG1|]. solve_regs_agree.
    - assert (S2 : exists r2, msteps SEGS (mkst r1 (rl dVL_24ed4 0x2500c) MZ1 rom) (mkst r2 (rl dVL_24ed4 0x24f88) MZ1 rom)
                              /\ ZInv r2 /\ getr r2 11 = Z_to_bv 64 (wpl * (i + 1)) /\ getr r2 12 = Z_to_bv 64 (i + 1)
                              /\ regs_agree (fun r : reg => In r [11; 12]%list) r1 r2).
      { eexists. split; [|split; [|split; [|split]]].
        - zvw F_2500c D_2500c (Z_to_bv 64 (i + 1)).         (* [comment removed for export] *)
          sn F_25010 D_25010.                               (* [comment removed for export] *)
          fixv (Z_to_bv 64 (wpl * (i + 1))) ltac:(rewrite zbv_addw_small by lia; f_equal; lia).
          stepb_tk F_25014 D_25014 ltac:(condZ).            (* [comment removed for export] *)
          apply mst_refl.
        - unfold ZInv. repeat split; gres; pin; reflexivity.
        - gres. reflexivity.
        - gres. reflexivity.
        - solve_regs_agree. }
      destruct S2 as (r2 & S2 & HZ2 & Q11' & Q12' & AG2).
      destruct (IH r2 (i + 1)%Z Hd1 ltac:(lia) ltac:(lia) HZ2 Q11' Q12') as (r3 & AG3 & POST).
      exists r3. split.
      + eapply regs_agree_trans; [regs_agree_weaken AG1|]. eapply regs_agree_trans; [regs_agree_weaken AG2 | exact AG3].
      + destruct POST as [S3|S3].
        * left. eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2 | exact S3].
        * right. eapply msteps_trans; [exact S1|]. eapply msteps_trans; [exact S2 | exact S3].
  Qed.

  (* [comment removed for export] *)
  Definition ZFS (Mx : word -> option byte) : Prop :=
    forall x : word, (sp - 128 <= bv_unsigned x < sp - 80)%Z -> Mx x = MZ x.

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
    ZFS Mx -> (80 + Z.of_nat n <= k <= 128)%Z ->
    rdn SEGS MZ (Z_to_bv 64 (sp - k)) n = Some bs -> rdn SEGS Mx (Z_to_bv 64 (sp - k)) n = Some bs.
  Proof.
    intros Mx k n bs HF Hk HM. nodisj. clear RR. rewrite <- HM. apply rdn_ext; rewrite u_Z2bv by lia; [lia|].
    intros x Hx. apply HF. lia.
  Qed.

  Lemma FS_MZ1 : FrameSame MZ1.
  Proof.
    clear RR AP FP. unfold MZ1, MZ.
    do 7 (apply FS_wbytes; [| lia | zlen; lia | zlen; lia]). apply FS_MC.
  Qed.
  Lemma FS_MZ0 : FrameSame MZ0.
  Proof. clear RR AP FP. unfold MZ0. apply FS_wbytes; [apply FS_MZ1 | lia | zlen; lia | zlen; lia]. Qed.

  (* [comment removed for export] *)
  Lemma mi_ZE : forall regs Mx,
    ZFS Mx -> getr regs 2 = Z_to_bv 64 (sp - 128) ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_24ed4 0x250a0) Mx rom) (mkst regs' (rl dVL_24b70 0x24c14) Mx rom)
      /\ getr regs' 10 = getr regs 10 /\ getr regs' 2 = Z_to_bv 64 (sp - 80)
      /\ getr regs' 8 = Z_to_bv 64 wpl /\ getr regs' 9 = Z_to_bv 64 pix /\ getr regs' 18 = Z_to_bv 64 pmax
      /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ regs_agree (fun x : reg => In x [1; 2; 8; 9; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs Mx HF H2. nodisj. clear RR.
    pose proof (u64_range s3v). pose proof (u64_range s4v).
    eexists. split.
    - stepLD F_250a0 D_250a0 (word_to_le_bytes 8 (rl dVL_24b70 0x24c14)) (rl dVL_24b70 0x24c14)
        ltac:(rdn_addr (sp - 88)%Z; apply (ZFS_rdn Mx 88 8); [exact HF | cbn; lia | unfold MZ; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_250a4 D_250a4 (word_to_le_bytes 8 (Z_to_bv 64 wpl)) (Z_to_bv 64 wpl)
        ltac:(rdn_addr (sp - 96)%Z; apply (ZFS_rdn Mx 96 8); [exact HF | cbn; lia | unfold MZ; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_250a8 D_250a8 (word_to_le_bytes 8 (Z_to_bv 64 pix)) (Z_to_bv 64 pix)
        ltac:(rdn_addr (sp - 104)%Z; apply (ZFS_rdn Mx 104 8); [exact HF | cbn; lia | unfold MZ; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_250ac D_250ac (word_to_le_bytes 8 (Z_to_bv 64 pmax)) (Z_to_bv 64 pmax)
        ltac:(rdn_addr (sp - 112)%Z; apply (ZFS_rdn Mx 112 8); [exact HF | cbn; lia | unfold MZ; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_250b0 D_250b0 (word_to_le_bytes 8 s3v) s3v
        ltac:(rdn_addr (sp - 120)%Z; apply (ZFS_rdn Mx 120 8); [exact HF | cbn; lia | unfold MZ; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      stepLD F_250b4 D_250b4 (word_to_le_bytes 8 s4v) s4v
        ltac:(rdn_addr (sp - 128)%Z; apply (ZFS_rdn Mx 128 8); [exact HF | cbn; lia | unfold MZ; rdn_chain])
        ltac:(apply bytes_le_to_Z_8).                      (* [comment removed for export] *)
      zvw F_250b8 D_250b8 (Z_to_bv 64 (sp - 80)).           (* [comment removed for export] *)
      stepretF F_250bc D_250bc F_24c14. (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma mi_ZX1 : forall regs, getr regs 2 = Z_to_bv 64 (sp - 128) ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_24ed4 0x25018) MZ1 rom) (mkst regs' (rl dVL_24b70 0x24c14) MZ1 rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 80) /\ getr regs' 18 = Z_to_bv 64 pmax
      /\ getr regs' 8 = Z_to_bv 64 wpl /\ getr regs' 9 = Z_to_bv 64 pix
      /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ regs_agree (fun x : reg => In x [1; 2; 8; 9; 10; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs H2. nodisj. clear RR.
    destruct (mi_ZE (regupd regs 10 (Z_to_bv 64 0)) MZ1 ZFS_MZ1 ltac:(gres; exact H2))
      as (r1 & S1 & E10 & E2 & E8 & E9 & E18 & E19 & E20 & AG1).
    exists r1. split.
    - sn F_25018 D_25018.                                   (* [comment removed for export] *)
      sn F_2501c D_2501c.                                   (* [comment removed for export] *)
      exact S1.
    - repeat split; try assumption.
      eapply regs_agree_trans; [|regs_agree_weaken AG1]. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma mi_ZX0 : forall regs, getr regs 2 = Z_to_bv 64 (sp - 128) -> getr regs 8 = Z_to_bv 64 (sp - 80) ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_24ed4 0x25090) MZ1 rom) (mkst regs' (rl dVL_24b70 0x24c14) MZ0 rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 80) /\ getr regs' 18 = Z_to_bv 64 pmax
      /\ getr regs' 8 = Z_to_bv 64 wpl /\ getr regs' 9 = Z_to_bv 64 pix
      /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ regs_agree (fun x : reg => In x [1; 2; 8; 9; 10; 18; 19; 20]%list) regs regs'.
  Proof.
    intros regs H2 H8. nodisj. clear RR.
    destruct (mi_ZE (regupd regs 10 (Z_to_bv 64 0)) MZ0 ZFS_MZ0 ltac:(gres; exact H2))
      as (r1 & S1 & E10 & E2 & E8 & E9 & E18 & E19 & E20 & AG1).
    exists r1. split.
    - sn F_25090 D_25090.                                   (* [comment removed for export] *)
      stz F_25094 D_25094 80%Z (Z_to_bv 64 0).                (* [comment removed for export] *)
      fold MZ0.
      sn F_25098 D_25098.                                   (* [comment removed for export] *)
      exact S1.
    - repeat split; try assumption.
      eapply regs_agree_trans; [|regs_agree_weaken AG1]. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma mi_C : forall regs Mx (e : Z), (e = 0 \/ e = 1)%Z -> mem_grows M Mx ->
    rdn SEGS Mx (Z_to_bv 64 (sp - 80)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 e)) ->
    getr regs 2 = Z_to_bv 64 (sp - 80) -> getr regs 18 = Z_to_bv 64 pmax ->
    exists regs',
      msteps SEGS (mkst regs (rl dVL_24b70 0x24c14) Mx rom) (mkst regs' (rl dVL_24b70 0x24ea8) (MF Mx (Z_to_bv 64 (1 - e))) rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 (sp - 80)
      /\ regs_agree (fun x : reg => In x [10; 11]%list) regs regs'.
  Proof.
    intros regs Mx e He HG Hrd H2 H18. nodisj. clear RR.
    eexists. split.
    - sn F_24c14 D_24c14.                                   (* [comment removed for export] *)
      stepLD F_24c18 D_24c18 (word_to_le_bytes 4 (Z_to_bv 64 e)) (Z_to_bv 64 e)
        ltac:(rdn_addr (sp - 80)%Z; exact Hrd)
        ltac:(apply bytes_le_to_Z_4; unorm; lia).          (* [comment removed for export] *)
      rewrite (v_lw_small e) by lia.
      stepiv F_24c1c D_24c1c (Z_to_bv 64 (1 - e))
        ltac:(gres; pin; imm_norm; rewrite zbv_seqz by lia; destruct He as [-> | ->]; reflexivity).   (* [comment removed for export] *)
      stepST F_24c20 D_24c20 (Z_to_bv 64 pmax) (Z_to_bv 64 (1 - e)) ltac:(apply sok_pmax; exact HG).   (* [comment removed for export] *)
      fold (MF Mx (Z_to_bv 64 (1 - e))).
      sn F_24c24 D_24c24.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma mi_run1 : forall regs, (d = 1)%Z ->
    getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 sp ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v ->
    getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v -> getr regs 22 = s6v ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 pmax ->
    exists regs' Mx (e : Z),
      msteps SEGS (mkst regs (rl dVL_24b70 0x24b70) M rom) (mkst regs' ra (MF Mx (Z_to_bv 64 (1 - e))) rom)
      /\ (Mx = MZ1 \/ Mx = MZ0) /\ (e = 0 \/ e = 1)%Z
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 sp
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v
      /\ regs_agree (fun x : reg => In x [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs Hd1 H1 H2 H8 H9 H18 H19 H20 H21 H22 H10 H11.
    destruct (mi_A regs H1 H2 H8 H9 H18 H19 H20 H21 H22 H10 H11) as (r1 & S1 & A2 & A9 & A18 & AG1).
    pose proof (AG1 19 ltac:(notin_list)) as A19. rewrite H19 in A19.
    pose proof (AG1 20 ltac:(notin_list)) as A20. rewrite H20 in A20.
    pose proof (AG1 21 ltac:(notin_list)) as A21. rewrite H21 in A21.
    destruct (mi_B r1 A2 A9) as (r2 & S2 & B2 & B10 & B8 & B11 & B12 & AG2).
    pose proof (AG2 9 ltac:(notin_list)) as B9. rewrite A9 in B9.
    pose proof (AG2 18 ltac:(notin_list)) as B18. rewrite A18 in B18.
    pose proof (AG2 19 ltac:(notin_list)) as B19. rewrite A19 in B19.
    pose proof (AG2 20 ltac:(notin_list)) as B20. rewrite A20 in B20.
    pose proof (AG2 21 ltac:(notin_list)) as B21. rewrite A21 in B21.
    destruct (mi_Z1 r2 Hd1 B2 B8 B11 B12 B9 B18 B19 B20) as (r3 & S3 & C2 & C8 & C19 & C20 & C9 & C18 & C10 & AG3).
    pose proof (AG3 21 ltac:(notin_list)) as C21. rewrite B21 in C21.
    destruct (mi_Z2 r3 Hd1 C2 C8 C19 C20 C9 C18 C10) as (r4 & S4 & HZ4 & D11 & D12 & AG4).
    pose proof (AG4 21 ltac:(notin_list)) as D21. rewrite C21 in D21.
    destruct (mi_Zloop (Z.to_nat (h - 1)) r4 0 Hd1 ltac:(lia) ltac:(lia) HZ4 D11 D12) as (r5 & AG5 & POST).
    assert (HZ5 : ZInv r5) by (unfold ZInv; rewrite !AG5 by notin_list; exact HZ4).
    destruct HZ5 as (E2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E8 & _).
    pose proof (AG5 21 ltac:(notin_list)) as E21. rewrite D21 in E21.
    destruct POST as [S5|S5].
    - (* [comment removed for export] *)
      destruct (mi_ZX1 r5 E2) as (r6 & S6 & F2 & F18 & F8 & F9 & F19 & F20 & AG6).
      pose proof (AG6 21 ltac:(notin_list)) as F21. rewrite E21 in F21.
      assert (Hrd : rdn SEGS MZ1 (Z_to_bv 64 (sp - 80)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1))).
      { clear AP FP S1 S2 S3 S4 S5 S6. unfold MZ1. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
      destruct (mi_C r6 MZ1 1 ltac:(lia) MZ1_grows Hrd F2 F18) as (r7 & S7 & G10 & G2 & AG7).
      destruct (mi_E r7 (MF MZ1 (Z_to_bv 64 (1 - 1))) (FS_MF _ _ FS_MZ1) G2)
        as (r8 & S8 & K10 & K1 & K2 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & AG8).
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
      destruct (mi_ZX0 r5 E2 E8) as (r6 & S6 & F2 & F18 & F8 & F9 & F19 & F20 & AG6).
      pose proof (AG6 21 ltac:(notin_list)) as F21. rewrite E21 in F21.
      assert (Hrd : rdn SEGS MZ0 (Z_to_bv 64 (sp - 80)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))).
      { clear AP FP S1 S2 S3 S4 S5 S6. unfold MZ0. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
      destruct (mi_C r6 MZ0 0 ltac:(lia) MZ0_grows Hrd F2 F18) as (r7 & S7 & G10 & G2 & AG7).
      destruct (mi_E r7 (MF MZ0 (Z_to_bv 64 (1 - 0))) (FS_MF _ _ FS_MZ0) G2)
        as (r8 & S8 & K10 & K1 & K2 & K8 & K9 & K18 & K19 & K20 & K21 & K22 & AG8).
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
    (bv_unsigned x < sp - 128 \/ sp <= bv_unsigned x)%Z -> (bv_unsigned x < pmax \/ pmax + 4 <= bv_unsigned x)%Z ->
    MC x = M x.
  Proof.
    intros x Hx Hp. clear RR AP FP FPM. unfold MC, MB, MA.
    rewrite !wbytes_outside by (zlen; rewrite ?u_Z2bv by lia; lia). reflexivity.
  Qed.
  Lemma MZ1_outside : forall x : word,
    (bv_unsigned x < sp - 128 \/ sp <= bv_unsigned x)%Z -> (bv_unsigned x < pmax \/ pmax + 4 <= bv_unsigned x)%Z ->
    MZ1 x = M x.
  Proof.
    intros x Hx Hp. pose proof (MC_outside x Hx Hp) as HC. clear RR AP FP FPM. unfold MZ1, MZ.
    rewrite !wbytes_outside by (zlen; rewrite ?u_Z2bv by lia; lia). exact HC.
  Qed.
  Lemma MZ0_outside : forall x : word,
    (bv_unsigned x < sp - 128 \/ sp <= bv_unsigned x)%Z -> (bv_unsigned x < pmax \/ pmax + 4 <= bv_unsigned x)%Z ->
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
    (forall x : word, (bv_unsigned x < sp - 128 \/ sp <= bv_unsigned x)%Z ->
                      (bv_unsigned x < pmax \/ pmax + 4 <= bv_unsigned x)%Z -> M' x = M x)
    /\ mem_grows M M'
    /\ rdn SEGS M' (Z_to_bv 64 pmax) 4 = Some (Z_to_le_bytes 4 mi)
    /\ (0 <= mi <= 255)%Z.

  (* [comment removed for export] *)
  Theorem maxindex_run : forall regs,
    getr regs 1 = ra -> getr regs 2 = Z_to_bv 64 sp ->
    getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v ->
    getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v -> getr regs 22 = s6v ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 pmax ->
    exists regs' M' (mi : Z),
      msteps SEGS (mkst regs (rl dVL_24b70 0x24b70) M rom) (mkst regs' ra M' rom)
      /\ PostMem M' mi
      /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 sp
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v
      /\ regs_agree (fun x : reg => In x [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 28; 29; 30; 31]%list) regs regs'.
  Proof.
    intros regs H1 H2 H8 H9 H18 H19 H20 H21 H22 H10 H11.
    destruct (Z.eq_dec d 1) as [Hd1|Hd1].
    - destruct (mi_run1 regs Hd1 H1 H2 H8 H9 H18 H19 H20 H21 H22 H10 H11)
        as (r' & Mx & e & RUN & HMx & He & Q10 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & AG).
      exists r', (MF Mx (Z_to_bv 64 (1 - e))), (1 - e)%Z. split; [exact RUN|]. split; [|repeat split; assumption].
      split; [|split; [|split]].
      + intros x Hx Hp. apply MF_outside; [|exact Hp].
        destruct HMx as [-> | ->]; [apply MZ1_outside | apply MZ0_outside]; assumption.
      + apply MF_grows. destruct HMx as [-> | ->]; [apply MZ1_grows | apply MZ0_grows].
      + rewrite MF_cell. rewrite u_Z2bv by lia. reflexivity.
      + lia.
    - destruct (mi_run248 regs Hd1 H1 H2 H8 H9 H18 H19 H20 H21 H22 H10 H11)
        as (r' & mx & RUN & Hmx & Q10 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & AG).
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

Theorem maxindex_contract : SSP.sum_contract SEGS (SSP.spec_maxindex (0x24b70 + dVL_24b70) 128).
Proof.
  apply SSP.sum_contract_in7_out1; [reflexivity | reflexivity |].
  intros pix pmax w h d wpl data R M rom PRE.
  unfold SSP.spec_maxindex in PRE. SSP.spec_unfold_in PRE.
  destruct PRE as (ITEMS & EFF & FR & RET).
  destruct ITEMS as ((H10 & _) & Hpix & (_ & Hpixal) & (H11 & _) & Hpmax & (_ & _ & (Rw & Cw)) & Hw & (_ & _ & (Rh & Ch)) & Hh
                     & (_ & _ & (Rd & Cd)) & Hd & (_ & _ & (Rwpl & Cwpl)) & Hwpl & (_ & F56 & (Rdata & Cdata)) & Hdata & (_ & Hdal)
                     & ((FRS & RR) & HRS & (Fpm & SOKp) & (_ & Hpal) & AP & (_ & SP16) & _)).
  destruct EFF as (_ & (Fsp & _ & Fsp2) & SOKf & _ & Fpm2 & _).
  destruct FR as ((F0 & F4 & F8 & F16 & F56' & FRR & FPM & _) & _).
  cbn [Z.of_nat Z.add] in F0, F4, F8, F16, F56', FPM.
  change (2 ^ (8 * Z.of_nat 4))%Z with (2 ^ 32)%Z in Rw, Rh, Rd, Rwpl.
  unfold SSP.flatZ in F56, FRS, Fpm. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in F56.
  set (sp := bv_unsigned (getr R 2)) in *.
  assert (FP : (pix + 64 <= sp - 128 \/ sp <= pix)%Z) by (clear FRR FPM AP; lia).
  clear F0 F4 F8 F16 F56' FRR.
  assert (H2 : getr R 2 = Z_to_bv 64 sp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (u64_range (getr R 2)) as Hsp. fold sp in Hsp.
  rewrite Z.add_0_r in Cw.
  assert (Hd' : (d = 1 \/ d = 2 \/ d = 4 \/ d = 8)%Z) by (generalize Hd; clear; cbn; intuition lia).
  assert (Hdata4 : (4 <= data /\ data < 2 ^ 64)%Z) by (clear FPM AP FP; lia).
  unfold SSP.spec_maxindex. SSP.spec_unfold.
  destruct (maxindex_run M rom pix pmax w h d wpl data sp (getr R 1) (getr R 8) (getr R 9) (getr R 18)
              (getr R 19) (getr R 20) (getr R 21) (getr R 22)
              ltac:(clear FPM AP FP; lia) Hpixal ltac:(clear FPM AP FP; lia) Hpal Rw Rh Rd Rwpl Hw Hh Hd' Hwpl Hdata4 Hdal
              ltac:(clear FPM AP FP; lia) SP16 RET Cw Ch Cd Cwpl Cdata ltac:(clear FPM AP FP; lia) RR SOKp AP FPM SOKf FP
              R eq_refl H2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl H10 H11)
    as (R' & M' & mi & RUN & (PO & PG & PC & Pmi) & A10 & A2 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & AG).
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
