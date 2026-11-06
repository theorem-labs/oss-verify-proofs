(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import StartupTac.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbMemcpyBase Ub_code_235f0_245f0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastS.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.peel ::= peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section ZC.
  Variable mem0 : word -> option byte.
  Variable d : word.
  Variable n : Z.
  Hypothesis Hn : (0 <= n)%Z.
  Hypothesis Hnw : (bv_unsigned d + n < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok SEGS mem0 d (Z.to_nat n) = true.

  (* [comment removed for export] *)
  Definition inz (i a b lo hi : Z) : bool :=
    (((0 <=? i) && (i <? a)) || ((b <=? i) && (i <? n)) || ((lo <=? i) && (i <? hi)))%Z.
  Definition zc (a b lo hi : Z) : word -> option byte :=
    fun x => if inz (bv_unsigned x - bv_unsigned d) a b lo hi then Some (Z_to_bv 8 0) else mem0 x.

  Lemma inz_spec : forall i a b lo hi,
    inz i a b lo hi = true <-> ((0 <= i < a) \/ (b <= i < n) \/ (lo <= i < hi))%Z.
  Proof.
    intros i a b lo hi. unfold inz. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le, !Z.ltb_lt. tauto.
  Qed.
  Lemma inz_false : forall i a b lo hi,
    inz i a b lo hi = false <-> ~ ((0 <= i < a) \/ (b <= i < n) \/ (lo <= i < hi))%Z.
  Proof. intros i a b lo hi. rewrite <- inz_spec. destruct (inz i a b lo hi); split; intros H; congruence. Qed.

  Lemma zc_init : forall a b lo hi, (a <= 0)%Z -> (n <= b)%Z -> (hi <= lo)%Z -> zc a b lo hi = mem0.
  Proof.
    intros a b lo hi Ha Hb Hl. apply functional_extensionality. intros x. unfold zc.
    destruct (inz _ a b lo hi) eqn:E; [|reflexivity]. apply inz_spec in E. lia.
  Qed.

  Lemma zc_full : forall a b lo hi,
    (forall i, ((0 <= i < a) \/ (b <= i < n) \/ (lo <= i < hi)) <-> (0 <= i < n))%Z ->
    zc a b lo hi = wbytes mem0 d (zeros (Z.to_nat n)).
  Proof.
    intros a b lo hi H. apply functional_extensionality. intros x. unfold zc.
    pose proof (u64_range x). pose proof (u64_range d).
    destruct (inz _ a b lo hi) eqn:E.
    - apply inz_spec in E. apply H in E.
      rewrite wbytes_inside by (rewrite length_zeros; lia). rewrite nth_zeros. reflexivity.
    - apply inz_false in E. rewrite H in E.
      rewrite wbytes_outside by (rewrite length_zeros; lia). reflexivity.
  Qed.

  Lemma zc_store : forall a b lo hi o (w : nat) a' b' lo' hi',
    (0 <= o)%Z -> (o + Z.of_nat w <= n)%Z ->
    (forall i, ((0 <= i < a') \/ (b' <= i < n) \/ (lo' <= i < hi'))
           <-> ((0 <= i < a) \/ (b <= i < n) \/ (lo <= i < hi) \/ (o <= i < o + Z.of_nat w)))%Z ->
    wbytes (zc a b lo hi) (Z_to_bv 64 (bv_unsigned d + o)) (zeros w) = zc a' b' lo' hi'.
  Proof.
    intros a b lo hi o w a' b' lo' hi' Ho How H. apply functional_extensionality. intros x. unfold zc.
    pose proof (u64_range x). pose proof (u64_range d).
    destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned d + o)) as [Hlt|Hge];
      [| destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned d + o + Z.of_nat w)) as [Hin|Hout]].
    - rewrite wbytes_outside by (rewrite length_zeros, u_Z2bv by lia; lia).
      destruct (inz _ a b lo hi) eqn:E1, (inz _ a' b' lo' hi') eqn:E2; try reflexivity; exfalso.
      + apply inz_spec in E1. apply inz_false in E2. apply E2. apply H. lia.
      + apply inz_false in E1. apply inz_spec in E2. apply H in E2. lia.
    - rewrite wbytes_inside by (rewrite length_zeros, u_Z2bv by lia; lia). rewrite nth_zeros.
      destruct (inz _ a' b' lo' hi') eqn:E2; [reflexivity|]. exfalso.
      apply inz_false in E2. apply E2. apply H. lia.
    - rewrite wbytes_outside by (rewrite length_zeros, u_Z2bv by lia; lia).
      destruct (inz _ a b lo hi) eqn:E1, (inz _ a' b' lo' hi') eqn:E2; try reflexivity; exfalso.
      + apply inz_spec in E1. apply inz_false in E2. apply E2. apply H. lia.
      + apply inz_false in E1. apply inz_spec in E2. apply H in E2. lia.
  Qed.

  Lemma zc_grows : forall a b lo hi, mem_grows mem0 (zc a b lo hi).
  Proof. intros a b lo hi x Hx. unfold zc. destruct (inz _ a b lo hi); [discriminate | exact Hx]. Qed.

  Lemma zc_ok : forall a b lo hi o (w : nat),
    (0 <= o)%Z -> (o + Z.of_nat w <= n)%Z ->
    store_ok SEGS (zc a b lo hi) (Z_to_bv 64 (bv_unsigned d + o)) w = true.
  Proof.
    intros a b lo hi o w Ho How. pose proof (u64_range d).
    apply (store_ok_mono SEGS w mem0); [apply zc_grows|].
    apply (store_ok_sub SEGS mem0 d _ (Z.to_nat n)); try (rewrite ?u_Z2bv by lia; lia). exact Hok.
  Qed.

  Lemma zc_sb : forall regs pc rom w rs1 rs2 (imm : bv 12) a b lo hi o a' b' lo' hi',
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
    v_addi (getr regs rs1) (bv_signed imm) = Z_to_bv 64 (bv_unsigned d + o) ->
    getr regs rs2 = Z_to_bv 64 0 ->
    (0 <= o)%Z -> (o + 1 <= n)%Z ->
    (forall i, ((0 <= i < a') \/ (b' <= i < n) \/ (lo' <= i < hi'))
           <-> ((0 <= i < a) \/ (b <= i < n) \/ (lo <= i < hi) \/ (o <= i < o + 1)))%Z ->
    RiscvSemantics.step SEGS (mkst regs pc (zc a b lo hi) rom) =
    MachineOk (mkst regs (v_addi pc 4) (zc a' b' lo' hi') rom).
  Proof.
    intros regs pc rom w rs1 rs2 imm a b lo hi o a' b' lo' hi' Hf He Hd Ha Hv Ho Ho1 H.
    rewrite <- (zc_store a b lo hi o 1 a' b' lo' hi') by assumption.
    eapply MmapSim.step_sb_at; [exact Hf | exact He | exact Hd | exact Ha | exact Hv | reflexivity |].
    apply zc_ok; assumption.
  Qed.

  Lemma zc_sw : forall regs pc rom w rs1 rs2 (imm : bv 12) a b lo hi o a' b' lo' hi',
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
    v_addi (getr regs rs1) (bv_signed imm) = Z_to_bv 64 (bv_unsigned d + o) ->
    getr regs rs2 = Z_to_bv 64 0 ->
    (0 <= o)%Z -> (o + 4 <= n)%Z ->
    (forall i, ((0 <= i < a') \/ (b' <= i < n) \/ (lo' <= i < hi'))
           <-> ((0 <= i < a) \/ (b <= i < n) \/ (lo <= i < hi) \/ (o <= i < o + 4)))%Z ->
    RiscvSemantics.step SEGS (mkst regs pc (zc a b lo hi) rom) =
    MachineOk (mkst regs (v_addi pc 4) (zc a' b' lo' hi') rom).
  Proof.
    intros regs pc rom w rs1 rs2 imm a b lo hi o a' b' lo' hi' Hf He Hd Ha Hv Ho Ho1 H.
    rewrite <- (zc_store a b lo hi o 4 a' b' lo' hi') by assumption.
    change (zeros 4) with (word_to_le_bytes 4 (Z_to_bv 64 0)).
    eapply step_sw_at; [exact Hf | exact He | exact Hd | exact Ha | exact Hv |].
    apply zc_ok; assumption.
  Qed.

  Lemma zc_sd : forall regs pc rom w rs1 rs2 (imm : bv 12) a b lo hi o a' b' lo' hi',
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ8 rs1 rs2 imm, 4%Z) ->
    v_addi (getr regs rs1) (bv_signed imm) = Z_to_bv 64 (bv_unsigned d + o) ->
    getr regs rs2 = Z_to_bv 64 0 ->
    (0 <= o)%Z -> (o + 8 <= n)%Z ->
    (forall i, ((0 <= i < a') \/ (b' <= i < n) \/ (lo' <= i < hi'))
           <-> ((0 <= i < a) \/ (b <= i < n) \/ (lo <= i < hi) \/ (o <= i < o + 8)))%Z ->
    RiscvSemantics.step SEGS (mkst regs pc (zc a b lo hi) rom) =
    MachineOk (mkst regs (v_addi pc 4) (zc a' b' lo' hi') rom).
  Proof.
    intros regs pc rom w rs1 rs2 imm a b lo hi o a' b' lo' hi' Hf He Hd Ha Hv Ho Ho1 H.
    rewrite <- (zc_store a b lo hi o 8 a' b' lo' hi') by assumption.
    change (zeros 8) with (word_to_le_bytes 8 (Z_to_bv 64 0)).
    eapply step_sd_at; [exact Hf | exact He | exact Hd | exact Ha | exact Hv |].
    apply zc_ok; assumption.
  Qed.
End ZC.

(* [comment removed for export] *)
Lemma v_andi3 : forall x : word,
  v_andi x 3 = Z_to_bv 64 (Z.land (bv_unsigned x) 3) /\ (0 <= Z.land (bv_unsigned x) 3 <= 3)%Z.
Proof.
  intros x. pose proof (u64_range x). split.
  - unfold v_andi. reflexivity.
  - rewrite land_3 by lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Qed.

(* [comment removed for export] *)
Lemma land_4_cases : forall a, (0 <= a)%Z -> Z.land a 4 = 0%Z \/ Z.land a 4 = 4%Z.
Proof.
  intros a Ha.
  destruct (Z.testbit a 2) eqn:T.
  - right. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
    destruct (Z.eq_dec i 2) as [->|Hne]; [rewrite T; reflexivity|].
    replace (Z.testbit 4 i) with false; [rewrite andb_false_r; reflexivity|].
    symmetry. change 4%Z with (2^2)%Z. rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
  - left. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.eq_dec i 2) as [->|Hne]; [rewrite T; reflexivity|].
    replace (Z.testbit 4 i) with false; [rewrite andb_false_r; reflexivity|].
    symmetry. change 4%Z with (2^2)%Z. rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia.
Qed.

Lemma v_andi4 : forall x : word, exists e, (e = 0 \/ e = 4)%Z /\ v_andi x 4 = Z_to_bv 64 e.
Proof.
  intros x. pose proof (u64_range x).
  exists (Z.land (bv_unsigned x) 4). split; [apply land_4_cases; lia | unfold v_andi; reflexivity].
Qed.

(* [comment removed for export] *)
Lemma land_m4_64 : forall z, (0 <= z < 2 ^ 64)%Z ->
  Z.land z (2 ^ 64 - 4) = (z - z mod 4)%Z.
Proof.
  intros z Hz.
  assert (E1 : Z.land z (2 ^ 64 - 4) = Z.ldiff z 3).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec.
    destruct (Z.lt_ge_cases i 64) as [Hl|Hh].
    - replace (2 ^ 64 - 4)%Z with ((-4) mod 2 ^ 64)%Z by reflexivity.
      rewrite Z.mod_pow2_bits_low by lia.
      change (-4)%Z with (Z.lnot 3). rewrite Z.lnot_spec by lia. reflexivity.
    - rewrite (Z_testbit_high 64 z i) by lia. reflexivity. }
  rewrite E1.
  pose proof (Z.lor_ldiff_and z 3) as E2.
  rewrite <- Z.lxor_lor in E2.
  2:{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
      destruct (Z.testbit z i), (Z.testbit 3 i); reflexivity. }
  rewrite <- Z.add_nocarry_lxor in E2.
  2:{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec, Z.bits_0.
      destruct (Z.testbit z i), (Z.testbit 3 i); reflexivity. }
  rewrite land_3 in E2 by lia. lia.
Qed.

Lemma v_andi_m4 : forall z, (0 <= z < 2 ^ 64)%Z ->
  v_andi (Z_to_bv 64 z) (-4) = Z_to_bv 64 (z - z mod 4).
Proof.
  intros z Hz. unfold v_andi. rewrite (u_Z2bv z) by lia.
  change (bv_wrap 64 (-4)) with (2 ^ 64 - 4)%Z. rewrite land_m4_64 by lia. reflexivity.
Qed.


Definition memset_clob : list reg := [11; 12; 13; 14; 15; 16]%list.

Section MS.
  Variable mem0 : word -> option byte.
  Variable d : word.
  Variable n : Z.
  Variable rom : word -> option byte.
  Hypothesis Hn : (0 <= n)%Z.
  Hypothesis Hnw : (bv_unsigned d + n < 2 ^ 64)%Z.
  Hypothesis Hok : store_ok SEGS mem0 d (Z.to_nat n) = true.

  #[local] Notation ZC := (fun a b => zc mem0 d n a b 0 0).
  #[local] Notation FIN := (wbytes mem0 d (zeros (Z.to_nat n))).

  Ltac addr := gres; rwH; imm_norm; rewrite ?v_addi_0;
    first [ reflexivity
          | apply Z_to_bv_u_eq_sym; lia
          | unfold v_addi, v_add; unorm; first [ f_equal; lia | apply Z_to_bv_u_eq_sym; lia ] ].
  Ltac zst L F D oo aa bb ll hh :=
    chain_step; [reflexivity
      | eapply (L mem0 d n Hnw Hok) with (o := oo) (a' := aa) (b' := bb) (lo' := ll) (hi' := hh);
        [exact F | reflexivity | exact D | addr | gres; rwH; reflexivity | lia | lia | intro; lia]
      | step_simpl].
  Ltac zsb F D oo aa bb := zst zc_sb F D oo aa bb 0%Z 0%Z.
  Ltac zsw F D oo aa bb := zst zc_sw F D oo aa bb 0%Z 0%Z.
  Ltac zsd F D oo aa bb := zst zc_sd F D oo aa bb 0%Z 0%Z.
  Ltac zsb3 F D oo aa bb ll hh := zst zc_sb F D oo aa bb ll hh.
  Ltac zsw3 F D oo aa bb ll hh := zst zc_sw F D oo aa bb ll hh.
  (* [comment removed for export] *)
  Ltac vc := gres; rwH; imm_norm; rewrite ?v_addi_0;
    first [ reflexivity
          | unfold v_addi, v_add, v_sub; unorm; first [reflexivity | f_equal; lia | apply Z_to_bv_u_eq_sym; lia | apply Z_to_bv_u_eq; lia] ].
  Ltac sv F D v := stepiv F D v vc.
  Ltac cond := cond_lia.
  Ltac fin aa bb := rewrite (zc_full mem0 d n Hn Hnw aa bb 0 0) by (intro; lia); apply mst_refl.

  (* [comment removed for export] *)
  Lemma ms_small : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 n ->
    (n <= 8)%Z ->
    exists regs',
      msteps SEGS (mkst regs (0x23eec : word) mem0 rom) (mkst regs' ret FIN rom)
      /\ regs_agree (fun r => In r memset_clob) regs regs'.
  Proof.
    intros regs ret Hret H1 H10 H11 H12 Hsm.
    pose proof (u64_range d) as Hd.
    replace (mkst regs (0x23eec : word) mem0 rom) with (mkst regs (0x23eec : word) (zc mem0 d n 0 n 0 0) rom)
      by (rewrite zc_init by lia; reflexivity).
    destruct (Z.eq_dec n 0) as [Hz|Hnz].
    { eexists. split.
      - stepb_tk F_23eec D_23eec ltac:(cond).     (* [comment removed for export] *)
        stepret F_23fe0 D_23fe0 ret ltac:(rwH; reflexivity).
        fin 0%Z n.
      - solve_regs_agree. }
    destruct (Z_lt_le_dec n 3) as [H3|H3].
    { eexists. split.
      - stepb_ft F_23eec D_23eec ltac:(cond).     (* [comment removed for export] *)
        zsb F_23ef0 D_23ef0 0%Z 1%Z n.            (* [comment removed for export] *)
        sv F_23ef4 D_23ef4 (Z_to_bv 64 (bv_unsigned d + n)).  (* [comment removed for export] *)
        stepn F_23ef8 D_23ef8.                    (* [comment removed for export] *)
        zsb F_23efc D_23efc (n - 1)%Z 1%Z (n - 1)%Z.  (* [comment removed for export] *)
        stepb_tk F_23f00 D_23f00 ltac:(cond).     (* [comment removed for export] *)
        stepret F_23fe0 D_23fe0 ret ltac:(rwH; reflexivity).
        fin 1%Z (n - 1)%Z.
      - solve_regs_agree. }
    destruct (Z_lt_le_dec n 7) as [H7|H7].
    { eexists. split.
      - stepb_ft F_23eec D_23eec ltac:(cond).     (* [comment removed for export] *)
        zsb F_23ef0 D_23ef0 0%Z 1%Z n.            (* [comment removed for export] *)
        sv F_23ef4 D_23ef4 (Z_to_bv 64 (bv_unsigned d + n)).  (* [comment removed for export] *)
        stepn F_23ef8 D_23ef8.                    (* [comment removed for export] *)
        zsb F_23efc D_23efc (n - 1)%Z 1%Z (n - 1)%Z.  (* [comment removed for export] *)
        stepb_ft F_23f00 D_23f00 ltac:(cond).     (* [comment removed for export] *)
        zsb F_23f04 D_23f04 1%Z 2%Z (n - 1)%Z.    (* [comment removed for export] *)
        zsb F_23f08 D_23f08 2%Z 3%Z (n - 1)%Z.    (* [comment removed for export] *)
        stepn F_23f0c D_23f0c.                    (* [comment removed for export] *)
        zsb3 F_23f10 D_23f10 (n - 3)%Z 3%Z (n - 1)%Z (n - 3)%Z (n - 2)%Z.  (* [comment removed for export] *)
        zsb F_23f14 D_23f14 (n - 2)%Z 3%Z (n - 3)%Z.  (* [comment removed for export] *)
        stepb_tk F_23f18 D_23f18 ltac:(cond).     (* [comment removed for export] *)
        stepret F_23fe0 D_23fe0 ret ltac:(rwH; reflexivity).
        fin 3%Z (n - 3)%Z.
      - solve_regs_agree. }
    { eexists. split.
      - stepb_ft F_23eec D_23eec ltac:(cond).     (* [comment removed for export] *)
        zsb F_23ef0 D_23ef0 0%Z 1%Z n.            (* [comment removed for export] *)
        sv F_23ef4 D_23ef4 (Z_to_bv 64 (bv_unsigned d + n)).  (* [comment removed for export] *)
        stepn F_23ef8 D_23ef8.                    (* [comment removed for export] *)
        zsb F_23efc D_23efc (n - 1)%Z 1%Z (n - 1)%Z.  (* [comment removed for export] *)
        stepb_ft F_23f00 D_23f00 ltac:(cond).     (* [comment removed for export] *)
        zsb F_23f04 D_23f04 1%Z 2%Z (n - 1)%Z.    (* [comment removed for export] *)
        zsb F_23f08 D_23f08 2%Z 3%Z (n - 1)%Z.    (* [comment removed for export] *)
        stepn F_23f0c D_23f0c.                    (* [comment removed for export] *)
        zsb3 F_23f10 D_23f10 (n - 3)%Z 3%Z (n - 1)%Z (n - 3)%Z (n - 2)%Z.  (* [comment removed for export] *)
        zsb F_23f14 D_23f14 (n - 2)%Z 3%Z (n - 3)%Z.  (* [comment removed for export] *)
        stepb_ft F_23f18 D_23f18 ltac:(cond).     (* [comment removed for export] *)
        zsb F_23f1c D_23f1c 3%Z 4%Z (n - 3)%Z.    (* [comment removed for export] *)
        stepn F_23f20 D_23f20.                    (* [comment removed for export] *)
        zsb F_23f24 D_23f24 (n - 4)%Z 4%Z (n - 4)%Z.  (* [comment removed for export] *)
        stepb_tk F_23f28 D_23f28 ltac:(cond).     (* [comment removed for export] *)
        stepret F_23fe0 D_23fe0 ret ltac:(rwH; reflexivity).
        fin 4%Z (n - 4)%Z.
      - solve_regs_agree. }
  Qed.

  (* [comment removed for export] *)
  Lemma ms_head : forall regs (ret : word),
    getr regs 1 = ret ->
    getr regs 10 = d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 n ->
    (9 <= n)%Z ->
    exists regs',
      msteps SEGS (mkst regs (0x23eec : word) mem0 rom) (mkst regs' (0x23f2c : word) (ZC 4%Z (n - 4)%Z) rom)
      /\ getr regs' 1 = ret /\ getr regs' 10 = d /\ getr regs' 11 = Z_to_bv 64 0
      /\ getr regs' 12 = Z_to_bv 64 n /\ getr regs' 15 = Z_to_bv 64 9
      /\ regs_agree (fun r => In r memset_clob) regs regs'.
  Proof.
    intros regs ret H1 H10 H11 H12 H9.
    pose proof (u64_range d) as Hd.
    replace (mkst regs (0x23eec : word) mem0 rom) with (mkst regs (0x23eec : word) (zc mem0 d n 0 n 0 0) rom)
      by (rewrite zc_init by lia; reflexivity).
    eexists. split.
    - stepb_ft F_23eec D_23eec ltac:(cond).     (* [comment removed for export] *)
      zsb F_23ef0 D_23ef0 0%Z 1%Z n.            (* [comment removed for export] *)
      sv F_23ef4 D_23ef4 (Z_to_bv 64 (bv_unsigned d + n)).  (* [comment removed for export] *)
      stepn F_23ef8 D_23ef8.                    (* [comment removed for export] *)
      zsb F_23efc D_23efc (n - 1)%Z 1%Z (n - 1)%Z.  (* [comment removed for export] *)
      stepb_ft F_23f00 D_23f00 ltac:(cond).     (* [comment removed for export] *)
      zsb F_23f04 D_23f04 1%Z 2%Z (n - 1)%Z.    (* [comment removed for export] *)
      zsb F_23f08 D_23f08 2%Z 3%Z (n - 1)%Z.    (* [comment removed for export] *)
      stepn F_23f0c D_23f0c.                    (* [comment removed for export] *)
      zsb3 F_23f10 D_23f10 (n - 3)%Z 3%Z (n - 1)%Z (n - 3)%Z (n - 2)%Z.  (* [comment removed for export] *)
      zsb F_23f14 D_23f14 (n - 2)%Z 3%Z (n - 3)%Z.  (* [comment removed for export] *)
      stepb_ft F_23f18 D_23f18 ltac:(cond).     (* [comment removed for export] *)
      zsb F_23f1c D_23f1c 3%Z 4%Z (n - 3)%Z.    (* [comment removed for export] *)
      stepn F_23f20 D_23f20.                    (* [comment removed for export] *)
      zsb F_23f24 D_23f24 (n - 4)%Z 4%Z (n - 4)%Z.  (* [comment removed for export] *)
      stepb_ft F_23f28 D_23f28 ltac:(cond).     (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; rwH; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma ms_loop : forall (it : nat) regs (ret : word) a b off m,
    getr regs 1 = ret -> getr regs 11 = Z_to_bv 64 (bv_unsigned d + off) -> getr regs 12 = Z_to_bv 64 0 ->
    getr regs 13 = Z_to_bv 64 31 -> getr regs 14 = Z_to_bv 64 m ->
    (0 <= off)%Z -> (off <= a)%Z -> (off + m <= n)%Z ->
    (32 * (Z.of_nat it + 1) <= m < 32 * (Z.of_nat it + 1) + 32)%Z ->
    exists regs',
      msteps SEGS (mkst regs (0x23fc4 : word) (ZC a b) rom)
                  (mkst regs' (0x23fe0 : word) (ZC (Z.max a (off + 32 * (Z.of_nat it + 1))) b) rom)
      /\ getr regs' 1 = ret /\ regs_agree (fun r => In r memset_clob) regs regs'.
  Proof.
    induction it as [|it IH]; intros regs ret a b off m H1 H11 H12 H13 H14 Hoff Ha Hm Hit;
      pose proof (u64_range d) as Hd.
    - eexists. split.
      + zsd F_23fc4 D_23fc4 off (Z.max a (off + 8)) b.          (* [comment removed for export] *)
        zsd F_23fc8 D_23fc8 (off + 8)%Z (Z.max a (off + 16)) b.  (* [comment removed for export] *)
        zsd F_23fcc D_23fcc (off + 16)%Z (Z.max a (off + 24)) b. (* [comment removed for export] *)
        zsd F_23fd0 D_23fd0 (off + 24)%Z (Z.max a (off + 32)) b. (* [comment removed for export] *)
        sv F_23fd4 D_23fd4 (Z_to_bv 64 (m - 32)).                (* [comment removed for export] *)
        sv F_23fd8 D_23fd8 (Z_to_bv 64 (bv_unsigned d + (off + 32))).  (* [comment removed for export] *)
        stepb_ft F_23fdc D_23fdc ltac:(cond).                     (* [comment removed for export] *)
        replace (off + 32 * (Z.of_nat 0 + 1))%Z with (off + 32)%Z by lia.
        apply mst_refl.
      + split; [gres; rwH; reflexivity | solve_regs_agree].
    - eapply (runs_trans SEGS _ (fun r => mkst r (0x23fc4 : word) (ZC (Z.max a (off + 32)) b) rom)
               (fun r => getr r 1 = ret /\ getr r 11 = Z_to_bv 64 (bv_unsigned d + (off + 32)) /\ getr r 12 = Z_to_bv 64 0
                         /\ getr r 13 = Z_to_bv 64 31 /\ getr r 14 = Z_to_bv 64 (m - 32)
                         /\ regs_agree (fun r => In r memset_clob) regs r)).
      + eexists. split.
        * zsd F_23fc4 D_23fc4 off (Z.max a (off + 8)) b.
          zsd F_23fc8 D_23fc8 (off + 8)%Z (Z.max a (off + 16)) b.
          zsd F_23fcc D_23fcc (off + 16)%Z (Z.max a (off + 24)) b.
          zsd F_23fd0 D_23fd0 (off + 24)%Z (Z.max a (off + 32)) b.
          sv F_23fd4 D_23fd4 (Z_to_bv 64 (m - 32)).
          sv F_23fd8 D_23fd8 (Z_to_bv 64 (bv_unsigned d + (off + 32))).
          stepb_tk F_23fdc D_23fdc ltac:(cond).                   (* [comment removed for export] *)
          apply mst_refl.
        * cbv beta. repeat split; gres; rwH; try reflexivity. solve_regs_agree.
      + cbv beta. intros r1 (R1 & R11 & R12 & R13 & R14 & K1).
        destruct (IH r1 ret (Z.max a (off + 32)) b (off + 32)%Z (m - 32)%Z R1 R11 R12 R13 R14
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & P1 & P2).
        exists r2. split; [|split; [exact P1 | eapply regs_agree_trans; eassumption]].
        replace (Z.max a (off + 32 * (Z.of_nat (S it) + 1)))%Z
           with (Z.max (Z.max a (off + 32)) (off + 32 + 32 * (Z.of_nat it + 1)))%Z by lia.
        exact RUN.
  Qed.

  (* [comment removed for export] *)
  Lemma ms_big : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 n -> getr regs 15 = Z_to_bv 64 9 ->
    (9 <= n)%Z ->
    exists regs',
      msteps SEGS (mkst regs (0x23f2c : word) (ZC 4%Z (n - 4)%Z) rom) (mkst regs' ret FIN rom)
      /\ regs_agree (fun r => In r memset_clob) regs regs'.
  Proof.
    intros regs ret Hret H1 H10 H11 H12 H15 H9.
    pose proof (u64_range d) as Hd.
    destruct (v_andi3 (v_subw (Z_to_bv 64 0) d)) as [EK HK].
    set (k := Z.land (bv_unsigned (v_subw (Z_to_bv 64 0) d)) 3) in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (Hq : exists q, ((n - k) mod 4 = n - k - 4 * q /\ 4 * q <= n - k < 4 * q + 4)%Z).
    { exists ((n - k) / 4)%Z. pose proof (Z.div_mod (n - k) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (n - k) 4 ltac:(lia)). lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    destruct Hq as (q & Hmod & Hq).
    destruct (v_andi4 (Z_to_bv 64 (bv_unsigned d + k))) as (e & He & EE).
    (* [comment removed for export] *)
    Ltac pre EK Hmod EE k q :=
      stepn F_23f2c D_23f2c;                                   (* [comment removed for export] *)
      stepn F_23f30 D_23f30;                                   (* [comment removed for export] *)
      stepn F_23f34 D_23f34;                                   (* [comment removed for export] *)
      stepiv F_23f38 D_23f38 (Z_to_bv 64 k) ltac:(gres; rwH; imm_norm; exact EK);   (* [comment removed for export] *)
      stepn F_23f3c D_23f3c;                                   (* [comment removed for export] *)
      sv F_23f40 D_23f40 (Z_to_bv 64 (n - k));                 (* [comment removed for export] *)
      sv F_23f44 D_23f44 (Z_to_bv 64 (bv_unsigned d + k));     (* [comment removed for export] *)
      stepn F_23f48 D_23f48;                                   (* [comment removed for export] *)
      stepiv F_23f4c D_23f4c (Z_to_bv 64 (4 * q))
        ltac:(gres; rwH; imm_norm; rewrite v_andi_m4 by lia; f_equal; lia);  (* [comment removed for export] *)
      stepn F_23f50 D_23f50;                                   (* [comment removed for export] *)
      zsw F_23f54 D_23f54 k (k + 4)%Z (n - 4)%Z;               (* [comment removed for export] *)
      sv F_23f58 D_23f58 (Z_to_bv 64 (bv_unsigned d + (k + 4 * q)));   (* [comment removed for export] *)
      zsw F_23f5c D_23f5c (k + 4 * q - 4)%Z (k + 4)%Z (k + 4 * q - 4)%Z.  (* [comment removed for export] *)
    destruct (Z_lt_le_dec (4 * q) 9) as [Hq9|Hq9].
    { eexists. split.
      - pre EK Hmod EE k q.
        stepb_tk F_23f60 D_23f60 ltac:(cond).                  (* [comment removed for export] *)
        stepret F_23fe0 D_23fe0 ret ltac:(rwH; reflexivity).
        fin (k + 4)%Z (k + 4 * q - 4)%Z.
      - solve_regs_agree. }
    Ltac mid k q :=
      stepb_ft F_23f60 D_23f60 ltac:(cond);                    (* [comment removed for export] *)
      zsw F_23f64 D_23f64 (k + 4)%Z (k + 8)%Z (k + 4 * q - 4)%Z;     (* [comment removed for export] *)
      zsw F_23f68 D_23f68 (k + 8)%Z (k + 12)%Z (k + 4 * q - 4)%Z;    (* [comment removed for export] *)
      stepn F_23f6c D_23f6c;                                   (* [comment removed for export] *)
      zsw3 F_23f70 D_23f70 (k + 4 * q - 12)%Z (k + 12)%Z (k + 4 * q - 4)%Z (k + 4 * q - 12)%Z (k + 4 * q - 8)%Z;  (* [comment removed for export] *)
      zsw F_23f74 D_23f74 (k + 4 * q - 8)%Z (k + 12)%Z (k + 4 * q - 12)%Z.   (* [comment removed for export] *)
    destruct (Z_lt_le_dec (4 * q) 25) as [Hq25|Hq25].
    { eexists. split.
      - pre EK Hmod EE k q. mid k q.
        stepb_tk F_23f78 D_23f78 ltac:(cond).                  (* [comment removed for export] *)
        stepret F_23fe0 D_23fe0 ret ltac:(rwH; reflexivity).
        fin (k + 12)%Z (k + 4 * q - 12)%Z.
      - solve_regs_agree. }
    Ltac mid2 EE e k q :=
      stepb_ft F_23f78 D_23f78 ltac:(cond);                    (* [comment removed for export] *)
      zsw F_23f7c D_23f7c (k + 12)%Z (k + 16)%Z (k + 4 * q - 12)%Z;   (* [comment removed for export] *)
      zsw F_23f80 D_23f80 (k + 16)%Z (k + 20)%Z (k + 4 * q - 12)%Z;   (* [comment removed for export] *)
      zsw F_23f84 D_23f84 (k + 20)%Z (k + 24)%Z (k + 4 * q - 12)%Z;   (* [comment removed for export] *)
      zsw F_23f88 D_23f88 (k + 24)%Z (k + 28)%Z (k + 4 * q - 12)%Z;   (* [comment removed for export] *)
      stepiv F_23f8c D_23f8c (Z_to_bv 64 e) ltac:(gres; rwH; imm_norm; exact EE);  (* [comment removed for export] *)
      stepn F_23f90 D_23f90;                                   (* [comment removed for export] *)
      sv F_23f94 D_23f94 (Z_to_bv 64 (e + 24));                (* [comment removed for export] *)
      sv F_23f98 D_23f98 (Z_to_bv 64 (4 * q - e - 24));        (* [comment removed for export] *)
      zsw3 F_23f9c D_23f9c (k + 4 * q - 28)%Z (k + 28)%Z (k + 4 * q - 12)%Z (k + 4 * q - 28)%Z (k + 4 * q - 24)%Z;  (* [comment removed for export] *)
      zsw3 F_23fa0 D_23fa0 (k + 4 * q - 24)%Z (k + 28)%Z (k + 4 * q - 12)%Z (k + 4 * q - 28)%Z (k + 4 * q - 20)%Z;  (* [comment removed for export] *)
      zsw3 F_23fa4 D_23fa4 (k + 4 * q - 20)%Z (k + 28)%Z (k + 4 * q - 12)%Z (k + 4 * q - 28)%Z (k + 4 * q - 16)%Z;  (* [comment removed for export] *)
      zsw F_23fa8 D_23fa8 (k + 4 * q - 16)%Z (k + 28)%Z (k + 4 * q - 28)%Z.  (* [comment removed for export] *)
    destruct (Z_lt_le_dec (4 * q - e - 24) 32) as [Hq32|Hq32].
    { eexists. split.
      - pre EK Hmod EE k q. mid k q. mid2 EE e k q.
        stepb_tk F_23fac D_23fac ltac:(cond).                  (* [comment removed for export] *)
        stepret F_23fe0 D_23fe0 ret ltac:(rwH; reflexivity).
        fin (k + 28)%Z (k + 4 * q - 28)%Z.
      - solve_regs_agree. }
    (* [comment removed for export] *)
    set (m := (4 * q - e - 24)%Z).
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    assert (Hit : exists it : nat, ((32 * (Z.of_nat it + 1) <= m < 32 * (Z.of_nat it + 1) + 32)
                   /\ (m - 32 * (Z.of_nat it + 1) <= 28))%Z).
    { exists (Z.to_nat (m / 32 - 1)). rewrite Z2Nat.id by (apply Z.le_0_sub, Z.div_le_lower_bound; lia).
      pose proof (Z.div_mod m 32 ltac:(lia)). pose proof (Z.mod_pos_bound m 32 ltac:(lia)). subst m. lia. }
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    destruct Hit as (it & Hit & Hrem).
    eapply (runs_trans SEGS _ (fun r => mkst r (0x23fc4 : word) (ZC (k + 28)%Z (k + 4 * q - 28)%Z) rom)
             (fun r => getr r 1 = ret /\ getr r 11 = Z_to_bv 64 (bv_unsigned d + (k + e + 24)) /\ getr r 12 = Z_to_bv 64 0
                       /\ getr r 13 = Z_to_bv 64 31 /\ getr r 14 = Z_to_bv 64 m
                       /\ regs_agree (fun r => In r memset_clob) regs r)).
    - eexists. split.
      + pre EK Hmod EE k q. mid k q. mid2 EE e k q.
        stepb_ft F_23fac D_23fac ltac:(cond).                  (* [comment removed for export] *)
        stepn F_23fb0 D_23fb0.                                 (* [comment removed for export] *)
        sv F_23fb4 D_23fb4 (Z_to_bv 64 (bv_unsigned d + (k + e + 24))).  (* [comment removed for export] *)
        stepn F_23fb8 D_23fb8.                                 (* [comment removed for export] *)
        stepn F_23fbc D_23fbc.                                 (* [comment removed for export] *)
        stepn F_23fc0 D_23fc0.                                 (* [comment removed for export] *)
        apply mst_refl.
      + cbv beta. subst m. repeat split; gres; rwH; try reflexivity. solve_regs_agree.
    - cbv beta. intros r1 (R1 & R11 & R12 & R13 & R14 & K1).
      eapply (runs_trans SEGS _ (fun r => mkst r (0x23fe0 : word) (ZC (Z.max (k + 28) (k + e + 24 + 32 * (Z.of_nat it + 1)))%Z (k + 4 * q - 28)%Z) rom)
               (fun r => getr r 1 = ret /\ regs_agree (fun r => In r memset_clob) regs r)).
      + destruct (ms_loop it r1 ret (k + 28)%Z (k + 4 * q - 28)%Z (k + e + 24)%Z m R1 R11 R12 R13 R14
                   ltac:(lia) ltac:(lia) ltac:(subst m; lia) Hit) as (r2 & RUN & P1 & P2).
        exists r2. split; [exact RUN | split; [exact P1 | eapply regs_agree_trans; eassumption]].
      + cbv beta. intros r2 (S1 & K2).
        eexists. split.
        * stepret F_23fe0 D_23fe0 ret ltac:(rwH; reflexivity).
          subst m. fin (Z.max (k + 28) (k + e + 24 + 32 * (Z.of_nat it + 1)))%Z (k + 4 * q - 28)%Z.
        * exact K2.
  Qed.

  (* [comment removed for export] *)
  Theorem ref_memset0 : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret ->
    getr regs 10 = d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 n ->
    exists regs',
      msteps SEGS (mkst regs (0x23eec : word) mem0 rom) (mkst regs' ret FIN rom)
      /\ regs_agree (fun r => In r memset_clob) regs regs'.
  Proof.
    intros regs ret Hret H1 H10 H11 H12.
    destruct (Z_lt_le_dec n 9) as [H9|H9].
    - apply ms_small; try assumption. lia.
    - eapply (runs_trans SEGS _ (fun r => mkst r (0x23f2c : word) (ZC 4%Z (n - 4)%Z) rom)
               (fun r => getr r 1 = ret /\ getr r 10 = d /\ getr r 11 = Z_to_bv 64 0
                         /\ getr r 12 = Z_to_bv 64 n /\ getr r 15 = Z_to_bv 64 9
                         /\ regs_agree (fun r => In r memset_clob) regs r)).
      + apply ms_head; assumption.
      + cbv beta. intros r1 (R1 & R10 & R11 & R12 & R15 & K1).
        destruct (ms_big r1 ret Hret R1 R10 R11 R12 R15 H9) as (r2 & RUN & K2).
        exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
  Qed.
End MS.

(* [comment removed for export] *)
Corollary ref_memset0_keeps : forall mem0 (d : word) (n : Z) rom regs (ret : word),
  (0 <= n)%Z -> (bv_unsigned d + n < 2 ^ 64)%Z -> store_ok SEGS mem0 d (Z.to_nat n) = true ->
  ret_ok ret -> getr regs 1 = ret ->
  getr regs 10 = d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 n ->
  exists regs',
    msteps SEGS (mkst regs (0x23eec : word) mem0 rom)
                (mkst regs' ret (wbytes mem0 d (zeros (Z.to_nat n))) rom)
    /\ keeps regs regs'.
Proof.
  intros mem0 d n rom regs ret Hn Hnw Hok Hret H1 H10 H11 H12.
  destruct (ref_memset0 mem0 d n rom Hn Hnw Hok regs ret Hret H1 H10 H11 H12) as (r & RUN & AG).
  exists r. split; [exact RUN|].
  intros x Hx. apply AG. intros Hin. unfold memset_clob in Hin. unfold callee_kept in Hx. cbn [In] in Hin, Hx.
  decompose [or] Hin; subst; try contradiction;
    repeat (destruct Hx as [Hx|Hx]; [apply bv_eq in Hx; cbv in Hx; discriminate Hx|]); exact Hx.
Qed.

(* [comment removed for export] *)
Lemma memset304_run : forall regs (mem rom : word -> option byte) (d ret : word),
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = d -> getr regs 11 = Z_to_bv 64 0 -> getr regs 12 = Z_to_bv 64 304 ->
  (bv_unsigned d mod 8 = 0)%Z ->
  (bv_unsigned d + 304 < 2^64)%Z ->
  store_ok SEGS mem d 304 = true ->
  exists regs' mem',
    msteps SEGS (mkst regs (0x23eec : word) mem rom) (mkst regs' ret mem' rom)
    /\ mem' = wbytes mem d (zeros 304)
    /\ regs_agree (fun r => In r memset_clob) regs regs'.
Proof.
  intros regs mem rom d ret H1 Hret H10 H11 H12 _ Hnw Hok.
  destruct (ref_memset0 mem d 304 rom ltac:(lia) Hnw Hok regs ret Hret H1 H10 H11 H12) as (r & RUN & AG).
  exists r, (wbytes mem d (zeros 304)). split; [exact RUN | split; [reflexivity | exact AG]].
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
