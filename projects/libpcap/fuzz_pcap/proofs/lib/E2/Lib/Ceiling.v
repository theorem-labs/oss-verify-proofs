(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Export LiaTuning.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition CEIL_LO : Z := 0x7fff7f800000.
Definition CEIL_HI : Z := 0x7fffff800000.

Class CEIL : Type := {
  alloc_ceiling : Z ;
  ceil_floor : CEIL_LO <= alloc_ceiling ;
  ceil_max : alloc_ceiling <= CEIL_HI ;
  ceil_pg : alloc_ceiling mod 4096 = 0
}.

Lemma CEIL_LO_val : CEIL_LO = 0x7fff7f800000. Proof. reflexivity. Qed.
Lemma CEIL_HI_val : CEIL_HI = 0x7fffff800000. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac ceil_bounds :=
  lazymatch goal with
  | CE : CEIL |- _ =>
      pose proof (@ceil_floor CE); pose proof (@ceil_max CE); pose proof (@ceil_pg CE);
      rewrite CEIL_LO_val in *; rewrite CEIL_HI_val in *
  end.

(* [comment removed for export] *)
Ltac ceil_facts :=
  lazymatch goal with
  | CE : CEIL |- _ =>
      first [ pose proof (@ceil_floor CE) as CEILF__; pose proof (@ceil_max CE) as CEILM__;
              pose proof (@ceil_pg CE) as CEILP__;
              rewrite CEIL_LO_val in CEILF__; rewrite CEIL_HI_val in CEILM__
            | idtac ]
  | |- _ => idtac
  end.

Section Facts.
Context {CE : CEIL}.

#[using="Type"] Lemma alloc_ceiling_window : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof. ceil_bounds. lia. Qed.
#[using="Type"] Lemma alloc_ceiling_pos : 0 < alloc_ceiling.
Proof. ceil_bounds. lia. Qed.
#[using="Type"] Lemma alloc_ceiling_lt47 : alloc_ceiling < 2^47.
Proof. ceil_bounds. lia. Qed.
#[using="Type"] Lemma alloc_ceiling_lt63 : alloc_ceiling < 2^63.
Proof. ceil_bounds. lia. Qed.
#[using="Type"] Lemma alloc_ceiling_lt64 : alloc_ceiling + 8388608 <= 2^64 - 4096.
Proof. ceil_bounds. lia. Qed.
#[using="Type"] Lemma alloc_ceiling_page : alloc_ceiling mod 4096 = 0.
Proof. exact ceil_pg. Qed.
#[using="Type"] Lemma alloc_ceiling_page_size : alloc_ceiling mod page_size = 0.
Proof. unfold page_size. exact ceil_pg. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma alloc_ceiling_window' : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000 /\ alloc_ceiling mod 4096 = 0.
Proof. ceil_facts. ceil_facts; split; [lia| exact CEILP__]. Qed.

End Facts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma page_round_down_Z_le : forall x, 0 <= x -> page_round_down_Z x <= x.
Proof. intros x Hx. unfold page_round_down_Z, page_size. pose proof (Z_div_mod_eq_full x 4096). pose proof (Z.mod_pos_bound x 4096). lia. Qed.
Lemma page_round_down_Z_gt : forall x, x - 4096 < page_round_down_Z x.
Proof. intros x. unfold page_round_down_Z, page_size. pose proof (Z_div_mod_eq_full x 4096). pose proof (Z.mod_pos_bound x 4096). lia. Qed.
Lemma page_round_down_Z_mod : forall x, page_round_down_Z x mod 4096 = 0.
Proof. intros x. unfold page_round_down_Z, page_size. apply Z_mod_mult. Qed.
Lemma page_round_down_Z_mono : forall x y, x <= y -> page_round_down_Z x <= page_round_down_Z y.
Proof. intros x y H. unfold page_round_down_Z, page_size. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; lia. Qed.
Lemma page_round_down_Z_id : forall x, x mod 4096 = 0 -> page_round_down_Z x = x.
Proof. intros x H. unfold page_round_down_Z, page_size. pose proof (Z_div_mod_eq_full x 4096). lia. Qed.
(* [comment removed for export] *)
Lemma page_round_down_Z_ge_aligned : forall a x, a mod 4096 = 0 -> a <= x -> a <= page_round_down_Z x.
Proof.
  intros a x Ha Hle. rewrite <- (page_round_down_Z_id a Ha). apply page_round_down_Z_mono. exact Hle.
Qed.

(* [comment removed for export] *)
Definition ceil_raw (sp0 : word) : Z := page_round_down_Z (bv_unsigned sp0 - stack_max_size).
Definition ceil_val (sp0 : word) : Z := Z.max CEIL_LO (Z.min CEIL_HI (ceil_raw sp0)).

Lemma ceil_raw_window : forall sp0, valid_sp sp0 -> CEIL_LO <= ceil_raw sp0 <= CEIL_HI.
Proof.
  intros sp0 (Hlo & Hhi & _). unfold ceil_raw, CEIL_LO, CEIL_HI. rewrite stack_max_size_val.
  unfold sp_window_lo in Hlo. unfold sp_window_hi in Hhi. split.
  - apply page_round_down_Z_ge_aligned; [reflexivity| lia].
  - eapply Z.le_trans; [apply page_round_down_Z_le; lia| lia].
Qed.
Lemma ceil_val_eq : forall sp0, valid_sp sp0 -> ceil_val sp0 = page_round_down_Z (bv_unsigned sp0 - stack_max_size).
Proof. intros sp0 H. pose proof (ceil_raw_window sp0 H). unfold ceil_val. fold (ceil_raw sp0). lia. Qed.
Lemma ceil_val_floor : forall sp0, CEIL_LO <= ceil_val sp0.
Proof. intros sp0. unfold ceil_val. lia. Qed.
Lemma ceil_val_max : forall sp0, ceil_val sp0 <= CEIL_HI.
Proof. intros sp0. unfold ceil_val, CEIL_LO, CEIL_HI. lia. Qed.
Lemma ceil_val_pg : forall sp0, ceil_val sp0 mod 4096 = 0.
Proof.
  intros sp0. unfold ceil_val.
  destruct (Z.max_spec CEIL_LO (Z.min CEIL_HI (ceil_raw sp0))) as [[_ ->]|[_ ->]]; [| reflexivity].
  destruct (Z.min_spec CEIL_HI (ceil_raw sp0)) as [[_ ->]|[_ ->]]; [reflexivity|].
  unfold ceil_raw. apply page_round_down_Z_mod.
Qed.

Definition ceil_of_sp (sp0 : word) : CEIL :=
  {| alloc_ceiling := ceil_val sp0 ;
     ceil_floor := ceil_val_floor sp0 ;
     ceil_max := ceil_val_max sp0 ;
     ceil_pg := ceil_val_pg sp0 |}.

Lemma alloc_ceiling_of_sp : forall sp0, valid_sp sp0 ->
  @alloc_ceiling (ceil_of_sp sp0) = page_round_down_Z (bv_unsigned sp0 - stack_max_size).
Proof. intros sp0 H. cbn [alloc_ceiling ceil_of_sp]. apply ceil_val_eq. exact H. Qed.

(* [comment removed for export] *)
Lemma ceil_of_sp_le_top : forall sp0, valid_sp sp0 ->
  @alloc_ceiling (ceil_of_sp sp0) <= bv_unsigned sp0 - stack_max_size.
Proof.
  intros sp0 H. rewrite (alloc_ceiling_of_sp sp0 H). apply page_round_down_Z_le.
  destruct H as (Hlo & _ & _). unfold sp_window_lo in Hlo. rewrite stack_max_size_val. lia.
Qed.

(* [comment removed for export] *)
Lemma grant_below_ceil_of_sp : forall sp0 a n, valid_sp sp0 ->
  a mod 4096 = 0 -> n mod 4096 = 0 ->
  a + n <= bv_unsigned sp0 - stack_max_size ->
  a + n <= @alloc_ceiling (ceil_of_sp sp0).
Proof.
  intros sp0 a n H Ha Hn Hle. rewrite (alloc_ceiling_of_sp sp0 H).
  apply page_round_down_Z_ge_aligned; [| exact Hle].
  rewrite Z.add_mod, Ha, Hn by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma alloc_top_ceil_of_sp : forall sp0 h, valid_sp sp0 ->
  vm_init_sp h = sp0 -> page_round_down_Z (alloc_top h) = @alloc_ceiling (ceil_of_sp sp0).
Proof. intros sp0 h H E. rewrite (alloc_ceiling_of_sp sp0 H). unfold alloc_top. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
Lemma alloc_top_ceil_bracket : forall sp0 h, valid_sp sp0 -> vm_init_sp h = sp0 ->
  alloc_top h - 4096 < @alloc_ceiling (ceil_of_sp sp0) <= alloc_top h.
Proof.
  intros sp0 h H E. rewrite <- (alloc_top_ceil_of_sp sp0 h H E). split; [apply page_round_down_Z_gt| apply page_round_down_Z_le].
  pose proof (ceil_raw_window sp0 H) as W. unfold ceil_raw, CEIL_LO in W. unfold alloc_top. rewrite E.
  pose proof (page_round_down_Z_le (bv_unsigned sp0 - stack_max_size)). rewrite stack_max_size_val in *.
  destruct H as (Hlo & _ & _). unfold sp_window_lo in Hlo. lia.
Qed.
