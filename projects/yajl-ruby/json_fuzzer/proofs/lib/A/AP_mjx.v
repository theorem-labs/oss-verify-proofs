(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import AM_kit AI_shadow AI_globals2 AI_gtrans AI_lowshadow AP_policy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition stack_shadow_zero (m : mem) : Prop :=
  forall a, A_HSH_LO <= a < A_HSH_HI -> mrd asegs m (wa a) = Some (Z_to_bv 8 0).

Definition mjx (m : mem) : Prop :=
  icp_globals asegs m 0x7fff8000 /\ icp_globals2 asegs m /\ low_shadow_ok m /\ stack_shadow_zero m.

Lemma mjx_g : forall m, mjx m -> icp_globals asegs m 0x7fff8000. Proof. intros m H; exact (proj1 H). Qed.
Lemma mjx_g2 : forall m, mjx m -> icp_globals2 asegs m. Proof. intros m H; exact (proj1 (proj2 H)). Qed.
Lemma mjx_ls : forall m, mjx m -> low_shadow_ok m. Proof. intros m H; exact (proj1 (proj2 (proj2 H))). Qed.
Lemma mjx_ssz : forall m, mjx m -> stack_shadow_zero m. Proof. intros m H; exact (proj2 (proj2 (proj2 H))). Qed.

(* [comment removed for export] *)
Definition mjx_ok_iv (iv : Z * Z) : Prop :=
  (A_CEIL <= fst iv /\ snd iv <= A_STK_HI) \/ (0xa8e18 <= fst iv /\ snd iv <= 0xa9420) \/ (0x5cfdd0 <= fst iv /\ snd iv <= 0x603000).

Lemma disjoint_from_ok : forall W a n, Forall mjx_ok_iv W ->
  (a + n <= 0xa8e18 \/ (0xa9420 <= a /\ a + n <= 0x5cfdd0) \/ (0x603000 <= a /\ a + n <= A_CEIL)) ->
  disjoint_from W a n.
Proof.
  intros W a n HF Ha. unfold A_CEIL, A_STK_HI in *. induction W as [|[lo hi] W IH]; cbn; [exact I|].
  apply Forall_cons_iff in HF. destruct HF as [H1 H2]. unfold mjx_ok_iv, A_CEIL, A_STK_HI in H1. cbn [fst snd] in H1.
  split; [lia| apply IH; exact H2].
Qed.

(* [comment removed for export] *)
Lemma A_HSH_LO_range : 0x10006fef8000 <= A_HSH_LO <= 0x10007ffef000.
Proof.
  unfold A_HSH_LO, A_CEIL. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  set (CE := Z.max 140735340871680 (Z.min 140737488355328 rc_sp) - 8388608).
  assert (CER : 0x7fff7f800000 <= CE <= 0x7fffff800000) by (subst CE; lia). clearbody CE. Z.div_mod_to_equations. lia.
Qed.

Lemma stack_shadow_zero_transport : forall W m m',
  stack_shadow_zero m -> munch W m m' -> Forall mjx_ok_iv W -> stack_shadow_zero m'.
Proof.
  intros W m m' H MU HF a Ha. unfold stack_shadow_zero, A_HSH_HI in *. unfold mrd in *. rewrite (MU (wa a)); [apply H; lia|].
  pose proof A_HSH_LO_range as LOB.
  rewrite wa_unsigned by lia. eapply (disjoint_outside W a 1); [| lia].
  apply disjoint_from_ok; [exact HF| unfold A_CEIL; lia].
Qed.

Lemma mjx_transport : forall W m m', mjx m -> munch W m m' -> wmono asegs m m' -> Forall mjx_ok_iv W -> mjx m'.
Proof.
  intros W m m' (G & G2 & LS & SZ) MU WM HF. split; [|split; [|split]].
  - eapply icp_globals_transport_cells; [exact G| exact MU| exact WM|].
    unfold icp_globals_cells. repeat (apply Forall_cons; [cbn [fst snd]; apply disjoint_from_ok; [exact HF| unfold A_CEIL; lia]|]). apply Forall_nil.
  - eapply icp_globals2_transport_cells; [exact G2| exact MU| exact WM|].
    unfold icp_globals2_cells. repeat (apply Forall_cons; [cbn [fst snd]; apply disjoint_from_ok; [exact HF| unfold A_CEIL; lia]|]). apply Forall_nil.
  - eapply low_shadow_transport; [exact LS| exact MU| exact WM|]. apply disjoint_from_ok; [exact HF| unfold A_CEIL; lia].
  - eapply stack_shadow_zero_transport; [exact SZ| exact MU| exact HF].
Qed.

(* [comment removed for export] *)
Lemma stack_window_span : forall A n, A_CEIL <= A -> 1 <= n -> A + n <= A_STK_HI ->
  A_HSH_LO <= shw_lo 0x7fff8000 A /\ shw_hi 0x7fff8000 A n <= A_HSH_HI /\ shw_lo 0x7fff8000 A + 8 <= shw_hi 0x7fff8000 A n.
Proof.
  intros A n H1 H2 H3. unfold A_HSH_LO, A_HSH_HI, A_CEIL, A_STK_HI in *.
  pose proof (shw_geom 0x7fff8000 A n ltac:(lia) ltac:(lia) H2) as GE; cbv zeta in GE.
  unfold shw_lo, shw_hi, al8 in *. rewrite !Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *.
  set (CE := Z.max 140735340871680 (Z.min 140737488355328 rc_sp) - 8388608) in *.
  assert (CER : 0x7fff7f800000 <= CE <= 0x7fffff800000) by (subst CE; lia). clearbody CE.
  repeat split; Z.div_mod_to_equations; lia.
Qed.

Lemma mjx_stack_window : forall m A n, mjx m -> A_CEIL <= A -> 1 <= n -> A + n <= A_STK_HI ->
  let N := Z.to_nat (shw_hi 0x7fff8000 A n - shw_lo 0x7fff8000 A) in
  shadow_window asegs m 0x7fff8000 A n (repeat (Z_to_bv 8 0) N) /\ range_clean 0x7fff8000 A n (repeat (Z_to_bv 8 0) N).
Proof.
  intros m A n MJ H1 H2 H3. pose proof (stack_window_span A n H1 H2 H3) as (S1 & S2 & S3). cbv zeta.
  pose proof (mjx_ssz m MJ) as SZ. pose proof A_HSH_LO_range as LOB. unfold A_CEIL, A_STK_HI, A_HSH_HI in *.
  split.
  - split.
    + split; [lia|]. split; [rewrite repeat_length; lia|].
      intros i Hi. rewrite repeat_length in Hi. rewrite nth_error_repeat by exact Hi.
      apply SZ. unfold A_HSH_HI. lia.
    + rewrite repeat_length. lia.
  - intros g Hg. pose proof (shw_geom 0x7fff8000 A n ltac:(lia) ltac:(lia) H2) as GE; cbv zeta in GE.
    exists (Z_to_bv 8 0). split; [| left; reflexivity]. apply nth_error_repeat. lia.
Qed.

Lemma mjx_rodata_window0 : forall m A n, mjx m -> 0x10000 <= A -> 1 <= n -> A + n <= 0x21000 ->
  let N := Z.to_nat (shw_hi 0x7fff8000 A n - shw_lo 0x7fff8000 A) in
  shadow_window asegs m 0x7fff8000 A n (repeat (Z_to_bv 8 0) N) /\ range_clean 0x7fff8000 A n (repeat (Z_to_bv 8 0) N).
Proof.
  intros m A n MJ H1 H2 H3. cbv zeta. pose proof (mjx_ls m MJ) as LS.
  pose proof (shw_geom 0x7fff8000 A n ltac:(lia) ltac:(lia) H2) as GE; cbv zeta in GE.
  assert (SP : 0x7fffa000 <= shw_lo 0x7fff8000 A /\ shw_hi 0x7fff8000 A n <= 0x7fffc204).
  { unfold shw_lo, shw_hi, al8 in *. rewrite !Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *. split; Z.div_mod_to_equations; lia. }
  split.
  - split; [| rewrite repeat_length; lia].
    rewrite <- (low_shadow_bytes_zero (shw_lo 0x7fff8000 A)) by (left; lia).
    apply low_shadow_bytes_at; [exact LS| lia | lia].
  - intros g Hg. exists (Z_to_bv 8 0). split; [| left; reflexivity]. apply nth_error_repeat. lia.
Qed.

Lemma mjx_statics_window : forall m A n, mjx m -> 0x5cfdd0 <= A -> 1 <= n -> A + n <= 0x603000 ->
  exists ws, shadow_window asegs m 0x7fff8000 A n ws /\ range_clean 0x7fff8000 A n ws.
Proof. intros m A n MJ H1 H2 H3. apply musl_statics_shadow_clean; [exact (mjx_ls m MJ)| lia| lia| lia]. Qed.
End RC__1.
