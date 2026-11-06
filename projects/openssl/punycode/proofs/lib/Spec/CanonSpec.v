(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import CatSim ShapeAlg.
From OSSVerify.Proofs.openssl.punycode.lib.Spec Require Import Prelim Canon.
From OSSVerify.Proofs.openssl.punycode.lib Require Import ClaVerdict Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)

Lemma emit_exit_iff : forall evs code fs tr,
  t_emit evs (t_exit code fs) tr <-> is_prefix tr (evs ++ [ExitEv code fs]).
Proof.
  intros evs code fs tr. unfold t_exit, t_emit, t_nil. split.
  - intros [Hp|(tr' & -> & [Hp|(tr'' & -> & ->)])].
    + apply is_prefix_app_r. exact Hp.
    + apply CatSim.is_prefix_app_mono. exact Hp.
    + rewrite app_nil_r. apply is_prefix_refl.
  - intros Hp. apply is_prefix_app_split in Hp as [Hp|(b' & -> & Hp)]; [left; exact Hp|].
    right. exists b'. split; [reflexivity|]. left. exact Hp.
Qed.

(* [comment removed for export] *)

Lemma bytes_roundtrip : forall l : list byte, map (Z_to_bv 8) (map bv_unsigned l) = l.
Proof. induction l as [|b l IH]; cbn; [reflexivity|]. rewrite IH, Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma str_s2b : forall s, map (Z_to_bv 8) (str s) = s2b s.
Proof.
  intros s. unfold str, s2b. rewrite map_map. apply map_ext. intros a.
  f_equal. unfold nat_of_ascii. rewrite N_nat_Z. reflexivity.
Qed.

Lemma evw_W : forall fd bs, evw fd bs = W fd (map (Z_to_bv 8) bs).
Proof. intros fd bs. unfold evw, W. rewrite map_map. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ct_die : forall fs (msgZ : list Z) (msg : list byte) tr,
  map (Z_to_bv 8) msgZ = msg ->
  (is_prefix tr (ct_events fs (mkCT 2 msgZ 2)) <-> t_die msg fs tr).
Proof.
  intros fs msgZ msg tr <-. unfold ct_events, t_die, exit_code. cbn [ct_fd ct_bytes ct_code].
  rewrite evw_W. symmetry. apply emit_exit_iff.
Qed.

Lemma msg_usage_eq : forall a0 : list byte, map (Z_to_bv 8) (Canon.msg_usage (map bv_unsigned a0)) = Spec.msg_usage a0.
Proof.
  intros a0. unfold Canon.msg_usage, Spec.msg_usage. rewrite !map_app, !str_s2b, bytes_roundtrip. reflexivity.
Qed.
Lemma msg_cannot_open_eq : forall p : list byte, map (Z_to_bv 8) (Canon.msg_cannot_open (map bv_unsigned p)) = Spec.msg_cannot_open p.
Proof.
  intros p. unfold Canon.msg_cannot_open, Spec.msg_cannot_open. rewrite !map_app, !str_s2b, bytes_roundtrip. reflexivity.
Qed.
Lemma msg_read_error_eq : forall p : list byte, map (Z_to_bv 8) (Canon.msg_read_error (map bv_unsigned p)) = Spec.msg_read_error p.
Proof.
  intros p. unfold Canon.msg_read_error, Spec.msg_read_error. rewrite !map_app, !str_s2b, bytes_roundtrip. reflexivity.
Qed.
Lemma msg_too_big_eq : map (Z_to_bv 8) msg_too_big = msg_refused.
Proof. unfold msg_too_big, msg_refused. rewrite !map_app, !str_s2b. reflexivity. Qed.
Lemma msg_short_eq : map (Z_to_bv 8) msg_short_hdr = msg_short.
Proof. unfold msg_short_hdr, msg_short. rewrite !map_app, !str_s2b. reflexivity. Qed.
Lemma msg_overrun_eq : map (Z_to_bv 8) msg_cfg_overrun = msg_overrun.
Proof. unfold msg_cfg_overrun, msg_overrun. rewrite !map_app, !str_s2b. reflexivity. Qed.

Lemma zeros_out_lines : forall n, map (Z_to_bv 8) (zeros_out n) = zero_lines n.
Proof.
  induction n as [|n IH]; [reflexivity|]. rewrite zeros_out_S, map_app, IH. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma znth_bytes : forall (data : list byte) (i : Z), 0 <= i -> znth (map bv_unsigned data) i = byte_at data (Z.to_nat i).
Proof.
  intros data i Hi. unfold znth, byte_at. destruct (Z.ltb_spec i 0); [lia|].
  change 0 with (bv_unsigned (Z_to_bv 8 0)) at 1. apply map_nth.
Qed.

Lemma byte_at_range : forall data i, 0 <= byte_at data i < 256.
Proof. intros data i. unfold byte_at. pose proof (bv_unsigned_in_range 8 (nth i data (Z_to_bv 8 0))) as H. exact H. Qed.

Lemma cfg_len_eq : forall data : list byte, cfg_len (map bv_unsigned data) = Z.of_nat (config_len data).
Proof.
  intros data. unfold cfg_len, config_len, cfg_word.
  rewrite (znth_bytes data 0), (znth_bytes data 1) by lia. change (Z.to_nat 0) with 0%nat. change (Z.to_nat 1) with 1%nat.
  pose proof (byte_at_range data 0). pose proof (byte_at_range data 1).
  change 0x7fff with (Z.ones 15). rewrite Z.land_ones by lia. change (2 ^ 15) with 32768.
  replace (byte_at data 0 + byte_at data 1 * 256) with (byte_at data 0 + 256 * byte_at data 1) by lia.
  rewrite Z2Nat.id; [reflexivity|]. apply Z.mod_pos_bound. lia.
Qed.

Lemma cfg_calls_eq : forall data : list byte, cfg_calls (map bv_unsigned data) = calls_of data.
Proof.
  intros data. unfold cfg_calls, calls_of. rewrite cfg_len_eq.
  destruct (config_len data) as [|k] eqn:E.
  - reflexivity.
  - replace (0 <? Z.of_nat (S k)) with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite (znth_bytes data 2) by lia. change (Z.to_nat 2) with 2%nat. pose proof (byte_at_range data 2).
    change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
    pose proof (Z.mod_pos_bound (byte_at data 2) 4 ltac:(lia)).
    rewrite Z2Nat.inj_add by lia. rewrite Nat.add_comm. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma file_trace_body : forall (data : list byte) fs tr,
  is_prefix tr (ct_events fs (file_trace (map bv_unsigned data))) <-> t_body data fs tr.
Proof.
  intros data fs tr. unfold file_trace, t_body, t_body_cfg, zlength. rewrite length_map, cfg_len_eq.
  change 67108864 with MAX_INPUT.
  destruct (MAX_INPUT <=? Z.of_nat (length data)) eqn:E1; [apply ct_die; exact msg_too_big_eq|].
  destruct (Nat.ltb_spec (length data) HDR_MIN) as [E2|E2].
  { replace (Z.of_nat (length data) <? 6) with true by (symmetry; apply Z.ltb_lt; unfold HDR_MIN in E2; lia).
    apply ct_die. exact msg_short_eq. }
  replace (Z.of_nat (length data) <? 6) with false by (symmetry; apply Z.ltb_ge; unfold HDR_MIN in E2; lia).
  destruct (Nat.ltb_spec (length data) (HDR_MIN + config_len data)) as [E3|E3].
  { replace (Z.of_nat (length data) <? 6 + Z.of_nat (config_len data)) with true
      by (symmetry; apply Z.ltb_lt; unfold HDR_MIN in E3; lia).
    apply ct_die. exact msg_overrun_eq. }
  replace (Z.of_nat (length data) <? 6 + Z.of_nat (config_len data)) with false
    by (symmetry; apply Z.ltb_ge; unfold HDR_MIN in E3; lia).
  unfold ct_events, t_target, exit_code. cbn [ct_fd ct_bytes ct_code].
  rewrite evw_W, cfg_calls_eq, zeros_out_lines. symmetry. apply emit_exit_iff.
Qed.

(* [comment removed for export] *)

Theorem canon_spec_eq : forall (argv : list (list byte)) (fs : Fs.Fs),
  t_eq (canonT (map (map bv_unsigned) argv) fs) (Spec.spec argv fs).
Proof.
  intros argv fs tr. rewrite canonT_iff. unfold Spec.spec, spec_cfg, ctrace_of, drv_classify.
  rewrite length_map.
  destruct argv as [|a0 [|path [|x argv']]].
  - (* [comment removed for export] *) cbn [length Z.of_nat Z.eqb negb map nth hd].
    split; [intros [ok H]| intros H; exists true]; revert H; apply (ct_die fs (Canon.msg_usage []) (Spec.msg_usage [])); exact (msg_usage_eq []).
  - (* [comment removed for export] *) cbn [length map nth hd]. change (negb (Z.of_nat 1 =? 2)) with true. cbv iota.
    split; [intros [ok H]| intros H; exists true]; revert H; apply ct_die; apply msg_usage_eq.
  - (* [comment removed for export] *) cbn [length map nth]. change (negb (Z.of_nat 2 =? 2)) with false. cbv iota.
    unfold open_class. rewrite bytes_roundtrip. change path_max with 4096%nat.
    destruct (4096 <=? length path)%nat eqn:E1.
    { split; [intros [[|] H]| intros H; exists true]; revert H; apply ct_die; apply msg_cannot_open_eq. }
    destruct path as [|b path'].
    { cbn [path_eqb]. split; [intros [[|] H]| intros H; exists true]; revert H; apply ct_die; apply msg_cannot_open_eq. }
    change (path_eqb (b :: path') []) with false. cbv iota.
    destruct (path_eqb (b :: path') dot_path) eqn:E2.
    { unfold t_alt2. split.
      - intros [[|] H]; [right; revert H; apply ct_die; apply msg_read_error_eq| left; revert H; apply ct_die; apply msg_cannot_open_eq].
      - intros [H|H]; [exists false| exists true]; revert H; apply ct_die; [apply msg_cannot_open_eq| apply msg_read_error_eq]. }
    destruct (fs_lookup fs (b :: path')) as [data|] eqn:E3.
    { unfold t_alt2. split.
      - intros [[|] H]; [right; apply file_trace_body; exact H| left; revert H; apply ct_die; apply msg_cannot_open_eq].
      - intros [H|H]; [exists false; revert H; apply ct_die; apply msg_cannot_open_eq| exists true; apply file_trace_body; exact H]. }
    split; [intros [[|] H]| intros H; exists true]; revert H; apply ct_die; apply msg_cannot_open_eq.
  - (* [comment removed for export] *) cbn [length map nth hd].
    replace (negb (Z.of_nat (S (S (S (length argv')))) =? 2)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; lia).
    cbv iota. split; [intros [ok H]| intros H; exists true]; revert H; apply ct_die; apply msg_usage_eq.
Qed.
