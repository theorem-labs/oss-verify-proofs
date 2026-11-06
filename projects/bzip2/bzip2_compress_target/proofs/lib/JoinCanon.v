(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ShapeAlg Spec Spec04.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Prelim Canon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module N := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec.
Module N4 := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Spec04.
Module SA := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg.
Module KP := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec.Prelim.
Module KC := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec.Canon.

(* [comment removed for export] *)
Definition argv_Z (argv : list (list byte)) : list (list Z) := map (map bv_unsigned) argv.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma is_prefix_app_mono' {A} : forall (l a b : list A), is_prefix a b -> is_prefix (l ++ a) (l ++ b).
Proof. induction l as [|x l IH]; intros a b H; cbn; [exact H| split; [reflexivity| apply IH; exact H]]. Qed.

Lemma emit_exit_iff : forall (evs : list event) (c : word) (fs : Fs.Fs) (tr : list event),
  SA.t_emit evs (SA.t_exit c fs) tr <-> is_prefix tr (evs ++ [ExitEv c fs]).
Proof.
  intros evs c fs tr. unfold SA.t_exit, SA.t_emit, SA.t_nil. split.
  - intros [Hp | (tr' & -> & [Hp | (tr'' & -> & ->)])].
    + apply SA.is_prefix_app_r. exact Hp.
    + apply is_prefix_app_mono'. exact Hp.
    + rewrite app_nil_r. apply is_prefix_refl.
  - intros Hp. destruct (SA.is_prefix_app_split _ _ _ Hp) as [H | (b' & -> & Hb)].
    + left. exact H.
    + right. exists b'. split; [reflexivity|]. left. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma W_evw : forall (fd : Z) (s : list byte), N.W fd s = KC.evw fd (map bv_unsigned s).
Proof.
  intros fd s. unfold N.W, KC.evw. rewrite map_map. apply map_ext.
  intros b. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma die_iff : forall (msg : list byte) (fs : Fs.Fs) (tr : list event),
  N.t_die msg fs tr <-> is_prefix tr (KC.ct_events fs (KC.mkCT 2 (map bv_unsigned msg) 2)).
Proof.
  intros msg fs tr. unfold N.t_die, KC.ct_events, N.exit_code. cbn [KC.ct_fd KC.ct_bytes KC.ct_code].
  rewrite emit_exit_iff, W_evw. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma s2b_str : forall s, map bv_unsigned (N.s2b s) = KP.str s.
Proof.
  intros s. unfold N.s2b, KP.str. rewrite map_map. apply map_ext. intros a.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  rewrite Z.mod_small.
  - unfold nat_of_ascii. apply N_nat_Z.
  - pose proof (N_ascii_bounded a) as HB. unfold nat_of_ascii. rewrite N_nat_Z.
    change (2 ^ Z.of_N 8) with 256. lia.
Qed.

(* [comment removed for export] *)

Lemma msg_usage_eq : forall a0, map bv_unsigned (N.msg_usage a0) = KC.msg_usage (map bv_unsigned a0).
Proof. intros. unfold N.msg_usage, KC.msg_usage. rewrite !map_app, !s2b_str. reflexivity. Qed.
Lemma msg_cannot_open_eq : forall p, map bv_unsigned (N.msg_cannot_open p) = KC.msg_cannot_open (map bv_unsigned p).
Proof. intros. unfold N.msg_cannot_open, KC.msg_cannot_open. rewrite !map_app, !s2b_str. reflexivity. Qed.
Lemma msg_read_error_eq : forall p, map bv_unsigned (N.msg_read_error p) = KC.msg_read_error (map bv_unsigned p).
Proof. intros. unfold N.msg_read_error, KC.msg_read_error. rewrite !map_app, !s2b_str. reflexivity. Qed.
Lemma msg_refused_eq : map bv_unsigned N.msg_refused = KC.msg_too_big.
Proof. unfold N.msg_refused, KC.msg_too_big. rewrite !map_app, !s2b_str. reflexivity. Qed.
Lemma msg_short_eq : map bv_unsigned N.msg_short = KC.msg_short_hdr.
Proof. unfold N.msg_short, KC.msg_short_hdr. rewrite !map_app, !s2b_str. reflexivity. Qed.
Lemma msg_overrun_eq : map bv_unsigned N.msg_overrun = KC.msg_cfg_overrun.
Proof. unfold N.msg_overrun, KC.msg_cfg_overrun. rewrite !map_app, !s2b_str. reflexivity. Qed.

Lemma zero_lines_eq : forall n, map bv_unsigned (N.zero_lines n) = KC.zeros_out n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  unfold KC.zeros_out in *. cbn [N.zero_lines repeat concat map]. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma znth_map : forall (data : list byte) (i : nat),
  KP.znth (map bv_unsigned data) (Z.of_nat i) = bv_unsigned (nth i data (Z_to_bv 8 0)).
Proof.
  intros data i. unfold KP.znth.
  destruct (Z.of_nat i <? 0) eqn:E; [apply Z.ltb_lt in E; lia|].
  rewrite Nat2Z.id. change 0 with (bv_unsigned (Z_to_bv 8 0)) at 1. apply map_nth.
Qed.

Lemma byte_range : forall (b : byte), 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range _ b) as H. unfold bv_modulus in H. change (2 ^ Z.of_N 8) with 256 in H. exact H. Qed.

Lemma body_iff : forall (data : list byte) (fs : Fs.Fs) (tr : list event),
  N4.t_body04 data fs tr <-> is_prefix tr (KC.ct_events fs (KC.file_trace (map bv_unsigned data))).
Proof.
  intros data fs tr. unfold N4.t_body04, KC.file_trace, KP.zlength. rewrite length_map.
  change 67108864 with N.MAX_INPUT.
  destruct (N.MAX_INPUT <=? Z.of_nat (length data)) eqn:E1.
  { rewrite die_iff, msg_refused_eq. reflexivity. }
  destruct (length data <? 6)%nat eqn:E2.
  { assert ((Z.of_nat (length data) <? 6) = true) as -> by (apply Nat.ltb_lt in E2; apply Z.ltb_lt; lia).
    rewrite die_iff, msg_short_eq. reflexivity. }
  assert ((Z.of_nat (length data) <? 6) = false) as -> by (apply Nat.ltb_ge in E2; apply Z.ltb_ge; lia).
  cbv zeta.
  set (b0 := bv_unsigned (nth 0 data (Z_to_bv 8 0))).
  set (b1 := bv_unsigned (nth 1 data (Z_to_bv 8 0))).
  set (b2 := bv_unsigned (nth 2 data (Z_to_bv 8 0))).
  assert (Hcl : KC.cfg_len (map bv_unsigned data) = (b0 + 256 * b1) mod 32768).
  { unfold KC.cfg_len. rewrite (znth_map data 0 : KP.znth _ 0 = _), (znth_map data 1 : KP.znth _ 1 = _). fold b0 b1.
    change 32767 with (Z.ones 15). rewrite Z.land_ones by lia. change (2 ^ 15) with 32768. f_equal. lia. }
  pose proof (byte_range (nth 0 data (Z_to_bv 8 0))) as R0. fold b0 in R0.
  pose proof (byte_range (nth 1 data (Z_to_bv 8 0))) as R1. fold b1 in R1.
  pose proof (byte_range (nth 2 data (Z_to_bv 8 0))) as R2. fold b2 in R2.
  pose proof (Z.mod_pos_bound (b0 + 256 * b1) 32768 ltac:(lia)) as RM.
  rewrite Hcl.
  destruct (length data <? 6 + Z.to_nat ((b0 + 256 * b1) mod 32768))%nat eqn:E3.
  { assert ((Z.of_nat (length data) <? 6 + (b0 + 256 * b1) mod 32768) = true) as ->
      by (apply Nat.ltb_lt in E3; apply Z.ltb_lt; lia).
    rewrite die_iff, msg_overrun_eq. reflexivity. }
  assert ((Z.of_nat (length data) <? 6 + (b0 + 256 * b1) mod 32768) = false) as ->
    by (apply Nat.ltb_ge in E3; apply Z.ltb_ge; lia).
  unfold KC.ct_events. cbn [KC.ct_fd KC.ct_bytes KC.ct_code].
  rewrite emit_exit_iff, W_evw, zero_lines_eq. unfold N.exit_code.
  assert (Hcalls : KC.cfg_calls (map bv_unsigned data)
                   = match Z.to_nat ((b0 + 256 * b1) mod 32768) with O => 1%nat | S _ => S (Z.to_nat (b2 mod 4)) end).
  { unfold KC.cfg_calls. rewrite Hcl, (znth_map data 2 : KP.znth _ 2 = _). fold b2.
    destruct (Z.to_nat ((b0 + 256 * b1) mod 32768)) eqn:En.
    - assert ((0 <? (b0 + 256 * b1) mod 32768) = false) as -> by (apply Z.ltb_ge; lia). reflexivity.
    - assert ((0 <? (b0 + 256 * b1) mod 32768) = true) as -> by (apply Z.ltb_lt; lia).
      change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2) with 4.
      pose proof (Z.mod_pos_bound b2 4 ltac:(lia)). rewrite Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat. lia. }
  rewrite Hcalls. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma unmap_bytes : forall (p : list byte), map (Z_to_bv 8) (map bv_unsigned p) = p.
Proof. intros p. rewrite map_map. rewrite <- (map_id p) at 2. apply map_ext. intros b. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)

Theorem canon_spec04 : forall (argv : list (list byte)) (fs : Fs.Fs) (tr : list event),
  KC.canonT (argv_Z argv) fs tr <-> N4.spec04 argv fs tr.
Proof.
  intros argv fs tr. rewrite KC.canonT_iff. unfold N4.spec04, KC.ctrace_of, argv_Z. rewrite length_map.
  destruct argv as [|a0 [|path [|x r]]].
  - (* [comment removed for export] *) cbn [length]. change (negb (Z.of_nat 0 =? 2)) with true. cbv iota.
    rewrite die_iff, msg_usage_eq. cbn [hd nth map]. split; [intros (_ & H); exact H| intros H; exists true; exact H].
  - (* [comment removed for export] *) cbn [length]. change (negb (Z.of_nat 1 =? 2)) with true. cbv iota.
    rewrite die_iff, msg_usage_eq. cbn [hd nth map]. split; [intros (_ & H); exact H| intros H; exists true; exact H].
  - (* [comment removed for export] *) cbn [length]. change (negb (Z.of_nat 2 =? 2)) with false. cbv iota. cbn [nth map].
    unfold KC.open_class. rewrite unmap_bytes.
    assert (HF : (exists ok : bool, is_prefix tr (KC.ct_events fs
                    (match (if ok then KC.OCFail else KC.OCFail) with
                     | KC.OCFail => KC.mkCT 2 (KC.msg_cannot_open (map bv_unsigned path)) 2
                     | KC.OCDir => KC.mkCT 2 (KC.msg_read_error (map bv_unsigned path)) 2
                     | KC.OCFile data => KC.file_trace (map bv_unsigned data) end)))
                 <-> N.t_die (N.msg_cannot_open path) fs tr).
    { rewrite die_iff, msg_cannot_open_eq. split; [intros ([|] & H); exact H| intros H; exists true; exact H]. }
    unfold path_max.
    destruct (4096 <=? length path)%nat eqn:E1; [exact HF|].
    change (N.list_byte_eqb path []) with (path_eqb path []).
    change (N.list_byte_eqb path N.dot_path) with (path_eqb path dot_path).
    destruct path as [|c path']; [cbn [path_eqb]; exact HF|].
    change (path_eqb (c :: path') []) with false. cbv iota.
    destruct (path_eqb (c :: path') dot_path) eqn:E2.
    + (* [comment removed for export] *) unfold SA.t_alt2, N4.t_opened_dir04. rewrite !die_iff, msg_cannot_open_eq, msg_read_error_eq.
      split; [intros ([|] & H); [right|left]; exact H| intros [H|H]; [exists false|exists true]; exact H].
    + destruct (fs_lookup fs (c :: path')) as [data|] eqn:E3; [|exact HF].
      unfold SA.t_alt2, N4.t_opened04. rewrite die_iff, msg_cannot_open_eq, body_iff.
      split; [intros ([|] & H); [right|left]; exact H| intros [H|H]; [exists false|exists true]; exact H].
  - (* [comment removed for export] *) cbn [length].
    assert (negb (Z.of_nat (S (S (S (length r)))) =? 2) = true) as -> by (apply negb_true_iff, Z.eqb_neq; lia).
    cbv iota. rewrite die_iff, msg_usage_eq. cbn [hd nth map].
    split; [intros (_ & H); exact H| intros H; exists true; exact H].
Qed.

(* [comment removed for export] *)
