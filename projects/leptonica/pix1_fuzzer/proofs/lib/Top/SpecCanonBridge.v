(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.CliDriver Require Import Spec.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.K5.Spec Require Import Prelim Canon.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Lemma is_prefix_app_l {A} : forall (a b c : list A), is_prefix b c -> is_prefix (a ++ b) (a ++ c).
Proof. induction a as [|x a IH]; intros b c H; cbn; [exact H| split; [reflexivity| apply IH; exact H]]. Qed.

Lemma t_emit_exit_iff : forall evs code fs tr,
  t_emit evs (t_exit code fs) tr <-> is_prefix tr (evs ++ [ExitEv code fs]).
Proof.
  intros evs code fs tr. unfold t_exit, t_emit, t_nil. split.
  - intros [H | (tr' & -> & [H | (tr'' & -> & ->)])].
    + apply is_prefix_app_r. exact H.
    + apply is_prefix_app_l. exact H.
    + rewrite app_nil_r. apply is_prefix_refl.
  - intros H. destruct (is_prefix_app_split _ _ _ H) as [Hp | (b' & -> & Hp)].
    + left. exact Hp.
    + right. exists b'. split; [reflexivity|]. left. exact Hp.
Qed.

(* [comment removed for export] *)
Definition b8 (l : list Z) : list byte := map (Z_to_bv 8) l.
Definition zs (l : list byte) : list Z := map bv_unsigned l.

Lemma b8_zs : forall l, b8 (zs l) = l.
Proof.
  induction l as [|b l IH]; cbn; [reflexivity|]. f_equal; [|exact IH]. apply Z_to_bv_bv_unsigned.
Qed.

Lemma b8_app : forall a b, b8 (a ++ b) = b8 a ++ b8 b.
Proof. intros. unfold b8. apply map_app. Qed.

Lemma W_b8 : forall ch l, W ch (b8 l) = evw ch l.
Proof. intros. unfold W, evw, b8. rewrite map_map. reflexivity. Qed.

Lemma s2b_str : forall s, s2b s = b8 (str s).
Proof.
  intros s. unfold s2b, str, b8. rewrite map_map. apply map_ext. intros a.
  f_equal. unfold nat_of_ascii. apply N_nat_Z.
Qed.

Lemma zero_lines_zeros : forall n, zero_lines n = b8 (zeros_out n).
Proof.
  induction n as [|n IH]; [reflexivity|].
  rewrite zeros_out_S. cbn [zero_lines]. rewrite b8_app, <- IH. reflexivity.
Qed.

Lemma msg_usage_b8 : forall a0, Spec.msg_usage a0 = b8 (Canon.msg_usage (zs a0)).
Proof.
  intros. unfold Spec.msg_usage, Canon.msg_usage. rewrite !b8_app, b8_zs, !s2b_str. reflexivity.
Qed.
Lemma msg_cannot_open_b8 : forall p, Spec.msg_cannot_open p = b8 (Canon.msg_cannot_open (zs p)).
Proof.
  intros. unfold Spec.msg_cannot_open, Canon.msg_cannot_open. rewrite !b8_app, b8_zs, !s2b_str. reflexivity.
Qed.
Lemma msg_read_error_b8 : forall p, Spec.msg_read_error p = b8 (Canon.msg_read_error (zs p)).
Proof.
  intros. unfold Spec.msg_read_error, Canon.msg_read_error. rewrite !b8_app, b8_zs, !s2b_str. reflexivity.
Qed.
Lemma msg_refused_b8 : Spec.msg_refused = b8 Canon.msg_too_big.
Proof. unfold Spec.msg_refused, Canon.msg_too_big. rewrite !b8_app, !s2b_str. reflexivity. Qed.
Lemma msg_short_b8 : Spec.msg_short = b8 Canon.msg_short_hdr.
Proof. unfold Spec.msg_short, Canon.msg_short_hdr. rewrite !b8_app, !s2b_str. reflexivity. Qed.
Lemma msg_overrun_b8 : Spec.msg_overrun = b8 Canon.msg_cfg_overrun.
Proof. unfold Spec.msg_overrun, Canon.msg_cfg_overrun. rewrite !b8_app, !s2b_str. reflexivity. Qed.

(* [comment removed for export] *)
Lemma t_die_ct : forall msgz fs tr,
  t_die (b8 msgz) fs tr <-> is_prefix tr (ct_events fs (mkCT 2 msgz 2)).
Proof.
  intros. unfold t_die, ct_events. cbn [ct_fd ct_bytes ct_code]. rewrite W_b8. apply t_emit_exit_iff.
Qed.

Lemma t_ok_ct : forall outz fs tr,
  t_emit (W 1 (b8 outz)) (t_exit (exit_code 0) fs) tr <-> is_prefix tr (ct_events fs (mkCT 1 outz 0)).
Proof.
  intros. unfold ct_events. cbn [ct_fd ct_bytes ct_code]. rewrite W_b8. apply t_emit_exit_iff.
Qed.

(* [comment removed for export] *)
Lemma zlength_zs : forall l, zlength (zs l) = Z.of_nat (length l).
Proof. intros. unfold zlength, zs. rewrite length_map. reflexivity. Qed.

Lemma znth_zs : forall l (k : nat), znth (zs l) (Z.of_nat k) = bv_unsigned (nth k l (Z_to_bv 8 0)).
Proof.
  intros l k. unfold znth, zs. rewrite Nat2Z.id.
  replace (Z.of_nat k <? 0)%Z with false by (symmetry; apply Z.ltb_ge; lia).
  change (nth k (map bv_unsigned l) (bv_unsigned (Z_to_bv 8 0)) = bv_unsigned (nth k l (Z_to_bv 8 0))). apply map_nth.
Qed.

Lemma byte_range : forall b : byte, (0 <= bv_unsigned b < 256)%Z.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

Lemma body_ct : forall data fs tr,
  t_body data fs tr <-> is_prefix tr (ct_events fs (file_trace (zs data))).
Proof.
  intros data fs tr. unfold t_body, file_trace. rewrite zlength_zs. unfold MAX_INPUT.
  destruct (67108864 <=? Z.of_nat (length data))%Z eqn:Hbig.
  { rewrite msg_refused_b8. apply t_die_ct. }
  destruct (length data <? 6)%nat eqn:Hs.
  { apply Nat.ltb_lt in Hs. replace (Z.of_nat (length data) <? 6)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite msg_short_b8. apply t_die_ct. }
  apply Nat.ltb_ge in Hs. replace (Z.of_nat (length data) <? 6)%Z with false by (symmetry; apply Z.ltb_ge; lia).
  unfold cfg_len, cfg_calls, cfg_len.
  set (b0 := bv_unsigned (nth 0 data (Z_to_bv 8 0))). set (b1 := bv_unsigned (nth 1 data (Z_to_bv 8 0))).
  set (b2 := bv_unsigned (nth 2 data (Z_to_bv 8 0))).
  assert (H0 : znth (zs data) 0 = b0) by exact (znth_zs data 0).
  assert (H1 : znth (zs data) 1 = b1) by exact (znth_zs data 1).
  assert (H2 : znth (zs data) 2 = b2) by exact (znth_zs data 2).
  rewrite !H0, !H1, !H2.
  pose proof (byte_range (nth 0 data (Z_to_bv 8 0))) as R0. pose proof (byte_range (nth 1 data (Z_to_bv 8 0))) as R1.
  pose proof (byte_range (nth 2 data (Z_to_bv 8 0))) as R2. fold b0 in R0. fold b1 in R1. fold b2 in R2.
  assert (Hland : Z.land (b0 + b1 * 256) 32767 = ((b0 + 256 * b1) mod 32768)%Z).
  { change 32767%Z with (Z.ones 15). rewrite Z.land_ones by lia. f_equal. lia. }
  rewrite Hland. set (c := ((b0 + 256 * b1) mod 32768)%Z).
  assert (Hc : (0 <= c < 32768)%Z) by (apply Z.mod_pos_bound; lia).
  destruct (length data <? 6 + Z.to_nat c)%nat eqn:Ho.
  { apply Nat.ltb_lt in Ho. replace (Z.of_nat (length data) <? 6 + c)%Z with true by (symmetry; apply Z.ltb_lt; lia).
    rewrite msg_overrun_b8. apply t_die_ct. }
  apply Nat.ltb_ge in Ho. replace (Z.of_nat (length data) <? 6 + c)%Z with false by (symmetry; apply Z.ltb_ge; lia).
  assert (Hcalls : match Z.to_nat c with O => 1%nat | S _ => S (Z.to_nat (b2 mod 4)) end
                   = Z.to_nat (Z.land (if (0 <? c)%Z then b2 else 0) 3 + 1)).
  { destruct (0 <? c)%Z eqn:Hz.
    - apply Z.ltb_lt in Hz. destruct (Z.to_nat c) eqn:Hn; [lia|].
      change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. change (2 ^ 2)%Z with 4%Z.
      pose proof (Z.mod_pos_bound b2 4 ltac:(lia)). rewrite Z2Nat.inj_add by lia. change (Z.to_nat 1) with 1%nat. lia.
    - apply Z.ltb_ge in Hz. assert (c = 0)%Z by lia. subst c. rewrite H. reflexivity. }
  rewrite Hcalls, zero_lines_zeros. apply t_ok_ct.
Qed.

(* [comment removed for export] *)
Lemma list_byte_eqb_path_eqb : forall p q, list_byte_eqb p q = path_eqb p q.
Proof. reflexivity. Qed.   (* [comment removed for export] *)

Theorem spec_canonT : forall argv fs, t_eq (spec argv fs) (canonT (map zs argv) fs).
Proof.
  intros argv fs tr. rewrite canonT_iff. unfold ctrace_of. rewrite length_map.
  destruct argv as [|a0 [|path [|x rest]]].
  - (* [comment removed for export] *) cbn [spec length Z.of_nat Z.eqb negb hd nth map]. rewrite (msg_usage_b8 []), t_die_ct.
    split; [intros H; exists true; exact H | intros [? H]; exact H].
  - (* [comment removed for export] *) cbn [spec length hd nth map]. change (negb (Z.of_nat 1 =? 2)%Z) with true. cbn iota.
    rewrite msg_usage_b8, t_die_ct. split; [intros H; exists true; exact H | intros [? H]; exact H].
  - (* [comment removed for export] *) cbn [spec length nth map]. change (negb (Z.of_nat 2 =? 2)%Z) with false. cbn iota.
    unfold open_class. fold (b8 (zs path)). rewrite b8_zs. unfold path_max.
    change (list_byte_eqb path Spec.dot_path) with (path_eqb path Uapi.dot_path).
    set (isdot := path_eqb path Uapi.dot_path). set (look := fs_lookup fs path).
    destruct (4096 <=? length path)%nat.
    { rewrite msg_cannot_open_b8, t_die_ct. split; [intros H; exists true; exact H | intros [[|] H]; exact H]. }
    assert (Hmt : forall (X Y : oclass), match path with [] => X | _ :: _ => Y end = if list_byte_eqb path [] then X else Y)
      by (intros; destruct path; reflexivity).
    rewrite Hmt. clear Hmt.
    destruct (list_byte_eqb path []).
    { rewrite msg_cannot_open_b8, t_die_ct. split; [intros H; exists true; exact H | intros [[|] H]; exact H]. }
    destruct isdot.
    { unfold t_alt2, t_opened_dir. rewrite msg_cannot_open_b8, msg_read_error_b8, !t_die_ct.
      split; [intros [H|H]; [exists false| exists true]; exact H | intros [[|] H]; [right|left]; exact H]. }
    destruct look as [data|].
    { unfold t_alt2, t_opened. rewrite msg_cannot_open_b8, t_die_ct, body_ct.
      split; [intros [H|H]; [exists false| exists true]; exact H | intros [[|] H]; [right|left]; exact H]. }
    rewrite msg_cannot_open_b8, t_die_ct. split; [intros H; exists true; exact H | intros [[|] H]; exact H].
  - (* [comment removed for export] *) cbn [spec hd nth map].
    replace (negb (Z.of_nat (length (a0 :: path :: x :: rest)) =? 2)%Z) with true
      by (symmetry; apply negb_true_iff, Z.eqb_neq; cbn [length]; lia).
    rewrite msg_usage_b8, t_die_ct. split; [intros H; exists true; exact H | intros [? H]; exact H].
Qed.

