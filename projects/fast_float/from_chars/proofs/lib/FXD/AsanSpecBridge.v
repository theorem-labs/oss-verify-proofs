(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run Specs Fs.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import ShapeSet RealizesCfg FxLin FxCore FxSound FxFacts.
From OSSVerify.Proofs.fast_float.from_chars.lib Require Import Spec.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxWvC FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanTMain2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainSF.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXG Require AsanMainP.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanTMain2 OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainSF.AsanSpecF OSSVerify.Proofs.fast_float.from_chars.lib.FXG.AsanMainP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma uE_lconst0 : forall E, Z.to_nat (uE E (lconst 0)) = O.
Proof. intros E. unfold uE. rewrite lden_lconst. reflexivity. Qed.
Lemma pre_cannot : s2b "cli: cannot open " = List.map (Z_to_bv 8) CANNOT_PRE. Proof. vm_compute. reflexivity. Qed.
Lemma suf_nl : nl = List.map (Z_to_bv 8) [10]. Proof. vm_compute. reflexivity. Qed.
Lemma msg_short_eq : msg_short = List.map (Z_to_bv 8) MSG_SHORT. Proof. vm_compute. reflexivity. Qed.
Lemma msg_ovr_eq : msg_overrun = List.map (Z_to_bv 8) MSG_OVR. Proof. vm_compute. reflexivity. Qed.
Lemma msg_refused_eq : msg_refused = List.map (Z_to_bv 8) MSG_REFUSED. Proof. vm_compute. reflexivity. Qed.
Lemma zl_eq : forall n, List.map (Z_to_bv 8) (zl n) = zero_lines n.
Proof. induction n as [|n IH]; [reflexivity|]. cbn [zl zero_lines List.map]. rewrite IH. reflexivity. Qed.

Section Den.
Variables (path0 : path) (fs0 : Fs.Fs) (argv0 : list byte) (data0 : list byte).
Abbreviation den := (shp_den path0 fs0 argv0).

#[using="Type"] Lemma lit_die : forall E (m : list Z), den E (ShEmit [PD 2 (SLit m) (lconst 0)] 2) = t_die (List.map (Z_to_bv 8) m) fs0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E m. unfold t_die, W, exit_code. cbn [shp_den List.map concat]. unfold pend_evs. cbn [pd_ch pd_off pd_src src_bytes].
  rewrite uE_lconst0, skipn_O, app_nil_r. reflexivity.
Qed.
#[using="Type"] Lemma calls_den : forall E n, den E (CALLS n) = t_emit (W 1 (zero_lines n)) (t_exit (exit_code 0) fs0).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E n. unfold CALLS, W, exit_code. cbn [shp_den List.map concat]. unfold pend_evs. cbn [pd_ch pd_off pd_src src_bytes].
  rewrite uE_lconst0, skipn_O, app_nil_r, zl_eq. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sh_top_den : forall E f, uE E ARGC = 2 -> uE E (hvar 17) = Z.of_nat (length path0) ->
  den E (SH_TOP f) = t_alt2 (t_die (msg_cannot_open path0) fs0) (den E f).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E f H2 H17. unfold SH_TOP. cbn [shp_den]. rewrite H2. cbn [Z.leb Z.compare Pos.compare Pos.compare_cont andb].
  f_equal. unfold SH_CANNOT, t_die, msg_cannot_open, W, exit_code. cbn [shp_den List.map concat]. unfold pend_evs. cbn [pd_ch pd_off pd_src src_bytes sarg].
  rewrite uE_lconst0, skipn_O, app_nil_r, H17, Nat2Z.id, firstn_all. rewrite pre_cannot, suf_nl. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sh_short_den : forall E, (length data0 <= 5)%nat -> den E SH_SHORT = t_body data0 fs0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E Hl. unfold SH_SHORT. rewrite lit_die, <- msg_short_eq. unfold t_body. cbv zeta.
  replace (MAX_INPUT <=? Z.of_nat (length data0)) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT; lia).
  replace (length data0 <? 6)%nat with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sh_refused_den : forall E, 67108864 <= Z.of_nat (length data0) -> den E SH_REFUSED = t_body data0 fs0.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E Hl. unfold SH_REFUSED. rewrite lit_die, <- msg_refused_eq. unfold t_body. cbv zeta.
  replace (MAX_INPUT <=? Z.of_nat (length data0)) with true by (symmetry; apply Z.leb_le; unfold MAX_INPUT in *; lia). reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma CLA_eq : CLA = ladd (hvar 0) (lscale 256 (hvar 1)). Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma CLB_eq : CLB = laddc CLA (- 32768). Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma LA_eq : LA = lsub (laddc CLA 5) (hvar 16). Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma LB_eq : LB = laddc LA (- 32768). Proof. LiaFast.lf_pins LiaFast.u0. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma bits_mod4 : forall d, 0 <= d <= 255 ->
  (if Z.testbit d 1 then if Z.testbit d 0 then 4 else 3 else if Z.testbit d 0 then 2 else 1) = 1 + d mod 4.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros d Hd.
  assert (H : forallb (fun n => Z.eqb (if Z.testbit (Z.of_nat n) 1 then if Z.testbit (Z.of_nat n) 0 then 4 else 3 else if Z.testbit (Z.of_nat n) 0 then 2 else 1)
                                     (1 + Z.of_nat n mod 4)) (seq 0 256) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in H. specialize (H (Z.to_nat d) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in H by lia.
  apply Z.eqb_eq in H. exact H.
Qed.

Section File.
Variable E : valu.
Hypothesis HL : uE E (hvar 16) = Z.of_nat (length data0).
Hypothesis Hb : forall i, (i < 3)%nat -> uE E (hvar i) = bv_unsigned (nth i data0 (Z_to_bv 8 0)).
Hypothesis Hlen : 6 <= Z.of_nat (length data0) < 67108864.

Let D0 : Z := bv_unsigned (nth 0 data0 (Z_to_bv 8 0)).
Let D1 : Z := bv_unsigned (nth 1 data0 (Z_to_bv 8 0)).
Let D2 : Z := bv_unsigned (nth 2 data0 (Z_to_bv 8 0)).
Let LEN : Z := Z.of_nat (length data0).
#[using="D0 D1 D2 LEN"] Lemma byte_rng : forall i, 0 <= bv_unsigned (nth i data0 (Z_to_bv 8 0)) <= 255.
Proof. LiaFast.lf_pins (fun (D0 D1 D2 LEN : LiaFast.U) => LiaFast.u0). intros i. pose proof (bv_unsigned_in_range 8 (nth i data0 (Z_to_bv 8 0))) as X. change (bv_modulus 8) with 256 in X. lia. Qed.

#[using="Hb D2 LEN"] Lemma uCLA : uE E CLA = D0 + 256 * D1.
Proof. LiaFast.lf_pins (fun (Hb D2 LEN : LiaFast.U) => LiaFast.u0).
  rewrite CLA_eq. unfold uE. rewrite lden_ladd, lden_lscale, bv_add_unsigned, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  fold (uE E (hvar 0)) (uE E (hvar 1)). rewrite (Hb 0%nat ltac:(lia)), (Hb 1%nat ltac:(lia)). fold D0 D1.
  pose proof (byte_rng 0) as R0. pose proof (byte_rng 1) as R1. fold D0 in R0. fold D1 in R1.
  rewrite (Z.mod_small (256 * D1)) by lia. apply Z.mod_small. lia.
Qed.
#[using="HL Hb D2"] Lemma uLA : uE E LA = (D0 + 256 * D1 + 5 - LEN) mod 2^64.
Proof. LiaFast.lf_pins (fun (HL Hb D2 : LiaFast.U) => LiaFast.u0).
  rewrite LA_eq. unfold uE. rewrite lden_lsub, lden_laddc, bv_sub_unsigned, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  fold (uE E CLA) (uE E (hvar 16)). rewrite uCLA, HL. fold LEN.
  pose proof (byte_rng 0) as R0. pose proof (byte_rng 1) as R1. fold D0 in R0. fold D1 in R1.
  rewrite (Z.mod_small (D0 + 256 * D1 + 5)) by lia. reflexivity.
Qed.
#[using="Hb D2 LEN"] Lemma uCLB : 128 <= D1 -> uE E CLB = D0 + 256 * D1 - 32768.
Proof. LiaFast.lf_pins (fun (Hb D2 LEN : LiaFast.U) => LiaFast.u0).
  intros H1. rewrite CLB_eq. unfold uE. rewrite lden_laddc, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  fold (uE E CLA). rewrite uCLA.
  pose proof (byte_rng 0) as R0. pose proof (byte_rng 1) as R1. fold D0 in R0. fold D1 in R1.
  replace (D0 + 256 * D1 + -32768) with (D0 + 256 * D1 - 32768) by ring. apply Z.mod_small. lia.
Qed.
#[using="HL Hb D2"] Lemma uLB : uE E LB = (D0 + 256 * D1 - 32768 + 5 - LEN) mod 2^64.
Proof. LiaFast.lf_pins (fun (HL Hb D2 : LiaFast.U) => LiaFast.u0).
  rewrite LB_eq. unfold uE. rewrite lden_laddc, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  fold (uE E LA). rewrite uLA. rewrite Zplus_mod_idemp_l. f_equal. ring.
Qed.

(* [comment removed for export] *)
#[using="data0 D0 D1 D2 LEN"] Lemma sgn_test : forall x, - 2^62 < x < 2^62 -> (Z.leb 0 (x mod 2^64) && Z.leb (x mod 2^64) T63)%bool = Z.leb 0 x.
Proof. LiaFast.lf_pins (fun (data0 D0 D1 D2 LEN : LiaFast.U) => LiaFast.u0).
  intros x Hx. unfold T63. destruct (Z_le_gt_dec 0 x) as [Hp|Hn].
  - rewrite Z.mod_small by lia. replace (0 <=? x) with true by (symmetry; apply Z.leb_le; lia).
    replace (x <=? 9223372036854775808) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
  - replace (x mod 2^64) with (x + 2^64) by (symmetry; rewrite <- (Z_mod_plus_full x 1 (2^64)); apply Z.mod_small; lia).
    replace (0 <=? x) with false by (symmetry; apply Z.leb_gt; lia).
    replace (x + 2^64 <=? 9223372036854775808) with false by (symmetry; apply Z.leb_gt; lia). apply andb_false_r.
Qed.

#[using="Hb D0 D1 D2 LEN"] Lemma bodyc_den : forall cl, uE E cl = Z.of_nat (config_len data0) ->
  den E (BODYC cl) = t_emit (W 1 (zero_lines (n_calls data0))) (t_exit (exit_code 0) fs0).
Proof. LiaFast.lf_pins (fun (Hb D0 D1 D2 LEN : LiaFast.U) => LiaFast.u0).
  intros cl Hcl. unfold BODYC. cbn [shp_den]. rewrite Hcl.
  unfold n_calls. destruct (config_len data0) as [|k] eqn:Hk.
  - cbn [Z.of_nat Z.leb Z.compare andb]. apply calls_den.
  - replace (0 <=? Z.of_nat (Datatypes.S k)) with true by (symmetry; apply Z.leb_le; lia).
    replace (Z.of_nat (Datatypes.S k) <=? 0) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
    rewrite (Hb 2%nat ltac:(lia)). fold D2.
    pose proof (byte_rng 2) as R2. fold D2 in R2. pose proof (bits_mod4 D2 R2) as HB.
    pose proof (Z.mod_pos_bound D2 4 ltac:(lia)) as HM.
    destruct (Z.testbit D2 1), (Z.testbit D2 0); rewrite calls_den; do 2 f_equal.
    + replace (D2 mod 4) with 3 by lia. reflexivity.
    + replace (D2 mod 4) with 2 by lia. reflexivity.
    + replace (D2 mod 4) with 1 by lia. reflexivity.
    + replace (D2 mod 4) with 0 by lia. reflexivity.
Qed.

#[using="HL Hb Hlen D0 D1 D2 LEN"] Theorem file_w_den : den E FILE_W = t_body data0 fs0.
Proof. LiaFast.lf_pins (fun (HL Hb Hlen D0 D1 D2 LEN : LiaFast.U) => LiaFast.u0).
  pose proof (byte_rng 0) as R0. pose proof (byte_rng 1) as R1. fold D0 in R0. fold D1 in R1.
  assert (Hcw : cfg_word data0 = D0 + 256 * D1) by reflexivity.
  unfold t_body. cbv zeta. fold LEN.
  replace (MAX_INPUT <=? LEN) with false by (symmetry; apply Z.leb_gt; unfold MAX_INPUT, LEN in *; lia).
  replace (length data0 <? 6)%nat with false by (symmetry; apply Nat.ltb_ge; unfold LEN in *; lia).
  unfold FILE_W. cbn [shp_den]. rewrite (Hb 1%nat ltac:(lia)). fold D1.
  replace (0 <=? D1) with true by (symmetry; apply Z.leb_le; lia). cbn [andb].
  destruct (Z_le_gt_dec D1 127) as [H1|H1].
  - replace (D1 <=? 127) with true by (symmetry; apply Z.leb_le; lia).
    assert (Hcl : Z.of_nat (config_len data0) = D0 + 256 * D1).
    { unfold config_len. rewrite Hcw. rewrite Z.mod_small by lia. apply Z2Nat.id. lia. }
    rewrite uLA, (sgn_test (D0 + 256 * D1 + 5 - LEN)) by (unfold LEN in *; lia).
    destruct (Z_le_gt_dec 0 (D0 + 256 * D1 + 5 - LEN)) as [Ho|Ho].
    + replace (0 <=? D0 + 256 * D1 + 5 - LEN) with true by (symmetry; apply Z.leb_le; lia).
      replace (length data0 <? 6 + config_len data0)%nat with true by (symmetry; apply Nat.ltb_lt; unfold LEN in *; lia).
      unfold SH_OVR. rewrite lit_die, <- msg_ovr_eq. reflexivity.
    + replace (0 <=? D0 + 256 * D1 + 5 - LEN) with false by (symmetry; apply Z.leb_gt; lia).
      replace (length data0 <? 6 + config_len data0)%nat with false by (symmetry; apply Nat.ltb_ge; unfold LEN in *; lia).
      apply bodyc_den. rewrite uCLA. symmetry. exact Hcl.
  - replace (D1 <=? 127) with false by (symmetry; apply Z.leb_gt; lia).
    assert (Hcl : Z.of_nat (config_len data0) = D0 + 256 * D1 - 32768).
    { unfold config_len. rewrite Hcw.
      replace ((D0 + 256 * D1) mod 32768) with (D0 + 256 * D1 - 32768) by (apply (Z.mod_unique_pos (D0 + 256 * D1) 32768 1); lia).
      apply Z2Nat.id. lia. }
    rewrite uLB, (sgn_test (D0 + 256 * D1 - 32768 + 5 - LEN)) by (unfold LEN in *; lia).
    destruct (Z_le_gt_dec 0 (D0 + 256 * D1 - 32768 + 5 - LEN)) as [Ho|Ho].
    + replace (0 <=? D0 + 256 * D1 - 32768 + 5 - LEN) with true by (symmetry; apply Z.leb_le; lia).
      replace (length data0 <? 6 + config_len data0)%nat with true by (symmetry; apply Nat.ltb_lt; unfold LEN in *; lia).
      unfold SH_OVR. rewrite lit_die, <- msg_ovr_eq. reflexivity.
    + replace (0 <=? D0 + 256 * D1 - 32768 + 5 - LEN) with false by (symmetry; apply Z.leb_gt; lia).
      replace (length data0 <? 6 + config_len data0)%nat with false by (symmetry; apply Nat.ltb_ge; unfold LEN in *; lia).
      apply bodyc_den. rewrite (uCLB ltac:(lia)). symmetry. exact Hcl.
Qed.
End File.
End Den.
