(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1rh.
Import ListNotations.
Open Scope Z_scope.

Definition ltp_params_ok (p : ltp_params) : Prop :=
0 <= ltp_pitch_bits p <= 7 /\ 0 <= ltp_gain_bits p <= 7
/\ 4 * 2 ^ ltp_gain_bits p <= gain_cdbk_size (ltp_gain_cdbk p).

Definition scb_params_ok (p : split_cb_params) : Prop :=
1 <= scb_subvect_size p <= 40 /\ 1 <= scb_nb_subvect p <= 8 /\ scb_subvect_size p * scb_nb_subvect p = 40
/\ 1 <= scb_shape_bits p <= 8
/\ 2 ^ scb_shape_bits p * scb_subvect_size p <= shape_cb_size (scb_shape_cb p)
/\ (scb_have_sign p = 0 \/ scb_have_sign p = 1).

Lemma ltp_params_ok_tables :
Forall ltp_params_ok [ltp_params_nb; ltp_params_vlbr; ltp_params_lbr; ltp_params_med].
Proof. repeat constructor; cbn; lia. Qed.

Lemma scb_params_ok_tables :
Forall scb_params_ok [split_cb_nb_vlbr; split_cb_nb_ulbr; split_cb_nb_lbr; split_cb_nb; split_cb_nb_med; split_cb_sb;
split_cb_high; split_cb_high_lbr].
Proof. repeat constructor; cbn; lia. Qed.

Lemma ltp_params_ok_In : forall p, In p [ltp_params_nb; ltp_params_vlbr; ltp_params_lbr; ltp_params_med] -> ltp_params_ok p.
Proof. intros p H. exact (proj1 (Forall_forall _ _) ltp_params_ok_tables p H). Qed.

Lemma scb_params_ok_In : forall p,
In p [split_cb_nb_vlbr; split_cb_nb_ulbr; split_cb_nb_lbr; split_cb_nb; split_cb_nb_med; split_cb_sb; split_cb_high; split_cb_high_lbr] ->
scb_params_ok p.
Proof. intros p H. exact (proj1 (Forall_forall _ _) scb_params_ok_tables p H). Qed.
