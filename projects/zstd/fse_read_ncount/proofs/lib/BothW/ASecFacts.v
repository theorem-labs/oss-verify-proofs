(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.BothW Require Import ABase AModelFacts APrimFacts.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Lemma not_primary_big : forall n, 0 <= n -> is_primary n = false -> 64512 < n.
Proof.
intros n N P. unfold is_primary, needed0, K_MAX_SIZE in P. apply Z.leb_gt in P.
rewrite rounded_size_eq, rz_size_eq in P.
destruct (Z_lt_le_dec 64512 n) as [L|L]; [exact L|]. exfalso.
assert (R : rz_log n <= 6).
{ unfold rz_log. destruct (n <=? 48); [lia|]. destruct (n <=? 96); [lia|]. destruct (n <=? 448); [lia|]. destruct (n <=? 3968); [lia|].
destruct (n <=? 16128); [lia|]. destruct (n <=? 32256); [lia|]. destruct (Z.leb_spec n 64512); lia. }
pose proof (rz_log_range n) as RR.
assert (P2 : 2 ^ rz_log n <= 64) by (change 64 with (2^6); apply Z.pow_le_mono_r; lia).
Z.div_mod_to_equations. nia.
Qed.
#[using="Type"] Lemma rz_log_big : forall n, 64512 < n -> rz_log n = 7.
Proof. intros n N. unfold rz_log. repeat (rewrite (proj2 (Z.leb_gt _ _)) by lia). reflexivity. Qed.
#[using="Type"] Lemma sec_facts : forall n, 1 <= n <= AREQMAX -> is_primary n = false ->
64512 < n
/\ rz_size n = 2048
/\ rounded_size n = (n + 7) / 8 * 8 /\ n <= rounded_size n <= n + 7 /\ rounded_size n mod 8 = 0
/\ needed_size n = rounded_size n + 4096
/\ sec_map_size n = (needed_size n + 4095) / 4096 * 4096 + 4096
/\ needed_size n + 4096 <= sec_map_size n <= needed_size n + 8191 /\ sec_map_size n mod 4096 = 0
/\ 73728 <= sec_map_size n <= 536821760.
Proof.
intros n N P. pose proof (not_primary_big n ltac:(lia) P) as B.
pose proof (rz_log_big n B) as RL.
assert (RZ : rz_size n = 2048) by (rewrite rz_size_eq, RL; reflexivity).
pose proof (rounded_size_eq n) as RS. rewrite Z.max_l in RS by lia.
assert (NS : needed_size n = rounded_size n + 4096) by (unfold needed_size; rewrite P; unfold needed0; rewrite RZ; lia).
assert (MS : sec_map_size n = (needed_size n + 4095) / 4096 * 4096 + 4096) by (unfold sec_map_size, rup, PG; f_equal; f_equal; f_equal; lia).
unfold AREQMAX in N.
split; [exact B|]. split; [exact RZ|]. split; [exact RS|].
split; [rewrite RS; Z.div_mod_to_equations; lia|]. split; [rewrite RS; Z.div_mod_to_equations; lia|].
split; [exact NS|]. split; [exact MS|].
rewrite MS, NS, RS. Z.div_mod_to_equations. lia.
Qed.
End CANSEC1.
