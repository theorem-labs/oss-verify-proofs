(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0f.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Lemma np2_aux_min : forall fuel n p K, 0 <= p -> p <= K <= p + Z.of_nat fuel -> n <= 2 ^ K ->
(forall q, p <= q < K -> 2 ^ q < n) -> YO07.np2_aux fuel n p = K.
Proof.
induction fuel as [|fuel IH]; intros n p K Hp HK Hn Hmin; cbn [YO07.np2_aux].
- lia.
- destruct (Z.ltb_spec (2 ^ p) n) as [Hlt | Hge].
+ assert (p < K) by (destruct (Z.eq_dec p K) as [-> |]; lia).
apply IH; [lia | lia | exact Hn | intros q Hq; apply Hmin; lia].
+ destruct (Z.eq_dec p K) as [-> | Hne]; [reflexivity|]. exfalso. pose proof (Hmin p ltac:(lia)). lia.
Qed.
Lemma np2ex_of_loop : forall K np, 0 <= K <= 16 -> np <= 2 ^ K -> (2 ^ K < 2 * np \/ K = 0) -> YO07.calcNextPower2Ex np = K.
Proof.
intros K np HK Hle Hmin. unfold YO07.calcNextPower2Ex. apply np2_aux_min; [lia | lia | exact Hle |].
intros q Hq. destruct Hmin as [Hmin | ->]; [|lia].
assert (E : 2 ^ K = 2 * 2 ^ (K - 1)) by (replace K with (K - 1 + 1) at 1 by lia; rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia).
assert (2 ^ q <= 2 ^ (K - 1)) by (apply Z.pow_le_mono_r; lia). lia.
Qed.
Lemma fl_tOpt_cases : forall g cur K, YO07.calcNextPower2Ex (YI0f.fl_npal g cur) = K -> 0 <= K <= 16 ->
(2 < K -> YI0f.fl_npal g cur <= (2 ^ K - 1) mod 256 -> YI0f.fl_tOpt g cur = (2 ^ K - 1) mod 256) /\
(2 < K -> (2 ^ K - 1) mod 256 < YI0f.fl_npal g cur -> YI0f.fl_tOpt g cur = (2 ^ (K + 1) - 1) mod 256) /\
(K <= 2 -> YI0f.fl_npal g cur <= 3 -> YI0f.fl_tOpt g cur = 3) /\
(K <= 2 -> 3 < YI0f.fl_npal g cur -> YI0f.fl_tOpt g cur = 7).
Proof.
intros g cur K HK RK. unfold YI0f.fl_tOpt, YI0f.fl_t0, YI0f.fl_p. rewrite HK.
repeat split; intros H1 H2.
- rewrite Z.max_r by lia. destruct (Z.ltb_spec ((2 ^ K - 1) mod 256) (YI0f.fl_npal g cur)); [lia | reflexivity].
- rewrite Z.max_r by lia. destruct (Z.ltb_spec ((2 ^ K - 1) mod 256) (YI0f.fl_npal g cur)); [reflexivity | lia].
- rewrite Z.max_l by lia. change ((2 ^ 2 - 1) mod 256) with 3. destruct (Z.ltb_spec 3 (YI0f.fl_npal g cur)); [lia | reflexivity].
- rewrite Z.max_l by lia. change ((2 ^ 2 - 1) mod 256) with 3. destruct (Z.ltb_spec 3 (YI0f.fl_npal g cur)); [reflexivity | lia].
Qed.
Lemma fl_tOpt_casesB : forall g cur K, YO07.calcNextPower2Ex (YI0f.fl_npal g cur) = K -> 0 <= K <= 16 ->
(2 <= K -> YI0f.fl_npal g cur <= (2 ^ K - 1) mod 256 -> YI0f.fl_tOpt g cur = (2 ^ K - 1) mod 256) /\
(2 <= K -> (2 ^ K - 1) mod 256 < YI0f.fl_npal g cur -> YI0f.fl_tOpt g cur = (2 ^ (K + 1) - 1) mod 256) /\
(K < 2 -> YI0f.fl_npal g cur <= 3 -> YI0f.fl_tOpt g cur = 3) /\
(K < 2 -> 3 < YI0f.fl_npal g cur -> YI0f.fl_tOpt g cur = 7).
Proof.
intros g cur K HK RK. unfold YI0f.fl_tOpt, YI0f.fl_t0, YI0f.fl_p. rewrite HK.
repeat split; intros H1 H2.
- rewrite Z.max_r by lia. destruct (Z.ltb_spec ((2 ^ K - 1) mod 256) (YI0f.fl_npal g cur)); [lia | reflexivity].
- rewrite Z.max_r by lia. destruct (Z.ltb_spec ((2 ^ K - 1) mod 256) (YI0f.fl_npal g cur)); [reflexivity | lia].
- rewrite Z.max_l by lia. change ((2 ^ 2 - 1) mod 256) with 3. destruct (Z.ltb_spec 3 (YI0f.fl_npal g cur)); [lia | reflexivity].
- rewrite Z.max_l by lia. change ((2 ^ 2 - 1) mod 256) with 3. destruct (Z.ltb_spec 3 (YI0f.fl_npal g cur)); [reflexivity | lia].
Qed.
