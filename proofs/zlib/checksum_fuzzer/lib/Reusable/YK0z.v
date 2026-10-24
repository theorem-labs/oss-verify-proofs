(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
Unset Lia Cache. Unset Nia Cache.
Import ListNotations.
Local Open Scope Z_scope.
Fixpoint udec_aux (v : Z) (fuel : nat) : list byte :=
match fuel with
| O => []
| S f => if v =? 0 then []
else udec_aux (v / 10) f ++ [Z_to_bv 8 (48 + v mod 10)]
end.
Definition udec (v : Z) : list byte :=
if v =? 0 then [Z_to_bv 8 48] else udec_aux v 24.
Lemma udec_aux_fuel : forall f g v,
0 <= v -> v < 10^(Z.of_nat f) -> (f <= g)%nat -> udec_aux v g = udec_aux v f.
Proof.
induction f as [|f IH]; intros g v Hv0 Hv Hfg.
- cbn in Hv. assert (v = 0) by lia. subst v.
destruct g as [|g]; [reflexivity|]. cbn [udec_aux]. reflexivity.
- destruct g as [|g]; [lia|].
cbn [udec_aux]. destruct (v =? 0) eqn:Ev; [reflexivity|].
rewrite (IH g (v / 10)); [reflexivity| | |lia].
+ apply Z.div_pos; lia.
+ apply Z.div_lt_upper_bound; [lia|].
replace (10 * 10 ^ Z.of_nat f) with (10 ^ Z.of_nat (S f)); [exact Hv|].
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity.
Qed.
Lemma pow10_20_gt : 2^64 < 10^20.
Proof. vm_compute. reflexivity. Qed.
Lemma udec_aux_S : forall f v,
udec_aux v (S f) = if v =? 0 then []
else udec_aux (v / 10) f ++ [Z_to_bv 8 (48 + v mod 10)].
Proof. reflexivity. Qed.
Lemma udec_single : forall v, 1 <= v <= 9 -> udec v = [Z_to_bv 8 (48 + v)].
Proof.
intros v Hv. unfold udec.
rewrite (proj2 (Z.eqb_neq v 0)) by lia.
rewrite (udec_aux_fuel 1 24 v); [| lia | cbn; lia | lia].
change 1%nat with (S 0%nat). rewrite udec_aux_S.
rewrite (proj2 (Z.eqb_neq v 0)) by lia.
cbn [udec_aux app]. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma udec_step : forall v, 10 <= v -> v < 2^64 ->
udec v = udec (v / 10) ++ [Z_to_bv 8 (48 + v mod 10)].
Proof.
intros v Hv10 Hv64. unfold udec.
rewrite (proj2 (Z.eqb_neq v 0)) by lia.
assert (Hd : v / 10 <> 0).
{ pose proof (Z.div_str_pos v 10 ltac:(lia)). lia. }
rewrite (proj2 (Z.eqb_neq (v/10) 0)) by exact Hd.
change 24%nat with (S 23%nat). rewrite udec_aux_S.
rewrite (proj2 (Z.eqb_neq v 0)) by lia.
rewrite (udec_aux_fuel 23 24 (v / 10)); [reflexivity| | |lia].
- apply Z.div_pos; lia.
- assert (v / 10 < 2^64)
by (pose proof (Z.div_le_upper_bound v 10 v ltac:(lia) ltac:(lia)); lia).
assert (10^20 <= 10^(Z.of_nat 23))
by (apply Z.pow_le_mono_r; [lia|change (Z.of_nat 23) with 23; lia]).
pose proof pow10_20_gt. lia.
Qed.
Lemma udec_aux_len : forall f v, (length (udec_aux v f) <= f)%nat.
Proof.
induction f as [|f IH]; intro v; cbn [udec_aux]; [cbn; lia|].
destruct (v =? 0); cbn [length]; [lia|].
rewrite length_app. cbn [length]. specialize (IH (v / 10)). lia.
Qed.
Lemma udec_len_le : forall v, 0 <= v -> v < 2^64 -> (length (udec v) <= 20)%nat.
Proof.
intros v Hv0 Hv. unfold udec. destruct (v =? 0) eqn:Ev; [cbn; lia|].
rewrite (udec_aux_fuel 20 24 v); [apply udec_aux_len| lia | |lia].
pose proof pow10_20_gt. change (Z.of_nat 20) with 20. lia.
Qed.
Lemma udec_len_pos : forall v, (1 <= length (udec v))%nat.
Proof.
intro v. unfold udec. destruct (Z.eqb_spec v 0) as [->|Hnz]; [cbn; lia|].
change 24%nat with (S 23%nat). rewrite udec_aux_S.
rewrite (proj2 (Z.eqb_neq v 0)) by exact Hnz.
rewrite length_app. cbn [length]. lia.
Qed.
