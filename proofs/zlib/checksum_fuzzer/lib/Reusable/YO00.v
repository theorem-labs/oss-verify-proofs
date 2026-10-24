(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0z.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Fixpoint udigits_aux (v : Z) (fuel : nat) : list Z :=
match fuel with
| O => []
| S f => if v =? 0 then []
else udigits_aux (v / 10) f ++ [48 + v mod 10]
end.
Definition dec_fuel : nat := 24%nat.
Definition udecZ (v : Z) : list Z :=
if v =? 0 then [48] else udigits_aux v dec_fuel.
Definition sdecZ (v : Z) : list Z :=
if v <? 0 then 45 :: udecZ (- v) else udecZ v.
Definition to_bytes (l : list Z) : list byte := map (Z_to_bv 8) l.
Example sdecZ_ex0 : sdecZ 0 = [48].                 Proof. reflexivity. Qed.
Example sdecZ_ex1 : sdecZ 7 = [55].                 Proof. reflexivity. Qed.
Example sdecZ_ex2 : sdecZ (-3) = [45; 51].          Proof. reflexivity. Qed.
Example sdecZ_ex3 : sdecZ 1024 = [49; 48; 50; 52].  Proof. reflexivity. Qed.
Example sdecZ_ex4 : sdecZ (-12) = [45; 49; 50].     Proof. reflexivity. Qed.
Example udecZ_ex5 : udecZ 67108864 = [54;55;49;48;56;56;54;52]. Proof. reflexivity. Qed.
Lemma udigits_aux_S : forall f v,
udigits_aux v (S f)
= if v =? 0 then [] else udigits_aux (v / 10) f ++ [48 + v mod 10].
Proof. reflexivity. Qed.
Lemma udigits_aux_fuel : forall f g v,
0 <= v -> v < 10 ^ (Z.of_nat f) -> (f <= g)%nat ->
udigits_aux v g = udigits_aux v f.
Proof.
induction f as [|f IH]; intros g v Hv0 Hv Hfg.
- cbn in Hv. assert (v = 0) by lia. subst v.
destruct g; reflexivity.
- destruct g as [|g]; [lia|].
rewrite !udigits_aux_S. destruct (v =? 0) eqn:Ev; [reflexivity|].
rewrite (IH g (v / 10)); [reflexivity| | |lia].
+ apply Z.div_pos; lia.
+ apply Z.div_lt_upper_bound; [lia|].
replace (10 * 10 ^ Z.of_nat f) with (10 ^ Z.of_nat (S f)); [exact Hv|].
rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity.
Qed.
Lemma udecZ_0 : udecZ 0 = [48].
Proof. reflexivity. Qed.
Lemma udecZ_single : forall v, 1 <= v <= 9 -> udecZ v = [48 + v].
Proof.
intros v Hv. unfold udecZ, dec_fuel.
rewrite (proj2 (Z.eqb_neq v 0)) by lia.
rewrite (udigits_aux_fuel 1 24 v); [| lia | cbn; lia | lia].
rewrite udigits_aux_S.
rewrite (proj2 (Z.eqb_neq v 0)) by lia.
cbn [udigits_aux app]. rewrite Z.mod_small by lia. reflexivity.
Qed.
Lemma pow10_20_gt' : 2^64 < 10^20.
Proof. vm_compute. reflexivity. Qed.
Lemma udecZ_step : forall v, 10 <= v -> v < 2^64 ->
udecZ v = udecZ (v / 10) ++ [48 + v mod 10].
Proof.
intros v Hv10 Hv64. unfold udecZ, dec_fuel.
rewrite (proj2 (Z.eqb_neq v 0)) by lia.
assert (Hd : v / 10 <> 0).
{ pose proof (Z.div_str_pos v 10 ltac:(lia)). lia. }
rewrite (proj2 (Z.eqb_neq (v/10) 0)) by exact Hd.
change 24%nat with (S 23%nat) at 1. rewrite udigits_aux_S.
rewrite (proj2 (Z.eqb_neq v 0)) by lia.
rewrite (udigits_aux_fuel 23 24 (v / 10)); [reflexivity| | |lia].
- apply Z.div_pos; lia.
- assert (v / 10 < 2^64)
by (pose proof (Z.div_le_upper_bound v 10 v ltac:(lia) ltac:(lia)); lia).
assert (10^20 <= 10^(Z.of_nat 23))
by (apply Z.pow_le_mono_r; [lia|change (Z.of_nat 23) with 23; lia]).
pose proof pow10_20_gt'. lia.
Qed.
Lemma udigits_aux_len : forall f v, (length (udigits_aux v f) <= f)%nat.
Proof.
induction f as [|f IH]; intro v; cbn [udigits_aux]; [cbn; lia|].
destruct (v =? 0); cbn [length]; [lia|].
rewrite length_app. cbn [length]. specialize (IH (v / 10)). lia.
Qed.
Lemma udecZ_len_le : forall v, 0 <= v -> v < 2^64 -> (length (udecZ v) <= 20)%nat.
Proof.
intros v Hv0 Hv. unfold udecZ, dec_fuel. destruct (v =? 0) eqn:Ev; [cbn; lia|].
rewrite (udigits_aux_fuel 20 24 v); [apply udigits_aux_len| lia | |lia].
pose proof pow10_20_gt'. change (Z.of_nat 20) with 20. lia.
Qed.
Lemma udecZ_len_pos : forall v, (1 <= length (udecZ v))%nat.
Proof.
intro v. unfold udecZ, dec_fuel. destruct (Z.eqb_spec v 0) as [->|Hnz]; [cbn; lia|].
change 24%nat with (S 23%nat). rewrite udigits_aux_S.
rewrite (proj2 (Z.eqb_neq v 0)) by exact Hnz.
rewrite length_app. cbn [length]. lia.
Qed.
Lemma udigits_aux_digits : forall f v, 0 <= v ->
Forall (fun d => 48 <= d <= 57) (udigits_aux v f).
Proof.
induction f as [|f IH]; intros v Hv; cbn [udigits_aux]; [constructor|].
destruct (v =? 0); [constructor|].
apply Forall_app. split.
- apply IH. apply Z.div_pos; lia.
- constructor; [|constructor].
pose proof (Z.mod_pos_bound v 10 ltac:(lia)). lia.
Qed.
Lemma udecZ_digits : forall v, 0 <= v -> Forall (fun d => 48 <= d <= 57) (udecZ v).
Proof.
intros v Hv. unfold udecZ. destruct (v =? 0).
- constructor; [lia|constructor].
- apply udigits_aux_digits; exact Hv.
Qed.
Lemma sdecZ_nonneg : forall v, 0 <= v -> sdecZ v = udecZ v.
Proof. intros v Hv. unfold sdecZ. destruct (Z.ltb_spec v 0); [lia|reflexivity]. Qed.
Lemma sdecZ_neg : forall v, v < 0 -> sdecZ v = 45 :: udecZ (- v).
Proof. intros v Hv. unfold sdecZ. destruct (Z.ltb_spec v 0); [reflexivity|lia]. Qed.
Lemma sdecZ_len_pos : forall v, (1 <= length (sdecZ v))%nat.
Proof.
intro v. unfold sdecZ. destruct (v <? 0); cbn [length];
[pose proof (udecZ_len_pos (-v)); lia | apply udecZ_len_pos].
Qed.
Lemma sdecZ_range : forall v, Forall (fun d => 0 <= d < 256) (sdecZ v).
Proof.
intro v. unfold sdecZ. destruct (Z.ltb_spec v 0).
- constructor; [lia|].
eapply Forall_impl; [|apply (udecZ_digits (-v)); lia]. cbn; intros; lia.
- eapply Forall_impl; [|apply (udecZ_digits v); lia]. cbn; intros; lia.
Qed.
Lemma udigits_aux_udec_aux : forall f v,
to_bytes (udigits_aux v f) = YK0z.udec_aux v f.
Proof.
induction f as [|f IH]; intro v; cbn [udigits_aux YK0z.udec_aux]; [reflexivity|].
destruct (v =? 0); [reflexivity|].
unfold to_bytes in *. rewrite map_app. cbn [map]. rewrite IH. reflexivity.
Qed.
Lemma udecZ_udec : forall v, to_bytes (udecZ v) = YK0z.udec v.
Proof.
intro v. unfold udecZ, YK0z.udec, dec_fuel.
destruct (v =? 0); [reflexivity|apply udigits_aux_udec_aux].
Qed.
Definition strZ (s : string) : list Z :=
map (fun a => Z.of_N (N_of_ascii a)) (list_ascii_of_string s).
Definition strB (s : string) : list byte := to_bytes (strZ s).
Definition nl : list byte := to_bytes [10].
