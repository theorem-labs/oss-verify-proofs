(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from projects/cgif/cgif_file_fuzzer/proofs/lib/YI0j.v (donor image sha256 7093581aab04), with its module paths changed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO07.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition hdr13 (W H pk : Z) : list Z := [71; 73; 70; 56; 57; 97; W mod 256; (W / 256) mod 256; H mod 256; (H / 256) mod 256; pk; 0; 0].
Definition net19 (loops : Z) : list Z := [33; 255; 11; 78; 69; 84; 83; 67; 65; 80; 69; 50; 46; 48; 3; 1; loops mod 256; (loops / 256) mod 256; 0].
Definition gct_pad (sgct : Z) (gct : list Z) : list Z := firstn (Z.to_nat (sgct * 3)) gct ++ zeros (((2 ^ pal_pow sgct - sgct) * 3) mod 65536).
Definition has_net (rattr : Z) : bool := flag rattr 1 && negb (flag rattr 2).
Lemma raw_header_eq : forall W H sgct gct rattr loops,
raw_header W H sgct gct rattr loops =
hdr13 W H (if sgct =? 0 then 0 else 128 + (pal_pow sgct - 1)) ++ (if sgct =? 0 then [] else gct_pad sgct gct) ++ (if has_net rattr then net19 loops else []).
Proof. intros. unfold raw_header, hdr13, net19, gct_pad, has_net, u16le. cbn [app]. destruct (sgct =? 0), (flag rattr 1 && negb (flag rattr 2)); reflexivity. Qed.
Lemma testbit_small : forall k n, 0 <= k < 4 -> 2 <= n -> Z.testbit k n = false.
Proof. intros k n Hk Hn. destruct (Z.eq_dec k 0) as [-> | Hk0]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|]. assert (Z.log2 k < 2) by (apply Z.log2_lt_pow2; lia). lia. Qed.
Lemma land_bits01 : forall r m, 0 <= m < 4 -> Z.land r m = Z.b2z (Z.testbit r 0 && Z.testbit m 0) + 2 * Z.b2z (Z.testbit r 1 && Z.testbit m 1).
Proof.
intros r m Hm. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
set (b0 := Z.testbit r 0 && Z.testbit m 0). set (b1 := Z.testbit r 1 && Z.testbit m 1).
destruct (Z.eq_dec n 0) as [-> | Hn0]; [| destruct (Z.eq_dec n 1) as [-> | Hn1]].
- fold b0. destruct b0, b1; reflexivity.
- fold b1. destruct b0, b1; reflexivity.
- rewrite (testbit_small m n Hm ltac:(lia)), andb_false_r. symmetry. apply testbit_small; [destruct b0, b1; cbn; lia | lia].
Qed.
Lemma has_net_land : forall rattr, has_net rattr = (Z.land rattr 3 =? 1).
Proof.
intros rattr. unfold has_net, flag. rewrite (land_bits01 rattr 1), (land_bits01 rattr 2), (land_bits01 rattr 3) by lia.
change (Z.testbit 1 0) with true. change (Z.testbit 1 1) with false. change (Z.testbit 2 0) with false. change (Z.testbit 2 1) with true.
change (Z.testbit 3 0) with true. change (Z.testbit 3 1) with true. rewrite !andb_true_r, !andb_false_r.
destruct (Z.testbit rattr 0), (Z.testbit rattr 1); reflexivity.
Qed.
Lemma np2_class : forall k n, 0 <= k <= 16 -> (k = 0 -> n <= 1) -> (0 < k -> 2 ^ (k - 1) < n) -> n <= 2 ^ k -> calcNextPower2Ex n = k.
Proof.
intros k n Hk H0 Hlo Hhi. unfold calcNextPower2Ex.
assert (G : forall fuel p, 0 <= p <= k -> (Z.of_nat fuel > k - p) -> np2_aux fuel n p = k).
{ induction fuel as [|fuel IH]; intros p Hp Hf; [lia|]. cbn [np2_aux].
destruct (Z.ltb_spec (2 ^ p) n) as [Hlt | Hge].
- assert (p < k). { destruct (Z.eq_dec p k) as [-> | ]; [lia | lia]. } apply IH; lia.
- destruct (Z.eq_dec p k) as [-> | Hne]; [reflexivity | exfalso].
assert (0 < k) by lia. specialize (Hlo H). assert (2 ^ p <= 2 ^ (k - 1)) by (apply Z.pow_le_mono_r; lia). lia. }
apply G; lia.
Qed.
Lemma pal_pow_class : forall k n, 0 <= k <= 16 -> (k = 0 -> n <= 1) -> (0 < k -> 2 ^ (k - 1) < n) -> n <= 2 ^ k -> pal_pow n = Z.max 1 k.
Proof. intros. unfold pal_pow. rewrite (np2_class k n) by assumption. reflexivity. Qed.
Lemma raw_header_class : forall k K2 W H sgct GCT rattr loops,
0 <= k <= 8 -> K2 = 2 ^ Z.max 1 k -> 1 <= sgct -> (k = 0 -> sgct <= 1) -> (0 < k -> 2 ^ (k - 1) < sgct) -> sgct <= 2 ^ k ->
raw_header W H sgct GCT rattr loops =
hdr13 W H (128 + (Z.max 1 k - 1)) ++ (firstn (Z.to_nat (3 * sgct)) GCT ++ repeat 0 (Z.to_nat (3 * (K2 - sgct)))) ++ (if has_net rattr then net19 loops else []).
Proof.
intros k K2 W H sgct GCT rattr loops Hk -> Hs1 H0 Hlo Hhi. rewrite raw_header_eq.
replace (sgct =? 0) with false by (symmetry; apply Z.eqb_neq; lia). unfold gct_pad, zeros.
rewrite (pal_pow_class k sgct ltac:(lia) H0 Hlo Hhi). rewrite (Z.mul_comm sgct 3).
assert (Hle : sgct <= 2 ^ Z.max 1 k) by (assert (2 ^ k <= 2 ^ Z.max 1 k) by (apply Z.pow_le_mono_r; lia); lia).
assert (Hub : 2 ^ Z.max 1 k <= 2 ^ 8) by (apply Z.pow_le_mono_r; lia). change (2 ^ 8) with 256 in Hub.
rewrite (Z.mod_small ((2 ^ Z.max 1 k - sgct) * 3) 65536) by lia. rewrite (Z.mul_comm (2 ^ Z.max 1 k - sgct) 3). reflexivity.
Qed.
