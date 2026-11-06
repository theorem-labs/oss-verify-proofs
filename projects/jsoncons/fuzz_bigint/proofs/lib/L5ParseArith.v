(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import BigModel BigFactsRun BigFactsDigits AxSymExec3 BigLinkBase.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5PA.
Import AX2.
(* [comment removed for export] *)
Lemma MM_val : BL.MM = 18446744073709551616. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma nwe_eval m : 10 <= m <= 4999 ->
  ((3402 * m) mod BL.MM / 1024 + 64) mod BL.MM / 64 = Z.of_nat (num_words_est (Z.to_nat m)).
Proof.
  intros Hm. rewrite MM_val.
  rewrite (Z.mod_small (3402 * m)) by lia.
  pose proof (Z.div_pos (3402 * m) 1024 ltac:(lia) ltac:(lia)) as B0.
  pose proof (Z.div_le_mono (3402 * m) 17006598 1024 ltac:(lia) ltac:(lia)) as B1. change (17006598 / 1024) with 16608 in B1.
  rewrite (Z.mod_small) by lia.
  unfold num_words_est. replace (Z.to_nat m <? 10)%nat with false.
  2: { symmetry. apply Nat.ltb_ge. lia. }
  rewrite (Z2Nat.id m) by lia.
  pose proof (Z.div_pos (m * 3402) 1024 ltac:(lia) ltac:(lia)) as B2.
  rewrite Z2Nat.id. 2: { apply Z.div_pos; lia. }
  replace (m * 3402) with (3402 * m) by lia. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma nwe_small m : 0 <= m <= 9 -> Z.of_nat (num_words_est (Z.to_nat m)) = 1.
Proof. intros Hm. unfold num_words_est. replace (Z.to_nat m <? 10)%nat with true. reflexivity. symmetry. apply Nat.ltb_lt. lia. Qed.

(* [comment removed for export] *)
Lemma land15_digit c : 48 <= c <= 57 -> Z.land c 15 = c - 48.
Proof.
  intros Hc.
  assert (H: c = 48 \/ c = 49 \/ c = 50 \/ c = 51 \/ c = 52 \/ c = 53 \/ c = 54 \/ c = 55 \/ c = 56 \/ c = 57) by lia.
  destruct H as [->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma shl3_eval cap : 0 <= cap <= 134217728 -> (cap * 8) mod BL.MM = 8 * cap.
Proof. intros. rewrite MM_val. rewrite Z.mod_small; lia. Qed.
Lemma shl3_eval' cap : 0 <= cap <= 134217728 -> (8 * cap) mod BL.MM = 8 * cap.
Proof. intros. rewrite MM_val. rewrite Z.mod_small; lia. Qed.

(* [comment removed for export] *)
Lemma setbit1_eval fb : 0 <= fb < 256 -> (Z.land fb 18446744073709551613 + 2) mod BL.MM = Z.lor fb 2.
Proof.
  intros Hfb. rewrite MM_val.
  assert (GEN: forall n : nat, (n < 256)%nat -> (Z.land (Z.of_nat n) 18446744073709551613 + 2) mod 18446744073709551616 = Z.lor (Z.of_nat n) 2).
  { intros n Hn. do 256 (destruct n as [|n]; [vm_compute; reflexivity|]). lia. }
  replace fb with (Z.of_nat (Z.to_nat fb)) by lia. apply GEN. lia.
Qed.

Lemma lor2_range fb : 0 <= fb < 256 -> 0 <= Z.lor fb 2 < 256.
Proof.
  intros Hfb.
  assert (GEN: forall n : nat, (n < 256)%nat -> 0 <= Z.lor (Z.of_nat n) 2 < 256).
  { intros n Hn. do 256 (destruct n as [|n]; [vm_compute; split; [discriminate|reflexivity] |]). lia. }
  replace fb with (Z.of_nat (Z.to_nat fb)) by lia. apply GEN. lia.
Qed.

(* [comment removed for export] *)
Lemma byte_cases (P : Z -> bool) : forallb (fun i => P (Z.of_nat i)) (seq 0 256) = true -> forall fb, 0 <= fb < 256 -> P fb = true.
Proof.
  intros H fb Hfb. rewrite forallb_forall in H. replace fb with (Z.of_nat (Z.to_nat fb)) by lia. apply H. apply in_seq. lia.
Qed.
(* [comment removed for export] *)
Lemma land252_div4 fb : 0 <= fb < 256 -> Z.land fb 252 = 4 * (fb / 4).
Proof.
  intros Hfb. pose proof (byte_cases (fun fb => Z.land fb 252 =? 4 * (fb / 4)) ltac:(vm_compute; reflexivity) fb Hfb) as X. cbn beta in X.
  apply Z.eqb_eq. exact X.
Qed.
Lemma land252_range fb : 0 <= fb < 256 -> 0 <= Z.land fb 252 < 256.
Proof. intros Hfb. rewrite land252_div4 by lia. lia. Qed.

End L5PA.
