(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section ExpDigits.
  Variable bs : list Z.

  Fixpoint dval_n (q : Z) (c : nat) : Z :=
    match c with O => 0 | S c' => dval_n q c' * 10 + (B bs (q + Z.of_nat c') - 48) end.

  Definition dval (q c : Z) : Z := dval_n q (Z.to_nat c).
  Definition digits (q c : Z) : Prop := forall i, 0 <= i < c -> 48 <= B bs (q + i) <= 57.
  Definition zeros (q z : Z) : Prop := forall i, 0 <= i < z -> B bs (q + i) = 48.

  Lemma dval_0 : forall q, dval q 0 = 0.
  Proof. reflexivity. Qed.

  Lemma dval_S : forall q c, 0 <= c -> dval q (c + 1) = dval q c * 10 + (B bs (q + c) - 48).
  Proof.
    intros q c Hc. unfold dval. replace (Z.to_nat (c + 1)) with (S (Z.to_nat c)) by lia.
    cbn [dval_n]. rewrite Z2Nat.id by lia. reflexivity.
  Qed.

  Lemma digits_0 : forall q, digits q 0.
  Proof. intros q i Hi. lia. Qed.
  Lemma digits_S : forall q c, 0 <= c -> digits q c -> 48 <= B bs (q + c) <= 57 -> digits q (c + 1).
  Proof. intros q c Hc H HB i Hi. destruct (Z.eq_dec i c) as [->|NE]; [exact HB| apply H; lia]. Qed.
  Lemma zeros_0 : forall q, zeros q 0.
  Proof. intros q i Hi. lia. Qed.
  Lemma zeros_S : forall q z, 0 <= z -> zeros q z -> B bs (q + z) = 48 -> zeros q (z + 1).
  Proof. intros q z Hz H HB i Hi. destruct (Z.eq_dec i z) as [->|NE]; [exact HB| apply H; lia]. Qed.

  Lemma dval_n_bound : forall q c, (forall i, (i < c)%nat -> 48 <= B bs (q + Z.of_nat i) <= 57) -> 0 <= dval_n q c < 10 ^ Z.of_nat c.
  Proof.
    intros q c. induction c as [|c IH]; intros H; [cbn; lia|].
    cbn [dval_n]. specialize (IH ltac:(intros i Hi; apply H; lia)). pose proof (H c ltac:(lia)) as HB.
    replace (Z.of_nat (S c)) with (Z.of_nat c + 1) by lia. rewrite Z.pow_add_r by lia. change (10 ^ 1) with 10. lia.
  Qed.

  Lemma dval_bound : forall q c, 0 <= c -> digits q c -> 0 <= dval q c < 10 ^ c.
  Proof.
    intros q c Hc H. unfold dval. pose proof (dval_n_bound q (Z.to_nat c)) as HB. rewrite Z2Nat.id in HB by lia.
    apply HB. intros i Hi. apply H. lia.
  Qed.

  Lemma dval_n_zeros : forall q z, (forall i, (i < z)%nat -> B bs (q + Z.of_nat i) = 48) -> dval_n q z = 0.
  Proof.
    intros q z. induction z as [|z IH]; intros H; [reflexivity|].
    cbn [dval_n]. rewrite IH by (intros i Hi; apply H; lia). rewrite (H z) by lia. reflexivity.
  Qed.

  Lemma dval_n_skip : forall q z n, (forall i, (i < z)%nat -> B bs (q + Z.of_nat i) = 48) ->
    dval_n q (z + n) = dval_n (q + Z.of_nat z) n.
  Proof.
    intros q z n H. induction n as [|n IH].
    - rewrite Nat.add_0_r. cbn [dval_n]. apply dval_n_zeros. exact H.
    - replace (z + S n)%nat with (S (z + n)) by lia. cbn [dval_n]. rewrite IH. f_equal. f_equal. f_equal. lia.
  Qed.

  Lemma dval_lt18 : forall q c z, 0 <= z <= c -> c - z <= 18 -> digits q c -> zeros q z -> 0 <= dval q c < 10 ^ 18.
  Proof.
    intros q c z Hz H18 HD HZ. unfold dval.
    replace (Z.to_nat c) with (Z.to_nat z + Z.to_nat (c - z))%nat by lia.
    rewrite dval_n_skip by (intros i Hi; apply HZ; lia).
    pose proof (dval_n_bound (q + Z.of_nat (Z.to_nat z)) (Z.to_nat (c - z))) as HB.
    specialize (HB ltac:(intros i Hi; replace (q + Z.of_nat (Z.to_nat z) + Z.of_nat i) with (q + (z + Z.of_nat i)) by lia; apply HD; lia)).
    rewrite !Z2Nat.id in HB by lia. rewrite Z2Nat.id by lia.
    assert (H10 : 10 ^ (c - z) <= 10 ^ 18) by (apply Z.pow_le_mono_r; lia).
    set (P := 10 ^ (c - z)) in *. set (V := dval_n _ _) in *. change (10 ^ 18) with 1000000000000000000 in *. lia.
  Qed.
End ExpDigits.
