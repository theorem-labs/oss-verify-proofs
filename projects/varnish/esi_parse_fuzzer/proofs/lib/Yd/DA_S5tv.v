(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ShapeAlg Shapi1s Spec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Definition cap (k : nat) : Z := (65536 * 2 ^ (Z.of_nat k))%Z.

Lemma cap_range : forall k, (k <= 10)%nat -> (65536 <= cap k <= 67108864)%Z.
Proof.
  intros k Hk. unfold cap. assert (1 <= 2 ^ Z.of_nat k <= 2 ^ 10)%Z.
  { split; [| apply Z.pow_le_mono_r; lia]. assert (0 < 2 ^ Z.of_nat k)%Z by (apply Z.pow_pos_nonneg; lia). lia. }
  change 67108864%Z with (65536 * 2 ^ 10)%Z. lia.
Qed.

Lemma cap_S : forall k, cap (S k) = (2 * cap k)%Z.
Proof. intros k. unfold cap. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia. Qed.

(* [comment removed for export] *)
Fixpoint lshape (data : list byte) (fs : Fs.Fs) (fuel : nat) (k : nat) (len : Z) : TSet :=
  match fuel with
  | O => t_nil
  | S f =>
      let L := Z.of_nat (length data) in
      if (len =? cap k)%Z then
        if (10 <=? Z.of_nat k)%Z then t_die msg_refused fs
        else lshape data fs f (S k) len    (* [comment removed for export] *)
      else
        let n := Z.min (Z.min (cap k - len) 65536) (L - len) in
        if (n =? 0)%Z then t_body data fs
        else lshape data fs f k (len + n)
  end.

(* [comment removed for export] *)
Lemma lshape_opened : forall data fs f k len,
  (Z.of_nat (length data) - len + 11 - Z.of_nat k < Z.of_nat f)%Z ->
  (k <= 10)%nat -> (0 <= len <= cap k)%Z -> (len <= Z.of_nat (length data))%Z ->
  (len = cap k \/ cap k <= 2 ^ 26)%Z ->
  t_eq (lshape data fs f k len) (t_opened data fs).
Proof.
  intros data fs f. induction f as [|f IH]; intros k len Hf Hk Hlen HL Hcap; [lia|].
  cbn [lshape]. set (L := Z.of_nat (length data)) in *.
  assert (CAPk : (cap k <= 2 ^ 26)%Z).
  { destruct Hcap as [->|H]; [|exact H]. unfold cap.
    assert (2 ^ Z.of_nat k <= 2 ^ 10)%Z by (apply Z.pow_le_mono_r; lia). change (2 ^ 26)%Z with (65536 * 2 ^ 10)%Z. lia. }
  destruct (Z.eqb_spec len (cap k)) as [E|NE].
  - destruct (Z.leb_spec 10 (Z.of_nat k)) as [K10|K10].
    + assert (k = 10)%nat by lia. subst k. unfold t_opened, t_body.
      change (cap 10) with 67108864%Z in E.
      replace (MAX_INPUT <=? Z.of_nat (length data))%Z with true by (symmetry; apply Z.leb_le; unfold MAX_INPUT; lia).
      apply t_eq_refl.
    + apply IH; try lia.
      * unfold cap in *. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia.
      * right. unfold cap in *. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
        assert (2 ^ Z.of_nat k <= 2 ^ 9)%Z by (apply Z.pow_le_mono_r; lia). change (2 ^ 26)%Z with (65536 * (2 * 2 ^ 9))%Z. lia.
  - set (n := Z.min (Z.min (cap k - len) 65536) (L - len)).
    destruct (Z.eqb_spec n 0) as [N0|N0].
    + assert (len = L) by (subst n; lia). unfold t_opened. apply t_eq_refl.
    + apply IH; subst n; lia.
Qed.
