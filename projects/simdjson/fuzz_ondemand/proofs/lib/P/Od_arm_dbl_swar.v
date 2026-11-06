(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjNumSwar.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma swar8n_hi : forall v W,
  Z.lor (Z.land W 1085102592571150095) (Z.land v 17361641481138401520) = 3689348814741910323 ->
  Z.land v 17361641481138401520 = 3472328296227680304.
Proof.
  intros v W H. apply (f_equal (fun x => Z.land x 17361641481138401520)) in H.
  rewrite Z.land_lor_distr_l in H. rewrite <- !Z.land_assoc in H.
  change (Z.land 1085102592571150095 17361641481138401520) with 0 in H.
  change (Z.land 17361641481138401520 17361641481138401520) with 17361641481138401520 in H.
  change (Z.land 3689348814741910323 17361641481138401520) with 3472328296227680304 in H.
  rewrite Z.land_0_r, Z.lor_0_l in H. exact H.
Qed.

Lemma nib_step : forall b w' Mn Rn, 0 <= b < 256 ->
  Z.land (b + 256 * w') (240 + 256 * Mn) = 48 + 256 * Rn -> 48 <= b <= 63 /\ Z.land w' Mn = Rn.
Proof.
  intros b w' Mn Rn Hb H. split.
  - pose proof (f_equal (fun x => Z.shiftr x 4 mod 2 ^ 4) H) as S. cbv beta in S.
    rewrite Z.shiftr_land, land_mod_distr in S by lia.
    rewrite !Z.shiftr_div_pow2 in S by lia. change (2 ^ 4) with 16 in S.
    replace ((b + 256 * w') / 16 mod 16) with (b / 16) in S by (Z.div_mod_to_equations; lia).
    replace ((240 + 256 * Mn) / 16 mod 16) with 15 in S by (Z.div_mod_to_equations; lia).
    replace ((48 + 256 * Rn) / 16 mod 16) with 3 in S by (Z.div_mod_to_equations; lia).
    change 15 with (Z.ones 4) in S. rewrite Z.land_ones in S by lia. change (2 ^ 4) with 16 in S.
    Z.div_mod_to_equations; lia.
  - pose proof (f_equal (fun x => Z.shiftr x 8) H) as S. cbv beta in S.
    rewrite Z.shiftr_land, !Z.shiftr_div_pow2 in S by lia. change (2 ^ 8) with 256 in S.
    replace ((b + 256 * w') / 256) with w' in S by (Z.div_mod_to_equations; lia).
    replace ((240 + 256 * Mn) / 256) with Mn in S by (Z.div_mod_to_equations; lia).
    replace ((48 + 256 * Rn) / 256) with Rn in S by (Z.div_mod_to_equations; lia).
    exact S.
Qed.

Lemma swar8n_horner : forall b0 b1 b2 b3 b4 b5 b6 b7 W,
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 -> 0 <= b7 < 256 ->
  Z.lor (Z.land W 1085102592571150095)
        (Z.land (b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))))) 17361641481138401520)
    = 3689348814741910323 ->
  48 <= b0 /\ 48 <= b1 /\ 48 <= b2 /\ 48 <= b3 /\ 48 <= b4 /\ 48 <= b5 /\ 48 <= b6 /\ 48 <= b7.
Proof.
  intros b0 b1 b2 b3 b4 b5 b6 b7 W H0 H1 H2 H3 H4 H5 H6 H7 H.
  apply swar8n_hi in H.
  change 17361641481138401520 with (240 + 256 * (240 + 256 * (240 + 256 * (240 + 256 * (240 + 256 * (240 + 256 * (240 + 256 * (240 + 256 * 0)))))))) in H.
  change 3472328296227680304 with (48 + 256 * (48 + 256 * (48 + 256 * (48 + 256 * (48 + 256 * (48 + 256 * (48 + 256 * (48 + 256 * 0)))))))) in H.
  apply nib_step in H; [|assumption]. destruct H as [G0 H]. split; [lia|].
  apply nib_step in H; [|assumption]. destruct H as [G1 H]. split; [lia|].
  apply nib_step in H; [|assumption]. destruct H as [G2 H]. split; [lia|].
  apply nib_step in H; [|assumption]. destruct H as [G3 H]. split; [lia|].
  apply nib_step in H; [|assumption]. destruct H as [G4 H]. split; [lia|].
  apply nib_step in H; [|assumption]. destruct H as [G5 H]. split; [lia|].
  apply nib_step in H; [|assumption]. destruct H as [G6 H]. split; [lia|].
  replace b7 with (b7 + 256 * 0) in H by lia.
  apply nib_step in H; [|assumption]. destruct H as [G7 H]. lia.
Qed.

Theorem swar8n_machine : forall b0 b1 b2 b3 b4 b5 b6 b7 W,
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 -> 0 <= b4 < 256 -> 0 <= b5 < 256 -> 0 <= b6 < 256 -> 0 <= b7 < 256 ->
  Z.lor (Z.land W 1085102592571150095) (Z.land (le8z b0 b1 b2 b3 b4 b5 b6 b7) 17361641481138401520) = 3689348814741910323 ->
  48 <= b0 /\ 48 <= b1 /\ 48 <= b2 /\ 48 <= b3 /\ 48 <= b4 /\ 48 <= b5 /\ 48 <= b6 /\ 48 <= b7.
Proof.
  intros b0 b1 b2 b3 b4 b5 b6 b7 W H0 H1 H2 H3 H4 H5 H6 H7 H.
  rewrite le8z_eq in H by assumption. eapply swar8n_horner; eassumption.
Qed.
