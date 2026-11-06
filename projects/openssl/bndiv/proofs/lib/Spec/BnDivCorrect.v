(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnWordsCorrect BnDivWords BnModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma BW_2_63 : BW = 2 * 2 ^ 63. Proof. reflexivity. Qed.

Section Qhat.
Variables d0 d1 n0 n1 n2 : Z.
Hypothesis Hd0 : 2 ^ 63 <= d0 < BW.
Hypothesis Hd1 : 0 <= d1 < BW.
Hypothesis Hn0 : 0 <= n0 < BW.
Hypothesis Hn1 : 0 <= n1 < BW.
Hypothesis Hn2 : 0 <= n2 < BW.

Let V2 := d0 * BW + d1.
Let U3 := (n0 * BW + n1) * BW + n2.

(* [comment removed for export] *)
Lemma qhat_test_iff : forall q rem, 0 <= q < BW -> 0 <= rem < BW -> q * d0 + rem = n0 * BW + n1 ->
  let t2 := d1 * q in
  ((t2 / BW <? rem) || ((t2 / BW =? rem) && (t2 mod BW <=? n2)) = true <-> q * V2 <= U3).
Proof.
  intros q rem Hq Hrem Hinv t2. pose proof BW_pos as BWp.
  pose proof (Z.div_mod t2 BW ltac:(lia)) as Edm. pose proof (Z.mod_pos_bound t2 BW BWp) as Hm.
  assert (EqV : q * V2 = (n0 * BW + n1 - rem) * BW + t2) by (subst V2 t2; rewrite <- Hinv; ring).
  rewrite EqV. subst U3.
  destruct (Z.ltb_spec (t2 / BW) rem) as [H1|H1]; cbn [orb].
  - split; [intros _|reflexivity]. nia.
  - destruct (Z.eqb_spec (t2 / BW) rem) as [H2|H2]; cbn [andb].
    + rewrite Z.leb_le. split; intros; nia.
    + split; [discriminate|]. intros H. exfalso. nia.
Qed.

(* [comment removed for export] *)
Lemma qhat_corr_spec : forall fuel q rem qt,
  0 <= q < BW -> 0 <= rem < BW -> q * d0 + rem = n0 * BW + n1 ->
  0 <= qt <= q -> qt * V2 <= U3 ->
  BW <= rem + Z.of_nat fuel * d0 - d0 ->
  let t2 := d1 * q in
  let q' := qhat_corr fuel q rem (t2 mod BW) (t2 / BW) n2 d0 d1 in
  qt <= q' <= q /\ q' * V2 <= U3.
Proof.
  pose proof BW_pos as BWp.
  assert (HV2 : BW <= V2).
  { subst V2. assert (1 * BW <= d0 * BW) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
  induction fuel as [|f IH]; intros q rem qt Hq Hrem Hinv Hqt HqtV Hfuel; cbv zeta.
  - exfalso. change (Z.of_nat 0) with 0 in Hfuel. lia.
  - cbn [qhat_corr]. pose proof (qhat_test_iff q rem Hq Hrem Hinv) as Htest. cbv zeta in Htest.
    destruct ((d1 * q / BW <? rem) || ((d1 * q / BW =? rem) && ((d1 * q) mod BW <=? n2))) eqn:Eb.
    + split; [lia|]. apply Htest. reflexivity.
    + assert (Hgt : U3 < q * V2).
      { destruct (Z.le_gt_cases (q * V2) U3) as [Hle|]; [|assumption]. apply Htest in Hle. congruence. }
      assert (Hq1 : qt <= q - 1).
      { assert (qt < q); [|lia]. apply Z.mul_lt_mono_pos_r with V2; lia. }
      assert (E1 : subw q 1 = q - 1) by (unfold subw; apply Z.mod_small; lia).
      rewrite E1. unfold addw.
      destruct (Z.lt_ge_cases (rem + d0) BW) as [Hno|Hov].
      * (* [comment removed for export] *)
        rewrite (Z.mod_small (rem + d0) BW) by lia.
        destruct (Z.ltb_spec (rem + d0) d0) as [|_]; [lia|].
        pose proof (Z.div_mod (d1 * q) BW ltac:(lia)) as Edm. pose proof (Z.mod_pos_bound (d1 * q) BW BWp) as Hm.
        assert (Hq0 : 0 <= d1 * (q - 1)) by (apply Z.mul_nonneg_nonneg; lia).
        assert (Hhi : 0 <= d1 * q / BW) by (apply Z.div_pos; [apply Z.mul_nonneg_nonneg|]; lia).
        (* [comment removed for export] *)
        assert (Et : subw ((d1 * q) mod BW) d1 = (d1 * (q - 1)) mod BW /\
                     (if (d1 * q) mod BW <? d1 then subw (d1 * q / BW) 1 else d1 * q / BW) = d1 * (q - 1) / BW).
        { assert (Ex : d1 * (q - 1) = BW * (d1 * q / BW) + ((d1 * q) mod BW - d1)) by lia.
          destruct (Z.ltb_spec ((d1 * q) mod BW) d1) as [Hb|Hb].
          - assert (Hhi1 : 1 <= d1 * q / BW).
            { destruct (Z.eq_dec (d1 * q / BW) 0) as [E0|]; [|lia]. rewrite E0 in Ex. lia. }
            assert (Ex2 : d1 * (q - 1) = (d1 * q / BW - 1) * BW + ((d1 * q) mod BW - d1 + BW)) by lia.
            destruct (divmod_BW (d1 * q / BW - 1) ((d1 * q) mod BW - d1 + BW) ltac:(lia)) as [Ed Em].
            rewrite Ex2, Ed, Em. split.
            + unfold subw. rewrite <- (Z.mod_add _ 1 BW) by lia. apply Z.mod_small. lia.
            + unfold subw. apply Z.mod_small.
              assert (d1 * q / BW < BW); [|lia]. apply Z.div_lt_upper_bound; [lia|]. apply (mul_bound d1 q BW BW); lia.
          - assert (Ex2 : d1 * (q - 1) = (d1 * q / BW) * BW + ((d1 * q) mod BW - d1)) by lia.
            destruct (divmod_BW (d1 * q / BW) ((d1 * q) mod BW - d1) ltac:(lia)) as [Ed Em].
            rewrite Ex2, Ed, Em. split; [|reflexivity]. unfold subw. apply Z.mod_small. lia. }
        destruct Et as [Et1 Et2]. rewrite Et1, Et2.
        specialize (IH (q - 1) (rem + d0) qt ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HqtV
                       ltac:(rewrite Nat2Z.inj_succ in Hfuel; lia)).
        cbv zeta in IH. destruct IH as [IH1 IH2]. split; [lia|exact IH2].
      * (* [comment removed for export] *)
        assert (Em : (rem + d0) mod BW = rem + d0 - BW).
        { rewrite <- (Z.mod_add _ (-1) BW) by lia. apply Z.mod_small. lia. }
        rewrite Em. destruct (Z.ltb_spec (rem + d0 - BW) d0) as [_|]; [|lia].
        split; [lia|].
        assert (E : (q - 1) * V2 = (n0 * BW + n1 - (rem + d0)) * BW + d1 * (q - 1)) by (subst V2; rewrite <- Hinv; ring).
        rewrite E. subst U3.
        assert (d1 * (q - 1) < BW * BW) by (apply mul_bound; lia).
        assert (BW * BW <= (rem + d0) * BW) by (apply Z.mul_le_mono_nonneg_r; lia). lia.
Qed.

(* [comment removed for export] *)
Theorem div_qhat_spec : forall u v S,
  1 <= S -> U3 * S <= u < (U3 + 1) * S -> V2 * S <= v < (V2 + 1) * S -> u < v * BW ->
  let q := div_qhat n0 n1 n2 d0 d1 in
  0 <= q < BW /\ u / v <= q <= u / v + 1.
Proof.
  intros u v S HS Hu Hv Huv. pose proof BW_pos as BWp. cbv zeta.
  assert (Hd0BW : 2 ^ 63 * BW <= d0 * BW) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (HV2 : BW <= V2) by (subst V2; rewrite BW_2_63 in *; lia).
  assert (HV2S : 0 < V2 * S) by (apply Z.mul_pos_pos; lia).
  assert (Hvpos : 0 < v) by lia.
  assert (HU3 : 0 <= U3).
  { subst U3. assert (0 <= n0 * BW) by (apply Z.mul_nonneg_nonneg; lia).
    assert (0 <= (n0 * BW + n1) * BW) by (apply Z.mul_nonneg_nonneg; lia). lia. }
  assert (Hu0 : 0 <= u) by (assert (0 <= U3 * S) by (apply Z.mul_nonneg_nonneg; lia); lia).
  set (qt := u / v).
  assert (Hqt0 : 0 <= qt) by (subst qt; apply Z.div_pos; lia).
  assert (HqtB : qt < BW) by (subst qt; apply Z.div_lt_upper_bound; lia).
  assert (Hqtv : qt * v <= u) by (subst qt; rewrite Z.mul_comm; apply Z.mul_div_le; lia).
  (* [comment removed for export] *)
  assert (HqtV : qt * V2 <= U3).
  { assert (qt * (V2 * S) <= qt * v) by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (Hx : qt * V2 * S < (U3 + 1) * S) by lia.
    apply Z.mul_lt_mono_pos_r in Hx; lia. }
  (* [comment removed for export] *)
  assert (Hup : forall q, 0 <= q < BW -> q * V2 <= U3 -> q <= qt + 1).
  { intros q Hq HqV. destruct (Z.eq_dec q 0) as [->|Hq0]; [lia|].
    assert (Hx : (q - 1) * v <= u).
    { assert ((q - 1) * v <= (q - 1) * ((V2 + 1) * S)) by (apply Z.mul_le_mono_nonneg_l; lia).
      assert ((q - 1) * ((V2 + 1) * S) <= q * V2 * S).
      { replace ((q - 1) * ((V2 + 1) * S)) with (q * V2 * S + (q - V2 - 1) * S) by ring.
        assert ((q - V2 - 1) * S <= 0) by (apply Z.mul_nonpos_nonneg; lia). lia. }
      assert (q * V2 * S <= U3 * S) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
    assert (q - 1 <= qt); [|lia]. subst qt. apply Z.div_le_lower_bound; lia. }
  (* [comment removed for export] *)
  assert (Hn1BW : 0 <= n1 * BW) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hu' : n0 * BW * BW * S <= u).
  { assert (n0 * BW * BW * S <= U3 * S); [|lia]. apply Z.mul_le_mono_nonneg_r; [lia|]. subst U3. lia. }
  assert (Hv' : v <= (d0 + 1) * BW * S).
  { assert ((V2 + 1) * S <= (d0 + 1) * BW * S); [|lia]. apply Z.mul_le_mono_nonneg_r; [lia|]. subst V2. lia. }
  assert (HBWS : 0 < BW * BW * S) by (apply Z.mul_pos_pos; [apply Z.mul_pos_pos|]; lia).
  (* [comment removed for export] *)
  assert (Hn0d0 : n0 <= d0).
  { assert (Hx : n0 * (BW * BW * S) < (d0 + 1) * (BW * BW * S)).
    { assert (v * BW <= (d0 + 1) * BW * S * BW) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
    apply Z.mul_lt_mono_pos_r in Hx; lia. }
  unfold div_qhat. destruct (Z.eqb_spec n0 d0) as [E|E].
  - (* [comment removed for export] *)
    split; [lia|]. split; [lia|].
    assert (Hx : (BW - 2) * v <= u).
    { assert ((BW - 2) * v <= (BW - 2) * ((d0 + 1) * BW * S)) by (apply Z.mul_le_mono_nonneg_l; lia).
      assert ((BW - 2) * ((d0 + 1) * BW * S) <= d0 * BW * BW * S); [|rewrite E in *; lia].
      replace ((BW - 2) * ((d0 + 1) * BW * S)) with (d0 * BW * BW * S + (BW - 2 * d0 - 2) * (BW * S)) by ring.
      assert ((BW - 2 * d0 - 2) * (BW * S) <= 0); [|lia].
      apply Z.mul_nonpos_nonneg; [rewrite BW_2_63 in *; lia|]. apply Z.mul_nonneg_nonneg; lia. }
    assert (BW - 2 <= qt); [|lia]. subst qt. apply Z.div_le_lower_bound; lia.
  - assert (Hlt : n0 < d0) by lia.
    rewrite (div_words_correct n0 n1 d0 Hd0 ltac:(lia) Hn1).
    set (q0 := (n0 * BW + n1) / d0).
    assert (Hd0pos : 0 < d0) by lia.
    assert (Hn0BW : 0 <= n0 * BW) by (apply Z.mul_nonneg_nonneg; lia).
    pose proof (Z.div_mod (n0 * BW + n1) d0 ltac:(lia)) as Edm. fold q0 in Edm.
    pose proof (Z.mod_pos_bound (n0 * BW + n1) d0 Hd0pos) as Hrm.
    set (r0 := (n0 * BW + n1) mod d0) in *.
    assert (Hq0 : 0 <= q0 < BW).
    { subst q0. split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
      assert ((n0 + 1) * BW <= d0 * BW) by (apply Z.mul_le_mono_nonneg_r; lia). lia. }
    assert (Erem : subw n1 (mulw q0 d0) = r0).
    { unfold subw, mulw. rewrite Zminus_mod_idemp_r.
      replace (n1 - q0 * d0) with (r0 + (- n0) * BW) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    rewrite Erem.
    (* [comment removed for export] *)
    assert (Hqtq0 : qt <= q0).
    { subst q0. apply Z.div_le_lower_bound; [lia|].
      assert (Hx : d0 * qt * (BW * S) < (n0 * BW + n1 + 1) * (BW * S)).
      { assert (E1 : qt * V2 * S = d0 * qt * (BW * S) + qt * d1 * S) by (subst V2; ring).
        assert (0 <= qt * d1 * S) by (apply Z.mul_nonneg_nonneg; [apply Z.mul_nonneg_nonneg|]; lia).
        assert (qt * V2 * S <= U3 * S) by (apply Z.mul_le_mono_nonneg_r; lia).
        assert (E2 : (n0 * BW + n1 + 1) * (BW * S) = U3 * S + (BW - n2) * S) by (subst U3; ring).
        assert (0 < (BW - n2) * S) by (apply Z.mul_pos_pos; lia). lia. }
      apply Z.mul_lt_mono_pos_r in Hx; [lia|]. apply Z.mul_pos_pos; lia. }
    pose proof (qhat_corr_spec QHAT_FUEL q0 r0 qt Hq0 ltac:(lia) ltac:(lia) ltac:(lia) HqtV
                  ltac:(unfold QHAT_FUEL; change (Z.of_nat 4) with 4; rewrite BW_2_63 in *; lia)) as Hc.
    cbv zeta in Hc. destruct Hc as [Hc1 Hc2].
    set (q' := qhat_corr QHAT_FUEL q0 r0 ((d1 * q0) mod BW) (d1 * q0 / BW) n2 d0 d1) in *.
    split; [lia|]. split; [lia|]. apply Hup; [lia|exact Hc2].
Qed.

End Qhat.
