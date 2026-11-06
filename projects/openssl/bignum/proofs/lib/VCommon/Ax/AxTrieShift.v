(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From Stdlib Require Import Uint63.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import ExTrie.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Unset Nia Cache.
Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Section Shift.
Context {A : Type}.
Variable D : nat.
Variable ke : Z.

Fixpoint ishift_aux (dd : nat) (t : itrie A) (acc wgt : Z) (out : itrie A) : itrie A :=
  match t, dd with
  | IEmpty, _ => out
  | ILeaf v, O => if ke <=? acc then iset D out (of_Z (acc - ke)) v else out
  | ILeaf _, S _ => out
  | INode _ _, O => out
  | INode l r, S dd' => ishift_aux dd' r (acc + wgt) (2 * wgt) (ishift_aux dd' l acc (2 * wgt) out)
  end.

Definition ishift (t : itrie A) : itrie A := ishift_aux D t 0 1 IEmpty.

Definition zget (dd : nat) (t : itrie A) (q : Z) : option A :=
  if (0 <=? q) && (q <? 2 ^ Z.of_nat dd) then iget dd t (of_Z q) else None.

Lemma zget_node (dd : nat) (l r : itrie A) (q : Z) : (dd < 62)%nat ->
  zget (S dd) (INode l r) q = if Z.even q then zget dd l (q / 2) else zget dd r (q / 2).
Proof.
  intros Hdd. unfold zget. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
  assert (H62 : 2 ^ Z.of_nat dd <= 2 ^ 61) by (apply Z.pow_le_mono_r; lia).
  destruct (0 <=? q) eqn:E0; cbn [andb].
  - apply Z.leb_le in E0. destruct (q <? 2 * 2 ^ Z.of_nat dd) eqn:E1.
    + apply Z.ltb_lt in E1. pose proof (Z.div_mod q 2 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound q 2 ltac:(lia)) as Bq.
      assert (Hq2 : 0 <= q / 2 < 2 ^ Z.of_nat dd) by lia.
      replace (0 <=? q / 2) with true by (symmetry; apply Z.leb_le; lia).
      replace (q / 2 <? 2 ^ Z.of_nat dd) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb iget].
      assert (Eq : to_Z (of_Z q) = q) by (rewrite of_Z_spec; apply Z.mod_small; change wB with (2 ^ 63); lia).
      assert (Eh : (of_Z q >> 1)%uint63 = of_Z (q / 2)).
      { apply to_Z_inj. rewrite phi_half, Eq, of_Z_spec. symmetry. apply Z.mod_small. change wB with (2 ^ 63). lia. }
      rewrite iodd_spec, Eq, Eh.
      destruct (Z.even q) eqn:Ev.
      * apply Z.even_spec in Ev. destruct Ev as [h Eh2]. replace (q mod 2) with 0 by (subst q; rewrite Z.mul_comm, Z_mod_mult; reflexivity). reflexivity.
      * assert (Ho : Z.odd q = true) by (rewrite <- Z.negb_even, Ev; reflexivity). apply Z.odd_spec in Ho. destruct Ho as [h Eh2].
        replace (q mod 2) with 1 by (subst q; rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full; reflexivity). reflexivity.
    + apply Z.ltb_ge in E1. pose proof (Z.div_mod q 2 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound q 2 ltac:(lia)) as Bq.
      replace (q / 2 <? 2 ^ Z.of_nat dd) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. destruct (Z.even q); reflexivity.
  - apply Z.leb_gt in E0. pose proof (Z.div_mod q 2 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound q 2 ltac:(lia)) as Bq.
    replace (0 <=? q / 2) with false by (symmetry; apply Z.leb_gt; lia). destruct (Z.even q); reflexivity.
Qed.

Lemma ishift_aux_spec : forall (dd : nat) (t : itrie A) (acc wgt : Z) (out : itrie A) (j : Z),
  (dd <= D)%nat -> (D < 62)%nat -> 0 <= ke -> 0 <= acc < wgt -> wgt * 2 ^ Z.of_nat dd = 2 ^ Z.of_nat D -> 0 <= j < 2 ^ Z.of_nat D ->
  iget D (ishift_aux dd t acc wgt out) (of_Z j) =
  match (if ((j + ke - acc) mod wgt =? 0) then zget dd t ((j + ke - acc) / wgt) else None) with
  | Some v => Some v
  | None => iget D out (of_Z j)
  end.
Proof.
  induction dd as [|dd IH]; intros t acc wgt out j HdD HD Hke Hacc Hw Hj.
  -
    cbn [Z.of_nat] in Hw. rewrite Z.pow_0_r, Z.mul_1_r in Hw. subst wgt.
    assert (H62 : 2 ^ Z.of_nat D <= 2 ^ 61) by (apply Z.pow_le_mono_r; lia).
    assert (Ej : to_Z (of_Z j) = j) by (rewrite of_Z_spec; apply Z.mod_small; change wB with (2 ^ 63); lia).
    unfold zget. cbn [Z.of_nat]. rewrite Z.pow_0_r.
    destruct t as [|v|l r]; cbn [ishift_aux iget].
    + destruct ((j + ke - acc) mod 2 ^ Z.of_nat D =? 0); [destruct ((0 <=? _) && (_ <? 1))|]; reflexivity.
    + destruct (ke <=? acc) eqn:Ek.
      * apply Z.leb_le in Ek. rewrite iget_iset, Ej.
        assert (Ea : to_Z (of_Z (acc - ke)) = acc - ke) by (rewrite of_Z_spec; apply Z.mod_small; change wB with (2 ^ 63); lia).
        rewrite Ea, (Z.mod_small (acc - ke)) by lia. rewrite (Z.mod_small j) by lia.
        destruct (Z.eqb_spec (acc - ke) j) as [E|E].
        -- replace (j + ke - acc) with 0 by lia. rewrite Z.mod_0_l by lia. cbn. reflexivity.
        -- destruct (Z.eqb_spec ((j + ke - acc) mod 2 ^ Z.of_nat D) 0) as [E2|E2]; [|reflexivity].
           pose proof (Z.div_mod (j + ke - acc) (2 ^ Z.of_nat D) ltac:(lia)) as Dm. rewrite E2, Z.add_0_r in Dm.
           destruct ((0 <=? (j + ke - acc) / 2 ^ Z.of_nat D) && ((j + ke - acc) / 2 ^ Z.of_nat D <? 1)) eqn:Eb; [|reflexivity].
           apply andb_prop in Eb as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2. exfalso. apply E. nia.
      * apply Z.leb_gt in Ek.
        destruct (Z.eqb_spec ((j + ke - acc) mod 2 ^ Z.of_nat D) 0) as [E2|E2]; [|reflexivity].
        pose proof (Z.div_mod (j + ke - acc) (2 ^ Z.of_nat D) ltac:(lia)) as Dm. rewrite E2, Z.add_0_r in Dm.
        destruct ((0 <=? (j + ke - acc) / 2 ^ Z.of_nat D) && ((j + ke - acc) / 2 ^ Z.of_nat D <? 1)) eqn:Eb; [|reflexivity].
        apply andb_prop in Eb as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2. exfalso. nia.
    + destruct ((j + ke - acc) mod 2 ^ Z.of_nat D =? 0); [destruct ((0 <=? _) && (_ <? 1))|]; reflexivity.
  -
    assert (Hwp : 0 < wgt) by lia.
    assert (Hw2 : 2 * wgt * 2 ^ Z.of_nat dd = 2 ^ Z.of_nat D) by (rewrite <- Hw, Nat2Z.inj_succ, Z.pow_succ_r by lia; ring).
    destruct t as [|v|l r]; cbn [ishift_aux].
    + unfold zget. rewrite iget_empty. destruct (_ =? 0); [destruct (_ && _)|]; reflexivity.
    + unfold zget. cbn [iget]. destruct (_ =? 0); [destruct (_ && _)|]; reflexivity.
    + rewrite (IH r (acc + wgt) (2 * wgt) _ j ltac:(lia) HD Hke ltac:(lia) Hw2 Hj).
      rewrite (IH l acc (2 * wgt) out j ltac:(lia) HD Hke ltac:(lia) Hw2 Hj).
      rewrite (zget_node dd l r) by lia.
      set (s := j + ke - acc).
      replace (j + ke - (acc + wgt)) with (s - wgt) by (unfold s; lia).
      pose proof (Z.div_mod s wgt ltac:(lia)) as Ds. pose proof (Z.mod_pos_bound s wgt Hwp) as Bs.
      set (q := s / wgt) in *. set (rm := s mod wgt) in *.
      pose proof (Z.div_mod q 2 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound q 2 ltac:(lia)) as Bq.

      assert (M1 : s mod (2 * wgt) = wgt * (q mod 2) + rm).
      { symmetry. apply (Z.mod_unique s (2 * wgt) (q / 2)); [nia | nia]. }
      assert (D1 : s / (2 * wgt) = q / 2).
      { symmetry. apply (Z.div_unique s (2 * wgt) (q / 2) (wgt * (q mod 2) + rm)); [nia | nia]. }
      assert (M2 : (s - wgt) mod (2 * wgt) = wgt * ((q - 1) mod 2) + rm).
      { pose proof (Z.div_mod (q - 1) 2 ltac:(lia)) as Dq1. pose proof (Z.mod_pos_bound (q - 1) 2 ltac:(lia)) as Bq1.
        symmetry. apply (Z.mod_unique (s - wgt) (2 * wgt) ((q - 1) / 2)); [nia | nia]. }
      assert (D2 : (s - wgt) / (2 * wgt) = (q - 1) / 2).
      { pose proof (Z.div_mod (q - 1) 2 ltac:(lia)) as Dq1. pose proof (Z.mod_pos_bound (q - 1) 2 ltac:(lia)) as Bq1.
        symmetry. apply (Z.div_unique (s - wgt) (2 * wgt) ((q - 1) / 2) (wgt * ((q - 1) mod 2) + rm)); [nia | nia]. }
      rewrite M1, D1, M2, D2.
      destruct (Z.eqb_spec rm 0) as [Er|Er].
      *
        destruct (Z.even q) eqn:Ev.
        -- assert (Eq0 : q mod 2 = 0) by (apply Z.even_spec in Ev; destruct Ev as [h ->]; rewrite Z.mul_comm, Z_mod_mult; reflexivity).
           assert (Eq1 : (q - 1) mod 2 = 1) by (pose proof (Z.div_mod (q - 1) 2 ltac:(lia)); pose proof (Z.mod_pos_bound (q - 1) 2 ltac:(lia)); lia).
           rewrite Eq0, Eq1, Er. replace (wgt * 0 + 0 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
           replace (wgt * 1 + 0 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
           destruct (zget dd l (q / 2)); reflexivity.
        -- assert (Eq0 : q mod 2 = 1) by (assert (Ho : Z.odd q = true) by (rewrite <- Z.negb_even, Ev; reflexivity); apply Z.odd_spec in Ho; destruct Ho as [h ->]; rewrite Z.add_comm, Z.mul_comm, Z_mod_plus_full; reflexivity).
           assert (Eq1 : (q - 1) mod 2 = 0) by (pose proof (Z.div_mod (q - 1) 2 ltac:(lia)); pose proof (Z.mod_pos_bound (q - 1) 2 ltac:(lia)); lia).
           assert (Eh : (q - 1) / 2 = q / 2) by (pose proof (Z.div_mod (q - 1) 2 ltac:(lia)); lia).
           rewrite Eq0, Eq1, Er, Eh. replace (wgt * 0 + 0 =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
           replace (wgt * 1 + 0 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
           destruct (zget dd r (q / 2)); reflexivity.
      * replace (wgt * (q mod 2) + rm =? 0) with false by (symmetry; apply Z.eqb_neq; nia).
        replace (wgt * ((q - 1) mod 2) + rm =? 0) with false
          by (symmetry; apply Z.eqb_neq; pose proof (Z.mod_pos_bound (q - 1) 2 ltac:(lia)); nia).
        reflexivity.
Qed.

Theorem iget_ishift (t : itrie A) (j : Z) : (D < 62)%nat -> 0 <= ke -> 0 <= j < 2 ^ Z.of_nat D ->
  iget D (ishift t) (of_Z j) = zget D t (j + ke).
Proof.
  intros HD Hke Hj. unfold ishift.
  rewrite (ishift_aux_spec D t 0 1 IEmpty j (Nat.le_refl D) HD Hke ltac:(lia) ltac:(lia) Hj).
  rewrite Z.mod_1_r, Z.sub_0_r, Z.div_1_r. cbn. rewrite iget_empty. destruct (zget D t (j + ke)); reflexivity.
Qed.

End Shift.
