(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.openssl.bndiv.lib.Spec Require Import BnBase BnWords BnKara BnModel BnTree BnWordsCorrect BnInv BnSpecs
  BnSpecs2 BnDivSpec BnMulSpec BnAddSpec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Correct.
Context {ptr : Type}.
Local Notation LS := (lstate ptr) (only parsing).
Local Notation BN := (bignum ptr) (only parsing).
Local Notation ops := (tree_ops ptr) (only parsing).

(* [comment removed for export] *)
Definition ls_inv (ls : LS) (X : blocks) : Prop := st_ok ls /\ own ls X /\ ctx_rest (ls_ctx ls).

Lemma ls_inv_init : ls_inv (ls_init : LS) [].
Proof.
  unfold ls_inv. split; [|split].
  - unfold st_ok, ls_init. cbn [ls_b1 ls_b2 ls_b3 ls_b4 ls_b5 ls_ctx ctx_nil cx_vals].
    repeat split; try (apply bn_ok_nil; right; reflexivity). left. reflexivity.
  - unfold own, blocks_of. cbn. apply Permutation_refl.
  - unfold ctx_rest, ctx_wf, ls_init, ctx_nil. cbn. repeat split; try lia; try (left; repeat split; reflexivity).
Qed.

(* [comment removed for export] *)
Definition sgn (b : bool) : Z := if b then -1 else 1.

Lemma bn_val_sgn : forall b : BN, bn_val b = sgn (bn_neg b) * bn_mag b.
Proof. intros b. unfold bn_val, sgn. destruct (bn_neg b); lia. Qed.

Lemma ctx_rest_same : forall c c' : bn_ctx ptr, ctx_same c c' -> ctx_rest c -> ctx_rest c'.
Proof.
  intros c c' Hsame [W F]. split; [eapply ctx_wf_same; eassumption|].
  destruct Hsame as (_ & _ & _ & _ & _ & E & _). rewrite E. exact F.
Qed.

Lemma firstn_MAX_LEN_length : forall (d : list Z), Z.of_nat (length (firstn MAX_LEN d)) <= MAX_BYTES.
Proof.
  intros d. rewrite length_firstn. unfold MAX_LEN, MAX_BYTES.
  assert (H : Z.of_nat (Init.Nat.min (Z.to_nat 256000) (length d)) <= Z.of_nat (Z.to_nat 256000)) by (apply Nat2Z.inj_le; apply Nat.le_min_l).
  rewrite Z2Nat.id in H by lia. exact H.
Qed.

(* [comment removed for export] *)
Lemma div_identity : forall (n1 n2 nq nr n5 : bool) (m1 m2 mq mr : Z) (zq zr z5 : bool),
  0 <= m1 -> 0 < m2 -> mq = m1 / m2 -> mr = m1 mod m2 ->
  nq = xorb n1 n2 && negb zq -> (zq = true -> mq = 0) ->
  nr = n1 && negb zr -> (zr = true -> mr = 0) ->
  n5 = xorb nq n2 && negb z5 -> (z5 = true -> mq * m2 = 0) -> (zq = true -> z5 = true) ->
  (sgn n5 * (mq * m2) + sgn nr * mr) = sgn n1 * m1.
Proof.
  intros n1 n2 nq nr n5 m1 m2 mq mr zq zr z5 Hm1 Hm2 Eq Er Enq Hzq Enr Hzr En5 Hz5 Hzq5.
  pose proof (Z.div_mod m1 m2 ltac:(lia)) as Edm. rewrite <- Eq, <- Er in Edm.
  assert (Hq0 : 0 <= mq) by (subst mq; apply Z.div_pos; lia).
  subst nq nr n5. unfold sgn.
  destruct n1, n2, zq, zr, z5; cbn [xorb andb negb];
    try (specialize (Hzq eq_refl)); try (specialize (Hzr eq_refl)); try (specialize (Hz5 eq_refl));
    try (specialize (Hzq5 eq_refl)); try discriminate; try nia.
Qed.

Theorem fuzz_one_wp : forall (ls : LS) (d : list Z) X, ls_inv ls X ->
  wp (bn_one ls d) X (fun r X' => ls_inv (fst r) X' /\ snd r = 0).
Proof.
  intros ls d X (Hs & Ho & Hrest). unfold bn_one. apply wp_bind.
  change (bwp (fuzz_one ops d) ls X (fun a s' X' => wp (TRet (s', a)) X' (fun r X'' => ls_inv (fst r) X'' /\ snd r = 0))).
  cbn [wp fst snd]. unfold fuzz_one.
  pose proof (firstn_MAX_LEN_length d) as Hlen. set (data := firstn MAX_LEN d) in *.
  set (parts := match data with
                | [] => (false, false, [], [])
                | b0 :: rest => (negb (Z.land b0 64 =? 0), negb (Z.land b0 128 =? 0),
                                 firstn (Z.to_nat (Z.land b0 63 * Z.of_nat (length rest) / 63)) rest,
                                 skipn (Z.to_nat (Z.land b0 63 * Z.of_nat (length rest) / 63)) rest)
                end).
  assert (Hparts : Z.of_nat (length (snd (fst parts))) <= MAX_BYTES /\ Z.of_nat (length (snd parts)) <= MAX_BYTES).
  { subst parts. destruct data as [|b0 rest]; cbn [fst snd length]; [unfold MAX_BYTES; lia|].
    cbn [length] in Hlen. rewrite length_firstn, length_skipn. lia. }
  destruct parts as [[[s1 s2] n1] n2]. cbn [fst snd] in Hparts. destruct Hparts as [Hn1 Hn2].
  (* [comment removed for export] *)
  apply bwp_bind. apply BN_bin2bn_spec; try assumption; try exact I.
  intros b1a Xa Hb1a Hnorm1a Htop1a _ Hsa Hoa.
  apply bwp_bind. apply BN_set_negative_spec; try assumption; try exact I.
  cbv zeta. change (getbn RB1 (setbn RB1 b1a ls)) with b1a. rewrite setbn_setbn_same. intros Hsb Hob.
  set (b1 := bn_with_neg b1a (s1 && negb (bn_top b1a =? 0)%nat)) in *.
  (* [comment removed for export] *)
  apply bwp_bind. apply BN_bin2bn_spec; try assumption; try exact I.
  intros b2a Xc Hb2a Hnorm2a Htop2a _ Hsc Hoc.
  apply bwp_bind. apply BN_set_negative_spec; try assumption; try exact I.
  cbv zeta. change (getbn RB2 (setbn RB2 b2a (setbn RB1 b1 ls))) with b2a. rewrite setbn_setbn_same. intros Hsd Hod.
  set (b2 := bn_with_neg b2a (s2 && negb (bn_top b2a =? 0)%nat)) in *.
  set (sd := setbn RB2 b2 (setbn RB1 b1 ls)) in *.
  assert (Hrestd : ctx_rest (ls_ctx sd)) by exact Hrest.
  assert (Htop1 : Z.of_nat (bn_top b1) <= 32000) by exact Htop1a.
  assert (Htop2 : Z.of_nat (bn_top b2) <= 32000) by exact Htop2a.
  assert (Hcan1 : bn_canon b1).
  { split; [exact Hnorm1a|]. subst b1. cbn [bn_with_neg bn_top bn_neg]. intros E. rewrite E. cbn. apply andb_false_r. }
  assert (Hcan2 : bn_canon b2).
  { split; [exact Hnorm2a|]. subst b2. cbn [bn_with_neg bn_top bn_neg]. intros E. rewrite E. cbn. apply andb_false_r. }
  assert (Hb1 : bn_ok b1) by (apply (st_ok_getbn RB1 sd Hsd I)).
  assert (Hb2 : bn_ok b2) by (apply (st_ok_getbn RB2 sd Hsd I)).
  apply bwp_bind, bwp_get. change (getbn RB2 sd) with b2.
  apply bwp_bind.
  destruct (Nat.eqb_spec (bn_top b2) 0) as [Ez|Enz].
  - (* [comment removed for export] *)
    apply bwp_ret. apply bwp_ret. cbn [fst snd]. split; [|reflexivity]. split; [exact Hsd|]. split; [exact Hod|exact Hrestd].
  - apply bwp_bind. apply BN_div_spec; try assumption; try (change (getbn RB2 sd) with b2; first [exact (proj1 Hcan2)|lia]);
      try (change (getbn RB1 sd) with b1; exact Htop1a); try (change (getbn RB2 sd) with b2; exact Htop2a).
    intros se Xe Hse Hoe Hreste E1 E2 E5. cbv zeta. change (getbn RB1 sd) with b1. change (getbn RB2 sd) with b2.
    intros Hcq Hcr Mq Mr Nq Nr Tq Tr.
    apply bwp_bind, bwp_get. apply bwp_bind, bwp_get. apply bwp_bind, bwp_get. apply bwp_bind, bwp_get.
    rewrite E1, E2. set (q := getbn RB3 se) in *. set (r := getbn RB4 se) in *.
    pose proof (st_ok_getbn RB3 se Hse I) as Hq. fold q in Hq. pose proof (st_ok_getbn RB4 se Hse I) as Hr. fold r in Hr.
    (* [comment removed for export] *)
    apply bwp_bind. apply BN_mul_spec; try assumption.
    { change (getbn RB3 se) with q. rewrite E2. change (getbn RB2 sd) with b2. lia. }
    intros sf Xf Hsf Hof Hrestf (F1 & F2 & F3 & F4). cbv zeta. change (getbn RB3 se) with q. rewrite E2. change (getbn RB2 sd) with b2.
    intros Hc5 M5 N5 T5. set (p := getbn RB5 sf) in *.
    pose proof (st_ok_getbn RB5 sf Hsf I) as Hp. fold p in Hp.
    (* [comment removed for export] *)
    apply bwp_bind. apply (BN_add_spec RB5 RB4); try assumption; try exact I; try congruence.
    { rewrite F4. exact Hcr. }
    { fold p. unfold DMAX_MAX. lia. }
    { rewrite F4. fold r. unfold DMAX_MAX. lia. }
    intros t Xg Ht Hct Vt Hsg Hog. fold p in Vt. rewrite F4 in Vt. fold r in Vt.
    apply bwp_bind, bwp_get. apply bwp_bind, bwp_get.
    change (getbn RB5 (setbn RB5 t sf)) with t. change (getbn RB1 (setbn RB5 t sf)) with (getbn RB1 sf). rewrite F1, E1.
    change (getbn RB1 sd) with b1.
    (* [comment removed for export] *)
    pose proof (bn_mag_nonneg b1 Hb1) as M1nn.
    assert (M2pos : 0 < bn_mag b2).
    { pose proof (bn_mag_ge b2 Hb2 (proj1 Hcan2) ltac:(lia)). pose proof (Bp_pos (bn_top b2 - 1)). lia. }
    pose proof (bn_norm_zero_iff q Hq (proj1 Hcq)) as Zq. pose proof (bn_norm_zero_iff r Hr (proj1 Hcr)) as Zr.
    pose proof (bn_norm_zero_iff p Hp (proj1 Hc5)) as Zp. pose proof (bn_norm_zero_iff b1 Hb1 (proj1 Hcan1)) as Z1.
    assert (Hval : bn_val t = bn_val b1).
    { rewrite Vt, !bn_val_sgn, M5.
      apply (div_identity (bn_neg b1) (bn_neg b2) (bn_neg q) (bn_neg r) (bn_neg p) (bn_mag b1) (bn_mag b2) (bn_mag q) (bn_mag r)
               (bn_top q =? 0)%nat (bn_top r =? 0)%nat (bn_top p =? 0)%nat); try assumption.
      - intros E. apply Nat.eqb_eq in E. apply Zq. exact E.
      - intros E. apply Nat.eqb_eq in E. apply Zr. exact E.
      - intros E. apply Nat.eqb_eq in E. apply Zp in E. rewrite <- M5. exact E.
      - intros E. apply Nat.eqb_eq in E. apply Zq in E. apply Nat.eqb_eq. apply Zp. rewrite M5, E. ring. }
    rewrite (cmp_pure_eq t b1 Ht Hb1 Hct Hcan1 Hval). cbn [Z.eqb]. rewrite andb_true_r.
    (* [comment removed for export] *)
    assert (Hsucc : (if (bn_top b1 =? 0)%nat then (bn_top q =? 0)%nat && (bn_top r =? 0)%nat
                     else if bn_neg b1
                          then (negb (Bool.eqb (bn_neg q) (bn_neg b2)) || (bn_top q =? 0)%nat) && (bn_neg r || (bn_top r =? 0)%nat)
                          else (Bool.eqb (bn_neg q) (bn_neg b2) || (bn_top q =? 0)%nat) && (negb (bn_neg r) || (bn_top r =? 0)%nat)) = true).
    { destruct (Nat.eqb_spec (bn_top b1) 0) as [E0|N0].
      - apply Z1 in E0. assert (Eq0 : bn_mag q = 0) by (rewrite Mq, E0; apply Z.div_0_l; lia).
        assert (Er0 : bn_mag r = 0) by (rewrite Mr, E0; apply Z.mod_0_l; lia).
        apply Zq in Eq0. apply Zr in Er0. rewrite Eq0, Er0. reflexivity.
      - rewrite Nq, Nr. destruct (bn_neg b1), (bn_neg b2), (bn_top q =? 0)%nat, (bn_top r =? 0)%nat; reflexivity. }
    rewrite Hsucc. apply bwp_ret. apply bwp_ret. cbn [fst snd]. split; [|reflexivity].
    split; [exact Hsg|]. split; [exact Hog|]. exact Hrestf.
Qed.

Lemma leaves_bbind : forall {A B} (m : BM (M:=btree ptr) (ptr:=ptr) A) (f : A -> BM B) (s : LS) (phi : B * LS -> Prop),
  (forall a s', leaves (f a s') phi) -> leaves (bbind ops m f s) phi.
Proof. intros A B m f s phi H. unfold bbind. cbn [bind tree_ops]. apply leaves_bind. intros [a s']. apply H. Qed.

Theorem fuzz_one_rc : forall (ls : LS) (d : list Z), leaves (bn_one ls d) (fun r => snd r = 0).
Proof.
  intros ls d. unfold bn_one. apply leaves_bind'.
  (* [comment removed for export] *)
  unfold fuzz_one.
  destruct (match firstn MAX_LEN d with
            | [] => (false, false, [], [])
            | b0 :: rest => _
            end) as [[[s1 s2] n1] n2].
  do 5 (apply leaves_bbind; intros). apply leaves_bbind. intros. cbn. reflexivity.
Qed.

End Correct.
