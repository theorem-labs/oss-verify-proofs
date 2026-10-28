(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Arith Bool.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCSortM. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzR2Theory.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lexlt_first_diff : forall u v, length u = length v ->
  (lexlt u v <-> exists d, (d < length u)%nat /\ (forall j, (j < d)%nat -> nth j u 0 = nth j v 0) /\ nth d u 0 < nth d v 0).
Proof.
  induction u as [|a u IH]; intros [|b v] Hl; cbn in *; try lia.
  - split; [tauto|cps_intros (d & Hd & _); lia].
  - split.
    + intros [H|[-> H]].
      * exists 0%nat. split; [lia|]. split; [intros; lia|exact H].
      * cps_destruct (proj1 (IH v ltac:(lia)) H) as (d & Hd & Hp & Hlt).
        exists (S d). split; [lia|]. split; [|exact Hlt].
        intros [|j] Hj; [reflexivity|]. apply Hp. lia.
    + cps_intros (d & Hd & Hp & Hlt). destruct d as [|d].
      * left. exact Hlt.
      * right. split; [exact (Hp 0%nat ltac:(lia))|].
        apply (proj2 (IH v ltac:(lia))). exists d. split; [lia|]. split; [|exact Hlt].
        intros j Hj. exact (Hp (S j) ltac:(lia)).
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma nth_rot : forall (t : list Z) p j, (p < length t)%nat -> (j < length t)%nat ->
  nth j (rot t p) 0 = nth ((p + j) mod length t) t 0.
Proof.
  intros t p j Hp Hj. unfold rot.
  destruct (Nat.lt_ge_cases j (length t - p)) as [A|A].
  - rewrite app_nth1 by (rewrite length_skipn; lia). rewrite nth_skipn. rewrite Nat.mod_small by lia. reflexivity.
  - rewrite app_nth2 by (rewrite length_skipn; lia). rewrite length_skipn, nth_firstn.
    destruct (Nat.ltb_spec (j - (length t - p)) p); [|lia].
    f_equal. replace (p + j)%nat with ((j - (length t - p)) + 1 * length t)%nat by lia.
    rewrite Nat.Div0.mod_add. symmetry. apply Nat.mod_small. lia.
Qed.

(* [comment removed for export] *)
Lemma lexle_first_diff : forall u v, length u = length v ->
  (lexle u v <-> (forall j, (j < length u)%nat -> nth j u 0 = nth j v 0) \/
                 exists d, (d < length u)%nat /\ (forall j, (j < d)%nat -> nth j u 0 = nth j v 0) /\ nth d u 0 < nth d v 0).
Proof.
  intros u v Hl. unfold lexle. rewrite (lexlt_first_diff u v Hl). split.
  - intros [H| ->]; [right; exact H|left; intros; reflexivity].
  - intros [H|H]; [right|left; exact H]. apply (nth_ext _ _ 0 0 Hl). intros j Hj. apply H. exact Hj.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section GtU.
  Variables (a2 : zarr) (qoff n : Z).
  Hypothesis Hn : 34 <= n.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis OVB : forall i, 0 <= i < 34 -> rd8 a2 (n + i) = rd8 a2 i.
  Hypothesis OVQ : forall i, 0 <= i < 34 -> qrd a2 qoff (n + i) = qrd a2 qoff i.

  Definition N : nat := Z.to_nat n.
  Definition blk : list Z := map (fun k => rd8 a2 (Z.of_nat k)) (seq 0 N).
  Lemma blk_length : length blk = N. Proof. unfold blk. rewrite length_map, length_seq. reflexivity. Qed.
  Lemma blk_nth : forall i, 0 <= i < n -> nth (Z.to_nat i) blk 0 = rd8 a2 i.
  Proof.
    intros i Hi. unfold blk. rewrite nth_map_seq by (unfold N; lia). f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Definition bt (i : Z) : Z := rd8 a2 (i mod n).
  Definition qt (i : Z) : Z := qrd a2 qoff (i mod n).
  Lemma mod_shift_n : forall i, n <= i < n + n -> i mod n = i - n.
  Proof.
    intros i Hi. rewrite <- (Z.mod_small (i - n) n) by lia.
    replace i with ((i - n) + 1 * n) at 1 by lia. rewrite Z.mod_add by lia. reflexivity.
  Qed.
  Lemma rd8_cyc : forall i, 0 <= i < n + 34 -> rd8 a2 i = bt i.
  Proof.
    intros i Hi. unfold bt. destruct (Z.lt_ge_cases i n).
    - rewrite Z.mod_small by lia. reflexivity.
    - replace i with (n + (i - n)) at 1 by lia. rewrite OVB by lia. f_equal. rewrite mod_shift_n by lia. reflexivity.
  Qed.
  Lemma qrd_cyc : forall i, 0 <= i < n + 34 -> qrd a2 qoff i = qt i.
  Proof.
    intros i Hi. unfold qt. destruct (Z.lt_ge_cases i n).
    - rewrite Z.mod_small by lia. reflexivity.
    - replace i with (n + (i - n)) at 1 by lia. rewrite OVQ by lia. f_equal. rewrite mod_shift_n by lia. reflexivity.
  Qed.
  Lemma bt_mod : forall i, bt (i mod n) = bt i.
  Proof. intros. unfold bt. rewrite Z.mod_mod by lia. reflexivity. Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition rotz (p : Z) : list Z := rot blk (Z.to_nat (p mod n)).
  Lemma rotz_length : forall p, length (rotz p) = N.
  Proof.
    intros p. unfold rotz. pose proof (Z.mod_pos_bound p n ltac:(lia)).
    rewrite rot_length; rewrite blk_length; unfold N; [reflexivity|lia|lia].
  Qed.
  Lemma rotz_nth : forall p j, 0 <= j < n -> nth (Z.to_nat j) (rotz p) 0 = bt (p + j).
  Proof.
    intros p j Hj. unfold rotz. pose proof (Z.mod_pos_bound p n ltac:(lia)) as Hp.
    rewrite nth_rot by (rewrite blk_length; unfold N; lia). rewrite blk_length.
    unfold bt. rewrite <- (blk_nth ((p + j) mod n)) by (apply Z.mod_pos_bound; lia).
    f_equal. unfold N.
    rewrite <- (Z2Nat.inj_add) by lia. rewrite <- Z2Nat.inj_mod by lia. f_equal.
    rewrite Z.add_mod_idemp_l by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition EQB (i1 i2 k : Z) : Prop := forall j, 0 <= j < k -> bt (i1 + j) = bt (i2 + j).

  (* [comment removed for export] *)
  Definition SOUND (i1 i2 : Z) (b : bool) : Prop :=
    (b = true -> lexle (rotz i2) (rotz i1)) /\ (b = false -> lexle (rotz i1) (rotz i2)).

  Lemma rotz_eq_of_EQB : forall i1 i2, EQB i1 i2 n -> rotz i1 = rotz i2.
  Proof.
    intros i1 i2 H. apply (nth_ext _ _ 0 0); [rewrite !rotz_length; reflexivity|].
    intros j Hj. rewrite rotz_length in Hj.
    replace j with (Z.to_nat (Z.of_nat j)) by lia. rewrite !rotz_nth by (unfold N in Hj; lia). apply H. unfold N in Hj; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma sound_byte : forall i1 i2 k, 0 <= k -> EQB i1 i2 k -> bt (i1 + k) <> bt (i2 + k) ->
    SOUND i1 i2 (bt (i2 + k) <? bt (i1 + k)).
  Proof.
    intros i1 i2 k Hk HE HNE.
    destruct (Z.lt_ge_cases k n) as [Kn|Kn].
    2: { exfalso. apply HNE. rewrite <- (bt_mod (i1 + k)), <- (bt_mod (i2 + k)).
         rewrite <- (Z.add_mod_idemp_r i1 k n), <- (Z.add_mod_idemp_r i2 k n) by lia. rewrite !bt_mod.
         apply HE. pose proof (Z.mod_pos_bound k n ltac:(lia)). lia. }
    split; intros Hb.
    - apply Z.ltb_lt in Hb. left. apply (proj2 (lexlt_first_diff _ _ ltac:(rewrite !rotz_length; reflexivity))).
      exists (Z.to_nat k). rewrite rotz_length. split; [unfold N; lia|]. split.
      + intros j Hj. replace j with (Z.to_nat (Z.of_nat j)) by lia. rewrite !rotz_nth by lia. symmetry. apply HE. lia.
      + rewrite !rotz_nth by lia. exact Hb.
    - apply Z.ltb_ge in Hb. left. apply (proj2 (lexlt_first_diff _ _ ltac:(rewrite !rotz_length; reflexivity))).
      exists (Z.to_nat k). rewrite rotz_length. split; [unfold N; lia|]. split.
      + intros j Hj. replace j with (Z.to_nat (Z.of_nat j)) by lia. rewrite !rotz_nth by lia. apply HE. lia.
      + rewrite !rotz_nth by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Hypothesis QIw : forall p p', 0 <= p < n -> 0 <= p' < n -> rd8 a2 p = rd8 a2 p' ->
    qrd a2 qoff p < qrd a2 qoff p' -> lexle (rot blk (Z.to_nat p)) (rot blk (Z.to_nat p')).

  Lemma rotz_small : forall p, 0 <= p < n -> rotz p = rot blk (Z.to_nat p).
  Proof. intros p Hp. unfold rotz. rewrite Z.mod_small by lia. reflexivity. Qed.
  Lemma rotz_mod : forall p, rotz (p mod n) = rotz p.
  Proof. intros p. unfold rotz. rewrite Z.mod_mod by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma lexle_shift_back : forall i1 i2 k, 0 <= k -> EQB i1 i2 k ->
    lexle (rotz (i2 + k)) (rotz (i1 + k)) -> lexle (rotz i2) (rotz i1).
  Proof.
    intros i1 i2 k Hk HE HL.
    apply (proj1 (lexle_first_diff _ _ ltac:(rewrite !rotz_length; reflexivity))) in HL.
    apply (proj2 (lexle_first_diff _ _ ltac:(rewrite !rotz_length; reflexivity))).
    rewrite rotz_length in *.
    destruct HL as [ALL | (e & He & Hp & Hlt)].
    - (* [comment removed for export] *)
      left. intros j Hj. replace j with (Z.to_nat (Z.of_nat j)) by lia. rewrite !rotz_nth by (unfold N in Hj; lia).
      destruct (Z.lt_ge_cases (Z.of_nat j) k) as [A|A]; [symmetry; apply HE; lia|].
      specialize (ALL (Z.to_nat (Z.of_nat j - k)) ltac:(unfold N in *; lia)).
      rewrite !rotz_nth in ALL by (unfold N in *; lia).
      replace (i2 + Z.of_nat j) with (i2 + k + (Z.of_nat j - k)) by lia.
      replace (i1 + Z.of_nat j) with (i1 + k + (Z.of_nat j - k)) by lia. exact ALL.
    - destruct (Z.lt_ge_cases (k + Z.of_nat e) n) as [A|A].
      + right. exists (Z.to_nat (k + Z.of_nat e)). split; [unfold N in *; lia|]. split.
        * intros j Hj. replace j with (Z.to_nat (Z.of_nat j)) by lia. rewrite !rotz_nth by (unfold N in *; lia).
          destruct (Z.lt_ge_cases (Z.of_nat j) k) as [B|B]; [symmetry; apply HE; lia|].
          specialize (Hp (Z.to_nat (Z.of_nat j - k)) ltac:(lia)). rewrite !rotz_nth in Hp by (unfold N in *; lia).
          replace (i2 + Z.of_nat j) with (i2 + k + (Z.of_nat j - k)) by lia.
          replace (i1 + Z.of_nat j) with (i1 + k + (Z.of_nat j - k)) by lia. exact Hp.
        * rewrite !rotz_nth by (unfold N in *; lia).
          replace e with (Z.to_nat (Z.of_nat e)) in Hlt by lia. rewrite !rotz_nth in Hlt by (unfold N in *; lia).
          replace (i2 + (k + Z.of_nat e)) with (i2 + k + Z.of_nat e) by lia.
          replace (i1 + (k + Z.of_nat e)) with (i1 + k + Z.of_nat e) by lia. exact Hlt.
      + (* [comment removed for export] *)
        left. intros j Hj. replace j with (Z.to_nat (Z.of_nat j)) by lia. rewrite !rotz_nth by (unfold N in Hj; lia).
        destruct (Z.lt_ge_cases (Z.of_nat j) k) as [B|B]; [symmetry; apply HE; lia|].
        specialize (Hp (Z.to_nat (Z.of_nat j - k)) ltac:(unfold N in *; lia)). rewrite !rotz_nth in Hp by (unfold N in *; lia).
        replace (i2 + Z.of_nat j) with (i2 + k + (Z.of_nat j - k)) by lia.
        replace (i1 + Z.of_nat j) with (i1 + k + (Z.of_nat j - k)) by lia. exact Hp.
  Qed.

  (* [comment removed for export] *)
  Lemma sound_quad : forall i1 i2 k, 0 <= k -> EQB i1 i2 (k + 1) -> qt (i1 + k) <> qt (i2 + k) ->
    SOUND i1 i2 (qt (i2 + k) <? qt (i1 + k)).
  Proof.
    intros i1 i2 k Hk HE HNE.
    assert (HEk : EQB i1 i2 k) by (intros j Hj; apply HE; lia).
    assert (Hb : bt (i1 + k) = bt (i2 + k)) by (apply HE; lia).
    set (p1 := (i1 + k) mod n). set (p2 := (i2 + k) mod n).
    pose proof (Z.mod_pos_bound (i1 + k) n ltac:(lia)) as R1. pose proof (Z.mod_pos_bound (i2 + k) n ltac:(lia)) as R2.
    assert (Hb' : rd8 a2 p1 = rd8 a2 p2) by (unfold bt in Hb; exact Hb).
    split; intros Hr.
    - apply Z.ltb_lt in Hr. apply (lexle_shift_back i1 i2 k Hk HEk).
      rewrite <- (rotz_mod (i2 + k)), <- (rotz_mod (i1 + k)). rewrite !rotz_small by lia.
      apply (QIw p2 p1); [lia|lia|symmetry; exact Hb'|]. unfold qt in Hr. exact Hr.
    - apply Z.ltb_ge in Hr. assert (Hr' : qt (i1 + k) < qt (i2 + k)) by lia.
      apply (lexle_shift_back i2 i1 k Hk ltac:(intros j Hj; symmetry; apply HEk; lia)).
      rewrite <- (rotz_mod (i2 + k)), <- (rotz_mod (i1 + k)). rewrite !rotz_small by lia.
      apply (QIw p1 p2); [lia|lia|exact Hb'|]. unfold qt in Hr'. exact Hr'.
  Qed.

  (* [comment removed for export] *)
  Lemma gtu_pre_spec : forall m i1 i2 k j1 j2,
    0 <= j1 -> 0 <= j2 -> 0 <= k -> j1 = i1 + k -> j2 = i2 + k -> j1 + Z.of_nat m <= n + 34 -> j2 + Z.of_nat m <= n + 34 ->
    EQB i1 i2 k ->
    match gtu_pre m a2 j1 j2 with
    | (None, j1', j2') => j1' = j1 + Z.of_nat m /\ j2' = j2 + Z.of_nat m /\ EQB i1 i2 (k + Z.of_nat m)
    | (Some b, _, _) => SOUND i1 i2 b
    end.
  Proof.
    induction m as [|m IH]; intros i1 i2 k j1 j2 H1 H2 Hk -> -> B1 B2 HE.
    - cbn. repeat split; try lia. replace (k + 0) with k by lia. exact HE.
    - cbn [gtu_pre]. rewrite !rd8_cyc by lia.
      destruct (Z.eqb_spec (bt (i1 + k)) (bt (i2 + k))) as [E|NE]; cbn [negb].
      + specialize (IH i1 i2 (k + 1) (i1 + k + 1) (i2 + k + 1) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
        assert (HE' : EQB i1 i2 (k + 1)).
        { intros j Hj. destruct (Z.eq_dec j k) as [->|]; [exact E|apply HE; lia]. }
        specialize (IH HE').
        destruct (gtu_pre m a2 (i1 + k + 1) (i2 + k + 1)) as [[r j1'] j2']. destruct r.
        * exact IH.
        * cps_destruct IH as (-> & -> & IH). repeat split; try lia. replace (k + Z.of_nat (S m)) with (k + 1 + Z.of_nat m) by lia. exact IH.
      + apply sound_byte; [lia|exact HE|exact NE].
  Qed.

  (* [comment removed for export] *)
  Lemma gtu_oct_spec : forall m i1 i2 k j1 j2,
    0 <= j1 -> 0 <= j2 -> 0 <= k -> j1 = i1 + k -> j2 = i2 + k -> j1 + Z.of_nat m <= n + 34 -> j2 + Z.of_nat m <= n + 34 ->
    EQB i1 i2 k ->
    match gtu_oct m a2 qoff j1 j2 with
    | (None, j1', j2') => j1' = j1 + Z.of_nat m /\ j2' = j2 + Z.of_nat m /\ EQB i1 i2 (k + Z.of_nat m)
    | (Some b, _, _) => SOUND i1 i2 b
    end.
  Proof.
    induction m as [|m IH]; intros i1 i2 k j1 j2 H1 H2 Hk -> -> B1 B2 HE.
    - cbn. repeat split; try lia. replace (k + 0) with k by lia. exact HE.
    - cbn [gtu_oct]. rewrite !rd8_cyc by lia.
      destruct (Z.eqb_spec (bt (i1 + k)) (bt (i2 + k))) as [E|NE]; cbn [negb].
      + assert (HE' : EQB i1 i2 (k + 1)).
        { intros j Hj. destruct (Z.eq_dec j k) as [->|]; [exact E|apply HE; lia]. }
        rewrite !qrd_cyc by lia.
        destruct (Z.eqb_spec (qt (i1 + k)) (qt (i2 + k))) as [EQ|NQ]; cbn [negb].
        * specialize (IH i1 i2 (k + 1) (i1 + k + 1) (i2 + k + 1) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HE').
          destruct (gtu_oct m a2 qoff (i1 + k + 1) (i2 + k + 1)) as [[r j1'] j2']. destruct r.
          -- exact IH.
          -- cps_destruct IH as (-> & -> & IH). repeat split; try lia.
             replace (k + Z.of_nat (S m)) with (k + 1 + Z.of_nat m) by lia. exact IH.
        * apply sound_quad; try lia; assumption.
      + apply sound_byte; [lia|exact HE|exact NE].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma SOUND_of_EQBn : forall i1 i2 b, EQB i1 i2 n -> SOUND i1 i2 b.
  Proof.
    intros i1 i2 b H. pose proof (rotz_eq_of_EQB _ _ H) as E. unfold SOUND. rewrite E. split; intros; right; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition cong (a b : Z) : Prop := (a - b) mod n = 0.
  Lemma cong_refl : forall a, cong a a. Proof. intros; unfold cong. rewrite Z.sub_diag. reflexivity. Qed.
  Lemma cong_sym : forall a b, cong a b -> cong b a.
  Proof.
    intros a b H. unfold cong in *. replace (b - a) with (- (a - b)) by lia.
    apply Z.mod_opp_l_z; [lia|exact H].
  Qed.
  Lemma cong_trans : forall a b c, cong a b -> cong b c -> cong a c.
  Proof.
    intros a b c H1 H2. unfold cong in *. replace (a - c) with ((a - b) + (b - c)) by lia.
    rewrite Z.add_mod, H1, H2 by lia. reflexivity.
  Qed.
  Lemma cong_add : forall a b d, cong a b -> cong (a + d) (b + d).
  Proof. intros a b d H. unfold cong in *. replace (a + d - (b + d)) with (a - b) by lia. exact H. Qed.
  Lemma cong_subn : forall a, cong (a - n) a.
  Proof. intros a. unfold cong. replace (a - n - a) with (-1 * n) by lia. apply Z_mod_mult. Qed.
  Lemma cong_mod_eq : forall a b, cong a b -> a mod n = b mod n.
  Proof.
    intros a b H. unfold cong in H. replace a with ((a - b) + b) by lia.
    rewrite Z.add_mod, H, Z.add_0_l, Z.mod_mod by lia. reflexivity.
  Qed.
  Lemma EQB_rebase : forall i1 i1' i2 k, cong i1' i1 -> EQB i1 i2 k -> EQB i1' i2 k.
  Proof.
    intros i1 i1' i2 k Hm H j Hj. rewrite <- (H j Hj). unfold bt. f_equal. apply cong_mod_eq. apply cong_add. exact Hm.
  Qed.
  Lemma EQB_sym : forall i1 i2 k, EQB i1 i2 k -> EQB i2 i1 k.
  Proof. intros i1 i2 k H j Hj. symmetry. apply H. exact Hj. Qed.
  Lemma EQB_rebase2 : forall i1 i1' i2 i2' k, cong i1' i1 -> cong i2' i2 -> EQB i1 i2 k -> EQB i1' i2' k.
  Proof.
    intros i1 i1' i2 i2' k M1 M2 H. apply (EQB_rebase i1); [exact M1|]. apply EQB_sym.
    apply (EQB_rebase i2); [exact M2|]. apply EQB_sym. exact H.
  Qed.
  Lemma rotz_rebase : forall i1 i1', cong i1' i1 -> rotz i1' = rotz i1.
  Proof. intros i1 i1' Hm. unfold rotz. rewrite (cong_mod_eq _ _ Hm). reflexivity. Qed.
  Lemma SOUND_rebase : forall i1 i1' i2 i2' b, cong i1' i1 -> cong i2' i2 -> SOUND i1' i2' b -> SOUND i1 i2 b.
  Proof.
    intros i1 i1' i2 i2' b M1 M2. unfold SOUND. rewrite (rotz_rebase i1 i1'), (rotz_rebase i2 i2') by assumption. tauto.
  Qed.

  Lemma gtu_loop_spec : forall fuel i1 i2 k j1 j2 kk budget,
    0 <= k -> 0 <= j1 <= n + 26 -> 0 <= j2 <= n + 26 ->
    cong j1 (i1 + k) -> cong j2 (i2 + k) -> EQB i1 i2 k ->
    n + 8 <= k + kk -> 0 <= kk -> kk + 8 <= 8 * Z.of_nat fuel ->
    SOUND i1 i2 (fst (gtu_loop fuel a2 qoff n j1 j2 kk budget)).
  Proof.
    induction fuel as [|fuel IH]; intros i1 i2 k j1 j2 kk budget Hk B1 B2 M1 M2 HE Hkk Hkk0 Hf; [lia|].
    cbn [gtu_loop].
    assert (C1 : cong (j1 - k) i1).
    { revert M1; unfold cong. replace (j1 - k - i1) with (j1 - (i1 + k)) by lia. exact (fun x => x). }
    assert (C2 : cong (j2 - k) i2).
    { revert M2; unfold cong. replace (j2 - k - i2) with (j2 - (i2 + k)) by lia. exact (fun x => x). }
    assert (HE' : EQB (j1 - k) (j2 - k) k) by (apply (EQB_rebase2 i1 _ i2); assumption).
    pose proof (gtu_oct_spec 8 (j1 - k) (j2 - k) k j1 j2 ltac:(lia) ltac:(lia) Hk ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) HE') as OS.
    destruct (gtu_oct 8 a2 qoff j1 j2) as [[r j1'] j2']. destruct r as [b|].
    - cbn [fst]. exact (SOUND_rebase i1 (j1 - k) i2 (j2 - k) b C1 C2 OS).
    - cps_destruct OS as (-> & -> & HE8). change (Z.of_nat 8) with 8 in HE8 |- *.
      assert (HE8' : EQB i1 i2 (k + 8)) by (apply (EQB_rebase2 (j1 - k) _ (j2 - k)); auto using cong_sym).
      set (j1n := if n <=? j1 + 8 then j1 + 8 - n else j1 + 8).
      set (j2n := if n <=? j2 + 8 then j2 + 8 - n else j2 + 8).
      assert (N1 : 0 <= j1n <= n + 26 /\ cong j1n (i1 + (k + 8))).
      { subst j1n. destruct (Z.leb_spec n (j1 + 8)).
        - split; [lia|]. apply (cong_trans _ (j1 + 8)); [apply cong_subn|].
          replace (i1 + (k + 8)) with (i1 + k + 8) by lia. apply cong_add. exact M1.
        - split; [lia|]. replace (i1 + (k + 8)) with (i1 + k + 8) by lia. apply cong_add. exact M1. }
      assert (N2 : 0 <= j2n <= n + 26 /\ cong j2n (i2 + (k + 8))).
      { subst j2n. destruct (Z.leb_spec n (j2 + 8)).
        - split; [lia|]. apply (cong_trans _ (j2 + 8)); [apply cong_subn|].
          replace (i2 + (k + 8)) with (i2 + k + 8) by lia. apply cong_add. exact M2.
        - split; [lia|]. replace (i2 + (k + 8)) with (i2 + k + 8) by lia. apply cong_add. exact M2. }
      destruct (Z.leb_spec 0 (kk - 8)).
      + apply (IH i1 i2 (k + 8) j1n j2n (kk - 8) (budget - 1)); try lia; try tauto.
      + cbn [fst]. apply SOUND_of_EQBn. intros j Hj. apply HE8'. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem mainGtU_sound : forall i1 i2 budget, 0 <= i1 <= n + 14 -> 0 <= i2 <= n + 14 ->
    SOUND i1 i2 (fst (mainGtU i1 i2 a2 qoff n budget)).
  Proof.
    intros i1 i2 budget H1 H2. unfold mainGtU.
    pose proof (gtu_pre_spec 12 i1 i2 0 i1 i2 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia)
                  ltac:(intros j Hj; lia)) as PS.
    destruct (gtu_pre 12 a2 i1 i2) as [[r j1] j2]. destruct r as [b|]; [exact PS|].
    cps_destruct PS as (-> & -> & HE). change (Z.of_nat 12) with 12 in HE |- *.
    apply (gtu_loop_spec _ i1 i2 12 (i1 + 12) (i2 + 12) (n + 8) budget); try lia.
    - apply cong_refl.
    - apply cong_refl.
    - replace (0 + 12) with 12 in HE by lia. exact HE.
    - (* [comment removed for export] *)
      rewrite !Nat2Z.inj_succ, Z2Nat.id by (apply Z.div_pos; lia).
      pose proof (Z.mul_div_le (n + 8) 8 ltac:(lia)). pose proof (Z_div_mod_eq_full (n + 8) 8).
      pose proof (Z.mod_pos_bound (n + 8) 8 ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End GtU.
