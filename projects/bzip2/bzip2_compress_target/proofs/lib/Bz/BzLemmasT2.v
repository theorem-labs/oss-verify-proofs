(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzModel BzLemmasHb BzLemmasT.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Lemma zsum_indicator : forall (s : Z) (n : nat), 0 <= s < Z.of_nat n ->
  zsum (fun b => if s =? b then 1 else 0) 0 n = 1.
Proof.
  intros s n Hs.
  assert (G : forall m, zsum (fun b => if s =? b then 1 else 0) 0 m = (if s <? Z.of_nat m then 1 else 0)).
  { induction m as [|m IH]; [cbn; destruct (Z.ltb_spec s 0); [lia|reflexivity]|].
    rewrite zsum_S, IH, Z.add_0_l.
    destruct (Z.ltb_spec s (Z.of_nat m)), (Z.eqb_spec s (Z.of_nat m)), (Z.ltb_spec s (Z.of_nat (S m))); lia. }
  rewrite G. destruct (Z.ltb_spec s (Z.of_nat n)); lia.
Qed.

Lemma zsum_add : forall f g lo n, zsum (fun q => f q + g q) lo n = zsum f lo n + zsum g lo n.
Proof. induction n; intros; cbn [zsum]; [lia|]. rewrite IHn. lia. Qed.

Lemma zsum_zero : forall f lo k, (forall q, f q = 0) -> zsum f lo k = 0.
Proof. induction k; intros; cbn [zsum]; [reflexivity|]. rewrite IHk, H by assumption. lia. Qed.

(* [comment removed for export] *)
Lemma occ_total : forall sym n, (forall k, 0 <= k < Z.of_nat n -> 0 <= sym k < 256) ->
  zsum (occ sym n) 0 256 = Z.of_nat n.
Proof.
  intros sym n Hs. induction n as [|n IH].
  - apply zsum_zero. intros. apply occ_0.
  - rewrite (zsum_ext (occ sym (S n)) (fun b => occ sym n b + (if sym (Z.of_nat n) =? b then 1 else 0))).
    2:{ intros q Hq. apply occ_S. }
    rewrite zsum_add, IH by (intros; apply Hs; lia).
    rewrite (zsum_indicator (sym (Z.of_nat n)) 256) by (change (Z.of_nat 256) with 256; apply Hs; lia). lia.
Qed.

Section Psum.
  Variables (sym unz : Z -> Z) (nblock : nat).
  Let n : Z := Z.of_nat nblock.
  Hypothesis Hsym : forall k, 0 <= k < n -> 0 <= sym k < 256.
  Hypothesis Hhist : hist_ok unz sym nblock.

  Lemma psum_256 : psum unz 256 = n.
  Proof.
    unfold psum. change (Z.to_nat 256) with 256%nat.
    rewrite (zsum_ext unz (occ sym nblock)); [apply occ_total; exact Hsym|].
    intros q Hq. apply Hhist. lia.
  Qed.
  Lemma unz_range : forall b, 0 <= b < 256 -> 0 <= unz b <= n.
  Proof. intros. rewrite (Hhist b H). apply occ_bounds. Qed.
  Lemma psum_range : forall j, 0 <= j <= 256 -> 0 <= psum unz j <= n.
  Proof.
    intros j Hj. rewrite <- psum_256.
    pose proof (psum_mono unz 0 j ltac:(lia) ltac:(intros; pose proof (unz_range q ltac:(lia)); lia)).
    pose proof (psum_mono unz j 256 ltac:(lia) ltac:(intros; pose proof (unz_range q ltac:(lia)); lia)).
    rewrite psum_0 in *. lia.
  Qed.
  Lemma psum_step_le : forall j, 0 <= j < 256 -> psum unz j <= psum unz (j + 1).
  Proof. intros. rewrite psum_succ by lia. pose proof (unz_range j ltac:(lia)). lia. Qed.
End Psum.

(* [comment removed for export] *)
Section FastValue.
  Variables (sym unz cf0 tt0 : Z -> Z) (nblock : nat).
  Let n : Z := Z.of_nat nblock.
  Hypothesis Hsym : forall k, 0 <= k < n -> 0 <= sym k < 256.
  Hypothesis Hhist : hist_ok unz sym nblock.
  Hypothesis Hcf : forall b, 0 <= b <= 256 -> cf0 b = psum unz b.
  Hypothesis Hcf256 : cf0 256 <= n.
  Hypothesis Htt0 : forall k, 0 <= k < n -> tt0 k = sym k.
  Hypothesis Htt0r : forall k, 0 <= tt0 k < 2 ^ 32.
  Hypothesis Hnmax : n <= 900000.

  Let T := tval sym cf0.

  Lemma Htt0' : forall k, 0 <= k < n -> lo8 (tt0 k) = sym k.
  Proof. intros. rewrite Htt0 by lia. apply lo8_small. apply Hsym. lia. Qed.

  (* [comment removed for export] *)
  Lemma tval_surj : forall j, 0 <= j < n -> exists k, 0 <= k < n /\ T k = j.
  Proof.
    intros j Hj.
    set (l := map T (zseq 0 nblock)).
    assert (NDZ : NoDup (zseq 0 nblock)).
    { unfold zseq. apply NoDup_nth_error. intros i k Hi E. rewrite length_map, length_seq in Hi.
      rewrite !nth_error_map, !nth_error_seq in E.
      destruct (Nat.ltb_spec i nblock); [|lia]. destruct (Nat.ltb_spec k nblock); cbn in E; [|discriminate].
      injection E. lia. }
    assert (ND : NoDup l).
    { unfold l. apply NoDup_map_NoDup_ForallPairs; [|exact NDZ].
      intros x y Hx Hy E. apply in_zseq in Hx. apply in_zseq in Hy.
      apply (tval_inj sym unz cf0 nblock Hsym Hhist Hcf Hcf256 x y); [unfold n; lia| unfold n; lia| exact E]. }
    assert (INCL : incl l (zseq 0 nblock)).
    { intros x Hx. unfold l in Hx. apply in_map_iff in Hx. cps_destruct Hx as (k & E & Hk). subst x. apply in_zseq in Hk. apply in_zseq.
      cps_destruct (tval_range sym unz cf0 nblock Hsym Hhist Hcf Hcf256 k ltac:(lia)) as (A & B & C). unfold T. lia. }
    assert (LEN : (length (zseq 0 nblock) <= length l)%nat) by (unfold l; rewrite length_map; lia).
    pose proof (NoDup_length_incl ND LEN INCL) as BACK.
    assert (IN : In j (zseq 0 nblock)) by (apply in_zseq; unfold n in Hj; lia).
    apply BACK in IN. unfold l in IN. apply in_map_iff in IN. cps_destruct IN as (k & E & Hk). apply in_zseq in Hk.
    exists k. unfold n. split; [lia| exact E].
  Qed.

  (* [comment removed for export] *)
  Lemma tinv_final_slots : forall m, (m <= nblock)%nat ->
    forall k, 0 <= k < Z.of_nat m -> fst (tinv 0 m tt0 cf0) (T k) = Z.lor (tt0 (T k)) (Z.shiftl k 8).
  Proof.
    induction m as [|m IH]; intros Hm k Hk; [lia|].
    rewrite tinv_snoc. cbn zeta. cbn [fst snd]. rewrite Z.add_0_l.
    cps_destruct (tinv_inv sym unz cf0 tt0 nblock Hsym Hhist Hcf Hcf256 Htt0' Htt0r Hnmax m ltac:(lia)) as (A1 & A2 & A3 & A4 & A5).
    set (r := tinv 0 m tt0 cf0) in *.
    assert (U : lo8 (fst r (Z.of_nat m)) = sym (Z.of_nat m)) by (apply A3; unfold n in *; lia).
    rewrite U. pose proof (Hsym (Z.of_nat m) ltac:(unfold n in *; lia)) as SB.
    assert (IDX : snd r (sym (Z.of_nat m)) = T (Z.of_nat m)) by (rewrite A1 by lia; unfold T, tval; now rewrite Nat2Z.id).
    rewrite IDX. rewrite zfupd_eq.
    destruct (Z.eqb_spec (T k) (T (Z.of_nat m))) as [E|NE].
    - assert (k = Z.of_nat m) by (apply (tval_inj sym unz cf0 nblock Hsym Hhist Hcf Hcf256); unfold n in *; try lia; exact E).
      subst k. f_equal.
      (* [comment removed for export] *)
      assert (G : forall m', (m' <= m)%nat -> fst (tinv 0 m' tt0 cf0) (T (Z.of_nat m)) = tt0 (T (Z.of_nat m))).
      { induction m' as [|m' IH']; intros Hm'; [reflexivity|].
        rewrite tinv_snoc. cbn zeta. cbn [fst snd]. rewrite Z.add_0_l.
        cps_destruct (tinv_inv sym unz cf0 tt0 nblock Hsym Hhist Hcf Hcf256 Htt0' Htt0r Hnmax m' ltac:(lia)) as (B1 & B2 & B3 & B4 & B5).
        set (r' := tinv 0 m' tt0 cf0) in *.
        rewrite (B3 (Z.of_nat m')) by (unfold n in *; lia).
        rewrite B1 by (apply Hsym; unfold n in *; lia).
        replace (cf0 (sym (Z.of_nat m')) + occ sym m' (sym (Z.of_nat m'))) with (T (Z.of_nat m')) by (unfold T, tval; now rewrite Nat2Z.id).
        rewrite zfupd_other; [apply IH'; lia|].
        intros EQ. assert (Z.of_nat m = Z.of_nat m') by (apply (tval_inj sym unz cf0 nblock Hsym Hhist Hcf Hcf256); unfold n in *; try lia; exact EQ). lia. }
      apply G. lia.
    - apply IH; [lia|]. assert (k <> Z.of_nat m) by (intros ->; apply NE; reflexivity). lia.
  Qed.

  Theorem tinv_final_shr8 : forall j, 0 <= j < n ->
    0 <= Z.shiftr (fst (tinv 0 nblock tt0 cf0) j) 8 < n.
  Proof.
    intros j Hj. cps_destruct (tval_surj j Hj) as (k & Hk & E). rewrite <- E.
    rewrite (tinv_final_slots nblock ltac:(lia) k) by (unfold n in Hk; lia).
    cps_destruct (tval_range sym unz cf0 nblock Hsym Hhist Hcf Hcf256 k ltac:(unfold n in Hk; lia)) as (A & B & C).
    fold T in A, C. rewrite Htt0 by (unfold n; lia). pose proof (Hsym (T k) ltac:(unfold n; lia)) as SB.
    rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag by lia. cbn [Z.shiftl].
    rewrite (Z.shiftr_eq_0 (sym (T k)) 8); [rewrite Z.lor_0_l; lia| lia|].
    destruct (Z.eq_dec (sym (T k)) 0) as [->|NZ]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma tinv_lt28 : forall m, (m <= nblock)%nat -> forall k, 0 <= k < n -> 0 <= fst (tinv 0 m tt0 cf0) k < 2 ^ 28.
  Proof.
    induction m as [|m IH]; intros Hm k Hk.
    - cbn [tinv fst]. rewrite Htt0 by lia. pose proof (Hsym k Hk). lia.
    - rewrite tinv_snoc. cbn zeta. cbn [fst snd]. rewrite Z.add_0_l.
      cps_destruct (tinv_inv sym unz cf0 tt0 nblock Hsym Hhist Hcf Hcf256 Htt0' Htt0r Hnmax m ltac:(lia)) as (A1 & A2 & A3 & A4 & A5).
      set (r := tinv 0 m tt0 cf0) in *.
      rewrite (A3 (Z.of_nat m)) by (unfold n in *; lia).
      rewrite A1 by (apply Hsym; unfold n in *; lia).
      replace (cf0 (sym (Z.of_nat m)) + occ sym m (sym (Z.of_nat m))) with (T (Z.of_nat m)) by (unfold T, tval; now rewrite Nat2Z.id).
      cps_destruct (tval_range sym unz cf0 nblock Hsym Hhist Hcf Hcf256 (Z.of_nat m) ltac:(unfold n in *; lia)) as (B1 & B2 & B3). fold T in B1, B3.
      rewrite zfupd_eq. destruct (Z.eqb_spec k (T (Z.of_nat m))) as [->|NE]; [|apply IH; lia].
      pose proof (IH ltac:(lia) (T (Z.of_nat m)) ltac:(unfold n; lia)) as R.
      apply (lor_lt_pow2 _ _ 28); [exact R|]. rewrite Z.shiftl_mul_pow2 by lia. unfold n in *. split; [lia|].
      change (2 ^ 28) with (2 ^ 20 * 2 ^ 8). apply Z.mul_lt_mono_pos_r; lia.
  Qed.
End FastValue.

(* [comment removed for export] *)
Section FastWalk.
  Variables (sym unz tt0 : Z -> Z) (nblock : Z).
  Hypothesis Hn : 0 <= nblock <= 900000.
  Hypothesis Hsym : forall k, 0 <= k < nblock -> 0 <= sym k < 256.
  Hypothesis Hhist : hist_ok unz sym (Z.to_nat nblock).
  Hypothesis Htt0 : forall k, 0 <= k < nblock -> tt0 k = sym k.
  Hypothesis Htt0r : forall k, 0 <= tt0 k < 2 ^ 32.

  Let nb := Z.to_nat nblock.
  Let HsymN : forall k, 0 <= k < Z.of_nat nb -> 0 <= sym k < 256. Proof. intros; apply Hsym; lia. Qed.
  Let Hcf : forall b, 0 <= b <= 256 -> psum unz b = psum unz b. Proof. reflexivity. Qed.
  Let Hcf256 : psum unz 256 <= Z.of_nat nb. Proof. rewrite (psum_256 sym unz nb HsymN Hhist). lia. Qed.
  Let Htt0N : forall k, 0 <= k < Z.of_nat nb -> tt0 k = sym k. Proof. intros; apply Htt0; lia. Qed.
  Let Htt0' : forall k, 0 <= k < Z.of_nat nb -> lo8 (tt0 k) = sym k.
  Proof. intros. rewrite Htt0 by lia. apply lo8_small. apply Hsym. lia. Qed.
  Let HnN : Z.of_nat nb <= 900000. Proof. lia. Qed.

  Theorem fast_step_pack : forall i, 0 <= i < nblock ->
    let r := tinv 0 (Z.to_nat i) tt0 (psum unz) in
    let uc := sym i in let idx := snd r uc in
    lo8 (fst r i) = uc /\ 0 <= uc < 256 /\ 0 <= idx < nblock /\ 0 <= fst r idx < 2 ^ 28 /\
    (forall k, 0 <= k < nblock -> 0 <= fst r k < 2 ^ 28) /\
    tinv 0 (Z.to_nat (i + 1)) tt0 (psum unz) = (zfupd (fst r) idx (Z.lor (fst r idx) (i * 256)), zfupd (snd r) uc (idx + 1)).
  Proof.
    intros i Hi. cbn zeta.
    pose proof (tinv_step_facts sym unz (psum unz) tt0 nb HsymN Hhist Hcf Hcf256 Htt0' Htt0r HnN (Z.to_nat i) ltac:(lia)) as TF.
    cbn zeta in TF. rewrite Z2Nat.id in TF by lia. cps_destruct TF as (U & R1 & IDX & R2 & R3 & R4 & R5).
    pose proof (tinv_lt28 sym unz (psum unz) tt0 nb HsymN Hhist Hcf Hcf256 Htt0N Htt0r HnN (Z.to_nat i) ltac:(lia)) as L28.
    rewrite <- U. split; [reflexivity|]. split; [exact R1|]. split; [unfold nb in R2; lia|].
    split; [apply L28; unfold nb in *; lia|]. split; [intros; apply L28; unfold nb; lia|].
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. rewrite tinv_snoc. cbn zeta.
    rewrite Z.add_0_l, Z2Nat.id by lia. rewrite U. rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
  Qed.

  Theorem fast_final_pack :
    let r := tinv 0 (Z.to_nat nblock) tt0 (psum unz) in
    (forall j, 0 <= j < nblock -> 0 <= Z.shiftr (fst r j) 8 < nblock) /\
    (forall k, 0 <= k < nblock -> 0 <= fst r k < 2 ^ 28).
  Proof.
    cbn zeta. split.
    - intros j Hj. pose proof (tinv_final_shr8 sym unz (psum unz) tt0 nb HsymN Hhist Hcf Hcf256 Htt0N Htt0r HnN j ltac:(lia)). unfold nb in *. lia.
    - intros k Hk. apply (tinv_lt28 sym unz (psum unz) tt0 nb HsymN Hhist Hcf Hcf256 Htt0N Htt0r HnN); unfold nb; lia.
  Qed.
End FastWalk.

(* [comment removed for export] *)
Section SmallWalk.
  Variables (sym unz ll16_0 ll4_0 : Z -> Z) (nblock o : Z).
  Hypothesis Hn : 0 <= nblock <= 900000.
  Hypothesis Hsym : forall k, 0 <= k < nblock -> 0 <= sym k < 256.
  Hypothesis Hhist : hist_ok unz sym (Z.to_nat nblock).
  Hypothesis Hll16 : forall k, 0 <= k < nblock -> ll16_0 k = sym k.
  Hypothesis Hll16r : forall k, 0 <= ll16_0 k < 2 ^ 16.
  Hypothesis Hll4r : forall a, 0 <= ll4_0 a < 256.
  Hypothesis Ho : 0 <= o < nblock.

  Let nb := Z.to_nat nblock.
  Let HsymN : forall k, 0 <= k < Z.of_nat nb -> 0 <= sym k < 256. Proof. intros; apply Hsym; lia. Qed.
  Let Hcf : forall b, 0 <= b <= 256 -> psum unz b = psum unz b. Proof. reflexivity. Qed.
  Let Hcf256 : psum unz 256 <= Z.of_nat nb. Proof. rewrite (psum_256 sym unz nb HsymN Hhist). lia. Qed.
  Let HnN : Z.of_nat nb <= 900000. Proof. lia. Qed.
  Let Hll16' : forall k, 0 <= k < Z.of_nat nb -> lo8 (ll16_0 k) = sym k.
  Proof. intros. rewrite Hll16 by lia. apply lo8_small. apply Hsym. lia. Qed.
  Let HoN : 0 <= o < Z.of_nat nb. Proof. lia. Qed.

  Definition tvst (i : Z) := tvec 0 (Z.to_nat i) ll16_0 ll4_0 (psum unz).

  Theorem small_step_pack : forall i, 0 <= i < nblock ->
    let '(a, b, c) := tvst i in
    let uc := sym i in let v := c uc in
    lo8 (a i) = uc /\ 0 <= uc < 256 /\ 0 <= v < nblock /\ 0 <= Z.shiftr v 16 < 16 /\
    0 <= b (Z.shiftr i 1) < 256 /\ (forall k, 0 <= a k < 2 ^ 16) /\ (forall y, 0 <= b y < 256) /\
    (forall b', 0 <= b' < 256 -> 0 <= c b' <= nblock) /\
    tvst (i + 1) = (fst (set_ll a b i v), snd (set_ll a b i v), zfupd c uc (v + 1)).
  Proof.
    intros i Hi. unfold tvst.
    pose proof (tvec_step_facts sym unz (psum unz) ll16_0 ll4_0 nb HsymN Hhist Hcf Hcf256 HnN Hll16' Hll16r Hll4r (Z.to_nat i) ltac:(lia)) as TF.
    pose proof (tvec_inv sym unz (psum unz) ll16_0 ll4_0 nb HsymN Hhist Hcf Hcf256 HnN Hll16' Hll16r Hll4r (Z.to_nat i) ltac:(lia)) as IV.
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. rewrite tvec_snoc.
    destruct (tvec 0 (Z.to_nat i) ll16_0 ll4_0 (psum unz)) as [[a b] c]. cbn zeta in *.
    rewrite Z2Nat.id in TF, IV by lia. cps_destruct TF as (U & R1 & V & R2 & R3 & R4 & R5 & R6 & R7 & R8).
    cps_destruct IV as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
    rewrite Z.add_0_l, Z2Nat.id by lia. rewrite !U in *.
    split; [reflexivity|]. split; [exact R1|]. split; [unfold nb in R2; lia|]. split; [exact R4|].
    split; [exact R6|]. split; [exact A5|]. split; [exact A6|]. split; [| reflexivity].
    intros b' Hb'. rewrite A1 by lia. pose proof (psum_range sym unz nb HsymN Hhist b' ltac:(lia)).
    pose proof (occ_bounds sym (Z.to_nat i) b'). pose proof (occ_le_mono sym (Z.to_nat i) nb b' ltac:(lia)).
    pose proof (Hhist b' Hb') as HB. pose proof (psum_succ unz b' ltac:(lia)) as PS.
    pose proof (psum_range sym unz nb HsymN Hhist (b' + 1) ltac:(lia)). unfold nb in *. lia.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition prst (s : nat) := pr_iter s (pr_start (psum unz) ll16_0 ll4_0 nb o).
  Definition ncyc : nat := cycle sym (psum unz) nb o.

  Lemma prst_0 : let '(a, b, c) := tvst nblock in prst 0 = (a, b, o, get_ll a b o).
  Proof.
    unfold prst, pr_start, ll16_T, ll4_T, tvst. fold nb. cbn [pr_iter].
    destruct (tvec 0 nb ll16_0 ll4_0 (psum unz)) as [[a b] c]. reflexivity.
  Qed.

  Theorem small_pr_pack :
    (1 <= Z.of_nat ncyc <= nblock) /\
    (forall s, (s < ncyc)%nat ->
       let '(a, b, i, j) := prst s in
       0 <= i < nblock /\ 0 <= j < nblock /\ 0 <= get_ll a b j < nblock /\ 0 <= b (Z.shiftr j 1) < 256 /\
       (forall y, 0 <= b y < 256) /\ (forall x, 0 <= a x < 2 ^ 16) /\
       prst (S s) = (fst (set_ll a b j i), snd (set_ll a b j i), j, get_ll a b j) /\
       (j = o <-> S s = ncyc)).
  Proof.
    pose proof (ptr_rev_facts sym unz (psum unz) ll16_0 ll4_0 nb HsymN Hhist Hcf Hcf256 HnN Hll16' Hll16r Hll4r o HoN) as [CR PF].
    split; [unfold ncyc, nb in *; lia|].
    intros s Hs. unfold prst. pose proof (PF s Hs) as X.
    destruct (pr_iter s _) as [[[a b] i] j] eqn:E. cbn zeta in X. cbn [pr_step] in X.
    cps_destruct X as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
    unfold nb in *. repeat (split; [first [assumption| lia]|]).
    split; [| exact B8]. rewrite pr_iter_S. unfold pr_start in E |- *. rewrite E. reflexivity.
  Qed.
End SmallWalk.
