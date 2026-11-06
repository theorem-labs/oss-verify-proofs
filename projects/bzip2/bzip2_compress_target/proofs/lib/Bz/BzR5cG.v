(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCStream BzDState.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cW.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cW.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuff BzCRebuildF BzCHuffF4. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5a BzR5bK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module BzR5b.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5a OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5bK.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sumF_S_r : forall m g j, sumF g j (S m) = sumF g j m + g (j + Z.of_nat m).
Proof. intros m g j. apply sumF_snoc. Qed.
Lemma sumF_mono_n : forall m m' g j, (m <= m')%nat -> (forall b, j <= b -> 0 <= g b) -> sumF g j m <= sumF g j m'.
Proof.
  intros m m' g j Hm Hg. induction Hm as [|m' Hm IH]; [lia|]. rewrite sumF_S_r.
  assert (0 <= g (j + Z.of_nat m')) by (apply Hg; lia). lia.
Qed.
(* [comment removed for export] *)
Lemma sumF_prefix : forall A g i, 0 <= i <= Z.of_nat A ->
  sumF (fun j => if j <? i then g j else 0) 0 A = sumF g 0 (Z.to_nat i).
Proof.
  intros A g i Hi.
  assert (G : forall m, (Z.to_nat i <= m)%nat -> sumF (fun j => if j <? i then g j else 0) 0 m = sumF g 0 (Z.to_nat i)).
  { intros m Hm. induction Hm as [|m Hm IH].
    - apply sumF_ext. intros b Hb. destruct (Z.ltb_spec b i); [reflexivity| lia].
    - rewrite sumF_S_r, IH. destruct (Z.ltb_spec (0 + Z.of_nat m) i); lia. }
  apply G. lia.
Qed.
(* [comment removed for export] *)
Lemma sumF_indic : forall m v a, sumF (fun b => ind (v =? b)) a m = ind ((a <=? v) && (v <? a + Z.of_nat m)).
Proof.
  induction m as [|m IH]; intros v a; cbn [sumF].
  - destruct (Z.leb_spec a v), (Z.ltb_spec v (a + Z.of_nat 0)); cbn; lia.
  - rewrite IH. unfold ind.
    destruct (Z.eqb_spec v a), (Z.leb_spec (a + 1) v), (Z.ltb_spec v (a + 1 + Z.of_nat m)), (Z.leb_spec a v), (Z.ltb_spec v (a + Z.of_nat (S m)));
      cbn; lia.
Qed.
Lemma ind_nonneg : forall b, 0 <= ind b <= 1.
Proof. intros [|]; cbn; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lexb (L : Z -> Z) (j i : Z) : bool := (L j <? L i) || ((L j =? L i) && (j <? i)).
(* [comment removed for export] *)
Definition ccode (L : Z -> Z) (A i : Z) : Z := sumF (fun j => if lexb L j i then 2 ^ (L i - L j) else 0) 0 (Z.to_nat A).
(* [comment removed for export] *)
Definition crank (L : Z -> Z) (A i : Z) : Z := sumF (fun j => ind (lexb L j i)) 0 (Z.to_nat A).
(* [comment removed for export] *)
Definition ceq (L : Z -> Z) (m : nat) (n : Z) : Z := sumF (fun j => ind (L j =? n)) 0 m.
Definition cnt_eq (L : Z -> Z) (A n : Z) : Z := ceq L (Z.to_nat A) n.
Definition cnt_lt (L : Z -> Z) (A n : Z) : Z := sumF (fun j => ind (L j <? n)) 0 (Z.to_nat A).
(* [comment removed for export] *)
Definition fcode (L : Z -> Z) (A n : Z) : Z := sumF (fun j => if L j <? n then 2 ^ (n - L j) else 0) 0 (Z.to_nat A).
Definition wsum (L : Z -> Z) (A n : Z) : Z := sumF (fun j => if L j <=? n then 2 ^ (n - L j) else 0) 0 (Z.to_nat A).

Section Canon.
  Variables (L : Z -> Z) (A : Z).
  Hypothesis HA : 0 <= A.
  Hypothesis Lpos : forall j, 0 <= j < A -> 1 <= L j.

  Lemma wsum_split : forall n, wsum L A n = fcode L A n + cnt_eq L A n.
  Proof.
    intros n. unfold wsum, fcode, cnt_eq, ceq. rewrite <- sumF_addf. apply sumF_ext. intros b Hb. unfold ind.
    destruct (Z.leb_spec (L b) n), (Z.ltb_spec (L b) n), (Z.eqb_spec (L b) n); try lia.
    replace (n - L b) with 0 by lia. cbn. lia.
  Qed.
  Lemma fcode_succ : forall n, fcode L A (n + 1) = 2 * wsum L A n.
  Proof.
    intros n. unfold wsum, fcode. rewrite <- sumF_scal. apply sumF_ext. intros b Hb.
    destruct (Z.ltb_spec (L b) (n + 1)), (Z.leb_spec (L b) n); try lia.
    replace (n + 1 - L b) with (Z.succ (n - L b)) by lia. rewrite Z.pow_succ_r by lia. lia.
  Qed.
  Lemma fcode_min : forall n, (forall j, 0 <= j < A -> n <= L j) -> fcode L A n = 0.
  Proof.
    intros n Hn. unfold fcode. apply sumF_zero. intros b Hb. destruct (Z.ltb_spec (L b) n); [|reflexivity].
    pose proof (Hn b ltac:(lia)). lia.
  Qed.
  Lemma cnt_lt_min : forall n, (forall j, 0 <= j < A -> n <= L j) -> cnt_lt L A n = 0.
  Proof.
    intros n Hn. unfold cnt_lt. apply sumF_zero. intros b Hb. destruct (Z.ltb_spec (L b) n); [|reflexivity].
    pose proof (Hn b ltac:(lia)). lia.
  Qed.
  Lemma cnt_lt_succ : forall n, cnt_lt L A (n + 1) = cnt_lt L A n + cnt_eq L A n.
  Proof.
    intros n. unfold cnt_lt, cnt_eq, ceq. rewrite <- sumF_addf. apply sumF_ext. intros b Hb. unfold ind.
    destruct (Z.ltb_spec (L b) (n + 1)), (Z.ltb_spec (L b) n), (Z.eqb_spec (L b) n); lia.
  Qed.
  Lemma fcode_nonneg : forall n, 0 <= fcode L A n.
  Proof. intros n. unfold fcode. apply sumF_nonneg. intros b Hb. destruct (L b <? n); [apply Z.pow_nonneg|]; lia. Qed.
  (* [comment removed for export] *)
  Lemma ceq_nonneg : forall m n, 0 <= ceq L m n.
  Proof. intros m n. unfold ceq. apply sumF_nonneg. intros b Hb. apply ind_nonneg. Qed.
  Lemma cnt_lt_nonneg : forall n, 0 <= cnt_lt L A n.
  Proof. intros n. unfold cnt_lt. apply sumF_nonneg. intros b Hb. apply ind_nonneg. Qed.
  Lemma ceq_S : forall m n, ceq L (S m) n = ceq L m n + ind (L (Z.of_nat m) =? n).
  Proof. intros m n. unfold ceq. rewrite sumF_S_r. rewrite Z.add_0_l. reflexivity. Qed.
  Lemma ceq_mono : forall m m' n, (m <= m')%nat -> ceq L m n <= ceq L m' n.
  Proof. intros m m' n Hm. unfold ceq. apply sumF_mono_n; [exact Hm|]. intros b Hb. apply ind_nonneg. Qed.
  (* [comment removed for export] *)
  Lemma ceq_lt_cnt : forall i, 0 <= i < A -> ceq L (Z.to_nat i) (L i) + 1 <= cnt_eq L A (L i).
  Proof.
    intros i Hi. unfold cnt_eq.
    pose proof (ceq_S (Z.to_nat i) (L i)) as E. rewrite Z2Nat.id, Z.eqb_refl in E by lia. cbn [ind] in E.
    pose proof (ceq_mono (S (Z.to_nat i)) (Z.to_nat A) (L i) ltac:(lia)). lia.
  Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma ccode_eq : forall i, 0 <= i < A -> ccode L A i = fcode L A (L i) + ceq L (Z.to_nat i) (L i).
  Proof.
    intros i Hi. unfold ccode, fcode, ceq.
    rewrite <- (sumF_prefix (Z.to_nat A) (fun j => ind (L j =? L i)) i) by lia.
    rewrite <- sumF_addf. apply sumF_ext. intros b Hb. unfold lexb, ind.
    destruct (Z.ltb_spec (L b) (L i)), (Z.eqb_spec (L b) (L i)), (Z.ltb_spec b i); cbn; try lia.
    all: replace (L i - L b) with 0 by lia; cbn; lia.
  Qed.
  Lemma crank_eq : forall i, 0 <= i < A -> crank L A i = cnt_lt L A (L i) + ceq L (Z.to_nat i) (L i).
  Proof.
    intros i Hi. unfold crank, cnt_lt, ceq.
    rewrite <- (sumF_prefix (Z.to_nat A) (fun j => ind (L j =? L i)) i) by lia.
    rewrite <- sumF_addf. apply sumF_ext. intros b Hb. unfold lexb, ind.
    destruct (Z.ltb_spec (L b) (L i)), (Z.eqb_spec (L b) (L i)), (Z.ltb_spec b i); cbn; lia.
  Qed.

  Lemma ccode_range : forall i, 0 <= i < A -> 0 <= ccode L A i /\ ccode L A i + 1 <= wsum L A (L i).
  Proof.
    intros i Hi. rewrite ccode_eq by lia. rewrite wsum_split.
    pose proof (fcode_nonneg (L i)). pose proof (ceq_nonneg (Z.to_nat i) (L i)). pose proof (ceq_lt_cnt i Hi). lia.
  Qed.
  Lemma crank_range : forall i, 0 <= i < A -> 0 <= crank L A i < A.
  Proof.
    intros i Hi. unfold crank. split; [apply sumF_nonneg; intros; apply ind_nonneg|].
    assert (E : sumF (fun j => ind (lexb L j i)) 0 (Z.to_nat A) <= sumF (fun j => 1 - ind (i =? j)) 0 (Z.to_nat A)).
    { apply sumF_lef. intros b Hb. unfold lexb, ind. destruct (Z.eqb_spec i b) as [->|NE].
      - rewrite Z.ltb_irrefl. cbn. rewrite Z.ltb_irrefl, Bool.andb_false_r. lia.
      - destruct (_ || _)%bool; lia. }
    assert (C : forall m, sumF (fun _ => 1) 0 m = Z.of_nat m) by (induction m as [|m IH]; [reflexivity| rewrite sumF_S_r, IH; lia]).
    assert (E2 : sumF (fun j => 1 - ind (i =? j)) 0 (Z.to_nat A) = Z.of_nat (Z.to_nat A) - 1).
    { rewrite (sumF_ext _ _ (fun j => 1 + (-1) * ind (i =? j))) by (intros; lia).
      rewrite sumF_addf, sumF_scal, sumF_indic, C.
      replace ((0 <=? i) && (i <? 0 + Z.of_nat (Z.to_nat A)))%bool with true by (symmetry; apply Bool.andb_true_iff; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
      cbn [ind]. lia. }
    rewrite E2 in E. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma wsum_scale : forall n n', 0 <= n <= n' -> wsum L A n * 2 ^ (n' - n) <= fcode L A n' + (if n =? n' then cnt_eq L A n' else 0).
  Proof.
    intros n n' Hn. destruct (Z.eqb_spec n n') as [<-|NE].
    - rewrite <- wsum_split. replace (n - n) with 0 by lia. cbn. lia.
    - rewrite Z.add_0_r. unfold wsum, fcode. rewrite Z.mul_comm, <- sumF_scal. apply sumF_lef. intros b Hb.
      destruct (Z.leb_spec (L b) n), (Z.ltb_spec (L b) n'); try lia;
        try (rewrite <- Z.pow_add_r by lia; replace (n' - n + (n - L b)) with (n' - L b) by lia; lia);
        try (apply Z.pow_nonneg; lia); try (apply Z.mul_nonneg_nonneg; try apply Z.pow_nonneg; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma ccode_prefix : forall i n, 0 <= i < A -> 0 <= n < L i -> wsum L A n <= ccode L A i / 2 ^ (L i - n).
  Proof.
    intros i n Hi Hn. pose proof (wsum_scale n (L i) ltac:(lia)) as W.
    replace (n =? L i) with false in W by (symmetry; apply Z.eqb_neq; lia). rewrite Z.add_0_r in W.
    rewrite ccode_eq by lia. pose proof (ceq_nonneg (Z.to_nat i) (L i)).
    apply Z.div_le_lower_bound; [apply Z.pow_pos_nonneg; lia|]. lia.
  Qed.

  (* [comment removed for export] *)
  Hypothesis KR : forall n, 1 <= n -> wsum L A n <= 2 ^ n.
  Lemma ccode_lt : forall i, 0 <= i < A -> 0 <= ccode L A i < 2 ^ (L i).
  Proof.
    intros i Hi. pose proof (ccode_range i Hi). pose proof (KR (L i) ltac:(pose proof (Lpos i Hi); lia)). lia.
  Qed.
End Canon.

(* [comment removed for export] *)
Lemma kraft17_KR : forall (L : Z -> Z) A, 0 <= A -> (forall j, 0 <= j < A -> 1 <= L j <= 17) ->
  sumF (fun j => 2 ^ (17 - L j)) 0 (Z.to_nat A) <= 2 ^ 17 ->
  forall n, 1 <= n -> wsum L A n <= 2 ^ n.
Proof.
  intros L A HA HL K n Hn.
  assert (W17 : wsum L A 17 = sumF (fun j => 2 ^ (17 - L j)) 0 (Z.to_nat A)).
  { unfold wsum. apply sumF_ext. intros b Hb. pose proof (HL b ltac:(lia)). destruct (Z.leb_spec (L b) 17); [reflexivity| lia]. }
  destruct (Z.le_gt_cases n 17) as [LE|GT].
  - pose proof (wsum_scale L A n 17 ltac:(lia)) as S.
    assert (F : fcode L A 17 + (if n =? 17 then cnt_eq L A 17 else 0) <= wsum L A 17).
    { rewrite (wsum_split L A 17). destruct (n =? 17); [lia|]. pose proof (ceq_nonneg L (Z.to_nat A) 17). unfold cnt_eq. lia. }
    apply (Z.mul_le_mono_pos_r _ _ (2 ^ (17 - n))); [apply Z.pow_pos_nonneg; lia|].
    rewrite <- Z.pow_add_r by lia. replace (n + (17 - n)) with 17 by lia. lia.
  - assert (E : wsum L A n = 2 ^ (n - 17) * wsum L A 17).
    { unfold wsum. rewrite <- sumF_scal. apply sumF_ext. intros b Hb. pose proof (HL b ltac:(lia)).
      destruct (Z.leb_spec (L b) n), (Z.leb_spec (L b) 17); try lia.
      rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    rewrite E, W17. replace n with ((n - 17) + 17) at 2 by lia. rewrite (Z.pow_add_r 2 (n - 17) 17) by lia.
    apply Z.mul_le_mono_nonneg_l; [apply Z.pow_nonneg; lia| exact K].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition Lrow (len : zarr) (lb : Z) (i : Z) : Z := zget len (lb + i).

Section Assign.
  Variables (len : zarr) (cb lb A : Z).
  Hypothesis HA : 0 <= A.
  #[local] Abbreviation L := (Lrow len lb).

  Lemma ha_inner_spec : forall k code n i vec, 0 <= i ->
    let r := ha_inner k code len cb lb n i vec in
    snd r = vec + sumF (fun j => ind (L j =? n)) i k /\
    (forall j, i <= j < i + Z.of_nat k -> L j = n -> zget (fst r) (cb + j) = vec + sumF (fun j' => ind (L j' =? n)) i (Z.to_nat (j - i))) /\
    (forall p, (p < cb + i \/ cb + i + Z.of_nat k <= p) -> zget (fst r) p = zget code p) /\
    (forall j, i <= j < i + Z.of_nat k -> L j <> n -> zget (fst r) (cb + j) = zget code (cb + j)).
  Proof.
    induction k as [|k IH]; intros code n i vec Hi; cbv zeta.
    - cbn [ha_inner fst snd sumF]. split; [lia|]. split; [intros; lia|]. split; [intros; reflexivity| intros; lia].
    - cbn [ha_inner]. fold (L i). destruct (Z.eqb_spec (L i) n) as [E|NE].
      + specialize (IH (zset code (cb + i) vec) n (i + 1) (vec + 1) ltac:(lia)). cbv zeta in IH. cps_destruct IH as (R1 & R2 & R3 & R4).
        split; [| split; [| split]].
        * rewrite R1. cbn [sumF]. fold (L i). rewrite E, Z.eqb_refl. cbn [ind]. lia.
        * intros j Hj Lj. destruct (Z.eq_dec j i) as [->|NJ].
          -- rewrite R3 by lia. rewrite zget_zset_same. replace (i - i) with 0 by lia. cbn [sumF Z.to_nat]. lia.
          -- rewrite R2 by lia. replace (Z.to_nat (j - i)) with (S (Z.to_nat (j - (i + 1)))) by lia. cbn [sumF]. fold (L i).
             rewrite E, Z.eqb_refl. cbn [ind]. replace (i + 1) with (i + 1) by lia. lia.
        * intros p Hp. rewrite R3 by lia. apply zget_zset_other. lia.
        * intros j Hj Lj. destruct (Z.eq_dec j i) as [->|NJ]; [congruence|]. rewrite R4 by lia. apply zget_zset_other. lia.
      + specialize (IH code n (i + 1) vec ltac:(lia)). cbv zeta in IH. cps_destruct IH as (R1 & R2 & R3 & R4).
        split; [| split; [| split]].
        * rewrite R1. cbn [sumF]. fold (L i). replace (L i =? n) with false by (symmetry; apply Z.eqb_neq; exact NE). cbn [ind]. lia.
        * intros j Hj Lj. destruct (Z.eq_dec j i) as [->|NJ]; [congruence|].
          rewrite R2 by lia. replace (Z.to_nat (j - i)) with (S (Z.to_nat (j - (i + 1)))) by lia. cbn [sumF]. fold (L i).
          replace (L i =? n) with false by (symmetry; apply Z.eqb_neq; exact NE). cbn [ind]. lia.
        * intros p Hp. destruct (Z.eq_dec p (cb + i)) as [->|NP]; [apply R4; lia|]. apply R3. lia.
        * intros j Hj Lj. destruct (Z.eq_dec j i) as [->|NJ]; [apply R3; lia|]. apply R4; lia.
  Qed.

  Lemma ha_outer_spec : forall k code n vec, 1 <= n -> vec = fcode L A n ->
    let r := ha_outer k code len cb lb A n vec in
    snd r = fcode L A (n + Z.of_nat k) /\
    (forall i, 0 <= i < A -> n <= L i < n + Z.of_nat k -> zget (fst r) (cb + i) = ccode L A i) /\
    (forall p, (p < cb \/ cb + A <= p) -> zget (fst r) p = zget code p) /\
    (forall i, 0 <= i < A -> ~ (n <= L i < n + Z.of_nat k) -> zget (fst r) (cb + i) = zget code (cb + i)).
  Proof.
    induction k as [|k IH]; intros code n vec Hn Hv; cbv zeta.
    - cbn [ha_outer fst snd]. rewrite Z.add_0_r. split; [exact Hv|]. split; [intros; lia|]. split; [intros; reflexivity| intros; reflexivity].
    - cbn [ha_outer]. pose proof (ha_inner_spec (Z.to_nat A) code n 0 vec ltac:(lia)) as IN. cbv zeta in IN.
      destruct (ha_inner (Z.to_nat A) code len cb lb n 0 vec) as [code1 vec1]. cbn [fst snd] in IN.
      cps_destruct IN as (V1 & C1 & F1 & U1).
      assert (V1' : Z.shiftl vec1 1 = fcode L A (n + 1)).
      { rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite V1, Hv, fcode_succ, wsum_split. unfold cnt_eq, ceq. lia. }
      specialize (IH code1 (n + 1) (Z.shiftl vec1 1) ltac:(lia) V1'). cbv zeta in IH. cps_destruct IH as (R1 & R2 & R3 & R4).
      split; [rewrite R1; f_equal; lia|]. split; [| split].
      + intros i Hi Li. destruct (Z.eq_dec (L i) n) as [E|NE].
        * rewrite R4 by lia. rewrite C1 by lia. rewrite ccode_eq, E, Hv by lia. unfold ceq. rewrite Z.sub_0_r. reflexivity.
        * apply R2; lia.
      + intros p Hp. rewrite R3 by lia. apply F1. lia.
      + intros i Hi NL. rewrite R4 by lia. apply U1; lia.
  Qed.

  Theorem hbAssignCodes_spec : forall code minLen maxLen,
    1 <= minLen -> (forall i, 0 <= i < A -> minLen <= L i <= maxLen) ->
    let r := hbAssignCodes code len cb lb minLen maxLen A in
    (forall i, 0 <= i < A -> zget r (cb + i) = ccode L A i) /\
    (forall p, (p < cb \/ cb + A <= p) -> zget r p = zget code p).
  Proof.
    intros code minLen maxLen Hm HL. cbv zeta. unfold hbAssignCodes.
    pose proof (ha_outer_spec (Z.to_nat (maxLen - minLen + 1)) code minLen 0 Hm) as OU. cbv zeta in OU.
    cps_destruct OU as (_ & R2 & R3 & _).
    { symmetry. apply fcode_min. intros j Hj. pose proof (HL j Hj). lia. }
    split; [| exact R3]. intros i Hi. apply R2; [lia|]. pose proof (HL i Hi). lia.
  Qed.
End Assign.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Tables.
  Variables (len : zarr) (off A : Z).
  Hypothesis HA : 0 <= A.
  #[local] Abbreviation Ld := (Lrow len off).

  Lemma hbd_permJ_spec : forall n j i perm pp, 0 <= j -> 0 <= pp ->
    let r := hbd_permJ n j i len perm off pp in
    snd r = pp + sumF (fun j' => ind (Ld j' =? i)) j n /\
    (forall jj, j <= jj < j + Z.of_nat n -> Ld jj = i ->
       zget (fst r) (off + pp + sumF (fun j' => ind (Ld j' =? i)) j (Z.to_nat (jj - j))) = jj) /\
    (forall p, (p < off + pp \/ off + snd r <= p) -> zget (fst r) p = zget perm p).
  Proof.
    induction n as [|n IH]; intros j i perm pp Hj Hpp; cbv zeta.
    - cbn [hbd_permJ fst snd sumF]. split; [lia|]. split; [intros; lia| intros; reflexivity].
    - cbn [hbd_permJ]. fold (Ld j). destruct (Z.eqb_spec (Ld j) i) as [E|NE].
      + specialize (IH (j + 1) i (zset perm (off + pp) j) (pp + 1) ltac:(lia) ltac:(lia)). cbv zeta in IH. cps_destruct IH as (R1 & R2 & R3).
        assert (SN : forall m, 0 <= sumF (fun j' : Z => ind (Ld j' =? i)) (j + 1) m) by (intros; apply sumF_nonneg; intros; apply ind_nonneg).
        split; [| split].
        * rewrite R1. cbn [sumF]. fold (Ld j). rewrite E, Z.eqb_refl. cbn [ind]. lia.
        * intros jj Hjj Ljj. destruct (Z.eq_dec jj j) as [->|NJ].
          -- replace (Z.to_nat (j - j)) with 0%nat by lia. cbn [sumF]. rewrite Z.add_0_r. rewrite R3; [apply zget_zset_same|].
             left. lia.
          -- replace (Z.to_nat (jj - j)) with (S (Z.to_nat (jj - (j + 1)))) by lia. cbn [sumF]. fold (Ld j). rewrite E, Z.eqb_refl. cbn [ind].
             replace (off + pp + (1 + sumF (fun j' : Z => ind (Ld j' =? i)) (j + 1) (Z.to_nat (jj - (j + 1))))) with
               (off + (pp + 1) + sumF (fun j' : Z => ind (Ld j' =? i)) (j + 1) (Z.to_nat (jj - (j + 1)))) by lia.
             apply R2; lia.
        * intros p Hp. rewrite R1 in Hp. rewrite R3.
          -- apply zget_zset_other. pose proof (SN n). lia.
          -- rewrite R1. pose proof (SN n). lia.
      + specialize (IH (j + 1) i perm pp ltac:(lia) ltac:(lia)). cbv zeta in IH. cps_destruct IH as (R1 & R2 & R3).
        split; [| split].
        * rewrite R1. cbn [sumF]. fold (Ld j). replace (Ld j =? i) with false by (symmetry; apply Z.eqb_neq; exact NE). cbn [ind]. lia.
        * intros jj Hjj Ljj. destruct (Z.eq_dec jj j) as [->|NJ]; [congruence|].
          replace (Z.to_nat (jj - j)) with (S (Z.to_nat (jj - (j + 1)))) by lia. cbn [sumF]. fold (Ld j).
          replace (Ld j =? i) with false by (symmetry; apply Z.eqb_neq; exact NE). cbn [ind]. rewrite Z.add_0_l. apply R2; lia.
        * intros p Hp. apply R3. rewrite R1 in Hp |- *. cbn [sumF] in Hp. fold (Ld j) in Hp.
          replace (Ld j =? i) with false in Hp by (symmetry; apply Z.eqb_neq; exact NE). cbn [ind] in Hp. lia.
  Qed.

  Lemma hbd_permI_spec : forall n i perm pp, 1 <= i -> pp = cnt_lt Ld A i ->
    let r := hbd_permI n i len perm off pp A in
    snd r = cnt_lt Ld A (i + Z.of_nat n) /\
    (forall j, 0 <= j < A -> i <= Ld j < i + Z.of_nat n -> zget (fst r) (off + crank Ld A j) = j) /\
    (forall p, (p < off + pp \/ off + snd r <= p) -> zget (fst r) p = zget perm p).
  Proof.
    induction n as [|n IH]; intros i perm pp Hi Hpp; cbv zeta.
    - cbn [hbd_permI fst snd]. rewrite Z.add_0_r. split; [exact Hpp|]. split; [intros; lia| intros; reflexivity].
    - cbn [hbd_permI]. pose proof (hbd_permJ_spec (Z.to_nat A) 0 i perm pp ltac:(lia) ltac:(rewrite Hpp; apply cnt_lt_nonneg)) as PJ.
      cbv zeta in PJ. destruct (hbd_permJ (Z.to_nat A) 0 i len perm off pp) as [perm1 pp1]. cbn [fst snd] in PJ.
      cps_destruct PJ as (P1 & P2 & P3).
      assert (P1' : pp1 = cnt_lt Ld A (i + 1)) by (rewrite P1, Hpp, cnt_lt_succ; reflexivity).
      specialize (IH (i + 1) perm1 pp1 ltac:(lia) P1'). cbv zeta in IH. cps_destruct IH as (R1 & R2 & R3).
      split; [rewrite R1; f_equal; lia|]. split.
      + intros j Hj Lj. destruct (Z.eq_dec (Ld j) i) as [E|NE].
        * rewrite R3.
          -- replace (off + crank Ld A j) with (off + pp + sumF (fun j' => ind (Ld j' =? i)) 0 (Z.to_nat (j - 0)))
               by (rewrite crank_eq, E, <- Hpp by lia; unfold ceq; rewrite Z.sub_0_r; lia).
             apply P2; lia.
          -- left. rewrite P1', crank_eq, E by lia.
             pose proof (ceq_lt_cnt Ld A j Hj) as C1. rewrite E in C1. rewrite cnt_lt_succ. unfold cnt_eq in *. lia.
        * apply R2; lia.
      + intros p Hp. rewrite R3; [apply P3|]; rewrite ?R1, ?P1' in *.
        * destruct Hp as [Hp|Hp]; [left; exact Hp| right].
          assert (M : cnt_lt Ld A (i + 1) <= cnt_lt Ld A (i + 1 + Z.of_nat n)); [| lia].
          unfold cnt_lt. apply sumF_lef. intros b Hb. unfold ind. destruct (Z.ltb_spec (Ld b) (i + 1)), (Z.ltb_spec (Ld b) (i + 1 + Z.of_nat n)); lia.
        * destruct Hp as [Hp|Hp]; [left| right; exact Hp]. rewrite Hpp in Hp. rewrite cnt_lt_succ. pose proof (ceq_nonneg Ld (Z.to_nat A) i). unfold cnt_eq. lia.
  Qed.

  Lemma hbd_zero_spec : forall n i a,
    (forall m, i <= m < i + Z.of_nat n -> zget (hbd_zero n i a off) (off + m) = 0) /\
    (forall p, (p < off + i \/ off + i + Z.of_nat n <= p) -> zget (hbd_zero n i a off) p = zget a p).
  Proof.
    induction n as [|n IH]; intros i a; cbn [hbd_zero].
    - split; [intros; lia| intros; reflexivity].
    - destruct (IH (i + 1) (zset a (off + i) 0)) as [R1 R2]. split.
      + intros m Hm. destruct (Z.eq_dec m i) as [->|NE]; [rewrite R2 by lia; apply zget_zset_same| apply R1; lia].
      + intros p Hp. rewrite R2 by lia. apply zget_zset_other. lia.
  Qed.

  Lemma hbd_count_spec : forall n i base p, 0 <= i ->
    zget (hbd_count n i len base off) p = zget base p + sumF (fun j => ind (off + Ld j + 1 =? p)) i n.
  Proof.
    induction n as [|n IH]; intros i base p Hi; cbn [hbd_count sumF]; [lia|].
    rewrite IH by lia. rewrite zget_zincr. fold (Ld i). unfold ind at 2.
    destruct (Z.eqb_spec p (off + Ld i + 1)) as [->|NE].
    - rewrite Z.eqb_refl. lia.
    - replace (off + Ld i + 1 =? p) with false by (symmetry; apply Z.eqb_neq; lia). lia.
  Qed.

  Lemma hbd_accum_spec : forall n i base, 1 <= i ->
    let r := hbd_accum n i base off in
    (forall m, i - 1 <= m < i + Z.of_nat n -> zget r (off + m) = sumF (fun m' => zget base (off + m')) (i - 1) (Z.to_nat (m - (i - 1) + 1))) /\
    (forall p, (p < off + i \/ off + i + Z.of_nat n <= p) -> zget r p = zget base p).
  Proof.
    induction n as [|n IH]; intros i base Hi; cbv zeta; cbn [hbd_accum].
    - split; [| intros; reflexivity]. intros m Hm. replace m with (i - 1) by lia.
      replace (Z.to_nat (i - 1 - (i - 1) + 1)) with 1%nat by lia. cbn [sumF]. lia.
    - set (X := zget base (off + i) + zget base (off + i - 1)).
      specialize (IH (i + 1) (zset base (off + i) X) ltac:(lia)). cbv zeta in IH.
      destruct IH as [R1 R2]. split.
      + intros m Hm. destruct (Z.eq_dec m (i - 1)) as [->|NE].
        * rewrite R2 by lia. rewrite zget_zset_other by lia.
          replace (Z.to_nat (i - 1 - (i - 1) + 1)) with 1%nat by lia. cbn [sumF]. lia.
        * rewrite R1 by lia. replace (i + 1 - 1) with i by lia.
          replace (Z.to_nat (m - i + 1)) with (S (Z.to_nat (m - i))) by lia.
          replace (Z.to_nat (m - (i - 1) + 1)) with (S (S (Z.to_nat (m - i)))) by lia.
          cbn [sumF]. rewrite zget_zset_same. replace (i - 1 + 1) with i by lia.
          rewrite (sumF_ext (Z.to_nat (m - i)) (fun m' => zget (zset base (off + i) X) (off + m')) (fun m' => zget base (off + m')) (i + 1))
            by (intros b Hb; apply zget_zset_other; lia).
          subst X. replace (off + i - 1) with (off + (i - 1)) by lia. lia.
      + intros p Hp. rewrite R2 by lia. apply zget_zset_other. lia.
  Qed.

  Lemma hbd_limit_spec : forall n i base limit vec, 1 <= i ->
    (forall m, i <= m <= i + Z.of_nat n -> zget base (off + m) = cnt_lt Ld A m) -> vec = fcode Ld A i ->
    let r := hbd_limit n i base limit off vec in
    snd r = fcode Ld A (i + Z.of_nat n) /\
    (forall m, i <= m < i + Z.of_nat n -> zget (fst r) (off + m) = wsum Ld A m - 1) /\
    (forall p, (p < off + i \/ off + i + Z.of_nat n <= p) -> zget (fst r) p = zget limit p).
  Proof.
    induction n as [|n IH]; intros i base limit vec Hi HB HV; cbv zeta; cbn [hbd_limit].
    - cbn [fst snd]. rewrite Z.add_0_r. split; [exact HV|]. split; [intros; lia| intros; reflexivity].
    - set (vec1 := vec + (zget base (off + i + 1) - zget base (off + i))).
      assert (V1 : vec1 = wsum Ld A i).
      { subst vec1. replace (off + i + 1) with (off + (i + 1)) by lia. rewrite !HB by lia. rewrite cnt_lt_succ, HV, wsum_split. lia. }
      specialize (IH (i + 1) base (zset limit (off + i) (vec1 - 1)) (2 * vec1) ltac:(lia) ltac:(intros; apply HB; lia) ltac:(rewrite V1, fcode_succ; reflexivity)).
      cbv zeta in IH. cps_destruct IH as (R1 & R2 & R3).
      split; [rewrite R1; f_equal; lia|]. split.
      + intros m Hm. destruct (Z.eq_dec m i) as [->|NE]; [rewrite R3 by lia; rewrite zget_zset_same; lia| apply R2; lia].
      + intros p Hp. rewrite R3 by lia. apply zget_zset_other. lia.
  Qed.

  Lemma hbd_base_spec : forall n i limit base, 1 <= i ->
    let r := hbd_base n i limit base off in
    (forall m, i <= m < i + Z.of_nat n -> zget r (off + m) = 2 * (zget limit (off + m - 1) + 1) - zget base (off + m)) /\
    (forall p, (p < off + i \/ off + i + Z.of_nat n <= p) -> zget r p = zget base p).
  Proof.
    induction n as [|n IH]; intros i limit base Hi; cbv zeta; cbn [hbd_base].
    - split; [intros; lia| intros; reflexivity].
    - specialize (IH (i + 1) limit (zset base (off + i) (2 * (zget limit (off + i - 1) + 1) - zget base (off + i))) ltac:(lia)).
      cbv zeta in IH. destruct IH as [R1 R2]. split.
      + intros m Hm. destruct (Z.eq_dec m i) as [->|NE]; [rewrite R2 by lia; apply zget_zset_same|].
        rewrite R1 by lia. rewrite zget_zset_other by lia. reflexivity.
      + intros p Hp. rewrite R2 by lia. apply zget_zset_other. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem hbCreateDecodeTables_spec : forall limit base perm minLen maxLen,
    1 <= minLen -> maxLen <= 21 -> (forall j, 0 <= j < A -> minLen <= Ld j <= maxLen) ->
    let '(li, ba, pe) := hbCreateDecodeTables limit base perm len off minLen maxLen A in
    (forall n, minLen <= n <= maxLen -> zget li (off + n) = wsum Ld A n - 1) /\
    (forall n, minLen <= n <= maxLen -> zget ba (off + n) = fcode Ld A n - cnt_lt Ld A n) /\
    (forall j, 0 <= j < A -> zget pe (off + crank Ld A j) = j) /\
    (forall p, (p < off \/ off + 23 <= p) -> zget li p = zget limit p) /\
    (forall p, (p < off \/ off + 23 <= p) -> zget ba p = zget base p) /\
    (forall p, (p < off \/ off + A <= p) -> zget pe p = zget perm p).
  Proof.
    intros limit base perm minLen maxLen Hmin Hmax HL. unfold hbCreateDecodeTables.
    (* [comment removed for export] *)
    pose proof (hbd_permI_spec (zspan minLen maxLen) minLen perm 0 Hmin) as PI. cbv zeta in PI.
    destruct (hbd_permI (zspan minLen maxLen) minLen len perm off 0 A) as [perm1 ppf]. cbn [fst snd] in PI.
    cps_destruct PI as (PP & P1 & P2); [symmetry; apply cnt_lt_min; intros j Hj; pose proof (HL j Hj); lia|].
    (* [comment removed for export] *)
    destruct (hbd_zero_spec (Z.to_nat BZ_MAX_CODE_LEN) 0 base) as [Z1 Z2].
    set (base1 := hbd_zero (Z.to_nat BZ_MAX_CODE_LEN) 0 base off) in *.
    pose proof (fun p => hbd_count_spec (Z.to_nat A) 0 base1 p ltac:(lia)) as CNT.
    set (base2 := hbd_count (Z.to_nat A) 0 len base1 off) in *.
    pose proof (hbd_accum_spec (Z.to_nat (BZ_MAX_CODE_LEN - 1)) 1 base2 ltac:(lia)) as AC. cbv zeta in AC. destruct AC as [A1 A2].
    set (base3 := hbd_accum (Z.to_nat (BZ_MAX_CODE_LEN - 1)) 1 base2 off) in *.
    assert (B3 : forall m, 0 <= m <= 22 -> zget base3 (off + m) = cnt_lt Ld A m).
    { intros m Hm. rewrite A1 by (unfold BZ_MAX_CODE_LEN; lia). replace (1 - 1) with 0 by lia.
      replace (Z.to_nat (m - 0 + 1)) with (S (Z.to_nat m)) by lia.
      transitivity (sumF (fun m' => sumF (fun j => ind (off + Ld j + 1 =? off + m')) 0 (Z.to_nat A)) 0 (S (Z.to_nat m))).
      { apply sumF_ext. intros b Hb. rewrite CNT, Z1 by (unfold BZ_MAX_CODE_LEN; lia). lia. }
      rewrite (sumF_swap (S (Z.to_nat m)) (Z.to_nat A) (fun m' j => ind (off + Ld j + 1 =? off + m')) 0 0).
      unfold cnt_lt. apply sumF_ext. intros j Hj. cbn beta.
      rewrite (sumF_ext (S (Z.to_nat m)) _ (fun b => ind (Ld j + 1 =? b))).
      2:{ intros b Hb. unfold ind. destruct (Z.eqb_spec (off + Ld j + 1) (off + b)), (Z.eqb_spec (Ld j + 1) b); lia. }
      rewrite sumF_indic. pose proof (HL j ltac:(lia)). unfold ind.
      destruct (Z.leb_spec 0 (Ld j + 1)), (Z.ltb_spec (Ld j + 1) (0 + Z.of_nat (S (Z.to_nat m)))), (Z.ltb_spec (Ld j) m); cbn; lia. }
    (* [comment removed for export] *)
    destruct (hbd_zero_spec (Z.to_nat BZ_MAX_CODE_LEN) 0 limit) as [Y1 Y2].
    set (limit1 := hbd_zero (Z.to_nat BZ_MAX_CODE_LEN) 0 limit off) in *.
    destruct (Z.le_gt_cases minLen maxLen) as [LE|GT].
    - pose proof (hbd_limit_spec (zspan minLen maxLen) minLen base3 limit1 0 Hmin) as LI. cbv zeta in LI.
      destruct (hbd_limit (zspan minLen maxLen) minLen base3 limit1 off 0) as [limit2 vecf]. cbn [fst snd] in LI.
      cps_destruct LI as (V2 & L1 & L2).
      { intros m Hm. apply B3. unfold zspan in Hm. lia. }
      { symmetry. apply fcode_min. intros j Hj. pose proof (HL j Hj). lia. }
      pose proof (hbd_base_spec (zspan (minLen + 1) maxLen) (minLen + 1) limit2 base3 ltac:(lia)) as BA. cbv zeta in BA. destruct BA as [BA1 BA2].
      split; [| split; [| split; [| split; [| split]]]].
      + intros n Hn. apply L1. unfold zspan. lia.
      + intros n Hn. destruct (Z.eq_dec n minLen) as [->|NE].
        * rewrite BA2 by lia. rewrite B3 by lia. rewrite fcode_min, cnt_lt_min. 1: lia. all: intros j Hj; pose proof (HL j Hj); lia.
        * rewrite BA1 by (unfold zspan; lia). replace (off + n - 1) with (off + (n - 1)) by lia.
          rewrite L1 by (unfold zspan; lia). rewrite B3 by lia.
          pose proof (fcode_succ Ld A (n - 1)) as F. replace (n - 1 + 1) with n in F by lia. lia.
      + intros j Hj. apply P1; [exact Hj|]. unfold zspan. pose proof (HL j Hj). lia.
      + intros p Hp. rewrite L2 by (unfold zspan; lia). apply Y2. unfold BZ_MAX_CODE_LEN. lia.
      + intros p Hp. rewrite BA2 by (unfold zspan; lia). rewrite A2 by (unfold BZ_MAX_CODE_LEN; lia).
        rewrite CNT. rewrite Z2 by (unfold BZ_MAX_CODE_LEN; lia). rewrite sumF_zero; [lia|].
        intros b Hb. pose proof (HL b ltac:(lia)). unfold ind. destruct (Z.eqb_spec (off + Ld b + 1) p); lia.
      + intros p Hp. apply P2. rewrite PP.
        assert (cnt_lt Ld A (minLen + Z.of_nat (zspan minLen maxLen)) <= A); [| lia].
        unfold cnt_lt. replace A with (Z.of_nat (Z.to_nat A)) at 2 by lia.
        generalize (Z.to_nat A) as m. induction m as [|m IH]; [cbn; lia|]. rewrite sumF_S_r. pose proof (ind_nonneg (Ld (0 + Z.of_nat m) <? minLen + Z.of_nat (zspan minLen maxLen))). lia.
    - (* [comment removed for export] *)
      replace (zspan minLen maxLen) with 0%nat by (unfold zspan; lia). replace (zspan (minLen + 1) maxLen) with 0%nat by (unfold zspan; lia).
      cbn [hbd_limit hbd_base].
      split; [intros; lia|]. split; [intros; lia|]. split; [| split; [| split]].
      + intros j Hj. pose proof (HL j Hj). lia.
      + intros p Hp. apply Y2. unfold BZ_MAX_CODE_LEN. lia.
      + intros p Hp. rewrite A2 by (unfold BZ_MAX_CODE_LEN; lia). rewrite CNT. rewrite Z2 by (unfold BZ_MAX_CODE_LEN; lia).
        rewrite sumF_zero; [lia|]. intros b Hb. pose proof (HL b ltac:(lia)). lia.
      + intros p Hp. apply P2. rewrite PP. replace (zspan minLen maxLen) with 0%nat in * by (unfold zspan; lia).
        rewrite Z.add_0_r. rewrite cnt_lt_min; [lia|]. intros j Hj. pose proof (HL j Hj). lia.
  Qed.
End Tables.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem drun_take2 : forall lbl L d s,
  let n := gb_bits lbl L in
  rd_ok d s -> 1 <= n <= 24 -> n <= b_len (rd_abs d s) ->
  exists (k : nat) (v : Z) (d1 : dst) (s1 : dstrm),
    (k <= 3)%nat /\ (k <= length (s_in s))%nat /\
    (forall f', drun (S k + f') lbl L d s = dgo f' (gb_after lbl v L d1 s1)) /\
    v = btake n (rd_abs d s) /\ rd_abs d1 s1 = bdrop n (rd_abs d s) /\ rd_ok d1 s1 /\ 0 <= v < 2 ^ n /\
    same_but_bits lbl d d1 /\ consumed_from k s s1.
Proof.
  intros lbl L d s n R Hn Hlen.
  assert (GEN : forall j (d0 : dst) (s0 : dstrm) k0,
            rd_ok d0 s0 -> rd_abs d0 s0 = rd_abs d s -> n <= d_bsLive d0 + 8 * Z.of_nat j ->
            same_but_bits lbl d d0 -> consumed_from k0 s s0 -> (k0 + j <= 3)%nat -> (k0 <= length (s_in s))%nat ->
            exists k v d1 s1, (k <= 3)%nat /\ (k <= length (s_in s))%nat /\
              (forall f', drun (S (k - k0) + f') lbl L d0 s0 = dgo f' (gb_after lbl v L d1 s1)) /\ (k0 <= k)%nat /\
              v = btake n (rd_abs d s) /\ rd_abs d1 s1 = bdrop n (rd_abs d s) /\ rd_ok d1 s1 /\ 0 <= v < 2 ^ n /\
              same_but_bits lbl d d1 /\ consumed_from k s s1).
  { induction j as [|j IH]; intros d0 s0 k0 R0 E0 Hj SB CF Hk HkL.
    - cbn [Z.of_nat] in Hj.
      pose proof (rd_extract_abs n d0 s0 R0 ltac:(lia)) as X. unfold rd_extract in X.
      cps_destruct X as (V & AB & R1 & VR).
      exists k0, (Z.land (Z.shiftr (d_bsBuff d0) (d_bsLive d0 - n)) (Z.shiftl 1 n - 1)), (d_set_bsLive (d_set_state d0 lbl) (d_bsLive d0 - n)), s0.
      split; [lia|]. split; [exact HkL|]. split.
      { intros f'. replace (S (k0 - k0) + f')%nat with (S f') by lia. rewrite drun_extract1 by lia.
        unfold rd_extract. reflexivity. }
      split; [lia|]. rewrite <- E0. split; [exact V|]. split; [exact AB|]. split; [exact R1|]. split; [exact VR|].
      split; [| exact CF]. unfold same_but_bits in *. rewrite SB. reflexivity.
    - destruct (Z.leb_spec n (d_bsLive d0)) as [Hle|Hlt].
      + apply (IH d0 s0 k0); try assumption; try lia.
      + assert (NE : s_in s0 <> []).
        { intros Hemp. pose proof (f_equal b_len E0) as LEN. unfold rd_abs in LEN; cbn [b_len] in LEN.
          rewrite Hemp in LEN. cbn [length] in LEN. change (Z.of_nat 0) with 0 in LEN.
          unfold rd_abs in Hlen; cbn [b_len] in Hlen. lia. }
        destruct (s_in s0) as [|b rest] eqn:Hs0; [exfalso; apply NE; reflexivity|].
        assert (HkL1 : (S k0 <= length (s_in s))%nat).
        { unfold consumed_from in CF. rewrite CF in Hs0. cbn [s_in s_set_tin s_set_in] in Hs0.
          destruct (Nat.le_gt_cases (length (s_in s)) k0) as [LE|GT]; [|lia].
          rewrite skipn_all2 in Hs0 by exact LE. discriminate. }
        pose proof (rd_pull_abs d0 s0 b rest R0 Hs0 ltac:(lia)) as X.
        unfold rd_pull in X. rewrite Hs0 in X.
        cps_destruct X as (AB1 & R1 & L1 & IN1).
        cps_destruct (IH (d_set_bsLive (d_set_bsBuff d0 (u32 (Z.lor (Z.shiftl (d_bsBuff d0) 8) b))) (d_bsLive d0 + 8))
                     (s_set_tin (s_set_in s0 rest) (s_tin s0 + 1)) (S k0)) as (k & v & d1 & s1 & K3 & KL & RUN & K0 & REST);
          try assumption; try (cbn [d_bsLive d_set_bsLive d_set_bsBuff] in *; lia).
        * rewrite AB1. exact E0.
        * unfold same_but_bits in *. rewrite SB. reflexivity.
        * unfold consumed_from in *. rewrite CF in Hs0 |- *. destruct s as [si so sa sti sto].
          unfold s_set_tin, s_set_in in *. cbn [s_in s_tin s_out s_avail_out s_tout] in *.
          f_equal; [| lia].
          replace (S k0) with (1 + k0)%nat by lia. rewrite <- skipn_skipn, Hs0. reflexivity.
        * exists k, v, d1, s1. split; [exact K3|]. split; [exact KL|]. split; [| split; [lia| exact REST]].
          intros f'. replace (S (k - k0) + f')%nat with (S (S (k - S k0) + f'))%nat by lia.
          rewrite (drun_pull1 _ lbl L d0 s0 b rest Hs0) by lia. unfold rd_pull. rewrite Hs0.
          rewrite (sbb_state _ _ _ SB). exact (RUN f'). }
  cps_destruct (GEN 3%nat (d_set_state d lbl) s 0%nat (rd_ok_state _ _ _ R) (rd_abs_state _ _ _)) as (k & v & d1 & s1 & K3 & KL & RUN & _ & REST).
  - change (Z.of_nat 3) with 3. change (d_bsLive (d_set_state d lbl)) with (d_bsLive d). destruct R as (R1 & _). lia.
  - unfold same_but_bits. destruct d; reflexivity.
  - unfold consumed_from. cbn [skipn]. rewrite Z.add_0_r. destruct s; reflexivity.
  - lia.
  - lia.
  - exists k, v, d1, s1. rewrite Nat.sub_0_r in RUN. split; [exact K3|]. split; [exact KL|]. split; [| exact REST].
    intros f'. rewrite <- (RUN f'). destruct k; reflexivity.
Qed.

(* [comment removed for export] *)
Definition dcost (d : dst) (s : dstrm) (d1 : dst) (s1 : dstrm) : Z :=
  (b_len (rd_abs d s) - b_len (rd_abs d1 s1)) + (Z.of_nat (length (s_in s)) - Z.of_nat (length (s_in s1))).

Lemma dcost_trans : forall d s d1 s1 d2 s2, dcost d s d2 s2 = dcost d s d1 s1 + dcost d1 s1 d2 s2.
Proof. intros. unfold dcost. lia. Qed.
Lemma dcost_refl : forall d s, dcost d s d s = 0.
Proof. intros. unfold dcost. lia. Qed.

Lemma consumed_from_len : forall k s s1, consumed_from k s s1 -> (k <= length (s_in s))%nat ->
  Z.of_nat (length (s_in s1)) = Z.of_nat (length (s_in s)) - Z.of_nat k.
Proof.
  intros k s s1 CF Hk. unfold consumed_from in CF. rewrite CF. cbn [s_in s_set_tin s_set_in]. rewrite length_skipn. lia.
Qed.
Lemma consumed_from_trans : forall k1 k2 s s1 s2, consumed_from k1 s s1 -> consumed_from k2 s1 s2 -> consumed_from (k1 + k2) s s2.
Proof.
  intros k1 k2 s s1 s2 C1 C2. unfold consumed_from in *. rewrite C2, C1. destruct s as [si so sa sti sto].
  cbn [s_in s_tin s_set_tin s_set_in s_out s_avail_out s_tout]. unfold s_set_tin, s_set_in. cbn.
  rewrite skipn_skipn. f_equal; [f_equal; lia| lia].
Qed.
Lemma consumed_from_0 : forall s, consumed_from 0 s s.
Proof. intros s. unfold consumed_from. cbn [skipn]. rewrite Z.add_0_r. destruct s; reflexivity. Qed.
Lemma same_but_bits_trans : forall l1 l2 d d1 d2, same_but_bits l1 d d1 -> same_but_bits l2 d1 d2 -> same_but_bits l2 d d2.
Proof. intros l1 l2 d d1 d2 A1 A2. unfold same_but_bits in *. rewrite A2, A1. destruct d; reflexivity. Qed.

(* [comment removed for export] *)
Lemma drun_take2_cost : forall lbl L d s k d1 s1,
  let n := gb_bits lbl L in 1 <= n ->
  (k <= length (s_in s))%nat -> rd_abs d1 s1 = bdrop n (rd_abs d s) -> consumed_from k s s1 ->
  Z.of_nat (S k) <= dcost d s d1 s1.
Proof.
  intros lbl L d s k d1 s1 n Hn Hk AB CF. unfold dcost. rewrite (consumed_from_len k s s1 CF Hk).
  pose proof (f_equal b_len AB) as E. unfold bdrop in E; cbn [b_len] in E. rewrite E. lia.
Qed.

(* [comment removed for export] *)
Definition mtf_fin (which : Z) (L : dsv) (lval : Z) (d : dst) (s : dstrm) : dres :=
  let L1 := sv_set_nextSym L lval in
  if which =? 3 then (if (lval =? BZ_RUNA) || (lval =? BZ_RUNB) then run_body L1 d s else run_exit L1 d s)
  else sym_dispatch L1 d s.

Lemma gb_after_mtf1 : forall which v L d s, (which = 1 \/ which = 3 \/ which = 5) ->
  gb_after (which + 35) v L d s = mtf_val_loop which (sv_set_zvec L v) d s /\ gb_bits (which + 35) L = sv_zn L.
Proof. intros which v L d s [-> |[-> | ->]]; split; reflexivity. Qed.
Lemma gb_after_mtf2 : forall which v L d s, (which = 1 \/ which = 3 \/ which = 5) ->
  gb_after (which + 36) v L d s = mtf_val_loop which (sv_set_zvec (sv_set_zj L v) (Z.lor (Z.shiftl (sv_zvec L) 1) v)) d s /\
  gb_bits (which + 36) L = 1.
Proof. intros which v L d s [-> |[-> | ->]]; split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma zvec_step : forall c r, 0 <= c -> 1 <= r ->
  Z.lor (Z.shiftl (c / 2 ^ r) 1) ((c mod 2 ^ r) / 2 ^ (r - 1)) = c / 2 ^ (r - 1).
Proof.
  intros c r Hc Hr.
  pose proof (pow2_pos (r - 1) ltac:(lia)) as P1.
  assert (E2 : 2 ^ r = 2 * 2 ^ (r - 1)) by (replace r with (Z.succ (r - 1)) at 1 by lia; rewrite Z.pow_succ_r; lia).
  pose proof (Z.div_mod c (2 ^ r) ltac:(lia)) as DM. pose proof (Z.mod_pos_bound c (2 ^ r) ltac:(lia)) as MB.
  set (q := c / 2 ^ r) in *. set (m := c mod 2 ^ r) in *.
  assert (Hq : 0 <= q) by (subst q; apply Z.div_pos; lia).
  assert (Hb : 0 <= m / 2 ^ (r - 1) < 2).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  rewrite (lor_disjoint (q * 2) (m / 2 ^ (r - 1)) 1); try lia.
  2:{ change (2 ^ 1) with 2. apply Z.mod_mul. lia. }
  rewrite DM. rewrite E2. replace (2 * 2 ^ (r - 1) * q + m) with (m + (q * 2) * 2 ^ (r - 1)) by lia.
  rewrite Z_div_plus by lia. lia.
Qed.

Section Decode.
  Variables (Lf : Z -> Z) (A minLen maxLen gSel : Z) (limit base perm : zarr).
  Hypothesis HA : 0 <= A <= 258.
  Hypothesis Hmin : 1 <= minLen.
  Hypothesis Hmax : maxLen <= 20.
  Hypothesis HL : forall j, 0 <= j < A -> minLen <= Lf j <= maxLen.
  Hypothesis KR : forall n, 1 <= n -> wsum Lf A n <= 2 ^ n.
  Hypothesis TL : forall n, minLen <= n <= maxLen -> zget limit (258 * gSel + n) = wsum Lf A n - 1.
  Hypothesis TB : forall n, minLen <= n <= maxLen -> zget base (258 * gSel + n) = fcode Lf A n - cnt_lt Lf A n.
  Hypothesis TP : forall j, 0 <= j < A -> zget perm (258 * gSel + crank Lf A j) = j.

  (* [comment removed for export] *)
  Definition lfin (L : dsv) (i : Z) : dsv :=
    if sv_zn L <? Lf i then sv_set_zvec (sv_set_zj (sv_set_zn L (Lf i)) (ccode Lf A i mod 2)) (ccode Lf A i) else L.

  Lemma mvl_step : forall which L d s i, 0 <= i < A -> sv_gSel L = gSel ->
    d_limit d = limit -> d_base d = base -> d_perm d = perm ->
    minLen <= sv_zn L <= Lf i -> sv_zvec L = ccode Lf A i / 2 ^ (Lf i - sv_zn L) ->
    mtf_val_loop which L d s =
      (if sv_zn L =? Lf i then mtf_fin which L i d s else DGo (which + 36) (sv_set_zn L (sv_zn L + 1)) d s).
  Proof.
    intros which L d s i Hi HG HLi HBa HPe Hzn Hzv. pose proof (HL i Hi) as HLi'.
    unfold mtf_val_loop. rewrite HG, HLi, HBa, HPe, Hzv.
    replace (20 <? sv_zn L) with false by (symmetry; apply Z.ltb_ge; lia).
    pose proof (ccode_range Lf A i Hi) as CR. pose proof (crank_range Lf A i Hi) as KR'.
    destruct (Z.eqb_spec (sv_zn L) (Lf i)) as [E|NE].
    - rewrite E, Z.sub_diag. change (2 ^ 0) with 1. rewrite Z.div_1_r.
      rewrite TL by lia. replace (ccode Lf A i <=? wsum Lf A (Lf i) - 1) with true by (symmetry; apply Z.leb_le; lia).
      rewrite TB by lia.
      replace (ccode Lf A i - (fcode Lf A (Lf i) - cnt_lt Lf A (Lf i))) with (crank Lf A i) by (rewrite ccode_eq, crank_eq by lia; lia).
      replace ((crank Lf A i <? 0) || (BZ_MAX_ALPHA_SIZE <=? crank Lf A i))%bool with false.
      2:{ symmetry. apply Bool.orb_false_iff. unfold BZ_MAX_ALPHA_SIZE. split; [apply Z.ltb_ge| apply Z.leb_gt]; lia. }
      rewrite TP by lia. unfold mtf_fin. reflexivity.
    - rewrite TL by lia.
      replace (ccode Lf A i / 2 ^ (Lf i - sv_zn L) <=? wsum Lf A (sv_zn L) - 1) with false; [reflexivity|].
      symmetry. apply Z.leb_gt. pose proof (ccode_prefix Lf A i (sv_zn L) Hi ltac:(lia)). lia.
  Qed.

  Lemma mvl_loop : forall m which L d s rest i,
    (which = 1 \/ which = 3 \/ which = 5) -> 0 <= i < A -> sv_gSel L = gSel ->
    d_limit d = limit -> d_base d = base -> d_perm d = perm ->
    minLen <= sv_zn L <= Lf i -> (Z.to_nat (Lf i - sv_zn L) <= m)%nat ->
    sv_zvec L = ccode Lf A i / 2 ^ (Lf i - sv_zn L) ->
    rd_ok d s -> bits_ok rest ->
    rd_abs d s = bapp (Bits (Lf i - sv_zn L) (ccode Lf A i mod 2 ^ (Lf i - sv_zn L))) rest ->
    exists k d1 s1,
      (forall f, dgo (k + f) (mtf_val_loop which L d s) = dgo f (mtf_fin which (lfin L i) i d1 s1)) /\
      rd_abs d1 s1 = rest /\ rd_ok d1 s1 /\ Z.of_nat k <= dcost d s d1 s1 /\
      (sv_zn L = Lf i -> d1 = d /\ s1 = s) /\
      (sv_zn L < Lf i -> same_but_bits (which + 36) d d1 /\ exists kb, consumed_from kb s s1).
  Proof.
    induction m as [|m IH]; intros which L d s rest i HW Hi HG HLi HBa HPe Hzn Hm Hzv RO BO AB.
    - assert (E : sv_zn L = Lf i) by lia.
      exists 0%nat, d, s. split.
      { intros f. rewrite (mvl_step which L d s i) by assumption. rewrite E, Z.eqb_refl. unfold lfin. rewrite E, Z.ltb_irrefl. reflexivity. }
      rewrite E, Z.sub_diag in AB. change (2 ^ 0) with 1 in AB. rewrite Z.mod_1_r in AB.
      rewrite AB. split; [apply bapp_bnil_l|]. split; [exact RO|]. split; [rewrite dcost_refl; lia|].
      split; [intros _; split; reflexivity| intros; lia].
    - destruct (Z.eq_dec (sv_zn L) (Lf i)) as [E|NE]; [apply (IH which L d s rest i); try assumption; lia|].
      pose proof (ccode_range Lf A i Hi) as CR.
      set (c := ccode Lf A i) in *. set (r := Lf i - sv_zn L) in *.
      assert (Hr : 1 <= r) by lia.
      pose proof (pow2_pos r ltac:(lia)) as Pr. pose proof (pow2_pos (r - 1) ltac:(lia)) as Pr1.
      pose proof (Z.mod_pos_bound c (2 ^ r) Pr) as MB.
      assert (OKx : bits_ok (Bits r (c mod 2 ^ r))) by (unfold bits_ok; cbn [b_len b_val]; lia).
      set (L2 := sv_set_zn L (sv_zn L + 1)).
      destruct (gb_after_mtf2 which 0 L2 d s HW) as [_ GB2].
      cps_destruct (drun_take2 (which + 36) L2 d s RO) as (k1 & v & d' & s' & K3 & KL & RUN & V & AB' & RO' & VR & SB & CF).
      { rewrite GB2. lia. }
      { rewrite GB2, AB. destruct BO as [BO1 BO2]. cbn [b_len bapp]. lia. }
      rewrite GB2 in V, AB', VR.
      rewrite AB, (btake_bapp_l 1 _ rest OKx BO) in V by (cbn [b_len]; lia). unfold btake in V. cbn [b_val b_len] in V.
      rewrite AB, (bdrop_bapp_l 1 _ rest OKx BO) in AB' by (cbn [b_len]; lia). unfold bdrop in AB'. cbn [b_val b_len] in AB'.
      rewrite (mod_pow2_mod_pow2 c (r - 1) r) in AB' by lia.
      destruct (gb_after_mtf2 which v L2 d' s' HW) as [GA2 _].
      set (L3 := sv_set_zvec (sv_set_zj L2 v) (Z.lor (Z.shiftl (sv_zvec L2) 1) v)) in GA2.
      assert (ZV3 : sv_zvec L3 = c / 2 ^ (r - 1)).
      { subst L3 L2. cbn [sv_zvec sv_set_zvec sv_set_zj sv_set_zn]. rewrite Hzv, V. apply zvec_step; lia. }
      assert (ZN3 : sv_zn L3 = sv_zn L + 1) by reflexivity.
      assert (TAB : d_limit d' = limit /\ d_base d' = base /\ d_perm d' = perm).
      { rewrite SB. cbn [d_limit d_base d_perm d_set_bsLive d_set_bsBuff d_set_state]. repeat split; assumption. }
      cps_destruct TAB as (HLi' & HBa' & HPe').
      cps_destruct (IH which L3 d' s' rest i HW Hi ltac:(exact HG) HLi' HBa' HPe' ltac:(rewrite ZN3; lia) ltac:(rewrite ZN3; lia)
                   ltac:(rewrite ZV3, ZN3; f_equal; f_equal; lia) RO' BO
                   ltac:(rewrite AB', ZN3; f_equal; f_equal; [lia|]; f_equal; f_equal; lia))
        as (k2 & d1 & s1 & RUN2 & AB2 & RO2 & CO2 & FZ & FNZ).
      exists (S k1 + k2)%nat, d1, s1.
      split; [| split; [exact AB2| split; [exact RO2| split; [| split; [intros; lia|]]]]].
      + intros f. rewrite (mvl_step which L d s i) by assumption.
        replace (sv_zn L =? Lf i) with false by (symmetry; apply Z.eqb_neq; exact NE). fold L2.
        cbn [dgo]. replace (S k1 + k2 + f)%nat with (S k1 + (k2 + f))%nat by lia. rewrite RUN, GA2, RUN2.
        f_equal. unfold lfin. rewrite ZN3.
        replace (sv_zn L <? Lf i) with true by (symmetry; apply Z.ltb_lt; lia).
        destruct (Z.ltb_spec (sv_zn L + 1) (Lf i)) as [LT|GE].
        * subst L3 L2. destruct L; reflexivity.
        * assert (R1 : r = 1) by lia.
          assert (Vb : v = c mod 2).
          { rewrite V, R1. change (2 ^ (1 - 1)) with 1. rewrite Z.div_1_r. reflexivity. }
          assert (Zc : Z.lor (Z.shiftl (sv_zvec L2) 1) v = c).
          { change (Z.lor (Z.shiftl (sv_zvec L2) 1) v) with (sv_zvec L3). rewrite ZV3, R1. change (2 ^ (1 - 1)) with 1. apply Z.div_1_r. }
          subst L3. rewrite Zc, Vb. subst L2. replace (sv_zn L + 1) with (Lf i) by lia. reflexivity.
      + rewrite (dcost_trans d s d' s' d1 s1).
        pose proof (drun_take2_cost (which + 36) L2 d s k1 d' s' ltac:(rewrite GB2; lia) KL ltac:(rewrite GB2; rewrite AB, (bdrop_bapp_l 1 _ rest OKx BO) by (cbn [b_len]; lia); unfold bdrop; cbn [b_val b_len]; rewrite (mod_pow2_mod_pow2 c (r - 1) r) by lia; exact AB') CF).
        lia.
      + intros _. split.
        * destruct (Z.eq_dec (sv_zn L + 1) (Lf i)) as [E1|NE1].
          -- destruct (FZ ltac:(rewrite ZN3; exact E1)) as [-> ->]. exact SB.
          -- destruct (FNZ ltac:(rewrite ZN3; lia)) as [SB2 _]. eapply same_but_bits_trans; [exact SB| exact SB2].
        * destruct (Z.eq_dec (sv_zn L + 1) (Lf i)) as [E1|NE1].
          -- destruct (FZ ltac:(rewrite ZN3; exact E1)) as [-> ->]. exists k1. exact CF.
          -- destruct (FNZ ltac:(rewrite ZN3; lia)) as [_ [kb CF2]]. exists (k1 + kb)%nat. eapply consumed_from_trans; [exact CF| exact CF2].
  Qed.

  (* [comment removed for export] *)
  Definition ldone (L : dsv) (i : Z) : dsv :=
    if minLen <? Lf i then sv_set_zvec (sv_set_zj (sv_set_zn L (Lf i)) (ccode Lf A i mod 2)) (ccode Lf A i)
    else sv_set_zvec L (ccode Lf A i).

  (* [comment removed for export] *)
  Theorem huff_decode : forall which L d s rest i,
    (which = 1 \/ which = 3 \/ which = 5) -> 0 <= i < A -> sv_gSel L = gSel ->
    d_limit d = limit -> d_base d = base -> d_perm d = perm ->
    sv_zn L = minLen -> rd_ok d s -> bits_ok rest ->
    rd_abs d s = bapp (Bits (Lf i) (ccode Lf A i)) rest ->
    exists k d1 s1 kb,
      (forall f, drun (k + f) (which + 35) L d s = dgo f (mtf_fin which (ldone L i) i d1 s1)) /\
      rd_abs d1 s1 = rest /\ rd_ok d1 s1 /\ Z.of_nat k <= dcost d s d1 s1 /\
      same_but_bits (if minLen <? Lf i then which + 36 else which + 35) d d1 /\ consumed_from kb s s1.
  Proof.
    intros which L d s rest i HW Hi HG HLi HBa HPe HZ RO BO AB.
    pose proof (HL i Hi) as HLi'. pose proof (ccode_lt Lf A ltac:(intros j Hj; pose proof (HL j Hj); lia) KR i Hi) as CR.
    set (c := ccode Lf A i) in *.
    assert (OKx : bits_ok (Bits (Lf i) c)) by (unfold bits_ok; cbn [b_len b_val]; lia).
    destruct (gb_after_mtf1 which 0 L d s HW) as [_ GB1].
    cps_destruct (drun_take2 (which + 35) L d s RO) as (k1 & v & d' & s' & K3 & KL & RUN & V & AB' & RO' & VR & SB & CF).
    { rewrite GB1, HZ. lia. }
    { rewrite GB1, HZ, AB. destruct BO as [BO1 BO2]. cbn [b_len bapp]. lia. }
    rewrite GB1, HZ in V, AB', VR.
    rewrite AB, (btake_bapp_l minLen _ rest OKx BO) in V by (cbn [b_len]; lia). unfold btake in V. cbn [b_val b_len] in V.
    rewrite AB, (bdrop_bapp_l minLen _ rest OKx BO) in AB' by (cbn [b_len]; lia). unfold bdrop in AB'. cbn [b_val b_len] in AB'.
    destruct (gb_after_mtf1 which v L d' s' HW) as [GA1 _].
    assert (TAB : d_limit d' = limit /\ d_base d' = base /\ d_perm d' = perm).
    { rewrite SB. cbn [d_limit d_base d_perm d_set_bsLive d_set_bsBuff d_set_state]. repeat split; assumption. }
    cps_destruct TAB as (HLi2 & HBa2 & HPe2).
    cps_destruct (mvl_loop (Z.to_nat (Lf i - minLen)) which (sv_set_zvec L v) d' s' rest i HW Hi ltac:(exact HG) HLi2 HBa2 HPe2
                 ltac:(cbn [sv_zn sv_set_zvec]; lia) ltac:(cbn [sv_zn sv_set_zvec]; lia)
                 ltac:(cbn [sv_zn sv_zvec sv_set_zvec]; rewrite HZ; exact V) RO' BO
                 ltac:(cbn [sv_zn sv_set_zvec]; rewrite HZ; exact AB'))
      as (k2 & d1 & s1 & RUN2 & AB2 & RO2 & CO2 & FZ & FNZ).
    cbn [sv_zn sv_set_zvec] in FZ, FNZ. rewrite HZ in FZ, FNZ.
    assert (KB : exists kb, consumed_from kb s s1).
    { destruct (Z.eq_dec minLen (Lf i)) as [E|NE].
      - destruct (FZ E) as [_ ->]. exists k1. exact CF.
      - destruct (FNZ ltac:(lia)) as [_ [kb CF2]]. exists (k1 + kb)%nat. eapply consumed_from_trans; [exact CF| exact CF2]. }
    destruct KB as [kb KB].
    exists (S k1 + k2)%nat, d1, s1, kb.
    split; [| split; [exact AB2| split; [exact RO2| split; [| split; [| exact KB]]]]].
    - intros f. replace (S k1 + k2 + f)%nat with (S k1 + (k2 + f))%nat by lia. rewrite RUN, GA1, RUN2.
      f_equal. unfold lfin, ldone. cbn [sv_zn sv_set_zvec]. rewrite HZ. fold c.
      destruct (Z.ltb_spec minLen (Lf i)) as [LT|GE].
      + destruct L; reflexivity.
      + rewrite V. replace (Lf i - minLen) with 0 by lia. change (2 ^ 0) with 1. rewrite Z.div_1_r. reflexivity.
    - rewrite (dcost_trans d s d' s' d1 s1).
      pose proof (drun_take2_cost (which + 35) L d s k1 d' s' ltac:(rewrite GB1, HZ; lia) KL
                    ltac:(rewrite GB1, HZ; rewrite AB, (bdrop_bapp_l minLen _ rest OKx BO) by (cbn [b_len]; lia); unfold bdrop; cbn [b_val b_len]; exact AB') CF).
      lia.
    - destruct (Z.ltb_spec minLen (Lf i)) as [LT|GE].
      + destruct (FNZ LT) as [SB2 _]. eapply same_but_bits_trans; [exact SB| exact SB2].
      + destruct (FZ ltac:(lia)) as [-> _]. exact SB.
  Qed.
End Decode.
End BzR5b.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzDBlock.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cW. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzR5cW.
Module BzR5cD.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock.BzDHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDBlock OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5a OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG.BzR5b.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cW OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cW.BzR5cLB.
Import ListNotations.
Local Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rd_abs_LB : forall x y B V s, rd_abs (setLB x B V) s = rd_abs (setLB y B V) s.
Proof. intros. unfold rd_abs. rewrite !lbg_bsBuff, !lbg_bsLive. reflexivity. Qed.
Lemma rd_ok_LB : forall x y B V s, rd_ok (setLB x B V) s -> rd_ok (setLB y B V) s.
Proof. intros x y B V s. unfold rd_ok. rewrite !lbg_bsBuff, !lbg_bsLive. tauto. Qed.
Lemma dcost_LB : forall d s x y B V s1, dcost d s (setLB x B V) s1 = dcost d s (setLB y B V) s1.
Proof. intros. unfold dcost. rewrite (rd_abs_LB x y). reflexivity. Qed.
Lemma dcost_LB_l : forall x y B V s d1 s1, dcost (setLB x B V) s d1 s1 = dcost (setLB y B V) s d1 s1.
Proof. intros. unfold dcost. rewrite (rd_abs_LB x y). reflexivity. Qed.
Lemma setLB_self : forall d, setLB d (d_bsBuff d) (d_bsLive d) = d.
Proof. intros d. rewrite setLB_eq. destruct d; reflexivity. Qed.
Lemma same_but_bits_LB : forall lbl d d1, same_but_bits lbl d d1 -> d1 = setLB (d_set_state d lbl) (d_bsBuff d1) (d_bsLive d1).
Proof. intros lbl d d1 H. rewrite setLB_eq. exact H. Qed.
Lemma dres_map2_comp : forall B V s B1 V1 s1 r,
  dres_map2 (FLB B V) s (dres_map2 (FLB B1 V1) s1 r) = dres_map2 (FLB B V) s r.
Proof. intros. destruct r; cbn; unfold FLB; rewrite lbs_setLB; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint dfeed (ws : list (Z * Z)) (r : dres) : option dres :=
  match ws with
  | [] => Some r
  | (n, v) :: ws' =>
      match r with
      | DGo lbl L d s =>
          if negb (mtf_lbl lbl) && (gb_bits lbl L =? n) then dfeed ws' (gb_after lbl v L (d_set_state d lbl) s) else None
      | _ => None
      end
  end.

Lemma dfeed_app : forall ws1 ws2 r, dfeed (ws1 ++ ws2) r = match dfeed ws1 r with Some r1 => dfeed ws2 r1 | None => None end.
Proof.
  induction ws1 as [|[n v] ws1 IH]; intros ws2 r; cbn [dfeed app]; [reflexivity|].
  destruct r as [lbl L d s| | ]; try reflexivity.
  destruct (negb (mtf_lbl lbl) && (gb_bits lbl L =? n))%bool; [apply IH| reflexivity].
Qed.

Lemma dfeed_ret : forall ws rv L d s r, dfeed ws (DRet rv L d s) = Some r -> ws = [] /\ r = DRet rv L d s.
Proof. intros [|[n v] ws] rv L d s r H; cbn in H; [split; [reflexivity| congruence] | discriminate]. Qed.
Lemma dfeed_retns : forall ws rv L d s r, dfeed ws (DRetNoSave rv L d s) = Some r -> ws = [] /\ r = DRetNoSave rv L d s.
Proof. intros [|[n v] ws] rv L d s r H; cbn in H; [split; [reflexivity| congruence] | discriminate]. Qed.

Lemma dfeed_LB : forall ws lbl L d s s2 B V r, dfeed ws (DGo lbl L d s) = Some r ->
  dfeed ws (DGo lbl L (setLB d B V) s2) = Some (dres_map2 (FLB B V) s2 r).
Proof.
  induction ws as [|[n v] ws IH]; intros lbl L d s s2 B V r H.
  - cbn in H |- *. inversion H. reflexivity.
  - cbn [dfeed] in H |- *. destruct (mtf_lbl lbl) eqn:ML; cbn [negb andb] in H |- *; [discriminate|].
    destruct (gb_bits lbl L =? n); [|discriminate].
    rewrite lbs_state, (gb_after_LB lbl v L (d_set_state d lbl) s s2 B V ML).
    destruct (gb_after lbl v L (d_set_state d lbl) s) as [l1 L1 d1 s1|rv L1 d1 s1|rv L1 d1 s1]; cbn [dres_map2].
    + eapply IH. exact H.
    + apply dfeed_ret in H as [-> ->]. reflexivity.
    + apply dfeed_retns in H as [-> ->]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem drun_feed : forall ws lbl L d s rest r,
  wlegal ws -> rd_ok d s -> bits_ok rest -> rd_abs d s = bapp (wbits ws) rest ->
  dfeed ws (DGo lbl L d s) = Some r ->
  exists (k : nat) B V s1 (kb : nat),
    (forall f, drun (k + f) lbl L d s = dgo f (dres_map2 (FLB B V) s1 r)) /\
    (forall x, rd_abs (setLB x B V) s1 = rest /\ rd_ok (setLB x B V) s1 /\ Z.of_nat k <= dcost d s (setLB x B V) s1) /\
    consumed_from kb s s1.
Proof.
  induction ws as [|[n v] ws IH]; intros lbl L d s rest r W RO BO AB H.
  - cbn in H. inversion H; subst r. exists 0%nat, (d_bsBuff d), (d_bsLive d), s, 0%nat.
    cbn [wbits] in AB. rewrite bapp_bnil_l in AB.
    split; [| split; [| apply consumed_from_0]].
    + intros f. cbn [dres_map2 dgo Nat.add]. unfold FLB. rewrite setLB_self. reflexivity.
    + intros x. rewrite (rd_abs_LB x d), (dcost_LB d s x d), setLB_self. split; [exact AB|]. split; [| rewrite dcost_refl; lia].
      apply (rd_ok_LB d). rewrite setLB_self. exact RO.
  - apply Forall_cons_iff in W as [[Wn Wv] W]. cbn [fst snd] in Wn, Wv.
    cbn [dfeed] in H. destruct (mtf_lbl lbl) eqn:ML; cbn [negb andb] in H; [discriminate|].
    destruct (Z.eqb_spec (gb_bits lbl L) n) as [GB|]; [|discriminate].
    rewrite wbits_cons in AB.
    assert (OK1 : bits_ok (Bits n v)) by (unfold bits_ok; cbn; lia).
    pose proof (wbits_ok ws W) as OK2.
    rewrite (bapp_assoc (Bits n v) (wbits ws) rest) in AB by (try apply wbits_len; try assumption; exact (proj1 BO)).
    cps_destruct (drun_take2 lbl L d s RO ltac:(rewrite GB; lia) ltac:(rewrite GB, AB; cbn [bapp b_len]; pose proof (wbits_len ws W); pose proof (proj1 BO); cbn in *; lia))
      as (k1 & v' & d1 & s1 & K3 & KL & RUN & V & AB1 & RO1 & VR & SB & CF).
    rewrite GB in V, AB1, VR.
    assert (OK12 : bits_ok (bapp (wbits ws) rest)) by (apply bapp_ok; assumption).
    pose proof (btake_bapp (Bits n v) _ OK1 OK12) as BT. cbn [b_len b_val] in BT.
    pose proof (bdrop_bapp (Bits n v) _ OK1 OK12) as BD. cbn [b_len] in BD.
    rewrite AB, BT in V. subst v'.
    rewrite AB, BD in AB1.
    pose proof (same_but_bits_LB _ _ _ SB) as D1.
    pose proof (drun_take2_cost lbl L d s k1 d1 s1 ltac:(rewrite GB; lia) KL ltac:(rewrite GB, AB, BD; exact AB1) CF) as C1.
    set (B1 := d_bsBuff d1) in *. set (V1 := d_bsLive d1) in *.
    rewrite D1 in RUN, AB1, RO1, C1.
    pose proof (gb_after_LB lbl v L (d_set_state d lbl) s s1 B1 V1 ML) as GA.
    destruct (gb_after lbl v L (d_set_state d lbl) s) as [l2 L2 d2 s2|rv L2 d2 s2|rv L2 d2 s2] eqn:HG; cbn [dres_map2] in GA.
    + (* [comment removed for export] *)
      cps_destruct (IH l2 L2 (setLB d2 B1 V1) s1 rest (dres_map2 (FLB B1 V1) s1 r) W) as (k2 & B & V' & s3 & kb2 & RUN2 & REST2 & CF2).
      { eapply rd_ok_LB. exact RO1. }
      { exact BO. }
      { rewrite (rd_abs_LB d2 (d_set_state d lbl)). exact AB1. }
      { eapply dfeed_LB. exact H. }
      exists (S k1 + k2)%nat, B, V', s3, (k1 + kb2)%nat.
      split; [| split].
      * intros f. replace (S k1 + k2 + f)%nat with (S k1 + (k2 + f))%nat by lia. rewrite RUN, GA. unfold FLB. cbn [dgo].
        rewrite RUN2. rewrite dres_map2_comp. reflexivity.
      * intros x. cps_destruct (REST2 x) as (R1 & R2 & R3). split; [exact R1|]. split; [exact R2|].
        rewrite (dcost_trans d s (setLB (d_set_state d lbl) B1 V1) s1). rewrite (dcost_LB_l d2 (d_set_state d lbl)) in R3. lia.
      * eapply consumed_from_trans; [exact CF| exact CF2].
    + (* [comment removed for export] *)
      apply dfeed_ret in H as [-> ->].
      exists (S k1)%nat, B1, V1, s1, k1.
      cbn [wbits] in AB1. rewrite bapp_bnil_l in AB1.
      split; [| split; [| exact CF]].
      * intros f. rewrite RUN, GA. reflexivity.
      * intros x. rewrite (rd_abs_LB x (d_set_state d lbl)), (dcost_LB d s x (d_set_state d lbl)).
        split; [exact AB1|]. split; [eapply rd_ok_LB; exact RO1| lia].
    + apply dfeed_retns in H as [-> ->].
      exists (S k1)%nat, B1, V1, s1, k1.
      cbn [wbits] in AB1. rewrite bapp_bnil_l in AB1.
      split; [| split; [| exact CF]].
      * intros f. rewrite RUN, GA. reflexivity.
      * intros x. rewrite (rd_abs_LB x (d_set_state d lbl)), (dcost_LB d s x (d_set_state d lbl)).
        split; [exact AB1|]. split; [eapply rd_ok_LB; exact RO1| lia].
Qed.
End BzR5cD.

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cW.BzR5cLB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cW OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzR5cG.BzR5cD.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma gb_after_10 : forall v L d s, gb_after 10 v L d s = if v =? 66 then DGo 11 L d s else DRet BZ_DATA_ERROR_MAGIC L d s          (* [comment removed for export] *).
Proof. reflexivity. Qed.
Lemma gb_after_11 : forall v L d s, gb_after 11 v L d s = if v =? 90 then DGo 12 L d s else DRet BZ_DATA_ERROR_MAGIC L d s          (* [comment removed for export] *).
Proof. reflexivity. Qed.
Lemma gb_after_12 : forall v L d s, gb_after 12 v L d s = if v =? 104 then DGo 13 L d s else DRet BZ_DATA_ERROR_MAGIC L d s         (* [comment removed for export] *).
Proof. reflexivity. Qed.
Lemma gb_after_13 : forall v L d s, gb_after 13 v L d s = (* [comment removed for export] *)
      let d1 := d_set_bs100k d v in
      if (v <? 49) || (57 <? v) then DRet BZ_DATA_ERROR_MAGIC L d1 s
      else let d2 := d_set_bs100k d1 (v - 48) in
           let d3 := if smallb d2 then d_set_ll_al d2 true else d_set_tt_al d2 true in
           DGo 14 L d3 s.
Proof. reflexivity. Qed.
Lemma gb_after_14 : forall v L d s, gb_after 14 v L d s = if v =? 23 then DGo 42 L d s else if v =? 49 then DGo 15 L d s else DRet BZ_DATA_ERROR L d s.
Proof. reflexivity. Qed.
Lemma gb_after_15 : forall v L d s, gb_after 15 v L d s = if v =? 65 then DGo 16 L d s else DRet BZ_DATA_ERROR L d s.
Proof. reflexivity. Qed.
Lemma gb_after_16 : forall v L d s, gb_after 16 v L d s = if v =? 89 then DGo 17 L d s else DRet BZ_DATA_ERROR L d s.
Proof. reflexivity. Qed.
Lemma gb_after_17 : forall v L d s, gb_after 17 v L d s = if v =? 38 then DGo 18 L d s else DRet BZ_DATA_ERROR L d s.
Proof. reflexivity. Qed.
Lemma gb_after_18 : forall v L d s, gb_after 18 v L d s = if v =? 83 then DGo 19 L d s else DRet BZ_DATA_ERROR L d s.
Proof. reflexivity. Qed.
Lemma gb_after_19 : forall v L d s, gb_after 19 v L d s = if v =? 89 then DGo 20 L (d_set_sbcrc (d_set_blockNo d (d_blockNo d + 1)) 0) s else DRet BZ_DATA_ERROR L d s.
Proof. reflexivity. Qed.
Lemma gb_after_20 : forall v L d s, gb_after 20 v L d s = DGo 21 L (d_set_sbcrc d (u32 (Z.lor (Z.shiftl (d_sbcrc d) 8) v))) s.
Proof. reflexivity. Qed.
Lemma gb_after_21 : forall v L d s, gb_after 21 v L d s = DGo 22 L (d_set_sbcrc d (u32 (Z.lor (Z.shiftl (d_sbcrc d) 8) v))) s.
Proof. reflexivity. Qed.
Lemma gb_after_22 : forall v L d s, gb_after 22 v L d s = DGo 23 L (d_set_sbcrc d (u32 (Z.lor (Z.shiftl (d_sbcrc d) 8) v))) s.
Proof. reflexivity. Qed.
Lemma gb_after_23 : forall v L d s, gb_after 23 v L d s = DGo 24 L (d_set_sbcrc d (u32 (Z.lor (Z.shiftl (d_sbcrc d) 8) v))) s.
Proof. reflexivity. Qed.
Lemma gb_after_24 : forall v L d s, gb_after 24 v L d s = DGo 25 L (d_set_origPtr (d_set_rand d v) 0) s.
Proof. reflexivity. Qed.
Lemma gb_after_25 : forall v L d s, gb_after 25 v L d s = DGo 26 L (d_set_origPtr d (Z.lor (Z.shiftl (d_origPtr d) 8) v)) s.
Proof. reflexivity. Qed.
Lemma gb_after_26 : forall v L d s, gb_after 26 v L d s = DGo 27 L (d_set_origPtr d (Z.lor (Z.shiftl (d_origPtr d) 8) v)) s.
Proof. reflexivity. Qed.
Lemma gb_after_27 : forall v L d s, gb_after 27 v L d s =
      let d1 := d_set_origPtr d (Z.lor (Z.shiftl (d_origPtr d) 8) v) in
      if d_origPtr d1 <? 0 then DRet BZ_DATA_ERROR L d1 s
      else if 10 + 100000 * d_bs100k d1 <? d_origPtr d1 then DRet BZ_DATA_ERROR L d1 s
      else DGo 28 (sv_set_i L 0) d1 s.
Proof. reflexivity. Qed.
Lemma gb_after_28 : forall v L d s, gb_after 28 v L d s = (* [comment removed for export] *)
      let d1 := d_set_inUse16 d (zset (d_inUse16 d) (sv_i L) (if v =? 1 then 1 else 0)) in
      let i1 := sv_i L + 1 in
      if i1 <? 16 then DGo 28 (sv_set_i L i1) d1 s
      else let d2 := d_set_inUse d1 (clear256 256 0 (d_inUse d1)) in
           map2_outer 17 0 (sv_set_i L 256) d2 s.
Proof. reflexivity. Qed.
Lemma gb_after_29 : forall v L d s, gb_after 29 v L d s = (* [comment removed for export] *)
      let d1 := if v =? 1 then d_set_inUse d (zset (d_inUse d) (sv_i L * 16 + sv_j L) 1) else d in
      let j1 := sv_j L + 1 in
      if j1 <? 16 then DGo 29 (sv_set_j L j1) d1 s
      else map2_outer 17 (sv_i L + 1) (sv_set_j L j1) d1 s.
Proof. reflexivity. Qed.
Lemma gb_after_30 : forall v L d s, gb_after 30 v L d s = if (v <? 2) || (BZ_N_GROUPS <? v) then DRet BZ_DATA_ERROR (sv_set_nGroups L v) d s
             else DGo 31 (sv_set_nGroups L v) d s.
Proof. reflexivity. Qed.
Lemma gb_after_31 : forall v L d s, gb_after 31 v L d s = if v <? 1 then DRet BZ_DATA_ERROR (sv_set_nSelectors L v) d s
             else DGo 32 (sv_set_j (sv_set_i (sv_set_nSelectors L v) 0) 0) d s.
Proof. reflexivity. Qed.
Lemma gb_after_32 : forall v L d s, gb_after 32 v L d s = (* [comment removed for export] *)
      if v =? 0 then
        let i := sv_i L in let j := sv_j L in
        let d1 := if i <? BZ_MAX_SELECTORS then d_set_selMtf d (zset (d_selMtf d) i j) else d in
        let i1 := i + 1 in
        if i1 <? sv_nSelectors L then DGo 32 (sv_set_j (sv_set_i L i1) 0) d1 s
        else
          (* [comment removed for export] *)
          let nSel := if BZ_MAX_SELECTORS <? sv_nSelectors L then BZ_MAX_SELECTORS else sv_nSelectors L in
          let pos0 := pos_init (Z.to_nat (sv_nGroups L)) 0 znew in
          let '(_, sel1) := sel_undo (Z.to_nat nSel) 0 pos0 (d_selMtf d1) (d_sel d1) in
          DGo 33 (sv_set_t (sv_set_i (sv_set_nSelectors L nSel) nSel) 0) (d_set_sel d1 sel1) s
      else
        let j1 := sv_j L + 1 in
        if sv_nGroups L <=? j1 then DRet BZ_DATA_ERROR (sv_set_j L j1) d s
        else DGo 32 (sv_set_j L j1) d s.
Proof. reflexivity. Qed.
Lemma gb_after_33 : forall v L d s, gb_after 33 v L d s = (* [comment removed for export] *)
      coding_check (sv_set_i (sv_set_curr L v) 0) d s.
Proof. reflexivity. Qed.
Lemma gb_after_34 : forall v L d s, gb_after 34 v L d s = (* [comment removed for export] *)
      if v =? 0 then
        let t := sv_t L in let i := sv_i L in
        let d1 := d_set_len d (zset (d_len d) (258 * t + i) (sv_curr L)) in
        let i1 := i + 1 in
        if i1 <? sv_alphaSize L then coding_check (sv_set_i L i1) d1 s
        else let t1 := t + 1 in
             if t1 <? sv_nGroups L then DGo 33 (sv_set_t (sv_set_i L i1) t1) d1 s
             else after_tables (sv_set_t (sv_set_i L i1) t1) d1 s
      else DGo 35 L d s.
Proof. reflexivity. Qed.
Lemma gb_after_35 : forall v L d s, gb_after 35 v L d s = coding_check (sv_set_curr L (if v =? 0 then sv_curr L + 1 else sv_curr L - 1)) d s.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gb_after_42 : forall v L d s, gb_after 42 v L d s = if v =? 114 then DGo 43 L d s else DRet BZ_DATA_ERROR L d s.
Proof. reflexivity. Qed.
Lemma gb_after_43 : forall v L d s, gb_after 43 v L d s = if v =? 69 then DGo 44 L d s else DRet BZ_DATA_ERROR L d s.
Proof. reflexivity. Qed.
Lemma gb_after_44 : forall v L d s, gb_after 44 v L d s = if v =? 56 then DGo 45 L d s else DRet BZ_DATA_ERROR L d s.
Proof. reflexivity. Qed.
Lemma gb_after_45 : forall v L d s, gb_after 45 v L d s = if v =? 80 then DGo 46 L d s else DRet BZ_DATA_ERROR L d s.
Proof. reflexivity. Qed.
Lemma gb_after_46 : forall v L d s, gb_after 46 v L d s = if v =? 144 then DGo 47 L (d_set_sccrc d 0) s else DRet BZ_DATA_ERROR L d s.
Proof. reflexivity. Qed.
Lemma gb_after_47 : forall v L d s, gb_after 47 v L d s = DGo 48 L (d_set_sccrc d (u32 (Z.lor (Z.shiftl (d_sccrc d) 8) v))) s.
Proof. reflexivity. Qed.
Lemma gb_after_48 : forall v L d s, gb_after 48 v L d s = DGo 49 L (d_set_sccrc d (u32 (Z.lor (Z.shiftl (d_sccrc d) 8) v))) s.
Proof. reflexivity. Qed.
Lemma gb_after_49 : forall v L d s, gb_after 49 v L d s = DGo 50 L (d_set_sccrc d (u32 (Z.lor (Z.shiftl (d_sccrc d) 8) v))) s.
Proof. reflexivity. Qed.
Lemma gb_after_50 : forall v L d s, gb_after 50 v L d s = DRet BZ_STREAM_END L (d_set_state (d_set_sccrc d (u32 (Z.lor (Z.shiftl (d_sccrc d) 8) v))) BZ_X_IDLE) s.
Proof. reflexivity. Qed.

Lemma gb_bits_10 : forall L, gb_bits 10 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_11 : forall L, gb_bits 11 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_12 : forall L, gb_bits 12 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_13 : forall L, gb_bits 13 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_14 : forall L, gb_bits 14 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_15 : forall L, gb_bits 15 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_16 : forall L, gb_bits 16 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_17 : forall L, gb_bits 17 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_18 : forall L, gb_bits 18 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_19 : forall L, gb_bits 19 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_20 : forall L, gb_bits 20 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_21 : forall L, gb_bits 21 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_22 : forall L, gb_bits 22 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_23 : forall L, gb_bits 23 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_24 : forall L, gb_bits 24 L = 1.
Proof. reflexivity. Qed.
Lemma gb_bits_25 : forall L, gb_bits 25 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_26 : forall L, gb_bits 26 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_27 : forall L, gb_bits 27 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_28 : forall L, gb_bits 28 L = 1.
Proof. reflexivity. Qed.
Lemma gb_bits_29 : forall L, gb_bits 29 L = 1.
Proof. reflexivity. Qed.
Lemma gb_bits_30 : forall L, gb_bits 30 L = 3.
Proof. reflexivity. Qed.
Lemma gb_bits_31 : forall L, gb_bits 31 L = 15.
Proof. reflexivity. Qed.
Lemma gb_bits_32 : forall L, gb_bits 32 L = 1.
Proof. reflexivity. Qed.
Lemma gb_bits_33 : forall L, gb_bits 33 L = 5.
Proof. reflexivity. Qed.
Lemma gb_bits_34 : forall L, gb_bits 34 L = 1.
Proof. reflexivity. Qed.
Lemma gb_bits_35 : forall L, gb_bits 35 L = 1.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gb_bits_42 : forall L, gb_bits 42 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_43 : forall L, gb_bits 43 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_44 : forall L, gb_bits 44 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_45 : forall L, gb_bits 45 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_46 : forall L, gb_bits 46 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_47 : forall L, gb_bits 47 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_48 : forall L, gb_bits 48 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_49 : forall L, gb_bits 49 L = 8.
Proof. reflexivity. Qed.
Lemma gb_bits_50 : forall L, gb_bits 50 L = 8.
Proof. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma dfeed_nil : forall r, dfeed [] r = Some r.
Proof. reflexivity. Qed.
Lemma dfeed_cons : forall n v ws lbl L d s, dfeed ((n, v) :: ws) (DGo lbl L d s) =
  (if negb (mtf_lbl lbl) && (gb_bits lbl L =? n) then dfeed ws (gb_after lbl v L (d_set_state d lbl) s) else None)%bool.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac zground a := lazymatch a with Z0 => idtac | Zpos _ => idtac | Zneg _ => idtac end.
Ltac zb1 :=
  match goal with
  | |- context [?a =? ?b] => zground a; zground b; let r := eval vm_compute in (a =? b) in change (a =? b) with r
  | |- context [?a <? ?b] => zground a; zground b; let r := eval vm_compute in (a <? b) in change (a <? b) with r
  | |- context [?a <=? ?b] => zground a; zground b; let r := eval vm_compute in (a <=? b) in change (a <=? b) with r
  end.
Ltac zb := repeat zb1; cbv beta iota.
(* [comment removed for export] *)
Ltac ostep GB GA :=
  rewrite dfeed_cons;
  match goal with |- context [mtf_lbl ?l] => let r := eval vm_compute in (mtf_lbl l) in change (mtf_lbl l) with r end;
  rewrite GB; zb; cbn [negb andb]; cbv beta iota; rewrite GA; zb.
