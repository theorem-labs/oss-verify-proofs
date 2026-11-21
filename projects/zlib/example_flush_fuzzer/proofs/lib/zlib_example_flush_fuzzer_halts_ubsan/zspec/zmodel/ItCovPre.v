(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface InflateState Inftrees ModelRel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ItableModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Fixpoint sumN (f : Z -> Z) (lo : Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S k => sumN f lo k + f (lo + Z.of_nat k)
  end.

Definition sumZ (f : Z -> Z) (lo hi : Z) : Z := sumN f lo (Z.to_nat (hi - lo)).

Lemma sumZ_nil : forall f lo hi, hi <= lo -> sumZ f lo hi = 0.
Proof. intros f lo hi H. unfold sumZ. replace (Z.to_nat (hi - lo)) with 0%nat by lia. reflexivity. Qed.

Lemma sumZ_snoc : forall f lo hi, lo <= hi -> sumZ f lo (hi + 1) = sumZ f lo hi + f hi.
Proof.
  intros f lo hi H. unfold sumZ. replace (Z.to_nat (hi + 1 - lo)) with (S (Z.to_nat (hi - lo))) by lia.
  cbn [sumN]. f_equal. f_equal. lia.
Qed.

Lemma sumZ_ext : forall f g lo hi, (forall j, lo <= j < hi -> f j = g j) -> sumZ f lo hi = sumZ g lo hi.
Proof.
  intros f g lo hi H. unfold sumZ.
  assert (A : forall n, Z.of_nat n <= hi - lo -> sumN f lo n = sumN g lo n).
  { induction n as [|n IH]; intros Hn; [reflexivity|]. cbn [sumN]. rewrite IH by lia. f_equal. apply H. lia. }
  destruct (Z_le_dec lo hi); [apply A; lia|]. replace (Z.to_nat (hi - lo)) with 0%nat by lia. reflexivity.
Qed.

Lemma sumZ_split : forall f lo mid hi, lo <= mid <= hi -> sumZ f lo hi = sumZ f lo mid + sumZ f mid hi.
Proof.
  intros f lo mid hi H.
  remember (Z.to_nat (hi - mid)) as n eqn:Hn.
  assert (Hhi : hi = mid + Z.of_nat n) by lia. rewrite Hhi. clear Hhi Hn.
  induction n as [|n IH].
  - rewrite Z.add_0_r. rewrite (sumZ_nil f mid mid) by lia. lia.
  - replace (mid + Z.of_nat (S n)) with (mid + Z.of_nat n + 1) by lia.
    rewrite !sumZ_snoc by lia. rewrite IH. lia.
Qed.

Lemma sumZ_nonneg : forall f lo hi, (forall j, lo <= j < hi -> 0 <= f j) -> 0 <= sumZ f lo hi.
Proof.
  intros f lo hi H. unfold sumZ.
  assert (A : forall n, Z.of_nat n <= hi - lo -> 0 <= sumN f lo n).
  { induction n as [|n IH]; intros Hn; [cbn; lia|]. cbn [sumN].
    assert (0 <= f (lo + Z.of_nat n)) by (apply H; lia). specialize (IH ltac:(lia)). lia. }
  destruct (Z_le_dec lo hi); [apply A; lia|]. replace (Z.to_nat (hi - lo)) with 0%nat by lia. cbn. lia.
Qed.

Lemma sumZ_mono : forall f g lo hi, (forall j, lo <= j < hi -> f j <= g j) -> sumZ f lo hi <= sumZ g lo hi.
Proof.
  intros f g lo hi H. unfold sumZ.
  assert (A : forall n, Z.of_nat n <= hi - lo -> sumN f lo n <= sumN g lo n).
  { induction n as [|n IH]; intros Hn; [cbn; lia|]. cbn [sumN].
    assert (f (lo + Z.of_nat n) <= g (lo + Z.of_nat n)) by (apply H; lia). specialize (IH ltac:(lia)). lia. }
  destruct (Z_le_dec lo hi); [apply A; lia|]. replace (Z.to_nat (hi - lo)) with 0%nat by lia. cbn. lia.
Qed.

Lemma sumZ_scale : forall c f lo hi, sumZ (fun j => c * f j) lo hi = c * sumZ f lo hi.
Proof.
  intros c f lo hi. unfold sumZ. induction (Z.to_nat (hi - lo)) as [|n IH]; cbn [sumN]; [lia|]. rewrite IH. lia.
Qed.

Lemma sumZ_add : forall f g lo hi, sumZ (fun j => f j + g j) lo hi = sumZ f lo hi + sumZ g lo hi.
Proof.
  intros f g lo hi. unfold sumZ. induction (Z.to_nat (hi - lo)) as [|n IH]; cbn [sumN]; [lia|]. rewrite IH. lia.
Qed.

Lemma sumZ_zero : forall lo hi, sumZ (fun _ => 0) lo hi = 0.
Proof. intros lo hi. unfold sumZ. induction (Z.to_nat (hi - lo)); cbn [sumN]; lia. Qed.

Lemma sumZ_one : forall f lo j hi, lo <= j < hi ->
  (forall i, lo <= i < hi -> i <> j -> f i = 0) -> sumZ f lo hi = f j.
Proof.
  intros f lo j hi Hj H0.
  rewrite (sumZ_split f lo j hi) by lia. rewrite (sumZ_split f j (j + 1) hi) by lia.
  rewrite (sumZ_snoc f j j) by lia. rewrite (sumZ_nil f j j) by lia.
  rewrite (sumZ_ext f (fun _ => 0) lo j) by (intros; apply H0; lia).
  rewrite (sumZ_ext f (fun _ => 0) (j + 1) hi) by (intros; apply H0; lia).
  assert (Z0 : forall a b, sumZ (fun _ => 0) a b = 0).
  { intros a b. unfold sumZ. induction (Z.to_nat (b - a)); cbn [sumN]; lia. }
  rewrite !Z0. lia.
Qed.


Section Lens.
  Variables (lens : arr) (lens_ofs codes : Z).
  Hypothesis Hcodes : 0 <= codes <= 288.
  Hypothesis Hlens : forall s, 0 <= s < codes -> 0 <= arr_get lens (lens_ofs + s) <= 15.

  Definition L (s : Z) : Z := arr_get lens (lens_ofs + s).

  Definition cntk (k l : Z) : Z := sumZ (fun s => if L s =? l then 1 else 0) 0 k.
  Definition cnt : Z -> Z := cntk codes.

  Lemma cntk_0 : forall l, cntk 0 l = 0.
  Proof. intro l. unfold cntk. apply sumZ_nil. lia. Qed.
  Lemma cntk_step : forall k l, 0 <= k -> cntk (k + 1) l = cntk k l + (if L k =? l then 1 else 0).
  Proof. intros k l Hk. unfold cntk. apply sumZ_snoc. lia. Qed.
  Lemma cntk_range : forall k l, 0 <= k -> 0 <= cntk k l <= k.
  Proof.
    intros k l Hk. remember (Z.to_nat k) as n eqn:Hn. replace k with (Z.of_nat n) by lia. clear k Hk Hn.
    induction n as [|n IH]; [rewrite cntk_0; lia|].
    replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia. rewrite cntk_step by lia. destruct (L _ =? l); lia.
  Qed.
  Lemma cnt_range : forall l, 0 <= cnt l <= codes.
  Proof. intro l. unfold cnt. apply cntk_range. lia. Qed.


  Lemma count_k_spec : forall k, 0 <= k <= codes ->
    arr_len (itm_count_k lens lens_ofs k) = 16 /\
    forall l, 0 <= l <= 15 -> arr_get (itm_count_k lens lens_ofs k) l = cntk k l.
  Proof.
    intros k Hk. remember (Z.to_nat k) as n eqn:Hn.
    assert (Hk' : k = Z.of_nat n) by lia. rewrite Hk'. assert (Hn' : Z.of_nat n <= codes) by lia. clear k Hk Hn Hk'.
    induction n as [|n IH].
    - rewrite itm_count_k_0 by lia. split; [apply it_zero_count_len|].
      intros l Hl. rewrite it_zero_count_spec, cntk_0. reflexivity.
    - destruct (IH ltac:(lia)) as [IHlen IHv].
      replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
      rewrite itm_count_k_step by lia. cbv zeta. split; [rewrite arr_len_set; exact IHlen|].
      intros l Hl. rewrite cntk_step by lia.
      pose proof (Hlens (Z.of_nat n) ltac:(lia)) as HL. fold (L (Z.of_nat n)) in HL |- *.
      rewrite arr_get_set. unfold arr_inb. rewrite IHlen.
      destruct (Z.eq_dec l (L (Z.of_nat n))) as [->|Hne].
      + rewrite !(Z.eqb_refl (L (Z.of_nat n))). replace ((0 <=? L (Z.of_nat n)) && (L (Z.of_nat n) <? 16)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
        cbn [andb]. rewrite IHv by lia.
        pose proof (cntk_range (Z.of_nat n) (L (Z.of_nat n)) ltac:(lia)). apply wrap16_id. lia.
      + replace (L (Z.of_nat n) =? l) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
        rewrite IHv by lia. lia.
  Qed.

  Definition count : arr := itm_count lens lens_ofs codes.

  Lemma count_len : arr_len count = 16.
  Proof. unfold count. rewrite itm_count_eq. apply (proj1 (count_k_spec codes ltac:(lia))). Qed.
  Lemma count_spec : forall l, 0 <= l <= 15 -> arr_get count l = cnt l.
  Proof. intros l Hl. unfold count, cnt. rewrite itm_count_eq. apply (proj2 (count_k_spec codes ltac:(lia))). exact Hl. Qed.


  Definition max : Z := it_find_max count.
  Definition min : Z := it_find_min count max.

  Lemma max_spec : 0 <= max <= 15 /\ (max = 0 \/ cnt max <> 0) /\ (forall j, max < j <= 15 -> cnt j = 0).
  Proof.
    unfold max. change (it_find_max count) with (itm_max count). rewrite itm_max_rec.
    destruct (find_max_rec_spec count 16 15 ltac:(lia) ltac:(cbn; lia)) as (A & B & C).
    split; [exact A|]. split.
    - destruct B as [B|B]; [left; exact B|right]. rewrite <- count_spec by lia. exact B.
    - intros j Hj. rewrite <- count_spec by lia. apply C. lia.
  Qed.


  Lemma min_spec : 1 <= max ->
    1 <= min <= max /\ (min = max \/ cnt min <> 0) /\ (forall j, 1 <= j < min -> cnt j = 0).
  Proof.
    intros Hm. pose proof max_spec as (A & _ & _). unfold min.
    change (it_find_min count max) with (itm_min count max). rewrite itm_min_rec by lia.
    destruct (find_min_rec_spec count max 16 1 ltac:(lia) ltac:(change (Z.of_nat 16) with 16; lia)) as (A' & B & C).
    split; [exact A'|]. split.
    - destruct B as [B|B]; [left; exact B|right]. rewrite <- count_spec by lia. exact B.
    - intros j Hj. rewrite <- count_spec by lia. apply C. lia.
  Qed.


  Definition kraft (k : Z) : Z := sumZ (fun l => cnt l * 2 ^ (k - l)) 1 (k + 1).

  Lemma kraft_step : forall k, 1 <= k -> kraft (k + 1) = 2 * kraft k + cnt (k + 1).
  Proof.
    intros k Hk. unfold kraft. rewrite (sumZ_snoc _ 1 (k + 1)) by lia.
    rewrite Z.sub_diag, Z.pow_0_r, Z.mul_1_r. f_equal.
    rewrite <- sumZ_scale. apply sumZ_ext. intros j Hj.
    replace (k + 1 - j) with (Z.succ (k - j)) by lia. rewrite Z.pow_succ_r by lia. lia.
  Qed.
  Lemma kraft_1 : kraft 1 = cnt 1.
  Proof. unfold kraft. rewrite (sumZ_snoc _ 1 1), sumZ_nil by lia. rewrite Z.sub_diag, Z.pow_0_r. lia. Qed.
  Lemma kraft_nonneg : forall k, 0 <= kraft k.
  Proof.
    intro k. unfold kraft. apply sumZ_nonneg. intros j Hj. pose proof (cnt_range j).
    apply Z.mul_nonneg_nonneg; [lia|]. apply Z.pow_nonneg. lia.
  Qed.

  Lemma left_rec_spec : forall n len lft,
    1 <= len <= 16 -> Z.of_nat n = 16 - len + 1 \/ (len = 16 /\ (0 < n)%nat) ->
    lft = 2 ^ (len - 1) - kraft (len - 1) \/ (len = 1 /\ lft = 1) ->
    0 <= lft ->
    left_rec count n len lft =
      if 2 ^ 15 <? kraft 15 then None else Some (2 ^ 15 - kraft 15).
  Proof.
    induction n as [|n IH]; intros len lft Hlen Hn Hlft Hpos; [lia|].
    rewrite left_rec_S. unfold MAXBITS.
    destruct (Z.leb_spec len 15).
    - rewrite count_spec by lia. rewrite Z.shiftl_mul_pow2, Z.pow_1_r by lia.
      assert (Hl' : lft * 2 - cnt len = 2 ^ len - kraft len).
      { destruct Hlft as [->|[-> ->]].
        - destruct (Z.eq_dec len 1) as [->|].
          + rewrite kraft_1. change (2 ^ (1 - 1)) with 1. change (2^1) with 2.
            unfold kraft. rewrite sumZ_nil by lia. lia.
          + pose proof (kraft_step (len - 1) ltac:(lia)) as E. replace (len - 1 + 1) with len in E by lia.
            assert (P : 2 ^ len = 2 * 2 ^ (len - 1)).
            { replace len with (Z.succ (len - 1)) at 1 by lia. rewrite Z.pow_succ_r by lia. reflexivity. }
            rewrite E, P. lia.
        - rewrite kraft_1. change (2 ^ 1) with 2. lia. }
      rewrite Hl'.
      destruct (Z.ltb_spec (2 ^ len - kraft len) 0).
      +
        assert (K : forall d, kraft (len + Z.of_nat d) >= 2 ^ Z.of_nat d * kraft len).
        { induction d as [|d IHd]. { rewrite Z.add_0_r. change (2 ^ Z.of_nat 0) with 1. lia. }
          replace (len + Z.of_nat (S d)) with (len + Z.of_nat d + 1) by lia. rewrite kraft_step by lia.
          replace (Z.of_nat (S d)) with (Z.succ (Z.of_nat d)) by lia. rewrite Z.pow_succ_r by lia.
          pose proof (cnt_range (len + Z.of_nat d + 1)). lia. }
        specialize (K (Z.to_nat (15 - len))). replace (len + Z.of_nat (Z.to_nat (15 - len))) with 15 in K by lia.
        rewrite Z2Nat.id in K by lia.
        assert (2 ^ 15 = 2 ^ (15 - len) * 2 ^ len) by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
        assert (0 < 2 ^ (15 - len)) by (apply Z.pow_pos_nonneg; lia).
        replace (2 ^ 15 <? kraft 15) with true; [reflexivity|]. symmetry. apply Z.ltb_lt. nia.
      + apply IH; try lia. left. replace (len + 1 - 1) with len by lia. reflexivity.
    - assert (len = 16) by lia. subst len. destruct Hlft as [Hl|[? _]]; [|lia].
      change (16 - 1) with 15 in Hl. subst lft.
      destruct (Z.ltb_spec (2 ^ 15) (kraft 15)); [lia|reflexivity].
  Qed.

  Lemma left_check_spec :
    it_left_check count = if 2 ^ 15 <? kraft 15 then None else Some (2 ^ 15 - kraft 15).
  Proof. rewrite it_left_check_rec. apply (left_rec_spec 16 1 1); lia. Qed.




  Lemma sum_cntk : forall k, 0 <= k <= codes -> sumZ (cntk k) 0 16 = k.
  Proof.
    intros k Hk. remember (Z.to_nat k) as n eqn:Hn.
    assert (Hk' : k = Z.of_nat n) by lia. rewrite Hk'. assert (Hn' : Z.of_nat n <= codes) by lia. clear k Hk Hn Hk'.
    induction n as [|n IH].
    - rewrite (sumZ_ext (cntk (Z.of_nat 0)) (fun _ => 0)); [apply sumZ_zero|]. intros j _. apply cntk_0.
    - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
      rewrite (sumZ_ext (cntk (Z.of_nat n + 1)) (fun l => cntk (Z.of_nat n) l + (if L (Z.of_nat n) =? l then 1 else 0)))
        by (intros j _; apply cntk_step; lia).
      rewrite sumZ_add. rewrite IH by lia.
      pose proof (Hlens (Z.of_nat n) ltac:(lia)) as HL. fold (L (Z.of_nat n)) in HL.
      enough (E : sumZ (fun l : Z => if L (Z.of_nat n) =? l then 1 else 0) 0 16 = 1) by lia.
      rewrite (sumZ_one _ 0 (L (Z.of_nat n)) 16); [| lia | intros i Hi Hne; destruct (Z.eqb_spec (L (Z.of_nat n)) i); lia].
      rewrite (Z.eqb_refl (L (Z.of_nat n))). reflexivity.
  Qed.

  Definition N : Z := sumZ cnt 1 16.

  Lemma N_eq : N = codes - cnt 0.
  Proof.
    unfold N. pose proof (sum_cntk codes ltac:(lia)) as S. unfold cnt.
    rewrite (sumZ_split (cntk codes) 0 1 16) in S by lia.
    replace (sumZ (cntk codes) 0 1) with (0 + cntk codes (0 + Z.of_nat 0)) in S by reflexivity.
    replace (0 + Z.of_nat 0) with 0 in S by lia. lia.
  Qed.
  Lemma N_range : 0 <= N <= codes.
  Proof. rewrite N_eq. pose proof (cnt_range 0). unfold N. pose proof (sumZ_nonneg cnt 1 16 ltac:(intros; pose proof (cnt_range j); lia)). lia. Qed.


  Definition coff (l : Z) : Z := sumZ cnt 1 l.

  Lemma coff_1 : coff 1 = 0.
  Proof. unfold coff. apply sumZ_nil. lia. Qed.
  Lemma coff_step : forall l, 1 <= l -> coff (l + 1) = coff l + cnt l.
  Proof. intros l Hl. unfold coff. apply sumZ_snoc. lia. Qed.
  Lemma coff_range : forall l, 1 <= l <= 16 -> 0 <= coff l <= N.
  Proof.
    intros l Hl. unfold coff, N. split.
    - apply sumZ_nonneg. intros j _. pose proof (cnt_range j). lia.
    - rewrite (sumZ_split cnt 1 l 16) by lia. pose proof (sumZ_nonneg cnt l 16 ltac:(intros; pose proof (cnt_range j); lia)). lia.
  Qed.
  Lemma coff_mono : forall l l', 1 <= l <= l' -> coff l <= coff l'.
  Proof.
    intros l l' H. unfold coff. rewrite (sumZ_split cnt 1 l l') by lia.
    pose proof (sumZ_nonneg cnt l l' ltac:(intros; pose proof (cnt_range j); lia)). lia.
  Qed.
  Lemma coff_16 : coff 16 = N.
  Proof. unfold coff, N. reflexivity. Qed.

  Definition offs : arr := itm_offs count.

  Lemma offs_spec : arr_len offs = 16 /\ forall l, 1 <= l <= 15 -> arr_get offs l = coff l.
  Proof.
    unfold offs. rewrite itm_offs_eq. unfold MAXBITS.
    assert (G : forall n, (1 <= n <= 15)%nat ->
      arr_len (itm_offs_k count (Z.of_nat n)) = 16 /\
      forall l, 1 <= l <= Z.of_nat n -> arr_get (itm_offs_k count (Z.of_nat n)) l = coff l).
    { induction n as [|n IH]; intros Hn; [lia|].
      destruct (Nat.eq_dec n 0) as [->|Hn0].
      - change (Z.of_nat 1) with 1. rewrite itm_offs_k_1. split.
        + rewrite arr_len_set. apply arr_len_make.
        + intros l Hl. assert (l = 1) by lia. subst l. rewrite arr_get_set. cbn. rewrite coff_1. reflexivity.
      - destruct (IH ltac:(lia)) as [IHlen IHv].
        replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia. rewrite itm_offs_k_step by lia. cbv zeta. split.
        + rewrite arr_len_set. exact IHlen.
        + intros l Hl. rewrite arr_get_set. unfold arr_inb. rewrite IHlen.
          destruct (Z.eqb_spec (Z.of_nat n + 1) l) as [<-|Hne].
          * replace ((0 <=? Z.of_nat n + 1) && (Z.of_nat n + 1 <? 16)) with true
              by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia). cbn [andb].
            rewrite IHv by lia. rewrite count_spec by lia. rewrite coff_step by lia.
            pose proof (coff_range (Z.of_nat n + 1) ltac:(lia)) as R. rewrite coff_step in R by lia.
            pose proof N_range. pose proof (coff_range (Z.of_nat n) ltac:(lia)). apply wrap16_id. lia.
          * cbn [andb]. apply IHv. lia. }
    destruct (G 15%nat ltac:(lia)) as [A B]. split; [exact A|]. intros l Hl. apply B. lia.
  Qed.


  Definition zseq (lo : Z) (n : nat) : list Z := map (fun i => lo + Z.of_nat i) (seq 0 n).

  Lemma zseq_S : forall lo n, zseq lo (S n) = zseq lo n ++ [lo + Z.of_nat n].
  Proof. intros lo n. unfold zseq. rewrite seq_S, map_app. reflexivity. Qed.
  Lemma in_zseq : forall lo n x, In x (zseq lo n) <-> lo <= x < lo + Z.of_nat n.
  Proof.
    intros lo n x. unfold zseq. rewrite in_map_iff. split.
    - intros (i & <- & Hi). apply in_seq in Hi. lia.
    - intros H. exists (Z.to_nat (x - lo)). split; [lia|]. apply in_seq. lia.
  Qed.

  Definition blkk (k : Z) (l : Z) : list Z := filter (fun s => L s =? l) (zseq 0 (Z.to_nat k)).
  Definition blk (l : Z) : list Z := blkk codes l.

  Lemma blkk_step : forall k l, 0 <= k ->
    blkk (k + 1) l = blkk k l ++ (if L k =? l then [k] else []).
  Proof.
    intros k l Hk. unfold blkk. replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
    rewrite zseq_S, filter_app. cbn [filter]. replace (0 + Z.of_nat (Z.to_nat k)) with k by lia.
    destruct (L k =? l); reflexivity.
  Qed.
  Lemma blkk_0 : forall l, blkk 0 l = [].
  Proof. intro l. reflexivity. Qed.
  Lemma blkk_length : forall k l, 0 <= k -> zlength (blkk k l) = cntk k l.
  Proof.
    intros k l Hk. remember (Z.to_nat k) as n eqn:Hn. replace k with (Z.of_nat n) by lia. clear k Hk Hn.
    induction n as [|n IH].
    - rewrite blkk_0, cntk_0. reflexivity.
    - replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia. rewrite blkk_step, cntk_step by lia.
      rewrite zlength_app, IH. destruct (L _ =? l); rewrite ?zlength_cons, ?zlength_nil; lia.
  Qed.
  Lemma blk_length : forall l, zlength (blk l) = cnt l.
  Proof. intro l. unfold blk, cnt. apply blkk_length. lia. Qed.
  Lemma in_blkk : forall k l x, 0 <= k -> In x (blkk k l) <-> 0 <= x < k /\ L x = l.
  Proof.
    intros k l x Hk. unfold blkk. rewrite filter_In, in_zseq. rewrite Z.eqb_eq. lia.
  Qed.

  Fixpoint Wmid (m : Z) (n : nat) : list Z :=
    match n with
    | O => []
    | S k => Wmid m k ++ blk (m + Z.of_nat n)
    end.
  Definition W : list Z := Wmid 0 15.

  Lemma Wmid_length : forall m n, 0 <= m -> zlength (Wmid m n) = sumZ cnt (m + 1) (m + Z.of_nat n + 1).
  Proof.
    intros m n Hm. induction n as [|n IH].
    - cbn [Wmid]. rewrite sumZ_nil by lia. reflexivity.
    - cbn [Wmid]. rewrite zlength_app, IH, blk_length.
      replace (m + Z.of_nat (S n) + 1) with (m + Z.of_nat n + 1 + 1) by lia. rewrite (sumZ_snoc cnt (m + 1) (m + Z.of_nat n + 1)) by lia.
      f_equal. f_equal. lia.
  Qed.

  Lemma Wmid_app : forall m a b, Wmid m (a + b) = Wmid m a ++ Wmid (m + Z.of_nat a) b.
  Proof.
    intros m a b. induction b as [|b IH].
    - cbn [Wmid]. rewrite Nat.add_0_r, app_nil_r. reflexivity.
    - rewrite Nat.add_succ_r. cbn [Wmid]. rewrite IH. rewrite <- app_assoc. f_equal. f_equal. f_equal. lia.
  Qed.

  Lemma W_block : forall l, 1 <= l <= 15 ->
    exists P S, W = P ++ blk l ++ S /\ zlength P = coff l.
  Proof.
    intros l Hl. unfold W.
    replace 15%nat with (Z.to_nat (l - 1) + (1 + Z.to_nat (15 - l)))%nat by lia.
    rewrite Wmid_app. rewrite (Wmid_app (0 + Z.of_nat (Z.to_nat (l - 1))) 1).
    exists (Wmid 0 (Z.to_nat (l - 1))), (Wmid (0 + Z.of_nat (Z.to_nat (l - 1)) + Z.of_nat 1) (Z.to_nat (15 - l))).
    split.
    - cbn [Wmid]. cbn [app]. replace (0 + Z.of_nat (Z.to_nat (l - 1)) + Z.of_nat 1) with l by lia.
      reflexivity.
    - rewrite Wmid_length by lia. unfold coff. f_equal; lia.
  Qed.

  Lemma znth_app_r : forall (P Q : list Z) i, zlength P <= i -> znth 0 (P ++ Q) i = znth 0 Q (i - zlength P).
  Proof.
    intros P Q i Hi. unfold znth, zlength in *. pose proof (Zle_0_nat (length P)).
    destruct (Z.ltb_spec i 0); [lia|]. destruct (Z.ltb_spec (i - Z.of_nat (length P)) 0); [lia|].
    rewrite app_nth2 by lia. f_equal. lia.
  Qed.
  Lemma znth_app_l : forall (P Q : list Z) i, 0 <= i < zlength P -> znth 0 (P ++ Q) i = znth 0 P i.
  Proof.
    intros P Q i Hi. unfold znth, zlength in *. destruct (Z.ltb_spec i 0); [lia|]. rewrite app_nth1 by lia. reflexivity.
  Qed.

  Lemma W_nth_block : forall l r, 1 <= l <= 15 -> 0 <= r < cnt l -> znth 0 W (coff l + r) = znth 0 (blk l) r.
  Proof.
    intros l r Hl Hr. destruct (W_block l Hl) as (P & S & E & HP). rewrite E.
    rewrite znth_app_r by lia. rewrite HP. replace (coff l + r - coff l) with r by lia.
    apply znth_app_l. rewrite blk_length. lia.
  Qed.

  Lemma W_block_spec : forall l i, 1 <= l <= 15 -> coff l <= i < coff l + cnt l ->
    0 <= znth 0 W i < codes /\ L (znth 0 W i) = l.
  Proof.
    intros l i Hl Hi. replace i with (coff l + (i - coff l)) by lia. rewrite W_nth_block by lia.
    replace (coff l + (i - coff l) - coff l) with (i - coff l) by lia.
    assert (In (znth 0 (blk l) (i - coff l)) (blk l)) as HIn.
    { unfold znth. destruct (Z.ltb_spec (i - coff l) 0); [lia|]. apply nth_In. pose proof (blk_length l). unfold zlength in *. lia. }
    unfold blk in *. apply in_blkk in HIn; [exact HIn|lia].
  Qed.

  Lemma W_index_block : forall i, 0 <= i < N -> exists l, 1 <= l <= 15 /\ coff l <= i < coff l + cnt l.
  Proof.
    intros i Hi.
    assert (G : forall n, (n <= 15)%nat -> i < coff (Z.of_nat n + 1) -> exists l, 1 <= l <= Z.of_nat n /\ coff l <= i < coff l + cnt l).
    { induction n as [|n IH]; intros Hn Hlt.
      - change (Z.of_nat 0 + 1) with 1 in Hlt. rewrite coff_1 in Hlt. lia.
      - replace (Z.of_nat (S n) + 1) with (Z.of_nat n + 1 + 1) in Hlt by lia. rewrite coff_step in Hlt by lia.
        destruct (Z_lt_le_dec i (coff (Z.of_nat n + 1))).
        + destruct (IH ltac:(lia) ltac:(lia)) as (l0 & A & B). exists l0. split; [lia|exact B].
        + exists (Z.of_nat n + 1). split; [lia|]. lia. }
    destruct (G 15%nat ltac:(lia)) as (l0 & A & B).
    - change (Z.of_nat 15 + 1) with 16. rewrite coff_16. lia.
    - exists l0. split; [lia|exact B].
  Qed.

  Lemma W_spec : forall i, 0 <= i < N -> 0 <= znth 0 W i < codes /\ 1 <= L (znth 0 W i) <= 15.
  Proof.
    intros i Hi. destruct (W_index_block i Hi) as (l & Hl & Hb).
    destruct (W_block_spec l i Hl Hb) as [A B]. rewrite B. lia.
  Qed.

  Lemma W_sorted : forall i j, 0 <= i <= j -> j < N -> L (znth 0 W i) <= L (znth 0 W j).
  Proof.
    intros i j Hij Hj.
    destruct (W_index_block i ltac:(lia)) as (l & Hl & Hb). destruct (W_block_spec l i Hl Hb) as [_ ->].
    destruct (W_index_block j ltac:(lia)) as (l' & Hl' & Hb'). destruct (W_block_spec l' j Hl' Hb') as [_ ->].
    destruct (Z_lt_le_dec l' l); [|lia].
    pose proof (coff_mono (l' + 1) l ltac:(lia)). rewrite coff_step in * by lia. lia.
  Qed.

  Lemma sort_k_spec : forall work k, N <= arr_len work -> 0 <= k <= codes ->
    let ow := itm_sort_k lens lens_ofs k offs work in
    arr_len (fst ow) = 16
    /\ (forall l, 1 <= l <= 15 -> arr_get (fst ow) l = coff l + cntk k l)
    /\ arr_len (snd ow) = arr_len work
    /\ (forall l r, 1 <= l <= 15 -> 0 <= r < cntk k l -> arr_get (snd ow) (coff l + r) = znth 0 (blkk k l) r)
    /\ (forall i, N <= i -> arr_get (snd ow) i = arr_get work i).
  Proof.
    intros work k Hw Hk. remember (Z.to_nat k) as n eqn:Hn.
    assert (Hk' : k = Z.of_nat n) by lia. rewrite Hk'. assert (Hn' : Z.of_nat n <= codes) by lia. clear k Hk Hn Hk'.
    destruct offs_spec as [OL OV].
    induction n as [|n IH].
    - rewrite itm_sort_k_0 by lia. cbn [fst snd]. split; [exact OL|]. split; [|split; [reflexivity|split]].
      + intros l Hl. rewrite OV, cntk_0 by lia. lia.
      + intros l r Hl Hr. rewrite cntk_0 in Hr. lia.
      + intros; reflexivity.
    - destruct (IH ltac:(lia)) as (A & B & C & D & E).
      replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia. rewrite itm_sort_k_step by lia.
      set (ow := itm_sort_k lens lens_ofs (Z.of_nat n) offs work) in *.
      destruct ow as [o w]. cbn [fst snd] in A, B, C, D, E. unfold sort_body.
      pose proof (Hlens (Z.of_nat n) ltac:(lia)) as HL. fold (L (Z.of_nat n)) in HL |- *.
      change (arr_get lens (lens_ofs + Z.of_nat n)) with (L (Z.of_nat n)).
      destruct (Z.eqb_spec (L (Z.of_nat n)) 0) as [HL0|HL0]; cbn [negb].
      +
        cbn [fst snd]. split; [exact A|]. split; [|split; [exact C|split]].
        * intros l Hl. rewrite B, cntk_step by lia. rewrite HL0. replace (0 =? l) with false by (symmetry; apply Z.eqb_neq; lia). lia.
        * intros l r Hl Hr. rewrite cntk_step, HL0 in Hr by lia. replace (0 =? l) with false in Hr by (symmetry; apply Z.eqb_neq; lia).
          rewrite blkk_step, HL0 by lia. replace (0 =? l) with false by (symmetry; apply Z.eqb_neq; lia). rewrite app_nil_r.
          apply D; lia.
        * exact E.
      + cbv zeta. cbn [fst snd].
        remember (L (Z.of_nat n)) as l0 eqn:El0.
        assert (Hcnt : 0 <= cntk (Z.of_nat n) l0 < cnt l0).
        { pose proof (cntk_range (Z.of_nat n) l0 ltac:(lia)). split; [lia|].
          unfold cnt. replace codes with ((Z.of_nat n + 1) + (codes - (Z.of_nat n + 1))) by lia.
          assert (M : forall d a, 0 <= a -> cntk a l0 <= cntk (a + Z.of_nat d) l0).
          { induction d as [|d IHd]; intros a Ha; [rewrite Z.add_0_r; lia|].
            replace (a + Z.of_nat (S d)) with (a + Z.of_nat d + 1) by lia. rewrite cntk_step by lia.
            specialize (IHd a Ha). destruct (_ =? _); lia. }
          pose proof (M (Z.to_nat (codes - (Z.of_nat n + 1))) (Z.of_nat n + 1) ltac:(lia)) as M1.
          rewrite Z2Nat.id in M1 by lia. rewrite cntk_step, <- El0, Z.eqb_refl in M1 by lia. lia. }
        pose proof (coff_range l0 ltac:(lia)) as CR.
        pose proof (coff_range (l0 + 1) ltac:(lia)) as CR1. rewrite coff_step in CR1 by lia.
        assert (CM : forall l, 1 <= l <= 15 -> cntk (Z.of_nat n) l <= cnt l).
        { intros l Hl. unfold cnt. replace codes with (Z.of_nat n + Z.of_nat (Z.to_nat (codes - Z.of_nat n))) by lia.
          assert (M : forall d a, 0 <= a -> cntk a l <= cntk (a + Z.of_nat d) l).
          { induction d as [|d IHd]; intros a Ha; [rewrite Z.add_0_r; lia|].
            replace (a + Z.of_nat (S d)) with (a + Z.of_nat d + 1) by lia. rewrite cntk_step by lia.
            specialize (IHd a Ha). destruct (_ =? _); lia. }
          apply M. lia. }
        split; [rewrite arr_len_set; exact A|]. split; [|split; [rewrite arr_len_set; exact C|split]].
        * intros l Hl. rewrite arr_get_set. unfold arr_inb. rewrite A.
          rewrite B, cntk_step, <- El0 by lia.
          destruct (Z.eqb_spec l0 l) as [<-|Hne].
          -- replace ((0 <=? l0) && (l0 <? 16)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
             cbn [andb]. pose proof N_range. rewrite wrap16_id by lia. lia.
          -- cbn [andb]. rewrite ?B by lia. lia.
        * intros l r Hl Hr. rewrite arr_get_set. unfold arr_inb. rewrite C. rewrite B by lia.
          rewrite blkk_step, <- El0 by lia. rewrite cntk_step, <- El0 in Hr by lia.
          destruct (Z.eqb_spec l0 l) as [El|Hne].
          -- subst l.
             destruct (Z.eqb_spec (coff l0 + cntk (Z.of_nat n) l0) (coff l0 + r)) as [Heq|Hne'].
             ++ assert (r = cntk (Z.of_nat n) l0) by lia. subst r.
                replace ((0 <=? coff l0 + cntk (Z.of_nat n) l0) && (coff l0 + cntk (Z.of_nat n) l0 <? arr_len work)) with true
                  by (symmetry; apply andb_true_intro; split; [apply Z.leb_le|apply Z.ltb_lt]; lia). cbn [andb].
                rewrite znth_app_r by (rewrite blkk_length; lia). rewrite blkk_length by lia.
                rewrite Z.sub_diag.
                change (znth 0 [Z.of_nat n] 0) with (Z.of_nat n). rewrite wrap16_id by lia. reflexivity.
             ++ cbn [andb]. rewrite znth_app_l by (rewrite blkk_length; lia). apply D; lia.
          -- rewrite app_nil_r.
             destruct (Z.eqb_spec (coff l0 + cntk (Z.of_nat n) l0) (coff l + r)) as [Heq|Hne'].
             ++ exfalso.
                pose proof (CM l Hl).
                destruct (Z_lt_le_dec l0 l).
                ** pose proof (coff_mono (l0 + 1) l ltac:(lia)) as M. rewrite coff_step in M by lia. lia.
                ** pose proof (coff_mono (l + 1) l0 ltac:(lia)) as M. rewrite coff_step in M by lia. lia.
             ++ cbn [andb]. apply D; lia.
        * intros i Hi. rewrite arr_get_set. unfold arr_inb. rewrite B by lia.
          destruct (Z.eqb_spec (coff l0 + cntk (Z.of_nat n) l0) i) as [Heq|Hne']; [exfalso; lia|].
          cbn [andb]. apply E. exact Hi.
  Qed.

  Lemma sort_spec : forall work, N <= arr_len work ->
    let work' := snd (it_sort lens lens_ofs codes (offs, work)) in
    arr_len work' = arr_len work
    /\ (forall i, 0 <= i < N -> arr_get work' i = znth 0 W i)
    /\ (forall i, N <= i -> arr_get work' i = arr_get work i).
  Proof.
    intros work Hw. rewrite it_sort_eq. change (forZ 0 codes (sort_body lens lens_ofs) (offs, work)) with (itm_sort_k lens lens_ofs codes offs work).
    destruct (sort_k_spec work codes Hw ltac:(lia)) as (A & B & C & D & E). cbv zeta.
    split; [exact C|]. split; [|exact E].
    intros i Hi. destruct (W_index_block i Hi) as (l & Hl & Hb).
    replace i with (coff l + (i - coff l)) by lia. rewrite W_nth_block by lia.
    unfold blk. apply D; [lia|]. unfold cnt in Hb. lia.
  Qed.

End Lens.
