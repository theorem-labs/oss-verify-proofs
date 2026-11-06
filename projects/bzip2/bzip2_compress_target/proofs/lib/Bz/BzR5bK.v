(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzArr BzCHuff BzCPermF BzCRebuildF BzCHuffF1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF4.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF4.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF4.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF6.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCPermF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF4.BzCHuffF2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF4.BzCHuffF3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF6.BzCHuffF5 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF6.
Import ListNotations.
Open Scope Z_scope.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ind (b : bool) : Z := if b then 1 else 0.

Lemma sumF_addf : forall n g h j, sumF (fun b => g b + h b) j n = sumF g j n + sumF h j n.
Proof. induction n as [|n IH]; intros g h j; cbn [sumF]; [lia|]. rewrite IH. lia. Qed.
Lemma sumF_scal : forall n k g j, sumF (fun b => k * g b) j n = k * sumF g j n.
Proof. induction n as [|n IH]; intros k g j; cbn [sumF]; [lia|]. rewrite IH. lia. Qed.
Lemma sumF_lef : forall n g h j, (forall b, j <= b < j + Z.of_nat n -> g b <= h b) -> sumF g j n <= sumF h j n.
Proof.
  induction n as [|n IH]; intros g h j H; cbn [sumF]; [lia|].
  assert (g j <= h j) by (apply H; lia). assert (sumF g (j + 1) n <= sumF h (j + 1) n) by (apply IH; intros; apply H; lia). lia.
Qed.
Lemma sumF_shift : forall n g j d, sumF g j n = sumF (fun b => g (b + d)) (j - d) n.
Proof.
  induction n as [|n IH]; intros g j d; cbn [sumF]; [lia|]. replace (j - d + d) with j by lia.
  rewrite (IH g (j + 1) d). replace (j + 1 - d) with (j - d + 1) by lia. lia.
Qed.
Lemma sumF_zero : forall n g j, (forall b, j <= b < j + Z.of_nat n -> g b = 0) -> sumF g j n = 0.
Proof. induction n as [|n IH]; intros g j H; cbn [sumF]; [lia|]. rewrite H by lia. rewrite IH by (intros; apply H; lia). lia. Qed.
(* [comment removed for export] *)
Lemma sumF_single : forall n g j v, j <= v < j + Z.of_nat n -> (forall b, j <= b < j + Z.of_nat n -> b <> v -> g b = 0) ->
  sumF g j n = g v.
Proof.
  induction n as [|n IH]; intros g j v Hv H; cbn [sumF]; [lia|].
  destruct (Z.eq_dec j v) as [->|NE].
  - rewrite sumF_zero by (intros; apply H; lia). lia.
  - rewrite H by lia. rewrite (IH g (j + 1) v) by (try lia; intros; apply H; lia). lia.
Qed.
(* [comment removed for export] *)
Lemma sumF_swap : forall n m (f : Z -> Z -> Z) j k,
  sumF (fun a => sumF (fun b => f a b) k m) j n = sumF (fun b => sumF (fun a => f a b) j n) k m.
Proof.
  induction n as [|n IH]; intros m f j k; cbn [sumF].
  - symmetry. apply sumF_zero. intros; reflexivity.
  - rewrite IH. rewrite <- sumF_addf. apply sumF_ext. intros b Hb. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma hcnt_sumF : forall h n v, 0 <= n -> hcnt h n v = sumF (fun c => ind (zget h c =? v)) 1 (Z.to_nat n).
Proof.
  intros h n v Hn. unfold hcnt. rewrite cntP_sumF. rewrite (sumF_shift (Z.to_nat n) _ 1 1).
  replace (1 - 1) with 0 by lia. apply sumF_ext. intros b Hb. unfold ind. reflexivity.
Qed.
Lemma hcnt_none : forall h n v, (forall z, 1 <= z <= n -> zget h z <> v) -> hcnt h n v = 0.
Proof.
  intros h n v H. pose proof (hcnt_nonneg h n v).
  destruct (Z.eq_dec (hcnt h n v) 0) as [E|NE]; [exact E|]. exfalso.
  cps_destruct (hcnt_ex h n v ltac:(lia)) as (z & Hz & Ez). exact (H z Hz Ez).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition CC (s : hms) : Prop := forall x, 1 <= x -> hcnt (hm_parent s) (hm_nNodes s) x <= 2.

Section CCLoop.
  Variables (A T0 TMAX : Z).
  Hypothesis HA : 2 <= A <= 258.
  Hypothesis HT : T0 + A <= TMAX.
  Hypothesis HTM : TMAX <= 8388607.

  Lemma cc_iter : forall k s, CI A T0 k s -> 1 < hm_nHeap s -> CC s -> CC (hm_combine_iter s).
  Proof.
    intros k s CIs GT C. unfold CC in C.
    pose proof (pop2_facts A T0 HA k s CIs GT) as PF. cbv zeta in PF.
    pose proof (ci_par _ _ _ _ CIs) as PAR. pose proof (ci_nN _ _ _ _ CIs) as NN. pose proof (ci_k _ _ _ _ CIs) as KK.
    set (h := hm_heap s) in *. set (wt := hm_weight s) in *. set (par := hm_parent s) in *.
    set (nH := hm_nHeap s) in *. set (nN := hm_nNodes s) in *.
    set (n1 := zget h 1) in *.
    set (hp1 := downheap (zset h 1 (zget h nH)) wt (nH - 1) 1) in *.
    set (n2 := zget hp1 1) in *.
    cps_destruct PF as (N1R & N1P & N2R & N2P & N12 & _).
    assert (IT : hm_parent (hm_combine_iter s) = zset (zset (zset par n2 (nN + 1)) n1 (nN + 1)) (nN + 1) (-1) /\
                 hm_nNodes (hm_combine_iter s) = nN + 1).
    { unfold hm_combine_iter. fold h wt par nH nN. fold n1 hp1. fold n2. split; reflexivity. }
    destruct IT as [IT1 IT2]. unfold CC. rewrite IT1, IT2. intros x Hx.
    rewrite hcnt_snoc by lia. replace (nN + 1 - 1) with nN by lia. rewrite zget_zset_same.
    replace (-1 =? x) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite (hcnt_ext (zset (zset par n2 (nN + 1)) n1 (nN + 1))).
    2:{ intros z Hz. apply zget_zset_other. lia. }
    rewrite hcnt_upd by lia. rewrite zget_zset_other by congruence. rewrite hcnt_upd by lia.
    rewrite N1P, N2P. replace (-1 =? x) with false by (symmetry; apply Z.eqb_neq; lia).
    destruct (Z.eqb_spec (nN + 1) x) as [<-|NE].
    - rewrite hcnt_none; [lia|]. intros z Hz Ez.
      destruct (Z.eq_dec (zget par z) (-1)) as [E|NE1]; [lia|]. pose proof (PAR z Hz NE1). lia.
    - pose proof (C x Hx). lia.
  Qed.

  Lemma cc_loop : forall fuel k s, CI A T0 k s -> CC s -> CC (hm_combine fuel s).
  Proof.
    induction fuel as [|fuel IH]; intros k s CIs C; cbn [hm_combine]; [exact C|].
    destruct (Z.ltb_spec 1 (hm_nHeap s)) as [GT|LE]; [|exact C].
    apply (IH (k + 1)); [apply (combine_iter_ok A T0 TMAX HA HT HTM); assumption| eapply cc_iter; eassumption].
  Qed.
End CCLoop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint up (par : zarr) (f : nat) (k : Z) : list Z :=
  match f with
  | O => [k]
  | S f' => if 0 <=? zget par k then k :: up par f' (zget par k) else [k]
  end.
Definition mem (x : Z) (l : list Z) : bool := existsb (Z.eqb x) l.
Definition upc (par : zarr) (k : Z) : list Z := up par 600 k.
Definition dep (par : zarr) (k : Z) : Z := hm_depth 600 par k 0.
Arguments upc : simpl never.
Arguments dep : simpl never.

Lemma mem_cons : forall x a l, mem x (a :: l) = ((x =? a) || mem x l)%bool.
Proof. reflexivity. Qed.
Lemma mem_one : forall x a, mem x [a] = (x =? a).
Proof. intros. unfold mem; cbn. apply Bool.orb_false_r. Qed.

(* [comment removed for export] *)
Lemma hm_depth_up : forall par f k j, hm_depth f par k j = j + Z.of_nat (length (up par f k)) - 1.
Proof.
  intros par. induction f as [|f IH]; intros k j; cbn [hm_depth up].
  - cbn [length]. lia.
  - destruct (0 <=? zget par k); [| cbn [length]; lia]. rewrite IH. cbn [length]. lia.
Qed.

(* [comment removed for export] *)
Lemma hm_fill_parent : forall n heap w parent nH i x,
  zget (snd (fst (hm_fill n heap w parent nH i))) x = if ((i <=? x) && (x <? i + Z.of_nat n))%bool then -1 else zget parent x.
Proof.
  induction n as [|n IH]; intros heap w parent nH i x; cbn [hm_fill].
  - cbn [fst snd]. destruct (Z.leb_spec i x), (Z.ltb_spec x (i + Z.of_nat 0%nat)); cbn; try reflexivity. lia.
  - rewrite IH. rewrite zget_zset.
    destruct (Z.leb_spec (i + 1) x), (Z.ltb_spec x (i + 1 + Z.of_nat n)), (Z.eqb_spec x i), (Z.leb_spec i x), (Z.ltb_spec x (i + Z.of_nat (S n)));
      cbn; try reflexivity; lia.
Qed.

Section Tree.
  Variables (A T0 : Z) (c : hms).
  Hypothesis HA : 2 <= A <= 258.
  Hypothesis CIc : CI A T0 (A - 1) c.
  Hypothesis CCc : CC c.
  #[local] Abbreviation par := (hm_parent c).
  #[local] Abbreviation N := (hm_nNodes c).

  Lemma tN : N = 2 * A - 1.
  Proof. exact (d1_nN A T0 c CIc). Qed.
  Lemma t_root : zget par N = -1.
  Proof. exact (last_is_root A T0 c HA CIc). Qed.
  Lemma t_up : forall k, 1 <= k < N -> k < zget par k <= N /\ A < zget par k.
  Proof.
    intros k Hk. destruct (par_cases A T0 c CIc k ltac:(lia)) as [R|X]; [|exact X]. exfalso.
    pose proof (root_is_top A T0 c CIc k ltac:(lia) R) as E1.
    pose proof (root_is_top A T0 c CIc N ltac:(lia) t_root) as E2. lia.
  Qed.

  Lemma up_fuel : forall f g k, 1 <= k <= N -> (Z.to_nat (N - k) < f)%nat -> (Z.to_nat (N - k) < g)%nat ->
    up par f k = up par g k.
  Proof.
    induction f as [|f IH]; intros g k Hk Hf Hg; [lia|]. destruct g as [|g]; [lia|]. cbn [up].
    destruct (Z.leb_spec 0 (zget par k)) as [P|P]; [|reflexivity].
    assert (k <> N) by (intros ->; rewrite t_root in P; lia).
    pose proof (t_up k ltac:(lia)) as [U _]. f_equal. apply IH; lia.
  Qed.

  Lemma upc_root : upc par N = [N].
  Proof.
    unfold upc. change (up par 600 N) with (if 0 <=? zget par N then N :: up par 599 (zget par N) else [N]).
    rewrite t_root. reflexivity.
  Qed.
  Lemma upc_step : forall k, 1 <= k < N -> upc par k = k :: upc par (zget par k).
  Proof.
    intros k Hk. pose proof (t_up k Hk) as [U _]. pose proof tN as TN. unfold upc.
    assert (E : up par 599 (zget par k) = up par 600 (zget par k)) by (apply up_fuel; lia).
    rewrite <- E.
    change (up par 600 k) with (if 0 <=? zget par k then k :: up par 599 (zget par k) else [k]).
    destruct (Z.leb_spec 0 (zget par k)); [reflexivity|lia].
  Qed.
  Lemma upc_head : forall k, 1 <= k <= N -> exists r, upc par k = k :: r.
  Proof.
    intros k Hk. destruct (Z.eq_dec k N) as [->|NE]; [rewrite upc_root; exists []; reflexivity|].
    rewrite upc_step by lia. eexists; reflexivity.
  Qed.
  Lemma mem_upc_self : forall k, 1 <= k <= N -> mem k (upc par k) = true.
  Proof. intros k Hk. destruct (upc_head k Hk) as [r ->]. rewrite mem_cons, Z.eqb_refl. reflexivity. Qed.

  Lemma dep_root : dep par N = 0.
  Proof. unfold dep. rewrite hm_depth_up. change (up par 600 N) with (upc par N). rewrite upc_root. cbn [length]. lia. Qed.
  Lemma dep_step : forall k, 1 <= k < N -> dep par k = dep par (zget par k) + 1.
  Proof.
    intros k Hk. unfold dep. rewrite !hm_depth_up. change (up par 600 k) with (upc par k).
    change (up par 600 (zget par k)) with (upc par (zget par k)). rewrite upc_step by lia. cbn [length]. lia.
  Qed.
  Lemma dep_nonneg : forall k, 0 <= dep par k.
  Proof. intros k. unfold dep. apply hm_depth_ge. Qed.

  (* [comment removed for export] *)
  Lemma upc_range : forall m k x, 1 <= k <= N -> (Z.to_nat (N - k) <= m)%nat -> mem x (upc par k) = true -> k <= x <= N.
  Proof.
    induction m as [|m IH]; intros k x Hk Hm MX.
    - assert (k = N) by lia. subst k. rewrite upc_root, mem_one in MX. apply Z.eqb_eq in MX. lia.
    - destruct (Z.eq_dec k N) as [->|NE].
      + rewrite upc_root, mem_one in MX. apply Z.eqb_eq in MX. lia.
      + pose proof (t_up k ltac:(lia)) as [U _]. rewrite upc_step, mem_cons in MX by lia.
        apply Bool.orb_true_iff in MX. destruct MX as [MX|MX]; [apply Z.eqb_eq in MX; lia|].
        pose proof (IH (zget par k) x ltac:(lia) ltac:(lia) MX). lia.
  Qed.
  Lemma upc_top : forall m k, 1 <= k <= N -> (Z.to_nat (N - k) <= m)%nat -> mem N (upc par k) = true.
  Proof.
    induction m as [|m IH]; intros k Hk Hm.
    - assert (k = N) by lia. subst k. rewrite upc_root, mem_one. apply Z.eqb_refl.
    - destruct (Z.eq_dec k N) as [->|NE]; [rewrite upc_root, mem_one; apply Z.eqb_refl|].
      pose proof (t_up k ltac:(lia)) as [U _]. rewrite upc_step, mem_cons by lia.
      rewrite (IH (zget par k)) by lia. apply Bool.orb_true_r.
  Qed.
  Lemma upc_leaf : forall x i, 1 <= i <= A -> 1 <= x <= A -> mem x (upc par i) = (x =? i).
  Proof.
    intros x i Hi Hx. pose proof tN as TN. pose proof (t_up i ltac:(lia)) as [U UA].
    rewrite upc_step, mem_cons by lia.
    destruct (mem x (upc par (zget par i))) eqn:MX; [|apply Bool.orb_false_r].
    pose proof (upc_range (Z.to_nat N) (zget par i) x ltac:(lia) ltac:(lia) MX). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma upc_split : forall m i x, 1 <= i <= N -> (Z.to_nat (N - i) <= m)%nat -> 1 <= x ->
    sumF (fun c0 => ind ((zget par c0 =? x) && mem c0 (upc par i))) 1 (Z.to_nat N) =
    ind (mem x (upc par i) && negb (x =? i)).
  Proof.
    induction m as [|m IH]; intros i x Hi Hm Hx.
    - assert (i = N) by lia. subst i. rewrite upc_root, mem_one.
      rewrite sumF_zero.
      + destruct (Z.eqb_spec x N); reflexivity.
      + intros b Hb. rewrite mem_one. destruct (Z.eqb_spec b N) as [->|NB]; [rewrite t_root|].
        * replace (-1 =? x) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
        * rewrite Bool.andb_false_r. reflexivity.
    - destruct (Z.eq_dec i N) as [->|NE]; [apply (IH N x); lia|].
      pose proof (t_up i ltac:(lia)) as [U _]. rewrite upc_step by lia.
      assert (NOTIN : mem i (upc par (zget par i)) = false).
      { destruct (mem i (upc par (zget par i))) eqn:MX; [|reflexivity].
        pose proof (upc_range (Z.to_nat N) (zget par i) i ltac:(lia) ltac:(lia) MX). lia. }
      transitivity (sumF (fun c0 => ind ((zget par c0 =? x) && (c0 =? i)) + ind ((zget par c0 =? x) && mem c0 (upc par (zget par i)))) 1 (Z.to_nat N)).
      { apply sumF_ext. intros b Hb. rewrite mem_cons.
        destruct (Z.eqb_spec b i) as [->|NB]; [rewrite NOTIN|]; destruct (zget par _ =? x), (mem _ _); reflexivity. }
      rewrite sumF_addf. rewrite (IH (zget par i) x) by lia.
      rewrite (sumF_single _ _ 1 i) by (try lia; intros b Hb NB; replace (b =? i) with false by (symmetry; apply Z.eqb_neq; lia); destruct (zget par b =? x); reflexivity).
      rewrite Z.eqb_refl, Bool.andb_true_r, mem_cons.
      destruct (Z.eqb_spec x i) as [->|NX].
      + rewrite NOTIN. replace (zget par i =? i) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
      + destruct (Z.eqb_spec (zget par i) x) as [E|NE2].
        * rewrite <- E, mem_upc_self, Z.eqb_refl by lia. reflexivity.
        * replace (x =? zget par i) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. rewrite Bool.andb_true_r.
          destruct (mem x (upc par (zget par i))); reflexivity.
  Qed.

  (* [comment removed for export] *)
  Variable M : Z.
  Hypothesis HM : forall i, 1 <= i <= A -> dep par i <= M.

  Definition TK (x : Z) : Z := sumF (fun i => if mem x (upc par i) then 2 ^ (M + dep par x - dep par i) else 0) 1 (Z.to_nat A).

  Lemma TK_leaf : forall x, 1 <= x <= A -> TK x = 2 ^ M.
  Proof.
    intros x Hx. unfold TK. rewrite (sumF_single _ _ 1 x) by (try lia; intros b Hb NB; rewrite upc_leaf by lia; replace (x =? b) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
    rewrite upc_leaf, Z.eqb_refl by lia. f_equal. lia.
  Qed.

  Lemma TK_node : forall x, A < x <= N -> 2 * TK x = sumF (fun c0 => ind (zget par c0 =? x) * TK c0) 1 (Z.to_nat N).
  Proof.
    intros x Hx. pose proof tN as TN. unfold TK.
    transitivity (2 * sumF (fun i => sumF (fun c0 => ind ((zget par c0 =? x) && mem c0 (upc par i))) 1 (Z.to_nat N) * 2 ^ (M + dep par x - dep par i)) 1 (Z.to_nat A)).
    { f_equal. apply sumF_ext. intros i Hi. rewrite (upc_split (Z.to_nat N)) by lia.
      replace (x =? i) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Bool.andb_true_r.
      destruct (mem x (upc par i)); cbn [ind]; lia. }
    rewrite <- sumF_scal.
    transitivity (sumF (fun i => sumF (fun c0 => ind (zget par c0 =? x) * (if mem c0 (upc par i) then 2 ^ (M + dep par c0 - dep par i) else 0)) 1 (Z.to_nat N)) 1 (Z.to_nat A)).
    2:{ rewrite (sumF_swap (Z.to_nat A) (Z.to_nat N) (fun i c0 => ind (zget par c0 =? x) * (if mem c0 (upc par i) then 2 ^ (M + dep par c0 - dep par i) else 0)) 1 1).
        apply sumF_ext. intros b Hb. cbn beta. rewrite <- sumF_scal. reflexivity. }
    apply sumF_ext. intros i Hi. cbn beta.
    set (P := 2 ^ (M + dep par x - dep par i)).
    transitivity (sumF (fun c0 => (2 * P) * ind ((zget par c0 =? x) && mem c0 (upc par i))) 1 (Z.to_nat N)).
    { rewrite sumF_scal. ring. }
    apply sumF_ext. intros b Hb. cbn beta. subst P.
    destruct (Z.eqb_spec (zget par b) x) as [E|NE]; cbn [ind andb]; [|lia].
    destruct (mem b (upc par i)) eqn:MB; cbn [ind]; [|lia].
    assert (b <> N) by (intros ->; rewrite t_root in E; lia).
    rewrite (dep_step b) by lia. rewrite E.
    pose proof (HM i ltac:(lia)). pose proof (dep_nonneg x).
    replace (M + (dep par x + 1) - dep par i) with (Z.succ (M + dep par x - dep par i)) by lia. rewrite Z.pow_succ_r by lia. lia.
  Qed.

  Lemma TK_bound : forall m x, 1 <= x <= N -> (Z.to_nat x <= m)%nat -> TK x <= 2 ^ M.
  Proof.
    induction m as [|m IH]; intros x Hx Hm; [lia|].
    destruct (Z.le_gt_cases x A) as [LE|GT]; [rewrite TK_leaf by lia; lia|].
    pose proof (TK_node x ltac:(lia)) as E.
    assert (B : sumF (fun c0 => ind (zget par c0 =? x) * TK c0) 1 (Z.to_nat N) <= sumF (fun c0 => 2 ^ M * ind (zget par c0 =? x)) 1 (Z.to_nat N)).
    { apply sumF_lef. intros b Hb. destruct (Z.eqb_spec (zget par b) x) as [EQ|NE]; cbn [ind]; [|lia].
      assert (b <> N) by (intros ->; rewrite t_root in EQ; lia).
      pose proof (t_up b ltac:(lia)) as [U _]. pose proof (IH b ltac:(lia) ltac:(lia)). lia. }
    rewrite sumF_scal, <- hcnt_sumF in B by lia. pose proof (CCc x ltac:(lia)) as C2.
    assert (0 <= 2 ^ M) by (apply Z.pow_nonneg; lia). nia.
  Qed.

  Theorem kraft_tree : sumF (fun i => 2 ^ (M - dep par i)) 1 (Z.to_nat A) <= 2 ^ M.
  Proof.
    pose proof tN as TN.
    pose proof (TK_bound (Z.to_nat N) N ltac:(lia) ltac:(lia)) as B. unfold TK in B.
    rewrite (sumF_ext (Z.to_nat A) _ (fun i => 2 ^ (M - dep par i))) in B; [exact B|].
    intros i Hi. rewrite (upc_top (Z.to_nat N)) by lia. rewrite dep_root. f_equal. lia.
  Qed.
End Tree.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section KRounds.
  Variables (A TMAX lb : Z).
  Hypothesis HA : 2 <= A <= 258.
  Hypothesis HTM : 774 <= TMAX <= 8388607.

  (* [comment removed for export] *)
  Definition kraft17 (len : zarr) : Prop := sumF (fun k => 2 ^ (17 - zget len k)) lb (Z.to_nat A) <= 2 ^ 17.

  Lemma round_kraft : forall s, LW (hs_weight s) A -> TS (hs_weight s) A + A <= TMAX ->
    let s' := hm_round A 17 lb s in hs_done s' = true -> kraft17 (hs_len s').
  Proof.
    intros s L HT. cbv zeta. unfold hm_round.
    pose proof (start_CI A TMAX (hs_weight s) (hs_heap s) (hs_parent s) HA L HT ltac:(lia)) as SC. cbv zeta in SC.
    pose proof (fun z => hm_fill_parent (Z.to_nat A) (zset (hs_heap s) 0 0) (zset (hs_weight s) 0 0) (zset (hs_parent s) 0 (-2)) 0 1 z) as PF.
    destruct (hm_fill (Z.to_nat A) (zset (hs_heap s) 0 0) (zset (hs_weight s) 0 0) (zset (hs_parent s) 0 (-2)) 0 1) as [[heap parent] nHeap].
    cbn [fst snd] in SC, PF. destruct SC as [-> CI0].
    assert (CC0 : CC (HMS heap (zset (hs_weight s) 0 0) parent A A)).
    { unfold CC; cbn [hm_parent hm_nNodes]. intros x Hx. rewrite hcnt_none; [lia|].
      intros z Hz. rewrite PF. destruct (Z.leb_spec 1 z), (Z.ltb_spec z (1 + Z.of_nat (Z.to_nat A))); cbn; lia. }
    pose proof (combine_loop A (TS (hs_weight s) A) TMAX HA HT ltac:(lia) (Z.to_nat A) 0 _ CI0 ltac:(cbn [hm_nHeap]; lia)) as CL.
    cbv zeta in CL. cps_destruct CL as (CIf & NH1 & WP).
    pose proof (cc_loop A (TS (hs_weight s) A) TMAX HA HT ltac:(lia) (Z.to_nat A) 0 _ CI0 CC0) as CCf.
    set (c := hm_combine (Z.to_nat A) _) in *.
    pose proof (hm_lens_spec (Z.to_nat A) (hs_len s) (hm_parent c) lb 17 1 false) as LS. cbv zeta in LS.
    destruct (hm_lens (Z.to_nat A) (hs_len s) (hm_parent c) lb 17 1 false) as [len tooLong].
    cbn [fst snd] in LS. cps_destruct LS as (V & F & T).
    destruct tooLong; cbn [hs_len hs_done]; [intros; discriminate|]. intros _.
    destruct (T eq_refl) as [_ D]. unfold kraft17.
    rewrite (sumF_shift (Z.to_nat A) _ lb (lb - 1)). replace (lb - (lb - 1)) with 1 by lia.
    rewrite (sumF_ext (Z.to_nat A) _ (fun i => 2 ^ (17 - dep (hm_parent c) i))).
    - apply (kraft_tree A (TS (hs_weight s) A) c HA CIf CCf 17). intros i Hi. unfold dep. apply D. lia.
    - intros b Hb. replace (b + (lb - 1)) with (lb + b - 1) by lia. rewrite V by lia.
      pose proof (D b ltac:(lia)). pose proof (hm_depth_ge 600 (hm_parent c) b 0).
      rewrite Z.mod_small by lia. reflexivity.
  Qed.

  Lemma rounds_kraft : forall f s, LW (hs_weight s) A -> TS (hs_weight s) A + A <= TMAX ->
    (hs_done s = true -> kraft17 (hs_len s)) ->
    let s' := hm_rounds f A 17 lb s in hs_done s' = true -> kraft17 (hs_len s').
  Proof.
    induction f as [|f IH]; intros s L HT D; cbv zeta.
    - cbn [hm_rounds]. exact D.
    - cbn [hm_rounds]. destruct (hs_done s) eqn:DS; [intros _; apply D; reflexivity|].
      pose proof (round_spec A TMAX lb HA HTM s L HT) as [R1 R2]. cbv zeta in R1, R2.
      pose proof (round_kraft s L HT) as K1. cbv zeta in K1.
      set (s1 := hm_round A 17 lb s) in *.
      destruct (hs_done s1) eqn:DS1.
      + rewrite (rounds_done_stay A lb f s1 DS1). intros _. apply K1. reflexivity.
      + destruct (R2 eq_refl) as [L1 T1].
        assert (HT1 : TS (hs_weight s1) A + A <= TMAX).
        { assert (TS (hs_weight s) A / 2 <= (TMAX - A) / 2) by (apply Z.div_le_mono; lia).
          assert ((TMAX - A) / 2 <= TMAX - 2 * A) by (apply Z.div_le_upper_bound; lia). lia. }
        apply (IH s1 L1 HT1). intros E. rewrite DS1 in E. discriminate.
  Qed.

  Theorem hbMakeCodeLengths_kraft : forall len freq heap0 weight0 parent0 fb,
    (forall i, 0 <= i < A -> 0 <= zget freq (fb + i)) ->
    sumF (fun i => Z.max (zget freq (fb + (i - 1))) 1) 1 (Z.to_nat A) + A <= TMAX ->
    kraft17 (hs_len (hbMakeCodeLengths len freq heap0 weight0 parent0 lb fb A 17)).
  Proof.
    intros len freq heap0 weight0 parent0 fb FNN FS.
    pose proof (hbMakeCodeLengths_done A TMAX lb HA HTM len freq heap0 weight0 parent0 fb FNN FS) as DN.
    unfold hbMakeCodeLengths in *.
    destruct (hm_winit_spec (Z.to_nat A) weight0 freq fb 0) as [W1 W2].
    set (W := hm_winit (Z.to_nat A) weight0 freq fb 0) in *.
    assert (WV : forall i, 1 <= i <= A -> zget W i = 256 * Z.max (zget freq (fb + (i - 1))) 1).
    { intros i Hi. replace i with (i - 1 + 1) at 1 by lia. rewrite W1 by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
      pose proof (FNN (i - 1) ltac:(lia)). destruct (Z.eqb_spec (zget freq (fb + (i - 1))) 0); lia. }
    assert (L : LW W A).
    { intros i Hi. exists (Z.max (zget freq (fb + (i - 1))) 1). split; [lia| apply WV; exact Hi]. }
    assert (T : TS W A = sumF (fun i => Z.max (zget freq (fb + (i - 1))) 1) 1 (Z.to_nat A)).
    { unfold TS. apply sumF_ext. intros b Hb. rewrite WV by lia. unfold tw. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. }
    pose proof (rounds_kraft 40 (HMST len heap0 W parent0 false)) as RS. cbn [hs_weight hs_len hs_done] in RS.
    apply (RS L ltac:(lia) ltac:(intros; discriminate) DN).
  Qed.
End KRounds.
