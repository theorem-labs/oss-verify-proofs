From Stdlib Require Import ZArith List Bool Lia Arith Permutation.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require SlotSizes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Reusable Require Import YO0i YO0f.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import AllocPack Contract.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar PjGrowUp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import Ledger ReaderRes PackVec PackBand.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterSpec WriterApp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import TxCalls.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import WriterRet put_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import WriterValue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import PjWriteHyp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import pj_set_c round_trip_text_c check_round_trip_c check_no_overread_c check_reject_clean_starved_c EntryDefs EntrySR.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require RttModel RttStgCmp check_round_trip_m CrsRoom PjWriteAdapt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog.CF Require Import SRCF.
Import ListNotations.
Local Open Scope Z_scope.

Lemma pk_zupd_len : forall l i v, length (zupd l i v) = length l.
Proof.
  induction l as [|h t IH]; intros [|i] v; cbn [zupd length]; try reflexivity. rewrite IH. reflexivity.
Qed.

Lemma pk_zupd_nth : forall l i v k, (k < length l)%nat -> nth k (zupd l i v) 0 = if Nat.eqb i k then v else nth k l 0.
Proof.
  induction l as [|h t IH]; intros i v k Hk; cbn [length] in Hk; [lia|].
  destruct i as [|i]; destruct k as [|k]; cbn [zupd nth Nat.eqb]; try reflexivity.
  apply IH. lia.
Qed.

Definition pk_bn (k n : Z) : Z := if Nat.eqb (Z.to_nat (band n)) (Z.to_nat k) then 1 else 0.

Lemma pk_bn_bi : forall k n, 0 <= k -> 0 <= n -> pk_bn k n = pq_bi k n.
Proof.
  intros k n Hk Hn. unfold pk_bn, pq_bi. pose proof (band_nonneg n Hn).
  destruct (Nat.eqb_spec (Z.to_nat (band n)) (Z.to_nat k)) as [E|E];
    destruct (Z.eqb_spec (band n) k) as [E'|E']; lia.
Qed.

Lemma pk_ltb_mono : forall a b, 0 <= a <= b -> (band b <? band a) = false.
Proof. intros a b H. apply Z.ltb_ge. apply band_mono. exact H. Qed.

Lemma pk_lv_len : forall L j d, length (lv_add L j d) = length L.
Proof. intros L j d. unfold lv_add, zset. apply pk_zupd_len. Qed.

Lemma pk_lv_add : forall L j d k, length L = 49%nat -> 0 <= k < 49 ->
  znth k (lv_add L j d) = znth k L + (if Nat.eqb (Z.to_nat j) (Z.to_nat k) then d else 0).
Proof.
  intros L j d k HL Hk. unfold lv_add, zset, znth.
  rewrite pk_zupd_nth by lia.
  destruct (Nat.eqb_spec (Z.to_nat j) (Z.to_nat k)) as [E|E]; [rewrite E; lia | lia].
Qed.

Lemma pk_list_ext : forall l1 l2, length l1 = 49%nat -> length l2 = 49%nat ->
  (forall k, 0 <= k < 49 -> znth k l1 = znth k l2) -> l1 = l2.
Proof.
  intros l1 l2 H1 H2 H. apply nth_ext with (d := 0) (d' := 0); [lia|]. intros n Hn.
  specialize (H (Z.of_nat n) ltac:(lia)). unfold znth in H. rewrite Nat2Z.id in H. exact H.
Qed.

Lemma pk_eq_of : forall b b', length (pb_live b) = 49%nat -> length (pb_live b') = 49%nat ->
  (forall k, 0 <= k < 49 -> znth k (pb_live b') = znth k (pb_live b)) ->
  pb_bytes b' = pb_bytes b -> pb_cap b' = pb_cap b -> b' = b.
Proof.
  intros [l y c] [l' y' c'] H1 H2 H Hy Hc. cbn [pb_live pb_bytes pb_cap] in *. subst y' c'.
  f_equal. apply pk_list_ext; assumption.
Qed.

Definition pk_at (b' b : pbound) (V : Z -> Z) (y : Z) : Prop :=
  length (pb_live b') = 49%nat /\ (forall k, 0 <= k < 49 -> znth k (pb_live b') = znth k (pb_live b) + V k) /\
  pb_bytes b' = pb_bytes b + y /\ pb_cap b' = pb_cap b.

Lemma pk_at_refl : forall b, length (pb_live b) = 49%nat -> pk_at b b (fun _ => 0) 0.
Proof. intros b HL. split; [exact HL|]. split; [intros k Hk; cbv beta; lia|]. split; [lia | reflexivity]. Qed.

Lemma pk_at_ext : forall b' b V W y z, pk_at b' b V y -> (forall k, 0 <= k < 49 -> V k = W k) -> y = z ->
  pk_at b' b W z.
Proof.
  intros b' b V W y z (H1 & H2 & H3 & H4) HV Hy. split; [exact H1|]. split; [|split; [lia | exact H4]].
  intros k Hk. rewrite H2 by exact Hk. rewrite HV by exact Hk. reflexivity.
Qed.

Lemma pk_at_trans : forall b1 b2 b3 V1 V2 y1 y2, pk_at b2 b1 V1 y1 -> pk_at b3 b2 V2 y2 ->
  pk_at b3 b1 (fun k => V1 k + V2 k) (y1 + y2).
Proof.
  intros b1 b2 b3 V1 V2 y1 y2 (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4). split; [exact B1|].
  split; [|split; [lia | congruence]]. intros k Hk. rewrite B2 by exact Hk. rewrite A2 by exact Hk. cbv beta. lia.
Qed.

Lemma pk_at_len : forall b' b V y, pk_at b' b V y -> length (pb_live b') = 49%nat.
Proof. intros b' b V y H. exact (proj1 H). Qed.

Lemma pk_at_zero : forall b b' V y, length (pb_live b) = 49%nat -> pk_at b' b V y ->
  (forall k, 0 <= k < 49 -> V k = 0) -> y = 0 -> b' = b.
Proof.
  intros b b' V y HL (H1 & H2 & H3 & H4) HV Hy. apply pk_eq_of; [exact HL | exact H1 | | lia | exact H4].
  intros k Hk. rewrite H2 by exact Hk. rewrite HV by exact Hk. lia.
Qed.

Lemma pk_at_same : forall b x x' V V' y y', pk_at x b V y -> pk_at x' b V' y' ->
  (forall k, 0 <= k < 49 -> V k = V' k) -> y = y' -> x = x'.
Proof.
  intros b x x' V V' y y' (A1 & A2 & A3 & A4) (B1 & B2 & B3 & B4) HV Hy.
  symmetry. apply pk_eq_of; [exact A1 | exact B1 | | lia | congruence].
  intros k Hk. rewrite A2, B2 by exact Hk. rewrite HV by exact Hk. reflexivity.
Qed.

Lemma pk_form_malloc : forall (b : pbound) n, rf_malloc pack_form b n = pb_malloc b n.
Proof. reflexivity. Qed.

Lemma pk_form_free : forall (b : pbound) n, rf_free pack_form b n = pb_free b n.
Proof. reflexivity. Qed.

Lemma pk_form_realloc : forall (b : pbound) k n, rf_realloc pack_form b k n = pb_realloc b k n.
Proof. reflexivity. Qed.

Lemma pk_malloc_at : forall b n, length (pb_live b) = 49%nat ->
  pk_at (rf_malloc pack_form b n) b (fun k => pk_bn k n) n.
Proof.
  intros b n HL. rewrite pk_form_malloc. unfold pk_at, pb_malloc. cbn [pb_live pb_bytes pb_cap].
  split; [rewrite pk_lv_len; exact HL|]. split; [|split; [lia | reflexivity]].
  intros k Hk. rewrite pk_lv_add by assumption. unfold pk_bn. destruct (Nat.eqb (Z.to_nat (band n)) (Z.to_nat k)); lia.
Qed.

Lemma pk_free_at : forall b n, length (pb_live b) = 49%nat ->
  pk_at (rf_free pack_form b n) b (fun k => - pk_bn k n) (- n).
Proof.
  intros b n HL. rewrite pk_form_free. unfold pk_at, pb_free. cbn [pb_live pb_bytes pb_cap].
  split; [rewrite pk_lv_len; exact HL|]. split; [|split; [lia | reflexivity]].
  intros k Hk. rewrite pk_lv_add by assumption. unfold pk_bn. destruct (Nat.eqb (Z.to_nat (band n)) (Z.to_nat k)); lia.
Qed.

Lemma pk_realloc_at : forall b m n, length (pb_live b) = 49%nat ->
  pk_at (rf_realloc pack_form b m n) b
    (fun k => if band n <? band m then pk_bn k n else pk_bn k n - pk_bn k m) (n - m).
Proof.
  intros b m n HL. rewrite pk_form_realloc. unfold pk_at, pb_realloc, lv_realloc. cbn [pb_live pb_bytes pb_cap].
  destruct (band n <? band m).
  - split; [rewrite pk_lv_len; exact HL|]. split; [|split; [lia | reflexivity]].
    intros k Hk. rewrite pk_lv_add by assumption. unfold pk_bn. destruct (Nat.eqb (Z.to_nat (band n)) (Z.to_nat k)); lia.
  - split; [rewrite !pk_lv_len; exact HL|]. split; [|split; [lia | reflexivity]].
    intros k Hk. rewrite pk_lv_add by (try rewrite pk_lv_len; assumption).
    rewrite pk_lv_add by assumption. unfold pk_bn.
    destruct (Nat.eqb (Z.to_nat (band n)) (Z.to_nat k)); destruct (Nat.eqb (Z.to_nat (band m)) (Z.to_nat k)); lia.
Qed.

Lemma pk_rf_run_cons : forall F b e tr, rf_run F b (e :: tr) = rf_run F (rf_ev F b e) tr.
Proof. reflexivity. Qed.

Lemma pk_rf_frees_cons : forall F b ak D, rf_frees F b (ak :: D) = rf_frees F (rf_free F b (snd ak + 16)) D.
Proof. reflexivity. Qed.

Lemma pk_ev_at : forall b e, length (pb_live b) = 49%nat ->
  pk_at (rf_ev pack_form b e) b (fun k => pq_ev k e) (held_ev e + 16 * nlive_ev e).
Proof.
  intros b e HL. destruct e as [n|[|m] n|n|n]; cbn [rf_ev nlive_ev held_ev].
  - apply (pk_at_ext _ _ _ _ _ _ (pk_malloc_at b (Z.of_nat n + 16) HL)); [|lia].
    intros k Hk. cbn [pq_ev]. apply pk_bn_bi; lia.
  - unfold rf_grow. change (Z.of_nat 0) with 0. rewrite Z.eqb_refl.
    apply (pk_at_ext _ _ _ _ _ _ (pk_malloc_at b (Z.of_nat n + 16) HL)); [|lia].
    intros k Hk. cbn [pq_ev Nat.eqb]. apply pk_bn_bi; lia.
  - unfold rf_grow. rewrite (proj2 (Z.eqb_neq (Z.of_nat (S m)) 0)) by lia.
    apply (pk_at_ext _ _ _ _ _ _ (pk_realloc_at b (Z.of_nat (S m) + 16) (Z.of_nat n + 16) HL)); [|lia].
    intros k Hk. cbn [pq_ev Nat.eqb]. rewrite !pk_bn_bi by lia. reflexivity.
  - apply (pk_at_ext _ _ _ _ _ _ (pk_at_refl b HL)); [|lia]. intros k Hk. reflexivity.
  - apply (pk_at_ext _ _ _ _ _ _ (pk_free_at b (Z.of_nat n + 16) HL)); [|lia].
    intros k Hk. cbn [pq_ev]. rewrite pk_bn_bi by lia. reflexivity.
Qed.

Lemma pk_run_at : forall tr b, length (pb_live b) = 49%nat ->
  pk_at (rf_run pack_form b tr) b (fun k => pq_run k tr) (held tr + 16 * nlive tr).
Proof.
  induction tr as [|e tr IH]; intros b HL.
  - apply (pk_at_ext _ _ _ _ _ _ (pk_at_refl b HL)); [|cbn [held nlive]; lia]. intros k Hk. reflexivity.
  - rewrite pk_rf_run_cons. pose proof (pk_ev_at b e HL) as H1. pose proof (IH _ (pk_at_len _ _ _ _ H1)) as H2.
    apply (pk_at_ext _ _ _ _ _ _ (pk_at_trans _ _ _ _ _ _ _ H1 H2)); [|cbn [held nlive]; lia].
    intros k Hk. reflexivity.
Qed.

Theorem pk_run : forall b tr, length (pb_live b) = 49%nat ->
  length (pb_live (rf_run pack_form b tr)) = 49%nat /\
  (forall k, 0 <= k < 49 -> znth k (pb_live (rf_run pack_form b tr)) = znth k (pb_live b) + pq_run k tr) /\
  pb_bytes (rf_run pack_form b tr) = pb_bytes b + held tr + 16 * nlive tr /\
  pb_cap (rf_run pack_form b tr) = pb_cap b.
Proof.
  intros b tr HL. destruct (pk_run_at tr b HL) as (A & B & C & D).
  split; [exact A|]. split; [exact B|]. split; [lia | exact D].
Qed.

Lemma pk_frees_at : forall D b, length (pb_live b) = 49%nat -> Forall (fun ak => 0 <= snd ak) D ->
  pk_at (rf_frees pack_form b D) b (fun k => pq_frees k D) (- lsum D - 16 * Z.of_nat (length D)).
Proof.
  induction D as [|[a n] D IH]; intros b HL HF.
  - apply (pk_at_ext _ _ _ _ _ _ (pk_at_refl b HL)); [|cbn [lsum length]; lia]. intros k Hk. reflexivity.
  - apply Forall_cons_iff in HF as [Hn HF]. cbn [snd] in Hn.
    rewrite pk_rf_frees_cons. cbn [snd]. pose proof (pk_free_at b (n + 16) HL) as H1.
    pose proof (IH _ (pk_at_len _ _ _ _ H1) HF) as H2.
    apply (pk_at_ext _ _ _ _ _ _ (pk_at_trans _ _ _ _ _ _ _ H1 H2)); [|cbn [lsum length]; lia].
    intros k Hk. cbn [pq_frees snd]. rewrite pk_bn_bi by lia. lia.
Qed.

Theorem pk_frees : forall b D, length (pb_live b) = 49%nat -> Forall (fun ak => 0 <= snd ak) D ->
  length (pb_live (rf_frees pack_form b D)) = 49%nat /\
  (forall k, 0 <= k < 49 -> znth k (pb_live (rf_frees pack_form b D)) = znth k (pb_live b) + pq_frees k D) /\
  pb_bytes (rf_frees pack_form b D) = pb_bytes b - lsum D - 16 * Z.of_nat (length D) /\
  pb_cap (rf_frees pack_form b D) = pb_cap b.
Proof.
  intros b D HL HF. destruct (pk_frees_at D b HL HF) as (A & B & C & E).
  split; [exact A|]. split; [exact B|]. split; [lia | exact E].
Qed.

Lemma pkA_malloc : forall b b' V y n, pk_at b' b V y ->
  pk_at (rf_malloc pack_form b' n) b (fun k => V k + pk_bn k n) (y + n).
Proof. intros b b' V y n H. exact (pk_at_trans _ _ _ _ _ _ _ H (pk_malloc_at b' n (pk_at_len _ _ _ _ H))). Qed.

Lemma pkA_free : forall b b' V y n, pk_at b' b V y ->
  pk_at (rf_free pack_form b' n) b (fun k => V k + - pk_bn k n) (y + - n).
Proof. intros b b' V y n H. exact (pk_at_trans _ _ _ _ _ _ _ H (pk_free_at b' n (pk_at_len _ _ _ _ H))). Qed.

Lemma pkA_realloc : forall b b' V y m n, pk_at b' b V y ->
  pk_at (rf_realloc pack_form b' m n) b
    (fun k => V k + (if band n <? band m then pk_bn k n else pk_bn k n - pk_bn k m)) (y + (n - m)).
Proof. intros b b' V y m n H. exact (pk_at_trans _ _ _ _ _ _ _ H (pk_realloc_at b' m n (pk_at_len _ _ _ _ H))). Qed.

Lemma pkA_run : forall b b' V y tr, pk_at b' b V y ->
  pk_at (rf_run pack_form b' tr) b (fun k => V k + pq_run k tr) (y + (held tr + 16 * nlive tr)).
Proof. intros b b' V y tr H. exact (pk_at_trans _ _ _ _ _ _ _ H (pk_run_at tr b' (pk_at_len _ _ _ _ H))). Qed.

Lemma pkA_frees : forall b b' V y D, pk_at b' b V y -> Forall (fun ak => 0 <= snd ak) D ->
  pk_at (rf_frees pack_form b' D) b (fun k => V k + pq_frees k D) (y + (- lsum D - 16 * Z.of_nat (length D))).
Proof.
  intros b b' V y D H HF. exact (pk_at_trans _ _ _ _ _ _ _ H (pk_frees_at D b' (pk_at_len _ _ _ _ H) HF)).
Qed.

Definition pk_cnt (k : Z) (s : list nat) : Z := zl (map (fun x => pq_bi k (Z.of_nat x + 16)) s).

Lemma pk_rm1 : forall (f : nat -> Z) x s, In x s -> zl (map f (rm1n x s)) + f x = zl (map f s).
Proof.
  intros f x s. induction s as [|y s IH]; intros H; [destruct H|].
  cbn [rm1n]. destruct (Nat.eqb_spec y x) as [->|Hne]; cbn [map zl]; [lia|].
  destruct H as [H|H]; [congruence|]. specialize (IH H). lia.
Qed.

Lemma pk_hit : forall x s t, Z.of_nat (length (t :: rm1n x s)) = Z.of_nat (length s) + 0 -> In x s.
Proof.
  intros x s t H. destruct (in_dec Nat.eq_dec x s) as [Hi|Hi]; [exact Hi|].
  rewrite (rm1_miss _ _ Hi) in H. cbn [length] in H. lia.
Qed.

Lemma pk_hit1 : forall x s, Z.of_nat (length (rm1n x s)) = Z.of_nat (length s) + -1 -> In x s.
Proof.
  intros x s H. destruct (in_dec Nat.eq_dec x s) as [Hi|Hi]; [exact Hi|].
  rewrite (rm1_miss _ _ Hi) in H. lia.
Qed.

Lemma pk_cnt_ev : forall k s e, (forall m n, e = EGrow m n -> (m < n)%nat) ->
  Z.of_nat (length (lsz_ev s e)) = Z.of_nat (length s) + nlive_ev e ->
  pk_cnt k (lsz_ev s e) = pk_cnt k s + pq_ev k e.
Proof.
  intros k s e HG HL. unfold pk_cnt.
  destruct e as [n|[|m] n|n|n]; cbn [lsz_ev nlive_ev pq_ev Nat.eqb] in *; cbn [map zl].
  - lia.
  - lia.
  - pose proof (HG (S m) n eq_refl) as Hmn. pose proof (pk_hit _ _ _ HL) as Hi.
    pose proof (pk_rm1 (fun x => pq_bi k (Z.of_nat x + 16)) (S m) s Hi) as R. cbv beta in R.
    rewrite (pk_ltb_mono (Z.of_nat (S m) + 16) (Z.of_nat n + 16)) by lia. lia.
  - lia.
  - pose proof (pk_hit1 _ _ HL) as Hi.
    pose proof (pk_rm1 (fun x => pq_bi k (Z.of_nat x + 16)) n s Hi) as R. cbv beta in R. lia.
Qed.

Lemma pk_cnt_fold : forall tr s k, grow_up tr ->
  Z.of_nat (length (fold_left lsz_ev tr s)) = Z.of_nat (length s) + nlive tr ->
  pk_cnt k (fold_left lsz_ev tr s) = pk_cnt k s + pq_run k tr.
Proof.
  induction tr as [|e tr IH]; intros s k HG H; cbn [fold_left nlive pq_run] in *; [lia|].
  pose proof (lsz_ev_ge s e) as G1. pose proof (lszf_ge tr (lsz_ev s e)) as G2.
  assert (E1 : Z.of_nat (length (lsz_ev s e)) = Z.of_nat (length s) + nlive_ev e) by lia.
  assert (E2 : Z.of_nat (length (fold_left lsz_ev tr (lsz_ev s e))) = Z.of_nat (length (lsz_ev s e)) + nlive tr)
    by lia.
  assert (HG1 : forall m n, e = EGrow m n -> (m < n)%nat).
  { intros m n ->. apply (HG m n). left. reflexivity. }
  assert (HG2 : grow_up tr) by (intros m n Hi; apply (HG m n); right; exact Hi).
  rewrite (IH _ k HG2 E2), (pk_cnt_ev k s e HG1 E1). lia.
Qed.

Lemma pk_frees_zl : forall D k, pq_frees k D = - zl (map (fun z => pq_bi k (z + 16)) (map snd D)).
Proof. induction D as [|ak D IH]; intros k; cbn [pq_frees map zl]; [lia | rewrite IH; lia]. Qed.

Lemma pk_cancel_v : forall tr D, grow_up tr -> Permutation (map snd D) (map Z.of_nat (lsz tr)) ->
  Z.of_nat (length D) = nlive tr ->
  (forall k, pq_run k tr + pq_frees k D = 0) /\
  held tr + 16 * nlive tr - lsum D - 16 * Z.of_nat (length D) = 0 /\ Forall (fun ak => 0 <= snd ak) D.
Proof.
  intros tr D HG HP HN.
  assert (HLz : Z.of_nat (length (lsz tr)) = nlive tr).
  { rewrite <- HN, <- (length_map Z.of_nat (lsz tr)), <- (Permutation_length HP), length_map. reflexivity. }
  split; [|split].
  - intros k. rewrite pk_frees_zl.
    rewrite (zl_perm _ _ (Permutation_map (fun z => pq_bi k (z + 16)) HP)), map_map. cbv beta.
    pose proof (pk_cnt_fold tr [] k HG ltac:(unfold lsz in HLz; cbn [length]; lia)) as E.
    unfold pk_cnt in E. cbn [map zl] in E. unfold lsz. lia.
  - pose proof (lsz_counts D tr HP HN). lia.
  - apply Forall_forall. intros ak Hin. apply (in_map snd) in Hin. apply (Permutation_in _ HP) in Hin.
    apply in_map_iff in Hin. destruct Hin as (x & Hx & _). lia.
Qed.

Theorem pk_cancel : forall b tr D, length (pb_live b) = 49%nat -> grow_up tr ->
  Permutation (map snd D) (map Z.of_nat (lsz tr)) -> Z.of_nat (length D) = nlive tr ->
  rf_frees pack_form (rf_run pack_form b tr) D = b.
Proof.
  intros b tr D HL HG HP HN. destruct (pk_cancel_v tr D HG HP HN) as (C1 & C2 & C3).
  pose proof (pkA_frees _ _ _ _ D (pk_run_at tr b HL) C3) as H.
  apply (pk_at_zero _ _ _ _ HL H); [intros k Hk; cbv beta; specialize (C1 k); lia | lia].
Qed.

Definition pk_ind (k c : Z) : Z := if c =? 0 then 0 else pq_bi k (c + 16).
Definition pk_indb (c : Z) : Z := if c =? 0 then 0 else c + 16.
Definition pk_indr (k c : Z) : Z := if c =? 0 then 0 else pq_bi k c.
Definition pk_indrb (c : Z) : Z := if c =? 0 then 0 else c.

Lemma pk_ind_0 : forall k, pk_ind k 0 = 0.
Proof. reflexivity. Qed.

Lemma pk_indb_0 : pk_indb 0 = 0.
Proof. reflexivity. Qed.

Lemma pk_indr_0 : forall k, pk_indr k 0 = 0.
Proof. reflexivity. Qed.

Lemma pk_indrb_id : forall c, pk_indrb c = c.
Proof. intros c. unfold pk_indrb. destruct (Z.eqb_spec c 0); lia. Qed.

Lemma pk_ind_nz : forall k c, c <> 0 -> pk_ind k c = pq_bi k (c + 16).
Proof. intros k c H. unfold pk_ind. rewrite (proj2 (Z.eqb_neq c 0) H). reflexivity. Qed.

Lemma pk_indb_nz : forall c, c <> 0 -> pk_indb c = c + 16.
Proof. intros c H. unfold pk_indb. rewrite (proj2 (Z.eqb_neq c 0) H). reflexivity. Qed.

Lemma pk_indr_nz : forall k c, c <> 0 -> pk_indr k c = pq_bi k c.
Proof. intros k c H. unfold pk_indr. rewrite (proj2 (Z.eqb_neq c 0) H). reflexivity. Qed.

Lemma pk_w_cap_w0 : forall c f, w_cap (w0 c f) = 0.
Proof. reflexivity. Qed.

Lemma pk_wnext_at : forall b st bs, length (pb_live b) = 49%nat -> 0 <= w_cap st ->
  pk_at (wnext pack_form b st bs) b (fun k => pk_ind k (w_cap (put1 st bs)) - pk_ind k (w_cap st))
    (pk_indb (w_cap (put1 st bs)) - pk_indb (w_cap st)).
Proof.
  intros b st bs HL Hc. pose proof (put1_cap st bs Hc) as Hle. unfold wnext.
  destruct (Z.eqb_spec (w_cap (put1 st bs)) (w_cap st)) as [E|N].
  - rewrite E. apply (pk_at_ext _ _ _ _ _ _ (pk_at_refl b HL)); [intros k Hk; cbv beta; lia | lia].
  - unfold wstep. destruct (Z.eqb_spec (w_cap st) 0) as [C0|Cn].
    + apply (pk_at_ext _ _ _ _ _ _ (pk_malloc_at b (w_cap (put1 st bs) + 16) HL)).
      * intros k Hk. cbv beta. rewrite C0, pk_ind_0, (pk_ind_nz k (w_cap (put1 st bs))) by lia.
        rewrite pk_bn_bi by lia. lia.
      * rewrite C0, pk_indb_0, (pk_indb_nz (w_cap (put1 st bs))) by lia. lia.
    + apply (pk_at_ext _ _ _ _ _ _ (pk_realloc_at b (w_cap st + 16) (w_cap (put1 st bs) + 16) HL)).
      * intros k Hk. cbv beta. rewrite (pk_ind_nz k (w_cap (put1 st bs))) by lia.
        rewrite (pk_ind_nz k (w_cap st)) by lia.
        rewrite (pk_ltb_mono (w_cap st + 16) (w_cap (put1 st bs) + 16)) by lia.
        rewrite !pk_bn_bi by lia. reflexivity.
      * rewrite (pk_indb_nz (w_cap (put1 st bs))) by lia. rewrite (pk_indb_nz (w_cap st)) by lia. lia.
Qed.

Lemma pk_wfold_at : forall P b st, length (pb_live b) = 49%nat -> 0 <= w_cap st ->
  pk_at (wfold pack_form b st P) b (fun k => pk_ind k (w_cap (putN st P)) - pk_ind k (w_cap st))
    (pk_indb (w_cap (putN st P)) - pk_indb (w_cap st)).
Proof.
  induction P as [|bs P IH]; intros b st HL Hc.
  - cbn [wfold]. rewrite putN_nil. apply (pk_at_ext _ _ _ _ _ _ (pk_at_refl b HL)); [intros k Hk; cbv beta; lia | lia].
  - cbn [wfold]. rewrite putN_cons. pose proof (pk_wnext_at b st bs HL Hc) as H1.
    pose proof (put1_cap st bs Hc) as Hle.
    pose proof (IH _ (put1 st bs) (pk_at_len _ _ _ _ H1) ltac:(lia)) as H2.
    apply (pk_at_ext _ _ _ _ _ _ (pk_at_trans _ _ _ _ _ _ _ H1 H2)); [intros k Hk; cbv beta; lia | lia].
Qed.

Theorem pk_wfold : forall b st P, length (pb_live b) = 49%nat -> 0 <= w_cap st ->
  length (pb_live (wfold pack_form b st P)) = 49%nat /\
  (forall k, 0 <= k < 49 -> znth k (pb_live (wfold pack_form b st P)) =
     znth k (pb_live b) + pk_ind k (w_cap (putN st P)) - pk_ind k (w_cap st)) /\
  pb_bytes (wfold pack_form b st P) = pb_bytes b + pk_indb (w_cap (putN st P)) - pk_indb (w_cap st) /\
  pb_cap (wfold pack_form b st P) = pb_cap b.
Proof.
  intros b st P HL Hc. destruct (pk_wfold_at P b st HL Hc) as (A & B & C & D).
  split; [exact A|]. split; [intros k Hk; rewrite B by exact Hk; lia|]. split; [lia | exact D].
Qed.

Lemma pk_txcap1_ge : forall len cap n, 0 <= cap -> cap <= tx_cap1 len cap n.
Proof. intros len cap n Hc. unfold tx_cap1. destruct (Z.leb_spec (len + n + 1) cap); lia. Qed.

Lemma pk_txcapf_ge : forall ns len cap, 0 <= cap -> cap <= tx_capf len cap ns.
Proof.
  induction ns as [|n ns IH]; intros len cap Hc; cbn [tx_capf]; [lia|].
  pose proof (pk_txcap1_ge len cap n Hc). specialize (IH (len + n) (tx_cap1 len cap n) ltac:(lia)). lia.
Qed.

Lemma pk_txnext_at : forall b len cap n, length (pb_live b) = 49%nat -> 0 <= cap ->
  pk_at (tx_next pack_form b len cap n) b (fun k => pk_indr k (tx_cap1 len cap n) - pk_indr k cap)
    (pk_indrb (tx_cap1 len cap n) - pk_indrb cap).
Proof.
  intros b len cap n HL Hc. rewrite !pk_indrb_id. unfold tx_next, tx_cap1.
  destruct (Z.leb_spec (len + n + 1) cap) as [Hle|Hgt].
  - apply (pk_at_ext _ _ _ _ _ _ (pk_at_refl b HL)); [intros k Hk; cbv beta; lia | lia].
  - unfold tx_step. destruct (Z.eqb_spec cap 0) as [C0|Cn].
    + subst cap. apply (pk_at_ext _ _ _ _ _ _ (pk_malloc_at b (2 * (len + n + 1)) HL)); [|lia].
      intros k Hk. cbv beta. rewrite pk_indr_0, (pk_indr_nz k (2 * (len + n + 1))) by lia.
      rewrite pk_bn_bi by lia. lia.
    + apply (pk_at_ext _ _ _ _ _ _ (pk_realloc_at b cap (2 * (len + n + 1)) HL)); [|lia].
      intros k Hk. cbv beta. rewrite (pk_indr_nz k (2 * (len + n + 1))) by lia.
      rewrite (pk_indr_nz k cap) by lia. rewrite (pk_ltb_mono cap (2 * (len + n + 1))) by lia.
      rewrite !pk_bn_bi by lia. reflexivity.
Qed.

Lemma pk_txfold_at : forall ns b len cap, length (pb_live b) = 49%nat -> 0 <= cap ->
  pk_at (tx_fold pack_form b len cap ns) b (fun k => pk_indr k (tx_capf len cap ns) - pk_indr k cap)
    (pk_indrb (tx_capf len cap ns) - pk_indrb cap).
Proof.
  induction ns as [|n ns IH]; intros b len cap HL Hc.
  - cbn [tx_fold tx_capf]. apply (pk_at_ext _ _ _ _ _ _ (pk_at_refl b HL)); [intros k Hk; cbv beta; lia | lia].
  - cbn [tx_fold tx_capf]. pose proof (pk_txnext_at b len cap n HL Hc) as H1.
    pose proof (pk_txcap1_ge len cap n Hc) as Hle.
    pose proof (IH _ (len + n) (tx_cap1 len cap n) (pk_at_len _ _ _ _ H1) ltac:(lia)) as H2.
    apply (pk_at_ext _ _ _ _ _ _ (pk_at_trans _ _ _ _ _ _ _ H1 H2)); [intros k Hk; cbv beta; lia | lia].
Qed.

Theorem pk_txfold : forall b len cap ns, length (pb_live b) = 49%nat -> 0 <= cap ->
  length (pb_live (tx_fold pack_form b len cap ns)) = 49%nat /\
  (forall k, 0 <= k < 49 -> znth k (pb_live (tx_fold pack_form b len cap ns)) =
     znth k (pb_live b) + pk_indr k (tx_capf len cap ns) - pk_indr k cap) /\
  pb_bytes (tx_fold pack_form b len cap ns) = pb_bytes b + pk_indrb (tx_capf len cap ns) - pk_indrb cap /\
  pb_cap (tx_fold pack_form b len cap ns) = pb_cap b.
Proof.
  intros b len cap ns HL Hc. destruct (pk_txfold_at ns b len cap HL Hc) as (A & B & C & D).
  split; [exact A|]. split; [intros k Hk; rewrite B by exact Hk; lia|]. split; [lia | exact D].
Qed.

Lemma pkA_wfold : forall b b' V y st P, pk_at b' b V y -> 0 <= w_cap st ->
  pk_at (wfold pack_form b' st P) b (fun k => V k + (pk_ind k (w_cap (putN st P)) - pk_ind k (w_cap st)))
    (y + (pk_indb (w_cap (putN st P)) - pk_indb (w_cap st))).
Proof.
  intros b b' V y st P H Hc. exact (pk_at_trans _ _ _ _ _ _ _ H (pk_wfold_at P b' st (pk_at_len _ _ _ _ H) Hc)).
Qed.

Lemma pkA_txfold : forall b b' V y len cap ns, pk_at b' b V y -> 0 <= cap ->
  pk_at (tx_fold pack_form b' len cap ns) b (fun k => V k + (pk_indr k (tx_capf len cap ns) - pk_indr k cap))
    (y + (pk_indrb (tx_capf len cap ns) - pk_indrb cap)).
Proof.
  intros b b' V y len cap ns H Hc.
  exact (pk_at_trans _ _ _ _ _ _ _ H (pk_txfold_at ns b' len cap (pk_at_len _ _ _ _ H) Hc)).
Qed.

Lemma pk_pqf_nonpos : forall k D, pq_frees k D <= 0.
Proof.
  intros k D. induction D as [|ak D IH]; cbn [pq_frees]; [lia|].
  unfold pq_bi. destruct (band (snd ak + 16) =? k); lia.
Qed.

Lemma pk_lsum_nonneg : forall D, Forall (fun ak => 0 <= snd ak) D -> 0 <= lsum D.
Proof.
  intros D H. induction H as [|[a s] l Hs Hl IH]; cbn [lsum snd] in *; lia.
Qed.

Theorem pk_frees_le : forall b D, length (pb_live b) = 49%nat -> (forall ak, In ak D -> 0 <= snd ak) ->
  length (pb_live (rf_frees pack_form b D)) = 49%nat /\
  (forall k, 0 <= k < 49 -> znth k (pb_live (rf_frees pack_form b D)) <= znth k (pb_live b)) /\
  pb_bytes (rf_frees pack_form b D) <= pb_bytes b /\ pb_cap (rf_frees pack_form b D) = pb_cap b.
Proof.
  intros b D HL HD. assert (HF : Forall (fun ak => 0 <= snd ak) D) by (apply Forall_forall; exact HD).
  destruct (pk_frees_at D b HL HF) as (A & B & C & E). pose proof (pk_lsum_nonneg D HF) as HS.
  split; [exact A|]. split; [|split; [lia | exact E]].
  intros k Hk. rewrite B by exact Hk. pose proof (pk_pqf_nonpos k D). lia.
Qed.

Lemma pk_pqf_app : forall k D1 D2, pq_frees k (D1 ++ D2) = pq_frees k D1 + pq_frees k D2.
Proof. intros k D1 D2. induction D1 as [|ak D1 IH]; cbn [app pq_frees]; [lia | rewrite IH; lia]. Qed.

Lemma pk_pqf_perm : forall k D D', Permutation D D' -> pq_frees k D = pq_frees k D'.
Proof.
  intros k D D' H. rewrite !pk_frees_zl. rewrite (zl_perm _ _ (Permutation_map _ (Permutation_map snd H))).
  reflexivity.
Qed.

Lemma pk_lsum_app : forall D1 D2, lsum (D1 ++ D2) = lsum D1 + lsum D2.
Proof. intros D1 D2. rewrite !lsum_zl, map_app, zl_app. reflexivity. Qed.

Lemma pk_lsum_perm : forall D D', Permutation D D' -> lsum D = lsum D'.
Proof. intros D D' H. rewrite !lsum_zl. apply zl_perm, Permutation_map, H. Qed.

Lemma pk_D_split : forall k D D1 D2, Permutation D (D1 ++ D2) ->
  pq_frees k D = pq_frees k D1 + pq_frees k D2 /\ lsum D = lsum D1 + lsum D2 /\
  Z.of_nat (length D) = Z.of_nat (length D1) + Z.of_nat (length D2).
Proof.
  intros k D D1 D2 H. rewrite (pk_pqf_perm _ _ _ H), pk_pqf_app, (pk_lsum_perm _ _ H), pk_lsum_app.
  rewrite (Permutation_length H), length_app. split; [reflexivity|]. split; [reflexivity | lia].
Qed.

Lemma pk_D_same : forall k D D', Permutation D D' ->
  pq_frees k D = pq_frees k D' /\ lsum D = lsum D' /\ Z.of_nat (length D) = Z.of_nat (length D').
Proof.
  intros k D D' H. rewrite (pk_pqf_perm _ _ _ H), (pk_lsum_perm _ _ H), (Permutation_length H).
  split; [reflexivity|]. split; reflexivity.
Qed.

Lemma pk_fa_perm : forall (P : Z * Z -> Prop) l l', Forall P l -> Permutation l l' -> Forall P l'.
Proof.
  intros P l l' H HP. rewrite Forall_forall in *. intros x Hx. apply H.
  exact (Permutation_in _ (Permutation_sym HP) Hx).
Qed.

Lemma pk_dl_perm : forall T (D D' : list (Z * Z)), Permutation (map snd D) (map Z.of_nat (lsz T)) ->
  Z.of_nat (length D) = nlive T -> Permutation D D' ->
  Permutation (map snd D') (map Z.of_nat (lsz T)) /\ Z.of_nat (length D') = nlive T.
Proof.
  intros T D D' H1 H2 H3. split; [exact (Permutation_trans (Permutation_map snd (Permutation_sym H3)) H1)|].
  rewrite <- (Permutation_length H3). exact H2.
Qed.

Lemma pk_len_malloc : forall b n, length (pb_live (rf_malloc pack_form b n)) = length (pb_live b).
Proof. intros b n. rewrite pk_form_malloc. unfold pb_malloc. cbn [pb_live]. apply pk_lv_len. Qed.

Lemma pk_len_free : forall b n, length (pb_live (rf_free pack_form b n)) = length (pb_live b).
Proof. intros b n. rewrite pk_form_free. unfold pb_free. cbn [pb_live]. apply pk_lv_len. Qed.

Lemma pk_len_realloc : forall b m n, length (pb_live (rf_realloc pack_form b m n)) = length (pb_live b).
Proof.
  intros b m n. rewrite pk_form_realloc. unfold pb_realloc, lv_realloc. cbn [pb_live].
  destruct (band n <? band m); rewrite !pk_lv_len; reflexivity.
Qed.

Lemma pk_len_run : forall tr b, length (pb_live (rf_run pack_form b tr)) = length (pb_live b).
Proof.
  induction tr as [|e tr IH]; intros b; [reflexivity|]. rewrite pk_rf_run_cons, IH.
  destruct e as [n|m n|n|n]; cbn [rf_ev]; [apply pk_len_malloc | | reflexivity | apply pk_len_free].
  unfold rf_grow. destruct (Z.of_nat m =? 0); [apply pk_len_malloc | apply pk_len_realloc].
Qed.

Lemma pk_len_frees : forall D b, length (pb_live (rf_frees pack_form b D)) = length (pb_live b).
Proof.
  induction D as [|ak D IH]; intros b; [reflexivity|]. rewrite pk_rf_frees_cons, IH. apply pk_len_free.
Qed.

Ltac pklen := repeat first [rewrite pk_len_run | rewrite pk_len_frees | rewrite pk_len_malloc |
  rewrite pk_len_free | rewrite pk_len_realloc].

Ltac pkstep := match goal with
  | |- pk_at ?b ?b _ _ => eapply pk_at_refl
  | |- pk_at (rf_malloc pack_form _ _) _ _ _ => eapply pkA_malloc
  | |- pk_at (rf_free pack_form _ _) _ _ _ => eapply pkA_free
  | |- pk_at (rf_realloc pack_form _ _ _) _ _ _ => eapply pkA_realloc
  | |- pk_at (rf_run pack_form _ _) _ _ _ => eapply pkA_run
  | |- pk_at (rf_frees pack_form _ _) _ _ _ => eapply pkA_frees
  | |- pk_at (wfold pack_form _ _ _) _ _ _ => eapply pkA_wfold
  | |- pk_at (tx_fold pack_form _ _ _ _) _ _ _ => eapply pkA_txfold
  end.

Ltac pkside := first [assumption | (rewrite pk_w_cap_w0; lia) | lia].

Ltac pkrun := repeat (pkstep; try pkside).

Theorem cno_fold_eq : forall b n T ok E1 E2 E3, length (pb_live b) = 49%nat ->
  cno_dl T E1 -> cno_dl T E2 -> cno_dl T E3 -> grow_up T ->
  cno_free3 pack_form (cno_mid pack_form b n T ok E1 E2 E3) n = b.
Proof.
  intros b n T ok E1 E2 E3 HL [P1 N1] [P2 N2] [P3 N3] HG.
  destruct (pk_cancel_v T E1 HG P1 N1) as (C1 & Y1 & F1).
  destruct (pk_cancel_v T E2 HG P2 N2) as (C2 & Y2 & F2).
  destruct (pk_cancel_v T E3 HG P3 N3) as (C3 & Y3 & F3).
  unfold cno_free3, cno_mid, cno_b3. destruct ok;
    (eapply pk_at_zero; [exact HL | pkrun | intros k Hk; cbv beta; specialize (C1 k); specialize (C2 k);
       specialize (C3 k); lia | lia]).
Qed.

Lemma pk_ent_b2_len : forall b x E1 E2 E3 Dp, length (pb_live b) = 49%nat ->
  length (pb_live (ent_b2 pack_form b x E1 E2 E3 Dp)) = 49%nat.
Proof.
  intros b x E1 E2 E3 Dp HL. unfold ent_b2, ent_b1, cno_free3, cno_mid, cno_b3.
  destruct (cno_ok x); pklen; exact HL.
Qed.

Theorem ent_b3_eq : forall b x E1 E2 E3 Dp, length (pb_live b) = 49%nat ->
  ent_b3 pack_form b x E1 E2 E3 Dp = ent_b2 pack_form b x E1 E2 E3 Dp.
Proof.
  intros b x E1 E2 E3 Dp HL. pose proof (pk_ent_b2_len b x E1 E2 E3 Dp HL) as HL2. unfold ent_b3.
  eapply pk_at_zero; [exact HL2 | pkrun | intros k Hk; cbv beta; lia | lia].
Qed.

Lemma pk_w0_pos : forall P c f, P <> [] -> c <> f -> 0 < w_cap (putN (w0 c f) P).
Proof.
  intros [|bs P] c f HP Hcf; [contradiction|]. rewrite putN_cons.
  assert (E : 0 < w_cap (put1 (w0 c f) bs)).
  { unfold put1. cbn [w0 w_failed w_text w_cap w_cnt w_fail w_calls length negb Z.eqb Z.of_nat].
    repeat match goal with |- context [if ?b then _ else _] => let H := fresh "Hb" in destruct b eqn:H end;
      cbn [w_cap]; try (apply newcap_pos; lia);
      repeat match goal with
      | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
      | H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
      end; lia. }
  pose proof (putN_cap P (put1 (w0 c f) bs) ltac:(lia)). lia.
Qed.

Lemma pk_wcap_eq : forall t p cnt, 0 <= cnt -> cnt + CF.PjWriteHyp.wcalls t p <= 2 ^ 64 - 1 ->
  w_cap (putN (w0 cnt (2 ^ 64 - 1)) (wdpieces t p)) = wcap t p /\ 0 < wcap t p.
Proof.
  intros t p cnt H0 H1. pose proof (CF.RttModel.wcalls_pos t p) as W.
  pose proof (pk_w0_pos (wdpieces t p) cnt (2 ^ 64 - 1) (CF.CrsRoom.wdpieces_nonempty t p) ltac:(lia)) as Hp.
  unfold CF.PjWriteHyp.wcalls in H1, W.
  rewrite (CF.PjWriteAdapt.pjwa_ok (wdpieces t p) cnt (2 ^ 64 - 1) H0 ltac:(lia) (or_intror H1)) in Hp |- *.
  cbn [w_cap] in Hp |- *. split; [reflexivity | exact Hp].
Qed.

Lemma pk_grow_ev_up : forall o n cap, grow_up (PjRoundTrip.grow_ev o n cap).
Proof.
  intros o n cap m n' H.
  assert (G : (Nat.ltb n cap = false -> cap < PjRoundTrip.gcap n cap)%nat).
  { intros E. unfold PjRoundTrip.gcap. rewrite E. destruct (Nat.eqb_spec cap 0); lia. }
  revert H. unfold PjRoundTrip.grow_ev. destruct (Nat.ltb n cap) eqn:E; [intros []|].
  specialize (G eq_refl). intros [H|H]; [injection H as <- <-; lia|].
  destruct o; [destruct H as [H|[]]; injection H as <- <-; lia | destruct H].
Qed.

Lemma ttrace_grow_up : forall t, grow_up (PjRoundTrip.ttrace t).
Proof.
  intros t. induction t as [| | | txt bits | s | items IH | ms IH] using jv_ind'.
  - exact grow_up_nil.
  - exact grow_up_nil.
  - exact grow_up_nil.
  - intros m n [H|[]]. discriminate.
  - intros m n [H|[]]. discriminate.
  - rewrite PjRoundTrip.tt_arr. assert (K : forall n cap, grow_up (PjRoundTrip.tgo_arr n cap items)).
    { induction IH as [|u r Hu Hr IHr]; intros n cap; cbn [PjRoundTrip.tgo_arr]; [exact grow_up_nil|].
      apply grow_up_app; [apply pk_grow_ev_up|]. apply grow_up_app; [exact Hu | apply IHr]. }
    apply K.
  - rewrite PjRoundTrip.tt_obj. assert (K : forall n cap, grow_up (PjRoundTrip.tgo_obj n cap ms)).
    { induction IH as [|[k u] r Hu Hr IHr]; intros n cap; cbn [PjRoundTrip.tgo_obj]; [exact grow_up_nil|].
      apply grow_up_app; [apply pk_grow_ev_up|]. cbn [snd] in Hu.
      intros m n' [H|H]; [discriminate|]. revert m n' H.
      apply grow_up_app; [exact Hu | apply IHr]. }
    apply K.
Qed.

Lemma rtt_bf_gen : forall b cnt t p, length (pb_live b) = 49%nat -> 0 <= cnt ->
  cnt + CF.PjWriteHyp.wcalls t p <= 2 ^ 64 - 1 ->
  rtt_bf pack_form b cnt t p = rf_run pack_form b (PjRoundTrip.ttrace t).
Proof.
  intros b cnt t p HL H0 H1. destruct (pk_wcap_eq t p cnt H0 H1) as (EW & PW).
  assert (PT : 0 < tx_capf 0 0 (rtt_ns t p)).
  { unfold rtt_ns. cbn [app tx_capf]. change (tx_cap1 0 0 0) with 2.
    pose proof (pk_txcapf_ge (tv_calls t p 0 ++ (if p then [1] else [])) (0 + 0) 2 ltac:(lia)). lia. }
  unfold rtt_bf, rtt_bp, rtt_bt, rtt_bw.
  eapply (pk_at_same b); [pkrun | pkrun | |].
  - intros k Hk. cbv beta. rewrite EW, pk_w_cap_w0, pk_ind_0, pk_indr_0.
    rewrite (pk_ind_nz k (wcap t p)) by lia. rewrite (pk_indr_nz k (tx_capf 0 0 (rtt_ns t p))) by lia.
    rewrite !pk_bn_bi by lia. lia.
  - rewrite EW, pk_w_cap_w0, pk_indb_0, (pk_indb_nz (wcap t p)) by lia. rewrite !pk_indrb_id. lia.
Qed.

Theorem rtt_bf_eq : forall b cnt t p, length (pb_live b) = 49%nat -> 0 <= cnt <= 2 ^ 62 ->
  wlen t p + 1 <= 2 ^ 28 -> rtt_bf pack_form b cnt t p = rf_run pack_form b (PjRoundTrip.ttrace t).
Proof.
  intros b cnt t p HL Hc Hw. apply rtt_bf_gen; [exact HL | lia|].
  pose proof (CF.RttStgCmp.rf_wcalls t p). lia.
Qed.

Lemma crt_b2_gen : forall b cnt t Df, length (pb_live b) = 49%nat -> 0 <= cnt -> crt_cnt2 cnt t <= 2 ^ 64 - 1 ->
  crt_dl (PjRoundTrip.ttrace t) Df -> crt_b2 pack_form b cnt t Df = rf_run pack_form b (PjRoundTrip.ttrace t).
Proof.
  intros b cnt t Df HL H0 H1 [HP HN]. pose proof (CF.RttModel.wcalls_pos t false). pose proof (CF.RttModel.wcalls_pos t true).
  unfold crt_cnt2, crt_cnt1 in H1. unfold crt_b2, crt_b1.
  rewrite (rtt_bf_gen b cnt t false HL H0) by lia.
  pose proof (pk_run_at (PjRoundTrip.ttrace t) b HL) as R.
  rewrite (rtt_bf_gen (rf_run pack_form b (PjRoundTrip.ttrace t)) (crt_cnt1 cnt t) t true (pk_at_len _ _ _ _ R))
    by (unfold crt_cnt1; lia).
  apply pk_cancel; [exact (pk_at_len _ _ _ _ R) | apply ttrace_grow_up | exact HP | exact HN].
Qed.

Lemma pk_crt_bd : forall y t, json_read jr_strtod y = Some t -> Z.of_nat (length y) <= 3 * 2 ^ 20 ->
  1 <= CF.PjWriteHyp.wcalls t false <= 2 ^ 17 /\ 1 <= CF.PjWriteHyp.wcalls t true <= 2 ^ 17 /\
  Z.of_nat (PjRoundTrip.tcalls t) <= 2 ^ 30 /\ 1 <= CF.PjWriteHyp.wcalls (crt_tree t) true <= 2 ^ 17 /\
  Z.of_nat (PjRoundTrip.tcalls (crt_tree t)) <= 2 ^ 30 /\ wlen t true + 1 <= 2 ^ 28 /\ wlen t false + 1 <= 2 ^ 28.
Proof.
  intros y t Hj Hy.
  pose proof (SlotSizes.wlen_false_read jr_strtod y t Hj : wlen t false <= 3 * Z.of_nat (length y)) as WF.
  pose proof (SlotSizes.wlen_true_read jr_strtod y t Hj : wlen t true <= 56 * Z.of_nat (length y) - 54) as WT.
  pose proof (CF.check_round_trip_m.crt_len t) as WC.
  pose proof (CF.RttStgCmp.rf_wcalls t false) as R1. pose proof (CF.RttStgCmp.rf_wcalls t true) as R2.
  pose proof (CF.RttStgCmp.rf_wcalls (crt_tree t) true) as R3.
  pose proof (CF.RttModel.wcalls_pos t false) as P1. pose proof (CF.RttModel.wcalls_pos t true) as P2.
  pose proof (CF.RttModel.wcalls_pos (crt_tree t) true) as P3.
  assert (HW : PjRoundTrip.pj_wf jr_strtod t) by (eapply PjRoundTrip.wf_read; exact Hj).
  pose proof (CF.check_round_trip_m.crt_wf y t Hj) as HW'.
  destruct (CF.RttModel.rtt_G9 t false HW) as (_ & _ & N1).
  destruct (CF.RttModel.rtt_G9 (crt_tree t) true HW') as (_ & _ & N2).
  pose proof (G7_4 jr_strtod (wdoc t false) []) as G1.
  pose proof (G7_4 jr_strtod (wdoc (crt_tree t) true) []) as G2.
  unfold ncalls in N1, N2. unfold wlen in *. lia.
Qed.

Lemma pk_set_len : forall n cap k, Z.of_nat (length (set_trace n cap k)) <= 3.
Proof.
  intros n cap k. unfold set_trace. rewrite length_app. destruct (n =? cap); cbn [length app]; lia.
Qed.

Lemma pk_set_cset : forall F b3 n T b4 cset Do, crt_set_res F b3 n T b4 cset Do -> 0 <= cset <= 3.
Proof.
  intros F b3 n T b4 cset Do (Db & _ & [(Hc & _) | (cap & Dold & Dnew & Dr & a & a' & _ & Hc & _)]).
  - lia.
  - pose proof (pk_set_len n cap 10). lia.
Qed.

Lemma pk_crt_count : forall F b cnt t cset bf y, json_read jr_strtod y = Some t -> Z.of_nat (length y) <= 3 * 2 ^ 20 ->
  crt_fin F b cnt t cset bf -> 0 <= crt_count t cset <= 2 ^ 33.
Proof.
  intros F b cnt t cset bf y Hj Hy HF.
  destruct (pk_crt_bd y t Hj Hy) as (A1 & A2 & A3 & A4 & A5 & _ & _).
  assert (Hcs : forall ms, t = JObj ms -> 0 <= cset <= 3).
  { intros ms ->. destruct HF as (Df & _ & b4 & Do & Dp & Dp' & Do' & HS & _). exact (pk_set_cset _ _ _ _ _ _ _ HS). }
  unfold crt_count. destruct t as [| | | txt bits | s | items | ms]; cbv iota beta; try lia.
  specialize (Hcs ms eq_refl). lia.
Qed.

Lemma pk_grow_evz : forall m n k, 0 < m <= n ->
  pq_ev k (EGrow (Z.to_nat m) (Z.to_nat n)) = pq_bi k (n + 16) - pq_bi k (m + 16) /\
  held_ev (EGrow (Z.to_nat m) (Z.to_nat n)) + 16 * nlive_ev (EGrow (Z.to_nat m) (Z.to_nat n)) = n - m.
Proof.
  intros m n k H. assert (Em : Z.to_nat m = S (Z.to_nat m - 1)) by lia.
  rewrite Em. cbn [pq_ev Nat.eqb held_ev nlive_ev]. rewrite <- Em. rewrite !Z2Nat.id by lia.
  rewrite (pk_ltb_mono (m + 16) (n + 16)) by lia. split; lia.
Qed.

Lemma pk_grow0_evz : forall m n k, m = 0 -> 0 <= n ->
  pq_ev k (EGrow (Z.to_nat m) (Z.to_nat n)) = pq_bi k (n + 16) /\
  held_ev (EGrow (Z.to_nat m) (Z.to_nat n)) + 16 * nlive_ev (EGrow (Z.to_nat m) (Z.to_nat n)) = n + 16.
Proof.
  intros m n k Hm Hn. subst m. change (Z.to_nat 0) with O.
  assert (E : Z.of_nat (Z.to_nat n) = n) by lia. split.
  - cbn [pq_ev Nat.eqb]. rewrite E. reflexivity.
  - cbn [held_ev nlive_ev]. rewrite E. change (Z.of_nat O) with 0. lia.
Qed.

Lemma pk_alloc_evz : forall n k, 0 <= n ->
  pq_ev k (EAlloc (Z.to_nat n)) = pq_bi k (n + 16) /\
  held_ev (EAlloc (Z.to_nat n)) + 16 * nlive_ev (EAlloc (Z.to_nat n)) = n + 16.
Proof.
  intros n k Hn. assert (E : Z.of_nat (Z.to_nat n) = n) by lia. split.
  - cbn [pq_ev]. rewrite E. reflexivity.
  - cbn [held_ev nlive_ev]. rewrite E. lia.
Qed.

Lemma pk_snd_fa : forall (D : list (Z * Z)) l, map snd D = l -> Forall (fun z => 0 <= z) l -> Forall (fun ak => 0 <= snd ak) D.
Proof.
  intros D l E H. rewrite Forall_forall in *. intros ak Hin. apply H. rewrite <- E. apply in_map. exact Hin.
Qed.

Lemma pk_set_v : forall n cap Dold Dnew, 0 <= n <= cap ->
  (n < cap /\ Dold = [] /\ Dnew = [] \/
   n = cap /\ map snd Dold = (if cap =? 0 then [] else [56 * cap; 8 * cap]) /\
     map snd Dnew = [56 * cap2 cap; 8 * cap2 cap]) ->
  (forall k, pq_run k (set_trace n cap 10) = pq_bi k 27 + pq_frees k Dold - pq_frees k Dnew) /\
  held (set_trace n cap 10) + 16 * nlive (set_trace n cap 10) =
    27 + (lsum Dnew + 16 * Z.of_nat (length Dnew)) - (lsum Dold + 16 * Z.of_nat (length Dold)) /\
  Forall (fun ak => 0 <= snd ak) Dnew.
Proof.
  intros n cap Dold Dnew Hn [(Hlt & -> & ->) | (-> & HO & HN)].
  - unfold set_trace. rewrite (proj2 (Z.eqb_neq n cap)) by lia. cbn [app].
    destruct (pk_alloc_evz (10 + 1) 0 ltac:(lia)) as (_ & Y).
    split; [|split; [|constructor]].
    + intros k. cbn [pq_run pq_frees]. rewrite (proj1 (pk_alloc_evz (10 + 1) k ltac:(lia))).
      change (10 + 1 + 16) with 27. lia.
    + cbn [held nlive lsum length]. lia.
  - unfold set_trace. rewrite Z.eqb_refl. cbn [app].
    assert (LO : lsum Dold = zl (map snd Dold) /\ Z.of_nat (length Dold) = Z.of_nat (length (map snd Dold)))
      by (rewrite lsum_zl, length_map; split; reflexivity).
    assert (LN : lsum Dnew = zl (map snd Dnew) /\ Z.of_nat (length Dnew) = Z.of_nat (length (map snd Dnew)))
      by (rewrite lsum_zl, length_map; split; reflexivity).
    rewrite HO in LO. rewrite HN in LN.
    destruct (Z.eqb_spec cap 0) as [C0|Cn].
    + assert (E2 : cap2 cap = 8) by (rewrite C0; reflexivity). rewrite E2 in *.
      destruct (pk_grow0_evz (56 * cap) (56 * 8) 0 ltac:(lia) ltac:(lia)) as (_ & Y1).
      destruct (pk_grow0_evz (8 * cap) (8 * 8) 0 ltac:(lia) ltac:(lia)) as (_ & Y2).
      destruct (pk_alloc_evz (10 + 1) 0 ltac:(lia)) as (_ & Y3).
      split; [|split].
      * intros k. rewrite !pk_frees_zl, HO, HN. cbn [pq_run map zl].
        rewrite (proj1 (pk_grow0_evz (56 * cap) (56 * 8) k ltac:(lia) ltac:(lia))).
        rewrite (proj1 (pk_grow0_evz (8 * cap) (8 * 8) k ltac:(lia) ltac:(lia))).
        rewrite (proj1 (pk_alloc_evz (10 + 1) k ltac:(lia))). change (10 + 1 + 16) with 27. lia.
      * cbn [held nlive map zl length] in *. lia.
      * apply (pk_snd_fa _ _ HN). repeat constructor; lia.
    + assert (E2 : cap2 cap = 2 * cap) by (unfold cap2; rewrite (proj2 (Z.eqb_neq cap 0) Cn); reflexivity).
      rewrite E2 in *.
      destruct (pk_grow_evz (56 * cap) (56 * (2 * cap)) 0 ltac:(lia)) as (_ & Y1).
      destruct (pk_grow_evz (8 * cap) (8 * (2 * cap)) 0 ltac:(lia)) as (_ & Y2).
      destruct (pk_alloc_evz (10 + 1) 0 ltac:(lia)) as (_ & Y3).
      split; [|split].
      * intros k. rewrite !pk_frees_zl, HO, HN. cbn [pq_run map zl].
        rewrite (proj1 (pk_grow_evz (56 * cap) (56 * (2 * cap)) k ltac:(lia))).
        rewrite (proj1 (pk_grow_evz (8 * cap) (8 * (2 * cap)) k ltac:(lia))).
        rewrite (proj1 (pk_alloc_evz (10 + 1) k ltac:(lia))). change (10 + 1 + 16) with 27. lia.
      * cbn [held nlive map zl length] in *. lia.
      * apply (pk_snd_fa _ _ HN). repeat constructor; lia.
Qed.

Lemma crt_fin_gen : forall b cnt t cset bf, length (pb_live b) = 49%nat -> 0 <= cnt ->
  crt_cnt2 cnt t + 4 + CF.PjWriteHyp.wcalls (crt_tree t) true <= 2 ^ 64 - 1 ->
  crt_fin pack_form b cnt t cset bf -> bf = b.
Proof.
  intros b cnt t cset bf HL H0 HB (Df & HDf & M).
  pose proof (CF.RttModel.wcalls_pos (crt_tree t) true) as WP.
  assert (Hc2 : 0 <= crt_cnt2 cnt t).
  { unfold crt_cnt2, crt_cnt1. pose proof (CF.RttModel.wcalls_pos t false). pose proof (CF.RttModel.wcalls_pos t true). lia. }
  rewrite (crt_b2_gen b cnt t Df HL H0 ltac:(lia) HDf) in M.
  pose proof (ttrace_grow_up t) as GT. pose proof (ttrace_grow_up (crt_tree t)) as GT'.
  destruct t as [| | | txt bits | s | items | ms].
  1-6: destruct M as (Db & Db' & [HP HN] & HPP & ->); destruct (pk_dl_perm _ _ _ HP HN HPP) as [HP' HN'];
       apply pk_cancel; [exact HL | exact GT | exact HP' | exact HN'].
  destruct M as (b4 & Do & Dp & Dp' & Do' & HS & [HPp HNp] & HPP & HPo & ->).
  pose proof (pk_set_cset _ _ _ _ _ _ _ HS) as Hcs.
  destruct (pk_wcap_eq (crt_tree (JObj ms)) true (crt_cnt2 cnt (JObj ms) + 1 + cset) ltac:(lia) ltac:(lia))
    as (EW & PW).
  destruct (pk_dl_perm _ _ _ HPp HNp HPP) as [HPp' HNp'].
  destruct (pk_cancel_v _ _ GT' HPp' HNp') as (CP & YP & FP).
  destruct HS as (Db & [HPDb HNDb] & [(Hc0 & Di & Dr & Di' & a & HP1 & HP2 & Eb4 & HP3) |
    (cap & Dold & Dnew & Dr & a & a' & Hn & Hcs' & Eb4 & HP1 & HP2 & HC)]).
  - destruct (pk_cancel_v _ _ GT HPDb HNDb) as (CB & YB & FB).
    pose proof (pk_fa_perm _ _ _ FB HP1) as FDD. apply Forall_app in FDD as [FDi FDr].
    pose proof (pk_fa_perm _ _ _ FDi HP2) as FDi'.
    assert (HPo' : Permutation Do' (Dr ++ [(a, 21)])) by exact (Permutation_trans (Permutation_sym HPo) HP3).
    assert (FDo' : Forall (fun ak => 0 <= snd ak) Do').
    { apply (pk_fa_perm _ (Dr ++ [(a, 21)])); [|exact (Permutation_sym HPo')].
      apply Forall_app. split; [exact FDr | repeat constructor; cbn [snd]; lia]. }
    subst b4. unfold crt_b5.
    eapply pk_at_zero; [exact HL | pkrun | |].
    + intros k Hk. cbv beta. rewrite EW, pk_w_cap_w0, pk_ind_0.
      rewrite (pk_ind_nz k (wcap (crt_tree (JObj ms)) true)) by lia. rewrite !pk_bn_bi by lia.
      destruct (pk_D_split k _ _ _ HP1) as (S1 & _ & _). destruct (pk_D_same k _ _ HP2) as (S2 & _ & _).
      destruct (pk_D_split k _ _ _ HPo') as (S3 & _ & _). cbn [pq_frees snd] in S3. change (21 + 16) with 37 in S3.
      specialize (CB k). specialize (CP k). lia.
    + rewrite EW, pk_w_cap_w0, pk_indb_0, (pk_indb_nz (wcap (crt_tree (JObj ms)) true)) by lia.
      destruct (pk_D_split 0 _ _ _ HP1) as (_ & S1 & L1). destruct (pk_D_same 0 _ _ HP2) as (_ & S2 & L2).
      destruct (pk_D_split 0 _ _ _ HPo') as (_ & S3 & L3). cbn [lsum length] in S3, L3. lia.
  - destruct (pk_cancel_v _ _ GT HPDb HNDb) as (CB & YB & FB).
    assert (Hn0 : 0 <= Z.of_nat (length ms) <= cap) by lia.
    destruct (pk_set_v _ _ _ _ Hn0 HC) as (SV & SY & FDn).
    pose proof (pk_fa_perm _ _ _ FB HP1) as FDD. apply Forall_app in FDD as [FDo FDr].
    assert (HPo' : Permutation Do' (Dnew ++ (a', 11) :: Dr ++ [(a, 21)]))
      by exact (Permutation_trans (Permutation_sym HPo) HP2).
    assert (FDo' : Forall (fun ak => 0 <= snd ak) Do').
    { apply (pk_fa_perm _ (Dnew ++ (a', 11) :: Dr ++ [(a, 21)])); [|exact (Permutation_sym HPo')].
      apply Forall_app. split; [exact FDn|]. constructor; [cbn [snd]; lia|].
      apply Forall_app. split; [exact FDr | repeat constructor; cbn [snd]; lia]. }
    subst b4. unfold crt_b5.
    eapply pk_at_zero; [exact HL | pkrun | |].
    + intros k Hk. cbv beta. rewrite EW, pk_w_cap_w0, pk_ind_0.
      rewrite (pk_ind_nz k (wcap (crt_tree (JObj ms)) true)) by lia. rewrite !pk_bn_bi by lia.
      destruct (pk_D_split k _ _ _ HP1) as (S1 & _ & _).
      destruct (pk_D_split k _ _ _ HPo') as (S3 & _ & _). cbn [pq_frees snd] in S3.
      rewrite pk_pqf_app in S3. cbn [pq_frees snd] in S3.
      change (11 + 16) with 27 in S3. change (21 + 16) with 37 in S3.
      specialize (CB k). specialize (CP k). specialize (SV k). lia.
    + rewrite EW, pk_w_cap_w0, pk_indb_0, (pk_indb_nz (wcap (crt_tree (JObj ms)) true)) by lia.
      destruct (pk_D_split 0 _ _ _ HP1) as (_ & S1 & L1).
      destruct (pk_D_split 0 _ _ _ HPo') as (_ & S3 & L3). cbn [lsum length] in S3, L3.
      rewrite pk_lsum_app in S3. rewrite length_app in L3. cbn [lsum length] in S3, L3. lia.
Qed.

Theorem crt_b2_eq : forall b cnt t Df y, length (pb_live b) = 49%nat -> 0 <= cnt <= 2 ^ 62 ->
  json_read jr_strtod y = Some t -> Z.of_nat (length y) <= 3 * 2 ^ 20 ->
  crt_dl (PjRoundTrip.ttrace t) Df -> crt_b2 pack_form b cnt t Df = rf_run pack_form b (PjRoundTrip.ttrace t).
Proof.
  intros b cnt t Df y HL Hc Hj Hy HD. destruct (pk_crt_bd y t Hj Hy) as (A1 & A2 & A3 & A4 & A5 & _ & _).
  apply crt_b2_gen; [exact HL | lia | unfold crt_cnt2, crt_cnt1; lia | exact HD].
Qed.

Theorem crt_fin_eq : forall b cnt t cset bf y, length (pb_live b) = 49%nat -> 0 <= cnt <= 2 ^ 62 ->
  json_read jr_strtod y = Some t -> Z.of_nat (length y) <= 3 * 2 ^ 20 ->
  crt_fin pack_form b cnt t cset bf -> bf = b.
Proof.
  intros b cnt t cset bf y HL Hc Hj Hy HF. destruct (pk_crt_bd y t Hj Hy) as (A1 & A2 & A3 & A4 & A5 & _ & _).
  apply (crt_fin_gen b cnt t cset bf HL ltac:(lia)); [unfold crt_cnt2, crt_cnt1; lia | exact HF].
Qed.

Lemma wstarve_eq : forall b c f t p, length (pb_live b) = 49%nat -> wstarve pack_form b c f t p = b.
Proof.
  intros b c f t p HL. unfold wstarve. cbv zeta.
  pose proof (putN_cap (wdpieces t p) (w0 c f) ltac:(rewrite pk_w_cap_w0; lia)) as Hge.
  rewrite pk_w_cap_w0 in Hge.
  destruct (Z.eqb_spec (w_cap (putN (w0 c f) (wdpieces t p))) 0) as [E|E].
  - eapply pk_at_zero; [exact HL | pkrun | |].
    + intros k Hk. cbv beta. rewrite E, pk_w_cap_w0, pk_ind_0. lia.
    + rewrite E, pk_w_cap_w0, pk_indb_0. lia.
  - eapply pk_at_zero; [exact HL | pkrun | |].
    + intros k Hk. cbv beta. rewrite pk_w_cap_w0, pk_ind_0, (pk_ind_nz k _ E). rewrite pk_bn_bi by lia. lia.
    + rewrite pk_w_cap_w0, pk_indb_0, (pk_indb_nz _ E). lia.
Qed.

Lemma wfull_gen : forall b c t p, length (pb_live b) = 49%nat -> c <> 2 ^ 64 - 1 -> wfull pack_form b c t p = b.
Proof.
  intros b c t p HL Hc. unfold wfull.
  pose proof (pk_w0_pos (wdpieces t p) c FMAX (CF.CrsRoom.wdpieces_nonempty t p) ltac:(unfold FMAX; lia)) as Hp.
  eapply pk_at_zero; [exact HL | pkrun | |].
  - intros k Hk. cbv beta. rewrite pk_w_cap_w0, pk_ind_0, (pk_ind_nz k (w_cap (putN (w0 c FMAX) (wdpieces t p))))
      by lia. rewrite pk_bn_bi by lia. lia.
  - rewrite pk_w_cap_w0, pk_indb_0, (pk_indb_nz (w_cap (putN (w0 c FMAX) (wdpieces t p)))) by lia. lia.
Qed.

Theorem wfull_eq : forall b c t p, length (pb_live b) = 49%nat -> 0 <= c <= 2 ^ 62 -> wfull pack_form b c t p = b.
Proof. intros b c t p HL Hc. apply wfull_gen; [exact HL | lia]. Qed.

Lemma crs_pass_fold_gen : forall b c x t p, length (pb_live b) = 49%nat -> c <> 2 ^ 64 - 1 ->
  crs_pass_fold pack_form b c x t p = b.
Proof.
  intros b c x t p HL Hc. unfold crs_pass_fold. rewrite (wfull_gen b c t p HL Hc). apply wstarve_eq. exact HL.
Qed.

Theorem crs_pass_fold_eq : forall b c x t p, length (pb_live b) = 49%nat -> 0 <= c <= 2 ^ 62 ->
  crs_pass_fold pack_form b c x t p = b.
Proof. intros b c x t p HL Hc. apply crs_pass_fold_gen; [exact HL | lia]. Qed.

Lemma pk_pick : forall x n, 0 <= n -> 0 <= pick x n <= n.
Proof.
  intros x n Hn. unfold pick. destruct (Z.eqb_spec n 0); [lia|].
  pose proof (Z.mod_pos_bound (djb2 5381 x) n ltac:(lia)). lia.
Qed.

Theorem crs_doc_fold_eq : forall b c x t, length (pb_live b) = 49%nat -> 0 <= c <= 2 ^ 62 ->
  wlen t true + 1 <= 2 ^ 28 -> crs_doc_fold pack_form b c x t = b.
Proof.
  intros b c x t HL Hc Hw.
  assert (Hn : crs_pass_cnt c x t true <> 2 ^ 64 - 1).
  { unfold crs_pass_cnt. change (wN t true) with (CF.PjWriteHyp.wcalls t true).
    pose proof (CF.RttStgCmp.rf_wcalls t true). pose proof (CF.RttModel.wcalls_pos t true).
    pose proof (pk_pick x (CF.PjWriteHyp.wcalls t true) ltac:(lia)). lia. }
  unfold crs_doc_fold. rewrite (crs_pass_fold_gen b c x t true HL ltac:(lia)).
  apply crs_pass_fold_gen; [exact HL | exact Hn].
Qed.

Theorem entry_fold_pack : forall b0 cnt0 x E1 E2 E3 Dp cset b4 trs Ds Df, length (pb_live b0) = 49%nat ->
  0 <= cnt0 <= 3 * 2 ^ 60 -> entry_wit pack_form b0 cnt0 x E1 E2 E3 Dp cset b4 trs Ds Df ->
  entry_fold pack_form b0 cnt0 x E1 E2 E3 Dp cset b4 trs Ds Df = b0.
Proof.
  intros b0 cnt0 x E1 E2 E3 Dp cset b4 trs Ds Df HL Hc HW. unfold entry_fold.
  destruct (Z.ltb_spec 0x300000 (ent_n x)) as [Hb|Hb]; [reflexivity|].
  destruct (HW Hb) as (W1 & W2 & W3 & W). clear HW.
  assert (GT : grow_up (ent_T x)) by (unfold ent_T; apply jr_grow_up).
  assert (B1 : ent_b1 pack_form b0 x E1 E2 E3 = b0) by (unfold ent_b1; apply cno_fold_eq; assumption).
  assert (Hzl : length (zb x) = length x) by (unfold zb; apply length_map).
  pose proof (G7_4 jr_strtod (zb x) []) as G0.
  assert (Htk : 0 <= ent_took x <= 2 * Z.of_nat (length x) + 2) by (unfold ent_took, ncalls; lia).
  unfold ent_n in Hb.
  pose proof (pk_run_at (ent_T x) b0 HL) as RL. pose proof (pk_at_len _ _ _ _ RL) as HLT.
  revert W. destruct (json_read jr_strtod (zb x)) as [t|] eqn:Ej; intros W.
  - assert (Ok : cno_ok x = true) by (unfold cno_ok; rewrite Ej; reflexivity).
    destruct W as (WF & WS & (D & HPD & [HD1 HD2])).
    destruct (pk_dl_perm _ _ _ HD1 HD2 HPD) as [HF1 HF2].
    assert (B3 : ent_b3 pack_form b0 x E1 E2 E3 [] = rf_run pack_form b0 (ent_T x)).
    { rewrite ent_b3_eq by exact HL. unfold ent_b2. rewrite Ok, B1. reflexivity. }
    rewrite B3 in WF.
    assert (Hc3 : 0 <= ent_c3 cnt0 x <= 2 ^ 62) by (unfold ent_c3; lia).
    pose proof (pk_crt_count _ _ _ _ _ _ (zb x) Ej ltac:(lia) WF) as HCC.
    destruct (pk_crt_bd (zb x) t Ej ltac:(lia)) as (_ & _ & _ & _ & _ & WT & _).
    rewrite (crt_fin_eq _ _ _ _ _ (zb x) HLT Hc3 Ej ltac:(lia) WF).
    assert (Hc4 : 0 <= ent_c4 cnt0 x t cset <= 3 * 2 ^ 60 + 2 ^ 34) by (unfold ent_c4, ent_c3 in *; lia).
    unfold ent_b5. destruct (Z.eqb_spec (ent_took x) 0) as [T0|T1].
    + rewrite (crs_doc_fold_eq _ (ent_c4 cnt0 x t cset) (zb x) t HLT ltac:(lia) WT).
      apply pk_cancel; [exact HL | exact GT | exact HF1 | exact HF2].
    + destruct (WS T1) as (ok & res & Ejr & _ & HPs & HNs).
      assert (GS : grow_up trs) by (pose proof (jr_grow_up jr_strtod (zb x) ok) as G'; rewrite Ejr in G'; exact G').
      pose proof (G7_4 jr_strtod (zb x) ok) as G1. rewrite Ejr in G1. cbn [snd] in G1.
      rewrite (pk_cancel _ trs Ds HLT GS HPs HNs).
      rewrite (crs_doc_fold_eq _ (ent_c4 cnt0 x t cset + Z.of_nat (calls trs)) (zb x) t HLT ltac:(lia) WT).
      apply pk_cancel; [exact HL | exact GT | exact HF1 | exact HF2].
  - assert (Ok : cno_ok x = false) by (unfold cno_ok; rewrite Ej; reflexivity).
    destruct W as ((D & HPD & [HD1 HD2]) & WS).
    destruct (pk_dl_perm _ _ _ HD1 HD2 HPD) as [HF1 HF2].
    assert (B3 : ent_b3 pack_form b0 x E1 E2 E3 Dp = b0).
    { rewrite ent_b3_eq by exact HL. unfold ent_b2. rewrite Ok, B1.
      apply pk_cancel; [exact HL | exact GT | exact HF1 | exact HF2]. }
    unfold ent_brej. destruct (Z.eqb_spec (ent_took x) 0) as [T0|T1]; [exact B3|].
    rewrite B3. destruct (WS T1) as (ok & res & Ejr & _ & HPs & HNs).
    assert (GS : grow_up trs) by (pose proof (jr_grow_up jr_strtod (zb x) ok) as G'; rewrite Ejr in G'; exact G').
    apply pk_cancel; [exact HL | exact GS | exact HPs | exact HNs].
Qed.
