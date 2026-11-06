From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel ManifestMem.
Import ListNotations.
Local Open Scope Z_scope.

Definition mt (h nd : list Z) (k : nat) : bool :=
  (k + length nd <=? length h)%nat && zl_eqb (firstn (length nd) (skipn k h)) nd.

Lemma find_sub_from_S : forall h nd i fuel,
  find_sub_from h nd i (S fuel) = if mt h nd i then Some i else find_sub_from h nd (S i) fuel.
Proof. reflexivity. Qed.

Lemma find_sub_from_some : forall fuel h nd i k, find_sub_from h nd i fuel = Some k ->
  (i <= k)%nat /\ mt h nd k = true /\ (forall k', (i <= k' < k)%nat -> mt h nd k' = false).
Proof.
  induction fuel as [|fuel IH]; intros h nd i k E; [discriminate|].
  rewrite find_sub_from_S in E. destruct (mt h nd i) eqn:C.
  - inversion E; subst. split; [lia|]. split; [exact C|]. intros; lia.
  - destruct (IH h nd (S i) k E) as (H1 & H2 & H3). split; [lia|]. split; [exact H2|].
    intros k' Hk'. destruct (Nat.eq_dec k' i) as [->|Hne]; [exact C|]. apply H3. lia.
Qed.

Lemma find_sub_from_none : forall fuel h nd i, find_sub_from h nd i fuel = None ->
  forall k, (i <= k < i + fuel)%nat -> mt h nd k = false.
Proof.
  induction fuel as [|fuel IH]; intros h nd i E k Hk; [lia|].
  rewrite find_sub_from_S in E. destruct (mt h nd i) eqn:C; [discriminate|].
  destruct (Nat.eq_dec k i) as [->|Hne]; [exact C|]. apply (IH h nd (S i) E). lia.
Qed.

Lemma mt_far : forall h nd k, (length h < k)%nat -> mt h nd k = false.
Proof.
  intros h nd k Hk. unfold mt. replace (k + length nd <=? length h)%nat with false; [reflexivity|].
  symmetry. apply Nat.leb_gt. lia.
Qed.

Lemma find_sub_none : forall h nd, find_sub h nd = None -> forall k, mt h nd k = false.
Proof.
  intros h nd E k. destruct (Nat.le_gt_cases k (length h)).
  - apply (find_sub_from_none (S (length h)) h nd 0 E). lia.
  - apply mt_far. lia.
Qed.

Lemma find_sub_some : forall h nd k, find_sub h nd = Some k ->
  mt h nd k = true /\ forall k', (k' < k)%nat -> mt h nd k' = false.
Proof.
  intros h nd k E. destruct (find_sub_from_some _ _ _ _ _ E) as (_ & H2 & H3). split; [exact H2|].
  intros k' Hk. apply H3. lia.
Qed.

Lemma mt_len : forall h nd k, mt h nd k = true -> (k + length nd <= length h)%nat.
Proof. intros h nd k M. unfold mt in M. apply andb_true_iff in M as [M _]. apply Nat.leb_le. exact M. Qed.

Lemma mt_skipn : forall h nd b k, (b <= length h)%nat -> mt (skipn b h) nd k = mt h nd (b + k).
Proof.
  intros h nd b k Hb. unfold mt. rewrite length_skipn, skipn_skipn.
  replace (k + b)%nat with (b + k)%nat by lia.
  replace (k + length nd <=? length h - b)%nat with (b + k + length nd <=? length h)%nat; [reflexivity|].
  destruct (Nat.leb_spec (b + k + length nd) (length h));
    destruct (Nat.leb_spec (k + length nd) (length h - b)); try reflexivity; lia.
Qed.

Lemma token_at_mt : forall t pre loc j, token_at t pre loc j = true -> mt t loc (j + length pre + 1) = true.
Proof.
  intros t pre loc j H. unfold token_at in H. cbv zeta in H.
  repeat rewrite andb_true_iff in H. destruct H as [[[[[H1 H2] H3] H4] H5] H6].
  unfold mt. apply andb_true_iff. split; assumption.
Qed.

Lemma token_true : forall t pre loc j, token_at t pre loc j = true -> token t pre loc = true.
Proof.
  intros t pre loc j H. apply (token_in t pre loc j); [|exact H].
  pose proof (mt_len _ _ _ (token_at_mt t pre loc j H)). lia.
Qed.

Lemma token_false : forall t pre loc b,
  (forall k, (b <= k)%nat -> mt t loc k = false) ->
  (forall j, (j + length pre + 1 < b)%nat -> token_at t pre loc j = false) ->
  token t pre loc = false.
Proof.
  intros t pre loc b NM INV. unfold token. apply not_true_iff_false. intro E.
  apply existsb_exists in E as (j & _ & Hj).
  destruct (Nat.lt_ge_cases (j + length pre + 1) b) as [Hl|Hl].
  - rewrite INV in Hj by exact Hl. discriminate.
  - pose proof (token_at_mt t pre loc j Hj) as M. rewrite NM in M by exact Hl. discriminate.
Qed.

Lemma inv_skip : forall t pre loc b i,
  (forall j, (j + length pre + 1 < b)%nat -> token_at t pre loc j = false) ->
  (forall k, (b <= k < b + i)%nat -> mt t loc k = false) ->
  forall j, (j + length pre + 1 < b + i)%nat -> token_at t pre loc j = false.
Proof.
  intros t pre loc b i INV NM j Hj.
  destruct (Nat.lt_ge_cases (j + length pre + 1) b) as [Hl|Hl]; [apply INV; exact Hl|].
  apply not_true_iff_false. intro E. pose proof (token_at_mt t pre loc j E) as M.
  rewrite NM in M by lia. discriminate.
Qed.

Lemma inv_step : forall t pre loc a,
  (forall j, (j + length pre + 1 < a)%nat -> token_at t pre loc j = false) ->
  ((length pre + 1 <= a)%nat -> token_at t pre loc (a - length pre - 1) = false) ->
  forall j, (j + length pre + 1 < S a)%nat -> token_at t pre loc j = false.
Proof.
  intros t pre loc a INV H j Hj.
  destruct (Nat.lt_ge_cases (j + length pre + 1) a) as [Hl|Hl]; [apply INV; exact Hl|].
  replace j with (a - length pre - 1)%nat by lia. apply H. lia.
Qed.

Lemma token_at_match : forall t pre loc j, mt t loc (j + length pre + 1) = true ->
  token_at t pre loc j =
  zl_eqb (firstn (length pre) (skipn j t)) pre && (byte_at t (j + length pre) =? 58)
  && match j with O => true | S j' => negb (name_char (byte_at t j')) && negb (byte_at t j' =? 46) end
  && negb (name_char (byte_at t (j + length pre + 1 + length loc))).
Proof.
  intros t pre loc j M. unfold mt in M. apply andb_true_iff in M as [M1 M2].
  unfold token_at. cbv zeta. rewrite M1, M2. cbn [andb]. rewrite andb_true_r. reflexivity.
Qed.

Lemma firstn_app_long : forall (l r : list Z) n, (n <= length l)%nat -> firstn n (l ++ r) = firstn n l.
Proof.
  intros l r n Hn. rewrite firstn_app. replace (n - length l)%nat with O by lia. cbn. apply app_nil_r.
Qed.

Lemma zbytes_skipn : forall bs k, zbytes (skipn k bs) = skipn k (zbytes bs).
Proof. intros. unfold zbytes. apply eq_sym, skipn_map. Qed.

Lemma length_zbytes : forall bs, length (zbytes bs) = length bs.
Proof. intros. unfold zbytes. apply length_map. Qed.

Lemma byte_at_zbytes : forall (tb ts : list byte) k d, (k <= length tb)%nat ->
  bv_unsigned (nth k (tb ++ Z_to_bv 8 0 :: ts) d) = byte_at (zbytes tb) k.
Proof.
  intros tb ts k d Hk. unfold byte_at, zbytes. destruct (Nat.lt_ge_cases k (length tb)) as [Hl|Hl].
  - rewrite app_nth1 by exact Hl. rewrite nth_indep with (d' := Z_to_bv 8 0) by exact Hl.
    apply eq_sym. apply (map_nth bv_unsigned tb (Z_to_bv 8 0) k).
  - replace k with (length tb) by lia. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
    rewrite nth_overflow by (rewrite length_map; lia). reflexivity.
Qed.

Lemma nc_char : forall c, 0 <= c < 256 ->
  name_char c = is_alnum c || ((c - 37) mod 2^64 <=? 58) && Z.testbit 0x0480000000200101 ((c - 37) mod 2^64)
                || (128 <=? c).
Proof.
  intros c Hc.
  assert (G : forallb (fun x => Bool.eqb (name_char x)
                (is_alnum x || ((x - 37) mod 2^64 <=? 58) && Z.testbit 0x0480000000200101 ((x - 37) mod 2^64)
                 || (128 <=? x))) (map Z.of_nat (seq 0 256)) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in G. specialize (G c). apply Bool.eqb_prop. apply G.
  apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.

Lemma byte_at_range : forall tb k, 0 <= byte_at (zbytes tb) k < 256.
Proof.
  intros tb k. unfold byte_at, zbytes. destruct (nth_in_or_default k (map bv_unsigned tb) 0) as [H|H].
  - apply in_map_iff in H as (b & <- & _). pose proof (bv_unsigned_in_range 8 b) as R. exact R.
  - rewrite H. lia.
Qed.
