(* B twin (fm.asan-ubsan) of lib/A/FMW_hp_model.v at a working branch 433b7106168: has_prefixed (G2), the pure steps of
   the loop invariant. No image numeral; the only change is the Require of lib.B FMH_Rt (FMH_Rt is per-image by
   its Requires, row B4b). INV a: no token starts at an index j whose location would start before a (fm's plain proof
   lib/Prog/has_prefixed.v hp_loop :146). The runtime answers (FMH_Rt.v occ_at, first_occ, no_occ, strn_eq) meet
   has_prefixed_model.v's mt and ManifestModel.token_at here. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Rt.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel has_prefixed_model.
Import ListNotations.
Open Scope Z_scope.

Section m.
Variables (tb pre lb : list Z) (P : nat).
Hypothesis HP : length pre = P.

Definition INV (a : nat) : Prop :=
  forall j, (j + length pre + 1 < a)%nat -> ManifestModel.token_at tb pre lb j = false.

Lemma mt_occ : forall b j, (b <= length tb)%nat -> has_prefixed_model.mt tb lb (b + j) = true ->
  occ_at (skipn b tb) lb j.
Proof.
intros b j Hb H. rewrite <- (has_prefixed_model.mt_skipn tb lb b j Hb) in H. unfold has_prefixed_model.mt in H.
apply andb_true_iff in H as [H1 H2]. split; [apply Nat.leb_le; exact H1|].
apply ManifestModel.zl_eqb_eq. exact H2.
Qed.

Lemma inv_step1 : forall a, INV a ->
  ((P + 1 <= a)%nat -> ManifestModel.token_at tb pre lb (a - P - 1) = false) -> INV (S a).
Proof.
intros a H1 H2 j Hj. exact (has_prefixed_model.inv_step tb pre lb a H1 ltac:(rewrite HP; exact H2) j Hj).
Qed.

(* the token at start = a - P - 1 needs at[-1] = ':' *)
Lemma tok_colon : forall a, (P + 1 <= a)%nat -> ManifestModel.byte_at tb (a - 1) <> 58 ->
  ManifestModel.token_at tb pre lb (a - P - 1) = false.
Proof.
intros a Ha Hc. apply not_true_iff_false. intro H. unfold ManifestModel.token_at in H. cbv zeta in H.
repeat rewrite andb_true_iff in H. destruct H as [[[[[_ _] H3] _] _] _].
rewrite HP in H3. replace (a - P - 1 + P)%nat with (a - 1)%nat in H3 by lia. apply Z.eqb_eq in H3. contradiction.
Qed.

(* strncmp's answer over plen bytes is the prefix comparison when both ranges lie inside the text *)
Lemma strn_eq_firstn : forall l1 l2, (P <= length l1)%nat -> (P <= length l2)%nat ->
  strn_eq P l1 l2 <-> firstn P l1 = firstn P l2.
Proof.
intros l1 l2 H1 H2. unfold strn_eq. rewrite !has_prefixed_model.firstn_app_long by lia. reflexivity.
Qed.

Lemma tok_prefix : forall a q, pre = firstn P (skipn q tb) -> (q + P <= length tb)%nat -> (a <= length tb)%nat ->
  (P + 1 <= a)%nat -> ~ strn_eq P (skipn (a - P - 1) tb) (skipn q tb) ->
  ManifestModel.token_at tb pre lb (a - P - 1) = false.
Proof.
intros a q Hpre Hq Ha HPa Hne. apply not_true_iff_false. intro H. unfold ManifestModel.token_at in H. cbv zeta in H.
repeat rewrite andb_true_iff in H. destruct H as [[[[[_ H2] _] _] _] _].
apply ManifestModel.zl_eqb_eq in H2. rewrite HP in H2. apply Hne.
apply strn_eq_firstn; [rewrite length_skipn; lia | rewrite length_skipn; lia |]. rewrite H2, Hpre. reflexivity.
Qed.

(* the byte before start is '.' or a name character *)
Lemma tok_before : forall a, (0 < a - P - 1)%nat ->
  ManifestModel.byte_at tb (a - P - 2) = 46 \/ ManifestModel.name_char (ManifestModel.byte_at tb (a - P - 2)) = true ->
  ManifestModel.token_at tb pre lb (a - P - 1) = false.
Proof.
intros a Ha Hb. apply not_true_iff_false. intro H. unfold ManifestModel.token_at in H. cbv zeta in H.
repeat rewrite andb_true_iff in H. destruct H as [[_ HM] _].
destruct (a - P - 1)%nat as [|j'] eqn:E; [lia|].
replace j' with (a - P - 2)%nat in HM by lia.
apply andb_true_iff in HM as [H1 H2].
destruct Hb as [Hb | Hb]; rewrite Hb in *.
- rewrite Z.eqb_refl in H2. cbn in H2. discriminate H2.
- cbn in H1. discriminate H1.
Qed.

(* the byte after the location is a name character *)
Lemma tok_after : forall a, (P + 1 <= a)%nat ->
  ManifestModel.name_char (ManifestModel.byte_at tb (a + length lb)) = true ->
  ManifestModel.token_at tb pre lb (a - P - 1) = false.
Proof.
intros a Ha Hn. apply not_true_iff_false. intro H. unfold ManifestModel.token_at in H. cbv zeta in H.
repeat rewrite andb_true_iff in H. destruct H as [_ H6].
rewrite HP in H6. replace (a - P - 1 + P + 1 + length lb)%nat with (a + length lb)%nat in H6 by lia.
rewrite Hn in H6. cbn in H6. discriminate H6.
Qed.

(* every check passed: a token at start *)
Lemma tok_hit : forall a q, pre = firstn P (skipn q tb) -> (q + P <= length tb)%nat -> (P + 1 <= a)%nat ->
  has_prefixed_model.mt tb lb a = true -> ManifestModel.byte_at tb (a - 1) = 58 ->
  strn_eq P (skipn (a - P - 1) tb) (skipn q tb) ->
  ((a - P - 1)%nat = O \/
   ((0 < a - P - 1)%nat /\ ManifestModel.byte_at tb (a - P - 2) <> 46 /\
    ManifestModel.name_char (ManifestModel.byte_at tb (a - P - 2)) = false)) ->
  ManifestModel.name_char (ManifestModel.byte_at tb (a + length lb)) = false ->
  ManifestModel.token tb pre lb = true.
Proof.
intros a q Hpre Hq HPa Hmt Hc Hs Hb Hn.
pose proof (has_prefixed_model.mt_len _ _ _ Hmt) as Hlen.
apply (has_prefixed_model.token_true tb pre lb (a - P - 1)).
assert (Hm : has_prefixed_model.mt tb lb (a - P - 1 + length pre + 1) = true)
  by (rewrite HP; replace (a - P - 1 + P + 1)%nat with a by lia; exact Hmt).
rewrite (has_prefixed_model.token_at_match tb pre lb (a - P - 1) Hm). rewrite HP.
replace (a - P - 1 + P + 1 + length lb)%nat with (a + length lb)%nat by lia.
replace (a - P - 1 + P)%nat with (a - 1)%nat by lia.
assert (Ep : ManifestModel.zl_eqb (firstn P (skipn (a - P - 1) tb)) pre = true).
{ apply ManifestModel.zl_eqb_eq. rewrite Hpre. apply strn_eq_firstn; [rewrite length_skipn; lia | rewrite length_skipn; lia |].
  exact Hs. }
assert (Ej : match (a - P - 1)%nat with
             | O => true
             | S j' => negb (ManifestModel.name_char (ManifestModel.byte_at tb j')) &&
                       negb (ManifestModel.byte_at tb j' =? 46)
             end = true).
{ destruct (a - P - 1)%nat as [|j'] eqn:E; [reflexivity|].
  destruct Hb as [Hb | (_ & Hb1 & Hb2)]; [first [discriminate Hb | rewrite E in Hb; discriminate Hb]|].
  replace j' with (a - P - 2)%nat by lia. rewrite Hb2. apply Z.eqb_neq in Hb1. rewrite Hb1. reflexivity. }
rewrite Ep, Hc, Z.eqb_refl, Ej, Hn. reflexivity.
Qed.

(* no occurrence at or after b, and INV b: no token *)
Lemma tok_none : forall b, INV b -> (forall k, (b <= k)%nat -> has_prefixed_model.mt tb lb k = false) ->
  ManifestModel.token tb pre lb = false.
Proof. intros b H1 H2. exact (has_prefixed_model.token_false tb pre lb b H2 H1). Qed.

(* strstr from b found nothing *)
Lemma noocc_mt : forall b, no_occ (skipn b tb) lb -> forall k, (b <= k)%nat -> has_prefixed_model.mt tb lb k = false.
Proof.
intros b Hno k Hk. destruct (Nat.le_gt_cases b (length tb)) as [Hb | Hb].
- destruct (has_prefixed_model.mt tb lb k) eqn:E; [|reflexivity]. exfalso.
  apply (Hno (k - b)%nat). apply mt_occ; [exact Hb|]. replace (b + (k - b))%nat with k by lia. exact E.
- apply has_prefixed_model.mt_far. lia.
Qed.

(* strstr from b found its first occurrence at b + j: INV carries over the skipped indices *)
Lemma first_occ_inv : forall b j, INV b -> first_occ (skipn b tb) lb j -> INV (b + j).
Proof.
intros b j H (Hocc & Hmin) j0 Hj0. apply (has_prefixed_model.inv_skip tb pre lb b j H); [|exact Hj0].
intros k Hk. destruct (has_prefixed_model.mt tb lb k) eqn:E; [|reflexivity]. exfalso.
destruct (Nat.le_gt_cases b (length tb)) as [Hb | Hb].
- apply (Hmin (k - b)%nat); [lia|]. apply mt_occ; [exact Hb|]. replace (b + (k - b))%nat with k by lia. exact E.
- destruct Hocc as (Hl & _). rewrite length_skipn in Hl. lia.
Qed.

(* the occurrence found is a match in the text *)
Lemma first_occ_mt : forall b j, (b <= length tb)%nat -> first_occ (skipn b tb) lb j ->
  has_prefixed_model.mt tb lb (b + j) = true.
Proof.
intros b j Hb ((Hl & He) & _). rewrite <- (has_prefixed_model.mt_skipn tb lb b j Hb). unfold has_prefixed_model.mt.
apply andb_true_iff. split; [apply Nat.leb_le; exact Hl|]. rewrite He. apply ManifestModel.zl_eqb_refl.
Qed.

(* the first strstr: INV holds at the first occurrence *)
Lemma INV_0 : INV 0.
Proof. intros j Hj. lia. Qed.
End m.
