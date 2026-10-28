(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatSim StoreOk As0Tables ArtMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatClsGfa2_b BatClsRefill_b BatCARSpec_b BatAlloc3Pure_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma art_cptr_apart : forall sz au w w0, 0 < sz -> art_cptr_ok sz au w -> art_cptr_ok sz au w0 -> w <> w0 ->
  16 * w0 + sz <= 16 * w \/ 16 * w + sz <= 16 * w0.
Proof.
  intros sz au w w0 Hsz (_ & _ & (i & Ei)) (_ & _ & (i0 & Ei0)) N.
  destruct (Z_lt_ge_dec i0 i) as [L|G]; [left|right].
  - assert (sz * (i0 + 1) <= sz * i) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
  - assert (i <> i0) by (intros E; subst i0; lia). assert (sz * (i + 1) <= sz * i0) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.

Lemma art_cptr_ok_dec : forall sz au w, 0 < sz -> {art_cptr_ok sz au w} + {~ art_cptr_ok sz au w}.
Proof.
  intros sz au w Hsz. unfold art_cptr_ok.
  destruct (Z_le_gt_dec 0 w) as [H0|H0]; [|right; intros (A & _); lia].
  destruct (Z_le_gt_dec (16 * w + sz) au) as [H1|H1]; [|right; intros (_ & A & _); lia].
  destruct (Z.eq_dec ((16 * w) mod sz) 0) as [H2|H2].
  - left. split; [exact H0|]. split; [exact H1|]. exists (16 * w / sz). pose proof (Z.div_mod (16 * w) sz ltac:(lia)) as D. lia.
  - right. intros (_ & _ & (i & Ei)). apply H2. rewrite Ei, Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma art_carved_complete : forall sz au new w0, 0 < sz -> sz mod 16 = 0 -> (exists ka, au = sz * ka) -> 0 <= new ->
  art_cptr_ok sz (au + new * sz) w0 -> ~ art_cptr_ok sz au w0 -> In w0 (art_carved au sz (Z.to_nat new)).
Proof.
  intros sz au new w0 Hsz Hsz16 (ka & Eau) Hnew (H0 & H1 & (i & Ei)) NOK.
  assert (Hgt : au < 16 * w0 + sz). { destruct (Z_lt_ge_dec au (16 * w0 + sz)) as [L|G]; [exact L|]. exfalso. apply NOK. split; [exact H0|]. split; [lia|]. exists i. exact Ei. }
  assert (Hi1 : ka <= i). { destruct (Z_le_gt_dec ka i) as [L|G]; [exact L|]. exfalso. assert (sz * (i + 1) <= sz * ka) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
  assert (Hi2 : i + 1 <= ka + new). { destruct (Z_le_gt_dec (i + 1) (ka + new)) as [L|G]; [exact L|]. exfalso. assert (sz * (ka + new + 1) <= sz * (i + 1)) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
  unfold art_carved. apply in_map_iff. exists (Z.to_nat (new - 1 - (i - ka))). split.
  - rewrite !Z2Nat.id by lia. replace (new - 1 - (new - 1 - (i - ka))) with (i - ka) by lia.
    replace (au + (i - ka) * sz) with (w0 * 16) by (rewrite Eau; lia). apply Z_div_mult. lia.
  - apply in_seq. lia.
Qed.

Lemma art_ca_pre_in : forall c cl w0,
  (In w0 (cl_cache (art_ca_pre c cl) ++ cl_free (art_ca_pre c cl)) <->
   In w0 (cl_cache cl ++ cl_free cl)
   \/ (cl_cache cl = [] /\ art_cls_needs_populate c cl = true /\ In w0 (art_carved (cl_au cl) (AsanTab.class_size c) (Z.to_nat (art_cls_new c cl))))).
Proof.
  intros c cl w0. unfold art_ca_pre. destruct (cl_cache cl) as [|z l] eqn:E.
  - rewrite art_cls_refill_eq. cbn [art_cls_take cl_cache cl_free].
    set (fl := cl_free (art_cls_pre_take c cl)). set (k := (length fl - art_refill_n c)%nat).
    assert (EQ : In w0 (skipn k fl ++ firstn k fl) <-> In w0 fl).
    { rewrite <- (firstn_skipn k fl) at 3. rewrite !in_app_iff. tauto. }
    rewrite EQ. unfold fl, art_cls_pre_take. destruct (art_cls_needs_populate c cl) eqn:NP.
    + unfold art_cls_populate. cbn [cl_free app]. rewrite in_app_iff. cbn [app]. split.
      * intros [H|H]; [left; exact H|right; repeat split; exact H].
      * intros [H|(_ & _ & H)]; [left; exact H|right; exact H].
    + cbn [app]. split; [intros H; left; exact H|intros [H|(_ & F & _)]; [exact H|discriminate F]].
  - split; [intros H; left; rewrite ?E in *; exact H|intros [H|(F & _)]; [rewrite ?E in *; exact H|discriminate F]].
Qed.

Lemma art_ca_pre_au : forall c cl,
  cl_au (art_ca_pre c cl) = cl_au cl
  \/ (cl_cache cl = [] /\ art_cls_needs_populate c cl = true /\ cl_au (art_ca_pre c cl) = cl_au cl + art_cls_new c cl * AsanTab.class_size c).
Proof.
  intros c cl. unfold art_ca_pre. destruct (cl_cache cl) as [|z l] eqn:E; [|left; reflexivity].
  rewrite art_cls_refill_eq. cbn [art_cls_take cl_au]. unfold art_cls_pre_take. destruct (art_cls_needs_populate c cl) eqn:NP; [|left; reflexivity].
  right. repeat split. 
Qed.

Lemma art_pop_in : forall clp w0, List.NoDup (cl_cache clp ++ cl_free clp) -> cl_cache clp <> [] ->
  (In w0 (cl_cache (art_cls_pop clp) ++ cl_free (art_cls_pop clp)) <-> In w0 (cl_cache clp ++ cl_free clp) /\ w0 <> last (cl_cache clp) 0).
Proof.
  intros clp w0 ND NE. cbn [art_cls_pop cl_cache cl_free]. set (l := last (cl_cache clp) 0).
  rewrite (app_removelast_last 0 NE) in ND. fold l in ND. rewrite (app_removelast_last 0 NE) at 2. fold l.
  set (rl := removelast (cl_cache clp)) in *. rewrite <- app_assoc in ND. cbn [app] in ND.
  apply NoDup_remove in ND. destruct ND as [_ NI]. rewrite !in_app_iff. cbn [In]. rewrite in_app_iff in NI. split.
  - intros H. split; [tauto|]. intros ->. tauto.
  - intros [[[H|[H|[]]]|H] N]; [left; exact H|exfalso; apply N; symmetry; exact H|right; exact H].
Qed.

Section Facts.
Variables (c : Z) (cl : art_cls).
Hypothesis Hc : 1 <= c <= 30.
Hypothesis OK : art_cls_ok c cl.
Let sz := AsanTab.class_size c.
Let w := art_ca_cptr c cl.
Let cl' := art_cls_pop (art_ca_pre c cl).

(* [comment removed for export] *)
#[using="Hc OK"] Lemma art_malloc_in_free : forall w0, art_cls_ok c (art_ca_pre c cl) -> In w0 (cl_cache cl' ++ cl_free cl') ->
  w0 <> w /\ (In w0 (cl_cache cl ++ cl_free cl) \/ ~ art_cptr_ok sz (cl_au cl) w0).
Proof.
  intros w0 OKp H. pose proof OKp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND). apply NoDup_ListNoDup in ND.
  apply (art_pop_in (art_ca_pre c cl) w0 ND (art_ca_pre_cache_ne c cl Hc OK)) in H. destruct H as [H N]. split; [exact N|].
  apply art_ca_pre_in in H. destruct H as [H|(_ & _ & H)]; [left; exact H|right].
  apply art_carved_in in H. destruct H as (i & Hi & Ew). intros (_ & B & _). fold sz in Ew.
  destruct OK as (_ & (Hau0 & _) & _ & _ & (ka & Eau) & _). destruct (art_class_size_facts c Hc) as (Hsz & Hsz16). fold sz in Eau, Hsz, Hsz16.
  assert (E16 : 16 * w0 = sz * (ka + i)).
  { rewrite Ew, Eau. replace (sz * ka + i * sz) with (sz * (ka + i)) by lia. pose proof (art_div16_mul sz (ka + i) Hsz16). lia. }
  assert (sz * ka <= sz * (ka + i)) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.

(* [comment removed for export] *)
#[using="Hc OK"] Lemma art_malloc_free_in : forall w0, art_cls_ok c (art_ca_pre c cl) -> art_cptr_ok sz (cl_au (art_ca_pre c cl)) w0 -> w0 <> w ->
  (art_cptr_ok sz (cl_au cl) w0 -> In w0 (cl_cache cl ++ cl_free cl)) -> In w0 (cl_cache cl' ++ cl_free cl').
Proof.
  intros w0 OKp V N OLD. pose proof OKp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ND). apply NoDup_ListNoDup in ND.
  apply (art_pop_in (art_ca_pre c cl) w0 ND (art_ca_pre_cache_ne c cl Hc OK)). split; [|exact N].
  apply art_ca_pre_in. destruct (art_class_size_facts c Hc) as (Hsz & Hsz16). fold sz in Hsz, Hsz16.
  destruct (art_cptr_ok_dec sz (cl_au cl) w0 ltac:(lia)) as [Y|NO]; [left; exact (OLD Y)|].
  destruct (art_ca_pre_au c cl) as [E|(E1 & E2 & E3)]; [rewrite E in V; contradiction|]. right. split; [exact E1|]. split; [exact E2|].
  fold sz in E3. rewrite E3 in V. destruct OK as (_ & (Hau0 & Haumu) & _ & _ & Hka & _). fold sz in Hka.
  apply art_carved_complete; try assumption; [lia|].
  unfold art_cls_new. fold sz. apply Z.div_pos; lia.
Qed.
End Facts.

Lemma art_ca_pre_mu_cases : forall c cl,
  (cl_mu (art_ca_pre c cl) = cl_mu cl /\ cl_au (art_ca_pre c cl) = cl_au cl)
  \/ (cl_cache cl = [] /\ art_cls_needs_populate c cl = true /\ cl_mu (art_ca_pre c cl) = cl_mu cl + 262144).
Proof.
  intros c cl. unfold art_ca_pre. destruct (cl_cache cl) as [|z l] eqn:E; [|left; split; reflexivity].
  rewrite art_cls_refill_eq. cbn [art_cls_take cl_au cl_mu]. unfold art_cls_pre_take. destruct (art_cls_needs_populate c cl) eqn:NP; [|left; split; reflexivity].
  right. repeat split.
Qed.

(* [comment removed for export] *)
Lemma art_cptr_new_lo : forall sz au au' w0, 0 < sz -> (exists ka, au = sz * ka) -> art_cptr_ok sz au' w0 -> ~ art_cptr_ok sz au w0 -> au <= 16 * w0.
Proof.
  intros sz au au' w0 Hsz (ka & Eau) (H0 & H1 & (i & Ei)) NOK.
  assert (Hgt : au < 16 * w0 + sz). { destruct (Z_lt_ge_dec au (16 * w0 + sz)) as [L|G]; [exact L|]. exfalso. apply NOK. split; [exact H0|]. split; [lia|]. exists i. exact Ei. }
  destruct (Z_le_gt_dec ka i) as [L|G]. { assert (sz * ka <= sz * i) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
  exfalso. assert (sz * (i + 1) <= sz * ka) by (apply Z.mul_le_mono_nonneg_l; lia). lia.
Qed.
