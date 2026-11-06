(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YG0m.v, with its module paths changed. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Lemma preg_room : forall U pp cc bb s s1 c n,
WfP U pp cc bb s1 -> 1 <= c <= 31 -> 1 <= pp -> st_cache_inited s1 = true -> regs_only s s1 -> cdef s1 c = cdef s c ->
pc_chunks (cache s1 c) = [] -> n <= 8 -> preg s c ->
fa_len (rg_free (reg s1 c)) < n ->
rg_mapped_user (reg s1 c) + kUserMapSize <= kUserMapSize * EV_MAX /\
(st_nev s1 <= EV_MAX \/ rg_alloc_user (reg s1 c) <= class_size c * (65536 - 10240)).
Proof.
intros U pp cc bb s s1 c n W1 Hc Hpp Hi1 RO1 DEF1 El N8 Hreg Hlt.
pose proof (class_ok c Hc) as (Ksz & _).
pose proof (wf_classes _ _ _ _ _ W1 c Hc) as C1. unfold wf_class in C1. rewrite Hi1 in C1.
assert (NR1 : nrecZ s1 c = nrecZ s c) by (apply nrecZ_regs_only; exact RO1).
destruct Hreg as [Hsmall | (D0 & HB & HCT)].
- destruct RO1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rnev).
pose proof (mapped_user_bound_small U pp cc bb s1 c W1 Hc ltac:(rewrite Rnev; exact Hsmall)) as MB.
split; [unfold kUserMapSize, EV_MAX in *; lia | left; rewrite Rnev; exact Hsmall].
- rewrite <- DEF1 in D0. unfold cdef, class_elems in D0. rewrite <- NR1 in HB, HCT. unfold nrecZ in HB, HCT.
split; [exact (proom_big c (reg s1 c) (cache s1 c) true (chunk_offs s1 c) (batch_offs s1 c) n C1 Ksz El Hlt N8 D0 HB)|].
right. pose proof (exact_alloc c (reg s1 c) (cache s1 c) true (chunk_offs s1 c) (batch_offs s1 c) C1 El D0) as EA.
pose proof (fa_len_nonneg _ (wr_runs _ _ _ _ _ _ C1)) as F0. rewrite EA. nia.
Qed.
Lemma preg_xfer : forall s s' c,
st_nev s' <= st_nev s -> cdef s' c = cdef s c -> nrecZ s' c = nrecZ s c -> preg s c -> preg s' c.
Proof. intros s s' c NE D N [H|(D0 & HB & HC)]; [left; lia | right; rewrite D, N; auto]. Qed.
Lemma aregime_preg : forall s c, aregime s -> 1 <= c <= 31 -> preg s c.
Proof.
intros s c [H|(((CP & _) & HB & _) & _)] Hc; [left; lia | right]. destruct (HB c Hc) as [B1 B2]. split; [exact (CP c Hc) | split; assumption].
Qed.
Lemma aregime_preg_tick : forall s c, aregime s -> 1 <= c <= 31 -> preg (set_nev (st_nev s + 1) s) c.
Proof.
intros s c [H|(((CP & _) & HB & _) & _)] Hc; [left; cbn [st_nev set_nev]; lia | right]. destruct (HB c Hc) as [B1 B2].
split; [exact (CP c Hc) | split; assumption].
Qed.
Lemma sec_hulls_same : forall s s', st_secs s' = st_secs s -> sec_hulls s' = sec_hulls s.
Proof. intros s s' E. unfold sec_hulls. rewrite E. reflexivity. Qed.
Lemma sec_hulls_dead : forall s s' r sm, nth_error (st_secs s) r = Some sm ->
st_secs s' = lupd (st_secs s) r (mkSec (sm_len sm) (sm_size sm) false) -> sec_hulls s' = sec_hulls s.
Proof.
intros s s' r sm Hn E. unfold sec_hulls. rewrite E. clear E. revert r Hn. induction (st_secs s) as [|a t IH]; intros r Hn; [destruct r; discriminate|].
destruct r as [|r]; cbn [lupd fold_right].
- cbn in Hn. injection Hn as ->. cbn [sm_len]. reflexivity.
- cbn in Hn. rewrite (IH r Hn). reflexivity.
Qed.
Lemma aregime_mid_tick : forall s, aregime s -> aregime_mid (set_nev (st_nev s + 1) s).
Proof.
intros s [H|((_ & _ & _ & HC & _) & HE & HH)]; [left; cbn [st_nev set_nev]; lia | right].
cbn [st_nev set_nev]. change (sec_hulls (set_nev (st_nev s + 1) s)) with (sec_hulls s). change (st_chunks (set_nev (st_nev s + 1) s)) with (st_chunks s).
repeat split; lia.
Qed.
Lemma aregime_mid_xfer : forall s s', aregime_mid s -> st_nev s' = st_nev s -> st_secs s' = st_secs s ->
(length (st_chunks s') <= length (st_chunks s))%nat -> aregime_mid s'.
Proof.
intros s s' [H|(HE & HH & HC)] NE SE CK; [left; lia | right]. rewrite NE, (sec_hulls_same s s' SE). repeat split; lia.
Qed.
Definition refill_reg (S : astate) (c : Z) : Prop :=
prim_user_mapped S + kUserMapSize <= kUserMapSize * st_nev S /\ preg S c /\ aregime_mid S.
Lemma refill_reg_init : forall S c, 0 <= c <= 31 -> refill_reg S c ->
refill_reg (set_cache_inited true (set_cache (init_caches (st_cache S)) S)) c.
Proof.
intros S c Hc (H1 & H2 & H3). split; [exact H1|]. split; [|exact H3].
apply (preg_xfer S); [cbn [st_nev set_cache_inited set_cache]; lia | | reflexivity | exact H2].
apply cdef_ext; [reflexivity|]. unfold class_elems. rewrite (cache_after_init S c Hc). reflexivity.
Qed.
Lemma refill_reg_tick : forall S X c, aregime S -> 1 <= c <= 31 ->
st_nev X = st_nev S + 1 -> st_secs X = st_secs S -> length (st_chunks X) = length (st_chunks S) ->
cdef X c = cdef S c -> nrecZ X c = nrecZ S c ->
prim_user_mapped X + kUserMapSize <= kUserMapSize * st_nev X -> refill_reg X c.
Proof.
intros S X c R Hc NE SE CK D N P. split; [exact P|]. split.
- destruct R as [H|(((CP & _) & HB & _) & _)]; [left; lia | right]. destruct (HB c Hc) as [B1 B2]. rewrite D, N. split; [exact (CP c Hc) | split; assumption].
- destruct R as [H|((_ & _ & _ & HC & _) & HE & HH)]; [left; lia | right]. rewrite NE, (sec_hulls_same S X SE), CK. repeat split; lia.
Qed.
Lemma qthread_bytes_nonneg : forall U pp cc bb s, WfP U pp cc bb s -> 0 <= qc_bytes (st_qthread s).
Proof.
intros U pp cc bb s W. pose proof (wf_quarantine _ _ _ _ _ W) as Q. rewrite (wq_bytes_t _ Q). apply sum_bytes_nonneg.
apply Forall_forall. intros k Hk. pose proof (proj1 (Forall_forall _ _) (wq_items _ Q) k) as X.
assert (Hin : In k (q_items s)) by (unfold q_items, all_batches; rewrite flat_map_app; apply in_app_iff; left; exact Hk).
destruct (X Hin) as [Hc _]. pose proof (proj1 (Forall_forall _ _) (wf_chunks _ _ _ _ _ W) k Hc) as [Hn _]. lia.
Qed.
Theorem batches_len_qloose : forall U pp cc bb s, WfP U pp cc bb s -> qloose s -> Z.of_nat (length (all_batches s)) <= 2 ^ 17.
Proof.
intros U pp cc bb s W (Q1 & Q2 & _). apply (batches_len_bound U pp cc bb s W); [lia | exact (qthread_bytes_nonneg U pp cc bb s W)].
Qed.
Theorem batches_len_fuel : forall U pp cc bb s, WfP U pp cc bb s -> qloose s -> Z.of_nat (length (all_batches s)) <= 16384.
Proof.
intros U pp cc bb s W (Q1 & Q2 & _). destruct (wf_regime _ _ _ _ _ W) as [Hs|[_ HC]].
- pose proof (batches_bound U pp cc bb s W Hs). unfold EV_MAX in *. lia.
- pose proof (wf_slack _ _ _ _ _ W) as (_ & C0 & _). pose proof (wf_quarantine _ _ _ _ _ W) as Q.
destruct (qbatches_bound U pp cc bb s W) as (ng & NG0 & C1 & C2).
pose proof (almost_full_items _ (wq_tfull _ Q)) as T1. pose proof (q_items_le_chunks U pp cc bb s W) as QL.
unfold q_items, all_batches in *. rewrite flat_map_app, !length_app in *. rewrite !Nat2Z.inj_add.
unfold kBatchSlots, kQuarantineCacheMax in *. lia.
Qed.
