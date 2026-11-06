(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk HeapIface HeapIfaceA HeapIfaceAEx.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem ArtRuns ArtBridge EatInitCache EatPopulate1 EatCls EatClsGfa2 EatCARSpec EatFxBatch3 EatSecRSpec EatWrapPure EatInvMallocPure EarInv EarInvFreePure EarCreditQ EarCreditC EarCredit EarCreditT.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma art_items_bytes : forall bs, art_batches_bytes bs = 8192 * Z.of_nat (length bs) + art_ibytes (art_items bs).
Proof.
  induction bs as [|b r IH]; [rewrite arq_bytes_nil; change (art_items []) with (@nil (Z * Z)); rewrite art_ibytes_nil; cbn [length]; lia|].
  rewrite arq_bytes_cons, art_items_cons, art_ibytes_app, IH. cbn [length]. rewrite Nat2Z.inj_succ. lia.
Qed.

Lemma art_nq_count : forall bs, art_nq bs = Z.of_nat (length bs) + Z.of_nat (length (art_items bs)).
Proof.
  induction bs as [|b r IH]; [reflexivity|]. unfold art_nq in *. cbn [fold_right length]. rewrite art_items_cons, length_app, IH. lia.
Qed.

Lemma art_in_multiples : forall q (k : nat) i, 0 <= i < Z.of_nat k -> In (q * i) (map (fun j => q * Z.of_nat j) (seq 0 k)).
Proof.
  intros q k i Hi. apply in_map_iff. exists (Z.to_nat i). split; [rewrite Z2Nat.id by lia; reflexivity|]. apply in_seq. lia.
Qed.

Lemma art_cls_count : forall c cl, 1 <= c <= 30 -> art_cls_ok c cl ->
  32 * (Z.of_nat (length (cl_cache cl)) + Z.of_nat (length (cl_free cl))) <= cl_au cl.
Proof.
  intros c cl Hc OK.
  destruct OK as (_ & (Hau0 & _) & _ & _ & (k & Eau) & _ & _ & _ & _ & FA & ND).
  destruct (art_class_size_facts c Hc) as ((Hsz32 & Hsz64) & Hsz16).
  set (sz := AsanTab.class_size c) in *.
  assert (Hk : 0 <= k) by nia.
  rewrite <- Nat2Z.inj_add, <- length_app.
  assert (LEN : (length (cl_cache cl ++ cl_free cl) <= length (map (fun j => (sz * Z.of_nat j)%Z) (seq 0 (Z.to_nat k))))%nat).
  { apply (art_inj_length Z Z (fun w => 16 * w)).
    - apply base.NoDup_ListNoDup. exact ND.
    - intros x y _ _ E. lia.
    - intros w Hw. pose proof (proj1 (Forall_forall _ _) FA w Hw) as (W0 & W1 & (i & Ei)). rewrite Ei. apply art_in_multiples. rewrite Z2Nat.id by exact Hk. nia. }
  rewrite length_map, length_seq in LEN. apply Nat2Z.inj_le in LEN. rewrite Z2Nat.id in LEN by exact Hk. nia.
Qed.

Lemma art_cost_sec_nonull : forall l, (forall len r, ~ In (AMmapNull len r) l) -> art_cost_sec l = 0.
Proof.
  induction l as [|e r IH]; intros H; [reflexivity|]. unfold art_cost_sec in *. cbn [fold_right].
  rewrite (IH (fun len r0 Hin => H len r0 (or_intror Hin))).
  destruct e as [a len|len r0|a len|a len|a len]; try reflexivity. exfalso. exact (H len r0 (or_introl eq_refl)).
Qed.

Lemma art_nirr_items_skipn : forall spb k bs, art_nirr spb (art_items (skipn k bs)) <= art_nirr spb (art_items bs).
Proof.
  intros spb k bs. rewrite <- (firstn_skipn k bs) at 2. rewrite art_items_app, art_nirr_app. pose proof (art_nirr_range spb (art_items (firstn k bs))). lia.
Qed.

Section R.
Variable FSG : Type.
Variables (bound : Z) (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z)) (M : word -> option byte).
Hypothesis REPB : art_alloc_rep_b FSG bound rn G LB M.
Hypothesis Hbound : bound <= 2 ^ 29.
Variables (BUDGET : Z) (cr : credit).

Hypothesis CRED : art_credit_ok FSG BUDGET rn (art_gs_drain G) LB cr.

Let qs := g_qt FSG G ++ g_qg FSG G.
Let gd := g_qg FSG G ++ g_qt FSG G.

Lemma art_rcyb_items_pos : art_items_pos qs.
Proof.
  intros b it Hb Hit. pose proof REPB as (_ & _ & _ & _ & CH & SECR & QR & _). destruct QR as (_ & _ & _ & _ & _ & _ & _ & ITEMS & _).
  destruct (ITEMS b it Hb Hit) as [(c & w & Hc & OKw & Est)|(s & Hs & Hq & Eu & En)].
  - destruct (CH c Hc) as (_ & _ & _ & CW). cbv zeta in CW. specialize (CW w OKw). rewrite Est in CW. destruct CW as (_ & _ & (b1 & _ & _ & _ & _ & Hn) & _). lia.
  - destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & PER & _). destruct (In_nth_error _ _ Hs) as (i & Hi). destruct (PER i s Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & Q & _).
    rewrite Hq in Q. destruct Q as ((b1 & _ & _ & _ & _ & Hn) & _). rewrite <- En. lia.
Qed.

Lemma art_rcyb_items_pos_gd : art_items_pos gd.
Proof.
  pose proof art_rcyb_items_pos as P. unfold qs in P. apply art_items_pos_app in P. destruct P as (Pt & Pg). unfold gd. apply art_items_pos_app. split; assumption.
Qed.

Lemma art_rcyb_qbytes : art_batches_bytes gd <= 805306368.
Proof.
  pose proof REPB as (_ & _ & _ & _ & _ & _ & QR & _). destruct QR as (_ & _ & B1 & B2 & _). unfold gd. rewrite arq_bytes_app.
  change (2 ^ 28) with 268435456 in B2. change (2 ^ 29) with 536870912 in Hbound. lia.
Qed.

Lemma art_rcyb_irr : exists irr, 0 <= irr <= 4096 /\ art_nirr (rn_spb rn) (art_items gd) <= irr /\ art_qg_ok gd.
Proof.
  destruct CRED as (irr & C1 & C2 & C3 & C4 & _ & _ & _ & _ & _ & C10 & QT & QG).
  cbn [art_gs_drain g_qt g_qg] in C10, QG. fold gd in C10, QG. change (art_items ([] ++ gd)) with (art_items gd) in C10.
  pose proof (art_nirr_range (rn_spb rn) (art_hdrs LB)) as R0.
  exists irr. unfold KCNT in C4. split; [lia|]. split; [lia|exact QG].
Qed.

Lemma art_rcyb_nb : Z.of_nat (length gd) <= 17416.
Proof.
  destruct art_rcyb_irr as (irr & Hirr & NI & QG).
  apply (art_nb_small (rn_spb rn) gd irr QG art_rcyb_items_pos_gd NI Hirr). pose proof art_rcyb_qbytes. change (2 ^ 30) with 1073741824. lia.
Qed.

Lemma art_rcyb_merge_dead : 2 ^ 28 < art_batches_bytes (g_qg FSG G) + art_batches_bytes (g_qt FSG G) -> 16384 * Z.of_nat (length gd) <= art_batches_bytes gd.
Proof.
  intros BIG. assert (EB : art_batches_bytes gd = art_batches_bytes (g_qg FSG G) + art_batches_bytes (g_qt FSG G)) by (unfold gd; apply arq_bytes_app).
  change (2 ^ 28) with 268435456 in BIG. destruct art_rcyb_irr as (irr & Hirr & NI & QG).
  pose proof REPB as (_ & _ & _ & _ & _ & _ & QR & _). destruct QR as (_ & _ & B1 & B2 & _).
  destruct (art_nb_bound (rn_spb rn) gd irr QG art_rcyb_items_pos_gd NI) as (X1 & X2).
  pose proof (art_nnonfull_range gd) as R. change (2 ^ 20) with 1048576 in X2. lia.
Qed.

Lemma art_rcyb_items : Z.of_nat (length (art_items gd)) <= 12587008.
Proof.
  destruct art_rcyb_irr as (irr & Hirr & NI & QG).
  assert (P1 : forall it, In it (art_items gd) -> 1 <= snd it).
  { intros it Hit. unfold art_items in Hit. apply in_flat_map in Hit. destruct Hit as (b & Hb & Hi). exact (art_rcyb_items_pos_gd b it Hb Hi). }
  pose proof (art_ibytes_irr (rn_spb rn) (art_items gd) P1) as IB.
  pose proof (art_items_bytes gd) as EB. pose proof art_rcyb_qbytes as QB. lia.
Qed.

Theorem art_rcyb_room : forall c, 1 <= c <= 30 ->
  Z.of_nat (length (cl_free (g_cls FSG G c))) + Z.of_nat (length (cl_cache (g_cls FSG G c))) + art_nq qs <= 134217720.
Proof.
  intros c Hc. pose proof REPB as (_ & _ & _ & (_ & PRIM & _) & _). destruct (PRIM c Hc) as (_ & OK & _).
  pose proof (art_cls_count c (g_cls FSG G c) Hc OK) as CNT. pose proof OK as (_ & (Hau0 & Haumu) & _ & _ & _ & Hmu & _).
  assert (ENQ : art_nq qs = art_nq gd) by (unfold qs, gd; rewrite !art_nq_app; lia).
  rewrite ENQ, art_nq_count. pose proof art_rcyb_nb as NB. pose proof art_rcyb_items as NI. lia.
Qed.
End R.
