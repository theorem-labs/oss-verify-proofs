(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require base.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk HeapIface HeapIfaceA HeapIfaceAEx.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem ArtRuns ArtBridge EatInitCache EatPopulate1 EatCls EatCARSpec EatFxBatch3 EatWrapPure EarInv EarInvFreePure EarCreditQ EarCreditC.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma art_cntw_irr : forall spb lo len l, spb + 7 * 2 ^ 32 <= lo -> art_cntw lo len l <= art_nirr spb l.
Proof.
  intros spb lo len l Hlo. unfold art_cntw, art_nirr. induction l as [|x r IH]; [cbn [List.filter length]; lia|].
  cbn [List.filter]. destruct (art_inw lo len x) eqn:E.
  - assert (I : art_irr spb x = true).
    { unfold art_inw in E. apply andb_true_iff in E. destruct E as (E & _). apply Z.leb_le in E. unfold art_irr. apply orb_true_iff. right. apply Z.leb_le. lia. }
    rewrite I. cbn [length]. rewrite !Nat2Z.inj_succ. lia.
  - destruct (art_irr spb x); cbn [length]; [rewrite Nat2Z.inj_succ; lia | lia].
Qed.

Lemma art_credit_perm : forall FSG BUDGET rn (G : art_gs FSG) (LB LB' : list (Z * Z)) cr,
  List.NoDup (map fst LB) -> List.NoDup (map fst LB') -> (forall b, In b LB <-> In b LB') ->
  art_credit_ok FSG BUDGET rn G LB cr -> art_credit_ok FSG BUDGET rn G LB' cr.
Proof.
  intros FSG BUDGET rn G LB LB' cr N1 N2 EQ (irr & C). exists irr.
  destruct (art_nirr_hdrs_perm (rn_spb rn) LB LB' N1 N2 EQ) as (E1 & E2). rewrite E1, E2. exact C.
Qed.

Section Cr.
Variable FSG : Type.
Variables (rn : art_run) (G : art_gs FSG) (LB : list (Z * Z)) (M : word -> option byte).
Hypothesis REP : art_alloc_rep FSG rn G LB M.
Hypothesis NDLB : base.NoDup (map fst LB).

Let qs := g_qt FSG G ++ g_qg FSG G.

Lemma art_cr_items_in : forall h n, art_in_batches qs h n -> In (h, n) (art_items qs).
Proof. intros h n (b & Hb & Hit). unfold art_items. apply in_flat_map. exists b. split; assumption. Qed.
Lemma art_cr_hdrs_in : forall u n, In (u, n) LB -> In (u - 16, n) (art_hdrs LB).
Proof. intros u n H. unfold art_hdrs. apply in_map_iff. exists (u, n). split; [reflexivity | exact H]. Qed.

Lemma art_cr_carved : forall c, 1 <= c <= 30 ->
  let cl := g_cls FSG G c in let rb := rn_spb rn + c * 2 ^ 32 in
  cl_au cl <= AsanTab.class_size c * (Z.of_nat (length (cl_cache cl)) + Z.of_nat (length (cl_free cl))
                                       + art_cntw rb (cl_au cl) (art_hdrs LB) + art_cntw rb (cl_au cl) (art_items qs)
                                       + (if c =? 24 then Z.of_nat (length qs) else 0)).
Proof.
  intros c Hc cl rb.
  destruct REP as (_ & _ & _ & (_ & PRIM & _) & CH & _).
  destruct (PRIM c Hc) as (_ & OK & _). fold cl in OK.
  destruct OK as (_ & (Hau0 & _) & _ & _ & (k & Eau) & _ & _ & _ & _ & _ & ND).
  destruct (art_class_size_facts c Hc) as ((Hsz32 & Hsz64) & Hsz16).
  set (sz := AsanTab.class_size c) in *.
  assert (Eq : sz = 16 * (sz / 16)). { pose proof (Z.div_mod sz 16 ltac:(lia)) as D. rewrite Hsz16 in D. lia. }
  set (q := sz / 16) in *. assert (Hq : 0 < q) by lia.
  assert (Hk : 0 <= k) by nia.
  specialize (CH c Hc). cbv zeta in CH. fold cl in CH. fold sz in CH. fold rb in CH. destruct CH as (_ & _ & _ & CW).
  pose proof (art_count_pure (g_st FSG G c) (cl_cache cl ++ cl_free cl) (art_hdrs LB) (art_items qs)
                (if c =? 24 then map bt_addr qs else []) rb sz q (Z.to_nat k) Eq Hq) as CNT.
  rewrite Z2Nat.id in CNT by exact Hk. rewrite <- Eau in CNT.
  assert (X : Z.of_nat (length (if c =? 24 then map bt_addr qs else [])) = (if c =? 24 then Z.of_nat (length qs) else 0)).
  { destruct (c =? 24); [rewrite length_map; reflexivity | reflexivity]. }
  rewrite X, length_app, Nat2Z.inj_add in CNT.
  assert (Hcnt : k <= Z.of_nat (length (cl_cache cl)) + Z.of_nat (length (cl_free cl))
                 + art_cntw rb (cl_au cl) (art_hdrs LB) + art_cntw rb (cl_au cl) (art_items qs) + (if c =? 24 then Z.of_nat (length qs) else 0)).
  { apply CNT. intros i Hi.
      assert (OKw : art_cptr_ok sz (cl_au cl) (q * i)). { unfold art_cptr_ok. split; [nia|]. split; [nia|]. exists i. nia. }
      specialize (CW (q * i) OKw).
      destruct (g_st FSG G c (q * i)) as [|u n|u n|].
    - exact (proj1 CW).
    - destruct CW as (C1 & C2 & C3 & (b1 & _ & _ & _ & _ & Hn) & _). split; [apply art_cr_hdrs_in; exact C1|]. split; nia.
    - destruct CW as (C2 & C3 & (b1 & _ & _ & _ & _ & Hn) & C4 & _). split; [apply art_cr_items_in; exact C4|]. split; nia.
    - destruct CW as (E24 & b & Hb & Eb). subst c. cbn [Z.eqb Pos.eqb]. apply in_map_iff. exists b. split; [rewrite Eb; nia | exact Hb]. }
  rewrite Eau at 1. nia.
Qed.

Lemma art_cr_items_pos : art_items_pos qs.
Proof.
  intros b it Hb Hit. pose proof REP as (_ & _ & _ & _ & CH & SECR & QR & _). destruct QR as (_ & _ & _ & _ & _ & _ & _ & ITEMS & _).
  destruct (ITEMS b it Hb Hit) as [(c & w & Hc & OKw & Est)|(s & Hs & Hq & Eu & En)].
  - destruct (CH c Hc) as (_ & _ & _ & CW). cbv zeta in CW. specialize (CW w OKw). rewrite Est in CW. destruct CW as (_ & _ & (b1 & _ & _ & _ & _ & Hn) & _). lia.
  - destruct SECR as (_ & _ & _ & _ & _ & _ & _ & _ & PER & _). destruct (In_nth_error _ _ Hs) as (i & Hi). destruct (PER i s Hi) as (_ & _ & _ & _ & _ & _ & _ & _ & Q & _).
    rewrite Hq in Q. destruct Q as ((b1 & _ & _ & _ & _ & Hn) & _). rewrite <- En. lia.
Qed.
Lemma art_batch_list_len1021 : forall (M0 : word -> option byte) bs f l b, art_batch_list M0 bs f l -> In b bs -> (length (bt_items b) <= 1021)%nat.
Proof.
  intros M0 bs. induction bs as [|x r IH]; intros f l b H Hb; [destruct Hb|].
  cbn [art_batch_list] in H. destruct H as (_ & Hl & _ & _ & _ & _ & Hr). destruct Hb as [<-|Hb]; [exact Hl|]. exact (IH _ _ b Hr Hb).
Qed.
Lemma art_cr_batch_len : forall b, In b qs -> (length (bt_items b) <= 1021)%nat.
Proof.
  intros b Hb. pose proof REP as (_ & _ & _ & _ & _ & _ & QR & _). destruct QR as ((f1 & l1 & _ & _ & _ & _ & BL1) & (f2 & l2 & _ & _ & _ & _ & BL2) & _).
  apply in_app_or in Hb. destruct Hb as [Hb|Hb]; [exact (art_batch_list_len1021 _ _ _ _ b BL1 Hb) | exact (art_batch_list_len1021 _ _ _ _ b BL2 Hb)].
Qed.
Lemma art_cr_qbytes : art_batches_bytes (g_qt FSG G) <= 2 ^ 20 /\ art_batches_bytes (g_qg FSG G) <= 2 ^ 28.
Proof. pose proof REP as (_ & _ & _ & _ & _ & _ & QR & _). destruct QR as (_ & _ & B1 & B2 & _). split; assumption. Qed.

Variable BUDGET : Z.
Variable cr : credit.
Hypothesis CRED : art_credit_ok FSG BUDGET rn G LB cr.

Lemma art_cr_nb : Z.of_nat (length qs) <= 4400 /\ Z.of_nat (length (art_items qs)) <= 1021 * 4400
                  /\ exists irr, 0 <= irr <= 4096 /\ art_nirr (rn_spb rn) (art_hdrs LB) + art_nirr (rn_spb rn) (art_items qs) <= irr
                                 /\ Z.of_nat (length LB) <= KCNT.
Proof.
  destruct CRED as (irr & C1 & C2 & C3 & C4 & _ & _ & _ & _ & _ & C10 & QT & QG). fold qs in C10.
  pose proof art_cr_items_pos as P. unfold qs in P. apply art_items_pos_app in P. destruct P as (Pt & Pg).
  destruct art_cr_qbytes as (Bt & Bg).
  assert (Hirr : 0 <= irr <= 4096) by (unfold KCNT in C4; lia).
  pose proof (art_nirr_range (rn_spb rn) (art_hdrs LB)) as R0.
  unfold qs in C10. rewrite art_items_app, art_nirr_app in C10.
  pose proof (art_nirr_range (rn_spb rn) (art_items (g_qt FSG G))) as R1. pose proof (art_nirr_range (rn_spb rn) (art_items (g_qg FSG G))) as R2.
  destruct (art_nb_bound (rn_spb rn) (g_qg FSG G) irr QG Pg ltac:(lia)) as (G1 & G2).
  destruct (art_nb_bound (rn_spb rn) (g_qt FSG G) irr (art_qg_ok_of_qt _ QT Pt) Pt ltac:(lia)) as (T1 & T2).
  assert (NB : Z.of_nat (length qs) <= 4400).
  { unfold qs. rewrite length_app, Nat2Z.inj_add. change (2 ^ 20) with 1048576 in *. change (2 ^ 28) with 268435456 in *. lia. }
  split; [exact NB|]. split.
  - pose proof (art_items_length qs art_cr_batch_len). lia.
  - exists irr. split; [exact Hirr|]. split; [unfold qs; rewrite art_items_app, art_nirr_app; lia|]. unfold KCNT in *. lia.
Qed.

Lemma art_cr_room : forall c, 1 <= c <= 30 ->
  let cl := g_cls FSG G c in
  art_cls_needs_populate c cl = true ->
  cl_mu cl + 262144 <= 3758096384 /\ art_cls_mfa' cl (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <= 536870912.
Proof.
  intros c Hc cl NP.
  pose proof (art_cr_carved c Hc) as CV. cbv zeta in CV. fold cl in CV.
  destruct art_cr_nb as (NB & NI & irr & Hirr & Cirr & HLB).
  pose proof REP as (_ & _ & _ & (_ & PRIM & _) & _). destruct (PRIM c Hc) as (_ & OK & _). fold cl in OK.
  pose proof OK as (Hcache & (Hau0 & Haumu) & Hrem & _ & _ & Hmu & (kf & Emfa) & (Hmfa0 & Hmfa1) & Hnf4 & _).
  destruct (art_class_size_facts c Hc) as ((Hsz32 & Hsz64) & Hsz16).
  pose proof (art_refill_n_range c ltac:(lia)) as RN.
  unfold art_cls_needs_populate in NP. apply Nat.ltb_lt in NP.
  set (sz := AsanTab.class_size c) in *.
  set (rb := rn_spb rn + c * 2 ^ 32) in *.
  pose proof (art_cntw_range rb (cl_au cl) (art_hdrs LB)) as W1. pose proof (art_cntw_range rb (cl_au cl) (art_items qs)) as W2.
  assert (HL : Z.of_nat (length (art_hdrs LB)) = Z.of_nat (length LB)) by (unfold art_hdrs; rewrite length_map; reflexivity).
  assert (AU : cl_au cl <= 3758096384 - 2 * 262144).
  { destruct (Z_le_gt_dec c 6) as [C6|C7].
    - assert (Hsz : sz <= 192) by (unfold sz, AsanTab.class_size; destruct (Z.leb_spec c 16); lia).
      assert (B : Z.of_nat (length (cl_cache cl)) + Z.of_nat (length (cl_free cl)) + art_cntw rb (cl_au cl) (art_hdrs LB) + art_cntw rb (cl_au cl) (art_items qs)
                  + (if c =? 24 then Z.of_nat (length qs) else 0) <= 16 + 8 + 8192 + 1021 * 4400 + 0).
      { destruct (Z.eqb_spec c 24); [lia|]. unfold KCNT in HLB. lia. }
      nia.
    - assert (I1 : art_cntw rb (cl_au cl) (art_hdrs LB) <= art_nirr (rn_spb rn) (art_hdrs LB)) by (apply art_cntw_irr; unfold rb; lia).
      assert (I2 : art_cntw rb (cl_au cl) (art_items qs) <= art_nirr (rn_spb rn) (art_items qs)) by (apply art_cntw_irr; unfold rb; lia).
      assert (B : Z.of_nat (length (cl_cache cl)) + Z.of_nat (length (cl_free cl)) + art_cntw rb (cl_au cl) (art_hdrs LB) + art_cntw rb (cl_au cl) (art_items qs)
                  + (if c =? 24 then Z.of_nat (length qs) else 0) <= 16 + 8 + 4096 + 4400).
      { destruct (c =? 24); lia. }
      nia. }
  split; [lia|].
  pose proof (art_new_le c cl Hc OK) as Hnew.
  unfold art_cls_mfa'. destruct (4 * (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) <=? cl_mfa cl); [exact Hmfa1|].
  assert (X : (4 * (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) + 262143) / 262144 <= 1); [|lia].
  assert ((4 * (Z.of_nat (length (cl_free cl)) + art_cls_new c cl) + 262143) / 262144 < 2); [|lia].
  apply Z.div_lt_upper_bound; lia.
Qed.
End Cr.
