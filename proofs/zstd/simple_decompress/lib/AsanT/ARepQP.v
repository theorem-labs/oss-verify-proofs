(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase ARep ARepQ ARepFrame AHeapP AKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma size_of_class_24 : size_of_class K_BATCH_CLASS = 8192.
Proof. vm_compute. reflexivity. Qed.

Lemma batches_bytes_app : forall l1 l2, batches_bytes (l1 ++ l2) = batches_bytes l1 + batches_bytes l2.
Proof. induction l1 as [|b l1 IH]; intros l2; cbn; [reflexivity| rewrite IH; unfold batches_bytes; lia]. Qed.
Lemma batches_bytes_cons : forall b l, batches_bytes (b :: l) = b_size b + batches_bytes l.
Proof. reflexivity. Qed.
Lemma batches_bytes_nil : batches_bytes [] = 0.
Proof. reflexivity. Qed.

Lemma batches_bytes_lb : forall l, Forall (fun b => Q_BATCH_BYTES <= b_size b) l -> Q_BATCH_BYTES * Z.of_nat (length l) <= batches_bytes l.
Proof.
  induction l as [|b l IH]; intros HF; cbn [length]; [rewrite batches_bytes_nil; lia|].
  rewrite batches_bytes_cons. inversion HF; subst. specialize (IH ltac:(assumption)). unfold Q_BATCH_BYTES in *. lia.
Qed.
Lemma batches_bytes_In : forall l b, Forall (fun b => Q_BATCH_BYTES <= b_size b) l -> In b l -> Q_BATCH_BYTES <= b_size b <= batches_bytes l.
Proof.
  induction l as [|a l IH]; intros b HF Hin; [destruct Hin|].
  rewrite batches_bytes_cons. inversion HF; subst. pose proof (batches_bytes_lb l ltac:(assumption)) as LB.
  destruct Hin as [<-|Hin]; [unfold Q_BATCH_BYTES in *; lia|]. specialize (IH b ltac:(assumption) Hin). unfold Q_BATCH_BYTES in *; lia.
Qed.

Lemma qaddrs_app : forall L qs1 qs2, qaddrs L (qs1 ++ qs2) = qaddrs L qs1 ++ qaddrs L qs2.
Proof. intros. unfold qaddrs. apply map_app. Qed.
Lemma qfirst_cons : forall L q qs, qfirst L (q :: qs) = abatch_addr L (qb_slot q).
Proof. reflexivity. Qed.
Lemma qfirst_nil : forall L, qfirst L [] = 0. Proof. reflexivity. Qed.
Lemma qlast_nil : forall L, qlast L [] = 0. Proof. reflexivity. Qed.
Lemma qlast_app1 : forall L qs q, qlast L (qs ++ [q]) = abatch_addr L (qb_slot q).
Proof. intros. unfold qlast. rewrite qaddrs_app. cbn [qaddrs map]. apply last_last. Qed.
Lemma qfirst_app : forall L qs1 qs2, qs1 <> [] -> qfirst L (qs1 ++ qs2) = qfirst L qs1.
Proof. intros L [|q qs1] qs2 NE; [congruence| reflexivity]. Qed.
Lemma last_app_ne : forall {A} (l1 l2 : list A) d, l2 <> [] -> last (l1 ++ l2) d = last l2 d.
Proof.
  intros A l1 l2 d NE. rewrite (app_removelast_last d NE) at 1. rewrite app_assoc, last_last.
  reflexivity.
Qed.
Lemma qlast_app : forall L qs1 qs2, qs2 <> [] -> qlast L (qs1 ++ qs2) = qlast L qs2.
Proof.
  intros L qs1 qs2 NE. unfold qlast. rewrite qaddrs_app. apply last_app_ne.
  unfold qaddrs. destruct qs2; [congruence| discriminate].
Qed.

Lemma qhdrs_length : forall L chs ks, length ks = length chs -> length (qhdrs L chs ks) = length chs.
Proof.
  induction chs as [|ch chs IH]; intros [|k ks] LEN; cbn in *; try lia.
  rewrite length_app, IH by lia. cbn. lia.
Qed.
Lemma qhdrs_cons : forall L ch chs k ks, qhdrs L (ch :: chs) (k :: ks) = qhdrs L chs ks ++ [qhdr L ch k].
Proof. reflexivity. Qed.

Lemma qentries_app : forall bs1 qs1 bs2 qs2, length qs1 = length bs1 ->
  qentries (bs1 ++ bs2) (qs1 ++ qs2) = qentries bs1 qs1 ++ qentries bs2 qs2.
Proof.
  induction bs1 as [|b bs1 IH]; intros [|q qs1] bs2 qs2 LEN; cbn in *; try lia; [reflexivity|].
  rewrite IH by lia. rewrite app_assoc. reflexivity.
Qed.

Lemma abatches_to_length : forall L m bs qs nxt, abatches_to L m bs qs nxt -> length qs = length bs.
Proof.
  induction bs as [|b bs IH]; intros [|q qs] nxt AB; cbn in *; try tauto.
  destruct AB as [_ AB]. rewrite (IH qs nxt AB). reflexivity.
Qed.
Lemma abatches_length : forall L m bs qs, abatches L m bs qs -> length qs = length bs.
Proof. intros. eapply abatches_to_length. exact H. Qed.

(* [comment removed for export] *)
Lemma abatches_to_app : forall L m bs1 qs1 bs2 qs2 nxt, length qs1 = length bs1 ->
  abatches_to L m (bs1 ++ bs2) (qs1 ++ qs2) nxt <-> abatches_to L m bs1 qs1 (hd nxt (qaddrs L qs2)) /\ abatches_to L m bs2 qs2 nxt.
Proof.
  induction bs1 as [|b bs1 IH]; intros [|q qs1] bs2 qs2 nxt LEN; cbn in *; try lia; [tauto|].
  rewrite IH by lia. rewrite qaddrs_app.
  assert (E : hd nxt (qaddrs L qs1 ++ qaddrs L qs2) = hd (hd nxt (qaddrs L qs2)) (qaddrs L qs1)).
  { destruct qs1; cbn; reflexivity. }
  rewrite E. tauto.
Qed.
Lemma abatches_to_last : forall L m b q nxt, abatches_to L m [b] [q] nxt <-> abatch_cells L m b q nxt.
Proof. intros. cbn. tauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma disjoint_from_Forall : forall W A n,
  Forall (fun iv => snd iv <= A \/ A + n <= fst iv) W -> disjoint_from W A n.
Proof. induction W as [|[lo hi] W IH]; intros A n HF; cbn; [exact I|]. inversion HF; subst. cbn in *. split; [lia| apply IH; assumption]. Qed.

Section Frames.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.

Lemma abatch_cells_frame : forall b q nx,
  abatch_cells L m b q nx -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES -> abatch_cells L m' b q nx.
Proof.
  intros b q nx (H1 & H2 & H3 & H4 & H5 & H6) D. unfold abatch_cells. cbv zeta. unfold Q_BATCH_BYTES, Q_BATCH in *.
  split; [| split; [| split; [| split; [exact H4| split; [exact H5| exact H6]]]]].
  - eapply cells_frame; [exact H1 | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D| lia| lia| lia].
  - eapply u64arr_frame; [exact H2 | exact MU | exact WM |]. rewrite length_map, qhdrs_length by exact H5. rewrite <- H4.
    eapply disjoint_from_sub; [exact D| lia| lia| lia].
  - eapply junk_frame; [exact H3 | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D| lia| lia| lia].
Qed.

Lemma abatches_to_frame : forall bs qs nxt,
  abatches_to L m bs qs nxt -> (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> abatches_to L m' bs qs nxt.
Proof.
  induction bs as [|b bs IH]; intros [|q qs] nxt AB D; cbn in *; try tauto.
  destruct AB as [AC AB]. split.
  - eapply abatch_cells_frame; [exact AC| apply D; left; reflexivity].
  - apply IH; [exact AB|]. intros q' Hq'. apply D. right. exact Hq'.
Qed.
Lemma abatches_frame : forall bs qs,
  abatches L m bs qs -> (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> abatches L m' bs qs.
Proof. intros. eapply abatches_to_frame; eassumption. Qed.

Lemma aqcache_frame : forall C bs qs bytes,
  aqcache L m C bs qs bytes -> disjoint_from W C 32 ->
  (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> aqcache L m' C bs qs bytes.
Proof.
  intros C bs qs bytes [QC AB] D DB. split.
  - eapply cells_frame; [exact QC | exact MU | exact WM | exact D].
  - eapply abatches_frame; [exact AB | exact DB].
Qed.

Lemma aintal_frame : forall ia,
  aintal ia m -> disjoint_from W AIA_FLAG 4 -> disjoint_from W AIA_BASE AIA_SIZE -> aintal ia m'.
Proof.
  intros ia (F & S & Z0) DF DB. unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in *. split; [| split].
  - eapply cells_frame; [exact F | exact MU | exact WM | exact DF].
  - eapply stk_transport_disjoint; [exact S | exact MU | exact WM |]. exact DB.
  - intros Hia j Hj. eapply bytes_at_agree; [exact (Z0 Hia j Hj)|].
    intros i Hi. apply MU. rewrite length_le8 in Hi. unfold AIA_MAP1, AIA_MAP1_LEN in *. cbn in Hj.
    rewrite wa_unsigned by lia.
    eapply disjoint_outside; [exact DB| lia].
Qed.

Lemma aquar_glob_const_frame :
  aquar_glob_const m -> disjoint_from W AQ_MAX 24 -> disjoint_from W AQ_MUTEX 4 -> aquar_glob_const m'.
Proof.
  intros [A B] D1 D2. split.
  - eapply cells_frame; [exact A | exact MU | exact WM | exact D1].
  - eapply cells_frame; [exact B | exact MU | exact WM | exact D2].
Qed.
End Frames.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qcoupled_bslot_busy : forall L st X Q q,
  qcoupled L st X Q -> In q (q_loc Q ++ q_glob Q) ->
  exists b, In b (x_busy X) /\ xb_st b = BBatch /\ xb_class b = K_BATCH_CLASS /\ xb_slot b = qb_slot q.
Proof.
  intros L st X Q q (_ & _ & _ & _ & _ & BS & _) Hin. apply (proj1 (BS (qb_slot q))). apply in_map. exact Hin.
Qed.

Theorem AQUAR_frame_at : forall L st st' X X' Q m m' W,
  AQUAR_at L st X Q m -> munch W m m' -> wmono bsegs m m' -> quar_untouched L X W -> quar_same st st' X X' ->
  AQUAR_at L st' X' Q m'.
Proof.
  intros L st st' X X' Q m m' W (GC & TC & GL & IA & CP & NUM) MU WM UT (E1 & E2 & E3 & E4 & E5 & FW & BW).
  unfold AQUAR_at. rewrite E1, E2, E3, E4.
  (* [comment removed for export] *)
  assert (DT : disjoint_from W (aq_tcache L) 32).
  { apply disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (A & _). unfold aq_tcache. cbn in A |- *. lia. }
  assert (DG : disjoint_from W AQ_MAX 24 /\ disjoint_from W AQ_MUTEX 4 /\ disjoint_from W AQ_GCACHE 32).
  { unfold AQ_MAX, AQ_MUTEX, AQ_GCACHE, AINSTANCE in *.
    repeat split; apply disjoint_from_Forall; eapply Forall_impl; try exact UT; intros iv (_ & A & _); unfold AINSTANCE in A; cbn in A |- *; lia. }
  destruct DG as (DG1 & DG2 & DG3).
  assert (DI1 : disjoint_from W AIA_FLAG 4 /\ disjoint_from W AIA_BASE AIA_SIZE).
  { unfold AIA_FLAG, AIA_BASE, AIA_SIZE in *.
    split; apply disjoint_from_Forall; eapply Forall_impl; try exact UT; intros iv (_ & _ & A & B & _); cbn in A, B |- *; lia. }
  destruct DI1 as [DF DB].
  assert (DQ : forall q, In q (q_loc Q ++ q_glob Q) -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES).
  { intros q Hq. destruct (qcoupled_bslot_busy L st X Q q CP Hq) as (b & Hb & Sb & Cb & Kb).
    apply disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (_ & _ & _ & _ & A).
    specialize (A b Hb). rewrite Sb in A. unfold xb_alloc in A. rewrite Cb, Kb, size_of_class_24 in A.
    unfold abatch_addr, Q_BATCH_BYTES. cbn. exact A. }
  split; [| split; [| split; [| split; [| split]]]].
  - eapply aquar_glob_const_frame; eassumption.
  - eapply aqcache_frame; [exact MU | exact WM | exact TC | exact DT |]. intros q Hq. apply DQ. apply in_app_iff. left. exact Hq.
  - eapply aqcache_frame; [exact MU | exact WM | exact GL | exact DG3 |]. intros q Hq. apply DQ. apply in_app_iff. right. exact Hq.
  - eapply aintal_frame; eassumption.
  - (* [comment removed for export] *)
    destruct CP as (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN).
    unfold qcoupled. cbv zeta. rewrite E1, E3.
    split; [exact LN1|]. split; [exact LN2|]. split.
    { eapply Forall_impl; [| exact OK]. intros [ch k] HOK. unfold qentry_ok in *. cbn [fst snd] in *.
      destruct ch as [c n | mb ms n]; [| exact I]. destruct HOK as (b1 & ctx & Hin). exists b1, ctx.
      specialize (FW _ Hin). cbn in FW. exact FW. }
    split; [exact ND1|]. split; [exact ND2|]. split.
    { intros k. rewrite (BS k). split; intros (b & Hb & Sb & R); exists b; (split; [| split; [exact Sb| exact R]]).
      - specialize (FW b Hb). rewrite Sb in FW. exact FW.
      - specialize (BW b Hb). rewrite Sb in BW. exact BW. }
    split; [| exact NN].
    intros c k. rewrite (PS c k). split; intros (b & Hb & Sb & R); exists b; (split; [| split; [exact Sb| exact R]]).
    + specialize (FW b Hb). rewrite Sb in FW. exact FW.
    + specialize (BW b Hb). rewrite Sb in BW. exact BW.
  - unfold qnum in *. rewrite E1, E2, E3, E4. exact NUM.
Qed.
Theorem AQUAR_frame : forall L st st' X X' m m' W,
  AQUAR L st X m -> munch W m m' -> wmono bsegs m m' -> quar_untouched L X W -> quar_same st st' X X' ->
  AQUAR L st' X' m'.
Proof. intros L st st' X X' m m' W [Q AQ] MU WM UT QS. exists Q. exact (AQUAR_frame_at L st st' X X' Q m m' W AQ MU WM UT QS). Qed.

(* [comment removed for export] *)
Lemma AQUAR_init : forall L st X m,
  a_qloc st = [] -> a_qloc_bytes st = 0 -> a_qglob st = [] -> a_qglob_bytes st = 0 ->
  aquar_glob_const m ->
  rw_cells bsegs m (aq_tcache L) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m AQ_GCACHE [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  aintal false m ->
  (forall b, In b (x_busy X) -> exists p, xb_st b = BLive p) ->
  AQUAR L st X m.
Proof.
  intros L st X m Q1 Q2 Q3 Q4 GC TC GL IA LIVE. exists qconc0. unfold AQUAR_at. rewrite Q1, Q2, Q3, Q4. cbn [q_loc q_glob q_ia q_pend qconc0].
  split; [exact GC|]. split; [split; [exact TC| exact I]|]. split; [split; [exact GL| exact I]|]. split; [exact IA|]. split.
  - unfold qcoupled. cbn. rewrite Q1, Q3. cbn. repeat split; try constructor; try (intros; tauto).
    + intros [b (Hb & Sb & _)]. destruct (LIVE b Hb) as [p E]. congruence.
    + intros [b (Hb & Sb & _)]. destruct (LIVE b Hb) as [p E]. congruence.
  - unfold qnum. rewrite Q1, Q2, Q3, Q4. cbn. unfold Q_CACHE, Q_MAX. repeat split; try lia. constructor.
Qed.
End CANSEC1.
