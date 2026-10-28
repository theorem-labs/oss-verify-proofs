(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase AQConst AKit ARep ARepQ ARepQP ARepQR ARepFrame ARepKit AHeapP AFrameD AFreeRep ARecRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition qnumR (st : astate) : Prop :=
     a_qloc_bytes st = batches_bytes (a_qloc st) /\ a_qglob_bytes st = batches_bytes (a_qglob st)
  /\ Forall (fun b => Q_BATCH_BYTES <= b_size b) (a_qloc st ++ a_qglob st).

Lemma qnumR_of_qnum : forall st, qnum st -> qnumR st.
Proof. intros st (A & B & C & _). exact (conj A (conj B C)). Qed.

Definition AQdr (R : qrconc) (mc mr : Z) (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop :=
     aquar_consts m /\ aquar_mutex m mc mr
  /\ aqcache L m (aq_tcache L) (a_qloc st) (qr_loc R) (a_qloc_bytes st)
  /\ aqcache L m AQ_GCACHE (a_qglob st) (qr_glob R) (a_qglob_bytes st)
  /\ abatches L m (map fst (qr_tmp R)) (map snd (qr_tmp R))
  /\ aintal (qr_ia R) m
  /\ qcoupled_rec L st X R
  /\ qnumR st /\ qnum_tmp (map fst (qr_tmp R)).

(* [comment removed for export] *)
Lemma qcoupled_rec_bslot_busy : forall L st X R kk,
  qcoupled_rec L st X R -> In kk (qr_bslots R) ->
  exists b, In b (x_busy X) /\ xb_st b = BBatch /\ xb_class b = K_BATCH_CLASS /\ xb_slot b = kk.
Proof. intros L st X R kk (_ & _ & _ & _ & _ & BS & _) Hin. apply (proj1 (BS kk)). exact Hin. Qed.

Lemma In_qr_bslots : forall R q,
  In q (qr_loc R ++ qr_glob R ++ map snd (qr_tmp R)) -> In (qb_slot q) (qr_bslots R).
Proof. intros R q H. unfold qr_bslots. apply in_app_iff. left. apply in_map. exact H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FrameD0.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.
(* [comment removed for export] *)
Lemma qd_abatch_cells_frameD : forall b q nx,
  abatch_cells L m b q nx -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES -> abatch_cells L m' b q nx.
Proof.
  intros b q nx (H1 & H2 & H3 & H4 & H5 & H6) D. unfold abatch_cells. cbv zeta. unfold Q_BATCH_BYTES, Q_BATCH in *.
  split; [| split; [| split; [| split; [exact H4| split; [exact H5| exact H6]]]]].
  - eapply cells_frameD; [exact H1 | exact MU |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D| lia| lia| lia].
  - eapply u64arr_frameD; [exact H2 | exact MU |]. rewrite length_map, qhdrs_length by exact H5. rewrite <- H4.
    eapply disjoint_from_sub; [exact D| lia| lia| lia].
  - eapply junk_frameD; [exact H3 | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D| lia| lia| lia].
Qed.
Lemma qd_abatches_to_frameD : forall bs qs nxt,
  abatches_to L m bs qs nxt -> (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> abatches_to L m' bs qs nxt.
Proof.
  induction bs as [|b bs IH]; intros [|q qs] nxt AB D; cbn in *; try tauto.
  destruct AB as [AC AB]. split.
  - eapply qd_abatch_cells_frameD; [exact AC| apply D; left; reflexivity].
  - apply IH; [exact AB|]. intros q' Hq'. apply D. right. exact Hq'.
Qed.
Lemma qd_abatches_frameD : forall bs qs,
  abatches L m bs qs -> (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> abatches L m' bs qs.
Proof. intros. eapply qd_abatches_to_frameD; eassumption. Qed.
Lemma qd_aqcache_frameD : forall C bs qs bytes,
  aqcache L m C bs qs bytes -> disjoint_from W C 32 ->
  (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> aqcache L m' C bs qs bytes.
Proof.
  intros C bs qs bytes [QC AB] D DB. split.
  - eapply cells_frameD; [exact QC | exact MU | exact D].
  - eapply qd_abatches_frameD; [exact AB | exact DB].
Qed.
Lemma qd_aintal_frameD : forall ia,
  aintal ia m -> disjoint_from W AIA_FLAG 4 -> disjoint_from W AIA_BASE AIA_SIZE -> aintal ia m'.
Proof.
  intros ia (F & S & Z0) DF DB. unfold AIA_FLAG, AIA_BASE, AIA_SIZE, AIA_MAP1, AIA_MAP1_LEN in *. split; [| split].
  - eapply cells_frameD; [exact F | exact MU | exact DF].
  - eapply stk_transportD; [exact S | exact MU |]. exact DB.
  - intros Hia j Hj. eapply bytes_at_agree; [exact (Z0 Hia j Hj)|].
    intros i Hi. apply MU. rewrite length_le8 in Hi. unfold AIA_MAP1, AIA_MAP1_LEN in *. cbn in Hj.
    rewrite wa_unsigned by lia.
    eapply disjoint_outside; [exact DB| lia].
Qed.
End FrameD0.

Section FrameD.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem) (X : aconc).
Hypothesis MU : munch W m m'.
Hypothesis UT : quar_untouched L X W.

Lemma qut_tcache : disjoint_from W (aq_tcache L) 32.
Proof. apply disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (A & _). unfold aq_tcache. cbn in A |- *. lia. Qed.
Lemma qut_glob : disjoint_from W AQ_MAX 24 /\ disjoint_from W AQ_MUTEX 4 /\ disjoint_from W AQ_GCACHE 32.
Proof.
  unfold AQ_MAX, AQ_MUTEX, AQ_GCACHE, AINSTANCE in *.
  repeat split; apply disjoint_from_Forall; eapply Forall_impl; try exact UT; intros iv (_ & A & _); unfold AINSTANCE in A; cbn in A |- *; lia.
Qed.
Lemma qut_ia : disjoint_from W AIA_FLAG 4 /\ disjoint_from W AIA_BASE AIA_SIZE.
Proof.
  unfold AIA_FLAG, AIA_BASE, AIA_SIZE in *.
  split; apply disjoint_from_Forall; eapply Forall_impl; try exact UT; intros iv (_ & _ & A & B & _); cbn in A, B |- *; lia.
Qed.
Lemma qut_bslot : forall st R q, qcoupled_rec L st X R ->
  In q (qr_loc R ++ qr_glob R ++ map snd (qr_tmp R)) -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES.
Proof.
  intros st R q CP Hq. destruct (qcoupled_rec_bslot_busy L st X R (qb_slot q) CP (In_qr_bslots R q Hq)) as (b & Hb & Sb & Cb & Kb).
  apply disjoint_from_Forall. eapply Forall_impl; [| exact UT]. intros iv (_ & _ & _ & _ & A).
  specialize (A b Hb). rewrite Sb in A. unfold xb_alloc in A. rewrite Cb, Kb, size_of_class_24 in A.
  unfold abatch_addr, Q_BATCH_BYTES. cbn. exact A.
Qed.

Lemma aquar_consts_frameD : aquar_consts m -> aquar_consts m'.
Proof. intros A. destruct qut_glob as (D1 & _). eapply cells_frameD; [exact A | exact MU | exact D1]. Qed.
Lemma aquar_mutex_frameD : forall mc mr, aquar_mutex m mc mr -> aquar_mutex m' mc mr.
Proof. intros mc mr A. destruct qut_glob as (_ & D2 & _). eapply cells_frameD; [exact A | exact MU | exact D2]. Qed.
End FrameD.

(* [comment removed for export] *)
Lemma qcoupled_rec_same : forall L st st' X X' R,
  qcoupled_rec L st X R -> quar_same st st' X X' -> qcoupled_rec L st' X' R.
Proof.
  intros L st st' X X' R (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN) (E1 & E2 & E3 & E4 & E5 & FW & BW).
  unfold qcoupled_rec, qr_entries in *. cbv zeta. rewrite E1, E3.
  split; [exact LN1|]. split; [exact LN2|]. split.
  { eapply Forall_impl; [| exact OK]. intros [ch k] HOK. unfold qentry_ok in *. cbn [fst snd] in *.
    destruct ch as [c n | mb ms n]; [| exact I]. destruct HOK as (b1 & ctx & Hin). exists b1, ctx.
    specialize (FW _ Hin). cbn in FW. exact FW. }
  split; [exact ND1|]. split; [exact ND2|]. split.
  { intros k. rewrite (BS k). split; intros (b & Hb & Sb & R'); exists b; (split; [| split; [exact Sb| exact R']]).
    - specialize (FW b Hb). rewrite Sb in FW. exact FW.
    - specialize (BW b Hb). rewrite Sb in BW. exact BW. }
  split; [| exact NN].
  intros c k. rewrite (PS c k). split; intros (b & Hb & Sb & R'); exists b; (split; [| split; [exact Sb| exact R']]).
  + specialize (FW b Hb). rewrite Sb in FW. exact FW.
  + specialize (BW b Hb). rewrite Sb in BW. exact BW.
Qed.

(* [comment removed for export] *)
Theorem AQdr_frameD : forall R mc mr L st st' X X' m m' W,
  AQdr R mc mr L st X m -> munch W m m' -> quar_untouched L X W -> quar_same st st' X X' ->
  AQdr R mc mr L st' X' m'.
Proof.
  intros R mc mr L st st' X X' m m' W (QC & MX & TC & GL & TB & IA & CP & NUM & NT) MU UT QS.
  pose proof QS as (E1 & E2 & E3 & E4 & _).
  unfold AQdr. rewrite E1, E2, E3, E4.
  destruct (qut_glob L W X UT) as (DG1 & DG2 & DG3). destruct (qut_ia L W X UT) as [DF DB].
  split; [eapply aquar_consts_frameD; eassumption|]. split; [eapply aquar_mutex_frameD; eassumption|].
  split. { eapply qd_aqcache_frameD; [exact MU | exact TC | exact (qut_tcache L W X UT) |]. intros q Hq. eapply qut_bslot; [exact UT| exact CP|]. apply in_app_iff. left. exact Hq. }
  split. { eapply qd_aqcache_frameD; [exact MU | exact GL | exact DG3 |]. intros q Hq. eapply qut_bslot; [exact UT| exact CP|]. apply in_app_iff. right. apply in_app_iff. left. exact Hq. }
  split. { eapply qd_abatches_frameD; [exact MU | exact TB |]. intros q Hq. eapply qut_bslot; [exact UT| exact CP|]. apply in_app_iff. right. apply in_app_iff. right. exact Hq. }
  split; [eapply qd_aintal_frameD; eassumption|].
  split; [eapply qcoupled_rec_same; eassumption|].
  split; [| exact NT]. unfold qnumR in *. rewrite E1, E2, E3, E4. exact NUM.
Qed.

(* [comment removed for export] *)
Theorem AQdr_frame : forall R mc mr L st st' X X' m m' W,
  AQdr R mc mr L st X m -> munch W m m' -> wmono bsegs m m' -> quar_untouched L X W -> quar_same st st' X X' ->
  AQdr R mc mr L st' X' m'.
Proof. intros. eapply AQdr_frameD; eassumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qprim_ids_app' : forall es1 es2, qprim_ids (es1 ++ es2) = qprim_ids es1 ++ qprim_ids es2.
Proof. intros. unfold qprim_ids. rewrite flat_map_app. reflexivity. Qed.

(* [comment removed for export] *)
Lemma qcoupled_rec_perm : forall L st st' X R R',
  qcoupled_rec L st X R ->
  length (qr_loc R') = length (a_qloc st') -> length (qr_glob R') = length (a_qglob st') ->
  Permutation (qr_entries st' R') (qr_entries st R) ->
  Permutation (qr_bslots R') (qr_bslots R) ->
  qr_qpend R' = qr_qpend R ->
  qcoupled_rec L st' X R'.
Proof.
  intros L st st' X R R' (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN) L1 L2 PE PB EQP.
  unfold qcoupled_rec. cbv zeta. rewrite EQP.
  assert (PE' : Permutation (qprim_ids (qr_entries st' R') ++ qr_qpend R) (qprim_ids (qr_entries st R) ++ qr_qpend R)).
  { apply Permutation_app_tail. apply qprim_ids_perm. exact PE. }
  split; [exact L1|]. split; [exact L2|].
  split; [eapply Permutation_Forall; [apply Permutation_sym; exact PE| exact OK]|].
  split; [eapply Permutation_NoDup'; [apply Permutation_sym; exact PE'| exact ND1]|].
  split; [eapply Permutation_NoDup'; [apply Permutation_sym; exact PB| exact ND2]|].
  split.
  { intros k0. rewrite <- (BS k0). split; intros H; (eapply Permutation_in; [| exact H]); [exact PB| apply Permutation_sym; exact PB]. }
  split.
  { intros c0 k0. rewrite <- (PS c0 k0). split; intros H; (eapply Permutation_in; [| exact H]); [exact PE'| apply Permutation_sym; exact PE']. }
  eapply Permutation_Forall; [apply Permutation_sym; exact PB| exact NN].
Qed.

(* [comment removed for export] *)
Definition qr_pop (R : qrconc) (b : abatch) (q : qbatchc) (T : list (abatch * qbatchc)) : qrconc :=
  mkQR (qr_loc R) (qr_glob R) (qr_ia R) T [qb_slot q] (combine (b_chunks b) (qb_ks q)) (qr_qpend R).

Lemma qcoupled_rec_pop : forall L st X R b q T,
  qcoupled_rec L st X R -> qr_tmp R = (b, q) :: T -> qr_pendb R = [] -> qr_pend R = [] ->
  qcoupled_rec L st X (qr_pop R b q T).
Proof.
  intros L st X R b q T CP ET EB EP. pose proof CP as (LN1 & LN2 & _).
  eapply qcoupled_rec_perm; [exact CP| exact LN1| exact LN2| | | reflexivity].
  - unfold qr_entries, qr_pop. cbn [qr_loc qr_glob qr_tmp qr_pend]. rewrite ET, EP. cbn [map fst snd qentries]. rewrite app_nil_r.
    apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app_comm.
  - unfold qr_bslots, qr_pop. cbn [qr_loc qr_glob qr_tmp qr_pendb]. rewrite ET, EB. cbn [map snd qb_slot]. rewrite app_nil_r.
    rewrite !map_app. cbn [map]. rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_head.
    apply Permutation_sym. apply Permutation_cons_append.
Qed.

(* [comment removed for export] *)
Definition qr_drop (R : qrconc) (pend' : list (achunk * Z)) : qrconc :=
  mkQR (qr_loc R) (qr_glob R) (qr_ia R) (qr_tmp R) (qr_pendb R) pend' (qr_qpend R).

Lemma qcoupled_rec_drop_sec : forall L st X R mb ms n kk pend',
  qcoupled_rec L st X R -> qr_pend R = (CSec mb ms n, kk) :: pend' ->
  qcoupled_rec L st X (qr_drop R pend').
Proof.
  intros L st X R mb ms n kk pend' (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN) EP.
  unfold qcoupled_rec, qr_entries, qr_bslots, qr_drop in *. cbn [qr_loc qr_glob qr_ia qr_tmp qr_pendb qr_pend] in *.
  rewrite EP in OK, ND1, PS.
  assert (EQ : forall es, qprim_ids (es ++ (CSec mb ms n, kk) :: pend') = qprim_ids (es ++ pend')).
  { intros es. rewrite !qprim_ids_app'. cbn [qprim_ids flat_map fst app]. reflexivity. }
  rewrite !app_assoc in OK, ND1, PS |- *. rewrite EQ in ND1, PS.
  split; [exact LN1|]. split; [exact LN2|]. split.
  { apply Forall_forall. intros e He. apply (proj1 (Forall_forall _ _) OK). revert He. rewrite !in_app_iff. cbn [In]. tauto. }
  split; [exact ND1|]. split; [exact ND2|]. split; [exact BS|]. split; [exact PS| exact NN].
Qed.

(* [comment removed for export] *)
Lemma qcoupled_rec_remove_entry : forall L st st' X R R' c k n b1 ctx l1 l2 drained,
  qcoupled_rec L st X R ->
  length (qr_loc R') = length (a_qloc st') -> length (qr_glob R') = length (a_qglob st') ->
  Permutation (qr_entries st R) ((CPrim c n, k) :: qr_entries st' R') ->
  qr_bslots R' = qr_bslots R -> qr_qpend R' = qr_qpend R ->
  x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2 -> awf L st X ->
  qcoupled_rec L st' (xrec st X c k l1 l2 drained) R'.
Proof.
  intros L st st' X R R' c k n b1 ctx l1 l2 drained (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN) L1 L2 PE EB EQP XB WF.
  unfold qcoupled_rec in *. cbv zeta in *. rewrite EB, EQP.
  set (es := qr_entries st R) in *. set (es' := qr_entries st' R') in *. set (qp := qr_qpend R) in *.
  assert (OK' : Forall (qentry_ok X) ((CPrim c n, k) :: es')) by (eapply Permutation_Forall; [exact PE| exact OK]).
  assert (PP : Permutation (qprim_ids es ++ qp) ((c, k) :: qprim_ids es' ++ qp)).
  { pose proof (Permutation_app_tail qp (qprim_ids_perm _ _ PE)) as H. cbn [qprim_ids flat_map fst snd app] in H. exact H. }
  assert (ND1c : List.NoDup ((c, k) :: qprim_ids es' ++ qp)) by exact (Permutation_NoDup' _ _ PP ND1).
  apply List.NoDup_cons_iff in ND1c. destruct ND1c as [NI ND1'].
  assert (PSc : forall c0 k0, In (c0, k0) ((c, k) :: qprim_ids es' ++ qp) <-> exists b, In b (x_busy X) /\ xb_st b = BQuar /\ xb_class b = c0 /\ xb_slot b = k0).
  { intros c0 k0. rewrite <- (PS c0 k0). split; intros H; (eapply Permutation_in; [| exact H]); [apply Permutation_sym; exact PP| exact PP]. }
  assert (XIN : forall y, In y (x_busy X) <-> In y (l1 ++ l2) \/ y = bany BQuar c k n b1 ctx).
  { intros y. rewrite XB, !in_app_iff. cbn [In]. split; intros H; decompose [or] H; auto. }
  split; [exact L1|]. split; [exact L2|]. split.
  { apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) OK' e (or_intror He)) as HOK.
    unfold qentry_ok in *. destruct e as [ch kk]. cbn [fst snd] in *. destruct ch as [c' n'| mb ms n']; [| exact I].
    destruct HOK as (b1' & ctx' & Hin). exists b1', ctx'. apply In_xrec. destruct (proj1 (XIN _) Hin) as [H|E]; [exact H|]. exfalso.
    unfold bany in E. injection E as Ec Ek En Eb Ex. subst c' kk. apply NI. apply in_app_iff. left. apply (proj2 (qprim_ids_In _ c k)). exists n'. exact He. }
  split; [exact ND1'|]. split; [exact ND2|]. split.
  { intros k0. rewrite (BS k0). split; intros (b & Hb & Sb & Cb & Kb); exists b; (split; [| auto]).
    - apply In_xrec. destruct (proj1 (XIN _) Hb) as [H| ->]; [exact H| cbn in Sb; discriminate].
    - apply (proj2 (XIN _)). left. apply In_xrec in Hb. exact Hb. }
  split; [| exact NN].
  intros c0 k0. split.
  - intros H. destruct (proj1 (PSc c0 k0) (or_intror H)) as (b & Hb & Sb & Cb & Kb). exists b. split; [| auto].
    apply In_xrec. destruct (proj1 (XIN _) Hb) as [Hl| ->]; [exact Hl|]. exfalso. cbn in Cb, Kb. rewrite <- Cb, <- Kb in H. exact (NI H).
  - intros (b & Hb & Sb & Cb & Kb). apply In_xrec in Hb.
    destruct (proj2 (PSc c0 k0) (ex_intro _ b (conj (proj2 (XIN _) (or_introl Hb)) (conj Sb (conj Cb Kb))))) as [E|H]; [| exact H].
    exfalso. injection E as Ec Ek. rewrite <- Ec in Cb. rewrite <- Ek in Kb. exact (key_fresh_g L st X BQuar c k n b1 ctx l1 l2 XB WF b Hb Cb Kb).
Qed.

Lemma qcoupled_rec_drop_prim : forall L st st' X R c k n b1 ctx l1 l2 drained pend',
  qcoupled_rec L st X R -> qr_pend R = (CPrim c n, k) :: pend' ->
  x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2 -> awf L st X ->
  a_qloc st' = a_qloc st -> a_qglob st' = a_qglob st ->
  qcoupled_rec L st' (xrec st X c k l1 l2 drained) (qr_drop R pend').
Proof.
  intros L st st' X R c k n b1 ctx l1 l2 drained pend' CP EP XB WF EL EG. pose proof CP as (LN1 & LN2 & _).
  eapply qcoupled_rec_remove_entry; [exact CP| rewrite EL; exact LN1| rewrite EG; exact LN2| | reflexivity| reflexivity| exact XB| exact WF].
  unfold qr_entries, qr_drop. cbn [qr_loc qr_glob qr_tmp qr_pend]. rewrite EL, EG, EP.
  rewrite !app_assoc. apply Permutation_sym. apply Permutation_middle.
Qed.

(* [comment removed for export] *)
Lemma qcoupled_rec_remove_bslot : forall L st st' X R R' kb nb b1 ctx l1 l2 drained,
  qcoupled_rec L st X R ->
  length (qr_loc R') = length (a_qloc st') -> length (qr_glob R') = length (a_qglob st') ->
  qr_entries st' R' = qr_entries st R ->
  Permutation (qr_bslots R) (kb :: qr_bslots R') -> qr_qpend R' = qr_qpend R ->
  x_busy X = l1 ++ bany BBatch K_BATCH_CLASS kb nb b1 ctx :: l2 -> awf L st X ->
  qcoupled_rec L st' (xrec st X K_BATCH_CLASS kb l1 l2 drained) R'.
Proof.
  intros L st st' X R R' kb nb b1 ctx l1 l2 drained (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN) L1 L2 EE PB EQP XB WF.
  unfold qcoupled_rec in *. cbv zeta in *. rewrite EE, EQP.
  set (es := qr_entries st R) in *.
  pose proof (Permutation_NoDup' _ _ PB ND2) as ND2c. apply List.NoDup_cons_iff in ND2c. destruct ND2c as [NI ND2'].
  assert (BSc : forall k0, In k0 (kb :: qr_bslots R') <-> exists b, In b (x_busy X) /\ xb_st b = BBatch /\ xb_class b = K_BATCH_CLASS /\ xb_slot b = k0).
  { intros k0. rewrite <- (BS k0). split; intros H; (eapply Permutation_in; [| exact H]); [apply Permutation_sym; exact PB| exact PB]. }
  assert (XIN : forall y, In y (x_busy X) <-> In y (l1 ++ l2) \/ y = bany BBatch K_BATCH_CLASS kb nb b1 ctx).
  { intros y. rewrite XB, !in_app_iff. cbn [In]. split; intros H; decompose [or] H; auto. }
  split; [exact L1|]. split; [exact L2|]. split.
  { apply Forall_forall. intros e He. pose proof (proj1 (Forall_forall _ _) OK e He) as HOK.
    unfold qentry_ok in *. destruct e as [ch kk]. cbn [fst snd] in *. destruct ch as [c' n'| mb ms n']; [| exact I].
    destruct HOK as (b1' & ctx' & Hin). exists b1', ctx'. apply In_xrec. destruct (proj1 (XIN _) Hin) as [H|E]; [exact H| discriminate]. }
  split; [exact ND1|]. split; [exact ND2'|]. split.
  { intros k0. split.
    - intros H. destruct (proj1 (BSc k0) (or_intror H)) as (b & Hb & Sb & Cb & Kb). exists b. split; [| auto].
      apply In_xrec. destruct (proj1 (XIN _) Hb) as [Hl| ->]; [exact Hl|]. exfalso. cbn in Kb. rewrite <- Kb in H. exact (NI H).
    - intros (b & Hb & Sb & Cb & Kb). apply In_xrec in Hb.
      destruct (proj2 (BSc k0) (ex_intro _ b (conj (proj2 (XIN _) (or_introl Hb)) (conj Sb (conj Cb Kb))))) as [E|H]; [| exact H].
      exfalso. rewrite <- E in Kb. exact (key_fresh_g L st X BBatch K_BATCH_CLASS kb nb b1 ctx l1 l2 XB WF b Hb Cb Kb). }
  split.
  { intros c0 k0. rewrite (PS c0 k0). split; intros (b & Hb & Sb & Cb & Kb); exists b; (split; [| auto]).
    - apply In_xrec. destruct (proj1 (XIN _) Hb) as [H| ->]; [exact H| cbn in Sb; discriminate].
    - apply (proj2 (XIN _)). left. apply In_xrec in Hb. exact Hb. }
  exact (Forall_inv_tail (Permutation_Forall PB NN)).
Qed.

(* [comment removed for export] *)
Definition qr_unbatch (R : qrconc) : qrconc := mkQR (qr_loc R) (qr_glob R) (qr_ia R) (qr_tmp R) [] [] (qr_qpend R).

Lemma qcoupled_rec_unbatch : forall L st st' X R kb nb b1 ctx l1 l2 drained,
  qcoupled_rec L st X R -> qr_pendb R = [kb] -> qr_pend R = [] ->
  x_busy X = l1 ++ bany BBatch K_BATCH_CLASS kb nb b1 ctx :: l2 -> awf L st X ->
  a_qloc st' = a_qloc st -> a_qglob st' = a_qglob st ->
  qcoupled_rec L st' (xrec st X K_BATCH_CLASS kb l1 l2 drained) (qr_unbatch R).
Proof.
  intros L st st' X R kb nb b1 ctx l1 l2 drained CP EB EP XB WF EL EG. pose proof CP as (LN1 & LN2 & _).
  eapply qcoupled_rec_remove_bslot; [exact CP| rewrite EL; exact LN1| rewrite EG; exact LN2| | | reflexivity| exact XB| exact WF].
  - unfold qr_entries, qr_unbatch. cbn [qr_loc qr_glob qr_tmp qr_pend]. rewrite EL, EG, EP. reflexivity.
  - unfold qr_bslots, qr_unbatch. cbn [qr_loc qr_glob qr_tmp qr_pendb]. rewrite EB, app_nil_r. apply Permutation_sym. apply Permutation_cons_append.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma AQUAR_at_of_dr : forall L st X R m,
  AQdr R 0 0 L st X m -> qr_tmp R = [] -> qr_pendb R = [] -> qr_pend R = [] ->
  a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX ->
  AQUAR_at L st X (mkQConc (qr_loc R) (qr_glob R) (qr_ia R) (qr_qpend R)) m.
Proof.
  intros L st X R m (QK & MX & TC & GL & TM & IA & CP & NUM & _) E1 E2 E3 B1 B2.
  unfold AQUAR_at. cbn [q_loc q_glob q_ia q_pend].
  split; [split; [exact QK| exact MX]|]. split; [exact TC|]. split; [exact GL|]. split; [exact IA|].
  split.
  - destruct CP as (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN).
    unfold qr_entries, qr_bslots in *. rewrite E1, E2, E3 in *. cbn [map fst snd qentries] in *. rewrite !app_nil_r in *.
    unfold qcoupled. cbv zeta.
    split; [exact LN1|]. split; [exact LN2|]. split; [exact OK|]. split; [exact ND1|]. split; [exact ND2|].
    split; [exact BS|]. split; [exact PS| exact NN].
  - destruct NUM as (N1 & N2 & N3). exact (conj N1 (conj N2 (conj N3 (conj B1 B2)))).
Qed.
End CANSEC1.
