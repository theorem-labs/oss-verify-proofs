(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode Tac InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase ABytes AKit AModelFacts ARep ALayout AHeapP ARepKit ARepFrame
     AQConst ARepQ ARepQP ADepot_iface ADepot F_adepot AFrameD ARepFrameD ASecRecycle_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Section FramesD.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.

Lemma abatch_cells_frameD : forall b q nx,
  abatch_cells L m b q nx -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES -> abatch_cells L m' b q nx.
Proof.
  intros b q nx (H1 & H2 & H3 & H4 & H5 & H6) D. unfold abatch_cells. cbv zeta. unfold Q_BATCH_BYTES, Q_BATCH in *.
  split; [| split; [| split; [| split; [exact H4| split; [exact H5| exact H6]]]]].
  - eapply cells_frameD; [exact H1 | exact MU |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D| lia| lia| lia].
  - eapply u64arr_frameD; [exact H2 | exact MU |]. rewrite length_map, qhdrs_length by exact H5. rewrite <- H4.
    eapply disjoint_from_sub; [exact D| lia| lia| lia].
  - eapply junk_frameD; [exact H3 | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D| lia| lia| lia].
Qed.

Lemma abatches_to_frameD : forall bs qs nxt,
  abatches_to L m bs qs nxt -> (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> abatches_to L m' bs qs nxt.
Proof.
  induction bs as [|b bs IH]; intros [|q qs] nxt AB D; cbn in *; try tauto.
  destruct AB as [AC AB]. split.
  - eapply abatch_cells_frameD; [exact AC| apply D; left; reflexivity].
  - apply IH; [exact AB|]. intros q' Hq'. apply D. right. exact Hq'.
Qed.
Lemma abatches_frameD : forall bs qs,
  abatches L m bs qs -> (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> abatches L m' bs qs.
Proof. intros. eapply abatches_to_frameD; eassumption. Qed.

Lemma aqcache_frameD : forall C bs qs bytes,
  aqcache L m C bs qs bytes -> disjoint_from W C 32 ->
  (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> aqcache L m' C bs qs bytes.
Proof.
  intros C bs qs bytes [QC AB] D DB. split.
  - eapply cells_frameD; [exact QC | exact MU | exact D].
  - eapply abatches_frameD; [exact AB | exact DB].
Qed.

Lemma aintal_frameD : forall ia,
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

Lemma aquar_glob_const_frameD :
  aquar_glob_const m -> disjoint_from W AQ_MAX 24 -> disjoint_from W AQ_MUTEX 4 -> aquar_glob_const m'.
Proof.
  intros [A B] D1 D2. split.
  - eapply cells_frameD; [exact A | exact MU | exact D1].
  - eapply cells_frameD; [exact B | exact MU | exact D2].
Qed.
End FramesD.

Theorem AQUAR_frame_atD : forall L st st' X X' Q m m' W,
  AQUAR_at L st X Q m -> munch W m m' -> quar_untouched L X W -> quar_same st st' X X' ->
  AQUAR_at L st' X' Q m'.
Proof.
  intros L st st' X X' Q m m' W (GC & TC & GL & IA & CP & NUM) MU UT (E1 & E2 & E3 & E4 & E5 & FW & BW).
  unfold AQUAR_at. rewrite E1, E2, E3, E4.

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
  - eapply aquar_glob_const_frameD; eassumption.
  - eapply aqcache_frameD; [exact MU | exact TC | exact DT |]. intros q Hq. apply DQ. apply in_app_iff. left. exact Hq.
  - eapply aqcache_frameD; [exact MU | exact GL | exact DG3 |]. intros q Hq. apply DQ. apply in_app_iff. right. exact Hq.
  - eapply aintal_frameD; eassumption.
  -
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
Theorem AQUAR_frameD : forall L st st' X X' m m' W,
  AQUAR L st X m -> munch W m m' -> quar_untouched L X W -> quar_same st st' X X' ->
  AQUAR L st' X' m'.
Proof. intros L st st' X X' m m' W [Q AQ] MU UT QS. exists Q. exact (AQUAR_frame_atD L st st' X X' Q m m' W AQ MU UT QS). Qed.

Lemma rw_cells_agreeD : forall m m' A cs,
  rw_cells asegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> m' (wa x) = m (wa x)) -> rw_cells asegs m' A cs.
Proof.
  intros m m' A cs [[WF B] (W0 & W1 & W)] E. pose proof (cells_bytes_length cs WF) as L.
  split; [split; [exact WF|]|].
  - eapply bytes_at_agree; [exact B|]. rewrite L. exact E.
  - split; [lia|]. split; [lia|]. intros i Hi. rewrite (wview_agree asegs m m' _ (E (A + i) ltac:(lia))). apply W. exact Hi.
Qed.
Lemma stk_agreeD : forall m m' lo hi,
  stk asegs m lo hi -> (forall x, lo <= x < hi -> m' (wa x) = m (wa x)) -> stk asegs m' lo hi.
Proof.
  intros m m' lo hi (H0 & H1 & H) E. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as [Hw (b & Hb)]. rewrite (wview_agree asegs m m' _ (E a Ha)). split; [exact Hw|].
  exists b. unfold mrd in *. rewrite E by lia. exact Hb.
Qed.

Lemma adepot_frameD : forall L m m' W,
  ADEPOTi L m -> munch W m m' ->
  Forall (fun iv => forall a, fst iv <= a < snd iv ->
            ~ (0x1ab988 <= a < 0x5fb9d0) /\ ~ (al_nodes L <= a < al_nodes L + 1048576) /\ ~ (al_store L <= a < al_store L + 8388608)) W ->
  ADEPOTi L m'.
Proof.
  intros L m m' W (D & WF & DC & LY) MU FA.
  exists D. split; [exact WF|]. split; [| exact LY].
  pose proof LY as (_ & _ & LN0 & LN1 & LS0 & LS1 & _). unfold AIMG_HI in *.
  pose proof WF as (N1 & LK & HD & ND & CMP & TF0 & TFB & NB).
  pose proof (CNT_nonneg (al_U L) (dhs D) (Z.to_nat (dN D))) as CN.
  assert (OUT : forall x, (0x1ab988 <= x < 0x5fb9d0 \/ al_nodes L <= x < al_nodes L + 1048576 \/ al_store L <= x < al_store L + 8388608) ->
                         m' (wa x) = m (wa x)).
  { intros x Hx. apply (munch_point W m m' x MU); [lia|].
    clear - FA Hx. induction FA as [| [lo hi] W Hiv FA IH]; cbn; [exact I|]. split; [| exact IH].
    intros Hin. destruct (Hiv x Hin) as (A & B & C). cbn in *. lia. }
  destruct DC as (C1 & C2 & C3 & C4 & C5 & CT & CN' & SK1 & SK2).
  unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in *.
  split; [eapply rw_cells_agreeD; [exact C1| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia]|].
  split; [eapply rw_cells_agreeD; [exact C2| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia]|].
  split; [eapply rw_cells_agreeD; [exact C3| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia]|].
  split; [eapply rw_cells_agreeD; [exact C4| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia]|].
  split; [eapply rw_cells_agreeD; [exact C5| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia]|].
  split. { intros b Hb. eapply rw_cells_agreeD; [exact (CT b Hb)| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia]. }
  split. { intros i Hi. eapply rw_cells_agreeD; [exact (CN' i Hi)| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia]. }
  split. { eapply stk_agreeD; [exact SK1| intros x Hx; apply OUT; lia]. }
  eapply stk_agreeD; [exact SK2| intros x Hx; apply OUT; lia].
Qed.

Theorem srec_holes_std : srec_holes_ok AQUAR (ADEPOT adepot_iface).
Proof.
  constructor.
  - exact AQUAR_frameD.
  - cbn [ADEPOT adepot_iface]. exact adepot_frameD.
Qed.
End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB ABytes.TwinB AKit.TwinB AModelFacts.TwinB ARep.TwinB ALayout.TwinB AHeapP.TwinB ARepKit.TwinB ARepFrame.TwinB AQConst.TwinB ARepQ.TwinB ARepQP.TwinB ADepot_iface.TwinB ADepot.TwinB F_adepot.TwinB AFrameD.TwinB ARepFrameD.TwinB ASecRecycle_iface.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Section FramesD.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.

Lemma abatch_cells_frameD : forall b q nx,
  abatch_cells L m b q nx -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES -> abatch_cells L m' b q nx.
Proof.
  intros b q nx (H1 & H2 & H3 & H4 & H5 & H6) D. unfold abatch_cells. cbv zeta. unfold Q_BATCH_BYTES, Q_BATCH in *.
  split; [| split; [| split; [| split; [exact H4| split; [exact H5| exact H6]]]]].
  - eapply cells_frameD; [exact H1 | exact MU |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D| lia| lia| lia].
  - eapply u64arr_frameD; [exact H2 | exact MU |]. rewrite length_map, qhdrs_length by exact H5. rewrite <- H4.
    eapply disjoint_from_sub; [exact D| lia| lia| lia].
  - eapply junk_frameD; [exact H3 | exact MU |]. intros Hp. eapply disjoint_from_sub; [exact D| lia| lia| lia].
Qed.

Lemma abatches_to_frameD : forall bs qs nxt,
  abatches_to L m bs qs nxt -> (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> abatches_to L m' bs qs nxt.
Proof.
  induction bs as [|b bs IH]; intros [|q qs] nxt AB D; cbn in *; try tauto.
  destruct AB as [AC AB]. split.
  - eapply abatch_cells_frameD; [exact AC| apply D; left; reflexivity].
  - apply IH; [exact AB|]. intros q' Hq'. apply D. right. exact Hq'.
Qed.
Lemma abatches_frameD : forall bs qs,
  abatches L m bs qs -> (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> abatches L m' bs qs.
Proof. intros. eapply abatches_to_frameD; eassumption. Qed.

Lemma aqcache_frameD : forall C bs qs bytes,
  aqcache L m C bs qs bytes -> disjoint_from W C 32 ->
  (forall q, In q qs -> disjoint_from W (abatch_addr L (qb_slot q)) Q_BATCH_BYTES) -> aqcache L m' C bs qs bytes.
Proof.
  intros C bs qs bytes [QC AB] D DB. split.
  - eapply cells_frameD; [exact QC | exact MU | exact D].
  - eapply abatches_frameD; [exact AB | exact DB].
Qed.

Lemma aintal_frameD : forall ia,
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

Lemma aquar_glob_const_frameD :
  aquar_glob_const m -> disjoint_from W AQ_MAX 24 -> disjoint_from W AQ_MUTEX 4 -> aquar_glob_const m'.
Proof.
  intros [A B] D1 D2. split.
  - eapply cells_frameD; [exact A | exact MU | exact D1].
  - eapply cells_frameD; [exact B | exact MU | exact D2].
Qed.
End FramesD.

Theorem AQUAR_frame_atD : forall L st st' X X' Q m m' W,
  AQUAR_at L st X Q m -> munch W m m' -> quar_untouched L X W -> quar_same st st' X X' ->
  AQUAR_at L st' X' Q m'.
Proof.
  intros L st st' X X' Q m m' W (GC & TC & GL & IA & CP & NUM) MU UT (E1 & E2 & E3 & E4 & E5 & FW & BW).
  unfold AQUAR_at. rewrite E1, E2, E3, E4.

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
  - eapply aquar_glob_const_frameD; eassumption.
  - eapply aqcache_frameD; [exact MU | exact TC | exact DT |]. intros q Hq. apply DQ. apply in_app_iff. left. exact Hq.
  - eapply aqcache_frameD; [exact MU | exact GL | exact DG3 |]. intros q Hq. apply DQ. apply in_app_iff. right. exact Hq.
  - eapply aintal_frameD; eassumption.
  -
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
Theorem AQUAR_frameD : forall L st st' X X' m m' W,
  AQUAR L st X m -> munch W m m' -> quar_untouched L X W -> quar_same st st' X X' ->
  AQUAR L st' X' m'.
Proof. intros L st st' X X' m m' W [Q AQ] MU UT QS. exists Q. exact (AQUAR_frame_atD L st st' X X' Q m m' W AQ MU UT QS). Qed.

Lemma rw_cells_agreeD : forall m m' A cs,
  rw_cells bsegs m A cs -> (forall x, A <= x < A + Z.of_nat (cells_size cs) -> m' (wa x) = m (wa x)) -> rw_cells bsegs m' A cs.
Proof.
  intros m m' A cs [[WF B] (W0 & W1 & W)] E. pose proof (cells_bytes_length cs WF) as L.
  split; [split; [exact WF|]|].
  - eapply bytes_at_agree; [exact B|]. rewrite L. exact E.
  - split; [lia|]. split; [lia|]. intros i Hi. rewrite (wview_agree bsegs m m' _ (E (A + i) ltac:(lia))). apply W. exact Hi.
Qed.
Lemma stk_agreeD : forall m m' lo hi,
  stk bsegs m lo hi -> (forall x, lo <= x < hi -> m' (wa x) = m (wa x)) -> stk bsegs m' lo hi.
Proof.
  intros m m' lo hi (H0 & H1 & H) E. split; [lia|]. split; [lia|]. intros a Ha.
  destruct (H a Ha) as [Hw (b & Hb)]. rewrite (wview_agree bsegs m m' _ (E a Ha)). split; [exact Hw|].
  exists b. unfold mrd in *. rewrite E by lia. exact Hb.
Qed.

Lemma adepot_frameD : forall L m m' W,
  ADEPOTi L m -> munch W m m' ->
  Forall (fun iv => forall a, fst iv <= a < snd iv ->
            ~ (0x1adb48 <= a < 0x5fdb90) /\ ~ (al_nodes L <= a < al_nodes L + 1048576) /\ ~ (al_store L <= a < al_store L + 8388608)) W ->
  ADEPOTi L m'.
Proof.
  intros L m m' W (D & WF & DC & LY) MU FA.
  exists D. split; [exact WF|]. split; [| exact LY].
  pose proof LY as (_ & _ & LN0 & LN1 & LS0 & LS1 & _). unfold AIMG_HI in *.
  pose proof WF as (N1 & LK & HD & ND & CMP & TF0 & TFB & NB).
  pose proof (CNT_nonneg (al_U L) (dhs D) (Z.to_nat (dN D))) as CN.
  assert (OUT : forall x, (0x1adb48 <= x < 0x5fdb90 \/ al_nodes L <= x < al_nodes L + 1048576 \/ al_store L <= x < al_store L + 8388608) ->
                         m' (wa x) = m (wa x)).
  { intros x Hx. apply (munch_point W m m' x MU); [lia|].
    clear - FA Hx. induction FA as [| [lo hi] W Hiv FA IH]; cbn; [exact I|]. split; [| exact IH].
    intros Hin. destruct (Hiv x Hin) as (A & B & C). cbn in *. lia. }
  destruct DC as (C1 & C2 & C3 & C4 & C5 & CT & CN' & SK1 & SK2).
  unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in *.
  split; [eapply rw_cells_agreeD; [exact C1| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia]|].
  split; [eapply rw_cells_agreeD; [exact C2| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia]|].
  split; [eapply rw_cells_agreeD; [exact C3| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia]|].
  split; [eapply rw_cells_agreeD; [exact C4| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia]|].
  split; [eapply rw_cells_agreeD; [exact C5| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia]|].
  split. { intros b Hb. eapply rw_cells_agreeD; [exact (CT b Hb)| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia]. }
  split. { intros i Hi. eapply rw_cells_agreeD; [exact (CN' i Hi)| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia]. }
  split. { eapply stk_agreeD; [exact SK1| intros x Hx; apply OUT; lia]. }
  eapply stk_agreeD; [exact SK2| intros x Hx; apply OUT; lia].
Qed.

Theorem srec_holes_std : srec_holes_ok AQUAR (ADEPOT adepot_iface).
Proof.
  constructor.
  - exact AQUAR_frameD.
  - cbn [ADEPOT adepot_iface]. exact adepot_frameD.
Qed.
End CANSEC1.
End TwinB.
