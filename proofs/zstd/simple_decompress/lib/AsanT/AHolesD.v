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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode Tac InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ABytes AKit AModelFacts ARep ALayout AHeapP ARepKit ARepFrame
     AQConst ARepQ ARepQP ADepot_iface ADepot F_adepot AFrameD ARepFrameD ASecRecycle_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
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

(* [comment removed for export] *)

Lemma aquar_glob_const_frameD :
  aquar_glob_const m -> disjoint_from W AQ_MAX 24 -> disjoint_from W AQ_MUTEX 4 -> aquar_glob_const m'.
Proof.
  intros [A B] D1 D2. split.
  - eapply cells_frameD; [exact A | exact MU | exact D1].
  - eapply cells_frameD; [exact B | exact MU | exact D2].
Qed.
End FramesD.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
            ~ (0x1a1bc8 <= a < 0x5f1c10) /\ ~ (al_nodes L <= a < al_nodes L + 1048576) /\ ~ (al_store L <= a < al_store L + 8388608)) W ->
  ADEPOTi L m'.
Proof.
  intros L m m' W (D & WF & DC & LY) MU FA.
  exists D. split; [exact WF|]. split; [| exact LY].
  pose proof LY as (_ & _ & LN0 & LN1 & LS0 & LS1 & _). unfold AIMG_HI in *.
  pose proof WF as (N1 & LK & HD & ND & CMP & TF0 & TFB & NB).
  pose proof (CNT_nonneg (al_U L) (dhs D) (Z.to_nat (dN D))) as CN.
  assert (OUT : forall x, (0x1a1bc8 <= x < 0x5f1c10 \/ al_nodes L <= x < al_nodes L + 1048576 \/ al_store L <= x < al_store L + 8388608) ->
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
