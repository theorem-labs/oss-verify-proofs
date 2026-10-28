(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode Tac InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase ABytes AKit AModelFacts ARep ALayout AHeapP ARepKit ARepFrame
     AQConst ARepQ ARepQP ADepot_iface ADepot F_adepot AFrameD ARepFrameD ASecRecycle_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AHolesD () := "C5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ<abatch_cellsK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6b_sizeC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7b_countK47Corelib4Init9Datatypes4list01C5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addI45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl8b_chunksC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ5qb_ksC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ5qhdrsC47Corelib5Lists7ListDef3mapC5ARocqVerifyHarness?AgentSubmission3Lib3Arr6u64arrC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission5BothW4ARep7junk_atC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00K47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2eq00C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegI47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega6VarMap1t01C5ARocqVerifyHarness?AgentSubmission5BothW9ARepFrameAdisjoint_from_subC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromC5ARocqVerifyHarness?AgentSubmission5BothW7AFrameD<cells_frameDK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr05K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C47Corelib4Init5Logic6eq_indC5ARocqVerifyHarness?AgentSubmission5BothW6ARepQP<qhdrs_lengthC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes6lengthC46Stdlib5Lists4List:length_mapC5ARocqVerifyHarness?AgentSubmission5BothW7AFrameD=u64arr_frameDC56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega=RingMicromega7Formula01C5ARocqVerifyHarness?AgentSubmission5BothW7AFrameD;junk_frameDK47Corelib4Init5Logic3and01C5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ7qb_slotC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ;abatch_addrK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00I5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6achunk00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums1Z01C5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7Q_BATCHC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl=Q_BATCH_BYTESC46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op201I5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl6abatch00I5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ7qbatchc00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsK47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205C5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ;abatches_toC47Corelib4Init5Logic9False_indC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ6qaddrsC46Stdlib5Lists4List2hdK47Corelib4Init5Logic2or01c5ARocqVerifyHarness?AgentSubmission5BothW7AHolesDCabatch_cells_frameDK47Corelib4Init5Logic2or02C47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List2InK47Corelib4Init5Logic4True01I47Corelib4Init5Logic5False00C5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ8abatchesc5ARocqVerifyHarness?AgentSubmission5BothW7AHolesDBabatches_to_frameDC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ7aqcacheC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ6qfirstC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ5qlastc5ARocqVerifyHarness?AgentSubmission5BothW7AHolesD?abatches_frameDC5ARocqVerifyHarness?AgentSubmission5BothW5ARepQ@aquar_glob_constK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04C5ARocqVerifyHarness?AgentSubmission5BothW7AQConst6AQ_MAXC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl5Q_MAXC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl5Q_MINC5ARocqVerifyHarness?AgentSubmission4Spec8AsanCtrl7Q_CACHEC5ARocqVerifyHarness?AgentSubmission5BothW7AQConst8AQ_MUTEXI47Corelib4Init9Datatypes6option00C5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Logic3notC5ARocqVerifyHarness?AgentSubmission3Lib5CellsBcells_bytes_lengthC5ARocqVerifyHarness?AgentSubmission5BothW6ADepot>bytes_at_agreeK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission5BothW7AFrameD;wview_agreeC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2ex00C5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romK47Corelib4Init5Logic2ex01C5ARocqVerifyHarness?AgentSubmission3Lib3Mem3mrdC5ARocqVerifyHarness?AgentSubmission5BothW6ADepot7ADEPOTiC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4al_UC5ARocqVerifyHarness?AgentSubmission5BothW6ADepot3dwfC5ARocqVerifyHarness?AgentSubmission5BothW6ADepot6dcellsC5ARocqVerifyHarness?AgentSubmission5BothW6ADepot7dlayoutC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission5BothW5ABase8al_nodesC5ARocqVerifyHarness?AgentSubmission5BothW5ABase8al_storeI47Corelib5Lists7ListDef6Forall00C56Stdlib6ZArith6BinInt1Z6moduloC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC5ARocqVerifyHarness?AgentSubmission5BothW6ADepot2dNC5ARocqVerifyHarness?AgentSubmission5BothW6ADepot3dlkC5ARocqVerifyHarness?AgentSubmission5BothW6ADepot5lk_okC5ARocqVerifyHarness?AgentSubmission5BothW6ADepot3dhdC5ARocqVerifyHarness?AgentSubmission5BothW6ADepot3dhsC5ARocqVerifyHarness?AgentSubmission5BothW6ADepot4dsidC5ARocqVerifyHarness?AgentSubmission5BothW6ADepot3dtfC56Stdlib6ZArith6BinInt1Z6to_natC5ARocqVerifyHarness?AgentSubmission5BothW6ADepot3BUDC5ARocqVerifyHarness?AgentSubmission5BothW6ADepot:CNT_nonnegC5ARocqVerifyHarness?AgentSubmission5BothW6ADepot3CNTI47Corelib4Init5Logic2or00C5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC5ARocqVerifyHarness?AgentSubmission3Lib5Frame7outsideK47Corelib4Init9Datatypes4prod01C47Corelib5Lists7ListDef:Forall_indC5ARocqVerifyHarness?AgentSubmission5BothW6ADepot;munch_pointC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses9and_morphc5ARocqVerifyHarness?AgentSubmission5BothW7AHolesD?rw_cells_agreeDK46Stdlib9micromega=RingMicromega5Psatz07c5ARocqVerifyHarness?AgentSubmission5BothW7AHolesD:stk_agreeDC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC5ARocqVerifyHarness?AgentSubmission5BothW6ADepot3bktC5ARocqVerifyHarness?AgentSubmission5BothW6ADepot5chainK46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula07K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell02C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega5Psatz05C5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission5BothW6ADepot4SSTFC5ARocqVerifyHarness?AgentSubmission5BothW6ADepot5SSPTRC5ARocqVerifyHarness?AgentSubmission5BothW6ADepot4SSSTC5ARocqVerifyHarness?AgentSubmission5BothW6ADepot5NUNIQC5ARocqVerifyHarness?AgentSubmission5BothW6ADepot4MAP1I5ARocqVerifyHarness?AgentSubmission5BothW5ABase7alayout00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3ivlI5ARocqVerifyHarness?AgentSubmission5BothW6ADepot6dstate00I47Corelib4Init5Logic4True00C5ARocqVerifyHarness?AgentSubmission5BothW6ADepot3TABC46Stdlib9micromega8ZifyInst7Inj_Z_Z".
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
            ~ (0x18c1c8 <= a < 0x5dc210) /\ ~ (al_nodes L <= a < al_nodes L + 1048576) /\ ~ (al_store L <= a < al_store L + 8388608)) W ->
  ADEPOTi L m'.
Proof.
  intros L m m' W (D & WF & DC & LY) MU FA.
  exists D. split; [exact WF|]. split; [| exact LY].
  pose proof LY as (_ & _ & LN0 & LN1 & LS0 & LS1 & _). unfold AIMG_HI in *.
  pose proof WF as (N1 & LK & HD & ND & CMP & TF0 & TFB & NB).
  pose proof (CNT_nonneg (al_U L) (dhs D) (Z.to_nat (dN D))) as CN.
  assert (OUT : forall x, (0x18c1c8 <= x < 0x5dc210 \/ al_nodes L <= x < al_nodes L + 1048576 \/ al_store L <= x < al_store L + 8388608) ->
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
