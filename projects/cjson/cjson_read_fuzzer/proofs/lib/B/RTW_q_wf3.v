(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From Stdlib Require Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_lib4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_dstateP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_wf2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_zone.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_lock.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_q_car.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_lib4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_q_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf2.RTW_q_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_zone OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_lock.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition Kst (st : rtstate) : rtstate :=
  q_set st [] [] (st_apend st) (st_qpend st) (st_qthread st ++ st_qglobal st ++ st_qtmp st) (st_qcur st).

Lemma Kst_qall : forall st, qall (Kst st) = qall st.
Proof. intros st. unfold Kst. rewrite qall_q_set, qall_eq. cbn [app]. rewrite <- !app_assoc. reflexivity. Qed.
Lemma Kst_qelems : forall st, qelems (Kst st) = qelems st.
Proof. intros st. unfold Kst. rewrite qelems_q_set, qelems_eq. reflexivity. Qed.
Lemma Kst_all_blocks : forall st, all_blocks (Kst st) = all_blocks st.
Proof. intros st. unfold Kst. rewrite all_blocks_q_set. fold (Kst st). rewrite Kst_qelems. reflexivity. Qed.
Lemma Kst_used_cptrs : forall st c, used_cptrs (Kst st) c = used_cptrs st c.
Proof.
  intros st c. unfold used_cptrs, batch_cptrs, qbatch_addrs. destruct st; cbn -[Z.add Z.mul Z.sub Z.div Z.eqb].
  rewrite <- !app_assoc. reflexivity.
Qed.
Lemma Kst_fields : forall st,
  st_qthread (Kst st) = [] /\ st_qglobal (Kst st) = [] /\ st_apend (Kst st) = st_apend st /\ st_qpend (Kst st) = st_qpend st
  /\ st_qtmp (Kst st) = st_qthread st ++ st_qglobal st ++ st_qtmp st /\ st_qcur (Kst st) = st_qcur st.
Proof. intros st. unfold Kst. apply q_set_fields. Qed.

Theorem RTWF_Kst : forall st, RTWFq st ->
  qc_bytes (st_qthread st) + qc_bytes (st_qglobal st) + qc_bytes (st_qtmp st) + qc_bytes (map fst (st_qcur st)) <= QREC_MAX ->
  RTWF (Kst st).
Proof.
  intros st WF HB. pose proof WF as (_ & _ & _ & _ & (Q1 & Q2 & Q3 & Q4 & Q5 & Q6) & _ & _).
  apply RTWF_ofq; [| rewrite (proj1 (Kst_fields st)); cbn; unfold QUAR_MAX_CACHE; lia
                  | rewrite (proj1 (proj2 (Kst_fields st))); cbn; unfold QUAR_MAX_SIZE; lia].
  unfold Kst. eapply (RTWFq_qstep st _ _ _ _ _ _ WF) with (gone := []).
  - intros c Hc. fold (Kst st). rewrite Kst_used_cptrs. apply Permutation_refl.
  - cbn [app]. fold (Kst st). rewrite Kst_all_blocks. apply Permutation_refl.
  - constructor.
  - intros b Hb. fold (Kst st) in Hb. rewrite Kst_qall in Hb. exact (Q1 b Hb).
  - intros b Hb. destruct Hb.
  - exact Q5.
  - exact Q6.
  - cbn [qc_bytes fold_right]. rewrite !qc_bytes_app. lia.
  - exact Q4.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section QXDEF.
Variable K : rtstate.          (* [comment removed for export] *)
Variable m : word -> option byte.

(* [comment removed for export] *)
Definition coreC : Prop :=
  R_link m /\ R_consts K m /\ R_rinfo K m /\ R_regions K m /\ R_cache K m
  /\ R_ptrarr K m /\ R_depot K m /\ R_fs K m /\ R_ia m /\ R_lowshadow m
  /\ (forall c' k', 0 <= c' < KNUMCLASSES -> In k' (avail_cptrs K c' ++ apend_cptrs K c') ->
        rw_cells bsegs m (SH (cptr_addr K c' k')) (zcells (sh_avail c'))).

(* [comment removed for export] *)
Definition R_alloc4 : Prop :=
  (exists j1 j2 j3, rw_cells bsegs m A_ALLOC [W8 (st_pbase K); W8 PRIM_RES_SIZE; CB 16 j1; W8 (st_spacebeg K); W4 (2^32 - 1); CB 4 j2; W8 (st_spacebeg K + KSPACESIZE); W1 0; CB 7 j3])
  /\ (exists j1 j2 j3, rw_cells bsegs m A_SECONDARY [W8 4096; W8 (st_pa K); W8 (st_pa K); W8 PTRARR_RES_SIZE; CB 16 j1; W8 (st_nreserved K); W8 (nsec K); CB 552 j2; W1 0; CB 7 j3])
  /\ (exists j, rw_cells bsegs m A_GSTATS [CB 40 j])
  /\ cells_at bsegs m A_MAXUSERSZ [W8 (2^40); W2 16; W2 2048; W1 1].

(* [comment removed for export] *)
Definition QA : Prop := exists j1 j2, rw_cells bsegs m A_QUAR [CB 64 j1; W8 QUAR_MAX_SIZE; W8 QUAR_MIN_SIZE; W8 QUAR_MAX_CACHE; CB 64 j2].
Definition QLK (a b : Z) : Prop :=
  exists (b2 b3 : byte) j4, rw_cells bsegs m (A_QUAR + 152) [C4 (wz (lkw a b (bv_unsigned b2 + 256 * bv_unsigned b3)))]
                        /\ rw_cells bsegs m (A_QUAR + 156) [CB 4 j4].
Definition QH4 (n f l byts : Z) : Prop := rw_cells bsegs m (A_QUAR + 160) [W8 n; W8 f; W8 l; W8 byts].
Definition QH (qg : list qbatch) : Prop := QH4 (zlen qg) (qc_first qg) (qc_last qg) (qc_bytes qg).
Definition QS : Prop := exists j5, rw_cells bsegs m (A_QUAR + 192) [CB 64 j5].

(* [comment removed for export] *)
Definition R_threadx : Prop :=
  vis m (st_t K) (st_t K + 4096)
  /\ (exists j1 j2 j3 j4 j5,
        rw_cells bsegs m (st_t K) [W8 (st_ctx K); W8 (ASTACK_TOP (st_sp0 K)); W8 (ASTACK_BOTTOM (st_sp0 K)); CB 16 j1;
                            W1 0; CB 7 j2; C8 j3; C8 j4; C8 j5; W8 (st_fs K)])
  /\ rw_cells bsegs m (st_t K + T_UNWINDING) [W1 0]
  /\ rw_cells bsegs m (st_ctx K + CTX_TID) [W4 0]
  /\ rw_cells bsegs m (st_ctx K + CTX_THREAD) [W8 (st_t K)]
  /\ cells_at bsegs m A_TSD_PTR [W8 A_TSD_MAIN]
  /\ cells_at bsegs m A_TSD_MAIN [W8 (st_ctx K)]
  /\ cells_at bsegs m A_DTV_PTR [W8 A_DTV]
  /\ cells_at bsegs m (A_DTV + 8 * A_TLSMOD) [W8 A_TLSBASE]
  /\ cells_at bsegs m A_FSTLS_CELL [W8 (st_fs K)]
  /\ cells_at bsegs m (ATP + A_DTLS_OFF) [W8 (tl_dtls_block (st_tls K))]
  /\ cells_at bsegs m (tl_dtls_block (st_tls K) + 16 * A_TLSMOD + 8) [W8 (tl_dtls_w (st_tls K))].
Definition TC (qt : list qbatch) : Prop :=
  rw_cells bsegs m (qcache_t K) [W8 (zlen qt); W8 (qc_first qt); W8 (qc_last qt); W8 (qc_bytes qt)].

(* [comment removed for export] *)
Definition QCUR (cur : list (qbatch * Z)) : Prop :=
  forall bd, In bd cur -> (exists nx, rw_cells bsegs m (qb_addr (fst bd)) [W8 nx; W8 (qb_size (fst bd)); W8 (qb_count (fst bd))]) /\ R_qslots m (fst bd).

(* [comment removed for export] *)
Definition QXb (a b : Z) (qt qg tmp : list qbatch) (cur : list (qbatch * Z)) (B : Z) : Prop :=
  coreC /\ R_alloc4 /\ QA /\ QLK a b /\ QH4 (zlen qg) (qc_first qg) (qc_last qg) B /\ QS /\ R_threadx /\ TC qt
  /\ R_live K m /\ R_quar K m
  /\ R_qlist m qt /\ R_qlist m qg /\ R_qlist m tmp /\ QCUR cur.
Definition QX (a b : Z) (qt qg tmp : list qbatch) (cur : list (qbatch * Z)) : Prop := QXb a b qt qg tmp cur (qc_bytes qg).
End QXDEF.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma A_QUAR_lit : A_QUAR = 681520. Proof. reflexivity. Qed.

Lemma quar_split : forall m j1 j2 j3 j4 qg,
  rw_cells bsegs m A_QUAR
      [CB 64 j1; W8 QUAR_MAX_SIZE; W8 QUAR_MIN_SIZE; W8 QUAR_MAX_CACHE; CB 64 j2; W1 0; W1 0; CB 6 j3;
       W8 (zlen qg); W8 (qc_first qg); W8 (qc_last qg); W8 (qc_bytes qg); CB 64 j4] ->
  QA m /\ QLK m 0 0 /\ QH m qg /\ QS m.
Proof.
  intros m j1 j2 j3 j4 qg H.
  apply (proj1 (rw_cells_app m A_QUAR [CB 64 j1; W8 QUAR_MAX_SIZE; W8 QUAR_MIN_SIZE; W8 QUAR_MAX_CACHE; CB 64 j2] _)) in H as [H1 H].
  apply (proj1 (rw_cells_app m _ [W1 0; W1 0; CB 6 j3] _)) in H as [H2 H].
  apply (proj1 (rw_cells_app m _ [W8 (zlen qg); W8 (qc_first qg); W8 (qc_last qg); W8 (qc_bytes qg)] _)) in H as [H3 H4].
  cbn [cells_size Cells.csize Nat.add] in H2, H3, H4.
  rewrite <- !Z.add_assoc in H3, H4. cbn [Z.add Z.of_nat Pos.of_succ_nat Pos.add Pos.succ] in H2, H3, H4.
  split; [exists j1, j2; exact H1|]. split; [| split; [exact H3| exists j4; exact H4]].
  destruct (qlock_of m _ 0 0 j3 ltac:(lia) ltac:(lia) H2) as (b2 & b3 & j5 & L1 & L2).
  exists b2, b3, j5. split; [exact L1|]. replace (A_QUAR + 156) with (A_QUAR + Z.of_nat 152 + 4) by reflexivity. exact L2.
Qed.

Lemma quar_join : forall m qg, QA m -> QLK m 0 0 -> QH m qg -> QS m ->
  exists j1 j2 j3 j4, rw_cells bsegs m A_QUAR
      [CB 64 j1; W8 QUAR_MAX_SIZE; W8 QUAR_MIN_SIZE; W8 QUAR_MAX_CACHE; CB 64 j2; W1 0; W1 0; CB 6 j3;
       W8 (zlen qg); W8 (qc_first qg); W8 (qc_last qg); W8 (qc_bytes qg); CB 64 j4].
Proof.
  intros m qg (j1 & j2 & H1) (b2 & b3 & j5 & L1 & L2) H3 (j4 & H4).
  pose proof (bv_unsigned_in_range 8 b2) as R2. pose proof (bv_unsigned_in_range 8 b3) as R3. unfold bv_modulus in R2, R3. cbn in R2, R3.
  pose proof (qlock_to m (A_QUAR + 152) _ 0 0 b2 b3 j5 ltac:(lia) ltac:(lia) (lkw_bytes 0 0 b2 b3 ltac:(lia) ltac:(lia)) L1
                ltac:(replace (A_QUAR + 152 + 4) with (A_QUAR + 156) by reflexivity; exact L2)) as H2.
  exists j1, j2, ([b2; b3] ++ j5), j4.
  apply (proj2 (rw_cells_app m A_QUAR [CB 64 j1; W8 QUAR_MAX_SIZE; W8 QUAR_MIN_SIZE; W8 QUAR_MAX_CACHE; CB 64 j2] _)). split; [exact H1|].
  apply (proj2 (rw_cells_app m _ [W1 0; W1 0; CB 6 ([b2; b3] ++ j5)] _)). split; [exact H2|].
  apply (proj2 (rw_cells_app m _ [W8 (zlen qg); W8 (qc_first qg); W8 (qc_last qg); W8 (qc_bytes qg)] _)).
  cbn [cells_size Cells.csize Nat.add]. rewrite <- !Z.add_assoc. cbn [Z.add Z.of_nat Pos.of_succ_nat Pos.add Pos.succ].
  split; [exact H3| exact H4].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma coreC_q_set : forall st qt qg ap qp tmp cur m,
  coreC (q_set st qt qg ap qp tmp cur) m <-> coreC (q_set st [] [] ap qp (qt ++ qg ++ tmp) cur) m.
Proof. intros. destruct st. split; intros H; exact H. Qed.

Theorem QX_of_RTREP : forall st m, RTREP st m ->
  QX (Kst st) m 0 0 (st_qthread st) (st_qglobal st) (st_qtmp st) (st_qcur st).
Proof.
  intros st m HR.
  destruct HR as [HL HC (A1 & A2 & A3 & (j1 & j2 & j3 & j4 & A4) & A5) HRI HRG HAV HCA HT HLV HQ (B1 & B2 & B3 & B4) HP HD HF HIA HLS].
  destruct (quar_split m j1 j2 j3 j4 _ A4) as (X1 & X2 & X3 & X4).
  pose proof HT as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13).
  unfold QX, QXb. split.
  { unfold coreC, Kst. destruct st. repeat (split; [assumption|]). exact HAV. }
  split; [unfold R_alloc4, Kst; destruct st; repeat (split; [assumption|]); assumption|].
  split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|].
  split; [unfold R_threadx, Kst; destruct st; repeat (split; [assumption|]); assumption|].
  split; [unfold TC, Kst; rewrite q_set_qcache_t; exact T3|].
  split; [unfold Kst; destruct st; exact HLV|].
  split.
  { unfold R_quar. rewrite Kst_qelems, (proj1 (proj2 (proj2 (proj2 (Kst_fields st))))). unfold Kst. destruct st. exact HQ. }
  split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. exact B4.
Qed.

Theorem RTREP_of_QX : forall K qt qg tmp cur m,
  let st := q_set K qt qg (st_apend K) (st_qpend K) tmp cur in
  QX K m 0 0 qt qg tmp cur ->
  (forall e, In e (qelems st) -> In e (qelems K)) ->
  RTREP st m.
Proof.
  intros K qt qg tmp cur m st (CO & A4 & X1 & X2 & X3 & X4 & TX & TCq & LV & [Q1 Q2] & B1 & B2 & B3 & B4) SUB.
  destruct (quar_join m qg X1 X2 X3 X4) as (j1 & j2 & j3 & j4 & AQ).
  assert (RQ : R_quar st m).
  { split.
    - intros A n Hin. pose proof (Q1 A n (SUB _ Hin)) as RB. subst st. destruct K. exact RB.
    - intros A n Hin. replace (st_qpend st) with (st_qpend K) in Hin by (subst st; destruct K; reflexivity).
      pose proof (Q2 A n Hin) as RB. subst st. destruct K. exact RB. }
  destruct CO as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11).
  destruct A4 as (A1 & A2 & A3 & A5). destruct TX as (T1 & T2 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13).
  unfold TC in TCq.
  subst st. destruct K. constructor; cbn in *; try assumption.
  - split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exists j1, j2, j3, j4; exact AQ| exact A5].
  - split; [exact T1|]. split; [exact T2|]. split; [exact TCq|]. repeat (split; [assumption|]). assumption.
  - split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. exact B4.
Qed.


End CeilWrap.
End RTW_q_car.

(* [comment removed for export] *)
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_drainw.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_lib2.
Module RTW_q_enqw.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_lib4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition AQENQ : Z := 0x363dc.

(* [comment removed for export] *)
Definition enq_frame (j0 : list byte) (vs5 vs4 vs3 vs2 vs1 vs0 vra : word) : list cell :=
  [CB 8 j0; C8 vs5; C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra].

(* [comment removed for export] *)
Lemma enq_pro_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 64 <= bv_unsigned sp ->
  evt bsegs (fun ms' => exists (j0 : list byte) (m' : word -> option byte),
      ms' = MS (mkR ra (wz (bv_unsigned sp - 64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x363fc) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp - 64)
      /\ rw_cells bsegs m' (bv_unsigned sp - 64) (enq_frame j0 s5 s4 s3 s2 s1 s0 ra))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz AQENQ) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI ST HCL LO.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold AQENQ in *. leaf_prep.
  carve_frame 64%nat ST.
  do 8 lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia.
  finish; eassumption.
Qed.

(* [comment removed for export] *)
Lemma enq_t1_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (j0 : list byte) (vs5 vs4 vs3 vs2 vs1 vs0 vra : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (c L f l B nx sz cnt mch size lo : Z) (js : list byte),
  mem_inv bsegs m ->
  a0 = wz c -> a3 = wz mch -> a4 = wz size ->
  0 < L < 2^63 -> 0 <= f < 2^64 -> 16 <= l -> l + QBATCH_SIZE <= alloc_ceiling -> 0 <= nx < 2^64 ->
  0 <= B -> 0 <= sz -> 0 <= size -> B + size < 2^63 -> sz + size < 2^63 ->
  0 <= cnt < QBATCH_CAP -> 0 <= mch < 2^64 ->
  16 <= c -> c + 32 <= alloc_ceiling ->
  (c + 32 <= l \/ l + QBATCH_SIZE <= c) ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp + 64 <= 2^64 ->
  rw_cells bsegs m (bv_unsigned sp) (enq_frame j0 vs5 vs4 vs3 vs2 vs1 vs0 vra) ->
  rw_cells bsegs m c [C8 (wz L); C8 (wz f); C8 (wz l); C8 (wz B)] ->
  rw_cells bsegs m l [C8 (wz nx); C8 (wz sz); C8 (wz cnt)] ->
  rw_cells bsegs m (l + cnt * 8 + 24) [CB 8 js] ->
  evt bsegs (fun ms' => exists (a1' a2' a5' a6' a7' : word) (m' : word -> option byte),
      ms' = MS (mkR vra (wz (bv_unsigned sp + 64)) gp tp t0 t1 t2 vs0 vs1 a0 a1' a2' a3 a4 a5' a6' a7'
                    vs2 vs3 vs4 vs5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc vra) fc None m' (seg_rom bsegs)
      /\ munch [(l + 8, l + 24); (l + cnt * 8 + 24, l + cnt * 8 + 32); (c + 24, c + 32)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp + 64)
      /\ rw_cells bsegs m' c [C8 (wz L); C8 (wz f); C8 (wz l); C8 (wz (B + size))]
      /\ rw_cells bsegs m' l [C8 (wz nx); C8 (wz (sz + size)); C8 (wz (cnt + 1))]
      /\ rw_cells bsegs m' (l + cnt * 8 + 24) [C8 (wz mch)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x363fc) fc None m (seg_rom bsegs)).
Proof.
  intros until js. intros MI -> -> -> HL Hf Hl1 Hl2 Hnx HB Hsz Hsize HBs Hss Hcnt Hmch Hc1 Hc2 DJ ST HCL LO SPH FR QC LB SL.
  pose proof (munch_refl [(l + 8, l + 24); (l + cnt * 8 + 24, l + cnt * 8 + 32); (c + 24, c + 32)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold QBATCH_SIZE, QBATCH_CAP, enq_frame in *. idtac. leaf_prep.
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) rewrite (Z.shiftl_mul_pow2 cnt 3) by lia. change (2 ^ 3) with 8.
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  do 7 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp + 64).
  finish; eassumption.
Qed.

(* [comment removed for export] *)
Lemma enq_t2p_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (cache cnt k : Z) (mx csz sv : word),
  mem_inv bsegs m ->
  a1 = wz cache -> a5 = wz cnt ->
  1 <= cnt <= 16 -> 0 <= k < 2^28 ->
  16 <= cache -> cache + 2584 <= alloc_ceiling ->   (* [comment removed for export] *)
  (cache + 2576) mod 8 = 0 ->
  rw_cells bsegs m (cache + 1920) [C4 (wz cnt); C4 mx; C8 csz] ->
  rw_cells bsegs m (cache + 4 * (cnt - 1) + 1936) [C4 (wz k)] ->
  rw_cells bsegs m (cache + 2576) [C8 sv] ->
  evt bsegs (fun ms' => exists (sv' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz (cache + 2576)) a2 a3 a4 (wz k) csz a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x36444) fc None m' (seg_rom bsegs)
      /\ munch [(cache + 1920, cache + 1924); (cache + 2576, cache + 2584)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (cache + 1920) [C4 (wz (cnt - 1)); C4 mx; C8 csz]
      /\ rw_cells bsegs m' (cache + 4 * (cnt - 1) + 1936) [C4 (wz k)]
      /\ rw_cells bsegs m' (cache + 2576) [C8 sv'])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x3641c) fc None m (seg_rom bsegs)).
Proof.
  intros until sv. intros MI -> -> Hcnt Hk Hc1 Hca AL8 PC CK SV.
  pose proof (munch_refl [(cache + 1920, cache + 1924); (cache + 2576, cache + 2584)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold AIMG_HI in *. idtac. leaf_prep.
  lstep. (* [comment removed for export] *) replace (cnt + -1) with (cnt - 1) in * by lia.
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) change 18446744073709551616 with (2^64). rewrite (shl32_shr30 (cnt - 1)) by lia.
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) rewrite (zx32_lit k) by lia.
  amo_zstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia.
  finish; eassumption.
Qed.

(* [comment removed for export] *)
Lemma enq_t2h_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (c k Sb P b L f l B mch size : Z) (jb0 jb1 jb2 jb3 : list byte) (j1 j2 j3 : list byte),
  mem_inv bsegs m ->
  a0 = wz c -> a3 = wz mch -> a4 = wz size -> a5 = wz k ->
  0 <= k < 2^28 -> 0 <= Sb -> Sb + 2^37 + 4096 <= alloc_ceiling -> b = Sb + 24 * 2^32 + 16 * k ->
  0 <= L < 2^64 -> 0 <= f < 2^64 -> 0 <= l < 2^64 -> 0 <= B < 2^64 -> 0 <= mch < 2^64 -> 0 <= size < 2^62 -> 0 <= P < 2^64 ->
  16 <= c -> c + 32 <= alloc_ceiling -> (c + 32 <= b \/ b + 32 <= c) ->
  rw_cells bsegs m A_ALLOC [W8 P; W8 PRIM_RES_SIZE; CB 16 j1; W8 Sb; W4 (2^32 - 1); CB 4 j2; W8 (Sb + KSPACESIZE); W1 0; CB 7 j3] ->
  rw_cells bsegs m b [CB 8 jb0; CB 8 jb1; CB 8 jb2; CB 8 jb3] ->
  rw_cells bsegs m c [C8 (wz L); C8 (wz f); C8 (wz l); C8 (wz B)] ->
  evt bsegs (fun ms' => exists (a6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (wz b) (wz 1) a3 (wz (size + 8192)) (wz L) a6' a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x36484) fc None m' (seg_rom bsegs)
      /\ munch [(b, b + 32)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' A_ALLOC [W8 P; W8 PRIM_RES_SIZE; CB 16 j1; W8 Sb; W4 (2^32 - 1); CB 4 j2; W8 (Sb + KSPACESIZE); W1 0; CB 7 j3]
      /\ rw_cells bsegs m' b [C8 (wz 0); C8 (wz (size + 8192)); C8 (wz 1); C8 (wz mch)]
      /\ rw_cells bsegs m' c [C8 (wz L); C8 (wz f); C8 (wz l); C8 (wz B)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x36444) fc None m (seg_rom bsegs)).
Proof.
  intros until j3. intros MI -> -> -> -> Hk HS1 HS2 Hb HL Hf Hl HB Hmch Hsize HP Hc1 Hc2 DJ AL NB QC.
  pose proof (munch_refl [(b, b + 32)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold A_ALLOC, KSPACESIZE, PRIM_RES_SIZE, AIMG_HI in *. idtac. leaf_prep.
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  match goal with |- context [Z_to_bv 64 (?x + (Sb + ?y))] =>
    replace (x + (Sb + y)) with b by (rewrite !Z.shiftl_mul_pow2 by lia; try rewrite unsigned_lit by lia; lia) end.
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia.
  finish; eassumption.
Qed.

(* [comment removed for export] *)
Lemma enq_t2e_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (j0 : list byte) (vs5 vs4 vs3 vs2 vs1 vs0 vra : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (c b f l B sz8 lo : Z),
  mem_inv bsegs m ->
  a0 = wz c -> a1 = wz b -> a2 = wz 1 -> a4 = wz sz8 -> a5 = wz 0 ->
  0 <= b < 2^64 -> 0 <= f < 2^64 -> 0 <= l < 2^64 -> 0 <= B -> 0 <= sz8 -> B + sz8 < 2^63 ->
  16 <= c -> c + 32 <= alloc_ceiling ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp + 64 <= 2^64 ->
  rw_cells bsegs m (bv_unsigned sp) (enq_frame j0 vs5 vs4 vs3 vs2 vs1 vs0 vra) ->
  rw_cells bsegs m c [C8 (wz 0); C8 (wz f); C8 (wz l); C8 (wz B)] ->
  evt bsegs (fun ms' => exists (a1' : word) (m' : word -> option byte),
      ms' = MS (mkR vra (wz (bv_unsigned sp + 64)) gp tp t0 t1 t2 vs0 vs1 a0 a1' a2 a3 a4 a5 a6 a7
                    vs2 vs3 vs4 vs5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc vra) fc None m' (seg_rom bsegs)
      /\ munch [(c, c + 32)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp + 64)
      /\ rw_cells bsegs m' c [C8 (wz 1); C8 (wz b); C8 (wz b); C8 (wz (B + sz8))])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x36484) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI -> -> -> -> -> Hb Hf Hl HB Hsz HBs Hc1 Hc2 ST HCL LO SPH FR QC.
  pose proof (munch_refl [(c, c + 32)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold enq_frame in *. idtac. leaf_prep.
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  do 7 lstep. lstep. lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp + 64).
  finish; eassumption.
Qed.

(* [comment removed for export] *)
Lemma enq_t2n_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (j0 : list byte) (vs5 vs4 vs3 vs2 vs1 vs0 vra : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (c b L f l B sz8 nx lo : Z),
  mem_inv bsegs m ->
  a0 = wz c -> a1 = wz b -> a4 = wz sz8 -> a5 = wz L ->
  0 <= b < 2^64 -> 0 < L < 2^63 -> 0 <= f < 2^64 -> 16 <= l -> l + 8 <= alloc_ceiling -> 0 <= nx < 2^64 -> 0 <= B -> 0 <= sz8 -> B + sz8 < 2^63 ->
  16 <= c -> c + 32 <= alloc_ceiling -> (c + 32 <= l \/ l + 8 <= c) ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp + 64 <= 2^64 ->
  rw_cells bsegs m (bv_unsigned sp) (enq_frame j0 vs5 vs4 vs3 vs2 vs1 vs0 vra) ->
  rw_cells bsegs m c [C8 (wz L); C8 (wz f); C8 (wz l); C8 (wz B)] ->
  rw_cells bsegs m l [C8 (wz nx)] ->
  evt bsegs (fun ms' => exists (a1' a2' : word) (m' : word -> option byte),
      ms' = MS (mkR vra (wz (bv_unsigned sp + 64)) gp tp t0 t1 t2 vs0 vs1 a0 a1' a2' a3 a4 a5 a6 a7
                    vs2 vs3 vs4 vs5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc vra) fc None m' (seg_rom bsegs)
      /\ munch [(l, l + 8); (c, c + 32)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp + 64)
      /\ rw_cells bsegs m' c [C8 (wz (L + 1)); C8 (wz f); C8 (wz b); C8 (wz (B + sz8))]
      /\ rw_cells bsegs m' l [C8 (wz b)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x36484) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI -> -> -> -> Hb HL Hf Hl1 Hl2 Hnx HB Hsz HBs Hc1 Hc2 DJ ST HCL LO SPH FR QC LN.
  pose proof (munch_refl [(l, l + 8); (c, c + 32)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  unfold enq_frame in *. idtac. leaf_prep.
  lstep; if_lia. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. (* [comment removed for export] *)
  do 7 lstep. lstep. lstep. (* [comment removed for export] *)
  try rewrite unsigned_lit in * by lia. try rewrite Z_to_bv_bv_unsigned.
  release_frame FR ST (bv_unsigned sp + 64).
  finish; eassumption.
Qed.

(* [comment removed for export] *)
Lemma enq_spin_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  mem_inv bsegs m -> a0 = wz 0 ->
  cells_at bsegs m GOT_SEALED [W8 1; W8 A_DYING] -> cells_at bsegs m A_DYING [W4 0] ->
  evt bsegs (jself bsegs)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x36530) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros MI -> GS DY.
  change (cells_at bsegs m GOT_SEALED [W8 1; W8 A_DYING]) with (ro_cells bsegs m GOT_SEALED [W8 1; W8 A_DYING]) in GS.
  change (cells_at bsegs m A_DYING [W4 0]) with (ro_cells bsegs m A_DYING [W4 0]) in DY.
  unfold GOT_SEALED, A_DYING in *. leaf_prep.
  lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) rewrite (sx32_lit 0) by lia.
  lstep; if_lia. (* [comment removed for export] *)
  apply evt_done. apply jself_MS. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Definition spin_cells (m : word -> option byte) : Prop :=
  cells_at bsegs m GOT_SEALED [W8 1; W8 A_DYING] /\ cells_at bsegs m A_DYING [W4 0].
Lemma rtrep_spin_cells : forall st m, RTREP st m -> spin_cells m.
Proof.
  intros st m HR. pose proof (rtrep_artcells st m HR) as HA. unfold ARTCELLS in HA. decompose [and ex] HA. clear HA.
  unfold spin_cells, GOT_SEALED, A_DYING. split; assumption.
Qed.


End CeilWrap.
End RTW_q_enqw.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_apz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_bandtac4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module RTW_q_rep.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RT_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_apz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_q_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf2.RTW_q_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_zone OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

(* [comment removed for export] *)
Local Ltac shlo := lazymatch goal with |- KLOWSHADOW_BEG <= SH ?x =>
  let H := fresh "H0x" in let M := fresh "M0x" in
  assert (H : 0 <= x) by (first [lia | blia | unfold QBATCH_SIZE, CEIL, KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF in *; lia]);
  pose proof (rt_SH_mono 0 x H) as M; change (SH 0) with 0x7fff8000 in M; unfold KLOWSHADOW_BEG; lia end.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nodup_map_mid : forall {X} (f : X -> Z) (q r : list X) b b0,
  List.NoDup (map f (q ++ b :: r)) -> In b0 (q ++ r) -> f b0 <> f b.
Proof.
  intros X f q r b b0 ND Hin E. rewrite map_app in ND. cbn [map] in ND.
  apply List.NoDup_remove_2 in ND.
  apply ND. rewrite <- E. rewrite in_app_iff, <- !in_map_iff || idtac.
  apply in_app_iff in Hin. apply in_or_app. destruct Hin as [Hin|Hin]; [left| right]; apply in_map; exact Hin.
Qed.

Lemma disjoint_from_forallq : forall (P : Z * Z -> Prop) W a sz,
  Forall P W -> (forall lo hi, P (lo, hi) -> a + sz <= lo \/ hi <= a) -> disjoint_from W a sz.
Proof.
  intros P W a sz HW HP. induction W as [|[lo hi] W IH]; [exact I|]. cbn. split; [apply HP; exact (Forall_inv HW)| apply IH; exact (Forall_inv_tail HW)].
Qed.

Lemma q_set_t : forall st qt qg ap qp tmp cur, st_t (q_set st qt qg ap qp tmp cur) = st_t st.
Proof. intros. destruct st. reflexivity. Qed.
Lemma q_set_ctx : forall st qt qg ap qp tmp cur, st_ctx (q_set st qt qg ap qp tmp cur) = st_ctx st.
Proof. intros. destruct st. reflexivity. Qed.
Lemma q_set_sp0 : forall st qt qg ap qp tmp cur, st_sp0 (q_set st qt qg ap qp tmp cur) = st_sp0 st.
Proof. intros. destruct st. reflexivity. Qed.
Lemma q_set_fs : forall st qt qg ap qp tmp cur, st_fs (q_set st qt qg ap qp tmp cur) = st_fs st.
Proof. intros. destruct st. reflexivity. Qed.
Lemma q_set_tls : forall st qt qg ap qp tmp cur, st_tls (q_set st qt qg ap qp tmp cur) = st_tls st.
Proof. intros. destruct st. reflexivity. Qed.

Lemma qc_last_snoc : forall l x, qc_last (l ++ [x]) = qb_addr x.
Proof. intros l x. unfold qc_last. destruct (l ++ [x]) eqn:E; [destruct l; discriminate|]. rewrite <- E, last_last. reflexivity. Qed.

Lemma qc_first_snoc_push : forall l b e, qc_first (l ++ [qb_push b e]) = qc_first (l ++ [b]).
Proof. intros l b e. destruct l; reflexivity. Qed.

Lemma qc_first_app_ne : forall l r r', l <> [] -> qc_first (l ++ r) = qc_first (l ++ r').
Proof. intros l r r' H. destruct l; [congruence| reflexivity]. Qed.

Lemma nthz_snoc_old : forall {X} (l : list X) x i d, 0 <= i < zlen l -> nthz (l ++ [x]) i d = nthz l i d.
Proof.
  intros X l x i d Hi. unfold nthz. destruct (i <? 0) eqn:E; [reflexivity|].
  apply app_nth1. unfold zlen in Hi. lia.
Qed.
Lemma nthz_snoc_new : forall {X} (l : list X) x d, nthz (l ++ [x]) (zlen l) d = x.
Proof.
  intros X l x d. unfold nthz. destruct (zlen l <? 0) eqn:E; [unfold zlen in E; apply Z.ltb_lt in E; lia|].
  unfold zlen. rewrite Nat2Z.id. rewrite nth_middle with (l' := []). reflexivity.
Qed.

Lemma split_snoc1 : forall {X} (q1 q2 q : list X) b0 x, q1 ++ b0 :: q2 = q ++ [x] ->
  (q2 = [] /\ q1 = q /\ b0 = x) \/ (exists q2', q2 = q2' ++ [x] /\ q = q1 ++ b0 :: q2').
Proof.
  intros X q1 q2 q b0 x E. induction q2 as [|y q2' _] using rev_ind.
  - left. apply app_inj_tail in E as [E1 E2]. auto.
  - right. exists q2'. replace (q1 ++ b0 :: q2' ++ [y]) with ((q1 ++ b0 :: q2') ++ [y]) in E by (rewrite <- app_assoc; reflexivity).
    apply app_inj_tail in E as [E1 ->]. auto.
Qed.
Lemma split_snoc2 : forall {X} (q1 q2 q : list X) b0 x y, q1 ++ b0 :: q2 = q ++ [x; y] ->
  (q2 = [y] /\ q1 = q /\ b0 = x) \/ (q2 = [] /\ q1 = q ++ [x] /\ b0 = y) \/ (exists q2', q2 = q2' ++ [x; y] /\ q = q1 ++ b0 :: q2').
Proof.
  intros X q1 q2 q b0 x y E. replace (q ++ [x; y]) with ((q ++ [x]) ++ [y]) in E by (rewrite <- app_assoc; reflexivity).
  destruct (split_snoc1 q1 q2 (q ++ [x]) b0 y E) as [(-> & -> & ->)|(q2' & -> & E')]; [right; left; auto|].
  destruct (split_snoc1 q1 q2' q b0 x (eq_sym E')) as [(-> & -> & ->)|(q2'' & -> & E'')]; [left; auto|].
  right. right. exists q2''. rewrite <- app_assoc. auto.
Qed.
Lemma qc_first_app_cons : forall l1 x r r', qc_first (l1 ++ x :: r) = qc_first (l1 ++ x :: r').
Proof. intros l1 x r r'. destruct l1; reflexivity. Qed.

Lemma qall_thread_split : forall st q b,
  st_qthread st = q ++ [b] -> qall st = q ++ b :: (st_qglobal st ++ st_qtmp st ++ map fst (st_qcur st)).
Proof. intros st q b HQ. unfold qall. rewrite HQ, <- app_assoc. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section BATCH.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variable b : qbatch.
Hypothesis Hb : In b (qall st).
Definition bk : Z := (qb_addr b - rbeg st 24) / 16.

Lemma H24 : 0 <= 24 < KNUMCLASSES. Proof. unfold KNUMCLASSES; lia. Qed.

Lemma bk_used : In bk (used_cptrs st 24) /\ qb_addr b = cptr_addr st 24 bk.
Proof. exact (batch_used st WF b Hb). Qed.

Lemma bk_batch : In bk (batch_cptrs st 24).
Proof. unfold batch_cptrs. rewrite Z.eqb_refl. apply in_map_iff. exists (qb_addr b). split; [reflexivity|]. unfold qbatch_addrs. apply in_map. exact Hb. Qed.

(* [comment removed for export] *)
Lemma bk_vs_block : forall A n, In (A, n) (all_blocks st) -> chunk_ne st 24 bk A n.
Proof.
  intros A n HB EP E. injection E as E1 E2.
  (nelim (prim_block_cptr st WF A n HB EP) 4%nat; intros _ IK _ _). rewrite E1, E2 in IK.
  pose proof (wc_used_nodup st 24 (wf_class_ok st WF 24 H24)) as ND. rewrite used_cptrs_split in ND.
  apply NoDup_app_remove_l in ND. eapply (nodup_app_disj _ _ bk ND IK). apply in_or_app. left. exact bk_batch.
Qed.

(* [comment removed for export] *)
Lemma bk_vs_avail : forall c' k', 0 <= c' < KNUMCLASSES -> In k' (avail_cptrs st c' ++ apend_cptrs st c') -> (c', k') <> (24, bk).
Proof.
  intros c' k' Hc' Hin E. injection E as -> ->.
  pose proof (wc_used_nodup st 24 (wf_class_ok st WF 24 H24)) as ND. rewrite used_cptrs_split in ND.
  apply in_app_iff in Hin as [Hin|Hin].
  - eapply (nodup_app_disj _ _ bk ND Hin). apply in_or_app. right. apply in_or_app. left. exact bk_batch.
  - apply NoDup_app_remove_l in ND. apply NoDup_app_remove_l in ND. eapply (nodup_app_disj _ _ bk ND bk_batch Hin).
Qed.

(* [comment removed for export] *)
Lemma bk_vs_batch : forall q r b0, qall st = q ++ b :: r -> In b0 (q ++ r) -> batch_ne st 24 bk b0.
Proof.
  intros q r b0 HQ Hin [_ E]. destruct bk_used as [_ Eb]. rewrite <- Eb in E.
  pose proof (wc_used_nodup st 24 (wf_class_ok st WF 24 H24)) as ND. rewrite used_cptrs_split in ND.
  apply NoDup_app_remove_l in ND. apply NoDup_app_remove_l in ND. apply NoDup_app_remove_r in ND.
  unfold batch_cptrs in ND. rewrite Z.eqb_refl in ND. unfold qbatch_addrs in ND. rewrite map_map, HQ in ND.
  eapply (nodup_map_mid (fun x => (qb_addr x - rbeg st 24) / 16) q r b b0 ND Hin). cbn beta. rewrite E. reflexivity.
Qed.
End BATCH.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition t1z_ok (st : rtstate) (b : qbatch) (iv : Z * Z) : Prop :=
     (qb_addr b + 8 <= fst iv /\ snd iv <= qb_addr b + 24)
  \/ (qb_addr b + 24 + 8 * qb_count b <= fst iv /\ snd iv <= qb_addr b + 32 + 8 * qb_count b)
  \/ (qcache_t st + 24 <= fst iv /\ snd iv <= qcache_t st + 32)
  \/ CEIL <= fst iv.

Section T1M.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variables (q : list qbatch) (b : qbatch) (A n : Z).
Hypothesis HQ : st_qthread st = q ++ [b].
Hypothesis HIN : In (A, n) (st_qpend st).
Hypothesis ROOM : qb_count b < QBATCH_CAP.
Let kb := bk st b.
Let st1 := st_enq_last st A n.

Lemma t1_b_in : In b (qall st).
Proof. unfold qall. rewrite HQ, !in_app_iff. left. right. left. reflexivity. Qed.

Lemma t1_st1_eq : st1 = q_set st (q ++ [qb_push b (A, n)]) (st_qglobal st) (st_apend st)
                           (remove_first ck_eqb (A, n) (st_qpend st)) (st_qtmp st) (st_qcur st).
Proof. unfold st1, st_enq_last. rewrite HQ, upd_last_snoc. reflexivity. Qed.

Lemma t1z_ucz : forall W, Forall (t1z_ok st b) W -> Forall (ucz_ok st 24 kb) W.
Proof.
  intros W HW. destruct (bk_used st WF b t1_b_in) as [_ Eb]. pose proof (proj1 (wq_batch st (wf_quar_ok st WF) b t1_b_in)) as CNT.
  pose proof (wq_cur_count0 b) as C0 || pose proof (Zle_0_nat 0) as C0.
  assert (CZ : 0 <= qb_count b) by (unfold qb_count; lia).
  eapply Forall_impl; [| exact HW]. intros [lo hi] Hz. unfold t1z_ok, ucz_ok in *. cbn [fst snd] in *.
  fold kb in Eb. rewrite <- Eb. change (csize 24) with 8192. unfold QBATCH_CAP in ROOM.
  destruct Hz as [Hz|[Hz|[Hz|Hz]]]; [left; lia| left; lia| right; right; left; lia| right; right; right; right; right; lia].
Qed.

Theorem RTREP_enq_last' : forall W m m',
  Forall (t1z_ok st b) W -> munch W m m' -> wmono bsegs m m' -> RTREP st m ->
  (bprim n = true -> rw_cells bsegs m (SH (b_lo A n)) (zcells (sh_quar n))) ->
  rw_cells bsegs m' (qcache_t st) [W8 (zlen q + 1); W8 (qc_first (q ++ [b])); W8 (qb_addr b); W8 (qc_bytes (q ++ [b]) + usz n)] ->
  rw_cells bsegs m' (qb_addr b) [W8 0; W8 (qb_size b + usz n); W8 (qb_count b + 1)] ->
  rw_cells bsegs m' (qb_addr b + 24 + 8 * qb_count b) [W8 (b_chunk_beg A)] ->
  RTREP st1 m'.
Proof.
  intros W m m' HW MU WM HR SHQ QC' LB' SL'.
  pose proof t1_b_in as Hb. destruct (bk_used st WF b Hb) as [UKb Eb]. fold kb in UKb, Eb.
  pose proof (t1z_ucz W HW) as HWU.
  pose proof H24 as Hc24. assert (Hc1 : 1 <= 24) by lia.
  pose proof (tpx_ok_of_RTWF st WF) as HX.
  (nelim (ucz_others st WF 24 kb Hc24 Hc1 UKb W HWU m m' MU WM HR) 11%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 XA).
  (* [comment removed for export] *)
  pose proof (proj1 (wq_batch st (wf_quar_ok st WF) b Hb)) as CNT. unfold QBATCH_CAP in ROOM, CNT.
  assert (CZ : 0 <= qb_count b) by (unfold qb_count; lia).
  pose proof (t_range st WF) as TR. (nelimp (batch_geom st WF b Hb) 5%nat; intros _ _ BG1 BG2 BAL).
  pose proof (region_facts st WF 24 Hc24) as RF. cbn zeta in RF. (nelim RF 10%nat; intros Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10).
  assert (DQ : disjoint_from W A_QUAR 256).
  { apply (disjoint_from_forallq (t1z_ok st b)); [exact HW|]. intros lo hi Hz. unfold t1z_ok in Hz. cbn [fst snd] in Hz.
    unfold qcache_t, T_QCACHE, A_QUAR, A_ALLOC, CEIL, KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF in *. blia. }
  assert (DSH : forall a sz, KLOWSHADOW_BEG <= a -> a + sz <= KHIGHMEM_BEG -> disjoint_from W a sz).
  { intros a sz Ha0 Ha. apply (disjoint_from_forallq (t1z_ok st b)); [exact HW|]. intros lo hi Hz. unfold t1z_ok in Hz. cbn [fst snd] in Hz.
    unfold qcache_t, T_QCACHE, CEIL, KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF in *. blia. }
  (* [comment removed for export] *)
  assert (RA : R_alloc st m').
  { (nelim (UZ_alloc4 st WF 24 kb Hc24 Hc1 UKb W HWU m m' MU WM (rr_alloc st m HR)) 4%nat; intros A1 A2 A3 A5).
    pose proof (UZ_quarcells st W m m' MU WM (rr_alloc st m HR) DQ) as A4.
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4| exact A5]. }
  (* [comment removed for export] *)
  assert (RV : R_avail st m').
  { intros c' k' Hc' Hin'. apply XA; [exact Hc'| exact Hin'| exact (bk_vs_avail st WF b Hb c' k' Hc' Hin')]. }
  (* [comment removed for export] *)
  assert (RT : R_thread st1 m').
  { rewrite t1_st1_eq. unfold R_thread. rewrite q_set_qcache_t. rewrite (proj1 (q_set_fields st _ _ _ _ _ _)).
    (nelim (UZ_thread st WF 24 kb Hc24 Hc1 UKb W HWU m m' MU WM (rr_thread st m HR) HX) 12%nat; intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12).
    rewrite !q_set_t, !q_set_ctx, !q_set_sp0, !q_set_fs, !q_set_tls.
    split; [exact T1|]. split; [exact T2|]. split.
    { rewrite zlen_app, zlen_cons, zlen_nil, qc_first_snoc_push, qc_last_snoc. cbn [qb_addr qb_push].
      rewrite qc_bytes_app, qc_bytes_cons, qc_bytes_nil, qb_size_push.
      replace (zlen q + (1 + 0)) with (zlen q + 1) by lia.
      replace (qc_bytes q + (qb_size b + Z.max n 1 + 0)) with (qc_bytes (q ++ [b]) + usz n) by (rewrite qc_bytes_app, qc_bytes_cons, qc_bytes_nil; unfold usz; lia).
      exact QC'. }
    repeat (split; [assumption|]). assumption. }
  (* [comment removed for export] *)
  assert (RL : R_live st m').
  { intros A' n' Hin'. apply (UZ_live st WF 24 kb Hc24 Hc1 UKb W HWU m m' MU WM (rr_live st m HR) A' n' Hin').
    apply (bk_vs_block st WF b Hb). unfold all_blocks. rewrite !in_app_iff. left. exact Hin'. }
  destruct (UZ_quar st WF 24 kb Hc24 Hc1 UKb W HWU m m' MU WM (rr_quar st m HR)) as [Q1 Q2].
  assert (HBA : In (A, n) (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; right; right; exact HIN).
  assert (RBQ : R_block st m' BQuar A n).
  { (nelimp (Q2 A n HIN (bk_vs_block st WF b Hb A n HBA)) 5%nat; intros HD BIG SEC V SHD).
    split; [exact HD|]. split; [exact BIG|]. split; [exact SEC|]. split; [exact V|].
    unfold R_bshadow in *. destruct (bprim n) eqn:EP; [| exact I].
    eapply (rwT W m m' MU WM); [exact (SHQ eq_refl)|]. rewrite zcells_size.
    (nelimp (block_geom st WF A n HBA) 11%nat; intros Gn GA K X Y CE L16 H16 EA Gp Gs).
    rewrite sh_quar_len by lia. apply DSH; [shlo|]. unfold sh_tot.
    assert (L8 : b_lo A n mod 8 = 0) by (apply (mod0_trans _ 8 16); [lia|lia|reflexivity|exact L16]).
    rewrite <- (rt_SH_aligned_add (b_lo A n) (asz n) L8). unfold usz in Y.
    pose proof (rt_SH_bounds (b_lo A n + asz n) ltac:(unfold b_hi, KHIGHMEM_BEG, AIMG_HI in *; blia)). unfold b_hi, KHIGHMEM_BEG, AIMG_HI in *. lia. }
  assert (RQ : R_quar st1 m').
  { rewrite t1_st1_eq. split.
    - intros A' n' Hin'. rewrite qelems_q_set in Hin'.
      assert (ALT : (A', n') = (A, n) \/ In (A', n') (qelems st)).
      { rewrite qelems_eq, HQ. rewrite !flat_map_app' in *. cbn [flat_map] in *. rewrite !app_nil_r in *.
        unfold qb_push in Hin'. cbn [qb_elems] in Hin'. rewrite !in_app_iff in *. cbn [In] in Hin'.
        assert (SYM : (A, n) = (A', n') -> (A', n') = (A, n)) by (intros E; symmetry; exact E). tauto. }
      destruct ALT as [E|Hin0].
      + injection E as -> ->. destruct st; exact RBQ.
      + pose proof (Q1 A' n' Hin0 (bk_vs_block st WF b Hb A' n' ltac:(unfold all_blocks; rewrite !in_app_iff; right; left; exact Hin0))) as RB.
        destruct st; exact RB.
    - intros A' n' Hin'. rewrite (proj1 (proj2 (proj2 (proj2 (q_set_fields st _ _ _ _ _ _))))) in Hin'.
      pose proof (remove_first_In _ _ _ _ Hin') as Hin0.
      pose proof (Q2 A' n' Hin0 (bk_vs_block st WF b Hb A' n' ltac:(unfold all_blocks; rewrite !in_app_iff; right; right; exact Hin0))) as RB.
      destruct st; exact RB. }
  (* [comment removed for export] *)
  assert (RB : R_batches st1 m').
  { rewrite t1_st1_eq. unfold R_batches.
    (nelim (q_set_fields st (q ++ [qb_push b (A, n)]) (st_qglobal st) (st_apend st) (remove_first ck_eqb (A, n) (st_qpend st)) (st_qtmp st) (st_qcur st)) 6%nat; intros F1 F2 F3 F4 F5 F6)
. rewrite F1, F2, F5, F6.
    (nelim (UZ_batches st WF 24 kb Hc24 Hc1 UKb W HWU m m' MU WM (rr_batches st m HR)) 4%nat; intros B1 B2 B3 B4).
    pose proof (qall_thread_split st q b HQ) as QS.
    assert (OLD : forall i, 0 <= i < qb_count b -> rw_cells bsegs m' (qb_addr b + 24 + 8 * i) [W8 (b_chunk_beg (fst (nthz (qb_elems b) i (0, 0))))]).
    { intros i Hi. destruct (proj1 (R_qlist_iff m (st_qthread st)) (proj1 (rr_batches st m HR)) q b [] HQ) as [_ (_ & SL & _)].
      eapply (rwT W m m' MU WM); [exact (SL i Hi)|]. cbn.
      apply (disjoint_from_forallq (t1z_ok st b)); [exact HW|]. intros lo hi Hz. unfold t1z_ok in Hz. cbn [fst snd] in Hz.
      pose proof (t_vs_prim st WF). unfold qcache_t, T_QCACHE, CEIL, KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, QBATCH_SIZE in *. nia. }
    split; [| split; [| split]].
    - apply (proj2 (R_qlist_iff m' _)). intros q1 b0 q2 E.
      destruct (split_snoc1 q1 q2 q b0 (qb_push b (A, n)) (eq_sym E)) as [(-> & -> & ->)|(q2' & -> & E')].
      + (* [comment removed for export] *)
        split.
        * cbn [qc_first]. rewrite qb_size_push, qb_count_push. cbn [qb_addr qb_push]. unfold usz in LB'. exact LB'.
        * split; [| split].
          -- cbn [qb_addr qb_push]. destruct (proj1 (R_qlist_iff m (st_qthread st)) (proj1 (rr_batches st m HR)) q b [] HQ) as [_ (V & _ & _)].
             eapply visT; [exact WM| exact V| pose proof (t_vs_prim st WF); unfold AIMG_HI, KHIGHMEM_BEG in *; lia].
          -- intros i Hi. rewrite qb_count_push in Hi. cbn [qb_addr qb_elems qb_push].
             destruct (Z.eq_dec i (qb_count b)) as [->|NE].
             ++ replace (qb_count b) with (zlen (qb_elems b)) by reflexivity. rewrite nthz_snoc_new. cbn [fst]. exact SL'.
             ++ rewrite nthz_snoc_old by (unfold qb_count, zlen in *; lia). apply OLD. lia.
          -- cbn [qb_addr qb_push]. destruct (proj1 (R_qlist_iff m (st_qthread st)) (proj1 (rr_batches st m HR)) q b [] HQ) as [_ (_ & _ & SHD)].
             eapply (rwT W m m' MU WM); [exact SHD|]. rewrite zcells_size. unfold sh_avail. change (csize 24) with 8192. unfold zrep, zlen. rewrite repeat_length, Z2Nat.id by lia.
             apply DSH; [shlo|]. rewrite <- (rt_SH_aligned_add (qb_addr b) 8192) by (apply (mod0_trans _ 8 32); [lia|lia|reflexivity|exact BAL]).
             pose proof (rt_SH_bounds (qb_addr b + 8192) ltac:(pose proof (t_vs_prim st WF); unfold QBATCH_SIZE, CEIL, KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF in *; lia)). unfold KHIGHMEM_BEG, AIMG_HI in *. lia.
      + (* [comment removed for export] *)
        rewrite (qc_first_snoc_push q2' b (A, n)).
        apply (B1 q1 b0 (q2' ++ [b])); [rewrite HQ, E', <- app_assoc; reflexivity|].
        apply (bk_vs_batch st WF b Hb q _ b0 QS). rewrite E'. rewrite !in_app_iff. cbn [In]. tauto.
    - apply (proj2 (R_qlist_iff m' _)). intros q1 b0 q2 E. apply (B2 q1 b0 q2 E).
      apply (bk_vs_batch st WF b Hb q _ b0 QS). rewrite E. rewrite !in_app_iff. cbn [In]. tauto.
    - apply (proj2 (R_qlist_iff m' _)). intros q1 b0 q2 E. apply (B3 q1 b0 q2 E).
      apply (bk_vs_batch st WF b Hb q _ b0 QS). rewrite E. rewrite !in_app_iff. cbn [In]. tauto.
    - intros bd Hbd. apply (B4 bd Hbd). apply (bk_vs_batch st WF b Hb q _ (fst bd) QS). rewrite !in_app_iff. right. right. right. apply in_map. exact Hbd. }
  rewrite t1_st1_eq in *. destruct st. constructor; assumption.
Qed.
End T1M.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition t2z_ok (st : rtstate) (ol : option qbatch) (iv : Z * Z) : Prop :=
     (match ol with Some l => qb_addr l <= fst iv /\ snd iv <= qb_addr l + 8 | None => False end)
  \/ (qcache_t st <= fst iv /\ snd iv <= qcache_t st + 32)
  \/ CEIL <= fst iv.

Section T2M.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variables (k A n : Z).
Hypothesis HK : In (24, k) (st_apend st).
Hypothesis HIN : In (A, n) (st_qpend st).
Let b := cptr_addr st 24 k.
Let nb := mkQB b [(A, n)].
Let st1 := st_enq_new st k A n.

Lemma t2_st1_eq : st1 = q_set st (st_qthread st ++ [nb]) (st_qglobal st) (remove_first ck_eqb (24, k) (st_apend st))
                           (remove_first ck_eqb (A, n) (st_qpend st)) (st_qtmp st) (st_qcur st).
Proof. reflexivity. Qed.

Lemma t2_k_used : In k (used_cptrs st 24).
Proof. unfold used_cptrs. rewrite !in_app_iff. right. right. right. right. right. exact (apend_in_cptrs st 24 k HK). Qed.

(* [comment removed for export] *)
Lemma t2_geom : rbeg st 24 <= b /\ b + 8192 <= rbeg st 24 + r_mapped (rg st 24) /\ KHIGHMEM_BEG <= rbeg st 24 /\ b mod 32 = 0
                /\ rbeg st 24 + KREGIONSIZE <= CEIL
                /\ r_mapped (rg st 24) <= KFREEARRAY_OFF /\ st_pbase st <= rbeg st 24 /\ rbeg st 24 + KREGIONSIZE <= st_pbase st + PRIM_RES_SIZE.
Proof.
  (nelimp (apend_geom st WF 24 k HK) 11%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11).
  change (csize 24) with 8192 in *. unfold b. repeat split; try lia; unfold CEIL, KREGIONSIZE, PRIM_RES_SIZE in *; lia.
Qed.

Section COMMON.
Variable W : list (Z * Z).
Variables (m m' : word -> option byte).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.
Hypothesis HR : RTREP st m.
Hypothesis SHQ : bprim n = true -> rw_cells bsegs m (SH (b_lo A n)) (zcells (sh_quar n)).
Hypothesis NB : rw_cells bsegs m b [W8 0; W8 (QBATCH_SIZE + usz n); W8 1; W8 (b_chunk_beg A)].
(* [comment removed for export] *)
Hypothesis DSH : forall a sz, KLOWSHADOW_BEG <= a -> a + sz <= KHIGHMEM_BEG -> disjoint_from W a sz.
Hypothesis DQ : disjoint_from W A_QUAR 256.
Hypothesis DB : disjoint_from W b 8192.
Variables (ck : Z).      (* [comment removed for export] *)
Hypothesis UK : In ck (used_cptrs st 24).
Hypothesis HWU : Forall (ucz_ok st 24 ck) W.
Hypothesis CKB : forall A' n', In (A', n') (all_blocks st) -> chunk_ne st 24 ck A' n'.
Hypothesis CKA : forall c' k', 0 <= c' < KNUMCLASSES -> In k' (avail_cptrs st c' ++ apend_cptrs st c') -> (c', k') <> (24, ck) \/ (c', k') = (24, k).

Lemma Hc24 : 0 <= 24 < KNUMCLASSES. Proof. unfold KNUMCLASSES; lia. Qed.

Lemma t2_alloc : R_alloc st m'.
Proof.
  (nelim (UZ_alloc4 st WF 24 ck Hc24 ltac:(lia) UK W HWU m m' MU WM (rr_alloc st m HR)) 4%nat; intros A1 A2 A3 A5).
  pose proof (UZ_quarcells st W m m' MU WM (rr_alloc st m HR) DQ) as A4.
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4| exact A5].
Qed.

(* [comment removed for export] *)
Lemma t2_avail : R_avail st1 m'.
Proof.
  rewrite t2_st1_eq. intros c' k' Hc' Hin'. rewrite q_set_cptr_addr. rewrite q_set_avail in Hin'.
  assert (Hin0 : In k' (avail_cptrs st c' ++ apend_cptrs st c')).
  { apply in_app_iff in Hin' as [H|H]; apply in_or_app; [left; exact H| right].
    unfold apend_cptrs in *. rewrite (proj1 (proj2 (proj2 (q_set_fields st _ _ _ _ _ _)))) in H.
    apply in_map_iff in H as ([c'' k''] & E & Hf). cbn [snd] in E. subst k''. apply filter_In in Hf as [Hf Hc''].
    apply in_map_iff. exists (c'', k'). split; [reflexivity|]. apply filter_In. split; [eapply remove_first_In; exact Hf| exact Hc'']. }
  assert (NK : (c', k') <> (24, k)).
  { intros E. injection E as -> ->. apply in_app_iff in Hin' as [H|H].
    - pose proof (wc_used_nodup st 24 (wf_class_ok st WF 24 Hc24)) as ND. unfold used_cptrs in ND.
      eapply (nodup_app_disj _ _ k ND H). rewrite !in_app_iff. right. right. right. right. exact (apend_in_cptrs st 24 k HK).
    - unfold apend_cptrs in H. rewrite (proj1 (proj2 (proj2 (q_set_fields st _ _ _ _ _ _)))) in H.
      apply in_map_iff in H as ([c'' k''] & E & Hf). cbn [snd] in E. subst k''. apply filter_In in Hf as [Hf Hc'']. cbn [fst] in Hc''.
      apply Z.eqb_eq in Hc''. subst c''.
      pose proof (wq_inflight st (wf_quar_ok st WF)) as [IL _].
      destruct (st_apend st) as [|x [|y l]] eqn:EA; [destruct HK| | rewrite !zlen_cons in IL; pose proof (zlen_nonneg l); lia].
      destruct HK as [E2|[]]. subst x. try rewrite EA in Hf. cbn in Hf. rewrite !Z.eqb_refl in Hf. cbn in Hf. exact Hf. }
  (nelim (ucz_others st WF 24 ck Hc24 ltac:(lia) UK W HWU m m' MU WM HR) 11%nat; intros _ _ _ _ _ _ _ _ _ _ XA).
  destruct (CKA c' k' Hc' Hin0) as [NE|E]; [exact (XA c' k' Hc' Hin0 NE)| exfalso; exact (NK E)].
Qed.

Lemma t2_live : R_live st m'.
Proof.
  intros A' n' Hin'. apply (UZ_live st WF 24 ck Hc24 ltac:(lia) UK W HWU m m' MU WM (rr_live st m HR) A' n' Hin').
  apply CKB. unfold all_blocks. rewrite !in_app_iff. left. exact Hin'.
Qed.

Lemma t2_HBA : In (A, n) (all_blocks st).
Proof. unfold all_blocks; rewrite !in_app_iff; right; right; exact HIN. Qed.

Lemma t2_block_new : R_block st m' BQuar A n.
Proof.
  destruct (UZ_quar st WF 24 ck Hc24 ltac:(lia) UK W HWU m m' MU WM (rr_quar st m HR)) as [Q1 Q2].
  (nelimp (Q2 A n HIN (CKB A n t2_HBA)) 5%nat; intros HD BIG SEC V SHD).
  split; [exact HD|]. split; [exact BIG|]. split; [exact SEC|]. split; [exact V|].
  unfold R_bshadow in *. destruct (bprim n) eqn:EP; [| exact I].
  eapply (rwT W m m' MU WM); [exact (SHQ eq_refl)|]. rewrite zcells_size.
  (nelimp (block_geom st WF A n t2_HBA) 11%nat; intros Gn GA K X Y CE L16 H16 EA Gp Gs).
  rewrite sh_quar_len by lia. apply DSH; [shlo|]. unfold sh_tot.
  assert (L8 : b_lo A n mod 8 = 0) by (apply (mod0_trans _ 8 16); [lia|lia|reflexivity|exact L16]).
  rewrite <- (rt_SH_aligned_add (b_lo A n) (asz n) L8). unfold usz in Y.
  pose proof (rt_SH_bounds (b_lo A n + asz n) ltac:(unfold b_hi, KHIGHMEM_BEG, AIMG_HI in *; blia)). unfold b_hi, KHIGHMEM_BEG, AIMG_HI in *. lia.
Qed.

Lemma t2_quar : R_quar st1 m'.
Proof.
  destruct (UZ_quar st WF 24 ck Hc24 ltac:(lia) UK W HWU m m' MU WM (rr_quar st m HR)) as [Q1 Q2].
  pose proof t2_block_new as RBQ.
  rewrite t2_st1_eq. split.
  - intros A' n' Hin'. rewrite qelems_q_set in Hin'.
    assert (ALT : (A', n') = (A, n) \/ In (A', n') (qelems st)).
    { rewrite qelems_eq. rewrite !flat_map_app' in *. cbn [flat_map nb qb_elems] in *. rewrite !app_nil_r in *.
      rewrite !in_app_iff in *. cbn [In] in Hin'.
      assert (SYM : (A, n) = (A', n') -> (A', n') = (A, n)) by (intros E; symmetry; exact E). tauto. }
    destruct ALT as [E|Hin0].
    + injection E as -> ->. destruct st; exact RBQ.
    + pose proof (Q1 A' n' Hin0 (CKB A' n' ltac:(unfold all_blocks; rewrite !in_app_iff; right; left; exact Hin0))) as RB. destruct st; exact RB.
  - intros A' n' Hin'. rewrite (proj1 (proj2 (proj2 (proj2 (q_set_fields st _ _ _ _ _ _))))) in Hin'.
    pose proof (remove_first_In _ _ _ _ Hin') as Hin0.
    pose proof (Q2 A' n' Hin0 (CKB A' n' ltac:(unfold all_blocks; rewrite !in_app_iff; right; right; exact Hin0))) as RB. destruct st; exact RB.
Qed.

(* [comment removed for export] *)
Lemma t2_QBC_new : QBC m' nb 0.
Proof.
  (nelimp t2_geom 8%nat; intros G1 G2 G3 G4 G5 G6 G7 G8).
  pose proof (region_facts st WF 24 Hc24) as RF. cbn zeta in RF. (nelim RF 10%nat; intros Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10).
  pose proof (rwT W m m' MU WM _ _ NB ltac:(cbn; eapply disjoint_from_mono; [exact DB| lia])) as NB'.
  unfold nb. split; [| split; [| split]].
  - cbn [qb_addr]. rewrite qb_size_one. unfold qb_count. cbn [qb_elems length Z.of_nat Pos.of_succ_nat].
    apply (rw_cells_take m' b [W8 0; W8 (QBATCH_SIZE + usz n); W8 1] [W8 (b_chunk_beg A)]) in NB' as H || pose proof (rw_cells_take m' b [W8 0; W8 (QBATCH_SIZE + usz n); W8 1] [W8 (b_chunk_beg A)] NB') as H.
    unfold usz in H. exact H.
  - cbn [qb_addr]. destruct (rr_regions st m HR 24 Hc24) as (V & _). cbn zeta in V.
    eapply visT; [exact WM| | unfold AIMG_HI, KHIGHMEM_BEG in *; lia].
    pose proof (proj2 (stk_split bsegs m _ b _ V ltac:(lia))) as V1. exact (proj1 (stk_split bsegs m _ (b + QBATCH_SIZE) _ V1 ltac:(unfold QBATCH_SIZE; lia))).
  - intros i Hi. unfold qb_count in Hi. cbn [qb_addr qb_elems length Z.of_nat Pos.of_succ_nat] in *.
    assert (i = 0) by lia. subst i. cbn [nthz Z.ltb Z.to_nat nth fst].
    pose proof (rw_cells_drop m' b [W8 0; W8 (QBATCH_SIZE + usz n); W8 1] [W8 (b_chunk_beg A)] NB') as H.
    cbn [cells_size csize Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H.
    replace (b + 24 + 8 * 0) with (b + 24) by lia. exact H.
  - cbn [qb_addr]. eapply (rwT W m m' MU WM); [exact (rr_avail st m HR 24 k Hc24 ltac:(apply in_or_app; right; exact (apend_in_cptrs st 24 k HK)))|].
    rewrite zcells_size. unfold sh_avail. change (csize 24) with 8192. unfold zrep, zlen. rewrite repeat_length, Z2Nat.id by lia.
    apply DSH; [shlo|]. fold b. rewrite <- (rt_SH_aligned_add b 8192) by (apply (mod0_trans _ 8 32); [lia|lia|reflexivity|exact G4]).
    pose proof (rt_SH_bounds (b + 8192) ltac:(unfold CEIL, KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF in *; lia)). unfold KHIGHMEM_BEG, AIMG_HI in *. lia.
Qed.

(* [comment removed for export] *)
Lemma t2_batches_other :
  (forall q1 b0 q2, st_qthread st = q1 ++ b0 :: q2 -> batch_ne st 24 ck b0 -> QBC m' b0 (qc_first q2))
  /\ (forall q1 b0 q2, st_qglobal st = q1 ++ b0 :: q2 -> batch_ne st 24 ck b0 -> QBC m' b0 (qc_first q2))
  /\ (forall q1 b0 q2, st_qtmp st = q1 ++ b0 :: q2 -> batch_ne st 24 ck b0 -> QBC m' b0 (qc_first q2))
  /\ (forall bd, In bd (st_qcur st) -> batch_ne st 24 ck (fst bd) ->
        (exists nx, rw_cells bsegs m' (qb_addr (fst bd)) [W8 nx; W8 (qb_size (fst bd)); W8 (qb_count (fst bd))]) /\ R_qslots m' (fst bd)).
Proof. exact (UZ_batches st WF 24 ck Hc24 ltac:(lia) UK W HWU m m' MU WM (rr_batches st m HR)). Qed.
End COMMON.

(* [comment removed for export] *)
Theorem RTREP_enq_new_e' : forall W m m',
  st_qthread st = [] ->
  Forall (t2z_ok st None) W -> munch W m m' -> wmono bsegs m m' -> RTREP st m ->
  (bprim n = true -> rw_cells bsegs m (SH (b_lo A n)) (zcells (sh_quar n))) ->
  rw_cells bsegs m b [W8 0; W8 (QBATCH_SIZE + usz n); W8 1; W8 (b_chunk_beg A)] ->
  rw_cells bsegs m' (qcache_t st) [W8 1; W8 b; W8 b; W8 (QBATCH_SIZE + usz n)] ->
  RTREP st1 m'.
Proof.
  intros W m m' HQ HW MU WM HR SHQ NB QC'.
  (nelimp t2_geom 8%nat; intros G1 G2 G3 G4 G5 G6 G7 G8). pose proof (t_range st WF) as TR. pose proof (t_vs_prim st WF) as TP.
  pose proof (tpx_ok_of_RTWF st WF) as HX. pose proof t2_k_used as UK.
  assert (HWU : Forall (ucz_ok st 24 k) W).
  { eapply Forall_impl; [| exact HW]. intros [lo hi] Hz. unfold t2z_ok, ucz_ok in *. cbn [fst snd] in *.
    destruct Hz as [Hz|[Hz|Hz]]; [destruct Hz| right; right; left; exact Hz| right; right; right; right; right; exact Hz]. }
  assert (DSH : forall a sz, KLOWSHADOW_BEG <= a -> a + sz <= KHIGHMEM_BEG -> disjoint_from W a sz).
  { intros a sz Ha0 Ha. apply (disjoint_from_forallq (t2z_ok st None)); [exact HW|]. intros lo hi Hz. unfold t2z_ok in Hz. cbn [fst snd] in Hz.
    unfold qcache_t, T_QCACHE, CEIL, KHIGHMEM_BEG, AIMG_HI in *. blia. }
  assert (DQ : disjoint_from W A_QUAR 256).
  { apply (disjoint_from_forallq (t2z_ok st None)); [exact HW|]. intros lo hi Hz. unfold t2z_ok in Hz. cbn [fst snd] in Hz.
    unfold qcache_t, T_QCACHE, A_QUAR, A_ALLOC, CEIL, KHIGHMEM_BEG, AIMG_HI in *. blia. }
  assert (DB : disjoint_from W b 8192).
  { apply (disjoint_from_forallq (t2z_ok st None)); [exact HW|]. intros lo hi Hz. unfold t2z_ok in Hz. cbn [fst snd] in Hz.
    unfold qcache_t, T_QCACHE, CEIL, KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, PRIM_RES_SIZE in *. lia. }
  assert (CKB : forall A' n', In (A', n') (all_blocks st) -> chunk_ne st 24 k A' n').
  { intros A' n' HB EP E. injection E as E1 E2.
    (nelim (prim_block_cptr st WF A' n' HB EP) 4%nat; intros _ IK _ _). rewrite E1, E2 in IK.
    pose proof (wc_used_nodup st 24 (wf_class_ok st WF 24 Hc24)) as ND. rewrite used_cptrs_split in ND.
    apply NoDup_app_remove_l in ND. eapply (nodup_app_disj _ _ k ND IK). apply in_or_app. right. exact (apend_in_cptrs st 24 k HK). }
  assert (CKA : forall c' k', 0 <= c' < KNUMCLASSES -> In k' (avail_cptrs st c' ++ apend_cptrs st c') -> (c', k') <> (24, k) \/ (c', k') = (24, k)).
  { intros c' k' _ _. destruct (Z.eq_dec c' 24) as [->|NC]; [| left; congruence]. destruct (Z.eq_dec k' k) as [->|NK]; [right; reflexivity| left; congruence]. }
  (nelim (ucz_others st WF 24 k Hc24 ltac:(lia) UK W HWU m m' MU WM HR) 11%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 XA).
  assert (RA : R_alloc st m') by (eapply t2_alloc; eassumption).
  assert (RV : R_avail st1 m') by (eapply t2_avail; eassumption).
  assert (RL : R_live st m') by (eapply t2_live; eassumption).
  assert (RQ : R_quar st1 m') by (eapply t2_quar; eassumption).
  assert (QN : QBC m' nb 0) by (eapply t2_QBC_new; eassumption).
  assert (RT : R_thread st1 m').
  { rewrite t2_st1_eq. unfold R_thread. rewrite q_set_qcache_t. rewrite (proj1 (q_set_fields st _ _ _ _ _ _)). rewrite HQ. cbn [app].
    (nelim (UZ_thread st WF 24 k Hc24 ltac:(lia) UK W HWU m m' MU WM (rr_thread st m HR) HX) 12%nat; intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12).
    rewrite !q_set_t, !q_set_ctx, !q_set_sp0, !q_set_fs, !q_set_tls.
    split; [exact T1|]. split; [exact T2|]. split.
    { rewrite zlen_cons, zlen_nil. cbn [qc_first qc_last last qb_addr nb]. unfold nb. rewrite qc_bytes_cons, qc_bytes_nil, qb_size_one.
      unfold usz in QC'. replace (1 + 0) with 1 by lia. replace (QBATCH_SIZE + Z.max n 1 + 0) with (QBATCH_SIZE + Z.max n 1) by lia. exact QC'. }
    repeat (split; [assumption|]). assumption. }
  assert (RB : R_batches st1 m').
  { rewrite t2_st1_eq. unfold R_batches.
    (nelim (q_set_fields st (st_qthread st ++ [nb]) (st_qglobal st) (remove_first ck_eqb (24, k) (st_apend st)) (remove_first ck_eqb (A, n) (st_qpend st)) (st_qtmp st) (st_qcur st)) 6%nat; intros F1 F2 F3 F4 F5 F6)
. rewrite F1, F2, F5, F6, HQ. cbn [app].
    eassert (BO : _) by (eapply (t2_batches_other W m m') with (ck := k); eassumption). (nelim BO 4%nat; intros B1 B2 B3 B4).
    assert (BN : forall b0, In b0 (qall st) -> batch_ne st 24 k b0).
    { intros b0 Hb0 [_ E]. pose proof (apend_vs_batch st WF 24 k HK b0 Hb0). change (csize 24) with 8192 in *. unfold QBATCH_SIZE, b in *. lia. }
    split; [| split; [| split]].
    - cbn [R_qlist]. destruct QN as [QL QS]. split; [exact QL|]. split; [exact QS| exact I].
    - apply (proj2 (R_qlist_iff m' _)). intros q1 b0 q2 E. apply (B2 q1 b0 q2 E). apply BN. unfold qall. rewrite E, !in_app_iff. cbn [In]. tauto.
    - apply (proj2 (R_qlist_iff m' _)). intros q1 b0 q2 E. apply (B3 q1 b0 q2 E). apply BN. unfold qall. rewrite E, !in_app_iff. cbn [In]. tauto.
    - intros bd Hbd. apply (B4 bd Hbd). apply BN. unfold qall. rewrite !in_app_iff. right. right. right. apply in_map. exact Hbd. }
  rewrite t2_st1_eq in *. destruct st. constructor; assumption.
Qed.

(* [comment removed for export] *)
Theorem RTREP_enq_new_n' : forall W m m' q l,
  st_qthread st = q ++ [l] ->
  Forall (t2z_ok st (Some l)) W -> munch W m m' -> wmono bsegs m m' -> RTREP st m ->
  (bprim n = true -> rw_cells bsegs m (SH (b_lo A n)) (zcells (sh_quar n))) ->
  rw_cells bsegs m b [W8 0; W8 (QBATCH_SIZE + usz n); W8 1; W8 (b_chunk_beg A)] ->
  rw_cells bsegs m' (qcache_t st) [W8 (zlen q + 2); W8 (qc_first (q ++ [l])); W8 b; W8 (qc_bytes (q ++ [l]) + (QBATCH_SIZE + usz n))] ->
  rw_cells bsegs m' (qb_addr l) [W8 b] ->
  RTREP st1 m'.
Proof.
  intros W m m' q l HQ HW MU WM HR SHQ NB QC' LN'.
  (nelimp t2_geom 8%nat; intros G1 G2 G3 G4 G5 G6 G7 G8). pose proof (t_range st WF) as TR. pose proof (t_vs_prim st WF) as TP.
  pose proof (tpx_ok_of_RTWF st WF) as HX.
  assert (Hl : In l (qall st)) by (unfold qall; rewrite HQ, !in_app_iff; left; right; left; reflexivity).
  destruct (bk_used st WF l Hl) as [UK El]. set (kl := bk st l) in *.
  (nelimp (batch_geom st WF l Hl) 5%nat; intros _ _ BG1 BG2 BAL).
  assert (HWU : Forall (ucz_ok st 24 kl) W).
  { eapply Forall_impl; [| exact HW]. intros [lo hi] Hz. unfold t2z_ok, ucz_ok in *. cbn [fst snd] in *. rewrite <- El. change (csize 24) with 8192.
    destruct Hz as [Hz|[Hz|Hz]]; [left; lia| right; right; left; exact Hz| right; right; right; right; right; exact Hz]. }
  assert (DSH : forall a sz, KLOWSHADOW_BEG <= a -> a + sz <= KHIGHMEM_BEG -> disjoint_from W a sz).
  { intros a sz Ha0 Ha. apply (disjoint_from_forallq (t2z_ok st (Some l))); [exact HW|]. intros lo hi Hz. unfold t2z_ok in Hz. cbn [fst snd] in Hz.
    unfold qcache_t, T_QCACHE, CEIL, KHIGHMEM_BEG, AIMG_HI in *. blia. }
  assert (DQ : disjoint_from W A_QUAR 256).
  { apply (disjoint_from_forallq (t2z_ok st (Some l))); [exact HW|]. intros lo hi Hz. unfold t2z_ok in Hz. cbn [fst snd] in Hz.
    unfold qcache_t, T_QCACHE, A_QUAR, A_ALLOC, CEIL, KHIGHMEM_BEG, AIMG_HI in *. blia. }
  pose proof (apend_vs_batch st WF 24 k HK l Hl) as LB0. change (csize 24) with 8192 in LB0. fold b in LB0.
  assert (DB : disjoint_from W b 8192).
  { apply (disjoint_from_forallq (t2z_ok st (Some l))); [exact HW|]. intros lo hi Hz. unfold t2z_ok in Hz. cbn [fst snd] in Hz.
    unfold qcache_t, T_QCACHE, CEIL, KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, QBATCH_SIZE, PRIM_RES_SIZE in *. lia. }
  pose proof (bk_vs_block st WF l Hl) as CKB. fold kl in CKB.
  assert (CKA : forall c' k', 0 <= c' < KNUMCLASSES -> In k' (avail_cptrs st c' ++ apend_cptrs st c') -> (c', k') <> (24, kl) \/ (c', k') = (24, k)).
  { intros c' k' Hc' Hin'. left. exact (bk_vs_avail st WF l Hl c' k' Hc' Hin'). }
  (nelim (ucz_others st WF 24 kl Hc24 ltac:(lia) UK W HWU m m' MU WM HR) 11%nat; intros X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 XA).
  assert (RA : R_alloc st m') by (eapply t2_alloc; eassumption).
  assert (RV : R_avail st1 m') by (eapply t2_avail; eassumption).
  assert (RL : R_live st m') by (eapply t2_live; eassumption).
  assert (RQ : R_quar st1 m') by (eapply t2_quar; eassumption).
  assert (QN : QBC m' nb 0) by (eapply t2_QBC_new; eassumption).
  assert (RT : R_thread st1 m').
  { rewrite t2_st1_eq. unfold R_thread. rewrite q_set_qcache_t. rewrite (proj1 (q_set_fields st _ _ _ _ _ _)). rewrite HQ.
    (nelim (UZ_thread st WF 24 kl Hc24 ltac:(lia) UK W HWU m m' MU WM (rr_thread st m HR) HX) 12%nat; intros T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12).
    rewrite !q_set_t, !q_set_ctx, !q_set_sp0, !q_set_fs, !q_set_tls.
    split; [exact T1|]. split; [exact T2|]. split.
    { rewrite <- app_assoc. cbn [app]. rewrite zlen_app, zlen_cons, zlen_cons, zlen_nil.
      assert (EF : qc_first (q ++ [l; nb]) = qc_first (q ++ [l])) by (destruct q; reflexivity). rewrite EF.
      replace (q ++ [l; nb]) with ((q ++ [l]) ++ [nb]) by (rewrite <- app_assoc; reflexivity).
      rewrite qc_last_snoc. unfold nb. cbn [qb_addr]. rewrite qc_bytes_app. rewrite (qc_bytes_cons _ []), qc_bytes_nil, qb_size_one.
      unfold usz in QC'. replace (zlen q + (1 + (1 + 0))) with (zlen q + 2) by lia.
      replace (qc_bytes (q ++ [l]) + (QBATCH_SIZE + Z.max n 1 + 0)) with (qc_bytes (q ++ [l]) + (QBATCH_SIZE + Z.max n 1)) by lia. exact QC'. }
    repeat (split; [assumption|]). assumption. }
  assert (RB : R_batches st1 m').
  { rewrite t2_st1_eq. unfold R_batches.
    (nelim (q_set_fields st (st_qthread st ++ [nb]) (st_qglobal st) (remove_first ck_eqb (24, k) (st_apend st)) (remove_first ck_eqb (A, n) (st_qpend st)) (st_qtmp st) (st_qcur st)) 6%nat; intros F1 F2 F3 F4 F5 F6)
. rewrite F1, F2, F5, F6, HQ, <- app_assoc. cbn [app].
    eassert (BO : _) by (eapply (t2_batches_other W m m') with (ck := kl); eassumption). (nelim BO 4%nat; intros B1 B2 B3 B4).
    pose proof (qall_thread_split st q l HQ) as QS.
    (* [comment removed for export] *)
    assert (QL : QBC m' l b).
    { destruct (proj1 (R_qlist_iff m (st_qthread st)) (proj1 (rr_batches st m HR)) q l [] HQ) as [HL (V & SL & SHD)]. cbn [qc_first] in HL.
      assert (OBJ : forall a sz, qb_addr l + 8 <= a -> a + sz <= qb_addr l + QBATCH_SIZE -> disjoint_from W a sz).
      { intros a sz Ha Hs. apply (disjoint_from_forallq (t2z_ok st (Some l))); [exact HW|]. intros lo hi Hz. unfold t2z_ok in Hz. cbn [fst snd] in Hz.
        unfold qcache_t, T_QCACHE, CEIL, KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, QBATCH_SIZE in *. lia. }
      pose proof (proj1 (wq_batch st (wf_quar_ok st WF) l Hl)) as CNT. unfold QBATCH_CAP in CNT. assert (CZ : 0 <= qb_count l) by (unfold qb_count; lia).
      split; [| split; [| split]].
      - pose proof (rw_cells_drop m (qb_addr l) [W8 0] [W8 (qb_size l); W8 (qb_count l)] HL) as HL2.
        cbn [cells_size csize Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HL2.
        apply (proj2 (rw_cells_app m' (qb_addr l) [W8 b] [W8 (qb_size l); W8 (qb_count l)])). split; [exact LN'|].
        cbn [cells_size csize Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. eapply (rwT W m m' MU WM); [exact HL2| cbn; apply OBJ; unfold QBATCH_SIZE; lia].
      - eapply visT; [exact WM| exact V| unfold AIMG_HI, KHIGHMEM_BEG in *; lia].
      - intros i Hi. eapply (rwT W m m' MU WM); [exact (SL i Hi)| cbn; apply OBJ; unfold QBATCH_SIZE; lia].
      - eapply (rwT W m m' MU WM); [exact SHD|]. rewrite zcells_size. unfold sh_avail. change (csize 24) with 8192. unfold zrep, zlen. rewrite repeat_length, Z2Nat.id by lia.
        apply DSH; [shlo|]. rewrite <- (rt_SH_aligned_add (qb_addr l) 8192) by (apply (mod0_trans _ 8 32); [lia|lia|reflexivity|exact BAL]).
        pose proof (rt_SH_bounds (qb_addr l + 8192) ltac:(unfold QBATCH_SIZE, CEIL, KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF in *; lia)). unfold KHIGHMEM_BEG, AIMG_HI in *. lia. }
    split; [| split; [| split]].
    - apply (proj2 (R_qlist_iff m' _)). intros q1 b0 q2 E.
      destruct (split_snoc2 q1 q2 q b0 l nb (eq_sym E)) as [(-> & -> & ->)|[(-> & -> & ->)|(q2' & -> & E')]].
      + cbn [qc_first qb_addr nb]. exact QL.
      + cbn [qc_first]. exact QN.
      + rewrite (qc_first_app_cons q2' l [nb] []).
        apply (B1 q1 b0 (q2' ++ [l])); [rewrite HQ, E', <- app_assoc; reflexivity|].
        apply (bk_vs_batch st WF l Hl q _ b0 QS). rewrite E'. rewrite !in_app_iff. cbn [In]. tauto.
    - apply (proj2 (R_qlist_iff m' _)). intros q1 b0 q2 E. apply (B2 q1 b0 q2 E). apply (bk_vs_batch st WF l Hl q _ b0 QS). rewrite E, !in_app_iff. cbn [In]. tauto.
    - apply (proj2 (R_qlist_iff m' _)). intros q1 b0 q2 E. apply (B3 q1 b0 q2 E). apply (bk_vs_batch st WF l Hl q _ b0 QS). rewrite E, !in_app_iff. cbn [In]. tauto.
    - intros bd Hbd. apply (B4 bd Hbd). apply (bk_vs_batch st WF l Hl q _ (fst bd) QS). rewrite !in_app_iff. right. right. right. apply in_map. exact Hbd. }
  rewrite t2_st1_eq in *. destruct st. constructor; assumption.
Qed.
End T2M.


End CeilWrap.
End RTW_q_rep.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_pop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Module RTW_q_enq2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RT_trans.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_apz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_pop OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf2.RTW_m_c1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_q_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf2.RTW_q_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_zone RTW_q_rep RTW_q_enqw OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma vis_cell : forall m lo hi a (k : nat), stk bsegs m lo hi -> lo <= a -> a + Z.of_nat k <= hi ->
  exists junk, rw_cells bsegs m a [CB k junk].
Proof.
  intros m lo hi a k V Hlo Hhi.
  destruct (stk_split bsegs m lo (a + Z.of_nat k) hi V ltac:(lia)) as [V1 _].
  (nelim (stk_carve bsegs m lo (a + Z.of_nat k) k V1 ltac:(lia)) 3%nat; intros _ junk H). exists junk.
  replace (a + Z.of_nat k - Z.of_nat k) with a in H by lia. exact H.
Qed.

(* [comment removed for export] *)
Lemma munch_cat : forall W1 W2 m m1 m2, munch W1 m m1 -> munch W2 m1 m2 -> munch (W1 ++ W2) m m2.
Proof.
  intros W1 W2 m m1 m2 H1 H2 x Hx. apply outside_app in Hx as [X1 X2]. rewrite (H2 x X2). apply H1. exact X1.
Qed.

(* [comment removed for export] *)
Lemma qb_size_lb : forall b, QBATCH_SIZE <= qb_size b.
Proof.
  intros b. unfold qb_size. assert (0 <= fold_right (fun e acc => Z.max (snd e) 1 + acc) 0 (qb_elems b)); [| lia].
  induction (qb_elems b) as [|e l IH]; cbn; lia.
Qed.
Lemma qc_bytes_lb : forall l, QBATCH_SIZE * zlen l <= qc_bytes l.
Proof.
  induction l as [|b l IH]; [cbn; unfold zlen; cbn; lia|]. rewrite qc_bytes_cons, zlen_cons. pose proof (qb_size_lb b). lia.
Qed.
Lemma qb_size_le_bytes : forall q1 b q2, qb_size b <= qc_bytes (q1 ++ b :: q2).
Proof.
  intros q1 b q2. rewrite qc_bytes_app, qc_bytes_cons. pose proof (qc_bytes_nonneg q1). pose proof (qc_bytes_nonneg q2). lia.
Qed.

(* [comment removed for export] *)
Section TPAGE.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variable SP : Z.
Hypothesis HSP : CEIL <= SP.
Lemma tpage_not_client_all : forall a, st_t st <= a < st_t st + 4096 ->
  ~ cj_client_addr (st_sp0 st) (st_lb st) (st_lf st) SP a.
Proof.
  intros a Ha HC. pose proof (t_range st WF) as [T1 T2]. unfold KHIGHMEM_BEG, AIMG_HI, CEIL in *.
  destruct HC as [H|[H|[(A & n & Hb & Hr)|[(F & k & Hb & Hr)|H]]]].
  - lia.
  - unfold aclient_image, AERRNO, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI, ATP in H. blia.
  - assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hb).
    pose proof (t_vs_block st WF A n HB) as TB.
    (nelimp (block_geom st WF A n HB) 6%nat; intros _ _ _ X Y _). unfold usz in Y. lia.
  - pose proof (t_vs_fs st WF) as TF. (nelimp (frame_range st WF F k Hb) 4%nat; intros Hk X Y _). (nelimp (fs_range st WF) 3%nat; intros F1 F2 _).
    unfold FS_FRAMES_OFF, KHIGHMEM_BEG, AIMG_HI in *.
    destruct Hr as [Hr|Hr]; [lia|].
    pose proof (rt_SH_bounds (F + fsz k) ltac:(unfold CEIL in *; blia)) as B.
    (nelimp (frame_range st WF F k Hb) 4%nat; intros _ _ _ AL). rewrite (rt_SH_aligned_add F (fsz k) AL) in B.
    pose proof (rt_SH_mono 0 F ltac:(blia)) as B0. change (SH 0) with 0x7fff8000 in B0. blia.
  - unfold astack_shadow in H. rewrite CEIL_eq, SH_CEIL in H. change (SH (2^47)) with 0x10007fff8000 in H. blia.
Qed.

(* [comment removed for export] *)
Lemma batch_not_client : forall b a, In b (qall st) -> qb_addr b <= a < qb_addr b + QBATCH_SIZE ->
  ~ cj_client_addr (st_sp0 st) (st_lb st) (st_lf st) SP a.
Proof.
  intros b a Hb Ha HC. (nelimp (batch_geom st WF b Hb) 5%nat; intros BF FF R1 R2 AL).
  pose proof (region_facts st WF 24 ltac:(unfold KNUMCLASSES; lia)) as RF. cbn zeta in RF. (nelim RF 7%nat; intros Y1 Y2 Y3 Y4 Y5 Y6 _).
  unfold KHIGHMEM_BEG, AIMG_HI, CEIL, KREGIONSIZE, KFREEARRAY_OFF, PRIM_RES_SIZE in *.
  destruct HC as [H|[H|[(A & n & Hlb & Hr)|[(F & k & Hlf & Hr)|H]]]].
  - lia.
  - unfold aclient_image, AERRNO, AGERROR0, AGERROR1, ADATA_LO, AIMG_HI, ATP in H. lia.
  - assert (HB : In (A, n) (all_blocks st)) by (unfold all_blocks; apply in_or_app; left; exact Hlb).
    pose proof (BF A n HB) as D. (nelimp (block_geom st WF A n HB) 6%nat; intros _ _ _ X Y _). unfold usz in Y. lia.
  - (nelimp (frame_range st WF F k Hlf) 4%nat; intros Hk X Y FAL). (nelimp (fs_range st WF) 3%nat; intros F1 F2 _).
    unfold framefree, FS_FRAMES_OFF, FS_TOTAL in *.
    assert (64 <= fsz k) by (destruct Hk as [-> | ->]; [change (fsz 1) with 128| change (fsz 2) with 256]; lia).
    destruct Hr as [Hr|Hr]; [lia|].
    pose proof (rt_SH_bounds (F + fsz k) ltac:(unfold CEIL, KHIGHMEM_BEG, AIMG_HI in *; blia)) as B. rewrite (rt_SH_aligned_add F (fsz k) FAL) in B. unfold KHIGHMEM_BEG, AIMG_HI in *. lia.
  - unfold astack_shadow in H. rewrite CEIL_eq, SH_CEIL in H. change (SH (2^47)) with 0x10007fff8000 in H. lia.
Qed.

(* [comment removed for export] *)
Lemma cli_pres_t1z : forall b W m m', In b (qall st) -> qb_count b < QBATCH_CAP ->
  Forall (fun iv : Z * Z => t1z_ok st b iv /\ (CEIL <= fst iv -> snd iv <= SP)) W ->
  munch W m m' -> wmono bsegs m m' -> cli_pres st SP m m'.
Proof.
  intros b W m m' Hb ROOM HW MU WM. unfold cli_pres. eapply cj_pres_of_munch; [exact MU| exact WM|].
  pose proof (proj1 (wq_batch st (wf_quar_ok st WF) b Hb)) as CNT. pose proof (t_range st WF) as TR.
  assert (CZ : 0 <= qb_count b) by (unfold qb_count; lia).
  intros a Ha HC. clear MU WM. induction W as [|[lo hi] W' IH]; [exact I|].
  pose proof (Forall_inv HW) as [A1 A2]. unfold t1z_ok in A1. cbn [fst snd] in A1, A2. cbn. split; [| apply IH; exact (Forall_inv_tail HW)].
  intros Hin. destruct A1 as [A1|[A1|[A1|A1]]].
  - apply (batch_not_client b a Hb); [unfold QBATCH_SIZE; lia| exact HC].
  - apply (batch_not_client b a Hb); [unfold QBATCH_SIZE, QBATCH_CAP in *; lia| exact HC].
  - apply (tpage_not_client_all a); [unfold qcache_t, T_QCACHE in *; lia| exact HC].
  - apply (below_sp_not_client st WF SP a); [specialize (A2 A1); lia| exact HC].
Qed.
End TPAGE.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma enq_t1_full :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (j0 : list byte) (vs5 vs4 vs3 vs2 vs1 vs0 vra : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate)
         (q : list qbatch) (b : qbatch) (A n lo : Z),
  RTREP st m -> RTWF st -> mem_inv bsegs m ->
  st_qthread st = q ++ [b] -> qb_count b <> QBATCH_CAP -> In (A, n) (st_qpend st) ->
  (bprim n = true -> rw_cells bsegs m (SH (b_lo A n)) (zcells (sh_quar n))) ->
  a0 = wz (qcache_t st) -> a3 = wz (b_chunk_beg A) -> a4 = wz (usz n) ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp + 64 <= 2^64 ->
  rw_cells bsegs m (bv_unsigned sp) (enq_frame j0 vs5 vs4 vs3 vs2 vs1 vs0 vra) ->
  evt bsegs (fun ms' => exists (a1' a2' a5' a6' a7' : word) (m' : word -> option byte),
      ms' = MS (mkR vra (wz (bv_unsigned sp + 64)) gp tp t0 t1 t2 vs0 vs1 a0 a1' a2' a3 a4 a5' a6' a7'
                    vs2 vs3 vs4 vs5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc vra) fc None m' (seg_rom bsegs)
      /\ munch [(qb_addr b + 8, qb_addr b + 24); (qb_addr b + qb_count b * 8 + 24, qb_addr b + qb_count b * 8 + 32);
                (qcache_t st + 24, qcache_t st + 32)] m m'
      /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp + 64)
      /\ cli_pres st (bv_unsigned sp + 64) m m' /\ errno_same m m'
      /\ RTREP (st_enq_last st A n) m')
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x363fc) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros HR WF MI HQ ROOM HIN SHQ -> -> -> ST HCL LO SPH FR.
  assert (Hb : In b (qall st)) by (unfold qall; rewrite HQ, !in_app_iff; left; right; left; reflexivity).
  pose proof (wq_batch st (wf_quar_ok st WF) b Hb) as [CNT _].
  assert (CZ : 0 <= qb_count b) by (unfold qb_count; lia).
  (nelimp (batch_geom st WF b Hb) 5%nat; intros _ _ BG1 BG2 BAL).
  pose proof (region_facts st WF 24 ltac:(unfold KNUMCLASSES; lia)) as RF. cbn zeta in RF. (nelim RF 7%nat; intros Y1 Y2 Y3 Y4 Y5 Y6 _).
  pose proof (t_range st WF) as TR. pose proof (t_vs_prim st WF) as TP.
  assert (HBA : In (A, n) (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; right; right; exact HIN).
  (nelimp (block_geom st WF A n HBA) 7%nat; intros Gn GA K X Y CE _).
  (* [comment removed for export] *)
  (nelimp (rr_thread st m HR) 4%nat; intros _ _ QC _). rewrite HQ in QC.
  rewrite zlen_app, zlen_cons, zlen_nil, qc_last_snoc in QC.
  destruct (proj1 (R_qlist_iff m (st_qthread st)) (proj1 (rr_batches st m HR)) q b [] HQ) as [LB (V & SL & SHD)]. cbn [qc_first] in LB.
  destruct (vis_cell m _ _ (qb_addr b + qb_count b * 8 + 24) 8 V ltac:(lia) ltac:(unfold QBATCH_SIZE, QBATCH_CAP in *; lia)) as [js SLOT].
  (* [comment removed for export] *)
  pose proof (wq_thread_max st (wf_quar_ok st WF)) as TM. rewrite HQ in TM.
  pose proof (qc_bytes_lb (q ++ [b])) as LBQ. rewrite zlen_app, zlen_cons, zlen_nil in LBQ. pose proof (zlen_nonneg q) as ZQ.
  pose proof (qb_size_le_bytes q b []) as SZB. pose proof (qb_size_lb b) as SZ0.
  assert (HF : 0 <= qc_first (q ++ [b]) < 2^64).
  { destruct q as [|b0 q']; cbn [qc_first app].
    - unfold KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF, KREGIONSIZE, PRIM_RES_SIZE, QBATCH_SIZE in *. lia.
    - assert (Hb0 : In b0 (qall st)) by (unfold qall; rewrite HQ, !in_app_iff; left; left; left; reflexivity).
      (nelimp (batch_geom st WF b0 Hb0) 5%nat; intros _ _ C1 C2 _). unfold KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF, KREGIONSIZE, PRIM_RES_SIZE, QBATCH_SIZE in *. lia. }
  replace (zlen q + (1 + 0)) with (zlen q + 1) in QC by lia.
  pose proof (qc_bytes_nonneg (q ++ [b])) as QB0.
  eapply evt_mono.
  { eapply (enq_t1_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j0 vs5 vs4 vs3 vs2 vs1 vs0 vra F fc m
              (qcache_t st) (zlen q + 1) (qc_first (q ++ [b])) (qb_addr b) (qc_bytes (q ++ [b])) 0 (qb_size b) (qb_count b)
              (b_chunk_beg A) (usz n) lo js);
        try reflexivity; try eassumption;
    unfold usz, b_chunk_beg, qcache_t, T_QCACHE, QBATCH_SIZE, QBATCH_CAP, QUAR_MAX_CACHE, KHIGHMEM_BEG, AIMG_HI, KFREEARRAY_OFF, KREGIONSIZE, PRIM_RES_SIZE in *;
    idtac; (cut_on [TM LBQ ZQ BG1 Y1 BG2 Y3 Y4 Y6 SZ0 K X Gn SZB ROOM CNT CZ Y TR Y2 TP] blia). }
  cbv beta. intros ms' nelH_; (nelim nelH_ 14%nat; intros a1' a2' a5' a6' a7' m' -> MU WM MI' ST' QC' LB' SL').
  exists a1', a2', a5', a6', a7', m'. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  split.
  { eapply (cli_pres_t1z st WF (bv_unsigned sp + 64) ltac:(idtac; unfold CEIL; lia) b); [exact Hb| unfold QBATCH_CAP in *; lia| | exact MU| exact WM].
    repeat apply Forall_cons; [| | | apply Forall_nil]; unfold t1z_ok; cbn [fst snd];
      (split; [| intros; unfold qcache_t, T_QCACHE, CEIL, KHIGHMEM_BEG, AIMG_HI, QBATCH_SIZE, QBATCH_CAP, KREGIONSIZE, KFREEARRAY_OFF, PRIM_RES_SIZE in *; lia]);
      [left; lia| right; left; lia| right; right; left; lia]. }
  split.
  { eapply errno_same_munch; [exact MU|]. repeat apply Forall_cons; [| | | apply Forall_nil]; cbn [fst snd];
      unfold AERRNO, ATP, qcache_t, T_QCACHE, KHIGHMEM_BEG, AIMG_HI in *; blia. }
  eapply (RTREP_enq_last' st WF q b A n HQ HIN ltac:(unfold QBATCH_CAP in *; lia) _ m m'); [| exact MU| exact WM| exact HR| exact SHQ| | |].
  - repeat apply Forall_cons; [| | | apply Forall_nil]; unfold t1z_ok; cbn [fst snd]; [left; lia| right; left; lia| right; right; left; lia].
  - exact QC'.
  - exact LB'.
  - replace (qb_addr b + 24 + 8 * qb_count b) with (qb_addr b + qb_count b * 8 + 24) by lia. exact SL'.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qthread_facts : forall st m, RTREP st m -> RTWF st ->
  0 <= zlen (st_qthread st) < 2^20 /\ 0 <= qc_first (st_qthread st) < 2^64 /\ 0 <= qc_last (st_qthread st) < 2^64
  /\ 0 <= qc_bytes (st_qthread st) <= QUAR_MAX_CACHE.
Proof.
  intros st m HR WF. pose proof (wq_thread_max st (wf_quar_ok st WF)) as TM. pose proof (qc_bytes_lb (st_qthread st)) as LB.
  pose proof (zlen_nonneg (st_qthread st)) as Z0. pose proof (qc_bytes_nonneg (st_qthread st)) as B0.
  assert (AD : forall b0, In b0 (st_qthread st) -> 0 <= qb_addr b0 < 2^64).
  { intros b0 Hb0. (nelimp (batch_geom st WF b0 ltac:(unfold qall; rewrite !in_app_iff; tauto)) 5%nat; intros _ _ R1 R2 _).
    pose proof (region_facts st WF 24 ltac:(unfold KNUMCLASSES; lia)) as RF. cbn zeta in RF. (nelim RF 7%nat; intros Y1 Y2 Y3 Y4 Y5 Y6 _).
    unfold KHIGHMEM_BEG, AIMG_HI, QBATCH_SIZE, KREGIONSIZE, KFREEARRAY_OFF, PRIM_RES_SIZE in *. lia. }
  unfold QUAR_MAX_CACHE, QBATCH_SIZE in *. split; [lia|]. split; [| split; [| lia]].
  - destruct (st_qthread st) as [|b0 q] eqn:E; cbn [qc_first]; [lia|]. apply AD. left. reflexivity.
  - unfold qc_last. destruct (st_qthread st) as [|b0 q] eqn:E; [lia|]. apply AD. apply last_In. discriminate.
Qed.

Definition t2_post (vra sp gp tp t0 t1 t2 vs0 vs1 a0 a3 a7 vs2 vs3 vs4 vs5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (st st' : rtstate) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (a1' a2' a4' a5' a6' : word) (m' : word -> option byte) (W : list (Z * Z)),
      ms' = MS (mkR vra (wz (bv_unsigned sp + 64)) gp tp t0 t1 t2 vs0 vs1 a0 a1' a2' a3 a4' a5' a6' a7
                    vs2 vs3 vs4 vs5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc vra) fc None m' (seg_rom bsegs)
      /\ munch W m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ Forall (fun iv : Z * Z => snd iv <= CEIL) W /\ stk bsegs m' lo (bv_unsigned sp + 64)
      /\ cli_pres st (bv_unsigned sp + 64) m m' /\ errno_same m m'
      /\ RTREP st' m'.

Section T2FULL.
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
          (j0 : list byte) (vs5 vs4 vs3 vs2 vs1 vs0 vra : word)
          (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate)
          (pre : list Z) (k A n lo : Z).
Let entry := MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (wz 0x3641c) fc None m (seg_rom bsegs).
Let post := t2_post vra sp gp tp t0 t1 t2 vs0 vs1 a0 a3 a7 vs2 vs3 vs4 vs5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                    st (st_enq_new (st_pop st 24 k pre) k A n) lo m.

(* [comment removed for export] *)
Definition t2_mid (CASE : Prop) : Prop :=
  RTREP st m -> RTWF st -> mem_inv bsegs m ->
  cch st 24 = pre ++ [k] -> st_apend st = [] -> In (A, n) (st_qpend st) ->
  CASE ->
  (bprim n = true -> rw_cells bsegs m (SH (b_lo A n)) (zcells (sh_quar n))) ->
  a0 = wz (qcache_t st) -> a1 = wz (acache st) -> a3 = wz (b_chunk_beg A) -> a4 = wz (usz n) -> a5 = wz (zlen pre + 1) ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp + 64 <= 2^64 ->
  rw_cells bsegs m (bv_unsigned sp) (enq_frame j0 vs5 vs4 vs3 vs2 vs1 vs0 vra) ->
  evt bsegs post entry.

(* [comment removed for export] *)
Lemma enq_t2_full_e : t2_mid (st_qthread st = []).
Proof.
  unfold t2_mid, post, entry, t2_post.
  intros HR WF MI HC HAP HIN CASEH SHQ -> -> -> -> -> ST HCL LO SPH FR.
  assert (Hc24 : 0 <= 24 < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  pose proof (t_range st WF) as TR; pose proof (t_vs_prim st WF) as TP; pose proof (wb_t_align st (wf_base_ok st WF)) as TAL.
  pose proof (tpx_ok_of_RTWF st WF) as HX.
  assert (HBA : In (A, n) (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; right; right; exact HIN).
  (nelimp (block_geom st WF A n HBA) 8%nat; intros Gn GA K X Y CE L16 _); unfold usz in Y.
  assert (L8 : b_lo A n mod 8 = 0) by (apply (mod0_trans _ 8 16); [lia|lia|reflexivity|exact L16]).
  (nelimp (S_range st WF) 3%nat; intros SR1 SR2 SR3); (nelimp (P_range st WF) 3%nat; intros PR1 PR2 PR3).
  destruct (rr_cache st m HR 24 Hc24) as [PC CEN].
  assert (LEN : zlen (cch st 24) = zlen pre + 1) by (rewrite HC, zlen_app, zlen_cons, zlen_nil; lia); rewrite LEN in PC.
  pose proof (zlen_nonneg pre) as PZ.
  pose proof (CEN (zlen pre) ltac:(lia)) as CK; rewrite HC, nthz_app_last in CK; clear CEN.
  replace (pcaddr st 24 + 16 + 4 * zlen pre) with (acache st + 4 * (zlen pre + 1 - 1) + 1936) in CK by (unfold pcaddr; lia).
  replace (pcaddr st 24) with (acache st + 1920) in PC by (unfold pcaddr; lia).
  destruct (tstat_cell st m HR WF) as [sv SV]; replace (st_t st + 2784) with (acache st + 2576) in SV by (unfold acache, T_ACACHE; lia).
  pose proof (wc_cache_max st 24 (wf_class_ok st WF 24 Hc24)) as CM; rewrite LEN in CM; change (cmaxcount 24) with 2 in CM.
  assert (CV : carved_cptr st 24 k) by
    (apply (wc_used_carved st 24 (wf_class_ok st WF 24 Hc24)); unfold used_cptrs, avail_cptrs; rewrite !in_app_iff; left; right; rewrite HC; apply in_or_app; right; left; reflexivity).
  (nelim (carved_chunk st WF 24 k Hc24 ltac:(lia) CV) 3%nat; intros C1 C2 C3); change (csize 24) with 8192 in C2, C3.
  pose proof (region_facts st WF 24 Hc24) as RF; cbn zeta in RF; (nelim RF 10%nat; intros Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10).
  (nelim CV 3%nat; intros j Hj Ek).
  assert (KB : 0 <= k < 2^28) by
    (pose proof (chunk_cptr_eq 24 j ltac:(lia)) as E16; rewrite <- Ek in E16; clear - E16 Hj C1 C2 Y5 Y6; unfold cptr_addr, KFREEARRAY_OFF in *; change (csize 24) with 8192 in E16; nia).
  set (b := cptr_addr st 24 k).
  assert (Eb : b = st_spacebeg st + 24 * 2^32 + 16 * k) by (unfold b, cptr_addr; rewrite (rbeg_val st); unfold KREGIONSIZE; lia).
  assert (AL8 : (acache st + 2576) mod 8 = 0) by
    (unfold acache, T_ACACHE; replace (st_t st + 208 + 2576) with (st_t st + 2784) by lia; apply mod0_add; [lia| apply (mod0_trans _ 8 4096); [lia|lia|reflexivity|exact TAL]| reflexivity]).
  (nelimp (rr_thread st m HR) 4%nat; intros _ _ QC _).
  (nelimp (proj1 (rr_alloc st m HR)) 4%nat; intros j1 j2 j3 AL).
  (nelim (qthread_facts st m HR WF) 4%nat; intros QF1 QF2 QF3 QF4).
  (* [comment removed for export] *)
  assert (NA : 1 <= zlen pre + 1 <= 16) by (clear - PZ CM; lia).
  (* [comment removed for export] *)
  assert (NT : (16 <= acache st /\ (acache st + 3888 <= 65536 \/ 6287360 <= acache st - 208)) /\ acache st + 2584 <= alloc_ceiling
               /\ 16 <= qcache_t st /\ qcache_t st + 32 <= acache st /\ acache st - 208 <= qcache_t st)
    by (clear - TR; unfold acache, T_ACACHE, qcache_t, T_QCACHE, AIMG_HI, KHIGHMEM_BEG in *; blia).
  assert (NS : 0 <= st_spacebeg st /\ st_spacebeg st + 2^37 + 4096 <= alloc_ceiling /\ 0 <= st_pbase st < 2^64)
    by (clear - SR1 SR2 PR1 PR2; unfold KHIGHMEM_BEG, AIMG_HI, KSPACESIZE, PRIM_RES_SIZE in *; lia).
  assert (NK : 0 <= b_chunk_beg A < 2^64 /\ 0 <= usz n < 2^62) by (clear - K X Y CE Gn; unfold b_chunk_beg, usz, KHIGHMEM_BEG, AIMG_HI in *; blia).
  assert (NSH : 2147450880 <= SH (b_lo A n) /\ SH (b_lo A n) + asz n / 8 <= 17594333495296)   (* [comment removed for export] *)
    by (split; [pose proof (rt_SH_mono 0 (b_lo A n) ltac:(clear - K; blia)) as SB0; change (SH 0) with 2147450880 in SB0; exact SB0|];
        rewrite <- (rt_SH_aligned_add (b_lo A n) (asz n) L8); pose proof (rt_SH_bounds (b_lo A n + asz n) ltac:(clear - K X Y CE; unfold b_hi, KHIGHMEM_BEG, AIMG_HI in *; blia)) as SB;
        clear - SB; unfold KHIGHMEM_BEG, AIMG_HI in *; lia).
  (* [comment removed for export] *)
  unfold enq_frame in FR; cbv beta delta [wz] in *; unfold ATP in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP; idtac.
  eapply evt_cut;
  [ eapply (enq_t2p_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (acache st) (zlen pre + 1) k
              (Z_to_bv 64 (pc_max_count st 24)) (Z_to_bv 64 (pc_class_size st 24)) sv);
      [exact MI| reflexivity| reflexivity| exact NA| exact KB
      | clear - NT; lia| idtac; clear - NT; lia
      | exact AL8| exact PC| exact CK| exact SV]
  | ].
  cbv beta; intros ms1 nelH_; (nelim nelH_ 9%nat; intros sv1 m1 -> MU1 WM1 MI1 PC1 CK1 SV1).
  set (st1 := st_pop st 24 k pre).
  pose proof (st_pop_same st 24 k pre) as SP'; fold st1 in SP'.
  destruct SP' as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16s & E17 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28). (* [comment removed for export] *)
  clear E4 E6 E7 E9 E10 E12 E13 E14 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 E28.
  assert (HR1 : RTREP st1 m1) by
    (eapply RTREP_pop'; [exact WF| exact HX| lia| exact HC| | exact WM1| exact HR|];
     [ eapply munch_weaken; [| exact MU1]; unfold sub_fp, pcaddr, acache, T_ACACHE; cbn [outside]; intros x Hx; (lia_on Hx)
     | replace (pcaddr st 24) with (acache st + 1920) by (unfold pcaddr; lia); replace (zlen pre) with (zlen pre + 1 - 1) by lia; exact PC1 ]).
  assert (WF1 : RTWF st1) by (apply RTWF_pop'; [exact WF| lia| exact HC| exact HAP]).
  assert (HK1 : In (24, k) (st_apend st1)) by (rewrite E5; left; reflexivity).
  assert (HIN1 : In (A, n) (st_qpend st1)) by (rewrite E8; exact HIN).
  assert (ECP : cptr_addr st1 24 k = b) by (unfold b, cptr_addr, rbeg; rewrite E16s; reflexivity).
  assert (EQC : qcache_t st1 = qcache_t st) by (unfold qcache_t; rewrite E15; reflexivity).
  assert (QC1 : rw_cells bsegs m1 (qcache_t st) [W8 (zlen (st_qthread st)); W8 (qc_first (st_qthread st)); W8 (qc_last (st_qthread st)); W8 (qc_bytes (st_qthread st))])
    by (eapply rw_cells_transport; [exact QC| exact MU1| exact WM1| clear - NT; cbn; lia]).
  assert (AL1 : rw_cells bsegs m1 A_ALLOC [W8 (st_pbase st); W8 PRIM_RES_SIZE; CB 16 j1; W8 (st_spacebeg st); W4 (2^32 - 1); CB 4 j2; W8 (st_spacebeg st + KSPACESIZE); W1 0; CB 7 j3])
    by (eapply rw_cells_transport; [exact AL| exact MU1| exact WM1| clear - NT; cbn; unfold A_ALLOC, AIMG_HI in *; lia]).
  assert (SHQ1 : bprim n = true -> rw_cells bsegs m1 (SH (b_lo A n)) (zcells (sh_quar n)))
    by (intros EP; eapply rw_cells_transport; [exact (SHQ EP)| exact MU1| exact WM1|]; rewrite zcells_size, sh_quar_len by lia;
        unfold sh_tot; clear - NSH TR; cbn; unfold acache, T_ACACHE, KHIGHMEM_BEG, AIMG_HI in *; blia).
  assert (FR1 : rw_cells bsegs m1 (bv_unsigned sp) [CB 8 j0; C8 vs5; C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra])
    by (eapply rw_cells_transport; [exact FR| exact MU1| exact WM1| clear - NT HCL LO; cbn; lia]).
  assert (ST1 : stk bsegs m1 lo (bv_unsigned sp))
    by (eapply stk_transport_disjoint; [exact ST| exact MU1| exact WM1| clear - NT HCL LO; cbn; lia]).
  clear PC CK SV QC AL FR ST.
  (* [comment removed for export] *)
  pose proof (apend_geom st1 WF1 24 k HK1) as AG; rewrite ECP, E17 in AG; change (csize 24) with 8192 in AG.
  (nelim AG 11%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11).
  assert (NB_ : 17594333495296 <= b /\ b + 8192 <= alloc_ceiling /\ (st_t st + 4096 <= b \/ b + 8192 <= st_t st))
    by (pose proof (t_vs_prim st WF) as TP0; clear - TP0 G1 G2 G3 G4 G5 G6 G7 G8; unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, PRIM_RES_SIZE, CEIL in *; lia).
  destruct (rr_regions st1 m1 HR1 24 Hc24) as (VR & _); cbn zeta in VR.
  destruct (vis_cell m1 _ _ b 32 VR ltac:(clear - G1; lia) ltac:(clear - G2 G3; lia)) as [junk NB0].
  pose proof (rw_cells_split_CB bsegs m1 b [] 32 junk [] [8; 8; 8; 8]%nat NB0 eq_refl) as NB1; cbn [app mk_CB_cells] in NB1; clear NB0.
  (* [comment removed for export] *)
  eapply evt_cut;
  [ eapply (enq_t2h_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1
              (qcache_t st) k (st_spacebeg st) (st_pbase st) b (zlen (st_qthread st)) (qc_first (st_qthread st)) (qc_last (st_qthread st)) (qc_bytes (st_qthread st))
              (b_chunk_beg A) (usz n));
      [exact MI1| reflexivity| reflexivity| reflexivity| reflexivity| exact KB
      | clear - NS; lia| idtac; clear - NS; lia| exact Eb
      | clear - QF1; lia| exact QF2| exact QF3| clear - QF4; unfold QUAR_MAX_CACHE in QF4; lia
      | clear - NK; lia| clear - NK; lia| clear - NS; lia
      | clear - NT; lia| idtac; clear - NT; lia
      | clear - NT NB_; unfold qcache_t, T_QCACHE, acache, T_ACACHE in *; lia
      | exact AL1| exact NB1| exact QC1]
  | ].
  cbv beta; intros ms2 nelH_; (nelim nelH_ 9%nat; intros a6' m2 -> MU2 WM2 MI2 AL2 NB2 QC2).
  assert (HR2 : RTREP st1 m2) by
    (eapply (apz_all st1 WF1 (tpx_ok_of_RTWF st1 WF1) 24 k HK1 [(b, b + 32)]); [| exact MU2| exact WM2| exact HR1|];
     [ constructor; [| constructor]; unfold apz_ok; cbn [fst snd]; left; rewrite ECP; change (csize 24) with 8192; lia
     | constructor; [| constructor]; cbn [fst snd]; left; rewrite ECP; change (csize 24) with 8192; lia ]).
  assert (SHQ2 : bprim n = true -> rw_cells bsegs m2 (SH (b_lo A n)) (zcells (sh_quar n)))
    by (intros EP; eapply rw_cells_transport; [exact (SHQ1 EP)| exact MU2| exact WM2|]; rewrite zcells_size, sh_quar_len by lia;
        unfold sh_tot; clear - NSH NB_; cbn; lia).
  assert (FR2 : rw_cells bsegs m2 (bv_unsigned sp) [CB 8 j0; C8 vs5; C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra])
    by (eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2| clear - NB_ HCL LO; cbn; lia]).
  assert (ST2 : stk bsegs m2 lo (bv_unsigned sp))
    by (eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2| clear - NB_ HCL LO; cbn; lia]).
  assert (HSP : CEIL <= bv_unsigned sp + 64) by (clear - HCL LO; unfold CEIL; lia).
  rename CASEH into HQE.
  rewrite HQE in QC2. cbn [zlen length Z.of_nat qc_first qc_last qc_bytes fold_right] in QC2.
  rewrite HQE. cbn [qc_first qc_last qc_bytes fold_right]. change (zlen (@nil qbatch)) with 0.
  (* [comment removed for export] *)
  eapply evt_mono.
  { eapply (enq_t2e_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j0 vs5 vs4 vs3 vs2 vs1 vs0 vra F fc m2
              (qcache_t st) b 0 0 0 (usz n + 8192) lo);
      [exact MI2| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
      | clear - NB_; lia| lia| lia| lia| clear - NK; lia| clear - NK; lia
      | clear - NT; unfold AIMG_HI in NT; lia| idtac; clear - NT; lia
      | exact ST2| idtac; exact HCL| exact LO| exact SPH| exact FR2| exact QC2]. }
  cbv beta. intros ms3 nelH_; (nelim nelH_ 8%nat; intros a1' m3 -> MU3 WM3 MI3 ST3 QC3).
  exists a1', (Z_to_bv 64 1), (Z_to_bv 64 (usz n + 8192)), (Z_to_bv 64 0), a6', m3,
         ([(acache st + 1920, acache st + 1924); (acache st + 2576, acache st + 2584)] ++ [(b, b + 32)] ++ [(qcache_t st, qcache_t st + 32)]).
  split; [reflexivity|].
  split; [eapply munch_cat; [exact MU1| eapply munch_cat; [exact MU2| exact MU3]]|].
  split; [eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]|].
  split; [exact MI3|].
  split.
  { clear - NT NB_. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold CEIL; lia. }
  split; [exact ST3|].
  split.
  { unfold cli_pres. eapply cj_pres_of_munch; [eapply munch_cat; [exact MU1| eapply munch_cat; [exact MU2| exact MU3]]| eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]|].
    intros a Ha HCa. cbn. repeat split; intros Hin.
    - apply (tpage_not_client st WF (bv_unsigned sp + 64) HSP a); [clear - Hin NT; unfold acache, T_ACACHE in *; lia| exact HCa].
    - apply (tpage_not_client st WF (bv_unsigned sp + 64) HSP a); [clear - Hin NT; unfold acache, T_ACACHE in *; lia| exact HCa].
    - pose proof (chunk_not_client st1 WF1 24 k HK1 (bv_unsigned sp + 64) HSP a) as NC. rewrite ECP, E1, E2, E3 in NC.
      apply NC; [change (csize 24) with 8192; clear - Hin; lia| exact HCa].
    - apply (tpage_not_client_all st WF (bv_unsigned sp + 64) HSP a); [clear - Hin; unfold qcache_t, T_QCACHE in *; lia| exact HCa]. }
  split.
  { eapply errno_same_munch; [eapply munch_cat; [exact MU1| eapply munch_cat; [exact MU2| exact MU3]]|].
    clear - NT NB_. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AERRNO, ATP, AIMG_HI, qcache_t, T_QCACHE, acache, T_ACACHE in *; lia. }
  eapply (RTREP_enq_new_e' st1 WF1 k A n HK1 HIN1 [(qcache_t st, qcache_t st + 32)] m2 m3).
  - rewrite E11. exact HQE.
  - constructor; [| constructor]. unfold t2z_ok. cbn [fst snd]. right. left. rewrite EQC. lia.
  - exact MU3.
  - exact WM3.
  - exact HR2.
  - exact SHQ2.
  - rewrite ECP. replace (QBATCH_SIZE + usz n) with (usz n + 8192) by (unfold QBATCH_SIZE; lia). exact NB2.
  - rewrite EQC, ECP. replace (QBATCH_SIZE + usz n) with (0 + (usz n + 8192)) by (unfold QBATCH_SIZE; lia). exact QC3.
Qed.

(* [comment removed for export] *)
Lemma enq_t2_full_n : forall q l, qb_count l = QBATCH_CAP -> t2_mid (st_qthread st = q ++ [l]).
Proof.
  intros q l HFULL.
  unfold t2_mid, post, entry, t2_post.
  intros HR WF MI HC HAP HIN CASEH SHQ -> -> -> -> -> ST HCL LO SPH FR.
  assert (Hc24 : 0 <= 24 < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  pose proof (t_range st WF) as TR; pose proof (t_vs_prim st WF) as TP; pose proof (wb_t_align st (wf_base_ok st WF)) as TAL.
  pose proof (tpx_ok_of_RTWF st WF) as HX.
  assert (HBA : In (A, n) (all_blocks st)) by (unfold all_blocks; rewrite !in_app_iff; right; right; exact HIN).
  (nelimp (block_geom st WF A n HBA) 8%nat; intros Gn GA K X Y CE L16 _); unfold usz in Y.
  assert (L8 : b_lo A n mod 8 = 0) by (apply (mod0_trans _ 8 16); [lia|lia|reflexivity|exact L16]).
  (nelimp (S_range st WF) 3%nat; intros SR1 SR2 SR3); (nelimp (P_range st WF) 3%nat; intros PR1 PR2 PR3).
  destruct (rr_cache st m HR 24 Hc24) as [PC CEN].
  assert (LEN : zlen (cch st 24) = zlen pre + 1) by (rewrite HC, zlen_app, zlen_cons, zlen_nil; lia); rewrite LEN in PC.
  pose proof (zlen_nonneg pre) as PZ.
  pose proof (CEN (zlen pre) ltac:(lia)) as CK; rewrite HC, nthz_app_last in CK; clear CEN.
  replace (pcaddr st 24 + 16 + 4 * zlen pre) with (acache st + 4 * (zlen pre + 1 - 1) + 1936) in CK by (unfold pcaddr; lia).
  replace (pcaddr st 24) with (acache st + 1920) in PC by (unfold pcaddr; lia).
  destruct (tstat_cell st m HR WF) as [sv SV]; replace (st_t st + 2784) with (acache st + 2576) in SV by (unfold acache, T_ACACHE; lia).
  pose proof (wc_cache_max st 24 (wf_class_ok st WF 24 Hc24)) as CM; rewrite LEN in CM; change (cmaxcount 24) with 2 in CM.
  assert (CV : carved_cptr st 24 k) by
    (apply (wc_used_carved st 24 (wf_class_ok st WF 24 Hc24)); unfold used_cptrs, avail_cptrs; rewrite !in_app_iff; left; right; rewrite HC; apply in_or_app; right; left; reflexivity).
  (nelim (carved_chunk st WF 24 k Hc24 ltac:(lia) CV) 3%nat; intros C1 C2 C3); change (csize 24) with 8192 in C2, C3.
  pose proof (region_facts st WF 24 Hc24) as RF; cbn zeta in RF; (nelim RF 10%nat; intros Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10).
  (nelim CV 3%nat; intros j Hj Ek).
  assert (KB : 0 <= k < 2^28) by
    (pose proof (chunk_cptr_eq 24 j ltac:(lia)) as E16; rewrite <- Ek in E16; clear - E16 Hj C1 C2 Y5 Y6; unfold cptr_addr, KFREEARRAY_OFF in *; change (csize 24) with 8192 in E16; nia).
  set (b := cptr_addr st 24 k).
  assert (Eb : b = st_spacebeg st + 24 * 2^32 + 16 * k) by (unfold b, cptr_addr; rewrite (rbeg_val st); unfold KREGIONSIZE; lia).
  assert (AL8 : (acache st + 2576) mod 8 = 0) by
    (unfold acache, T_ACACHE; replace (st_t st + 208 + 2576) with (st_t st + 2784) by lia; apply mod0_add; [lia| apply (mod0_trans _ 8 4096); [lia|lia|reflexivity|exact TAL]| reflexivity]).
  (nelimp (rr_thread st m HR) 4%nat; intros _ _ QC _).
  (nelimp (proj1 (rr_alloc st m HR)) 4%nat; intros j1 j2 j3 AL).
  (nelim (qthread_facts st m HR WF) 4%nat; intros QF1 QF2 QF3 QF4).
  (* [comment removed for export] *)
  assert (NA : 1 <= zlen pre + 1 <= 16) by (clear - PZ CM; lia).
  (* [comment removed for export] *)
  assert (NT : (16 <= acache st /\ (acache st + 3888 <= 65536 \/ 6287360 <= acache st - 208)) /\ acache st + 2584 <= alloc_ceiling
               /\ 16 <= qcache_t st /\ qcache_t st + 32 <= acache st /\ acache st - 208 <= qcache_t st)
    by (clear - TR; unfold acache, T_ACACHE, qcache_t, T_QCACHE, AIMG_HI, KHIGHMEM_BEG in *; blia).
  assert (NS : 0 <= st_spacebeg st /\ st_spacebeg st + 2^37 + 4096 <= alloc_ceiling /\ 0 <= st_pbase st < 2^64)
    by (clear - SR1 SR2 PR1 PR2; unfold KHIGHMEM_BEG, AIMG_HI, KSPACESIZE, PRIM_RES_SIZE in *; lia).
  assert (NK : 0 <= b_chunk_beg A < 2^64 /\ 0 <= usz n < 2^62) by (clear - K X Y CE Gn; unfold b_chunk_beg, usz, KHIGHMEM_BEG, AIMG_HI in *; blia).
  assert (NSH : 2147450880 <= SH (b_lo A n) /\ SH (b_lo A n) + asz n / 8 <= 17594333495296)   (* [comment removed for export] *)
    by (split; [pose proof (rt_SH_mono 0 (b_lo A n) ltac:(clear - K; blia)) as SB0; change (SH 0) with 2147450880 in SB0; exact SB0|];
        rewrite <- (rt_SH_aligned_add (b_lo A n) (asz n) L8); pose proof (rt_SH_bounds (b_lo A n + asz n) ltac:(clear - K X Y CE; unfold b_hi, KHIGHMEM_BEG, AIMG_HI in *; blia)) as SB;
        clear - SB; unfold KHIGHMEM_BEG, AIMG_HI in *; lia).
  (* [comment removed for export] *)
  unfold enq_frame in FR; cbv beta delta [wz] in *; unfold ATP in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP; idtac.
  eapply evt_cut;
  [ eapply (enq_t2p_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (acache st) (zlen pre + 1) k
              (Z_to_bv 64 (pc_max_count st 24)) (Z_to_bv 64 (pc_class_size st 24)) sv);
      [exact MI| reflexivity| reflexivity| exact NA| exact KB
      | clear - NT; lia| idtac; clear - NT; lia
      | exact AL8| exact PC| exact CK| exact SV]
  | ].
  cbv beta; intros ms1 nelH_; (nelim nelH_ 9%nat; intros sv1 m1 -> MU1 WM1 MI1 PC1 CK1 SV1).
  set (st1 := st_pop st 24 k pre).
  pose proof (st_pop_same st 24 k pre) as SP'; fold st1 in SP'.
  destruct SP' as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16s & E17 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28). (* [comment removed for export] *)
  clear E4 E6 E7 E9 E10 E12 E13 E14 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 E28.
  assert (HR1 : RTREP st1 m1) by
    (eapply RTREP_pop'; [exact WF| exact HX| lia| exact HC| | exact WM1| exact HR|];
     [ eapply munch_weaken; [| exact MU1]; unfold sub_fp, pcaddr, acache, T_ACACHE; cbn [outside]; intros x Hx; (lia_on Hx)
     | replace (pcaddr st 24) with (acache st + 1920) by (unfold pcaddr; lia); replace (zlen pre) with (zlen pre + 1 - 1) by lia; exact PC1 ]).
  assert (WF1 : RTWF st1) by (apply RTWF_pop'; [exact WF| lia| exact HC| exact HAP]).
  assert (HK1 : In (24, k) (st_apend st1)) by (rewrite E5; left; reflexivity).
  assert (HIN1 : In (A, n) (st_qpend st1)) by (rewrite E8; exact HIN).
  assert (ECP : cptr_addr st1 24 k = b) by (unfold b, cptr_addr, rbeg; rewrite E16s; reflexivity).
  assert (EQC : qcache_t st1 = qcache_t st) by (unfold qcache_t; rewrite E15; reflexivity).
  assert (QC1 : rw_cells bsegs m1 (qcache_t st) [W8 (zlen (st_qthread st)); W8 (qc_first (st_qthread st)); W8 (qc_last (st_qthread st)); W8 (qc_bytes (st_qthread st))])
    by (eapply rw_cells_transport; [exact QC| exact MU1| exact WM1| clear - NT; cbn; lia]).
  assert (AL1 : rw_cells bsegs m1 A_ALLOC [W8 (st_pbase st); W8 PRIM_RES_SIZE; CB 16 j1; W8 (st_spacebeg st); W4 (2^32 - 1); CB 4 j2; W8 (st_spacebeg st + KSPACESIZE); W1 0; CB 7 j3])
    by (eapply rw_cells_transport; [exact AL| exact MU1| exact WM1| clear - NT; cbn; unfold A_ALLOC, AIMG_HI in *; lia]).
  assert (SHQ1 : bprim n = true -> rw_cells bsegs m1 (SH (b_lo A n)) (zcells (sh_quar n)))
    by (intros EP; eapply rw_cells_transport; [exact (SHQ EP)| exact MU1| exact WM1|]; rewrite zcells_size, sh_quar_len by lia;
        unfold sh_tot; clear - NSH TR; cbn; unfold acache, T_ACACHE, KHIGHMEM_BEG, AIMG_HI in *; blia).
  assert (FR1 : rw_cells bsegs m1 (bv_unsigned sp) [CB 8 j0; C8 vs5; C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra])
    by (eapply rw_cells_transport; [exact FR| exact MU1| exact WM1| clear - NT HCL LO; cbn; lia]).
  assert (ST1 : stk bsegs m1 lo (bv_unsigned sp))
    by (eapply stk_transport_disjoint; [exact ST| exact MU1| exact WM1| clear - NT HCL LO; cbn; lia]).
  clear PC CK SV QC AL FR ST.
  (* [comment removed for export] *)
  pose proof (apend_geom st1 WF1 24 k HK1) as AG; rewrite ECP, E17 in AG; change (csize 24) with 8192 in AG.
  (nelim AG 11%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11).
  assert (NB_ : 17594333495296 <= b /\ b + 8192 <= alloc_ceiling /\ (st_t st + 4096 <= b \/ b + 8192 <= st_t st))
    by (pose proof (t_vs_prim st WF) as TP0; clear - TP0 G1 G2 G3 G4 G5 G6 G7 G8; unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, PRIM_RES_SIZE, CEIL in *; lia).
  destruct (rr_regions st1 m1 HR1 24 Hc24) as (VR & _); cbn zeta in VR.
  destruct (vis_cell m1 _ _ b 32 VR ltac:(clear - G1; lia) ltac:(clear - G2 G3; lia)) as [junk NB0].
  pose proof (rw_cells_split_CB bsegs m1 b [] 32 junk [] [8; 8; 8; 8]%nat NB0 eq_refl) as NB1; cbn [app mk_CB_cells] in NB1; clear NB0.
  (* [comment removed for export] *)
  eapply evt_cut;
  [ eapply (enq_t2h_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1
              (qcache_t st) k (st_spacebeg st) (st_pbase st) b (zlen (st_qthread st)) (qc_first (st_qthread st)) (qc_last (st_qthread st)) (qc_bytes (st_qthread st))
              (b_chunk_beg A) (usz n));
      [exact MI1| reflexivity| reflexivity| reflexivity| reflexivity| exact KB
      | clear - NS; lia| idtac; clear - NS; lia| exact Eb
      | clear - QF1; lia| exact QF2| exact QF3| clear - QF4; unfold QUAR_MAX_CACHE in QF4; lia
      | clear - NK; lia| clear - NK; lia| clear - NS; lia
      | clear - NT; lia| idtac; clear - NT; lia
      | clear - NT NB_; unfold qcache_t, T_QCACHE, acache, T_ACACHE in *; lia
      | exact AL1| exact NB1| exact QC1]
  | ].
  cbv beta; intros ms2 nelH_; (nelim nelH_ 9%nat; intros a6' m2 -> MU2 WM2 MI2 AL2 NB2 QC2).
  assert (HR2 : RTREP st1 m2) by
    (eapply (apz_all st1 WF1 (tpx_ok_of_RTWF st1 WF1) 24 k HK1 [(b, b + 32)]); [| exact MU2| exact WM2| exact HR1|];
     [ constructor; [| constructor]; unfold apz_ok; cbn [fst snd]; left; rewrite ECP; change (csize 24) with 8192; lia
     | constructor; [| constructor]; cbn [fst snd]; left; rewrite ECP; change (csize 24) with 8192; lia ]).
  assert (SHQ2 : bprim n = true -> rw_cells bsegs m2 (SH (b_lo A n)) (zcells (sh_quar n)))
    by (intros EP; eapply rw_cells_transport; [exact (SHQ1 EP)| exact MU2| exact WM2|]; rewrite zcells_size, sh_quar_len by lia;
        unfold sh_tot; clear - NSH NB_; cbn; lia).
  assert (FR2 : rw_cells bsegs m2 (bv_unsigned sp) [CB 8 j0; C8 vs5; C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra])
    by (eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2| clear - NB_ HCL LO; cbn; lia]).
  assert (ST2 : stk bsegs m2 lo (bv_unsigned sp))
    by (eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2| clear - NB_ HCL LO; cbn; lia]).
  assert (HSP : CEIL <= bv_unsigned sp + 64) by (clear - HCL LO; unfold CEIL; lia).
  rename CASEH into HQN.
  rewrite HQN in QC2. rewrite zlen_app, qc_last_snoc in QC2. change (zlen [l]) with 1 in QC2.
  rewrite HQN in QF1, QF2, QF4. rewrite zlen_app in QF1. change (zlen [l]) with 1 in QF1. pose proof (zlen_nonneg q) as ZQ.
  (* [comment removed for export] *)
  assert (Hl0 : In l (qall st)) by (unfold qall; rewrite HQN, !in_app_iff; left; right; left; reflexivity).
  assert (Hl : In l (qall st1)) by (unfold qall; rewrite E11, HQN, !in_app_iff; left; right; left; reflexivity).
  destruct (proj1 (R_qlist_iff m2 (st_qthread st1)) (proj1 (rr_batches st1 m2 HR2)) q l [] ltac:(rewrite E11; exact HQN)) as [LBl _]. cbn [qc_first] in LBl.
  pose proof (rw_cells_take m2 (qb_addr l) [W8 0] [W8 (qb_size l); W8 (qb_count l)] LBl) as LN2.
  (nelimp (batch_geom st WF l Hl0) 5%nat; intros _ _ BL1 BL2 BAL).
  pose proof (apend_vs_batch st1 WF1 24 k HK1 l Hl) as LVB. rewrite ECP in LVB. change (csize 24) with 8192 in LVB.
  assert (NL : 17594333495296 <= qb_addr l /\ qb_addr l + 8192 <= alloc_ceiling /\ (st_t st + 4096 <= qb_addr l \/ qb_addr l + 8192 <= st_t st)).
  { pose proof (t_vs_prim st WF) as TP0. clear - TP0 BL1 BL2 Y1 Y2 Y3 Y4 Y5 Y6. unfold KHIGHMEM_BEG, AIMG_HI, QBATCH_SIZE, KREGIONSIZE, KFREEARRAY_OFF, PRIM_RES_SIZE in *. lia. }
  rewrite HQN. rewrite zlen_app. change (zlen [l]) with 1.
  (* [comment removed for export] *)
  eapply evt_mono.
  { eapply (enq_t2n_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j0 vs5 vs4 vs3 vs2 vs1 vs0 vra F fc m2
              (qcache_t st) b (zlen q + 1) (qc_first (q ++ [l])) (qb_addr l) (qc_bytes (q ++ [l])) (usz n + 8192) 0 lo);
      [exact MI2| reflexivity| reflexivity| reflexivity| reflexivity
      | clear - NB_; lia| clear - ZQ QF1; lia| exact QF2
      | clear - NL; lia| idtac; clear - NL; lia
      | lia| clear - QF4; lia| clear - NK; lia| clear - NK QF4; unfold QUAR_MAX_CACHE in QF4; lia
      | clear - NT; unfold AIMG_HI in NT; lia| idtac; clear - NT; lia
      | clear - NT NL; unfold qcache_t, T_QCACHE, acache, T_ACACHE in *; lia
      | exact ST2| idtac; exact HCL| exact LO| exact SPH| exact FR2| exact QC2| exact LN2]. }
  cbv beta. intros ms3 nelH_; (nelim nelH_ 10%nat; intros a1' a2' m3 -> MU3 WM3 MI3 ST3 QC3 LN3).
  exists a1', a2', (Z_to_bv 64 (usz n + 8192)), (Z_to_bv 64 (zlen q + 1)), a6', m3,
         ([(acache st + 1920, acache st + 1924); (acache st + 2576, acache st + 2584)] ++ [(b, b + 32)] ++ [(qb_addr l, qb_addr l + 8); (qcache_t st, qcache_t st + 32)]).
  split; [reflexivity|].
  split; [eapply munch_cat; [exact MU1| eapply munch_cat; [exact MU2| exact MU3]]|].
  split; [eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]|].
  split; [exact MI3|].
  split.
  { clear - NT NB_ NL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold CEIL; lia. }
  split; [exact ST3|].
  split.
  { unfold cli_pres. eapply cj_pres_of_munch; [eapply munch_cat; [exact MU1| eapply munch_cat; [exact MU2| exact MU3]]| eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]|].
    intros a Ha HCa. cbn. repeat split; intros Hin.
    - apply (tpage_not_client st WF (bv_unsigned sp + 64) HSP a); [clear - Hin NT; unfold acache, T_ACACHE in *; lia| exact HCa].
    - apply (tpage_not_client st WF (bv_unsigned sp + 64) HSP a); [clear - Hin NT; unfold acache, T_ACACHE in *; lia| exact HCa].
    - pose proof (chunk_not_client st1 WF1 24 k HK1 (bv_unsigned sp + 64) HSP a) as NC. rewrite ECP, E1, E2, E3 in NC.
      apply NC; [change (csize 24) with 8192; clear - Hin; lia| exact HCa].
    - apply (batch_not_client st WF (bv_unsigned sp + 64) HSP l a Hl0); [clear - Hin; unfold QBATCH_SIZE; lia| exact HCa].
    - apply (tpage_not_client_all st WF (bv_unsigned sp + 64) HSP a); [clear - Hin; unfold qcache_t, T_QCACHE in *; lia| exact HCa]. }
  split.
  { eapply errno_same_munch; [eapply munch_cat; [exact MU1| eapply munch_cat; [exact MU2| exact MU3]]|].
    clear - NT NB_ NL. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold AERRNO, ATP, AIMG_HI, qcache_t, T_QCACHE, acache, T_ACACHE in *; lia. }
  eapply (RTREP_enq_new_n' st1 WF1 k A n HK1 HIN1 [(qb_addr l, qb_addr l + 8); (qcache_t st, qcache_t st + 32)] m2 m3 q l).
  - rewrite E11. exact HQN.
  - constructor; [| constructor; [| constructor]]; unfold t2z_ok; cbn [fst snd]; [left; lia| right; left; rewrite EQC; lia].
  - exact MU3.
  - exact WM3.
  - exact HR2.
  - exact SHQ2.
  - rewrite ECP. replace (QBATCH_SIZE + usz n) with (usz n + 8192) by (unfold QBATCH_SIZE; lia). exact NB2.
  - rewrite EQC, ECP. replace (zlen q + 2) with (zlen q + 1 + 1) by lia.
    replace (qc_bytes (q ++ [l]) + (QBATCH_SIZE + usz n)) with (qc_bytes (q ++ [l]) + (usz n + 8192)) by (unfold QBATCH_SIZE; lia). exact QC3.
  - rewrite ECP. exact LN3.
Qed.
End T2FULL.


End CeilWrap.
End RTW_q_enq2.

(* [comment removed for export] *)
Module RTW_q_zone2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_apz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_lib4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_q_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf2.RTW_q_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_zone OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_lock RTW_q_car OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac ulia := unfold KHIGHMEM_BEG, AIMG_HI, CEIL, KREGIONSIZE, KFREEARRAY_OFF, PRIM_RES_SIZE, PTRARR_RES_SIZE, QBATCH_SIZE in *; first [lia | blia].

Section UCZ2.
Variable st : rtstate.
Hypothesis WF : RTWF st.
Variables (c k : Z).
Hypothesis HcK : 0 <= c < KNUMCLASSES.
Hypothesis Hc1 : 1 <= c.
Hypothesis UK : In k (used_cptrs st c).
Variable W : list (Z * Z).
Hypothesis HW : Forall (ucz_ok st c k) W.
Variables (m m' : word -> option byte).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.

Local Ltac img := apply (ucz_img st WF c k HcK Hc1 UK W HW);
  [unfold AIMG_LO, A_ALLOC; cbn -[Z.add Z.mul Z.le Z.lt Z.sub]; lia| unfold AIMG_HI, A_ALLOC; cbn -[Z.add Z.mul Z.le Z.lt Z.sub]; lia| unfold A_QUAR, A_ALLOC; cbn -[Z.add Z.mul Z.le Z.lt Z.sub]; lia].

(* [comment removed for export] *)
Theorem UZ_core :
  (forall c' k', 0 <= c' < KNUMCLASSES -> In k' (avail_cptrs st c' ++ apend_cptrs st c') -> (c', k') <> (c, k)) ->
  coreC st m -> coreC st m'.
Proof.
  intros CKA (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11).
  Local Ltac tapp T st WF W m m' MU WM :=
    first [ eapply (T st WF W m m' MU WM) | eapply (T st W m m' MU WM) | eapply (T W m m' MU WM) | eapply (T W m m' MU) ].
  split; [tapp T_link st WF W m m' MU WM; [exact H1| exact (UZ_link st WF c k HcK Hc1 UK W HW)]|].
  split; [tapp T_consts st WF W m m' MU WM; [exact H2| exact (UZ_consts st WF c k HcK Hc1 UK W HW)]|].
  split; [tapp T_rinfo st WF W m m' MU WM; [exact H3| exact (UZ_rinfo st WF c k HcK Hc1 UK W HW)]|].
  split; [tapp T_regions st WF W m m' MU WM; [exact H4| exact (UZ_regions st WF c k HcK Hc1 UK W HW)]|].
  split; [tapp T_cache st WF W m m' MU WM; [exact H5| exact (UZ_cache st WF c k HcK Hc1 UK W HW)]|].
  split; [tapp T_ptrarr st WF W m m' MU WM; [exact H6| exact (UZ_ptrarr st WF c k HcK Hc1 UK W HW)]|].
  split; [tapp T_depot st WF W m m' MU WM; [exact H7| exact (UZ_depot st WF c k HcK Hc1 UK W HW)]|].
  split; [tapp T_fs st WF W m m' MU WM; [exact H8| exact (UZ_fs st WF c k HcK Hc1 UK W HW)]|].
  split; [tapp T_ia st WF W m m' MU WM; [exact H9| exact (UZ_ia st WF c k HcK Hc1 UK W HW)]|].
  split; [tapp T_lowshadow st WF W m m' MU WM; [exact H10| exact (UZ_lowshadow st WF c k HcK Hc1 UK W HW)]|].
  intros c' k' Hc' Hin. eapply (rwT W m m' MU WM); [exact (H11 c' k' Hc' Hin)|].
  destruct (Z.eq_dec c' 0) as [->|NZ].
  { exfalso. unfold avail_cptrs in Hin. pose proof (wb_class0 st (wf_base_ok st WF)) as [E1 E2]. rewrite E1, E2 in Hin. cbn in Hin.
    unfold apend_cptrs in Hin. apply in_map_iff in Hin as ([c'' k''] & _ & Hf). apply filter_In in Hf as [Hin Hb]. cbn [fst] in Hb.
    apply Z.eqb_eq in Hb. subst c''. pose proof (wq_apend st (wf_quar_ok st WF) _ Hin). cbn [fst] in *. lia. }
  pose proof (csize_pos c' ltac:(unfold KNUMCLASSES in Hc'; lia)) as SP.
  unfold sh_avail. rewrite zcells_zrep_size by (Z.div_mod_to_equations; lia).
  apply (UZ_avail_other st WF c k HcK Hc1 UK W HW); [exact Hc'| exact Hin| exact (CKA c' k' Hc' Hin)].
Qed.

(* [comment removed for export] *)
Lemma UZ_alloc4' : R_alloc4 st m -> R_alloc4 st m'.
Proof.
  intros ((j1 & j2 & j3 & H1) & (i1 & i2 & i3 & H2) & (jg & H3) & H5).
  split; [exists j1, j2, j3; eapply (rwT W m m' MU WM); [exact H1| unfold A_ALLOC; img]|].
  split; [exists i1, i2, i3; eapply (rwT W m m' MU WM); [exact H2| unfold A_SECONDARY, A_ALLOC; img]|].
  split; [exists jg; eapply (rwT W m m' MU WM); [exact H3| unfold A_GSTATS, A_ALLOC; img]|].
  eapply (roT W m m' MU); [exact H5| unfold A_MAXUSERSZ; img].
Qed.

(* [comment removed for export] *)
Lemma UZ_QA : QA m -> disjoint_from W A_QUAR 152 -> QA m'.
Proof. intros (j1 & j2 & H) D. exists j1, j2. eapply (rwT W m m' MU WM); [exact H| exact D]. Qed.
Lemma UZ_QLK : forall a b, QLK m a b -> disjoint_from W (A_QUAR + 152) 8 -> QLK m' a b.
Proof.
  intros a b (b2 & b3 & j4 & H1 & H2) D. exists b2, b3, j4.
  split; [eapply (rwT W m m' MU WM); [exact H1|]| eapply (rwT W m m' MU WM); [exact H2|]]; cbn;
    (eapply disjoint_from_sub; [exact D| lia| lia]).
Qed.
Lemma UZ_QH4 : forall n f l byts, QH4 m n f l byts -> disjoint_from W (A_QUAR + 160) 32 -> QH4 m' n f l byts.
Proof. intros n f l byts H D. eapply (rwT W m m' MU WM); [exact H| exact D]. Qed.
Lemma UZ_QH : forall qg, QH m qg -> disjoint_from W (A_QUAR + 160) 32 -> QH m' qg.
Proof. intros qg H D. eapply (rwT W m m' MU WM); [exact H| exact D]. Qed.
Lemma UZ_QS : QS m -> disjoint_from W (A_QUAR + 192) 64 -> QS m'.
Proof. intros (j5 & H) D. exists j5. eapply (rwT W m m' MU WM); [exact H| exact D]. Qed.
Lemma UZ_TC : forall qt, TC st m qt -> disjoint_from W (qcache_t st) 32 -> TC st m' qt.
Proof. intros qt H D. eapply (rwT W m m' MU WM); [exact H| exact D]. Qed.

(* [comment removed for export] *)
Lemma UZ_threadx : R_threadx st m -> tpx_ok st -> R_threadx st m'.
Proof.
  intros (TV & (j1 & j2 & j3 & j4 & j5 & TT) & TU & CT1 & CT2 & K1 & K2 & K3 & K4 & K5 & K6 & K7) [CX DX].
  pose proof (t_range st WF) as [T1 T2]. pose proof (t_vs_chunkU st WF c k HcK Hc1 UK) as TCU. pose proof (shU st WF c k HcK Hc1 UK) as (S1 & S2 & S3 & S4).
  change (SH KHIGHMEM_BEG) with 0x2008fff7000 in S1.
  destruct (wb_ctx_loose st (wf_base_ok st WF)) as (cb & ck & CL1 & CL2 & CL3). destruct (loose0_range st WF _ _ CL1) as (R1 & R2 & R3 & R4). olin R1.
  pose proof (loose_vs_chunkU st WF c k HcK Hc1 UK cb ck CL1) as LC.
  destruct (wb_dtls_loose st (wf_base_ok st WF)) as (db & dk & DL1 & DL2 & DL3). destruct (loose0_range st WF _ _ DL1) as (Q1 & Q2 & Q3 & Q4).
  pose proof (oclr_lin _ _ Q1 ltac:(lia)) as (_ & QLB & QLI). unfold KLOWSHADOW_BEG, KHIGHMEM_BEG, AIMG_LO, AIMG_HI in QLB, QLI.
  pose proof (loose_vs_chunkU st WF c k HcK Hc1 UK db dk DL1) as LD.
  unfold R_threadx. unfold A_TSD_PTR, A_TSD_MAIN, A_DTV_PTR, A_DTV, A_TLSMOD, A_FSTLS_CELL, A_DTLS_OFF, ATP in *.
  split; [eapply visTo; [exact WM| exact TV| exact T1| unfold CEIL in *; lia]|].
  split; [exists j1, j2, j3, j4, j5; eapply (rwT W m m' MU WM); [exact TT| cbn; apply (ucz_disj st WF c k W HW); unfold T_QCACHE, T_STATS, CEIL in *; rewrite ?A_QUAR_val in *; blia]|].
  split; [eapply (rwT W m m' MU WM); [exact TU| cbn; apply (ucz_disj st WF c k W HW); unfold T_QCACHE, T_UNWINDING, T_STATS, CEIL in *; rewrite ?A_QUAR_val in *; blia]|].
  split; [eapply (rwT W m m' MU WM); [exact CT1| cbn; eapply (ucz_obj st WF c k HcK Hc1 UK W HW (st_ctx st) (st_ctx st + 160)); unfold CTX_TID, CEIL in *; blia]|].
  split; [eapply (rwT W m m' MU WM); [exact CT2| cbn; eapply (ucz_obj st WF c k HcK Hc1 UK W HW (st_ctx st) (st_ctx st + 160)); unfold CTX_THREAD, CEIL in *; blia]|].
  split; [eapply (roT W m m' MU); [exact K1| cbn; img]|].
  split; [eapply (roT W m m' MU); [exact K2| cbn; img]|].
  split; [eapply (roT W m m' MU); [exact K3| cbn; img]|].
  split; [eapply (roT W m m' MU); [exact K4| cbn; img]|].
  split; [eapply (roT W m m' MU); [exact K5| cbn; img]|].
  split; [eapply (roT W m m' MU); [exact K6| cbn; img]|].
  eapply (roT W m m' MU); [exact K7| cbn]. eapply (ucz_obj st WF c k HcK Hc1 UK W HW (tl_dtls_block (st_tls st) + 24) (tl_dtls_block (st_tls st) + 32));
    [ clear - LD DL2 DL3; lia | exact DX | clear - QLB DL2 DL3 Q2; unfold KLOWSHADOW_BEG, KHIGHMEM_BEG; lia
    | clear - QLI DL2 DL3 Q2; unfold AIMG_LO, AIMG_HI; lia | unfold CEIL; clear - Q3 DL3; lia | lia | lia ].
Qed.

(* [comment removed for export] *)
Lemma UZ_live' : R_live st m -> (forall A n, In (A, n) (st_lb st) -> chunk_ne st c k A n) -> R_live st m'.
Proof. intros H NE A n Hin. exact (UZ_live st WF c k HcK Hc1 UK W HW m m' MU WM H A n Hin (NE A n Hin)). Qed.
Lemma UZ_quar' : R_quar st m ->
  (forall A n, In (A, n) (qelems st) -> chunk_ne st c k A n) ->
  (forall A n, In (A, n) (st_qpend st) -> chunk_ne st c k A n) ->
  R_quar st m'.
Proof.
  intros H NE1 NE2. destruct (UZ_quar st WF c k HcK Hc1 UK W HW m m' MU WM H) as [Q1 Q2].
  split; [intros A n Hin; exact (Q1 A n Hin (NE1 A n Hin))| intros A n Hin; exact (Q2 A n Hin (NE2 A n Hin))].
Qed.

(* [comment removed for export] *)
Lemma UZ_qlist' : forall q, R_qlist m q -> (forall b, In b q -> In b (qall st) /\ batch_ne st c k b) -> R_qlist m' q.
Proof.
  intros q H SUB. apply (proj2 (R_qlist_iff m' q)). intros q1 b q2 E.
  apply (UZ_qlist st WF c k HcK Hc1 UK W HW m m' q MU WM (fun b0 Hb0 => proj1 (SUB b0 Hb0)) H q1 b q2 E).
  apply (proj2 (SUB b ltac:(rewrite E; apply in_or_app; right; left; reflexivity))).
Qed.
Lemma UZ_qcur' : forall cur, QCUR m cur -> (forall bd, In bd cur -> In (fst bd) (qall st) /\ batch_ne st c k (fst bd)) -> QCUR m' cur.
Proof.
  intros cur H SUB bd Hbd. destruct (SUB bd Hbd) as [Hin NE]. destruct (H bd Hbd) as [[nx HL] HS].
  destruct (UZ_QBC st WF c k HcK Hc1 UK W HW m m' MU WM (fst bd) nx Hin NE (conj HL HS)) as [HL' HS'].
  split; [exists nx; exact HL'| exact HS'].
Qed.

(* [comment removed for export] *)
Lemma UZ_QBC_a : forall x nxt, In (qb_addr x) (qbatch_addrs st) -> 0 <= qb_count x <= QBATCH_CAP -> batch_ne st c k x ->
  QBC m x nxt -> QBC m' x nxt.
Proof.
  intros x nxt Ha CNT NE (HL & (V & SL & SHD)).
  apply in_map_iff in Ha as (b0 & Eb & Hb0).
  assert (NE0 : batch_ne st c k b0) by (intros [E1 E2]; apply NE; split; [exact E1| rewrite <- Eb; exact E2]).
  destruct (batch_geom st WF b0 Hb0) as (BB & BF & R1 & R2 & AL). rewrite Eb in R1, R2, AL.
  pose proof (region_facts st WF 24 ltac:(unfold KNUMCLASSES; lia)) as RF. cbn zeta in RF. destruct RF as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  pose proof (used_vs_batch st WF c k HcK Hc1 UK b0 Hb0 NE0) as CB. rewrite Eb in CB.
  assert (TB : qb_addr x + QBATCH_SIZE <= st_t st \/ st_t st + 4096 <= qb_addr x).
  { pose proof (t_vs_prim st WF). unfold KREGIONSIZE, KFREEARRAY_OFF, QBATCH_SIZE in *. lia. }
  unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, KFREEARRAY_OFF, QBATCH_SIZE, QBATCH_CAP, PRIM_RES_SIZE in *.
  assert (OBJ : forall a sz, qb_addr x <= a -> a + sz <= qb_addr x + 8192 -> disjoint_from W a sz).
  { intros a sz Ha Hs. eapply (ucz_obj st WF c k HcK Hc1 UK W HW (qb_addr x) (qb_addr x + 8192)); [ulia| ulia| ulia| ulia| ulia| ulia| ulia]. }
  split; [| split; [| split]].
  - eapply (rwT W m m' MU WM); [exact HL| cbn; apply OBJ; lia].
  - eapply visT; [exact WM| exact V| unfold AIMG_HI; lia].
  - intros i Hi. eapply (rwT W m m' MU WM); [exact (SL i Hi)| cbn; apply OBJ; lia].
  - assert (AL8 : qb_addr x mod 8 = 0) by (apply (mod0_trans _ 8 32); [lia|lia|reflexivity|exact AL]).
    eapply (rwT W m m' MU WM); [exact SHD|]. unfold sh_avail. change (csize 24) with 8192. rewrite zcells_zrep_size by lia.
    eapply (ucz_sh st WF c k HcK Hc1 UK W HW (qb_addr x) (qb_addr x + 8192)); [ulia| ulia| exact AL8| ulia| ulia| ].
    rewrite rt_SH_aligned_add by exact AL8. change (8192 / 8) with 1024. lia.
Qed.
Lemma UZ_qlist_a : forall q, R_qlist m q ->
  (forall b, In b q -> In (qb_addr b) (qbatch_addrs st) /\ 0 <= qb_count b <= QBATCH_CAP /\ batch_ne st c k b) -> R_qlist m' q.
Proof.
  intros q H SUB. apply (proj2 (R_qlist_iff m' q)). intros q1 b q2 E.
  destruct (SUB b ltac:(rewrite E; apply in_or_app; right; left; reflexivity)) as (A1 & A2 & A3).
  apply (UZ_QBC_a b _ A1 A2 A3). exact (proj1 (R_qlist_iff m q) H q1 b q2 E).
Qed.
Lemma UZ_qcur_a : forall cur, QCUR m cur ->
  (forall bd, In bd cur -> In (qb_addr (fst bd)) (qbatch_addrs st) /\ 0 <= qb_count (fst bd) <= QBATCH_CAP /\ batch_ne st c k (fst bd)) -> QCUR m' cur.
Proof.
  intros cur H SUB bd Hbd. destruct (SUB bd Hbd) as (A1 & A2 & A3). destruct (H bd Hbd) as [[nx HL] HS].
  destruct (UZ_QBC_a (fst bd) nx A1 A2 A3 (conj HL HS)) as [HL' HS']. split; [exists nx; exact HL'| exact HS'].
Qed.
End UCZ2.


End CeilWrap.
End RTW_q_zone2.

(* [comment removed for export] *)
Module RTW_q_drain2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.LNodes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_lib2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_lib4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_apz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_q_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf2.RTW_q_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_zone RTW_q_rep RTW_q_enq2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_lock RTW_q_car RTW_q_zone2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma H24 : 0 <= 24 < KNUMCLASSES. Proof. unfold KNUMCLASSES; lia. Qed.

Lemma nodup_qbatch_addrs : forall st, RTWF st -> List.NoDup (qbatch_addrs st).
Proof.
  intros st WF. pose proof (wc_used_nodup st 24 (wf_class_ok st WF 24 H24)) as ND. rewrite used_cptrs_split in ND.
  apply NoDup_app_remove_l in ND. apply NoDup_app_remove_l in ND. apply NoDup_app_remove_r in ND.
  unfold batch_cptrs in ND. rewrite Z.eqb_refl in ND.
  exact (NoDup_map_inv _ _ ND).
Qed.

(* [comment removed for export] *)
Definition QBCx (m : word -> option byte) (b : qbatch) : Prop :=
  rw_cells bsegs m (qb_addr b + 8) [W8 (qb_size b); W8 (qb_count b)] /\ R_qslots m b.
Lemma QBC_split : forall m b nxt, QBC m b nxt <-> rw_cells bsegs m (qb_addr b) [W8 nxt] /\ QBCx m b.
Proof.
  intros m b nxt. unfold QBC, QBCx.
  pose proof (rw_cells_app m (qb_addr b) [W8 nxt] [W8 (qb_size b); W8 (qb_count b)]) as E.
  cbn [cells_size Cells.csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ app] in E. rewrite E. tauto.
Qed.

Section KB.
Variable K : rtstate.
Hypothesis WF : RTWF K.

Lemma batch_facts : forall b, In b (qall K) ->
  KHIGHMEM_BEG <= qb_addr b /\ qb_addr b + QBATCH_SIZE <= CEIL /\ qb_addr b mod 32 = 0
  /\ (st_t K + 4096 <= qb_addr b \/ qb_addr b + QBATCH_SIZE <= st_t K)
  /\ 0 <= qb_count b <= QBATCH_CAP.
Proof.
  intros b Hb. destruct (batch_geom K WF b Hb) as (_ & _ & R1 & R2 & AL).
  pose proof (region_facts K WF 24 H24) as RF. cbn zeta in RF. destruct RF as (X1 & X2 & X3 & X4 & X5 & X6 & _).
  pose proof (t_vs_prim K WF) as TP. pose proof (proj1 (wq_batch K (wf_quar_ok K WF) b Hb)) as CNT.
  assert (0 <= qb_count b) by (unfold qb_count; lia).
  unfold QBATCH_SIZE, CEIL, KREGIONSIZE, KFREEARRAY_OFF in *. repeat split; try lia.
Qed.

(* [comment removed for export] *)
Lemma QBCx_keep : forall W m m' b, munch W m m' -> wmono bsegs m m' -> In b (qall K) -> QBCx m b ->
  Forall (fun iv => CEIL <= fst iv \/ snd iv <= AIMG_HI \/ (st_t K <= fst iv /\ snd iv <= st_t K + 4096)
                    \/ (qb_addr b <= fst iv /\ snd iv <= qb_addr b + 8)) W ->
  QBCx m' b.
Proof.
  intros W m m' b MU WM Hb (HC & V & SL & SHD) HW.
  pose proof (batch_facts b Hb) as (B1 & B2 & B3 & B4 & B5). pose proof (t_range K WF) as [T1 T2].
  assert (AL8 : qb_addr b mod 8 = 0) by (apply (mod0_trans _ 8 32); [lia|lia|reflexivity|exact B3]).
  pose proof (rt_SH_bounds (qb_addr b) ltac:(unfold QBATCH_SIZE, CEIL, KHIGHMEM_BEG, AIMG_HI in *; lia)) as SB1.
  pose proof (rt_SH_bounds (qb_addr b + 8192) ltac:(unfold QBATCH_SIZE, CEIL, KHIGHMEM_BEG, AIMG_HI in *; lia)) as SB2.
  pose proof (rt_SH_aligned_add (qb_addr b) 8192 AL8) as SA. change (8192 / 8) with 1024 in SA.
  assert (OBJ : forall a sz, qb_addr b + 8 <= a -> a + sz <= qb_addr b + 8192 -> disjoint_from W a sz).
  { intros a sz Ha Hs. apply (disjoint_from_forallq _ W a sz HW). intros lo hi X. cbn [fst snd] in X.
    unfold QBATCH_SIZE, CEIL, AIMG_HI, KHIGHMEM_BEG in *. lia. }
  assert (SHW : disjoint_from W (SH (qb_addr b)) 1024).
  { apply (disjoint_from_forallq _ W _ _ HW). intros lo hi X. cbn [fst snd] in X.
    unfold QBATCH_SIZE, CEIL, AIMG_HI, KHIGHMEM_BEG in *. blia. }
  split; [| split; [| split]].
  - eapply (rwT W m m' MU WM); [exact HC| cbn; apply OBJ; lia].
  - eapply visT; [exact WM| exact V| unfold AIMG_HI, KHIGHMEM_BEG in *; lia].
  - intros i Hi. eapply (rwT W m m' MU WM); [exact (SL i Hi)| cbn; apply OBJ; unfold QBATCH_CAP in *; lia].
  - eapply (rwT W m m' MU WM); [exact SHD|]. unfold sh_avail. change (csize 24) with 8192. rewrite zcells_zrep_size by lia.
    change (8192 / 8) with 1024. exact SHW.
Qed.
End KB.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma snoc_or_nil' : forall {X} (l : list X), l = [] \/ exists q x, l = q ++ [x].
Proof.
  intros X l. induction l as [|a l IH] using rev_ind; [left; reflexivity|]. right. exists l, a. reflexivity.
Qed.
Lemma app_mid_cases : forall {X} (q1 q2 l1 l2 : list X) (b : X), q1 ++ b :: q2 = l1 ++ l2 ->
  (exists r, l1 = q1 ++ b :: r /\ q2 = r ++ l2) \/ (exists r, l2 = r ++ b :: q2 /\ q1 = l1 ++ r).
Proof.
  intros X q1. induction q1 as [|x q1 IH]; intros q2 l1 l2 b E.
  - destruct l1 as [|y l1]; cbn in E.
    + right. exists []. cbn. split; [symmetry; exact E| reflexivity].
    + injection E as -> ->. left. exists l1. split; reflexivity.
  - destruct l1 as [|y l1]; cbn in E.
    + right. exists (x :: q1). cbn. split; [symmetry; exact E| reflexivity].
    + injection E as -> E. destruct (IH _ _ _ _ E) as [(r & -> & ->)|(r & -> & ->)].
      * left. exists r. split; reflexivity.
      * right. exists r. split; reflexivity.
Qed.
Lemma qc_first_app_l : forall l r, l <> [] -> qc_first (l ++ r) = qc_first l.
Proof. intros l r H. destruct l; [congruence| reflexivity]. Qed.
Lemma qc_last_app_r : forall l r, r <> [] -> qc_last (l ++ r) = qc_last r.
Proof.
  intros l r H. destruct (snoc_or_nil' r) as [->|(q & x & ->)]; [congruence|]. rewrite app_assoc, !qc_last_snoc. reflexivity.
Qed.
Lemma zlen_pos_ne : forall {X} (l : list X), l <> [] -> 1 <= zlen l.
Proof. intros X l H. destruct l; [congruence|]. rewrite zlen_cons. pose proof (zlen_nonneg l). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dwin (K : rtstate) (lo SP : Z) (iv : Z * Z) : Prop :=
  (lo <= fst iv /\ snd iv <= SP)
  \/ (A_QUAR + 152 <= fst iv /\ snd iv <= A_QUAR + 192)
  \/ (st_t K <= fst iv /\ snd iv <= st_t K + 4096)
  \/ (exists b, In b (qall K) /\ qb_addr b <= fst iv /\ snd iv <= qb_addr b + QBATCH_SIZE).

Section DRAINF.
Variable K : rtstate.
Hypothesis WF : RTWF K.
Variables (qt qg tmp : list qbatch) (cur : list (qbatch * Z)).
Hypothesis PERM : Permutation (qt ++ qg ++ tmp ++ map fst cur) (qall K).
Hypothesis QTNE : qt <> [].
Hypothesis BG : 0 <= qc_bytes qg.
Hypothesis BT : 0 <= qc_bytes qt.
Hypothesis BB : qc_bytes qg + qc_bytes qt < 2^62.

Lemma in_K : forall b, In b (qt ++ qg ++ tmp ++ map fst cur) -> In b (qall K).
Proof. intros b Hb. eapply Permutation_in; [exact PERM| exact Hb]. Qed.
Lemma nodup_lists : List.NoDup (map qb_addr (qt ++ qg ++ tmp ++ map fst cur)).
Proof. eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact PERM| exact (nodup_qbatch_addrs K WF)]. Qed.

Definition drain_postF (ra sp gp tp t2 s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (lo : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' a4' a5' a6' a7' : word) (j0 : list byte) (m' : word -> option byte) (Wd : list (Z * Z)),
      ms' = MS (mkR ra (wz (bv_unsigned sp - 48)) gp tp t0' t1' t2 s0 s1 a0 a1 a2 a3 a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x33bf8) fc None m' (seg_rom bsegs)
      /\ QX K m' 0 0 [] (qg ++ qt) tmp cur
      /\ rw_cells bsegs m' (bv_unsigned sp - 48) (drain_frame j0 s3 s2 s1 s0 ra)
      /\ stk bsegs m' lo (bv_unsigned sp - 48) /\ mem_inv bsegs m'
      /\ munch Wd m m' /\ Forall (dwin K lo (bv_unsigned sp)) Wd /\ wmono bsegs m m'.

Theorem drain_front_ne :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) q' gL,
  qg = q' ++ [gL] ->
  QX K m 0 0 qt qg tmp cur -> mem_inv bsegs m ->
  a0 = wz A_QUAR -> a1 = wz (qcache_t K) ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 48 <= bv_unsigned sp ->
  evt bsegs (drain_postF ra sp gp tp t2 s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz AQDRAIN) fc None m (seg_rom bsegs)).
Proof.
  intros until gL. intros HQG X MI Ha0 Ha1 ST HCL LO.
  pose proof X as (CO & A4 & XA & (b2 & b3 & j4 & L1 & L2) & XH & XS & TX & TCq & LV & QR & RL1 & RL2 & RL3 & RC).
  unfold TC in TCq. unfold QH, QH4 in XH.
  pose proof (t_range K WF) as [T1 T2]. idtac.
  assert (HgL : In gL (qall K)) by (apply in_K; rewrite HQG, !in_app_iff; cbn; tauto).
  pose proof (batch_facts K WF gL HgL) as (G1 & G2 & G3 & G4 & G5).
  (* [comment removed for export] *)
  pose proof (proj1 (R_qlist_iff m qg) RL2 q' gL [] HQG) as QB. cbn [qc_first] in QB.
  apply QBC_split in QB as [LNK BX].
  (* [comment removed for export] *)
  assert (NT : 0 < zlen qt) by (pose proof (zlen_pos_ne qt QTNE); lia).
  assert (QGNE : qg <> []) by (rewrite HQG; destruct q'; discriminate).
  pose proof (zlen_pos_ne qg QGNE) as NG.
  pose proof (qc_bytes_lb qt) as LBT. pose proof (qc_bytes_lb qg) as LBG. unfold QBATCH_SIZE in LBT, LBG.
  assert (AF : forall l, (forall b, In b l -> In b (qall K)) -> 0 <= qc_first l < 2^64).
  { intros l Hl. destruct l as [|b l]; [cbn; lia|]. cbn [qc_first]. pose proof (batch_facts K WF b (Hl b ltac:(left; reflexivity))). unfold QBATCH_SIZE, KHIGHMEM_BEG, AIMG_HI, CEIL in *. lia. }
  assert (AL : forall l, (forall b, In b l -> In b (qall K)) -> 0 <= qc_last l < 2^64).
  { intros l Hl. destruct (snoc_or_nil' l) as [->|(q & b & ->)]; [cbn; lia|]. rewrite qc_last_snoc.
    pose proof (batch_facts K WF b (Hl b ltac:(apply in_or_app; right; left; reflexivity))). unfold QBATCH_SIZE, KHIGHMEM_BEG, AIMG_HI, CEIL in *. lia. }
  assert (SUBT : forall b, In b qt -> In b (qall K)) by (intros b Hb; apply in_K; rewrite !in_app_iff; tauto).
  assert (SUBG : forall b, In b qg -> In b (qall K)) by (intros b Hb; apply in_K; rewrite !in_app_iff; tauto).
  pose proof (AF qt SUBT) as F1. pose proof (AL qt SUBT) as F2. pose proof (AF qg SUBG) as F3.
  rewrite HQG in XH at 3. rewrite qc_last_snoc in XH.
  eapply evt_cut.
  { eapply (drain_a1_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              (qcache_t K) (zlen qg) (qc_first qg) (qb_addr gL) (qc_bytes qg) (zlen qt) (qc_first qt) (qc_last qt) (qc_bytes qt) lo (wz 0) b2 b3);
      [exact MI| exact Ha0| exact Ha1| lia| lia| lia| lia| lia| lia| lia| lia| lia
      | unfold qcache_t, T_QCACHE, AIMG_HI, KHIGHMEM_BEG in *; blia| idtac; unfold qcache_t, T_QCACHE, CEIL in *; lia
      | unfold AIMG_HI, KHIGHMEM_BEG in *; lia| idtac; unfold QBATCH_SIZE, CEIL in *; lia
      | unfold qcache_t, T_QCACHE, QBATCH_SIZE in *; lia
      | exact ST| idtac; lia| lia| exact L1| exact XH| exact TCq| exact LNK]. }
  cbv beta. intros ms1 (t0' & t1' & a4' & a5' & a6' & a7' & j0 & m' & -> & MU & WM & MI' & ST' & FR' & L1' & XH' & TC' & LNK').
  apply evt_done. unfold drain_postF.
  exists t0', t1', a4', a5', a6', a7', j0, m'. eexists. split; [reflexivity|].
  (* [comment removed for export] *)
  destruct (bk_used K WF gL HgL) as [UKb Eb]. set (kb := bk K gL) in *.
  assert (Hc1 : 1 <= 24) by lia.
  match type of MU with munch ?Wx _ _ => set (W := Wx) in * end.
  assert (HWU : Forall (ucz_ok K 24 kb) W).
  { subst W. unfold ucz_ok. change (csize 24) with 8192.
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold QBATCH_SIZE, CEIL in *; try lia. }
  assert (NDF : forall b0, In b0 ((qt ++ q') ++ (tmp ++ map fst cur)) -> qb_addr b0 <> qb_addr gL).
  { intros b0 Hb0. pose proof nodup_lists as ND. rewrite HQG in ND.
    replace (qt ++ (q' ++ [gL]) ++ tmp ++ map fst cur) with ((qt ++ q') ++ gL :: (tmp ++ map fst cur)) in ND
      by (rewrite <- !app_assoc; reflexivity).
    exact (nodup_map_mid qb_addr (qt ++ q') (tmp ++ map fst cur) gL b0 ND Hb0). }
  assert (BNE : forall b0, In b0 ((qt ++ q') ++ (tmp ++ map fst cur)) -> batch_ne K 24 kb b0).
  { intros b0 Hb0 [_ E]. apply (NDF b0 Hb0). rewrite E, Eb. reflexivity. }
  assert (DQ : forall a n, A_QUAR + 192 <= a \/ a + n <= A_QUAR + 152 \/ (A_QUAR + 156 <= a /\ a + n <= A_QUAR + 160) ->
               AIMG_LO <= a -> a + n <= AIMG_HI -> disjoint_from W a n).   (* [comment removed for export] *)
  { intros a n H1 H0 H2. subst W. cbn. unfold qcache_t, T_QCACHE, AIMG_LO, AIMG_HI, KHIGHMEM_BEG, QBATCH_SIZE, CEIL in *. repeat split; blia. }
  split.
  { (* [comment removed for export] *)
    split; [exact (UZ_core K WF 24 kb H24 Hc1 UKb W HWU m m' MU WM (bk_vs_avail K WF gL HgL) CO)|].
    split; [exact (UZ_alloc4' K WF 24 kb H24 Hc1 UKb W HWU m m' MU WM A4)|].
    split; [apply (UZ_QA W m m' MU WM XA); apply DQ; [lia| unfold A_QUAR, A_ALLOC, AIMG_LO; lia| unfold A_QUAR, A_ALLOC, AIMG_HI; lia]|].
    split; [exists b2, b3, j4; split; [exact L1'| eapply (rwT W m m' MU WM); [exact L2| cbn; apply DQ; [lia| unfold A_QUAR, A_ALLOC, AIMG_LO; lia| unfold A_QUAR, A_ALLOC, AIMG_HI; lia]]]|].
    split; [unfold QH, QH4; rewrite (zlen_app qg qt), (qc_first_app_l qg qt QGNE), (qc_last_app_r qg qt QTNE), (qc_bytes_app qg qt); exact XH'|].
    split; [apply (UZ_QS W m m' MU WM XS); apply DQ; [lia| unfold A_QUAR, A_ALLOC, AIMG_LO; lia| unfold A_QUAR, A_ALLOC, AIMG_HI; lia]|].
    split; [exact (UZ_threadx K WF 24 kb H24 Hc1 UKb W HWU m m' MU WM TX (tpx_ok_of_RTWF K WF))|].
    split; [exact TC'|].
    split; [apply (UZ_live' K WF 24 kb H24 Hc1 UKb W HWU m m' MU WM LV); intros A n Hin; apply (bk_vs_block K WF gL HgL); unfold all_blocks; rewrite !in_app_iff; tauto|].
    split; [apply (UZ_quar' K WF 24 kb H24 Hc1 UKb W HWU m m' MU WM QR); intros A n Hin; apply (bk_vs_block K WF gL HgL); unfold all_blocks; rewrite !in_app_iff; tauto|].
    split; [exact I|].
    split.
    { apply (proj2 (R_qlist_iff m' (qg ++ qt))). intros q1 b q2 E.
      destruct (app_mid_cases q1 q2 qg qt b (eq_sym E)) as [(r & E1 & ->)|(r & E2 & ->)].
      - rewrite HQG in E1. destruct (split_snoc1 q1 r q' b gL (eq_sym E1)) as [(-> & -> & ->)|(r' & -> & E')].
        + (* [comment removed for export] *)
          cbn [app]. apply QBC_split. split; [exact LNK'|].
          apply (QBCx_keep K WF W m m' gL MU WM HgL BX).
          subst W. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
            unfold qcache_t, T_QCACHE, A_QUAR, A_ALLOC, AIMG_HI, CEIL in *; lia.
        + (* [comment removed for export] *)
          rewrite (qc_first_app_l (r' ++ [gL]) qt ltac:(destruct r'; discriminate)).
          apply (UZ_QBC K WF 24 kb H24 Hc1 UKb W HWU m m' MU WM b).
          * apply SUBG. rewrite HQG, E'. rewrite !in_app_iff. cbn [In]. tauto.
          * apply BNE. rewrite E'. rewrite !in_app_iff. cbn [In]. tauto.
          * exact (proj1 (R_qlist_iff m qg) RL2 q1 b (r' ++ [gL]) ltac:(rewrite HQG, E', <- app_assoc; reflexivity)).
      - (* [comment removed for export] *)
        apply (UZ_QBC K WF 24 kb H24 Hc1 UKb W HWU m m' MU WM b).
        + apply SUBT. rewrite E2. apply in_or_app. right. left. reflexivity.
        + apply BNE. rewrite E2. rewrite !in_app_iff. cbn [In]. tauto.
        + exact (proj1 (R_qlist_iff m qt) RL1 r b q2 E2). }
    split; [apply (UZ_qlist' K WF 24 kb H24 Hc1 UKb W HWU m m' MU WM tmp RL3); intros b Hb; split; [apply in_K| apply BNE]; rewrite !in_app_iff; tauto|].
    apply (UZ_qcur' K WF 24 kb H24 Hc1 UKb W HWU m m' MU WM cur RC). intros bd Hbd. split; [apply in_K| apply BNE]; rewrite !in_app_iff; pose proof (in_map fst cur bd Hbd); tauto. }
  split; [exact FR'|]. split; [exact ST'|]. split; [exact MI'|]. split; [exact MU|]. split; [| exact WM].
  subst W. unfold dwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - left. lia.
  - right. left. lia.
  - right. left. lia.
  - right. right. left. unfold qcache_t, T_QCACHE. lia.
  - right. right. right. exists gL. split; [exact HgL|]. unfold QBATCH_SIZE. lia.
Qed.

Theorem drain_front_e :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  qg = [] ->
  QX K m 0 0 qt qg tmp cur -> mem_inv bsegs m ->
  a0 = wz A_QUAR -> a1 = wz (qcache_t K) ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 48 <= bv_unsigned sp ->
  evt bsegs (drain_postF ra sp gp tp t2 s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz AQDRAIN) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros HQG X MI Ha0 Ha1 ST HCL LO.
  pose proof X as (CO & A4 & XA & (b2 & b3 & j4 & L1 & L2) & XH & XS & TX & TCq & LV & QR & RL1 & RL2 & RL3 & RC).
  unfold TC in TCq. unfold QH, QH4 in XH.
  pose proof (t_range K WF) as [T1 T2]. idtac.
  destruct (snoc_or_nil' qt) as [E0|(qT & lt & HQT)]; [congruence|].
  assert (Hlt : In lt (qall K)) by (apply in_K; rewrite HQT, !in_app_iff; cbn; tauto).
  pose proof (batch_facts K WF lt Hlt) as (G1 & G2 & G3 & G4 & G5).
  (* [comment removed for export] *)
  pose proof (proj1 (R_qlist_iff m qt) RL1 qT lt [] HQT) as QB. cbn [qc_first] in QB.
  apply QBC_split in QB as [LNK BX].
  assert (NT : 0 < zlen qt) by (pose proof (zlen_pos_ne qt QTNE); lia).
  pose proof (qc_bytes_lb qt) as LBT. unfold QBATCH_SIZE in LBT.
  assert (AF : forall l, (forall b, In b l -> In b (qall K)) -> 0 <= qc_first l < 2^64).
  { intros l Hl. destruct l as [|b l]; [cbn; lia|]. cbn [qc_first]. pose proof (batch_facts K WF b (Hl b ltac:(left; reflexivity))). unfold QBATCH_SIZE, KHIGHMEM_BEG, AIMG_HI, CEIL in *. lia. }
  assert (AL : forall l, (forall b, In b l -> In b (qall K)) -> 0 <= qc_last l < 2^64).
  { intros l Hl. destruct (snoc_or_nil' l) as [->|(q & b & ->)]; [cbn; lia|]. rewrite qc_last_snoc.
    pose proof (batch_facts K WF b (Hl b ltac:(apply in_or_app; right; left; reflexivity))). unfold QBATCH_SIZE, KHIGHMEM_BEG, AIMG_HI, CEIL in *. lia. }
  assert (SUBT : forall b, In b qt -> In b (qall K)) by (intros b Hb; apply in_K; rewrite !in_app_iff; tauto).
  pose proof (AF qt SUBT) as F1. pose proof (AL qt SUBT) as F2.
  rewrite HQG in XH.
  eapply evt_cut.
  { eapply (drain_a0_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              (qcache_t K) 0 (zlen qt) (qc_first qt) (qc_last qt) (qc_bytes qt) lo b2 b3);
      [exact MI| exact Ha0| exact Ha1| lia| lia| lia| lia| lia| lia
      | unfold qcache_t, T_QCACHE, AIMG_HI, KHIGHMEM_BEG in *; blia| idtac; unfold qcache_t, T_QCACHE, CEIL in *; lia
      | exact ST| idtac; lia| lia| exact L1| exact XH| exact TCq]. }
  cbv beta. intros ms1 (t0' & t1' & a4' & a5' & a6' & a7' & j0 & m' & -> & MU & WM & MI' & ST' & FR' & L1' & XH' & TC').
  apply evt_done. unfold drain_postF.
  exists t0', t1', a4', a5', a6', a7', j0, m'. eexists. split; [reflexivity|].
  destruct (bk_used K WF lt Hlt) as [UKb Eb]. set (kb := bk K lt) in *.
  assert (Hc1 : 1 <= 24) by lia.
  match type of MU with munch ?Wx _ _ => set (W := Wx) in * end.
  assert (HWU : Forall (ucz_ok K 24 kb) W).
  { subst W. unfold ucz_ok. change (csize 24) with 8192.
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; unfold QBATCH_SIZE, CEIL in *; try lia. }
  assert (NDF : forall b0, In b0 (qT ++ (qg ++ tmp ++ map fst cur)) -> qb_addr b0 <> qb_addr lt).
  { intros b0 Hb0. pose proof nodup_lists as ND. rewrite HQT in ND.
    replace ((qT ++ [lt]) ++ qg ++ tmp ++ map fst cur) with (qT ++ lt :: (qg ++ tmp ++ map fst cur)) in ND
      by (rewrite <- !app_assoc; reflexivity).
    exact (nodup_map_mid qb_addr qT (qg ++ tmp ++ map fst cur) lt b0 ND Hb0). }
  assert (BNE : forall b0, In b0 (qT ++ (qg ++ tmp ++ map fst cur)) -> batch_ne K 24 kb b0).
  { intros b0 Hb0 [_ E]. apply (NDF b0 Hb0). rewrite E, Eb. reflexivity. }
  assert (DQ : forall a n, A_QUAR + 192 <= a \/ a + n <= A_QUAR + 152 \/ (A_QUAR + 156 <= a /\ a + n <= A_QUAR + 160) ->
               AIMG_LO <= a -> a + n <= AIMG_HI -> disjoint_from W a n).   (* [comment removed for export] *)
  { intros a n H1 H0 H2. subst W. cbn. unfold qcache_t, T_QCACHE, AIMG_LO, AIMG_HI, KHIGHMEM_BEG, QBATCH_SIZE, CEIL in *. repeat split; blia. }
  rewrite HQG. cbn [app].
  split.
  { (* [comment removed for export] *)
    split; [exact (UZ_core K WF 24 kb H24 Hc1 UKb W HWU m m' MU WM (bk_vs_avail K WF lt Hlt) CO)|].
    split; [exact (UZ_alloc4' K WF 24 kb H24 Hc1 UKb W HWU m m' MU WM A4)|].
    split; [apply (UZ_QA W m m' MU WM XA); apply DQ; [lia| unfold A_QUAR, A_ALLOC, AIMG_LO; lia| unfold A_QUAR, A_ALLOC, AIMG_HI; lia]|].
    split; [exists b2, b3, j4; split; [exact L1'| eapply (rwT W m m' MU WM); [exact L2| cbn; apply DQ; [lia| unfold A_QUAR, A_ALLOC, AIMG_LO; lia| unfold A_QUAR, A_ALLOC, AIMG_HI; lia]]]|].
    split; [unfold QH, QH4; cbn [qc_bytes fold_right Z.add] in XH'; exact XH'|].
    split; [apply (UZ_QS W m m' MU WM XS); apply DQ; [lia| unfold A_QUAR, A_ALLOC, AIMG_LO; lia| unfold A_QUAR, A_ALLOC, AIMG_HI; lia]|].
    split; [exact (UZ_threadx K WF 24 kb H24 Hc1 UKb W HWU m m' MU WM TX (tpx_ok_of_RTWF K WF))|].
    split; [exact TC'|].
    split; [apply (UZ_live' K WF 24 kb H24 Hc1 UKb W HWU m m' MU WM LV); intros A n Hin; apply (bk_vs_block K WF lt Hlt); unfold all_blocks; rewrite !in_app_iff; tauto|].
    split; [apply (UZ_quar' K WF 24 kb H24 Hc1 UKb W HWU m m' MU WM QR); intros A n Hin; apply (bk_vs_block K WF lt Hlt); unfold all_blocks; rewrite !in_app_iff; tauto|].
    split; [exact I|].
    split.
    { apply (proj2 (R_qlist_iff m' qt)). intros q1 b q2 E.
      rewrite HQT in E. destruct (split_snoc1 q1 q2 qT b lt (eq_sym E)) as [(-> & -> & ->)|(r' & -> & E')].
      - (* [comment removed for export] *)
        apply QBC_split. split.
        + eapply (rwT W m m' MU WM); [exact LNK| subst W; cbn; unfold qcache_t, T_QCACHE, A_QUAR, A_ALLOC, QBATCH_SIZE, CEIL, KHIGHMEM_BEG, AIMG_HI in *; repeat split; lia].
        + apply (QBCx_keep K WF W m m' lt MU WM Hlt BX).
          subst W. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
            unfold qcache_t, T_QCACHE, A_QUAR, A_ALLOC, AIMG_HI, CEIL in *; lia.
      - apply (UZ_QBC K WF 24 kb H24 Hc1 UKb W HWU m m' MU WM b).
        + apply SUBT. rewrite HQT, E'. rewrite !in_app_iff. cbn [In]. tauto.
        + apply BNE. rewrite E'. rewrite !in_app_iff. cbn [In]. tauto.
        + exact (proj1 (R_qlist_iff m qt) RL1 q1 b (r' ++ [lt]) ltac:(rewrite HQT, E', <- app_assoc; reflexivity)). }
    split; [apply (UZ_qlist' K WF 24 kb H24 Hc1 UKb W HWU m m' MU WM tmp RL3); intros b Hb; split; [apply in_K| apply BNE]; rewrite !in_app_iff; tauto|].
    apply (UZ_qcur' K WF 24 kb H24 Hc1 UKb W HWU m m' MU WM cur RC). intros bd Hbd. split; [apply in_K| apply BNE]; rewrite !in_app_iff; pose proof (in_map fst cur bd Hbd); tauto. }
  split; [exact FR'|]. split; [exact ST'|]. split; [exact MI'|]. split; [exact MU|]. split; [| exact WM].
  subst W. unfold dwin. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
  - left. lia.
  - right. left. lia.
  - right. left. lia.
  - right. right. left. unfold qcache_t, T_QCACHE. lia.
Qed.

Theorem drain_front_full :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
  QX K m 0 0 qt qg tmp cur -> mem_inv bsegs m ->
  a0 = wz A_QUAR -> a1 = wz (qcache_t K) ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 48 <= bv_unsigned sp ->
  evt bsegs (drain_postF ra sp gp tp t2 s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz AQDRAIN) fc None m (seg_rom bsegs)).
Proof.
  intros. destruct (snoc_or_nil' qg) as [E|(q' & gL & E)]; [eapply drain_front_e; eassumption| eapply drain_front_ne; eassumption].
Qed.
End DRAINF.


End CeilWrap.
End RTW_q_drain2.

(* [comment removed for export] *)
Module RTW_q_bz.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_apz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_lib4 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_m_live OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_q_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf2.RTW_q_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_zone RTW_q_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_lock RTW_q_car RTW_q_zone2 RTW_q_drain2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma R_qlist_app : forall m q r,
  R_qlist m (q ++ r) <-> (forall q1 b q2, q = q1 ++ b :: q2 -> QBC m b (qc_first (q2 ++ r))) /\ R_qlist m r.
Proof.
  intros m q r. rewrite !R_qlist_iff. split.
  - intros H. split.
    + intros q1 b q2 E. apply (H q1 b (q2 ++ r)). rewrite E, <- app_assoc. reflexivity.
    + intros q1 b q2 E. apply (H (q ++ q1) b q2). rewrite E, <- app_assoc. reflexivity.
  - intros [H1 H2] q1 b q2 E. destruct (app_mid_cases q1 q2 q r b (eq_sym E)) as [(s & -> & ->)|(s & -> & ->)].
    + exact (H1 q1 b s eq_refl).
    + exact (H2 s b q2 eq_refl).
Qed.
Lemma R_qlist_one : forall m b, R_qlist m [b] <-> QBC m b 0.
Proof. intros m b. cbn [R_qlist]. unfold QBC. cbn [qc_first]. tauto. Qed.
Lemma R_qlist_cons : forall m b q, R_qlist m (b :: q) <-> QBC m b (qc_first q) /\ R_qlist m q.
Proof. intros m b q. cbn [R_qlist]. unfold QBC. tauto. Qed.

Section BZ.
Variable K : rtstate.
Hypothesis WF : RTWF K.
Variable v : qbatch.
Hypothesis Hv : In v (qall K).
Variable W : list (Z * Z).
Hypothesis HW : Forall (ucz_ok K 24 (bk K v)) W.
Variables (m m' : word -> option byte).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.

Let Hc1 : 1 <= 24 := ltac:(lia).

Lemma bz_ne : forall x, qb_addr x <> qb_addr v -> batch_ne K 24 (bk K v) x.
Proof. intros x NE [_ E]. apply NE. rewrite E. symmetry. exact (proj2 (bk_used K WF v Hv)). Qed.

Theorem bzone :
     (coreC K m -> coreC K m')
  /\ (R_alloc4 K m -> R_alloc4 K m')
  /\ (R_threadx K m -> R_threadx K m')
  /\ (R_live K m -> R_live K m')
  /\ (R_quar K m -> R_quar K m')
  /\ (forall q, R_qlist m q -> (forall x, In x q -> In x (qall K) /\ qb_addr x <> qb_addr v) -> R_qlist m' q)
  /\ (forall cu, QCUR m cu -> (forall bd, In bd cu -> In (fst bd) (qall K) /\ qb_addr (fst bd) <> qb_addr v) -> QCUR m' cu)
  /\ (forall x nxt, In x (qall K) -> qb_addr x <> qb_addr v -> QBC m x nxt -> QBC m' x nxt).
Proof.
  destruct (bk_used K WF v Hv) as [UKb Eb].
  split; [exact (UZ_core K WF 24 (bk K v) H24 Hc1 UKb W HW m m' MU WM (bk_vs_avail K WF v Hv))|].
  split; [exact (UZ_alloc4' K WF 24 (bk K v) H24 Hc1 UKb W HW m m' MU WM)|].
  split; [intros TX; exact (UZ_threadx K WF 24 (bk K v) H24 Hc1 UKb W HW m m' MU WM TX (tpx_ok_of_RTWF K WF))|].
  split; [intros LV; apply (UZ_live' K WF 24 (bk K v) H24 Hc1 UKb W HW m m' MU WM LV); intros A n Hin; apply (bk_vs_block K WF v Hv); unfold all_blocks; rewrite !in_app_iff; tauto|].
  split; [intros QR; apply (UZ_quar' K WF 24 (bk K v) H24 Hc1 UKb W HW m m' MU WM QR); intros A n Hin; apply (bk_vs_block K WF v Hv); unfold all_blocks; rewrite !in_app_iff; tauto|].
  split; [intros q RL SUB; apply (UZ_qlist' K WF 24 (bk K v) H24 Hc1 UKb W HW m m' MU WM q RL); intros x Hx; destruct (SUB x Hx) as [H1 H2]; split; [exact H1| apply bz_ne; exact H2]|].
  split; [intros cu RC SUB; apply (UZ_qcur' K WF 24 (bk K v) H24 Hc1 UKb W HW m m' MU WM cu RC); intros bd Hbd; destruct (SUB bd Hbd) as [H1 H2]; split; [exact H1| apply bz_ne; exact H2]|].
  intros x nxt Hx NE QB. exact (UZ_QBC K WF 24 (bk K v) H24 Hc1 UKb W HW m m' MU WM x nxt Hx (bz_ne x NE) QB).
Qed.
End BZ.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qall_of_addr : forall K x, In (qb_addr x) (qbatch_addrs K) -> exists b0, In b0 (qall K) /\ qb_addr b0 = qb_addr x.
Proof. intros K x Ha. apply in_map_iff in Ha as (b0 & E & Hb0). exists b0. split; [exact Hb0| exact E]. Qed.

Lemma batch_facts_a : forall K x, RTWF K -> In (qb_addr x) (qbatch_addrs K) ->
  KHIGHMEM_BEG <= qb_addr x /\ qb_addr x + QBATCH_SIZE <= CEIL /\ qb_addr x mod 32 = 0
  /\ (st_t K + 4096 <= qb_addr x \/ qb_addr x + QBATCH_SIZE <= st_t K).
Proof.
  intros K x WF Ha. destruct (qall_of_addr K x Ha) as (b0 & Hb0 & E). rewrite <- E.
  pose proof (batch_facts K WF b0 Hb0) as (B1 & B2 & B3 & B4 & _). repeat split; assumption.
Qed.

Lemma QBCx_keep_a : forall K W m m' x, RTWF K -> munch W m m' -> wmono bsegs m m' ->
  In (qb_addr x) (qbatch_addrs K) -> 0 <= qb_count x <= QBATCH_CAP -> QBCx m x ->
  Forall (fun iv => CEIL <= fst iv \/ snd iv <= AIMG_HI \/ (st_t K <= fst iv /\ snd iv <= st_t K + 4096)
                    \/ (qb_addr x <= fst iv /\ snd iv <= qb_addr x + 8)) W ->
  QBCx m' x.
Proof.
  intros K W m m' x WF MU WM Ha CNT (HC & V & SL & SHD) HW.
  pose proof (batch_facts_a K x WF Ha) as (B1 & B2 & B3 & B4). pose proof (t_range K WF) as [T1 T2].
  assert (AL8 : qb_addr x mod 8 = 0) by (apply (mod0_trans _ 8 32); [lia|lia|reflexivity|exact B3]).
  pose proof (rt_SH_bounds (qb_addr x) ltac:(unfold QBATCH_SIZE, CEIL, KHIGHMEM_BEG, AIMG_HI in *; lia)) as SB1.
  pose proof (rt_SH_bounds (qb_addr x + 8192) ltac:(unfold QBATCH_SIZE, CEIL, KHIGHMEM_BEG, AIMG_HI in *; lia)) as SB2.
  pose proof (rt_SH_aligned_add (qb_addr x) 8192 AL8) as SA. change (8192 / 8) with 1024 in SA.
  assert (OBJ : forall a sz, qb_addr x + 8 <= a -> a + sz <= qb_addr x + 8192 -> disjoint_from W a sz).
  { intros a sz H1 H2. apply (disjoint_from_forallq _ W a sz HW). intros lo hi X. cbn [fst snd] in X.
    unfold QBATCH_SIZE, CEIL, AIMG_HI, KHIGHMEM_BEG in *. lia. }
  assert (SHW : disjoint_from W (SH (qb_addr x)) 1024).
  { apply (disjoint_from_forallq _ W _ _ HW). intros lo hi X. cbn [fst snd] in X.
    unfold QBATCH_SIZE, CEIL, AIMG_HI, KHIGHMEM_BEG in *. blia. }
  split; [| split; [| split]].
  - eapply (rwT W m m' MU WM); [exact HC| cbn; apply OBJ; lia].
  - eapply visT; [exact WM| exact V| unfold AIMG_HI, KHIGHMEM_BEG in *; lia].
  - intros i Hi. eapply (rwT W m m' MU WM); [exact (SL i Hi)| cbn; apply OBJ; unfold QBATCH_CAP in *; lia].
  - eapply (rwT W m m' MU WM); [exact SHD|]. unfold sh_avail. change (csize 24) with 8192. rewrite zcells_zrep_size by lia.
    change (8192 / 8) with 1024. exact SHW.
Qed.

Section BZA.
Variable K : rtstate.
Hypothesis WF : RTWF K.
Variable v : qbatch.
Hypothesis Hv : In (qb_addr v) (qbatch_addrs K).
Variable W : list (Z * Z).
Hypothesis HW : Forall (ucz_ok K 24 (bk K v)) W.
Variables (m m' : word -> option byte).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.

Theorem bzone_a :
     (coreC K m -> coreC K m')
  /\ (R_alloc4 K m -> R_alloc4 K m')
  /\ (R_threadx K m -> R_threadx K m')
  /\ (R_live K m -> R_live K m')
  /\ (R_quar K m -> R_quar K m')
  /\ (forall q, R_qlist m q -> (forall x, In x q -> In (qb_addr x) (qbatch_addrs K) /\ 0 <= qb_count x <= QBATCH_CAP /\ qb_addr x <> qb_addr v) -> R_qlist m' q)
  /\ (forall cu, QCUR m cu -> (forall bd, In bd cu -> In (qb_addr (fst bd)) (qbatch_addrs K) /\ 0 <= qb_count (fst bd) <= QBATCH_CAP /\ qb_addr (fst bd) <> qb_addr v) -> QCUR m' cu)
  /\ (forall x nxt, In (qb_addr x) (qbatch_addrs K) -> 0 <= qb_count x <= QBATCH_CAP -> qb_addr x <> qb_addr v -> QBC m x nxt -> QBC m' x nxt).
Proof.
  destruct (qall_of_addr K v Hv) as (b0 & Hb0 & Eb0).
  assert (EK : bk K v = bk K b0) by (unfold bk; rewrite Eb0; reflexivity).
  assert (HW0 : Forall (ucz_ok K 24 (bk K b0)) W) by (rewrite <- EK; exact HW).
  destruct (bzone K WF b0 Hb0 W HW0 m m' MU WM) as (Z1 & Z2 & Z3 & Z4 & Z5 & _ & _ & _).
  destruct (bk_used K WF b0 Hb0) as [UKb Eb]. assert (Hc1 : 1 <= 24) by lia.
  assert (BNE : forall x, qb_addr x <> qb_addr v -> batch_ne K 24 (bk K b0) x).
  { intros x NE [_ E]. apply NE. rewrite E, <- Eb0. symmetry. exact Eb. }
  split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|]. split; [exact Z4|]. split; [exact Z5|].
  split; [intros q RL SUB; apply (UZ_qlist_a K WF 24 (bk K b0) H24 Hc1 UKb W HW0 m m' MU WM q RL); intros x Hx; destruct (SUB x Hx) as (A1 & A2 & A3); split; [exact A1| split; [exact A2| apply BNE; exact A3]]|].
  split; [intros cu RC SUB; apply (UZ_qcur_a K WF 24 (bk K b0) H24 Hc1 UKb W HW0 m m' MU WM cu RC); intros bd Hbd; destruct (SUB bd Hbd) as (A1 & A2 & A3); split; [exact A1| split; [exact A2| apply BNE; exact A3]]|].
  intros x nxt Hx CNT NE QB. exact (UZ_QBC_a K WF 24 (bk K b0) H24 Hc1 UKb W HW0 m m' MU WM x nxt Hx CNT (BNE x NE) QB).
Qed.
End BZA.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition curpart (cur : list (qbatch * Z)) : list (Z * Z) :=
  flat_map (fun bd : qbatch * Z => skipn (Z.to_nat (snd bd)) (qb_elems (fst bd))) cur.
Definition ainv (K : rtstate) (qt : list qbatch) (cur : list (qbatch * Z)) (qg tmp : list qbatch) : Prop :=
     Permutation (map qb_addr (qt ++ qg ++ tmp ++ map fst cur)) (qbatch_addrs K)
  /\ (forall b, In b (qt ++ qg ++ tmp ++ map fst cur) -> qb_count b <= QBATCH_CAP)
  /\ Permutation (flat_map qb_elems (qt ++ qg ++ tmp) ++ curpart cur) (qelems K)
  /\ qc_bytes qg + qc_bytes tmp < 2^61.

Lemma qb_count_nonneg : forall b, 0 <= qb_count b.
Proof. intros b. unfold qb_count. lia. Qed.

Section AINV.
Variable K : rtstate.
Hypothesis WF : RTWF K.
Variables (qt : list qbatch) (cur : list (qbatch * Z)).

Lemma ainv_addr : forall qg tmp b, ainv K qt cur qg tmp -> In b (qt ++ qg ++ tmp ++ map fst cur) -> In (qb_addr b) (qbatch_addrs K).
Proof. intros qg tmp b (P & _) Hb. eapply Permutation_in; [exact P|]. apply in_map. exact Hb. Qed.
Lemma ainv_cnt : forall qg tmp b, ainv K qt cur qg tmp -> In b (qt ++ qg ++ tmp ++ map fst cur) -> 0 <= qb_count b <= QBATCH_CAP.
Proof. intros qg tmp b (_ & C & _) Hb. split; [apply qb_count_nonneg| exact (C b Hb)]. Qed.
Lemma ainv_nodup : forall qg tmp, ainv K qt cur qg tmp -> List.NoDup (map qb_addr (qt ++ qg ++ tmp ++ map fst cur)).
Proof. intros qg tmp (P & _). eapply Permutation_NoDup; [apply Permutation_sym; exact P| exact (nodup_qbatch_addrs K WF)]. Qed.

Lemma ainv_elems : forall qg tmp e, ainv K qt cur qg tmp -> In e (flat_map qb_elems (qt ++ qg ++ tmp)) -> In e (qelems K).
Proof. intros qg tmp e (_ & _ & P & _) He. eapply Permutation_in; [exact P|]. apply in_or_app. left. exact He. Qed.

Lemma ainv_of_perm : forall qg tmp, st_qcur K = [] -> cur = [] -> Permutation (qt ++ qg ++ tmp ++ map fst cur) (qall K) ->
  qc_bytes qg + qc_bytes tmp < 2^61 -> ainv K qt cur qg tmp.
Proof.
  intros qg tmp HC HC' P B. split; [apply Permutation_map; exact P|]. split; [| split; [| exact B]].
  - intros b Hb. exact (proj1 (wq_batch K (wf_quar_ok K WF) b (Permutation_in _ P Hb))).
  - unfold qelems, curpart. rewrite HC, HC'. cbn [flat_map map]. rewrite !app_nil_r.
    apply Permutation_flat_map'. unfold qall in P. rewrite HC, HC' in P. cbn [map] in P. rewrite !app_nil_r in P. exact P.
Qed.
End AINV.

Lemma bk_used_a : forall K v, RTWF K -> In (qb_addr v) (qbatch_addrs K) ->
  In (bk K v) (used_cptrs K 24) /\ qb_addr v = cptr_addr K 24 (bk K v).
Proof.
  intros K v WF Ha. destruct (qall_of_addr K v Ha) as (b0 & Hb0 & E).
  replace (bk K v) with (bk K b0) by (unfold bk; rewrite E; reflexivity). rewrite <- E. exact (bk_used K WF b0 Hb0).
Qed.

Lemma batch_disj : forall K a1 a2, RTWF K -> In a1 (qbatch_addrs K) -> In a2 (qbatch_addrs K) -> a1 <> a2 ->
  a1 + QBATCH_SIZE <= a2 \/ a2 + QBATCH_SIZE <= a1.
Proof.
  intros K a1 a2 WF H1 H2 NE.
  apply in_map_iff in H1 as (b1 & <- & Hb1). apply in_map_iff in H2 as (b2 & <- & Hb2).
  destruct (bk_used K WF b1 Hb1) as [UK1 E1].
  pose proof (used_vs_batch K WF 24 (bk K b1) H24 ltac:(lia) UK1 b2 Hb2) as D.
  rewrite <- E1 in D. change (csize 24) with QBATCH_SIZE in D.
  assert (BN : batch_ne K 24 (bk K b1) b2) by (intros [_ E]; apply NE; rewrite E, E1; reflexivity).
  specialize (D BN). lia.
Qed.

Lemma ainv_pop : forall K qt cur b rest tmp, ainv K qt cur (b :: rest) tmp -> ainv K qt cur rest (tmp ++ [b]).
Proof.
  intros K qt cur b rest tmp (P & C & E & B).
  assert (PL : Permutation (qt ++ rest ++ (tmp ++ [b]) ++ map fst cur) (qt ++ (b :: rest) ++ tmp ++ map fst cur)).
  { apply Permutation_app_head. rewrite <- !app_assoc. cbn [app].
    replace (rest ++ tmp ++ b :: map fst cur) with ((rest ++ tmp) ++ b :: map fst cur) by (rewrite <- app_assoc; reflexivity).
    replace (rest ++ tmp ++ map fst cur) with ((rest ++ tmp) ++ map fst cur) by (rewrite <- app_assoc; reflexivity).
    apply Permutation_sym. apply Permutation_middle. }
  split; [eapply Permutation_trans; [apply Permutation_map; exact PL| exact P]|].
  split; [intros x Hx; apply C; eapply Permutation_in; [exact PL| exact Hx]|].
  split.
  - eapply Permutation_trans; [| exact E]. apply Permutation_app_tail.
    rewrite !flat_map_app. cbn [flat_map]. rewrite app_nil_r. apply Permutation_app_head. rewrite <- !app_assoc.
    rewrite (app_assoc (flat_map qb_elems rest) (flat_map qb_elems tmp) (qb_elems b)). apply Permutation_app_comm.
  - rewrite (qc_bytes_app tmp [b]). rewrite (qc_bytes_cons b rest) in B. cbn [qc_bytes fold_right] in *. lia.
Qed.


End CeilWrap.
End RTW_q_bz.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep CJ_iface RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_pop.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_pop.RT_artP.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_dstateP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RT_trans.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_dstateP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_q_trans.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_wf2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_wf2.RTW_q_wf.
Import RTW_q_drain2.
Import RTW_q_bz.
Import RTW_q_car.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition esum (l : list (Z * Z)) : Z := fold_right (fun e acc => Z.max (snd e) 1 + acc) 0 l.

Lemma esum_cons : forall e l, esum (e :: l) = Z.max (snd e) 1 + esum l.
Proof. intros. reflexivity. Qed.
Lemma esum_app : forall l l', esum (l ++ l') = esum l + esum l'.
Proof.
  induction l as [|e l IH]; intros l'; [reflexivity|].
  change ((e :: l) ++ l') with (e :: (l ++ l')). rewrite !esum_cons, IH. lia.
Qed.
Lemma esum_perm : forall l l', Permutation l l' -> esum l = esum l'.
Proof. intros l l' P. induction P; [reflexivity| rewrite !esum_cons; lia| rewrite !esum_cons; lia| lia]. Qed.

Lemma qb_size_esum : forall b, qb_size b = QBATCH_SIZE + esum (qb_elems b).
Proof. intros. reflexivity. Qed.
Lemma qc_bytes_esum : forall l, qc_bytes l = QBATCH_SIZE * zlen l + esum (flat_map qb_elems l).
Proof.
  induction l as [|b l IH]; [unfold zlen; cbn; lia|].
  rewrite qc_bytes_cons, zlen_cons. cbn [flat_map]. rewrite esum_app, IH, qb_size_esum. lia.
Qed.


(* [comment removed for export] *)
Lemma ainv_bytes : forall K qt qg tmp, st_qcur K = [] -> ainv K qt [] qg tmp ->
  qc_bytes qt + qc_bytes qg + qc_bytes tmp = qc_bytes (st_qthread K ++ st_qglobal K ++ st_qtmp K).
Proof.
  intros K qt qg tmp HC (P & _ & E & _).
  cbn [map] in P. rewrite app_nil_r in P. unfold curpart in E. cbn [flat_map] in E. rewrite app_nil_r in E.
  unfold qbatch_addrs, qall in P. rewrite HC in P. cbn [map] in P. rewrite app_nil_r in P.
  unfold qelems in E. rewrite HC in E. cbn [flat_map] in E. rewrite app_nil_r in E.
  replace (qc_bytes qt + qc_bytes qg + qc_bytes tmp) with (qc_bytes (qt ++ qg ++ tmp)) by (rewrite !qc_bytes_app; lia).
  rewrite !qc_bytes_esum.
  pose proof (Permutation_length P) as L. rewrite !length_map in L.
  rewrite (esum_perm _ _ E). unfold zlen. rewrite L. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section LISTS.
Variable K : rtstate.
Hypothesis WF : RTWF K.
Hypothesis KT : st_qthread K = [].
Hypothesis KG : st_qglobal K = [].
Hypothesis KC : st_qcur K = [].
Variables (qg tmp : list qbatch).
Hypothesis AI : ainv K [] [] qg tmp.

Definition sL : rtstate := q_set K [] qg (st_apend K) (st_qpend K) tmp [].

Lemma sL_fields : st_qthread sL = [] /\ st_qglobal sL = qg /\ st_apend sL = st_apend K /\ st_qpend sL = st_qpend K
  /\ st_qtmp sL = tmp /\ st_qcur sL = [].
Proof. unfold sL. apply q_set_fields. Qed.

Lemma sL_qelems : Permutation (qelems sL) (qelems K).
Proof.
  unfold sL. rewrite qelems_q_set. pose proof AI as (_ & _ & E & _). unfold curpart in E. exact E.
Qed.

Lemma sL_addrs : Permutation (map qb_addr (qall sL)) (qbatch_addrs K).
Proof. unfold sL. rewrite qall_q_set. pose proof AI as (P & _). exact P. Qed.

Lemma sL_bytes : qc_bytes qg + qc_bytes tmp = qc_bytes (st_qtmp K).
Proof.
  pose proof (ainv_bytes K [] qg tmp KC AI) as E. rewrite KT, KG in E. cbn [app] in E. change (qc_bytes []) with 0 in E. lia.
Qed.

(* [comment removed for export] *)
Lemma used_cptrs_q_set : forall st qt' qg' ap qp tmp' cur c,
  used_cptrs (q_set st qt' qg' ap qp tmp' cur) c
  = avail_cptrs st c ++ live_cptrs st c
    ++ map (fun b => b_cptr st (fst b) (snd b)) (List.filter (cf c) (qelems (q_set st qt' qg' ap qp tmp' cur)))
    ++ map (fun b => b_cptr st (fst b) (snd b)) (List.filter (cf c) qp)
    ++ (if c =? 24 then map (fun a => (a - rbeg st 24) / 16) (map qb_addr (qt' ++ qg' ++ tmp' ++ map fst cur)) else [])
    ++ map snd (List.filter (fun ck => fst ck =? c) ap).
Proof. intros. destruct st. reflexivity. Qed.

Theorem RTWFq_lists : RTWFq sL.
Proof.
  pose proof (wf_quar_ok K WF) as WQ.
  unfold sL. eapply (RTWFq_qstep K [] qg (st_apend K) (st_qpend K) tmp [] (RTWFq_of K WF)) with (gone := []).
  - intros c Hc. rewrite used_cptrs_q_set, used_cptrs_eq.
    apply Permutation_app_head. apply Permutation_app_head. apply Permutation_app.
    + apply Permutation_map. apply Permutation_filter'. fold sL. pose proof sL_qelems as PE.
      first [exact PE| apply Permutation_sym; exact PE].
    + apply Permutation_app_head. apply Permutation_app_tail. destruct (c =? 24); [| apply Permutation_refl].
      apply Permutation_map. pose proof sL_addrs as PA. unfold sL in PA. rewrite qall_q_set in PA. unfold qbatch_addrs in PA.
      first [exact PA| apply Permutation_sym; exact PA].
  - cbn [app]. rewrite all_blocks_q_set, all_blocks_eq. apply Permutation_app_head. apply Permutation_app_tail.
    apply Permutation_sym. fold sL. exact sL_qelems.
  - constructor.
  - intros b Hb. rewrite qall_q_set in Hb. cbn [map] in Hb. rewrite app_nil_r in Hb. cbn [app] in Hb.
    assert (Hb' : In b ([] ++ qg ++ tmp ++ map fst (@nil (qbatch * Z)))) by (cbn [map]; rewrite app_nil_r; exact Hb).
    split; [exact (proj2 (ainv_cnt K [] [] qg tmp b AI Hb'))|].
    destruct (qall_of_addr K b (ainv_addr K [] [] qg tmp b AI Hb')) as (b0 & Hb0 & E0).
    destruct (wq_batch K WQ b0 Hb0) as [_ (k & Hk & Ek)]. exists k. split; [exact Hk| rewrite <- E0; exact Ek].
  - intros b Hb. destruct Hb.
  - intros bd Hbd. destruct Hbd.
  - exact (wq_apend K WQ).
  - cbn [map qc_bytes fold_right]. pose proof (wq_rec_max K WQ) as R. rewrite KG, KC in R. cbn [map qc_bytes fold_right] in R.
    fold sL in *. pose proof sL_bytes. unfold QREC_MAX. lia.
  - exact (wq_inflight K WQ).
Qed.

Theorem RTWF_lists : qc_bytes qg <= QUAR_MAX_SIZE -> RTWF sL.
Proof.
  intros HB. apply RTWF_ofq; [exact RTWFq_lists| |].
  - rewrite (proj1 sL_fields). cbn. unfold QUAR_MAX_CACHE. lia.
  - rewrite (proj1 (proj2 sL_fields)). exact HB.
Qed.

Theorem rt_prov_lists : rt_prov sL = rt_prov K.
Proof.
  pose proof (rt_prov_q_set K [] qg (st_apend K) (st_qpend K) tmp []) as E. cbn zeta in E. fold sL in E.
  rewrite E.
  - unfold prov_nb, prov_q. rewrite KT, (proj1 sL_fields). cbn. lia.
  - apply Permutation_app_tail. apply Permutation_sym. exact sL_qelems.
Qed.

(* [comment removed for export] *)
Lemma RTMODEL_lists : forall mo, RTMODEL K mo -> RTMODEL sL mo.
Proof. intros mo H. unfold sL. apply RTMODEL_q_set. exact H. Qed.
Lemma GWIN_lists : forall m mo g, GWIN K m mo g -> GWIN sL m mo g.
Proof. intros m mo g H. unfold sL. apply GWIN_q_set. exact H. Qed.
Lemma SWIN_lists : forall g, SWIN K g -> SWIN sL g.
Proof. intros g H. unfold sL. apply SWIN_q_set. exact H. Qed.
End LISTS.


End CeilWrap.
