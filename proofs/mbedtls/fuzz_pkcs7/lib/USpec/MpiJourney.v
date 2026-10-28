(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_mpi_free U_mpi_addsub.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Export MpiOpnd.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MpiJourney () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "J.XJ"; "Corelib.Init.Logic.and"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.block_range"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blocks_apart"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.MOK"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_limbs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_pres"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_ivs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "stdpp.bitvector.definitions.Z_to_bv"; "J.FB"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Nat.mul"; "Corelib.Lists.ListDef.firstn"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Corelib.Lists.ListDef.skipn"; "J.XD"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.mpi_binop_post"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "J.BJ"].


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mpd_out_trans : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "PLB,(0.$1.)PdX,$2.PLB1,(0.$1.)Pd1,$2.PLB2,(0.$1.)Pd2,$2.P,(3.R6.R5.R4.R3.)P,(3.R5.R4.R3.R2.)P,Pb,$1.P,(4.$1.R1.(5.R6.))(6.(4.$1.R2.(5.R9.))(7.(4.$1.R2.R:.)))P,Pb,$1.P,(4.$1.R1.(5.R9.))(4.$1.R2.R;.)(3.R:.R9.R6.R5.)")
(* [comment removed for export] *).
Proof.
  intros LB dX LB1 d1 LB2 d2 (A1 & O1 & S1 & K1 & E1) (A2 & O2 & S2 & K2 & E2) FR XIN.
  unfold mpd_out. split; [congruence|]. split; [exact O2|]. split; [| split].
  - intros b Hb. destruct (S2 b Hb) as [H|H]; [| right; exact H].
    destruct (S1 b H) as [H'|H']; [left; exact H'|]. right. rewrite (E2 b H' Hb). exact H'.
  - intros b Hb NX. apply K2; [exact (K1 b Hb NX)|]. intros H1. destruct (FR b H1) as [C|C]; [exact (NX C)| exact (C Hb)].
  - intros b HbX Hb2.
    assert (SG : forall d b', In b (mpd_blk d) -> In b' (mpd_blk d) -> mpd_blk d = [b]).
    { intros d b' H _. unfold mpd_blk in *. destruct (md_own d); try (destruct H; fail). destruct H as [<-|[]]. reflexivity. }
    destruct (S2 b Hb2) as [H1|H2].
    + pose proof (E1 b HbX H1) as EQ1. assert (Hb1 : In b (mpd_blk d1)) by (rewrite EQ1; exact HbX).
      rewrite (E2 b Hb1 Hb2). exact EQ1.
    + rewrite (SG d2 b H2 H2), (SG dX b HbX HbX). reflexivity.
Qed.


Definition blk_eq_dec (x y : blk) : {x = y} + {x <> y}.
Proof. decide equality; apply Z.eq_dec. Defined.

(* [comment removed for export] *)
Section J.
  Variable segs : list Segment.
  Variable L : heap_layout.
  Variable HI : heap_iface segs L.
  (* [comment removed for export] *)
  Variables (h : HST segs L HI) (LB : list blk) (m : mem) (mo : Model) (dX : mpd) (sp : word) (lo FS : Z) (FRAME : list cell).
  Let SP := bv_unsigned sp.

  (* [comment removed for export] *)
  Record JC : Prop := {
    jc_HLS : 0 <= hl_stack L;
    jc_SW : forall a, hl_static L a -> hl_written L a;
    jc_DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L;
    jc_HND : forall h LB m mo, HEAP segs L HI h LB m mo -> List.NoDup (map fst LB);
    jc_ROIMG : forall a, ro_addr segs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L;
    jc_DHI : hl_data_hi L <= alloc_ceiling;
    jc_HH : HEAP segs L HI h LB m mo;
    jc_MX : mpd_at segs m LB dX;
    jc_NST : md_own dX <> LStatic;
    jc_XW : mpd_writable L LB SP (heap_top segs L HI h) dX;
    jc_XLS : md_own dX <> LNull -> md_p dX + 4 * md_n dX <= lo \/ SP <= md_p dX;
    jc_ACL : alloc_ceiling <= lo;
    jc_FS0 : 0 <= FS;
    jc_SLO : lo <= SP - FS - 16 - hl_stack L;
    jc_HTOP : SP <= heap_top segs L HI h;
    jc_FSZ : Z.of_nat (cells_size FRAME) = FS }.
  Hypothesis JCX : JC.
  Local Ltac jc_open := pose proof JCX as [HLS SW DIMG HND ROIMG DHI HH MX NST XW XLS ACL FS0 SLO HTOP FSZ].

  (* [comment removed for export] *)
  Record XJ (EX : list blk) (hc : HST segs L HI) (LBc : list blk) (mc : mem) (moc : Model) (dXc : mpd) : Prop := {
    xj_mi : mem_inv segs mc;
    xj_stk : stk segs mc lo (SP - FS);
    xj_fr : rw_cells segs mc (SP - FS) FRAME;
    xj_heap : HEAP segs L HI hc (EX ++ LBc) mc moc;
    xj_top : heap_top segs L HI hc = heap_top segs L HI h;
    xj_mf : mo_frame mo moc;
    xj_sok : statics_ok segs L mc;
    xj_X : mpd_at segs mc LBc dXc;
    xj_addr : md_addr dXc = md_addr dX;
    xj_pad : md_pad dXc = md_pad dX;
    xj_nst : md_own dXc <> LStatic;
    xj_out : mpd_out LB dX LBc dXc;
    xj_fresh : forall b, In b (mpd_blk dXc) -> In b (mpd_blk dX) \/ ~ In b LB;
    xj_presx : heap_presx segs L LB SP (mpd_ivs dX) m mc;
    (* [comment removed for export] *)
    xj_XP : md_own dXc = LHeap -> md_addr dX + 16 <= md_p dXc \/ md_p dXc + 4 * md_n dXc <= md_addr dX;
    (* [comment removed for export] *)
    xj_nmono : md_n dX <= md_n dXc
  }.

  (* [comment removed for export] *)
  #[using="JCX"] Lemma xj_facts : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "PEX,(0.$1.)Phc,(8.Vsegs,VL,VHI,)PLBc,(0.$1.)Pmc,P,(9.&40.)(:.(9.&8.))Pmoc,$;.PdXc,$2.P,(<.R6.R5.R4.R3.R2.R1.)(=.(>.(?.$10.$10.)Lb,(?.$10.$10.)(11.VL,(12.$10.$10.R1.)(13.$10.$10.R1.))(14.$1.R7.R5.))(=.(15.(14.$1.R7.R5.))(=.(16.$10.(17.(?.$10.$10.)$10.(12.$10.$10.)(14.$1.R7.R5.)))(=.(18.R3.)(=.(6.(19.(1:.(1;.VdX,)+10.)Vlo,)(19.VSP,(1;.VdX,)))(=.(1<.=(1;.VdX,))(=.(19.(1:.(1;.VdX,)+10.)(1=.+2.+40.))(=.(1>.$10.(1?.(1;.VdX,)+8.)=)(=.(1>.$10.(20.(21.(9.&40.)(22.R2.)))(23.R2.))(=.(=.(19.=(23.R2.))(19.(23.R2.)+2710.))(=.P,(1>.$24.(25.R2.)$26.)(=.(1>.$10.(27.R3.)=)(1>.$10.(23.R3.)=))P,(7.(1>.$24.(25.R2.)$26.))(=.(1>.$24.(25.R3.)$28.)(=.(19.+1.(23.R3.))(=.(4.(?.$10.$10.)(29.$10.$10.(27.R3.)(2:.+4.(23.R3.)))R6.)(=.(1>.$10.(1?.(27.R3.)+10.)=)(=.(2;.Vsegs,R5.(27.R3.)(22.R3.))(=.(1<.=(27.R3.))(=.(19.(1:.(27.R3.)(2:.+4.(23.R3.)))(2<.VL,))(6.(19.(1:.(27.R3.)(2:.+4.(23.R3.)))(2=.VL,))(19.(2>.VL,)(27.R3.)))))))))))))))))))))")
(* [comment removed for export] *).
  Proof.
    jc_open.
    intros EX hc LBc mc moc dXc J. pose proof (heap_blocks _ _ HI _ _ _ _ (xj_heap _ _ _ _ _ _ J)) as [HBR HAP].
    pose proof (heap_blocks _ _ HI _ _ _ _ HH) as [HBR0 _].
    split; [exact HBR|]. split; [exact HAP|]. split; [exact (HND _ _ _ _ (xj_heap _ _ _ _ _ _ J))|]. split; [exact (heap_mok _ _ HI _ _ _ _ (xj_heap _ _ _ _ _ _ J))|].
    destruct XW as (XCW & XD & XP).
    split; [exact (client_wrange_where L _ _ _ (md_addr dX) 16 lo XCW ltac:(lia) HBR0 DHI ACL ltac:(lia))|].
    pose proof (xj_X _ _ _ _ _ _ J) as [(CX & XAL & X0 & LEN & NR & OWN) SG]. rewrite (xj_addr _ _ _ _ _ _ J) in *.
    pose proof (rw_cells_bound _ _ _ _ CX) as XB. unfold mpi_cells in XB. cbn [cells_size csize Nat.add] in XB.
    unfold MPI_MAX_LIMBS in NR.
    split; [exact X0|]. split; [lia|]. split; [exact XAL|]. split; [exact LEN|]. split; [exact NR|].
    split; [intros EO; rewrite EO in OWN; exact OWN|].
    intros NN. pose proof (xj_nst _ _ _ _ _ _ J) as NS. destruct (md_own dXc); [exfalso; exact (NN eq_refl)| | exfalso; exact (NS eq_refl)].
    destruct OWN as (O1 & O2 & O3 & O4). assert (O2' : In (md_p dXc, 4 * md_n dXc) (EX ++ LBc)) by (apply in_or_app; right; exact O2).
    pose proof (proj1 (Forall_forall _ _) HBR _ O2') as (R0 & R1 & R2 & R3 & R4). cbn in R0, R1, R2, R3, R4.
    split; [reflexivity|]. split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [exact O4|]. lia.
  Qed.


  (* [comment removed for export] *)
  #[using="JCX"] Lemma xj_cwX : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "PEX,(0.$1.)Phc,(8.Vsegs,VL,VHI,)PLBc,(0.$1.)Pmc,P,(9.&40.)(:.(9.&8.))Pmoc,$;.PdXc,$2.P,(<.R6.R5.R4.R3.R2.R1.)(2?.VL,R5.VSP,(30.Vsegs,VL,VHI,Vh,)(1;.VdX,)+10.)")
(* [comment removed for export] *).
  Proof.
    jc_open.
    intros EX hc LBc mc moc dXc J a Ha. destruct XW as (XCW & XD & XP).
    destruct (XCW a Ha) as [C|[C|(b & Hb & R)]]; [left; exact C| right; left; exact C| right; right].
    exists b. split; [| exact R]. apply (proj1 (proj2 (proj2 (proj2 (xj_out _ _ _ _ _ _ J))))); [exact Hb|].
    intros HbX. unfold mpd_blk in HbX. destruct (md_own dX) eqn:EO; try (destruct HbX; fail).
    destruct HbX as [<-|[]]. cbn in R. pose proof (XP eq_refl). lia.
  Qed.

  #[using="JCX"] Lemma xj_crX : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "PEX,(0.$1.)Phc,(8.Vsegs,VL,VHI,)PLBc,(0.$1.)Pmc,P,(9.&40.)(:.(9.&8.))Pmoc,$;.PdXc,$2.PSP',$10.P,(<.R7.R6.R5.R4.R3.R2.)P,(19.R2.VSP,)(31.VL,(14.$1.R9.R7.)R3.(1;.VdX,)+10.)")
(* [comment removed for export] *).
  Proof.
    jc_open.
    intros EX hc LBc mc moc dXc SP' J LE a Ha. destruct (xj_cwX _ _ _ _ _ _ J a Ha) as [C|[C|(b & Hb & R)]]; [left; lia| right; left; exact C| right; right].
    exists b. split; [apply in_or_app; right; exact Hb| exact R].
  Qed.

  (* [comment removed for export] *)
  #[using="JCX"] Lemma xj_presx_step : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "PEX,(0.$1.)Phc,(8.Vsegs,VL,VHI,)PLBc,(0.$1.)Pmc,P,(9.&40.)(:.(9.&8.))Pmoc,$;.PdXc,$2.PLBn,(0.$1.)PSPn,$10.Pm2,P,(9.&40.)(:.(9.&8.))P,(<.R9.R8.R7.R6.R5.R4.)P,(32.Vsegs,VL,R4.R3.R7.R2.)P,Pb,$1.P,(4.$1.R1.R:.)(4.$1.R2.R7.)P,(19.R5.VSP,)(33.Vsegs,VL,VLB,VSP,(34.VdX,)Vm,R5.)")
(* [comment removed for export] *).
  Proof.
    jc_open.
    intros EX hc LBc mc moc dXc LBn SPn m2 J HP SUB LE. eapply heap_presx_trans; [exact (xj_presx _ _ _ _ _ _ J)|].
    intros a Ha Hc Ho. apply HP; [exact Ha|].
    destruct Hc as [C|[C|(b & Hb & R)]]; [left; lia| right; left; exact C| right; right].
    exists b. split; [| exact R]. apply SUB. apply (proj1 (proj2 (proj2 (proj2 (xj_out _ _ _ _ _ _ J))))); [exact Hb|].
    intros HbX. unfold mpd_blk in HbX. unfold mpd_ivs in Ho. destruct (md_own dX) eqn:EO; try (destruct HbX; fail).
    destruct HbX as [<-|[]]. cbn in R, Ho. lia.
  Qed.

  #[using="JCX"] Lemma xj_presx_stepx : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "PEX,(0.$1.)Phc,(8.Vsegs,VL,VHI,)PLBc,(0.$1.)Pmc,P,(9.&40.)(:.(9.&8.))Pmoc,$;.PdXc,$2.PLBn,(0.$1.)PSPn,$10.PXI,(0.$35.)Pm2,P,(9.&40.)(:.(9.&8.))P,(<.R:.R9.R8.R7.R6.R5.)P,(33.Vsegs,VL,R5.R4.R3.R8.R2.)P,Pb,$1.P,(4.$1.R1.R;.)(4.$1.R2.R8.)P,(19.R6.VSP,)P,Pa,$10.P,(36.(34.VdX,)R1.)P,(37.VL,VLB,VSP,R2.)(36.R9.R3.)(33.Vsegs,VL,VLB,VSP,(34.VdX,)Vm,R6.)")
(* [comment removed for export] *).
  Proof.
    jc_open.
    intros EX hc LBc mc moc dXc LBn SPn XI m2 J HP SUB LE HXI. eapply heap_presx_trans; [exact (xj_presx _ _ _ _ _ _ J)|].
    intros a Ha Hc Ho. apply HP; [exact Ha| | exact (HXI a Ho Hc)].
    destruct Hc as [C|[C|(b & Hb & R)]]; [left; lia| right; left; exact C| right; right].
    exists b. split; [| exact R]. apply SUB. apply (proj1 (proj2 (proj2 (proj2 (xj_out _ _ _ _ _ _ J))))); [exact Hb|].
    intros HbX. unfold mpd_blk in HbX. unfold mpd_ivs in Ho. destruct (md_own dX) eqn:EO; try (destruct HbX; fail).
    destruct HbX as [<-|[]]. cbn in R, Ho. lia.
  Qed.

  #[using="JCX"] Lemma xj_blocks_orig : forall EX hc LBc mc moc dXc b, XJ EX hc LBc mc moc dXc -> In b LB -> In b LBc \/ In b (mpd_blk dX).
  Proof.
    jc_open.
    intros EX hc LBc mc moc dXc b J Hb. pose proof (proj1 (proj2 (proj2 (proj2 (xj_out _ _ _ _ _ _ J))))) as O4.
    unfold mpd_blk in *. destruct (md_own dX); [left| | left].
    1,3: apply O4; [exact Hb| intros []].
    destruct b as [q k]. destruct (Z.eq_dec q (md_p dX)) as [->|NE].
    - destruct (Z.eq_dec k (4 * md_n dX)) as [->|NK]; [right; left; reflexivity|].
      left. apply O4; [exact Hb|]. intros [E|[]]. injection E. lia.
    - left. apply O4; [exact Hb|]. intros [E|[]]. injection E. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="JCX"] Lemma xj_not_limbs : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "PEX,(0.$1.)Phc,(8.Vsegs,VL,VHI,)PLBc,(0.$1.)Pmc,P,(9.&40.)(:.(9.&8.))Pmoc,$;.PdXc,$2.Pa,$10.P,(<.R7.R6.R5.R4.R3.R2.)P,(37.VL,VLB,VSP,R2.)P,(36.(34.VdX,)R3.)P,(1>.$24.(25.R5.)$28.)(7.(=.(19.(27.R6.)R5.)(1<.R5.(1:.(27.R6.)(2:.+4.(23.R6.))))))")
(* [comment removed for export] *).
  Proof.
    jc_open.
    intros EX hc LBc mc moc dXc a J Hc Ho EO R.
    pose proof (xj_facts _ _ _ _ _ _ J) as (HBR1 & HAP1 & ND1 & _ & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1).
    destruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & XIN & _ & _ & P0 & PC & PI).
    destruct Hc as [C|[[C1 C2]|(b & Hb & Rb)]]; [lia| lia|].
    unfold mpd_ivs in Ho. cbn in Ho. destruct Ho as [Ho1 Ho2].
    destruct (xj_blocks_orig _ _ _ _ _ _ _ J Hb) as [HbC|HbX].
    - destruct b as [q k]. cbn in Rb.
      destruct (blk_eq_dec (q, k) (md_p dXc, 4 * md_n dXc)) as [E|NE].
      + injection E as -> ->.
        destruct (xj_fresh _ _ _ _ _ _ J (md_p dXc, 4 * md_n dXc) ltac:(unfold mpd_blk; rewrite EO; left; reflexivity)) as [HX|HN].
        * unfold mpd_blk in HX. destruct (md_own dX); try (destruct HX; fail). destruct HX as [E|[]]. injection E as E1 E2. cbn in Ho2. lia.
        * exact (HN Hb).
      + pose proof (blocks_apart_neq (EX ++ LBc) (q, k) (md_p dXc, 4 * md_n dXc) HAP1 ltac:(apply in_or_app; right; exact HbC) ltac:(apply in_or_app; right; exact XIN) NE) as D.
        cbn in D. pose proof (proj1 (Forall_forall _ _) HBR1 _ ltac:(apply in_or_app; right; exact HbC)) as (_ & _ & R2 & _). cbn in R2. lia.
    - unfold mpd_blk in HbX. destruct (md_own dX); try (destruct HbX; fail). destruct HbX as [<-|[]]. cbn in Rb, Ho2. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="JCX"] Lemma xj_transport : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "PEX,(0.$1.)PEX2,(0.$1.)Phc,(8.Vsegs,VL,VHI,)PLBc,(0.$1.)Pmc,P,(9.&40.)(:.(9.&8.))Pmoc,$;.PdXc,$2.Pm2,P,(9.&40.)(:.(9.&8.))Pmo2,$;.Ph2,(8.Vsegs,VL,VHI,)P,(<.R:.R8.R7.R6.R5.R4.)P,(38.Vsegs,R4.)P,(39.Vsegs,R5.Vlo,(3:.VSP,VFS,))P,(3;.R8.R5.)P,(32.Vsegs,VL,(14.$1.R>.R;.)(3:.VSP,VFS,)R:.R7.)P,(1>.$10.(30.Vsegs,VL,VHI,R6.)(30.Vsegs,VL,VHI,R=.))P,(3<.Vsegs,VL,VHI,R7.(14.$1.R?.R=.)R9.R8.)(<.R10.R8.R>.R:.R9.R;.)")
(* [comment removed for export] *).
  Proof.
    jc_open.
    intros EX EX2 hc LBc mc moc dXc m2 mo2 h2 J MI2 ST2 MF2 HP HT2 HH2.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 AD1 PD1 NS1 OUT1 FRS1 HPX1 XP1].
    constructor; try assumption.
    - eapply heap_pres_rw_cells; [exact HP| exact FR1| apply client_range_stack; lia].
    - congruence.
    - eapply mo_frame_trans; [exact MF1| exact MF2].
    - eapply statics_ok_heap_pres; [exact SOK1| exact HP| exact SW].
    - eapply mpd_at_heap_pres; [exact MX1| exact HP| exact MI1| exact MI2| rewrite AD1; eapply xj_crX; [exact J| lia]| |].
      + intros EO. pose proof MX1 as [(_ & _ & _ & _ & _ & OW) _]. rewrite EO in OW. destruct OW as (_ & IN & _).
        eapply client_range_block; [apply in_or_app; right; exact IN| lia| lia].
      + intros b Hb. unfold mpd_blk in Hb. pose proof MX1 as [(_ & _ & _ & _ & _ & OW) _]. destruct (md_own dXc); try (destruct Hb; fail).
        destruct Hb as [<-|[]]. exact (proj1 (proj2 OW)).
    - eapply xj_presx_step; [exact J| exact HP| intros b Hb; apply in_or_app; right; exact Hb| lia].
  Qed.

  (* [comment removed for export] *)
  #[using="JCX"] Lemma xj_calloc_fail : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "Phc,(8.Vsegs,VL,VHI,)PLBc,(0.$1.)Pmc,P,(9.&40.)(:.(9.&8.))Pmoc,$;.PdXc,$2.Pm2,P,(9.&40.)(:.(9.&8.))Pmo2,$;.Ph2,(8.Vsegs,VL,VHI,)P,(<.(3=.$1.)R8.R7.R6.R5.R4.)P,(38.Vsegs,R4.)P,(39.Vsegs,R5.Vlo,(3:.VSP,VFS,))P,(3;.R8.R5.)P,(32.Vsegs,VL,R;.(3:.VSP,VFS,)R:.R7.)P,(1>.$10.(30.Vsegs,VL,VHI,R6.)(30.Vsegs,VL,VHI,R=.))P,(3<.Vsegs,VL,VHI,R7.R=.R9.R8.)(<.(3=.$1.)R8.R>.R:.R9.R;.)")
(* [comment removed for export] *).
  Proof. intros. eapply (xj_transport [] []); eassumption. Qed.

  (* [comment removed for export] *)
  Record FB (LBc : list blk) (An cnt : Z) (ys : list word) (mc : mem) (dXc : mpd) : Prop := {
    fb_range : block_range L An (4 * cnt);
    fb_new : In (An, 4 * cnt) LB -> In (An, 4 * cnt) (mpd_blk dX);
    fb_newc : ~ In (An, 4 * cnt) LBc;
    fb_apart : forall B k, In (B, k) LBc -> An + 4 * cnt <= B \/ B + k <= An;
    fb_arr : u32arr segs mc An ys;
    fb_len : Z.of_nat (length ys) = cnt;
    fb_cnt : 0 <= md_n dXc < cnt /\ cnt <= 10000;
    fb_XS : md_addr dX + 16 <= An \/ An + 4 * cnt <= md_addr dX
  }.

  #[using="JCX"] Lemma xj_calloc_ok : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "Phc,(8.Vsegs,VL,VHI,)PLBc,(0.$1.)Pmc,P,(9.&40.)(:.(9.&8.))Pmoc,$;.PdXc,$2.Pm2,P,(9.&40.)(:.(9.&8.))Pmo2,$;.Ph2,(8.Vsegs,VL,VHI,)PAn,$10.Pcnt,$10.P,(<.(3=.$1.)R:.R9.R8.R7.R6.)P,(38.Vsegs,R6.)P,(39.Vsegs,R7.Vlo,(3:.VSP,VFS,))P,(3;.R:.R7.)P,(32.Vsegs,VL,R=.(3:.VSP,VFS,)R<.R9.)P,(1>.$10.(30.Vsegs,VL,VHI,R8.)(30.Vsegs,VL,VHI,R?.))P,(3<.Vsegs,VL,VHI,R9.(3>.(?.$10.$10.)(29.$10.$10.R8.(2:.+4.R7.))R?.)R;.R:.)P,(11.VL,R9.(2:.+4.R8.))P,(3?.Vsegs,R=.R:.(3>.$40.(41.(42.(2:.+4.R9.))(43.(9.&8.)(44.&8.=)(42.(2:.+4.R9.))))(3=.$40.)))P,(=.(1<.(23.R?.)R:.)(19.R:.+2710.))(=.(<.(3>.(?.$10.$10.)(29.$10.$10.R<.(2:.+4.R;.))(3=.(?.$10.$10.)))R=.R13.R?.R>.R10.)(45.R13.R<.R;.(43.(9.&40.)(44.&40.=)(42.R;.))R?.R10.))")
(* [comment removed for export] *).
  Proof.
    jc_open.
    intros hc LBc mc moc dXc m2 mo2 h2 An cnt J MI2 ST2 MF2 HP HT2 HH2 BR HNEW CNT.
    pose proof (xj_facts _ _ _ _ _ _ J) as (HBR1 & HAP1 & ND1 & _ & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1). cbn [app] in HBR1, HAP1, ND1.
    assert (J2 : XJ [(An, 4 * cnt)] h2 LBc m2 mo2 dXc) by (eapply (xj_transport [] [(An, 4 * cnt)]); eassumption).
    split; [exact J2|].
    pose proof (heap_blocks _ _ HI _ _ _ _ HH2) as [HBR2 HAP2]. cbn in HAP2. destruct HAP2 as [APA _].
    pose proof BR as (An0 & An16 & _ & AnC & AnI).
    assert (NEWC : ~ In (An, 4 * cnt) LBc) by (intros Hin; destruct (APA An (4 * cnt) Hin); lia).
    constructor.
    - exact BR.
    - intros Hin. destruct (xj_blocks_orig _ _ _ _ _ _ _ J Hin) as [C|C]; [exfalso; exact (NEWC C)| exact C].
    - exact NEWC.
    - exact APA.
    - eapply u32arr_of_cells; [exact HNEW|]. rewrite u32s_repeat0. f_equal. lia.
    - rewrite repeat_length. lia.
    - lia.
    - destruct (client_range_apart L LBc lo (md_addr dX) 16 An (4 * cnt) ltac:(eapply (xj_crX [] hc); [exact J| lia])); try lia. exact APA.
  Qed.

  (* [comment removed for export] *)
  #[using="JCX"] Lemma xg_memcpy_pre : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "Phc,(8.Vsegs,VL,VHI,)PLBc,(0.$1.)Pmc,P,(9.&40.)(:.(9.&8.))Pmoc,$;.PdXc,$2.PAn,$10.Pcnt,$10.Pys,(0.(9.&40.))P,(<.(3>.(?.$10.$10.)(29.$10.$10.R3.(2:.+4.R2.))(3=.(?.$10.$10.)))R8.R7.R6.R5.R4.)P,(45.R8.R4.R3.R2.R7.R5.)P,(1>.$24.(25.R6.)$28.)(=.(46.Vsegs,R9.(27.R7.)(47.(22.R7.)))(=.(1>.$48.(21.(9.&8.)(47.(22.R7.)))(42.(2:.+4.(23.R7.))))(=.(3?.Vsegs,R9.R6.(3>.$40.(41.(49.#4.(21.(9.&40.)(4:.(9.&40.)(42.(23.R7.))R4.)))(47.(4:.(9.&40.)(42.(23.R7.))R4.)))(3=.$40.)))(=.(1>.$48.(49.#4.(21.(9.&40.)(4:.(9.&40.)(42.(23.R7.))R4.)))(42.(2:.+4.(23.R7.))))(=.(6.(19.(1:.(27.R7.)(2:.+4.(23.R7.)))R6.)(19.(1:.R6.(2:.+4.(23.R7.)))(27.R7.)))(=.(1<.=(27.R7.))(=.(19.(1:.(27.R7.)(2:.+4.(23.R7.)))(2<.VL,))(=.(1<.=R6.)(19.(1:.R6.(2:.+4.R5.))(2<.VL,))))))))))")
(* [comment removed for export] *).
  Proof.
    jc_open.
    intros hc LBc mc moc dXc An cnt ys J F EO.
    pose proof (xj_facts _ _ _ _ _ _ J) as (HBR1 & HAP1 & ND1 & _ & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1).
    destruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI).
    pose proof F as [BR NEW NEWC APA ARR LEN CNT FXS]. pose proof BR as (An0 & An16 & _ & AnC & AnI).
    split; [apply u32arr_ro; exact XARR|]. split; [rewrite u32s_length; lia|].
    rewrite <- (firstn_skipn (Z.to_nat (md_n dXc)) ys) in ARR. apply u32arr_app in ARR. destruct ARR as [A1 A2].
    split; [apply u32arr_cells; exact A1|].
    assert (LF : length (firstn (Z.to_nat (md_n dXc)) ys) = Z.to_nat (md_n dXc)) by (rewrite firstn_length; lia).
    split; [rewrite LF; lia|]. split; [destruct (APA _ _ XIN); lia|]. lia.
  Qed.

  #[using="JCX"] Lemma xg_memcpy_post : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "Phc,(8.Vsegs,VL,VHI,)PLBc,(0.$1.)Pmc,P,(9.&40.)(:.(9.&8.))Pmoc,$;.PdXc,$2.PAn,$10.Pcnt,$10.Pys,(0.(9.&40.))Pm3,P,(9.&40.)(:.(9.&8.))P,(<.(3>.(?.$10.$10.)(29.$10.$10.R4.(2:.+4.R3.))(3=.(?.$10.$10.)))R9.R8.R7.R6.R5.)P,(45.R9.R5.R4.R3.R8.R6.)P,(1>.$24.(25.R7.)$28.)P,(4;.(3>.(?.$10.$10.)(29.$10.$10.R7.(1:.R7.(2:.+4.(23.R8.))))(3=.(?.$10.$10.)))R:.R4.)P,(4<.Vsegs,R;.R5.)P,(38.Vsegs,R6.)P,(3?.Vsegs,R7.R:.(3>.$40.(41.(42.(2:.+4.(23.R;.)))(47.(22.R;.)))(3=.$40.)))(=.(<.(3>.(?.$10.$10.)(29.$10.$10.R;.(2:.+4.R:.))(3=.(?.$10.$10.)))R10.R?.R8.R=.R<.)(45.R?.R;.R:.(14.(9.&40.)(22.R<.)(4=.(9.&40.)(42.(23.R<.))R9.))R8.R<.))")
(* [comment removed for export] *).
  Proof.
    jc_open.
    intros hc LBc mc moc dXc An cnt ys m3 J F EO MU WM MI3 CP.
    pose proof (xj_facts _ _ _ _ _ _ J) as (HBR1 & HAP1 & ND1 & _ & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1).
    destruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI).
    pose proof F as [BR NEW NEWC APA ARR LEN CNT FXS]. pose proof BR as (An0 & An16 & _ & AnC & AnI).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 AD1 PD1 NS1 OUT1 FRS1 HPX1 XP1].
    split.
    - constructor; try assumption.
      + eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. cbn. lia.
      + eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. cbn. rewrite FSZ. lia.
      + eapply (HEAP_munch segs L HI) with (SP := lo); [exact HH1| exact MU| exact WM| exact ACL|].
        intros a Ha NO. cbn in NO. right; right. exists (An, 4 * cnt). split; [left; reflexivity| cbn; lia].
      + eapply statics_ok_munch; [exact SOK1| exact MU|]. intros a Hd NW. cbn. lia.
      + eapply mpd_at_munch_any; [exact MX1| exact MU| exact WM| rewrite AD1; cbn; lia|]. intros _. cbn. destruct (APA _ _ XIN); lia.
      + eapply heap_presx_trans; [exact HPX1|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
        intros a Ha Hc Ho. cbn. split; [| exact I].
        destruct Hc as [C|[[C1 C2]|(b & Hb & Rb)]]; [lia| lia|].
        destruct (xj_blocks_orig _ _ _ _ _ _ _ J Hb) as [HbC|HbX].
        * destruct b as [q k]. cbn in Rb. destruct (APA q k HbC); lia.
        * unfold mpd_blk in HbX. unfold mpd_ivs in Ho. destruct (md_own dX); try (destruct HbX; fail). destruct HbX as [<-|[]]. cbn in Rb, Ho. lia.
    - constructor; try assumption.
      + rewrite <- (firstn_skipn (Z.to_nat (md_n dXc)) ys) in ARR. apply u32arr_app in ARR. destruct ARR as [_ A2].
        rewrite firstn_length in A2. replace (Init.Nat.min (Z.to_nat (md_n dXc)) (length ys)) with (Z.to_nat (md_n dXc)) in A2 by lia.
        apply u32arr_app. split; [eapply u32arr_of_cells; [exact CP| reflexivity]|].
        replace (4 * Z.of_nat (length (md_limbs dXc))) with (4 * Z.of_nat (Z.to_nat (md_n dXc))) by lia.
        eapply u32arr_transport; [exact A2| exact MU| exact WM|]. cbn. rewrite skipn_length. lia.
      + rewrite app_length, skipn_length. lia.
  Qed.

  (* [comment removed for export] *)
  Record XD (hd : HST segs L HI) (LBd : list blk) (An cnt : Z) (ys : list word) (me : mem) (moe : Model) (dXc : mpd) : Prop := {
    xd_mi : mem_inv segs me;
    xd_stk : stk segs me lo (SP - FS);
    xd_fr : rw_cells segs me (SP - FS) FRAME;
    xd_heap : HEAP segs L HI hd ((An, 4 * cnt) :: LBd) me moe;
    xd_top : heap_top segs L HI hd = heap_top segs L HI h;
    xd_mf : mo_frame mo moe;
    xd_sok : statics_ok segs L me;
    xd_struct : rw_cells segs me (md_addr dX) (mpi_cells (md_p dXc) (Z_to_bv 64 (md_sg dXc)) (md_n dXc) (md_pad dX));
    xd_sg : md_sg dXc = 1 \/ md_sg dXc = -1;
    xd_sub : forall b, In b LBd -> In b LB;
    xd_keep : forall b, In b LB -> ~ In b (mpd_blk dX) -> In b LBd;
    xd_gone : forall b, In b (mpd_blk dX) -> ~ In b LBd;
    xd_new : In (An, 4 * cnt) LB -> In (An, 4 * cnt) (mpd_blk dX);
    xd_apart : forall B k, In (B, k) LBd -> An + 4 * cnt <= B \/ B + k <= An;
    xd_arr : u32arr segs me An ys;
    xd_len : Z.of_nat (length ys) = cnt;
    xd_cnt : 0 <= md_n dXc < cnt /\ cnt <= 10000;
    xd_XS : md_addr dX + 16 <= An \/ An + 4 * cnt <= md_addr dX;
    xd_presx : heap_presx segs L LB SP (mpd_ivs dX) m me;
    xd_range : block_range L An (4 * cnt);
    xd_nmono : md_n dX <= md_n dXc
  }.

  #[using="JCX"] Lemma xg_null : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "Phc,(8.Vsegs,VL,VHI,)PLBc,(0.$1.)Pmc,P,(9.&40.)(:.(9.&8.))Pmoc,$;.PdXc,$2.PAn,$10.Pcnt,$10.Pys,(0.(9.&40.))P,(<.(3>.(?.$10.$10.)(29.$10.$10.R3.(2:.+4.R2.))(3=.(?.$10.$10.)))R8.R7.R6.R5.R4.)P,(45.R8.R4.R3.R2.R7.R5.)P,(1>.$24.(25.R6.)$26.)(4>.R;.R:.R6.R5.R4.R9.R8.R7.)")
(* [comment removed for export] *).
  Proof.
    jc_open.
    intros hc LBc mc moc dXc An cnt ys J F EO.
    pose proof F as [BR NEW NEWC APA ARR LEN CNT FXS].
    pose proof J as [MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 AD1 PD1 NS1 OUT1 FRS1 HPX1 XP1].
    pose proof MX1 as [(CX & _) SG]. rewrite AD1, PD1 in CX.
    pose proof OUT1 as (_ & _ & O3 & O4 & O5).
    constructor; try assumption.
    - intros b Hb. destruct (O3 b Hb) as [C|C]; [exact C|]. unfold mpd_blk in C. rewrite EO in C. destruct C.
    - intros b HbX HbC. pose proof (O5 b HbX HbC) as E. unfold mpd_blk in E, HbX. rewrite EO in E.
      destruct (md_own dX); try (destruct HbX; fail). discriminate.
  Qed.

  #[using="JCX"] Lemma xg_zfree_pre : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "Phc,(8.Vsegs,VL,VHI,)PLBc,(0.$1.)Pmc,P,(9.&40.)(:.(9.&8.))Pmoc,$;.PdXc,$2.PAn,$10.Pcnt,$10.Pys,(0.(9.&40.))P,(<.(3>.(?.$10.$10.)(29.$10.$10.R3.(2:.+4.R2.))(3=.(?.$10.$10.)))R8.R7.R6.R5.R4.)P,(45.R8.R4.R3.R2.R7.R5.)P,(1>.$24.(25.R6.)$28.)(=.(4.(?.$10.$10.)(29.$10.$10.(27.R7.)(2:.+4.(23.R7.)))(3>.(?.$10.$10.)(29.$10.$10.R6.(2:.+4.R5.))R:.))(=.(3?.Vsegs,R9.(27.R7.)(3>.$40.(41.(49.#4.(21.(9.&40.)(22.R7.)))(47.(22.R7.)))(3=.$40.)))(=.(1>.$48.(49.#4.(21.(9.&40.)(22.R7.)))(42.(2:.+4.(23.R7.))))(=.(19.=(2:.+4.(23.R7.)))(1<.(2:.+4.(23.R7.))(1=.+2.+40.))))))")
(* [comment removed for export] *).
  Proof.
    jc_open.
    intros hc LBc mc moc dXc An cnt ys J F EO.
    pose proof (xj_facts _ _ _ _ _ _ J) as (HBR1 & HAP1 & ND1 & _ & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1).
    destruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI).
    split; [right; exact XIN|]. split; [apply u32arr_cells; exact XARR|]. lia.
  Qed.

  #[using="Type"] Lemma lb_remove_cons_other : forall (A B : Z) k (l : list blk), B <> A -> lb_remove A ((B, k) :: l) = (B, k) :: lb_remove A l.
  Proof. intros A B k l NE. cbn. destruct (Z.eqb_spec B A); [contradiction| reflexivity]. Qed.

  #[using="JCX"] Lemma xg_zfree_post : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "Phc,(8.Vsegs,VL,VHI,)PLBc,(0.$1.)Pmc,P,(9.&40.)(:.(9.&8.))Pmoc,$;.PdXc,$2.PAn,$10.Pcnt,$10.Pys,(0.(9.&40.))Pm4,P,(9.&40.)(:.(9.&8.))Pmo4,$;.Ph4,(8.Vsegs,VL,VHI,)P,(<.(3>.(?.$10.$10.)(29.$10.$10.R6.(2:.+4.R5.))(3=.(?.$10.$10.)))R;.R:.R9.R8.R7.)P,(45.R;.R7.R6.R5.R:.R8.)P,(1>.$24.(25.R9.)$28.)P,(38.Vsegs,R6.)P,(39.Vsegs,R7.Vlo,(3:.VSP,VFS,))P,(3;.R=.R7.)P,(1>.$10.(30.Vsegs,VL,VHI,R7.)(30.Vsegs,VL,VHI,R11.))P,(3<.Vsegs,VL,VHI,R8.(4?.(27.R>.)(3>.(?.$10.$10.)(29.$10.$10.R=.(2:.+4.R<.))R11.))R:.R9.)P,(33.Vsegs,VL,(4?.(27.R?.)(3>.(?.$10.$10.)(29.$10.$10.R>.(2:.+4.R=.))R12.))(3:.VSP,VFS,)(3>.(?.$10.$10.)(29.$10.$10.(27.R?.)(1:.(27.R?.)(2:.+4.(23.R?.))))(3=.(?.$10.$10.)))R11.R;.)P,(50.Vsegs,VL,R<.)(4>.R;.(4?.(27.R11.)R14.)R10.R?.R>.R=.R<.R11.)")
(* [comment removed for export] *).
  Proof.
    jc_open.
    intros hc LBc mc moc dXc An cnt ys m4 mo4 h4 J F EO MI4 ST4 MF4 HT4 HH4 HP4 SOK4.
    pose proof (xj_facts _ _ _ _ _ _ J) as (HBR1 & HAP1 & ND1 & _ & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1).
    destruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI).
    pose proof F as [BR NEW NEWC APA ARR LEN CNT FXS]. pose proof BR as (An0 & An16 & _ & AnC & AnI).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 AD1 PD1 NS1 OUT1 FRS1 HPX1 XP1].
    pose proof MX1 as [(CX & _) SG]. rewrite AD1, PD1 in CX.
    pose proof OUT1 as (_ & _ & O3 & O4 & O5).
    assert (NEA : An <> md_p dXc) by (destruct (APA _ _ XIN); lia).
    rewrite (lb_remove_cons_other (md_p dXc) An (4 * cnt) LBc NEA) in HH4, HP4.
    assert (NDc : List.NoDup (map fst LBc)) by (cbn in ND1; inversion ND1; assumption).
    assert (NOTIN : ~ In (md_p dXc, 4 * md_n dXc) (lb_remove (md_p dXc) LBc)) by (apply lb_remove_notin; exact NDc).
    assert (KEEPc : forall q k, In (q, k) LBc -> (q, k) <> (md_p dXc, 4 * md_n dXc) -> In (q, k) (lb_remove (md_p dXc) LBc)).
    { intros q k Hq NE. eapply in_lb_remove_other; [exact NDc| exact XIN| exact Hq| exact NE]. }
    constructor; try assumption.
    - eapply heap_presx_rw_cells; [exact HP4| exact FR1| apply client_range_stack; lia| cbn; rewrite FSZ; lia].
    - congruence.
    - eapply mo_frame_trans; [exact MF1| exact MF4].
    - eapply heap_presx_rw_cells; [exact HP4| exact CX| | cbn; pose proof (XP1 EO); lia].
      intros a Ha. cbn in Ha. destruct (xj_cwX _ _ _ _ _ _ J a Ha) as [C|[C|([q k] & Hq & R)]]; [left; lia| right; left; exact C| right; right].
      exists (q, k). split; [| exact R]. right. apply KEEPc; [exact Hq|]. intros E. injection E as -> ->. cbn in R, Ha. pose proof (XP1 EO). lia.
    - intros b Hb. pose proof (In_lb_remove _ _ _ Hb) as HbC. destruct (O3 b HbC) as [C|C]; [exact C|].
      unfold mpd_blk in C. rewrite EO in C. destruct C as [<-|[]]. exfalso. exact (NOTIN Hb).
    - intros [q k] Hb NX. pose proof (O4 _ Hb NX) as HbC. apply KEEPc; [exact HbC|]. intros E. rewrite E in *.
      destruct (FRS1 (md_p dXc, 4 * md_n dXc) ltac:(unfold mpd_blk; rewrite EO; left; reflexivity)) as [C|C]; [exact (NX C)| exact (C Hb)].
    - intros b HbX Hb4. pose proof (In_lb_remove _ _ _ Hb4) as HbC. pose proof (O5 b HbX HbC) as E.
      assert (Hb' : In b (mpd_blk dXc)) by (rewrite E; exact HbX). unfold mpd_blk in Hb'. rewrite EO in Hb'. destruct Hb' as [<-|[]]. exact (NOTIN Hb4).
    - intros q k Hq. apply APA. eapply In_lb_remove. exact Hq.
    - destruct ARR as [AB AW]. split.
      + eapply heap_presx_bytes_at; [exact HP4| exact AB| rewrite u32s_length; eapply client_range_block; [left; reflexivity| lia| cbn; lia]| cbn; rewrite u32s_length; destruct (APA _ _ XIN); lia].
      + eapply heap_presx_wr_at; [exact HP4| exact AW| eapply client_range_block; [left; reflexivity| lia| cbn; lia]| cbn; destruct (APA _ _ XIN); lia].
    - eapply heap_presx_trans; [exact HPX1|]. intros a Ha Hc Ho.
      pose proof (xj_not_limbs _ _ _ _ _ _ a J Hc Ho EO) as NL.
      apply HP4; [exact Ha| | cbn; split; [exact NL| exact I]].
      destruct Hc as [C|[C|(b & Hb & Rb)]]; [left; lia| right; left; exact C| right; right].
      destruct (xj_blocks_orig _ _ _ _ _ _ _ J Hb) as [HbC|HbX].
      + destruct b as [q k]. exists (q, k). split; [| exact Rb]. right. apply KEEPc; [exact HbC|]. intros E. injection E as -> ->. cbn in Rb. lia.
      + exfalso. unfold mpd_blk in HbX. unfold mpd_ivs in Ho. destruct (md_own dX); try (destruct HbX; fail). destruct HbX as [<-|[]]. cbn in Rb, Ho. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="JCX"] Lemma xd_finish : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "Phd,(8.Vsegs,VL,VHI,)PLBd,(0.$1.)PAn,$10.Pcnt,$10.Pys,(0.(9.&40.))Pme,P,(9.&40.)(:.(9.&8.))Pmoe,$;.PdXc,$2.Pm5,P,(9.&40.)(:.(9.&8.))P,(4>.R9.R8.R7.R6.R5.R4.R3.R2.)P,(4;.(3>.(?.$10.$10.)(29.$10.$10.(1;.VdX,)(1:.(1;.VdX,)+10.))(3=.(?.$10.$10.)))R5.R2.)P,(4<.Vsegs,R6.R3.)P,(38.Vsegs,R4.)P,(3?.Vsegs,R5.(1;.VdX,)(51.R;.(44.&40.(52.R6.))R:.(53.VdX,)))(<.(3=.$1.)R>.(3>.(?.$10.$10.)(29.$10.$10.R<.(2:.+4.R;.))R=.)R6.R8.(54.(1;.VdX,)(52.R7.)R;.R<.R:.(53.VdX,)$28.))")
(* [comment removed for export] *).
  Proof.
    jc_open.
    intros hd LBd An cnt ys me moe dXc m5 D MU WM MI5 CX5.
    pose proof D as [MI4 ST4 FR4 HH4 HT4 MF4 SOK4 CX4 SG SUB KEEP GONE NEW APA ARR LEN CNT DXS HPX4 BR NMX].
    pose proof BR as (An0 & An16 & _ & AnC & AnI).
    pose proof (heap_blocks _ _ HI _ _ _ _ HH) as [HBR0 _]. pose proof XW as (XCW & XDW & XP).
    pose proof (client_wrange_where L _ _ _ (md_addr dX) 16 lo XCW ltac:(lia) HBR0 DHI ACL ltac:(lia)) as XS.
    pose proof MX as [(CX0 & XAL & X0 & _) _]. pose proof (rw_cells_bound _ _ _ _ CX0) as XB. unfold mpi_cells in XB. cbn [cells_size csize Nat.add] in XB.
    constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app]; try assumption.
    - eapply stk_transport_disjoint; [exact ST4| exact MU| exact WM|]. cbn. lia.
    - eapply rw_cells_transport; [exact FR4| exact MU| exact WM|]. cbn. rewrite FSZ. lia.
    - eapply (HEAP_munch segs L HI) with (SP := lo); [exact HH4| exact MU| exact WM| exact ACL|].
      intros a Ha NO. cbn in NO. rewrite HT4. assert (Ha' : md_addr dX <= a < md_addr dX + 16) by lia.
      destruct (XCW a Ha') as [C|[C|([q k] & Hq & R)]]; [left; lia| right; left; exact C| right; right].
      exists (q, k). split; [| exact R]. right. apply KEEP; [exact Hq|]. cbn in R.
      unfold mpd_blk. destruct (md_own dX) eqn:EO; try (intros []; fail). intros [E|[]]. injection E as E1 E2. pose proof (XP eq_refl). lia.
    - eapply statics_ok_munch; [exact SOK4| exact MU|]. intros a Hd NW. cbn. split; [| exact I]. intros C. exact (NW (XDW a C Hd)).
    - split; [| exact SG]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [exact CX5|]. split; [exact XAL|]. split; [exact X0|]. split; [exact LEN|]. split; [unfold MPI_MAX_LIMBS; lia|].
      split; [lia|]. split; [left; reflexivity|]. split; [exact An16|].
      eapply u32arr_transport; [exact ARR| exact MU| exact WM|]. cbn. lia.
    - reflexivity.
    - reflexivity.
    - discriminate.
    - unfold mpd_out. cbn [md_addr md_own mpd_blk md_p md_n]. split; [reflexivity|]. split; [discriminate|].
      split; [intros b [<-|Hb]; [right; left; reflexivity| left; exact (SUB b Hb)]|].
      split; [intros b Hb NX; right; exact (KEEP b Hb NX)|].
      intros b HbX [<-|Hb4]; [| exfalso; exact (GONE b HbX Hb4)].
      unfold mpd_blk in HbX |- *. destruct (md_own dX); try (destruct HbX; fail). destruct HbX as [E|[]]. rewrite E. reflexivity.
    - unfold mpd_blk; cbn [md_own md_p md_n]. intros b [<-|[]].
      destruct (in_dec blk_eq_dec (An, 4 * cnt) LB) as [Hin|Hnin]; [left; exact (NEW Hin)| right; exact Hnin].
    - eapply heap_presx_trans; [exact HPX4|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. unfold mpd_ivs in Ho. cbn in Ho |- *. split; [| exact I]. lia.
    - intros _. exact DXS.
    - lia.
  Qed.

  (* [comment removed for export] *)
  #[using="JCX"] Lemma xj_limbs : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "Phc,(8.Vsegs,VL,VHI,)PLBc,(0.$1.)Pmc,P,(9.&40.)(:.(9.&8.))Pmoc,$;.PX,$10.Psg,$10.Pn,$10.Pp,$10.Pxs,(0.(9.&40.))Ppad,(9.&40.)PW,(0.$35.)Pm',P,(9.&40.)(:.(9.&8.))Pxs',(0.(9.&40.))P,(<.(3=.$1.)R=.R<.R;.R:.(54.R9.R8.R7.R6.R5.R4.$28.))P,(4;.R4.R<.R3.)P,(4<.Vsegs,R=.R4.)P,(38.Vsegs,R5.)P,(39.Vsegs,R6.Vlo,(3:.VSP,VFS,))P,Pa,$10.P,(7.(36.R9.R1.))(6.(=.(19.R=.R2.)(1<.R2.(1:.R=.(2:.+4.R>.))))(=.(19.Vlo,R2.)(1<.R2.(3:.VSP,VFS,))))P,(55.R9.(3:.VSP,VFS,)VFS,)P,(55.R:.R10.+10.)P,(2;.Vsegs,R:.R>.R9.)P,(1>.$48.(21.(9.&40.)R:.)(21.(9.&40.)R>.))(<.(3=.$1.)R17.R16.R<.R14.(54.R13.R12.R11.R10.R;.R>.$28.))")
(* [comment removed for export] *).
  Proof.
    jc_open.
    intros hc LBc mc moc X sg n p xs pad W m' xs' J MU WM MI' ST' HW DF DS ARR' LEN'.
    pose proof (xj_facts _ _ _ _ _ _ J) as (HBR1 & HAP1 & ND1 & _ & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1).
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app] in *.
    destruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI).
    pose proof J as [MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 AD1 PD1 NS1 OUT1 FRS1 HPX1 XP1].
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app] in *.
    assert (OUTW : forall a, (p + 4 * n <= a \/ a < p) -> (a < lo \/ SP - FS <= a) -> outside W a).
    { intros a H1 H2. destruct (outside_dec W a) as [O|NO]; [exact O|]. exfalso. destruct (HW a NO); lia. }
    constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app]; try assumption.
    - eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. rewrite FSZ. exact DF.
    - eapply (HEAP_munch segs L HI) with (SP := lo); [exact HH1| exact MU| exact WM| exact ACL|].
      intros a Ha NO. rewrite HT1. destruct (HW a NO) as [R|R]; [right; right; exists (p, 4 * n); split; [exact XIN| cbn; lia]| left; lia].
    - eapply statics_ok_munch; [exact SOK1| exact MU|]. intros a Hd NW. apply OUTW; lia.
    - pose proof MX1 as [(CX & _ & _ & _ & _ & OW) SG]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      split; [| exact SG]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [eapply rw_cells_transport; [exact CX| exact MU| exact WM| unfold mpi_cells; cbn [cells_size csize Nat.add]; exact DS]|].
      split; [rewrite AD1; exact XAL|]. split; [rewrite AD1; exact X0|]. split; [rewrite <- LEN1, LEN'; reflexivity|]. split; [unfold MPI_MAX_LIMBS; lia|].
      split; [exact N1|]. split; [exact XIN|]. split; [exact XPAL| exact ARR'].
    - eapply heap_presx_trans; [exact HPX1|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. pose proof (xj_not_limbs _ _ _ _ _ _ a J Hc Ho eq_refl) as NL. cbn [md_p md_n] in NL.
      pose proof (heap_blocks _ _ HI _ _ _ _ HH) as [HBR0 _].
      apply OUTW; [lia|]. destruct Hc as [C|[[C1 C2]|([q k] & Hb & Rb)]]; [lia| lia|].
      pose proof (proj1 (Forall_forall _ _) HBR0 _ Hb) as (_ & _ & _ & R3 & _). cbn in R3, Rb. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="JCX"] Lemma xj_post : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "Phc,(8.Vsegs,VL,VHI,)PLBc,(0.$1.)Pmc,P,(9.&40.)(:.(9.&8.))Pmoc,$;.PdXc,$2.PR,P,$10.P,$2.SpPr,$10.Pra,(9.&40.)Pgp,(9.&40.)Ptp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PF,(56.&5.(9.&40.))Pfc,(9.&20.)P,(<.(3=.$1.)R26.R25.R24.R23.R22.)P,A2.R22.R21.R23.(57.Vsegs,VL,VHI,R21.Vsp,R20.R1?.R1;.R1:.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R4.R3.Vh,VLB,VdX,R23.Vlo,Vm,Vmo,(58.(59.(5:.R21.Vsp,R20.R1?.R1>.R1=.R1<.R1;.R1:.(44.&40.R22.)R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)R4.(5;.R21.)R3.(5<.(9.&40.))R26.(5=.Vsegs,))R25.))")
(* [comment removed for export] *).
  Proof.
    jc_open.
    intros until fc. intros J HR. pose proof J as [MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 AD1 PD1 NS1 OUT1 FRS1 HPX1 XP1]. cbn [app] in HH1.
    unfold mpi_binop_post. do 14 eexists. exists mc, moc, hc, LBc, dXc, r.
    split; [reflexivity|]. split; [exact MI1|].
    split; [pose proof (stk_release segs mc lo (SP - FS) FRAME ST1 FR1 ltac:(lia)) as ST; rewrite FSZ in ST; replace (SP - FS + FS) with SP in ST by lia; exact ST|].
    split; [exact MF1|]. split; [exact HT1|]. split; [exact HH1|]. split; [exact MX1|]. split; [exact OUT1|]. split; [exact HPX1|]. split; [exact SOK1| exact HR].
  Qed.

  (* [comment removed for export] *)
  #[using="JCX"] Lemma xj_struct_sign : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "Phc,(8.Vsegs,VL,VHI,)PLBc,(0.$1.)Pmc,P,(9.&40.)(:.(9.&8.))Pmoc,$;.Psg,$10.Pn,$10.Pp,$10.Pxs,(0.(9.&40.))Pown,$24.Pm',P,(9.&40.)(:.(9.&8.))Psg',$10.P,(<.(3=.$1.)R;.R:.R9.R8.(54.(1;.VdX,)R7.R6.R5.R4.(53.VdX,)R3.))P,(4;.(3>.(?.$10.$10.)(29.$10.$10.(1;.VdX,)(1:.(1;.VdX,)+10.))(3=.(?.$10.$10.)))R:.R3.)P,(4<.Vsegs,R;.R4.)P,(38.Vsegs,R5.)P,(3?.Vsegs,R6.(1;.VdX,)(51.R9.(44.&40.R5.)R:.(53.VdX,)))P,(6.(1>.$10.R6.+1.)(1>.$10.R6.-1.))(<.(3=.$1.)R11.R10.R8.R>.(54.(1;.VdX,)R7.R<.R;.R:.(53.VdX,)R9.))")
(* [comment removed for export] *).
  Proof.
    jc_open.
    intros hc LBc mc moc sg n p xs own m' sg' J MU WM MI' CX' SG'.
    pose proof (xj_facts _ _ _ _ _ _ J) as (HBR1 & HAP1 & ND1 & _ & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1).
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app] in *.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 MF1 SOK1 MX1 AD1 PD1 NS1 OUT1 FRS1 HPX1 XP1].
    cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app] in *. destruct XW as (XCW & XDW & XP).
    constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own app]; try assumption.
    - eapply stk_transport_disjoint; [exact ST1| exact MU| exact WM|]. cbn. lia.
    - eapply rw_cells_transport; [exact FR1| exact MU| exact WM|]. cbn. rewrite FSZ. lia.
    - eapply (HEAP_munch segs L HI) with (SP := lo); [exact HH1| exact MU| exact WM| exact ACL|].
      intros a Ha NO. cbn in NO. rewrite HT1. assert (Ha' : md_addr dX <= a < md_addr dX + 16) by lia.
      destruct (xj_cwX _ _ _ _ _ _ J a Ha') as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C].
    - eapply statics_ok_munch; [exact SOK1| exact MU|]. intros a Hd NW. cbn. split; [| exact I]. intros C. exact (NW (XDW a C Hd)).
    - pose proof MX1 as [(CX & XAL' & X0' & LEN & NR & OW) _]. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own] in *.
      split; [| exact SG']. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [exact CX'|]. split; [exact XAL'|]. split; [exact X0'|]. split; [exact LEN|]. split; [exact NR|].
      destruct own; [exact OW| | exfalso; exact (NS1 eq_refl)].
      destruct OW as (O1 & O2 & O3 & O4). split; [exact O1|]. split; [exact O2|]. split; [exact O3|].
      eapply u32arr_transport; [exact O4| exact MU| exact WM|]. cbn. pose proof (XP1 eq_refl). lia.
    - eapply heap_presx_trans; [exact HPX1|]. eapply heap_presx_of_munch; [exact MU| exact WM|].
      intros a Ha Hc Ho. unfold mpd_ivs in Ho. cbn in Ho |- *. split; [| exact I]. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable dB : mpd.
  Record JB : Prop := {
    jb_MB0 : opnd_at segs m LB SP dB;
    jb_OB : opnd_sep dX dB lo SP;
    jb_CRB : client_range L LB lo (md_addr dB) 16;
    jb_CRBL : md_own dB = LHeap -> client_range L LB lo (md_p dB) (4 * md_n dB);
    jb_SXB : md_addr dX + 16 <= md_addr dB \/ md_addr dB + 16 <= md_addr dX }.
  Hypothesis DBJ : JB.
  Local Ltac jb_open := pose proof DBJ as [MB0 OB CRB CRBL SXB].

  Record BJ (LBc : list blk) (mc : mem) (dXc : mpd) : Prop := {
    bj_at : opnd_at segs mc LBc SP dB;
    bj_sepS : md_own dXc = LHeap -> md_addr dB + 16 <= md_p dXc \/ md_p dXc + 4 * md_n dXc <= md_addr dB;
    bj_sepL : md_own dXc = LHeap -> md_own dB <> LNull -> md_p dXc + 4 * md_n dXc <= md_p dB \/ md_p dB + 4 * md_n dB <= md_p dXc
  }.

  #[using="L HI h m mo dX FS FRAME JCX DBJ"] Lemma bj_facts : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "PLBc,(0.$1.)Pmc,P,(9.&40.)(:.(9.&8.))PdXc,$2.P,(5>.R3.R2.R1.)(=.(1<.=(1;.VdB,))(=.(19.(1:.(1;.VdB,)+10.)(1=.+2.+40.))(=.(1>.$10.(1?.(1;.VdB,)+8.)=)(=.(1>.$10.(20.(21.(9.&40.)(22.VdB,)))(23.VdB,))(=.(=.(19.=(23.VdB,))(19.(23.VdB,)+2710.))(=.(6.(19.(1:.(1;.VdB,)+10.)Vlo,)(19.VSP,(1;.VdB,)))(=.P,(1>.$24.(25.VdB,)$26.)(=.(1>.$10.(27.VdB,)=)(1>.$10.(23.VdB,)=))P,(7.(1>.$24.(25.VdB,)$26.))(=.(19.+1.(23.VdB,))(=.(1<.=(27.VdB,))(=.(1>.$10.(1?.(27.VdB,)+4.)=)(=.(46.Vsegs,R4.(27.VdB,)(47.(22.VdB,)))(=.(6.(19.(1:.(27.VdB,)(2:.+4.(23.VdB,)))Vlo,)(19.VSP,(27.VdB,)))P,(1>.$24.(25.VdB,)$28.)(=.(4.(?.$10.$10.)(29.$10.$10.(27.VdB,)(2:.+4.(23.VdB,)))VLB,)(4.(?.$10.$10.)(29.$10.$10.(27.VdB,)(2:.+4.(23.VdB,)))R6.))))))))))))))")
(* [comment removed for export] *).
  Proof.
    jc_open. jb_open.
    intros LBc mc dXc B. pose proof (opnd_view _ _ _ _ _ (bj_at _ _ _ B)) as [(CB & BAL & B0 & LENB & NRB & OWNB) SGB].
    pose proof (rw_cells_bound _ _ _ _ CB) as BB. unfold mpi_cells in BB. cbn [cells_size csize Nat.add] in BB. unfold MPI_MAX_LIMBS in NRB.
    pose proof OB as (OB1 & OB2 & OB3 & OB4 & OB5). pose proof (heap_blocks _ _ HI _ _ _ _ HH) as [HBR0 _].
    split; [exact B0|]. split; [lia|]. split; [exact BAL|]. split; [exact LENB|]. split; [exact NRB|]. split; [exact OB4|].
    split; [intros EO; rewrite EO in OWNB; exact OWNB|].
    intros BN. pose proof (opnd_view _ _ _ _ _ MB0) as [(_ & _ & _ & _ & _ & OWNB0) _].
    destruct (md_own dB); [exfalso; exact (BN eq_refl)| |].
    - destruct OWNB as (N1 & BIN & BPAL & BARR). destruct OWNB0 as (_ & BIN0 & _).
      pose proof (proj1 (Forall_forall _ _) HBR0 _ BIN0) as (R0 & R1 & _). cbn in R0, R1.
      split; [exact N1|]. split; [exact R0|]. split; [clear - BPAL R0; lia|]. split; [apply u32arr_ro; exact BARR|]. split; [exact (OB5 BN)|]. intros _. split; assumption.
    - destruct OWNB as (N1 & BPAL & BP0 & BBY & BRO). split; [exact N1|]. split; [exact BP0|]. split; [exact BPAL|]. split; [exact BBY|]. split; [exact (OB5 BN)|]. intros; discriminate.
  Qed.

  (* [comment removed for export] *)
  #[using="JCX DBJ"] Lemma bj_client : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "PEX,(0.$1.)Phc,(8.Vsegs,VL,VHI,)PLBc,(0.$1.)Pmc,P,(9.&40.)(:.(9.&8.))Pmoc,$;.PdXc,$2.PLBn,(0.$1.)PSPn,$10.P,(<.R8.R7.R6.R5.R4.R3.)P,(5>.R7.R6.R4.)P,Pb,$1.P,(4.$1.R1.R9.)P,P,(1>.$24.(25.R7.)$28.)(7.(1>.$1.R3.(29.$10.$10.(27.R8.)(2:.+4.(23.R8.)))))(4.$1.R3.R7.)P,(19.R4.VSP,)(=.(31.VL,R6.R5.(1;.VdB,)+10.)P,(1>.$24.(25.VdB,)$28.)(31.VL,R7.R6.(27.VdB,)(2:.+4.(23.VdB,))))")
(* [comment removed for export] *).
  Proof.
    jc_open. jb_open.
    intros EX hc LBc mc moc dXc LBn SPn J B SUB LE. pose proof OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    pose proof (bj_facts _ _ _ B) as (B0 & B16 & BAL & LENB & NRB & BS & OWNB0 & OWNB1).
    split.
    - intros a Ha. destruct (CRB a Ha) as [C|[C|([q k] & Hq & R)]]; [left; lia| right; left; exact C| right; right].
      exists (q, k). split; [| exact R]. cbn in R. apply SUB.
      + apply (proj1 (proj2 (proj2 (proj2 (xj_out _ _ _ _ _ _ J))))); [exact Hq|]. unfold mpd_blk. destruct (md_own dX) eqn:EO; try (intros []; fail).
        intros [E|[]]. injection E as E1 E2. pose proof (OB2 eq_refl). lia.
      + intros EO E. injection E as E1 E2. pose proof (bj_sepS _ _ _ B EO). lia.
    - intros EO a Ha. destruct (OWNB1 ltac:(rewrite EO; discriminate)) as (N1 & P0 & _ & _ & _ & BIN). destruct (BIN EO) as [BIN0 BINc].
      right; right. exists (md_p dB, 4 * md_n dB). split; [| cbn; lia]. apply SUB; [exact BINc|].
      intros EOX E. injection E as E1 E2. pose proof (bj_sepL _ _ _ B EOX ltac:(rewrite EO; discriminate)). lia.
  Qed.

  #[using="JCX DBJ"] Lemma bj_heap_pres : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "PEX,(0.$1.)Phc,(8.Vsegs,VL,VHI,)PLBc,(0.$1.)Pmc,P,(9.&40.)(:.(9.&8.))Pmoc,$;.PdXc,$2.Pm2,P,(9.&40.)(:.(9.&8.))P,(<.R7.R6.R5.R4.R3.R2.)P,(5>.R6.R5.R3.)P,(32.Vsegs,VL,(14.$1.R9.R7.)(3:.VSP,VFS,)R6.R3.)P,(38.Vsegs,R4.)(5>.R9.R5.R6.)")
(* [comment removed for export] *).
  Proof.
    jc_open. jb_open.
    intros EX hc LBc mc moc dXc m2 J B HP MI2. pose proof B as [BA BS BL].
    destruct (bj_client EX hc LBc mc moc dXc (EX ++ LBc) (SP - FS) J B ltac:(intros b Hb _; apply in_or_app; right; exact Hb) ltac:(lia)) as [C1 C2].
    constructor; [| exact BS| exact BL].
    eapply opnd_at_heap_pres; [exact BA| exact HP| exact (xj_mi _ _ _ _ _ _ J)| exact MI2| exact C1| exact C2| | lia].
    intros b Hb. unfold mpd_blk in Hb. pose proof (opnd_view _ _ _ _ _ BA) as [(_ & _ & _ & _ & _ & OW) _]. destruct (md_own dB); try (destruct Hb; fail). destruct Hb as [<-|[]]. exact (proj1 (proj2 OW)).
  Qed.

  #[using="L HI h LB m mo dX lo FS FRAME JCX DBJ"] Lemma bj_munch : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "PLBc,(0.$1.)Pmc,P,(9.&40.)(:.(9.&8.))PdXc,$2.PW,(0.$35.)Pm',P,(9.&40.)(:.(9.&8.))P,(5>.R5.R4.R3.)P,(4;.R3.R5.R2.)P,(4<.Vsegs,R6.R3.)P,(55.R5.(1;.VdB,)+10.)P,P,(7.(1>.$24.(25.VdB,)$26.))(55.R7.(27.VdB,)(2:.+4.(23.VdB,)))(5>.R:.R6.R8.)")
(* [comment removed for export] *).
  Proof.
    jc_open. jb_open.
    intros LBc mc dXc W m' [BA BS BL] MU WM D1 D2. constructor; [| exact BS| exact BL].
    eapply opnd_at_munch_any; eassumption.
  Qed.

  #[using="JCX DBJ"] Lemma bj_zfree : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "Phc,(8.Vsegs,VL,VHI,)PLBc,(0.$1.)Pmc,P,(9.&40.)(:.(9.&8.))Pmoc,$;.PdXc,$2.PAn,$10.Pcnt,$10.Pys,(0.(9.&40.))Pm4,P,(9.&40.)(:.(9.&8.))P,(<.(3>.(?.$10.$10.)(29.$10.$10.R4.(2:.+4.R3.))(3=.(?.$10.$10.)))R9.R8.R7.R6.R5.)P,(45.R9.R5.R4.R3.R8.R6.)P,(5>.R:.R9.R7.)P,(1>.$24.(25.R8.)$28.)P,(33.Vsegs,VL,(4?.(27.R9.)(3>.(?.$10.$10.)(29.$10.$10.R8.(2:.+4.R7.))R<.))(3:.VSP,VFS,)(3>.(?.$10.$10.)(29.$10.$10.(27.R9.)(1:.(27.R9.)(2:.+4.(23.R9.))))(3=.(?.$10.$10.)))R;.R5.)P,(38.Vsegs,R6.)(5>.(4?.(27.R;.)R>.)R7.R;.)")
(* [comment removed for export] *).
  Proof.
    jc_open. jb_open.
    intros hc LBc mc moc dXc An cnt ys m4 J F B EO HP4 MI4. pose proof B as [BA BS BL].
    pose proof (xj_facts _ _ _ _ _ _ J) as (HBR1 & HAP1 & ND1 & _ & XS & X0 & X16 & XAL & LEN1 & NR1 & OWN0 & OWN1).
    destruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI).
    pose proof F as [BR NEW NEWC APA ARR LEN CNT FXS].
    assert (NEA : An <> md_p dXc) by (destruct (APA _ _ XIN); lia).
    rewrite (lb_remove_cons_other (md_p dXc) An (4 * cnt) LBc NEA) in HP4.
    assert (NDc : List.NoDup (map fst LBc)) by (cbn in ND1; inversion ND1; assumption).
    assert (SUB : forall b, In b LBc -> (md_own dXc = LHeap -> b <> (md_p dXc, 4 * md_n dXc)) -> In b ((An, 4 * cnt) :: lb_remove (md_p dXc) LBc)).
    { intros [q k] Hb NE. right. eapply in_lb_remove_other; [exact NDc| exact XIN| exact Hb| exact (NE EO)]. }
    destruct (bj_client _ hc LBc mc moc dXc _ (SP - FS) J B SUB ltac:(lia)) as [C1 C2].
    pose proof (bj_facts _ _ _ B) as (B0 & B16 & BAL & LENB & NRB & BSK & OWNB0 & OWNB1).
    constructor; [| exact BS| exact BL].
    eapply opnd_at_heap_presx; [exact BA| exact HP4| exact (xj_mi _ _ _ _ _ _ J)| exact MI4| exact C1| exact C2| cbn; pose proof (BS EO); lia| intros BN; cbn; pose proof (BL EO BN); lia| | lia].
    intros b Hb. unfold mpd_blk in Hb. destruct (md_own dB) eqn:EOB; try (destruct Hb; fail). destruct Hb as [<-|[]].
    destruct (OWNB1 ltac:(discriminate)) as (_ & _ & _ & _ & _ & BIN). destruct (BIN eq_refl) as [_ BINc].
    eapply in_lb_remove_other; [exact NDc| exact XIN| exact BINc|]. intros E. injection E as E1 E2. pose proof (BL EO ltac:(discriminate)). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="JCX DBJ"] Lemma bj_fb_apart : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "Phc,(8.Vsegs,VL,VHI,)PLBc,(0.$1.)Pmc,P,(9.&40.)(:.(9.&8.))Pmoc,$;.PdXc,$2.PAn,$10.Pcnt,$10.Pys,(0.(9.&40.))P,(<.(3>.(?.$10.$10.)(29.$10.$10.R3.(2:.+4.R2.))(3=.(?.$10.$10.)))R8.R7.R6.R5.R4.)P,(45.R8.R4.R3.R2.R7.R5.)P,(5>.R9.R8.R6.)(=.(6.(19.(1:.(1;.VdB,)+10.)R6.)(19.(1:.R6.(2:.+4.R5.))(1;.VdB,)))P,(7.(1>.$24.(25.VdB,)$26.))(6.(19.(1:.R7.(2:.+4.R6.))(27.VdB,))(19.(1:.(27.VdB,)(2:.+4.(23.VdB,)))R7.)))")
(* [comment removed for export] *).
  Proof.
    jc_open. jb_open.
    intros hc LBc mc moc dXc An cnt ys J F B. pose proof B as [BA BS BL].
    pose proof F as [BR NEW NEWC APA ARR LEN CNT FXS]. pose proof BR as (An0 & An16 & _ & AnC & AnI). pose proof OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    pose proof (bj_facts _ _ _ B) as (B0 & B16 & BAL & LENB & NRB & BSK & OWNB0 & OWNB1).
    destruct (bj_client _ hc LBc mc moc dXc LBc lo J B ltac:(intros b Hb _; exact Hb) ltac:(lia)) as [C1 C2].
    split.
    - destruct (client_range_apart L LBc lo (md_addr dB) 16 An (4 * cnt) C1); try lia. exact APA.
    - intros BN. destruct (OWNB1 BN) as (N1 & P0 & BPAL & BBY & BSK' & BIN).
      pose proof (opnd_view _ _ _ _ _ BA) as [(_ & _ & _ & _ & _ & OW) _]. destruct (md_own dB); [exfalso; exact (BN eq_refl)| |].
      + destruct (BIN eq_refl) as [_ BINc]. exact (APA _ _ BINc).
      + destruct OW as (_ & _ & _ & _ & [BRO|[BSP _]]); [| left; lia]. pose proof (u32ro_bound _ _ _ _ BBY) as BB.
        pose proof (ROIMG (md_p dB + 0) (BRO 0 ltac:(lia)) ltac:(lia)) as I0.
        pose proof (ROIMG (md_p dB + (4 * md_n dB - 1)) (BRO (4 * md_n dB - 1) ltac:(lia)) ltac:(lia)) as I1. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="JCX DBJ"] Lemma bj_finish : ltac2:(CDefT.buildp (gd_tbl_MpiJourney ()) "Phd,(8.Vsegs,VL,VHI,)PLBd,(0.$1.)PAn,$10.Pcnt,$10.Pys,(0.(9.&40.))Pme,P,(9.&40.)(:.(9.&8.))Pmoe,$;.PdXc,$2.Pm5,P,(9.&40.)(:.(9.&8.))P,(4>.R9.R8.R7.R6.R5.R4.R3.R2.)P,(5>.R9.R5.R3.)P,(4;.(3>.(?.$10.$10.)(29.$10.$10.(1;.VdX,)(1:.(1;.VdX,)+10.))(3=.(?.$10.$10.)))R6.R3.)P,(4<.Vsegs,R7.R4.)(5>.(3>.(?.$10.$10.)(29.$10.$10.R;.(2:.+4.R:.))R<.)R5.(54.(1;.VdX,)(52.R6.)R:.R;.R9.(53.VdX,)$28.))")
(* [comment removed for export] *).
  Proof.
    jc_open. jb_open.
    intros hd LBd An cnt ys me moe dXc m5 D B MU WM. pose proof B as [BA BS BL].
    pose proof D as [MI4 ST4 FR4 HH4 HT4 MF4 SOK4 CX4 SG SUB KEEP GONE NEW APA ARR LEN CNT DXS HPX4 BR].
    pose proof BR as (An0 & An16 & _ & AnC & AnI). pose proof OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    pose proof (bj_facts _ _ _ B) as (B0 & B16 & BAL & LENB & NRB & BSK & OWNB0 & OWNB1).
    (* [comment removed for export] *)
    assert (CRB' : client_range L LBd lo (md_addr dB) 16).
    { intros a Ha. destruct (CRB a Ha) as [C|[C|([q k] & Hq & R)]]; [left; exact C| right; left; exact C| right; right].
      exists (q, k). split; [| exact R]. cbn in R. apply KEEP; [exact Hq|]. unfold mpd_blk. destruct (md_own dX) eqn:EO; try (intros []; fail).
      intros [E|[]]. injection E as E1 E2. pose proof (OB2 eq_refl). lia. }
    assert (BSA : md_addr dB + 16 <= An \/ An + 4 * cnt <= md_addr dB).
    { destruct (client_range_apart L LBd lo (md_addr dB) 16 An (4 * cnt) CRB'); try lia. exact APA. }
    assert (BLA : md_own dB <> LNull -> An + 4 * cnt <= md_p dB \/ md_p dB + 4 * md_n dB <= An).
    { intros BN. destruct (OWNB1 BN) as (N1 & P0 & BPAL & BBY & BSK' & BIN).
      pose proof (opnd_view _ _ _ _ _ BA) as [(_ & _ & _ & _ & _ & OW) _]. destruct (md_own dB); [exfalso; exact (BN eq_refl)| |].
      - destruct (BIN eq_refl) as [_ BINd]. exact (APA _ _ BINd).
      - destruct OW as (_ & _ & _ & _ & [BRO|[BSP _]]); [| left; lia]. pose proof (u32ro_bound _ _ _ _ BBY) as BB.
        pose proof (ROIMG (md_p dB + 0) (BRO 0 ltac:(lia)) ltac:(lia)) as I0.
        pose proof (ROIMG (md_p dB + (4 * md_n dB - 1)) (BRO (4 * md_n dB - 1) ltac:(lia)) ltac:(lia)) as I1. lia. }
    constructor; cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
    - eapply opnd_at_munch_any; [| exact MU| exact WM| cbn; lia| intros BN; cbn; pose proof (OB1 BN); lia].
      eapply opnd_at_blocks; [exact BA|]. intros b Hb. right. unfold mpd_blk in Hb.
      pose proof (opnd_view _ _ _ _ _ BA) as [(_ & _ & _ & _ & _ & OW) _]. destruct (md_own dB); try (destruct Hb; fail). destruct Hb as [<-|[]]. exact (proj1 (proj2 OW)).
    - intros _. lia.
    - intros _ BN. destruct (BLA BN); lia.
  Qed.

End J.
