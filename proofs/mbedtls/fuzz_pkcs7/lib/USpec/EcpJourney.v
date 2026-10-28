(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux Asn1AuxA AStep CellsX MpiCoreAux MpiWalkAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiJourney.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_mpi_free U_mpi_addsub U_ecp_mul_mod.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_EcpJourney () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "Corelib.Init.Datatypes.list"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_addr"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Journey.jst"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Journey.jtmp"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_free.mpi_free_stmt"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_written"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_static"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_stack"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_tp"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.const_at"; "RocqVerifyHarness.AgentSubmission.Spec.EcpFacts.lb_free_mpd"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.mpi_cells"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_free.mpi_free_X"; "RocqVerifyHarness.AgentSubmission.Lib.AEvt.aevtM"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "RocqVerifyHarness.AgentSubmission.U.U_ecp_mul_mod.mm_inv"].


Section Journey.
  Variable segs : list Segment.
  Variable L : heap_layout.
  Variable HI : heap_iface segs L.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HND : forall h LB m mo, HEAP segs L HI h LB m mo -> List.NoDup (map fst LB).

  Definition jst (h : HST segs L HI) (LB : list blk) (SP FR : Z) (XO : list ivl) (MC lo : Z) (m : mem) (mo : Model)
      (hk : HST segs L HI) (LBk : list blk) (mk : mem) (mok : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_EcpJourney ()) "(0.(1.Vsegs,VL,VHI,O4.O3.O2.O1.)(0.Pb,$2.P,(3.$2.R1.O<.)(3.$2.R2.O3.)(0.(4.Vsegs,VL,O<.O;.O9.O6.O2.)(0.(5.Vsegs,VL,O2.)(0.(6.Vsegs,O2.)(0.(7.O5.O1.)(0.(8.$9.(:.Vsegs,VL,VHI,O4.)(:.Vsegs,VL,VHI,O=.))(0.(;.(<.&40.)Lc,(<.&40.)(=.Vsegs,O2.O8.(>.$?.(10.R1.)(11.$?.))))(12.Vsegs,O2.O7.(13.O;.O:.))))))))))")
(* [comment removed for export] *).

  Definition jtmp (LB LBk : list blk) (mk : mem) (A : Z) (d : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_EcpJourney ()) "(0.(14.Vsegs,O3.O4.O1.)(0.(8.$9.(15.O1.)O2.)(0.(16.(8.$17.(18.O1.)$19.))Pb,$2.P,(3.$2.R1.(1:.O1.))(16.(3.$2.R2.O5.)))))")
(* [comment removed for export] *).

  #[using="Type"] Lemma j_nodup_fst_neq : ltac2:(CDefT.buildp (gd_tbl_EcpJourney ()) "PLB,(1;.$2.)PB,$9.Pk,$9.PP,$9.Pj,$9.P,(1<.$9.(1=.(1>.$9.$9.)$9.(1?.$9.$9.)R5.))P,(3.(1>.$9.$9.)(20.$9.$9.R5.R4.)R6.)P,(3.(1>.$9.$9.)(20.$9.$9.R4.R3.)R7.)P,(16.(8.(1>.$9.$9.)(20.$9.$9.R7.R6.)(20.$9.$9.R5.R4.)))(16.(8.$9.R8.R6.))")
(* [comment removed for export] *).
  Proof.
    induction LB as [|x r IH]; cbn; intros B k P j ND H1 H2 NE; [destruct H1|].
    apply List.NoDup_cons_iff in ND as [NI ND].
    destruct H1 as [->|H1]; destruct H2 as [E|H2].
    - congruence.
    - cbn in NI. intros ->. apply NI. apply in_map_iff. exists (P, j). auto.
    - subst x. cbn in NI. intros ->. apply NI. apply in_map_iff. exists (P, k). auto.
    - exact (IH _ _ _ _ ND H1 H2 NE).
  Qed.

  #[using="Type"] Lemma mpd_blk_single : forall d b, In b (mpd_blk d) -> mpd_blk d = [b] /\ md_own d = LHeap /\ b = (md_p d, 4 * md_n d).
  Proof. intros d b H. unfold mpd_blk in *. destruct (md_own d); [destruct H| | destruct H]. destruct H as [<-|[]]. auto. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma j_out_stack : ltac2:(CDefT.buildp (gd_tbl_EcpJourney ()) "Ph,(21.Vsegs,VL,VHI,)PLB,(1;.$2.)Pm,P,(<.&40.)(22.(<.&8.))Pmo,$23.PSP,$9.Plo,$9.Pa,$9.Plo',$9.Phi',$9.P,(1.Vsegs,VL,VHI,R9.R8.R7.R6.)P,(24.(25.VL,)R5.)P,(24.(26.VL,)(25.VL,))P,(27.VL,R;.R8.R6.)P,(24.R8.R6.)P,(24.R6.R:.)(16.(0.(24.R8.R9.)(28.R9.R7.)))")
(* [comment removed for export] *).
  Proof.
    intros h LB m mo SP lo a lo' hi' HH ACL DHI HC H1 H2 C. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
    destruct HC as [X|[X|([B j] & Hb & X)]]; [lia| lia|].
    pose proof (proj1 (Forall_forall _ _) HBR _ Hb) as (_ & _ & _ & B4 & _). cbn in X, B4. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="DIMG"] Lemma j_out_blk : ltac2:(CDefT.buildp (gd_tbl_EcpJourney ()) "Phh,(21.Vsegs,VL,VHI,)PLBB,(1;.$2.)Pmm,P,(<.&40.)(22.(<.&8.))Pmmo,$23.PLB,(1;.(1>.$9.$9.))PSP,$9.Pa,$9.PP,$9.Pk,$9.P,(1.Vsegs,VL,VHI,R9.R8.R7.R6.)P,(3.(1>.$9.$9.)(20.$9.$9.R3.R2.)R9.)P,(16.(3.(1>.$9.$9.)(20.$9.$9.R4.R3.)R7.))P,Pb,(1>.$9.$9.)P,(3.(1>.$9.$9.)R1.R9.)(3.(1>.$9.$9.)R2.R=.)P,(28.=R5.)P,(24.(25.VL,)R9.)P,(27.VL,R;.R:.R9.)(16.(0.(24.R9.R:.)(28.R:.(29.R9.R8.))))")
(* [comment removed for export] *).
  Proof.
    intros hh LBB mm mmo LB SP a P k HH IN NIN SUB Hk ACL HC C. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR HAP].
    destruct HC as [X|[X|([B j] & Hb & X)]].
    - pose proof (proj1 (Forall_forall _ _) HBR _ IN) as (_ & _ & _ & B4 & _). cbn in B4. lia.
    - exact (blk_off_data segs L HI DIMG _ _ _ _ _ _ a HH IN (proj1 X) C).
    - cbn in X. assert (NE : (B, j) <> (P, k)) by (intros E; rewrite E in Hb; exact (NIN Hb)).
      destruct (blocks_apart_neq _ _ _ HAP (SUB _ Hb) IN NE ltac:(cbn; lia) ltac:(cbn; lia)) as [D|D]; cbn in D; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma j_blk_apart : ltac2:(CDefT.buildp (gd_tbl_EcpJourney ()) "Phh,(21.Vsegs,VL,VHI,)PLBB,(1;.$2.)Pmm,P,(<.&40.)(22.(<.&8.))Pmmo,$23.PP,$9.Pk,$9.PB,$9.Pj,$9.P,(1.Vsegs,VL,VHI,R8.R7.R6.R5.)P,(3.(1>.$9.$9.)(20.$9.$9.R5.R4.)R8.)P,(3.(1>.$9.$9.)(20.$9.$9.R4.R3.)R9.)P,(16.(8.(1>.$9.$9.)(20.$9.$9.R7.R6.)(20.$9.$9.R5.R4.)))P,(28.=R7.)P,(28.=R6.)(2:.(24.(29.R:.R9.)R8.)(24.(29.R8.R7.)R:.))")
(* [comment removed for export] *).
  Proof.
    intros hh LBB mm mmo P k B j HH I1 I2 NE Hk Hj. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [_ HAP].
    destruct (blocks_apart_neq _ _ _ HAP I1 I2 NE ltac:(cbn; lia) ltac:(cbn; lia)) as [D|D]; cbn in D; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="DIMG"] Lemma j_blk_MC : ltac2:(CDefT.buildp (gd_tbl_EcpJourney ()) "Ph,(21.Vsegs,VL,VHI,)PLB,(1;.$2.)Pm,P,(<.&40.)(22.(<.&8.))Pmo,$23.Pp,$9.Pk,$9.PMC,$9.P,(1.Vsegs,VL,VHI,R7.R6.R5.R4.)P,(3.(1>.$9.$9.)(20.$9.$9.R4.R3.)R7.)P,(28.=R4.)P,(24.(2;.VL,)R4.)P,(24.(29.R5.+8.)(26.VL,))(2:.(24.(29.R8.R7.)R6.)(24.(29.R6.+8.)R8.))")
(* [comment removed for export] *).
  Proof.
    intros h LB m mo p k MC HH IN Hk MC1 MC2. destruct (Z_le_dec (p + k) MC); [left; lia|]. destruct (Z_le_dec (MC + 8) p); [right; lia|]. exfalso.
    apply (blk_off_data segs L HI DIMG _ _ _ _ _ _ (Z.max p MC) HH IN); lia.
  Qed.

  #[using="Type"] Lemma jst_step : ltac2:(CDefT.buildp (gd_tbl_EcpJourney ()) "Ph,(21.Vsegs,VL,VHI,)PLB,(1;.$2.)PSP,$9.PFR,$9.PXO,(1;.$2<.)PMC,$9.Plo,$9.Pm,P,(<.&40.)(22.(<.&8.))Pmo,$23.Phk,(21.Vsegs,VL,VHI,)PLBk,(1;.$2.)Pmk,P,(<.&40.)(22.(<.&8.))Pmok,$23.Phk',(21.Vsegs,VL,VHI,)PLBk',(1;.$2.)Pmk',P,(<.&40.)(22.(<.&8.))Pmok',$23.PLBX,(1;.$2.)PSPX,$9.PXs,(1;.$2<.)P,(2=.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)P,(24.R3.R13.)P,(1.Vsegs,VL,VHI,R9.R8.R7.R6.)P,Pb,$2.P,(3.$2.R1.R17.)(3.$2.R2.R;.)P,(4.Vsegs,VL,R7.R6.R5.R=.R9.)P,Pb,$2.P,(3.$2.R1.R19.)(3.$2.R2.R:.)P,Pa,$9.P,(0.(24.=R1.)(28.R1.(2>.+2.+40.)))P,(27.VL,R1;.R1:.R2.)P,(2?.R19.R3.)(2?.R;.R4.)P,(5.Vsegs,VL,R<.)P,(6.Vsegs,R=.)P,(7.R11.R=.)P,(8.$9.(:.Vsegs,VL,VHI,R11.)(:.Vsegs,VL,VHI,R15.))P,(;.(<.&40.)Lc,(<.&40.)(=.Vsegs,R11.R1;.(>.$?.(10.R1.)(11.$?.))))P,(12.Vsegs,R11.R1:.(13.R1>.R1=.))(2=.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R14.R13.R12.R11.)")
(* [comment removed for export] *).
  Proof.
    intros until Xs. intros (HHk & SUBk & PXk & SOKk & MIk & MFk & HTk & CNTk & STk) LEX HH' SUB' PX SUBX OUT SOK' MI' MF' HT' CNT' ST'.
    unfold jst. refine (conj HH' (conj SUB' (conj _ (conj SOK' (conj MI' (conj _ (conj _ (conj CNT' ST')))))))).
    - eapply heap_presx_trans; [exact PXk|]. intros a Ha HC HO. apply PX; [exact Ha| | exact (OUT a Ha HC HO)].
      destruct HC as [X|[X|(b & Hb & X)]]; [left; lia| right; left; exact X| right; right; exists b; split; [exact (SUBX _ Hb)| exact X]].
    - eapply mo_frame_trans; [exact MFk| exact MF'].
    - rewrite HT'. exact HTk.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma jst_mpd : ltac2:(CDefT.buildp (gd_tbl_EcpJourney ()) "Ph,(21.Vsegs,VL,VHI,)PLB,(1;.$2.)PSP,$9.PFR,$9.PXO,(1;.$2<.)PMC,$9.Plo,$9.Pm,P,(<.&40.)(22.(<.&8.))Pmo,$23.Phk,(21.Vsegs,VL,VHI,)PLBk,(1;.$2.)Pmk,P,(<.&40.)(22.(<.&8.))Pmok,$23.Pd,$30.P,(2=.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(6.Vsegs,R8.)P,(14.Vsegs,R9.R?.R3.)P,(31.VL,R10.R?.(15.R4.)+10.)P,(32.R>.(15.R5.)+10.)P,P,(8.$17.(18.R6.)$33.)(32.R10.(34.R7.)(35.+4.(36.R7.)))(14.Vsegs,R9.R:.R7.)")
(* [comment removed for export] *).
  Proof.
    intros until d. intros (HHk & SUBk & PXk & SOKk & MIk & _) MI MD CR DX DL.
    split; [| exact (proj2 MD)]. apply (mpdr_at_LB_one segs) with (LB := LB).
    - eapply (mpdr_at_presx segs L); [exact (proj1 MD)| exact PXk| exact MI| exact MIk| exact CR| exact DX|].
      intros O. pose proof (proj1 MD) as (_ & _ & _ & _ & _ & HO). rewrite O in HO. destruct HO as (_ & IN & _). exact (conj IN (DL O)).
    - intros O. pose proof (proj1 MD) as (_ & _ & _ & _ & _ & HO). rewrite O in HO. destruct HO as (_ & IN & _). exact (SUBk _ IN).
  Qed.

  #[using="Type"] Lemma jtmp_presx : ltac2:(CDefT.buildp (gd_tbl_EcpJourney ()) "PLB,(1;.$2.)PLBk,(1;.$2.)PLBX,(1;.$2.)PLBk',(1;.(1>.$9.$9.))Pmk,P,(<.&40.)(22.(<.&8.))Pmk',P,(<.&40.)(22.(<.&8.))PSP',$9.PXs,(1;.$2<.)PA,$9.Pe,$30.P,(37.R:.R9.R6.R2.R1.)P,(4.Vsegs,VL,R9.R5.R4.R7.R6.)P,(6.Vsegs,R8.)P,(6.Vsegs,R8.)P,(31.VL,R<.R8.R6.+10.)P,(32.R8.R7.+10.)P,P,(8.$17.(18.R7.)$33.)(0.(3.(1>.$9.$9.)(20.$9.$9.(34.R8.)(35.+4.(36.R8.)))R?.)(0.(3.(1>.$9.$9.)(20.$9.$9.(34.R8.)(35.+4.(36.R8.)))R>.)(32.R:.(34.R8.)(35.+4.(36.R8.)))))(37.R11.R>.R<.R9.R8.)")
(* [comment removed for export] *).
  Proof.
    intros LB LBk LBX LBk' mk mk' SP' Xs A e (ME & EA & NS & FRS) PX MI MI' CR DX HL.
    refine (conj _ (conj EA (conj NS FRS))). split; [| exact (proj2 ME)].
    apply (mpdr_at_LB_one segs) with (LB := LBX); [| intros O; exact (proj1 (proj2 (HL O)))].
    eapply (mpdr_at_presx segs L); [exact (proj1 ME)| exact PX| exact MI| exact MI'| rewrite EA; exact CR| rewrite EA; exact DX| intros O; destruct (HL O) as (X1 & _ & X3); exact (conj X1 X3)].
  Qed.

  #[using="Type"] Lemma jtmp_blk : ltac2:(CDefT.buildp (gd_tbl_EcpJourney ()) "Phk,(21.Vsegs,VL,VHI,)PLB,(1;.$2.)PLBk,(1;.$2.)Pmk,P,(<.&40.)(22.(<.&8.))Pmok,$23.PA,$9.Pe,$30.P,(1.Vsegs,VL,VHI,R7.R5.R4.R3.)P,(37.R7.R6.R5.R3.R2.)P,(8.$17.(18.R3.)$33.)(0.(3.(1>.$9.$9.)(20.$9.$9.(34.R4.)(35.+4.(36.R4.)))R8.)(0.(24.+1.(36.R4.))(0.(28.=(34.R4.))(0.(24.(29.(34.R4.)(35.+4.(36.R4.)))(25.VL,))(16.(3.(1>.$9.$9.)(20.$9.$9.(34.R4.)(35.+4.(36.R4.)))R9.))))))")
(* [comment removed for export] *).
  Proof.
    intros hk LB LBk mk mok A e HH (ME & _ & _ & FRS) O. destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
    destruct (mpdr_blk_facts segs L mk LBk e (proj1 ME) O HBR) as (I1 & I2 & I3 & I4 & _).
    refine (conj I1 (conj I2 (conj I3 (conj I4 _)))). apply FRS. unfold mpd_blk. rewrite O. left; reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="DIMG HND"] Lemma jst_free : ltac2:(CDefT.buildp (gd_tbl_EcpJourney ()) "PFREE,$9.PMSF,$9.Ph,(21.Vsegs,VL,VHI,)PLB,(1;.$2.)PSP,$9.PFR,$9.PXO,(1;.$2<.)PMC,$9.Plo,$9.Pm,P,(<.&40.)(22.(<.&8.))Pmo,$23.Phk,(21.Vsegs,VL,VHI,)PLBk,(1;.$2.)Pmk,P,(<.&40.)(22.(<.&8.))Pmok,$23.Pd,$30.PRET,$9.PSP',$9.Pgp,(<.&40.)Ptp,(<.&40.)Pt0,(<.&40.)Pt1,(<.&40.)Pt2,(<.&40.)Ps0,(<.&40.)Ps1,(<.&40.)Pa0,(<.&40.)Pa1,(<.&40.)Pa2,(<.&40.)Pa3,(<.&40.)Pa4,(<.&40.)Pa5,(<.&40.)Pa6,(<.&40.)Pa7,(<.&40.)Ps2,(<.&40.)Ps3,(<.&40.)Ps4,(<.&40.)Ps5,(<.&40.)Ps6,(<.&40.)Ps7,(<.&40.)Ps8,(<.&40.)Ps9,(<.&40.)Ps10,(<.&40.)Ps11,(<.&40.)Pt3,(<.&40.)Pt4,(<.&40.)Pt5,(<.&40.)Pt6,(<.&40.)PF,(38.&5.(<.&40.))Pfc,(<.&20.)PQ',P,$39.SpP,(3:.Vsegs,VL,VHI,R32.R31.)P,(8.$9.R22.(13.R2?.R2>.))P,(2=.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.)P,(24.=R30.)P,(1.Vsegs,VL,VHI,R34.R33.R2=.R2<.)P,(37.R34.R2;.R2:.(15.R28.)R28.)P,(3;.VL,R2<.(13.R34.R33.)(:.Vsegs,VL,VHI,R36.)(15.R29.)+10.)P,Pb,$2.Pa,$9.P,(3.$2.R2.R2?.)P,(0.(24.(15.R2=.)R2.)(28.R2.(29.(15.R2=.)+10.)))P,(0.(24.(1?.$9.$9.R4.)R3.)(28.R3.(29.(1?.$9.$9.R4.)(3<.$9.$9.R4.))))(3.$2.R5.R3;.)P,Pa,$9.P,(0.(24.(15.R2<.)R1.)(28.R1.(29.(15.R2<.)+10.)))P,(0.(24.(2;.VL,)R2.)(28.R2.(26.VL,)))(3=.VL,R3.)P,(2:.(24.(29.R34.+8.)(15.R2<.))(24.(29.(15.R2<.)+10.)R34.))P,(24.(2;.VL,)R35.)P,(24.(29.R36.+8.)(26.VL,))P,Pa,$9.P,(0.(24.R38.R1.)(28.R1.(29.R38.+8.)))(0.(16.(3>.VL,R2.))(3=.VL,R2.))P,Pa,$9.P,(0.(24.=R1.)(28.R1.(2>.+2.+40.)))P,(27.VL,R3>.R3=.R2.)P,(2?.R3<.R3.)(16.(0.(24.(15.R34.)R4.)(28.R4.(29.(15.R34.)+10.))))P,(24.R38.(13.(13.(13.R3<.R3;.)+20.)(3?.VL,)))P,(24.=(3?.VL,))P,(24.(25.VL,)R3:.)P,(24.R3?.(:.Vsegs,VL,VHI,R41.))P,(8.$9.(40.(13.R40.R3?.)+10.)=)P,(24.(26.VL,)(25.VL,))P,(8.(<.&40.)R33.(41.&40.(42.VL,)))P,(43.VL,R46.+8.)P,(28.R44.(2>.+2.+40.))P,(0.(24.=R39.)(28.R39.(2>.+2.+40.)))P,(8.$9.(40.R3:.+2.)=)P,(8.(<.&40.)R32.(41.&40.(15.R3<.)))P,Pmk',P,(<.&40.)(22.(<.&8.))Pmok',$23.Phk',(21.Vsegs,VL,VHI,)Pt0',(<.&40.)Pt1',(<.&40.)Pt2',(<.&40.)Pa0',(<.&40.)Pa1',(<.&40.)Pa2',(<.&40.)Pa3',(<.&40.)Pa4',(<.&40.)Pa5',(<.&40.)Pa6',(<.&40.)Pa7',(<.&40.)Pt3',(<.&40.)Pt4',(<.&40.)Pt5',(<.&40.)Pt6',(<.&40.)P,(2=.R5<.R5;.R5:.R59.R58.R57.R56.R55.R54.R10.(44.R4?.R52.)R12.R11.)P,(=.Vsegs,R13.(15.R50.)(45.=(41.&40.+1.)=(46.R50.)))P,(4.Vsegs,VL,(44.R51.R54.)(13.R5<.R5;.)(>.(1>.$9.$9.)(20.$9.$9.(15.R51.)(29.(15.R51.)+10.))(47.(18.R51.)(34.R51.)(36.R51.)))R53.R14.)P,P,(8.$17.(18.R52.)$33.)(0.(3.(1>.$9.$9.)(20.$9.$9.(34.R53.)(35.+4.(36.R53.)))R56.)(0.(24.+1.(36.R53.))(0.(28.=(34.R53.))(0.(24.(29.(34.R53.)(35.+4.(36.R53.)))(25.VL,))(16.(3.(1>.$9.$9.)(20.$9.$9.(34.R53.)(35.+4.(36.R53.)))R5?.))))))P,(6.Vsegs,R55.)(48.Vsegs,R16.R32.(49.(4:.(41.&40.R53.)(41.&40.R52.)R51.R50.R14.R13.R12.R4<.R4;.R11.R10.R?.R>.R=.R<.R;.R:.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R9.R8.R7.R6.)R34.(41.&40.R53.)R33.(4;.(<.&40.))R17.(4<.Vsegs,)))(48.Vsegs,R3?.R1<.(49.(4:.(41.&40.R3=.)(41.&40.R3<.)R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R1>.(41.&40.R4=.)R1=.(4;.(<.&40.))R40.(4<.Vsegs,)))")
(* [comment removed for export] *).
  Proof.
    intros until Q'. intros SF ESP STK FR0 HH TMP CW CWB WD AMC MC1 MC2 MCS OUTA SLO HLS ACL HTOP SPA DHI TP CA SPU HR HRE -> K. pose proof alloc_ceiling_pos as ACP. subst SP'.
    pose proof STK as (HHk & SUBk & PXk & SOKk & MIk & MFk & HTk & [ck CNTk] & STk). pose proof TMP as (MD & _ & NS & FRS).
    pose proof (HND _ _ _ _ HHk) as NDk. destruct (heap_blocks _ _ HI _ _ _ _ HHk) as [HBRk HAPk].
    pose proof (jtmp_blk hk LB LBk mk mok _ d HHk TMP) as BL.
    pose proof (heap_mok _ _ HI _ _ _ _ HHk) as MK.
    assert (LO0 : 0 <= lo) by (destruct STk as [? _]; assumption).
    assert (SUB' : forall b, In b LB -> In b (lb_free_mpd d LBk)).
    { intros [B k] Hb. apply lb_free_mpd_keep; [exact (SUBk _ Hb)|]. intros O.
      eapply (j_nodup_fst_neq LBk); [exact NDk| exact (SUBk _ Hb)| exact (proj1 (BL O))|].
      intros E. apply (FRS (B, k)); [| exact Hb]. unfold mpd_blk. rewrite O, E. left; reflexivity. }
    assert (CW' : client_wrange L (lb_free_mpd d LBk) (SP - FR) (heap_top segs L HI hk) (md_addr d) 16).
    { rewrite HTk. intros a Ha. destruct (CW a Ha) as [C|[C|([B k] & Hb & R)]]; [left; exact C| right; left; exact C| right; right].
      exists (B, k). split; [| exact R]. apply SUB'. exact (CWB _ a Hb Ha R). }
    assert (AP : md_own d = LHeap -> md_addr d + 16 <= md_p d \/ md_p d + 4 * md_n d <= md_addr d).
    { intros O. destruct (BL O) as (IN & N1 & P0 & B4 & NIN).
      destruct (Z_le_dec (md_addr d + 16) (md_p d)); [left; lia|]. destruct (Z_le_dec (md_p d + 4 * md_n d) (md_addr d)); [right; lia|]. exfalso.
      set (a := Z.max (md_addr d) (md_p d)).
      assert (Ha : md_addr d <= a < md_addr d + 16) by lia. assert (Hp : md_p d <= a < md_p d + 4 * md_n d) by lia.
      destruct (CW a Ha) as [C|[C|([B k] & Hb & R)]]; [lia| |].
      - pose proof (proj1 (Forall_forall _ _) HBRk _ IN) as (_ & _ & _ & _ & B5). cbn in B5. destruct DIMG. lia.
      - cbn in R. destruct (blk_eq_dec (B, k) (md_p d, 4 * md_n d)) as [E|NE].
        + apply NIN. rewrite <- E. exact (CWB _ a Hb Ha R).
        + destruct (blocks_apart_neq _ _ _ HAPk Hb IN NE ltac:(cbn; lia) ltac:(cbn; lia)) as [D|D]; cbn in D; lia. }
    unfold mpi_free_stmt in SF.
    eapply aevtM_cut.
    { pose proof MD as [MA _]. unfold mpdr_at in MA.
      eapply SF with (lo := lo) (h := hk) (LB := LBk); rewrite ?(unsigned_lit (SP - FR)), ?HTk by lia;
        first [ exact HHk | exact MA | exact NS | exact TP | exact MIk | exact SOKk | exact CA | exact DHI | exact STk | exact WD | exact SPA | exact AP | reflexivity
              | match goal with |- client_wrange _ _ _ _ _ _ => rewrite <- HTk; exact CW' end
              | lia ]. }
    clear SF. cbv beta. intros ms' mo' PO. unfold mpi_free_post in PO.
    destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mk' & mok' & hk' & E & PO). injection E as -> ->.
    rewrite ?(unsigned_lit (SP - FR)) in PO by lia.
    destruct PO as (MI' & ST' & MF' & HT' & HH' & CH' & PX' & SOK').
    change (mpi_free_LB _ _ _ LBk) with (lb_free_mpd d LBk) in HH', PX'.
    rewrite (ret_pc_even RET HR HRE).
    eapply K; [| exact CH'| exact PX'| exact BL| exact MIk].
    eapply jst_step with (SPX := SP - FR); [exact STK| lia| exact HH'| exact SUB'| exact PX'| exact SUB'| | exact SOK'| exact MI'| exact MF'| exact HT'| | exact ST'].
    - intros a Ha HC HO. cbn. split.
      + exact (OUTA a Ha HC HO).
      + unfold mpi_free_X. destruct (md_own d) eqn:O; cbn; [exact I| | exact I]. split; [| exact I].
        destruct (BL eq_refl) as (IN & N1 & _ & _ & NIN).
        eapply (j_out_blk hk LBk mk mok LB SP a); [exact HHk| exact IN| exact NIN| exact SUBk| lia| lia| exact HC].
    - exists ck. eapply heap_presx_rw_cells; [exact PX'| exact CNTk| cbn; intros a Ha; right; left; split; [lia| apply MCS; lia]|].
      cbn. split; [lia|]. unfold mpi_free_X. destruct (md_own d) eqn:O; cbn; [exact I| | exact I]. split; [| exact I].
      destruct (BL eq_refl) as (IN & N1 & _). pose proof (j_blk_MC hk LBk mk mok _ _ MC HHk IN ltac:(lia) MC1 MC2). lia.
  all: match goal with |- ?gg => idtac "FREELEFT" gg end.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma jst_prefix : ltac2:(CDefT.buildp (gd_tbl_EcpJourney ()) "Ph,(21.Vsegs,VL,VHI,)PLB,(1;.$2.)PSP,$9.PFR,$9.PXO,(1;.$2<.)PMC,$9.Plo,$9.Pm,P,(<.&40.)(22.(<.&8.))Pmo,$23.Pm1,P,(<.&40.)(22.(<.&8.))Pcnt,(<.&40.)P,(1.Vsegs,VL,VHI,R;.R:.R4.R3.)P,(4=.(>.(1>.$9.$9.)(20.$9.$9.R6.R:.)(11.(1>.$9.$9.)))R5.R3.)P,(4>.Vsegs,R6.R4.)P,(6.Vsegs,R5.)P,(5.Vsegs,VL,R8.)P,(=.Vsegs,R9.R;.(>.$?.(10.R6.)(11.$?.)))P,(24.(29.R<.+8.)(26.VL,))P,(24.(26.VL,)(25.VL,))P,(24.(25.VL,)R=.)P,(24.R>.(13.R12.R11.))P,(24.R13.(:.Vsegs,VL,VHI,R15.))P,(12.Vsegs,R=.R10.(13.R14.R13.))(2=.R17.R16.R15.R14.R13.R12.R11.R10.R?.R17.R16.R>.R?.)")
(* [comment removed for export] *).
  Proof.
    intros h LB SP FR XO MC lo m mo m1 cnt HH MU WM MI1 SOK CNT MC2 DHI ACL SLO HTOP ST1. pose proof alloc_ceiling_pos as ACP.
    destruct (heap_blocks _ _ HI _ _ _ _ HH) as [HBR _].
    unfold jst. refine (conj _ (conj (fun b Hb => Hb) (conj _ (conj _ (conj MI1 (conj (mo_frame_refl mo) (conj eq_refl (conj _ ST1)))))))).
    - apply (@HEAP_munch segs L HI h _ m m1 mo _ lo HH MU WM ACL). intros a Ha NO. cbn in NO. left. lia.
    - eapply heap_presx_frame; [exact MU| exact WM| exact HBR| exact DHI| lia].
    - eapply statics_ok_munch; [exact SOK| exact MU| intros a Ha _; cbn; lia].
    - exists cnt. eapply rw_cells_transport; [exact CNT| exact MU| exact WM| cbn; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="DIMG"] Lemma jst_munch : ltac2:(CDefT.buildp (gd_tbl_EcpJourney ()) "Ph,(21.Vsegs,VL,VHI,)PLB,(1;.$2.)PSP,$9.PFR,$9.PXO,(1;.$2<.)PMC,$9.Plo,$9.Pm,P,(<.&40.)(22.(<.&8.))Pmo,$23.Phk,(21.Vsegs,VL,VHI,)PLBk,(1;.$2.)Pmk,P,(<.&40.)(22.(<.&8.))Pmok,$23.Pmk',P,(<.&40.)(22.(<.&8.))PW,(1;.$2<.)P,(2=.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R4.R3.)P,(1.Vsegs,VL,VHI,R10.R?.R9.R8.)P,(24.=R>.)P,(4=.R4.R7.R5.)P,(4>.Vsegs,R8.R6.)P,(6.Vsegs,R7.)P,(12.Vsegs,R8.R?.(13.R13.R12.))P,Pa,$9.P,(16.(2?.R9.R1.))(2:.(0.(24.R12.R2.)(28.R2.(13.R16.R15.)))(;.$9.LP,$9.(;.$9.Lk,$9.(0.(3.(1>.$9.$9.)(20.$9.$9.R2.R1.)R10.)(0.(16.(3.(1>.$9.$9.)(20.$9.$9.R2.R1.)R19.))(0.(24.R2.R4.)(28.R4.(29.R2.R1.))))))))P,(32.R9.R12.+8.)P,(24.(25.VL,)R12.)P,(24.R13.(13.R17.R16.))P,(24.(26.VL,)(25.VL,))P,(24.R19.(:.Vsegs,VL,VHI,R1;.))P,(24.(29.R17.+8.)(26.VL,))(2=.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R10.R11.)")
(* [comment removed for export] *).
  Proof.
    intros until W. intros STK HH FR0 MU WM MI' ST' HW DW ACL SLO DHI HTOP MC2. pose proof alloc_ceiling_pos as ACP.
    pose proof STK as (HHk & SUBk & PXk & SOKk & MIk & MFk & HTk & [ck CNTk] & STk).
    destruct (heap_blocks _ _ HI _ _ _ _ HHk) as [HBRk HAPk].
    assert (LO0 : 0 <= lo) by (destruct STk as [? _]; assumption).
    assert (OW : forall a, 0 <= a < 2^64 -> client_addr L LB SP a -> outside W a).
    { intros a Ha HC. destruct (outside_dec W a) as [O|NO]; [exact O|]. exfalso. destruct (HW a NO) as [X|(P & k & IN & NIN & X)].
      - exact (j_out_stack h LB m mo SP lo a lo (SP - FR) HH ACL DHI HC ltac:(lia) ltac:(lia) X).
      - exact (j_out_blk hk LBk mk mok LB SP a P k HHk IN NIN SUBk ltac:(lia) ltac:(lia) HC X). }
    unfold jst. refine (conj _ (conj SUBk (conj _ (conj _ (conj MI' (conj MFk (conj HTk (conj _ ST')))))))).
    - apply (@HEAP_munch segs L HI hk _ mk mk' mok _ lo HHk MU WM ACL). intros a Ha NO.
      destruct (HW a NO) as [X|(P & k & IN & NIN & X)]; [left; rewrite HTk; lia| right; right; exists (P, k); split; [exact IN| cbn; lia]].
    - eapply heap_presx_trans; [exact PXk|]. eapply heap_presx_of_munch; [exact MU| exact WM|]. intros a Ha HC _. exact (OW a Ha HC).
    - eapply statics_ok_munch; [exact SOKk| exact MU|]. intros a Ha _. destruct (outside_dec W a) as [O|NO]; [exact O|]. exfalso.
      destruct (HW a NO) as [X|(P & k & IN & NIN & X)]; [lia|].
      exact (blk_off_data segs L HI DIMG _ _ _ _ _ _ a HHk IN ltac:(lia) X).
    - exists ck. eapply rw_cells_transport; [exact CNTk| exact MU| exact WM| exact DW].
  Qed.

  (* [comment removed for export] *)
  #[using="DIMG"] Lemma jst_of_mm : ltac2:(CDefT.buildp (gd_tbl_EcpJourney ()) "PMT,(1;.$4?.)Ph,(21.Vsegs,VL,VHI,)PLB,(1;.$2.)PSP,$9.PFR,$9.PXO,(1;.$2<.)PMC,$9.Plo,$9.Pm,P,(<.&40.)(22.(<.&8.))Pmo,$23.PhO,(21.Vsegs,VL,VHI,)PLBO,(1;.$2.)PmO,P,(<.&40.)(22.(<.&8.))PmoO,$23.PdYO,$30.PG,$9.Pg,$50.PhS,(21.Vsegs,VL,VHI,)PLBS,(1;.$2.)PdYS,$30.PmS,P,(<.&40.)(22.(<.&8.))PmoS,$23.P,(2=.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.)P,(37.R15.R<.R;.(15.R9.)R9.)P,(51.Vsegs,VL,VHI,R18.R>.R=.R:.R9.R8.R12.R15.R14.R11.R<.R;.R7.R6.R5.R4.R3.)P,(1.Vsegs,VL,VHI,R18.R17.R11.R10.)P,(24.=R16.)P,(24.(25.VL,)R14.)P,(24.R15.(13.R19.R18.))P,(24.(26.VL,)(25.VL,))P,Pa,$9.P,(0.(24.=R1.)(28.R1.(2>.+2.+40.)))P,(27.VL,R1>.R1=.R2.)P,(2?.R1<.R3.)(0.(16.(0.(24.(15.R14.)R4.)(28.R4.(29.(15.R14.)+10.))))(16.(0.(24.R1<.R4.)(28.R4.(29.R1<.+8.)))))(0.(2=.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R>.R=.R;.R:.)(0.(37.R1=.R=.R;.(15.R11.)R<.)(0.(8.(<.&40.)(46.R<.)(46.R11.))(0.(24.(36.R11.)(36.R<.))Pb,$2.P,(3.$2.R1.R>.)(2:.(3.$2.R2.R16.)(3.$2.R2.(1:.R>.)))))))")
(* [comment removed for export] *).
  Proof.
    intros until moS. intros STO TY INV HH FR0 ACL SLO DHI OXO. pose proof alloc_ceiling_pos as ACP.
    pose proof STO as (HHO & SUBO & PXO & SOKO & MIO & MFO & HTO & CNTO & STO'). pose proof TY as (MAO & _ & NSO & FRO).
    pose proof INV as (HHS & MAS & OUTS & FRS & PADS & NLES & PXS & SOKS & MIS & MFS & HTS & GRS & CNTS & STS).
    pose proof OUTS as (EAS & NSS & K1 & K2 & K3).
    assert (SUBS : forall b, In b LB -> In b LBS).
    { intros b Hb. apply K2; [exact (SUBO _ Hb)|]. intros HX. exact (FRO _ HX Hb). }
    split; [| split; [| exact (conj PADS (conj NLES K1))]].
    - eapply jst_step; [exact STO| apply Z.le_refl| exact HHS| exact SUBS| exact PXS| exact SUBO| | exact SOKS| exact MIS| exact MFS| exact HTS| exact CNTS| exact STS].
      intros a Ha HC HO. destruct (OXO a Ha HC HO) as [O1 O2]. rewrite outside_app. split; [| cbn; split; [exact O2| exact I]].
      unfold mpd_ivs. cbn. split; [exact O1|]. destruct (md_own dYO) eqn:OY; cbn; [exact I| | exfalso; exact (NSO eq_refl)].
      split; [| exact I]. destruct (jtmp_blk hO LB LBO mO moO _ dYO HHO TY OY) as (IN & N1 & _ & _ & NIN).
      eapply (j_out_blk hO LBO mO moO LB SP a); [exact HHO| exact IN| exact NIN| exact SUBO| lia| lia| exact HC].
    - refine (conj MAS (conj EAS (conj NSS _))). intros b Hb HbL. destruct (FRS b Hb) as [X|X]; [exact (FRO _ X HbL)| exact (X (SUBO _ HbL))].
  Qed.

  (* [comment removed for export] *)
  #[using="DIMG"] Lemma j_fresh_apart : ltac2:(CDefT.buildp (gd_tbl_EcpJourney ()) "Phk,(21.Vsegs,VL,VHI,)PLBk,(1;.$2.)Pmk,P,(<.&40.)(22.(<.&8.))Pmok,$23.PLB,(1;.(1>.$9.$9.))Plo,$9.PP,$9.Pk,$9.PA,$9.Pn,$9.P,(1.Vsegs,VL,VHI,R:.R9.R8.R7.)P,(3.(1>.$9.$9.)(20.$9.$9.R5.R4.)R:.)P,(16.(3.(1>.$9.$9.)(20.$9.$9.R6.R5.)R8.))P,Pb,(1>.$9.$9.)P,(3.(1>.$9.$9.)R1.R:.)(3.(1>.$9.$9.)R2.R>.)P,(28.=R7.)P,(31.VL,R;.R:.R7.R6.)P,(28.=R7.)P,(24.(25.VL,)R<.)(2:.(24.(29.R<.R;.)R:.)(24.(29.R:.R9.)R<.))")
(* [comment removed for export] *).
  Proof.
    intros hk LBk mk mok LB lo P k A n HH IN NIN SUB Hk CR Hn ACL.
    destruct (Z_le_dec (P + k) A); [left; lia|]. destruct (Z_le_dec (A + n) P); [right; lia|]. exfalso.
    set (a := Z.max A P). assert (Ha : A <= a < A + n) by lia. assert (Hp : P <= a < P + k) by lia.
    exact (j_out_blk hk LBk mk mok LB lo a P k HH IN NIN SUB Hk ACL (CR a Ha) Hp).
  Qed.
End Journey.
