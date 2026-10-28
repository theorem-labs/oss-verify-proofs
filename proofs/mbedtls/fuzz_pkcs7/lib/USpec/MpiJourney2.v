(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux Asn1AuxA MpiCoreAux HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.USpec Require Import MpiJourney.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_mpi_addsub.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MpiJourney2 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.USpec.MpiJourney.XJ"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.mo_frame"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.heap_top"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.HEAP"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.Lib.Asn1Aux.heap_presx"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_ivs"; "RocqVerifyHarness.AgentSubmission.Lib.AStep.statics_ok"; "RocqVerifyHarness.AgentSubmission.U.U_mpi_addsub.binop_keep"; "RocqVerifyHarness.AgentSubmission.USpec.MpiJourney.JB"; "RocqVerifyHarness.AgentSubmission.USpec.MpiJourney.BJ"].


Section J2.
  Variables (segs : list Segment) (L : heap_layout) (HI : heap_iface segs L).
  Variables (h : HST segs L HI) (LB : list blk) (m : mem) (mo : Model) (dX : mpd) (sp : word) (lo : Z) (FS : Z) (FRAME : list cell).
  Local Notation SP := (bv_unsigned sp).
  Hypothesis JCX : JC segs L HI h LB m mo dX sp lo FS FRAME.
  Local Ltac jc_open := pose proof JCX as [HLS SW DIMG HND ROIMG DHI HH MX NST XW XLS ACL FS0 SLO HTOP FSZ].
  Local Notation XJ0 := (XJ segs L HI h LB m mo dX sp lo FS FRAME []).

  (* [comment removed for export] *)
  #[using="JCX"] Lemma xj_call : ltac2:(CDefT.buildp (gd_tbl_MpiJourney2 ()) "Phc,(0.Vsegs,VL,VHI,)PLBc,(1.$2.)Pmc,P,(3.&40.)(4.(3.&8.))Pmoc,$5.PdXc,$6.Ph1,(0.Vsegs,VL,VHI,)PLB1,(1.$2.)Pm1,P,(3.&40.)(4.(3.&8.))Pmo1,$5.PdX1,$6.P,(7.Vsegs,VL,VHI,Vh,VLB,Vm,Vmo,VdX,Vsp,Vlo,VFS,VFRAME,(8.$2.)R:.R9.R8.R7.R6.)P,(9.Vsegs,R4.)P,(:.Vsegs,R5.Vlo,(;.(<.&40.Vsp,)VFS,))P,(=.R:.R5.)P,(>.$?.(10.Vsegs,VL,VHI,R9.)(10.Vsegs,VL,VHI,R>.))P,(11.Vsegs,VL,VHI,R:.R9.R8.R7.)P,(12.Vsegs,R9.R:.R7.)P,(13.R10.R=.R;.R8.)P,(14.Vsegs,VL,R11.(;.(<.&40.Vsp,)VFS,)(15.R>.)R10.R;.)P,(16.Vsegs,VL,R<.)P,(17.R13.R10.R;.)(7.Vsegs,VL,VHI,Vh,VLB,Vm,Vmo,VdX,Vsp,Vlo,VFS,VFRAME,(8.$2.)R10.R?.R>.R=.R<.)")
(* [comment removed for export] *).
  Proof.
    jc_open. intros hc LBc mc moc dXc h1 LB1 m1 mo1 dX1 J MI1 ST1 MF1 HT1 HH1 MX1 OUT1 HPX1 SOK1 (AD1 & PD1 & FR1 & NM1).
    pose proof J as [MI0 ST0 FR0 HH0 HT0 MF0 SOK0 MX0 AD0 PD0 NS0 OUT0 FRS0 HPX0 XP0 NM0]. cbn [app] in HH0.
    pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J) as (HBR0 & HAP0 & ND0 & MK0 & XS & X0 & X16 & XAL & LEN0 & NR0 & OWN0 & OWN1). cbn [app] in HBR0.
    pose proof OUT1 as (_ & NS1 & O3 & O4 & O5). pose proof OUT0 as (_ & _ & P3 & P4 & P5).
    constructor; try assumption.
    - eapply heap_presx_rw_cells; [exact HPX1| exact FR0| apply client_range_stack; lia|].
      rewrite FSZ. unfold mpd_ivs. rewrite AD0. cbn. split; [lia|].
      destruct (md_own dXc) eqn:EO; [exact I| | exfalso; exact (NS0 eq_refl)]. split; [| exact I].
      destruct (OWN1 ltac:(discriminate)) as (_ & _ & _ & _ & _ & _ & PC & _). lia.
    - rewrite HT1. exact HT0.
    - eapply mo_frame_trans; [exact MF0| exact MF1].
    - rewrite AD1. exact AD0.
    - rewrite PD1. exact PD0.
    - eapply mpd_out_trans; [exact OUT0| exact OUT1| exact FRS0| intros b Hb; unfold mpd_blk in Hb; pose proof MX as [(_ & _ & _ & _ & _ & OW) _]; destruct (md_own dX); try (destruct Hb; fail); destruct Hb as [<-|[]]; exact (proj1 (proj2 OW))].
    - intros b Hb. destruct (FR1 b Hb) as [C|C]; [exact (FRS0 b C)|].
      destruct (in_dec blk_eq_dec b LB) as [Hin|Hnin]; [| right; exact Hnin].
      left. destruct (in_dec blk_eq_dec b (mpd_blk dX)) as [Hx|Hx]; [exact Hx|]. exfalso. exact (C (P4 b Hin Hx)).
    - eapply heap_presx_trans; [exact HPX0|].
      intros a Ha Hc Ho. apply (HPX1 a Ha).
      + (* [comment removed for export] *)
        destruct Hc as [C|[C|([q k] & Hq & R)]]; [left; lia| right; left; exact C|].
        destruct (in_dec blk_eq_dec (q, k) (mpd_blk dX)) as [Hx|Hx].
        * exfalso. unfold mpd_blk in Hx. unfold mpd_ivs in Ho. cbn in Ho. destruct (md_own dX); try (destruct Hx; fail).
          destruct Hx as [E|[]]. injection E as E1 E2. rewrite <- E1, <- E2 in R. cbn in R, Ho. lia.
        * right; right. exists (q, k). split; [exact (P4 _ Hq Hx)| exact R].
      + (* [comment removed for export] *)
        unfold mpd_ivs in Ho |- *. rewrite AD0. cbn in Ho |- *. destruct Ho as [O1 O2]. split; [exact O1|].
        destruct (md_own dXc) eqn:EO; [exact I| |].
        * split; [| exact I]. destruct (FRS0 (md_p dXc, 4 * md_n dXc) ltac:(unfold mpd_blk; rewrite EO; left; reflexivity)) as [C|C].
          -- unfold mpd_blk in C. destruct (md_own dX); try (destruct C; fail). destruct C as [E|[]]. injection E as E1 E2. rewrite <- E1, <- E2. cbn in O2. lia.
          -- (* [comment removed for export] *)
             destruct (OWN1 ltac:(discriminate)) as (_ & N1 & XIN & _ & _ & P0 & PC & PI).
             destruct Hc as [Cs|[[Cd1 Cd2]|([q k] & Hq & R)]]; [lia| pose proof DIMG; lia|].
             cbn in R. pose proof (heap_blocks _ _ HI _ _ _ _ HH0) as [_ HAPc].
             assert (NE : (q, k) <> (md_p dXc, 4 * md_n dXc)) by (intros E; apply C; rewrite <- E; exact Hq).
             assert (Hq' : In (q, k) LBc).
             { apply P4; [exact Hq|]. intros Hx. apply C. unfold mpd_blk in Hx |- *. destruct (md_own dX); try (destruct Hx; fail).
               destruct Hx as [E|[]]. injection E as E1 E2. cbn in O2. lia. }
             pose proof (proj1 (Forall_forall _ _) HBR0 _ Hq') as (_ & _ & K0 & _). cbn in K0.
             destruct (Z.eq_dec k 0) as [->|Kp]; [lia|].
             destruct (blocks_apart_neq _ _ _ HAPc Hq' XIN NE ltac:(cbn; lia) ltac:(cbn; lia)) as [D|D]; cbn in D; lia.
        * exfalso. exact (NS0 eq_refl).
    - intros EO. pose proof XW as (XCW & _ & XP).
      eapply (new_limbs_apart_range segs L HI h1 LB LB1 m1 m1 mo1 lo dX dX1 (md_addr dX) 16); try eassumption.
      + eapply mpd_out_trans; [exact OUT0| exact OUT1| exact FRS0| intros b Hb; unfold mpd_blk in Hb; pose proof MX as [(_ & _ & _ & _ & _ & OW) _]; destruct (md_own dX); try (destruct Hb; fail); destruct Hb as [<-|[]]; exact (proj1 (proj2 OW))].
      + intros b Hb. destruct (FR1 b Hb) as [C|C]; [exact (FRS0 b C)|].
        destruct (in_dec blk_eq_dec b LB) as [Hin|Hnin]; [| right; exact Hnin].
        left. destruct (in_dec blk_eq_dec b (mpd_blk dX)) as [Hx|Hx]; [exact Hx|]. exfalso. exact (C (P4 b Hin Hx)).
      + pose proof DIMG; lia. + pose proof DIMG; lia.
      + intros a Ha. destruct (XCW a Ha) as [C|[C|C]]; [left; lia| right; left; exact C| right; right; exact C].
      + lia.
    - lia.
  Qed.

  (* [comment removed for export] *)
  #[using="JCX"] Lemma bj_call : ltac2:(CDefT.buildp (gd_tbl_MpiJourney2 ()) "PdB,$6.Phc,(0.Vsegs,VL,VHI,)PLBc,(1.$2.)Pmc,P,(3.&40.)(4.(3.&8.))Pmoc,$5.PdXc,$6.Ph1,(0.Vsegs,VL,VHI,)PLB1,(1.$2.)Pm1,P,(3.&40.)(4.(3.&8.))Pmo1,$5.PdX1,$6.P,(18.Vsegs,VL,VLB,Vm,VdX,Vsp,Vlo,R;.)P,(7.Vsegs,VL,VHI,Vh,VLB,Vm,Vmo,VdX,Vsp,Vlo,VFS,VFRAME,(8.$2.)R;.R:.R9.R8.R7.)P,(19.Vsegs,Vsp,R=.R;.R:.R8.)P,(9.Vsegs,R6.)P,(11.Vsegs,VL,VHI,R9.R8.R7.R6.)P,(12.Vsegs,R8.R9.R6.)P,(13.R?.R<.R:.R7.)P,(14.Vsegs,VL,R10.(;.(<.&40.Vsp,)VFS,)(15.R=.)R?.R:.)P,(17.R11.R>.R9.)(19.Vsegs,Vsp,R14.R=.R<.R:.)")
(* [comment removed for export] *).
  Proof.
    jc_open. intros dB hc LBc mc moc dXc h1 LB1 m1 mo1 dX1 DBJ J B MI1 HH1 MX1 OUT1 HPX1 (AD1 & PD1 & FR1 & NM1).
    pose proof DBJ as [MB0 OB CRB CRBL SXB]. pose proof OB as (OB1 & OB2 & OB3 & OB4 & OB5).
    pose proof J as [MI0 ST0 FR0 HH0 HT0 MF0 SOK0 MX0 AD0 PD0 NS0 OUT0 FRS0 HPX0 XP0 NM0]. cbn [app] in HH0.
    pose proof (xj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ _ _ _ _ _ J) as (HBR0 & HAP0 & ND0 & MK0 & XS & X0 & X16 & XAL & LEN0 & NR0 & OWN0 & OWN1). cbn [app] in HBR0.
    pose proof (bj_facts _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ _ _ _ B) as (B0 & B16 & BAL & LENB & NRB & BS & OWNB0 & OWNB1).
    pose proof B as [BA BSS BSL]. pose proof OUT1 as (_ & NS1 & O3 & O4 & O5).
    destruct (bj_client _ _ _ _ _ _ _ _ _ _ _ _ JCX _ DBJ [] hc LBc mc moc dXc LBc (SP - FS) J B ltac:(intros b Hb _; exact Hb) ltac:(lia)) as [C1 C2].
    (* [comment removed for export] *)
    assert (NEWAP : forall A n, (forall a, A <= a < A + n -> client_addr L LB lo a) -> 0 < n ->
              (md_own dX = LHeap -> A + n <= md_p dX \/ md_p dX + 4 * md_n dX <= A) ->
              md_own dX1 = LHeap -> A + n <= md_p dX1 \/ md_p dX1 + 4 * md_n dX1 <= A).
    { intros A n CR Hn D EO1.
      eapply (new_limbs_apart_range segs L HI h1 LB LB1 m1 m1 mo1 lo dX dX1 A n); try eassumption.
      - eapply mpd_out_trans; [exact OUT0| exact OUT1| exact FRS0| intros b Hb; unfold mpd_blk in Hb; pose proof MX as [(_ & _ & _ & _ & _ & OW) _]; destruct (md_own dX); try (destruct Hb; fail); destruct Hb as [<-|[]]; exact (proj1 (proj2 OW))].
      - intros b Hb. destruct (FR1 b Hb) as [C|C]; [exact (FRS0 b C)|].
        destruct (in_dec blk_eq_dec b LB) as [Hin|Hnin]; [| right; exact Hnin].
        left. destruct (in_dec blk_eq_dec b (mpd_blk dX)) as [Hx|Hx]; [exact Hx|]. exfalso. pose proof OUT0 as (_ & _ & _ & P4 & _). exact (C (P4 b Hin Hx)).
      - pose proof DIMG; lia. - pose proof DIMG; lia. }
    constructor.
    - eapply opnd_at_heap_presx; [exact BA| exact HPX1| exact MI0| exact MI1| exact C1| exact C2| | | | lia].
      + unfold mpd_ivs. rewrite AD0. cbn. split; [lia|]. destruct (md_own dXc) eqn:EO; [exact I| | exfalso; exact (NS0 eq_refl)]. split; [| exact I]. pose proof (BSS eq_refl). lia.
      + intros BN. destruct (OWNB1 BN) as (N1 & P0 & _).
        unfold mpd_ivs. rewrite AD0. cbn. split; [pose proof (OB1 BN); lia|].
        destruct (md_own dXc) eqn:EO; [exact I| | exfalso; exact (NS0 eq_refl)]. split; [| exact I]. pose proof (BSL eq_refl BN). lia.
      + intros b Hb. unfold mpd_blk in Hb. destruct (md_own dB) eqn:EOB; try (destruct Hb; fail). destruct Hb as [<-|[]].
        destruct (OWNB1 ltac:(discriminate)) as (N1 & P0 & _ & _ & _ & BIN). destruct (BIN eq_refl) as [_ BINc].
        apply O4; [exact BINc|]. intros Hx. unfold mpd_blk in Hx. destruct (md_own dXc) eqn:EO; try (destruct Hx; fail).
        destruct Hx as [E|[]]. injection E as E1 E2.
        destruct (OWN1 ltac:(discriminate)) as (_ & NX1 & _). pose proof (BSL eq_refl ltac:(discriminate)). lia.
    - intros EO1. exact (NEWAP (md_addr dB) 16 CRB ltac:(lia) OB2 EO1).
    - intros EO1 BN. destruct (OWNB1 BN) as (N1 & P0 & BP4 & BBY & BLS & BIN).
      destruct (md_own dB) eqn:EOB; [exfalso; exact (BN eq_refl)| |].
      + destruct (NEWAP (md_p dB) (4 * md_n dB) (CRBL eq_refl) ltac:(lia)) as [D|D]; [| exact EO1| right; exact D| left; exact D].
        intros EOX. destruct OB3 as [E|[E|[E|E]]]; [| exfalso; exact (E EOX)| discriminate| lia].
        (* [comment removed for export] *) exfalso. rewrite <- E in SXB. lia.
      + (* [comment removed for export] *)
        pose proof MX1 as [(_ & _ & _ & _ & _ & OW1) _]. rewrite EO1 in OW1. destruct OW1 as (NX1 & XIN1 & _ & _).
        pose proof (heap_blocks _ _ HI _ _ _ _ HH1) as [HBR1 _]. pose proof (proj1 (Forall_forall _ _) HBR1 _ XIN1) as (R0 & _ & _ & R3 & R4). cbn in R0, R3, R4.
        pose proof (opnd_view _ _ _ _ _ MB0) as [(_ & _ & _ & LENB0 & _ & OWB) _]. rewrite EOB in OWB. destruct OWB as (_ & _ & _ & _ & [BRO|[BSP _]]).
        2: { (* [comment removed for export] *) lia. }
        assert (BND : md_p dB + 4 * md_n dB <= 2^64).
        { pose proof (bytes_at_bound _ _ _ _ BBY) as K. rewrite u32s_length in K. lia. }
        pose proof (BRO 0 ltac:(lia)) as RO0. rewrite Z.add_0_r in RO0. pose proof (ROIMG (md_p dB) RO0 ltac:(lia)) as I0.
        pose proof (BRO (4 * md_n dB - 1) ltac:(lia)) as RO1. pose proof (ROIMG (md_p dB + (4 * md_n dB - 1)) RO1 ltac:(lia)) as I1. lia.
  Qed.
End J2.
