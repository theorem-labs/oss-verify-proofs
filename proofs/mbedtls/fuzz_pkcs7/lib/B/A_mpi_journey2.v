(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiJourney.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_opnd A_mpi_journey.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_mpi_journey2 () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.XJA"; "Corelib.Init.Datatypes.nil"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpd_keep"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.binop_keep"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.BJA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RIDE.rideA"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.XDA"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_journey.FBA"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.lb_remove"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.w_client"].


Lemma In_mpd_keep_not_blk : forall LB d b, In b (mpd_keep LB d) -> ~ In b (mpd_blk d).
Proof.
  intros LB d b Hb. unfold mpd_keep in Hb. unfold mpd_blk. destruct (md_own d); [intros []| | intros []].
  apply filter_In in Hb. destruct Hb as [_ Hne]. intros [E|[]]. rewrite <- E in Hne.
  unfold blk_eqb in Hne. cbn in Hne. rewrite !Z.eqb_refl in Hne. discriminate Hne.
Qed.

Section JA2.
  Variable segs : list Segment.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA segs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Variables (h : HST segs R HIA) (LB LF : list blk) (m : mem) (dX : mpd) (sp : word) (lo FS : Z) (FRAME : list cell).
  Local Notation SP := (bv_unsigned sp).
  Local Notation X := (md_addr dX).
  Hypothesis JC : JCA segs R HIA h LB LF m dX sp lo FS FRAME.
  Local Ltac jc_open := pose proof JC as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
  Local Notation XJ0 := (XJA segs R HIA h LB LF m dX sp lo FS FRAME []).

  (* [comment removed for export] *)
  #[using="Type"] Lemma xa_keep_keep : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey2 ()) "Pv,$0.Pf,$0.Phc,(1.Vsegs,VR,VHIA,)PLBc,(2.$3.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.Pb,$3.P,(7.Vsegs,VR,VHIA,Vh,VLB,VLF,Vm,VdX,Vsp,Vlo,VFS,VFRAME,(8.$3.)R7.R6.R5.R4.R3.R2.)P,(9.$3.R2.(:.VLB,VdX,))(9.$3.R3.(:.R6.R4.))")
(* [comment removed for export] *).
  Proof.
    intros v f hc LBc mc dXc b J Hb.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1].
    apply In_mpd_keep_intro; [eapply (xa_keep_sub segs R HIA h LB LF m dX sp lo FS FRAME); [exact J| exact Hb]|].
    intros Hc. destruct (FRA1 b Hc) as [K|K]; [exact (In_mpd_keep_not_blk _ _ _ Hb K)|].
    ddestruct K as (_ & _ & _ & K3). destruct b as [B j]. cbn [fst snd] in K3.
    pose proof (K3 B j ltac:(apply in_app_iff; left; exact Hb)) as K.
    unfold mpd_blk in Hc. pose proof MX1 as [(_ & _ & _ & _ & _ & OW) _].
    destruct (md_own dXc); try (destruct Hc; fail). destruct Hc as [E|[]]. injection E as E1 E2. destruct OW as (N1 & _). clear - K E2 N1. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma xa_fresh_call : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey2 ()) "Pv,$0.Pf,$0.Phc,(1.Vsegs,VR,VHIA,)PLBc,(2.$3.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.PdX',$6.P,(7.Vsegs,VR,VHIA,Vh,VLB,VLF,Vm,VdX,Vsp,Vlo,VFS,VFRAME,(8.$3.)R7.R6.R5.R4.R3.R2.)P,Pb,$3.P,(9.$3.R1.(;.R3.))(<.(9.$3.R2.(;.R5.))(=.VR,(:.R7.R5.)VLF,(>.$0.$0.R2.)(?.$0.$0.R2.)))Pb,$3.P,(9.$3.R1.(;.R4.))(<.(9.$3.R2.(;.VdX,))(=.VR,(:.VLB,VdX,)VLF,(>.$0.$0.R2.)(?.$0.$0.R2.)))")
(* [comment removed for export] *).
  Proof.
    intros v f hc LBc mc dXc dX' J FRA' b Hb.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1].
    destruct (FRA' b Hb) as [K|K]; [exact (FRA1 b K)| right].
    eapply fresh_apart_blocks_mono; [exact K|]. intros b' Hb'. eapply xa_keep_keep; [exact J| exact Hb'].
  Qed.

  (* [comment removed for export] *)
  #[using="JC"] Lemma xa_call : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey2 ()) "Pv,$0.Pf,$0.Phc,(1.Vsegs,VR,VHIA,)PLBc,(2.$3.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.Pm',P,(4.&40.)(5.(4.&8.))Ph',(1.Vsegs,VR,VHIA,)PLB',(2.$3.)PdX',$6.PSPc,$0.PPHI',$0.PFR',$0.P,(7.Vsegs,VR,VHIA,Vh,VLB,VLF,Vm,VdX,Vsp,Vlo,VFS,VFRAME,(8.$3.)R=.R<.R;.R:.R9.R8.)P,(10.(11.Vlo,R4.)(11.R4.(12.(13.&40.Vsp,)VFS,)))P,(11.=R4.)P,(11.=R4.)P,(14.Vsegs,R;.)P,(15.Vsegs,R<.Vlo,(12.(13.&40.Vsp,)VFS,))P,(16.Vsegs,VR,(:.R10.R>.)VLF,R9.(17.VR,)(18.Vsegs,VR,VHIA,R11.)(19.(1:.$0.$0.)(1;.$0.$0.(1<.VdX,)(1=.(1<.VdX,)+10.))(8.(1:.$0.$0.)))R?.R=.)P,(1>.$0.(1?.Vsegs,VR,VHIA,R=.)(1?.Vsegs,VR,VHIA,R12.))P,(1>.$0.(18.Vsegs,VR,VHIA,R>.)(18.Vsegs,VR,VHIA,R13.))P,(1>.$0.(20.Vsegs,VR,VHIA,R?.)(20.Vsegs,VR,VHIA,R14.))P,Px,$0.P,(21.Vsegs,VR,VHIA,R16.R1.)(21.Vsegs,VR,VHIA,R12.R2.)P,(11.(22.Vsegs,VR,VHIA,R11.)(1=.(22.Vsegs,VR,VHIA,R16.)R=.))P,(11.(23.Vsegs,VR,VHIA,R12.)(1=.(23.Vsegs,VR,VHIA,R17.)R=.))P,(24.Vsegs,VR,VHIA,R13.R12.VLF,R14.)P,(25.Vsegs,R15.R13.R12.)P,(26.R19.R17.R14.R13.)P,(27.R1:.R18.R14.)P,Pb,$3.P,(9.$3.R1.(;.R16.))(<.(9.$3.R2.(;.R1;.))(=.VR,(:.R1=.R1;.)VLF,(>.$0.$0.R2.)(?.$0.$0.R2.)))(7.Vsegs,VR,VHIA,Vh,VLB,VLF,Vm,VdX,Vsp,Vlo,VFS,VFRAME,(8.$3.)(1=.R1?.R14.)(1=.R1>.R13.)R18.R17.R19.R16.)")
(* [comment removed for export] *).
  Proof.
    jc_open. dpose (jca_facts segs R HIA h LB LF m dX sp lo FS FRAME JC) as (LO0 & LOSP & SP64 & ALO & ACP & X0 & X16 & XAL & DSX & LEN & NR).
    intros v f hc LBc mc dXc m' h' LB' dX' SPc PHI' FR' J HSPc HPHI HFR MI' ST' HP HT' HS' HF' HCS' HV' HFR' HH' MX' OUT' BK FRA'.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1].
    dpose OUT' as (OA & ONS & O3 & O4 & O5). dpose BK as (BA & BP & BF & BN). dpose OUT1 as (_ & _ & P3 & P4 & P5).
    pose proof (xa_fresh_call _ _ _ _ _ _ _ J FRA') as FRA2.
    destruct XW as [CW DXP].
    pose proof (client_wrange_keep L LB LF SP (htop segs R HIA h) dX X 16 CW DXP) as CWk.
    assert (CRk : client_range L (mpd_keep LBc dXc ++ fdata LF) SPc X 16).
    { eapply client_range_inside; [eapply client_wrange_sp_mono; [| exact CWk]; clear - HSPc FS16; lia| | clear; lia| clear; lia].
      intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; eapply xa_keep_keep; [exact J| exact Hb]| right; exact Hb]. }
    pose proof HP as HPc. rewrite HS1 in HP.
    assert (HPo : presA segs R (mpd_keep LB dX) LF SP (arl_stklo R) (hstkhi segs R HIA h) [(X, X + 16)] mc m').
    { eapply presA_weaken; [exact HP| intros b Hb; eapply xa_keep_keep; [exact J| exact Hb]| intros b Hb; exact Hb| clear - HSPc LOSP FS16; lia| clear; lia| clear; lia| intros y Hy; exact Hy]. }
    pose proof MX' as [(CX' & _ & _ & LEN' & NR' & OW') SG'].
    constructor; cbn [app]; try assumption.
    - eapply (presA_rw_cells segs R); [exact HP| exact FR1| rewrite FSZ; apply client_range_stack; clear - HSPc; lia| rewrite FSZ; cbn [disjoint_from]; split; [clear - DSX LOSP FS16; lia| exact I]].
    - rewrite HT'. exact HT1.
    - rewrite HS'. exact HS1.
    - rewrite HF'. exact HF1.
    - intros x Hx. apply HCS', HCS1, Hx.
    - clear - HV' HV1 HPHI. lia.
    - clear - HFR' HFR1 HFR. lia.
    - rewrite BA. exact AD1.
    - rewrite BP. exact PD1.
    - eapply mpd_out_trans; [exact OUT1| exact OUT'| exact FRS1|].
      intros b Hb. unfold mpd_blk in Hb. pose proof MX as [(_ & _ & _ & _ & _ & OW) _]. destruct (md_own dX); try (destruct Hb; fail). destruct Hb as [<-|[]]. exact (proj1 (proj2 OW)).
    - intros b Hb. destruct (BF b Hb) as [C|C]; [exact (FRS1 b C)|].
      destruct (in_dec blk_eq_dec b LB) as [Hin|Hnin]; [| right; exact Hnin].
      left. destruct (in_dec blk_eq_dec b (mpd_blk dX)) as [Hx|Hx]; [exact Hx|]. exfalso. exact (C (P4 b Hin Hx)).
    - eapply presA_trans; [exact HPX1| exact HPo].
    - eapply aobj_cs_mono; [exact HCS'|].
      eapply (presA_aobj0 segs R); [exact (hcs_ok segs R HIA hc)| exact HPc| exact OX1| intros x Hx; eapply hcs_below_top; exact Hx|].
      right. split; [exact CRk| clear - ALO LOS HSPc; lia].
    - (* [comment removed for export] *)
      intros EO. destruct (FRA' (md_p dX', 4 * md_n dX') ltac:(unfold mpd_blk; rewrite EO; left; reflexivity)) as [Hb|HFRA].
      + assert (EOX : md_own dXc = LHeap /\ md_p dXc = md_p dX' /\ md_n dXc = md_n dX').
        { unfold mpd_blk in Hb. destruct (md_own dXc); try (destruct Hb; fail). destruct Hb as [E|[]]. injection E as E1 E2.
          split; [reflexivity| split; [exact E1| clear - E2; lia]]. }
        ddestruct EOX as (EOd & EP & EN). destruct (XP1 EOd); [left| right]; rewrite <- ?EP, <- ?EN; assumption.
      + cbn [fst snd] in HFRA. rewrite EO in OW'. destruct OW' as (N1' & _).
        destruct (fresh_apart_client R (mpd_keep LBc dXc) LF SPc X 16 _ _ HFRA CRk ltac:(clear; lia) ltac:(clear - N1'; lia) ltac:(clear - ALO LOS HSPc; lia)); [right| left]; assumption.
    - (* [comment removed for export] *)
      intros ON. assert (EO : md_own dX' = LHeap) by (destruct (md_own dX'); [exfalso; exact (ON eq_refl)| reflexivity| exfalso; exact (ONS eq_refl)]).
      destruct (FRA' (md_p dX', 4 * md_n dX') ltac:(unfold mpd_blk; rewrite EO; left; reflexivity)) as [Hb|HFRA].
      + assert (EOX : md_own dXc = LHeap /\ md_p dXc = md_p dX' /\ md_n dXc = md_n dX').
        { unfold mpd_blk in Hb. destruct (md_own dXc); try (destruct Hb; fail). destruct Hb as [E|[]]. injection E as E1 E2.
          split; [reflexivity| split; [exact E1| clear - E2; lia]]. }
        ddestruct EOX as (EOd & EP & EN). destruct (XLS1 ltac:(rewrite EOd; discriminate)); [left| right]; rewrite <- ?EP, <- ?EN; assumption.
      + cbn [fst snd] in HFRA. dpose HFRA as (_ & AC' & _). left. clear - AC' ALO LOS. lia.
    - clear - NM1 BN. lia.
    all: match goal with |- ?g => idtac "XC-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable dB : mpd.
  Hypothesis DBJ : JBA segs R HIA LB LF m dX sp lo dB.
  Local Ltac jb_open := pose proof DBJ as [MB0 OB CRB CRBL SXB BIMG].
  Local Notation BJ0 := (BJA segs R HIA LF sp dB).

  #[using="JC DBJ"] Lemma bja_call : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey2 ()) "Pv,$0.Pf,$0.Phc,(1.Vsegs,VR,VHIA,)PLBc,(2.$3.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.Pm',P,(4.&40.)(5.(4.&8.))Ph',(1.Vsegs,VR,VHIA,)PLB',(2.$3.)PdX',$6.PSPc,$0.P,(7.Vsegs,VR,VHIA,Vh,VLB,VLF,Vm,VdX,Vsp,Vlo,VFS,VFRAME,(8.$3.)R;.R:.R9.R8.R7.R6.)P,(28.Vsegs,VR,VHIA,VLF,Vsp,VdB,R:.R9.R8.R7.)P,(10.(11.Vlo,R3.)(11.R3.(12.(13.&40.Vsp,)VFS,)))P,(14.Vsegs,R8.)P,(16.Vsegs,VR,(:.R<.R:.)VLF,R5.(17.VR,)(18.Vsegs,VR,VHIA,R=.)(19.(1:.$0.$0.)(1;.$0.$0.(1<.VdX,)(1=.(1<.VdX,)+10.))(8.(1:.$0.$0.)))R;.R9.)P,Px,$0.P,(21.Vsegs,VR,VHIA,R?.R1.)(21.Vsegs,VR,VHIA,R;.R2.)P,(24.Vsegs,VR,VHIA,R:.R9.VLF,R;.)P,(25.Vsegs,R<.R:.R9.)P,(26.R10.R>.R;.R:.)P,Pb,$3.P,(9.$3.R1.(;.R<.))(<.(9.$3.R2.(;.R11.))(=.VR,(:.R13.R11.)VLF,(>.$0.$0.R2.)(?.$0.$0.R2.)))(28.Vsegs,VR,VHIA,VLF,Vsp,VdB,R>.R=.R?.R<.)")
(* [comment removed for export] *).
  Proof.
    jc_open. jb_open. dpose (jca_facts segs R HIA h LB LF m dX sp lo FS FRAME JC) as (LO0 & LOSP & SP64 & ALO & ACP & X0 & X16 & XAL & DSX & LEN & NR).
    intros v f hc LBc mc dXc m' h' LB' dX' SPc J B HSPc MI' HP HCS' HH' MX' OUT' FRA'.
    pose proof J as [MI1 ST1 FR1 HH1 HT1 HS1 HF1 HCS1 HV1 HFR1 MX1 AD1 PD1 NS1 OUT1 FRS1 FRA1 HPX1 OX1 XP1 XLS1 NM1].
    pose proof B as [BA BS BL BO BOL]. dpose OB as (OB1 & OB2 & OB3 & OB4 & OB5). dpose OUT' as (OA & ONS & O3 & O4 & O5).
    pose proof (bja_facts segs R HIA h LB LF m dX sp lo FS FRAME JC dB DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
    pose proof MX' as [(_ & _ & _ & LEN' & NR' & OW') SG'].
    pose proof (xa_fresh_call _ _ _ _ _ _ _ J FRA') as FRA2.
    destruct (bja_client segs R HIA h LB LF m dX sp lo FS FRAME JC dB DBJ [] v f hc LBc mc dXc (mpd_keep LBc dXc) SPc J B) as [CRBk CRBLk].
    { intros b Hb NE. apply In_mpd_keep_intro; [exact Hb|]. unfold mpd_blk. destruct (md_own dXc) eqn:EO; try (intros []; fail). intros [E|[]]. exact (NE eq_refl (eq_sym E)). }
    { clear - HSPc FS16. lia. }
    (* [comment removed for export] *)
    assert (BINL : md_own dB = LHeap -> In (md_p dB, 4 * md_n dB) LB').
    { intros EOB. ddestruct (OWNE1 ltac:(rewrite EOB; discriminate)) as (NB1 & _ & _ & _ & _ & BHP & _). destruct (BHP EOB) as [_ BINc].
      apply O4; [exact BINc|]. unfold mpd_blk. destruct (md_own dXc) eqn:EOX; try (intros []; fail). intros [E|[]]. injection E as Q1 Q2.
      pose proof MX1 as [(_ & _ & _ & _ & _ & OWX) _]. rewrite EOX in OWX. pose proof (proj1 OWX) as NX1.
      pose proof (BL eq_refl ltac:(rewrite EOB; discriminate)) as K. clear - K Q1 Q2 NB1 NX1. lia. }
    pose proof HP as HPc. rewrite HS1 in HP.
    constructor.
    - (* [comment removed for export] *)
      eapply (opnd_atA_heap_presx segs R LF mc m' LBc (mpd_keep LBc dXc ++ fdata LF) LB' SPc SP [(X, X + 16)]);
        [exact BA| exact (presA_presx segs R _ _ _ _ _ _ _ _ HP)| exact MI1| exact MI'| exact CRBk| exact CRBLk| cbn; split; [clear - SXB; lia| exact I]
        | intros BN; cbn; split; [pose proof (OB1 BN) as K; clear - K; lia| exact I]| | clear - HSPc FS16; lia| intros b Hb; apply in_or_app; right; exact Hb].
      intros b Hb. unfold mpd_blk in Hb. destruct (md_own dB) eqn:EOB; try (destruct Hb; fail). destruct Hb as [<-|[]]. exact (BINL eq_refl).
    - (* [comment removed for export] *)
      intros EO. rewrite EO in OW'. destruct OW' as (N1' & _).
      destruct (new_limbs_apartA R LB LF SPc dX dX' (md_addr dB) 16 FRA2 EO N1' ltac:(eapply client_range_sep; [exact CRB| intros b Hb; exact Hb| clear - OB4 HSPc FS16; lia]) OB2 ltac:(clear - ALO LOS HSPc; lia) ltac:(clear; lia)); [left| right]; assumption.
    - (* [comment removed for export] *)
      intros EO BN. rewrite EO in OW'. destruct OW' as (N1' & _). ddestruct (OWNE1 BN) as (NB1 & BP0 & _ & BBY & BSK & BHP & BST).
      destruct (md_own dB) eqn:EOB; [exfalso; exact (BN eq_refl)| |].
      + destruct (new_limbs_apartA R LB LF SPc dX dX' (md_p dB) (4 * md_n dB) FRA2 EO N1'
                   ltac:(eapply client_range_sep; [exact (CRBL eq_refl)| intros b Hb; exact Hb| clear - BSK HSPc FS16; lia])
                   ltac:(intros EOX; destruct OB3 as [C|[C|[C|C]]]; [exfalso; rewrite C in SXB; clear - SXB; lia| exfalso; exact (C EOX)| discriminate| clear - C; lia])
                   ltac:(clear - ALO LOS HSPc; lia) ltac:(clear - NB1; lia)); [right| left]; assumption.
      + (* [comment removed for export] *)
        destruct (FRA' (md_p dX', 4 * md_n dX') ltac:(unfold mpd_blk; rewrite EO; left; reflexivity)) as [Hb|HFRA].
        * assert (EOX : md_own dXc = LHeap /\ md_p dXc = md_p dX' /\ md_n dXc = md_n dX').
          { unfold mpd_blk in Hb. destruct (md_own dXc); try (destruct Hb; fail). destruct Hb as [E|[]]. injection E as E1 E2.
            split; [reflexivity| split; [exact E1| clear - E2; lia]]. }
          ddestruct EOX as (EOd & EP & EN). rewrite <- EP, <- EN. apply (BL EOd). congruence.
        * cbn [fst snd] in HFRA. dpose HFRA as (A0' & AC' & AD' & _).
          destruct (BST eq_refl) as [BRO|[BSP BH]].
          -- pose proof MX' as [(_ & _ & _ & _ & _ & OWn) _]. rewrite EO in OWn. ddestruct OWn as (_ & PIN & _).
             destruct (hm_apart segs R HIA h' LB' LF m' HH') as [HF'' _]. rewrite Forall_forall in HF''.
             destruct (HF'' _ ltac:(apply in_app_iff; left; exact PIN)) as (_ & _ & _ & BI). cbn [fst snd] in BI.
             pose proof (ROIMG (md_p dB + 0) (BRO 0 ltac:(clear - NB1; lia)) ltac:(pose proof (u32ro_bound _ _ _ _ BBY) as BB; clear - BB NB1 LENE; lia)) as I0.
             pose proof (ROIMG (md_p dB + (4 * md_n dB - 1)) (BRO (4 * md_n dB - 1) ltac:(clear - NB1; lia)) ltac:(pose proof (u32ro_bound _ _ _ _ BBY) as BB; clear - BB NB1 LENE; lia)) as I1.
             clear - I0 I1 BI NB1. lia.
          -- exact (fresh_apart_client R (mpd_keep LBc dXc) LF lo (md_p dB) (4 * md_n dB) (md_p dX') (4 * md_n dX') HFRA
                      ltac:(eapply client_range_temp; [exact BSP| clear - LOSP FS16; lia| intros b Hb; apply in_or_app; right; exact Hb])
                      ltac:(clear - NB1; lia) ltac:(clear - N1'; lia) ltac:(clear - ALO LOS; lia)).
    - (* [comment removed for export] *)
      eapply aobj_cs_mono; [exact HCS'|].
      eapply (presA_aobj0 segs R); [exact (hcs_ok segs R HIA hc)| exact HPc| exact BO| intros x Hx; eapply hcs_below_top; exact Hx|].
      right. split; [exact CRBk| clear - ALO LOS HSPc; lia].
    - (* [comment removed for export] *)
      intros BN. ddestruct (OWNE1 BN) as (NB1 & BP0 & _ & BBY & BSK & BHP & BST).
      destruct (md_own dB) eqn:EOB; [exfalso; exact (BN eq_refl)| |].
      + eapply hm_aobj_block; [exact HH'| exact (BINL eq_refl)].
      + destruct (BST eq_refl) as [BRO|[BSP BH]].
        * eapply BIMG; [reflexivity| exact BRO| exact HH'].
        * eapply aobj_cs_mono; [exact HCS'|].
          eapply (presA_aobj0 segs R); [exact (hcs_ok segs R HIA hc)| exact HPc| exact (BOL BN)| intros x Hx; eapply hcs_below_top; exact Hx|].
          right. split; [eapply client_range_temp; [exact BSP| clear - HSPc FS16; lia| intros b Hb; apply in_or_app; right; exact Hb]| clear - ALO LOS HSPc; lia].
    all: match goal with |- ?g => idtac "BC-LEFT:" g end.
  Qed.
End JA2.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RIDE.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Variables (h : HST asegs R HIA) (LB LF : list blk) (m : mem) (dX : mpd) (sp : word) (lo FS : Z) (FRAME : list cell).
  Local Notation X := (md_addr dX).
  Hypothesis JC : JCA asegs R HIA h LB LF m dX sp lo FS FRAME.
  Local Ltac jc_open := pose proof JC as [NEEDR HND DIMG ROIMG HH MX NST XW XLS LOS FS16 SLO TOP SPA FSZ].
  Local Notation XJ0 := (XJA asegs R HIA h LB LF m dX sp lo FS FRAME []).
  Local Notation JBE dE := (JBA asegs R HIA LB LF m dX sp lo dE).
  Local Notation BJE dE := (BJA asegs R HIA LF sp dE).

  Definition rideA (dE : mpd) (hc : HST asegs R HIA) (LBc : list blk) (mc : mem) (dXc : mpd) : Prop :=
    md_addr dE = X \/ (JBE dE /\ BJE dE hc LBc mc dXc).

  #[using="JC"] Lemma rideA_transport : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey2 ()) "PdE,$6.PEX,(2.$3.)Pv,$0.Pf,$0.Phc,(1.$29.VR,VHIA,)PLBc,(2.$3.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.Pm2,P,(4.&40.)(5.(4.&8.))Ph2,(1.$29.VR,VHIA,)PLB2,(2.$3.)P,(7.$29.VR,VHIA,Vh,VLB,VLF,Vm,VdX,Vsp,Vlo,VFS,VFRAME,R:.R9.R8.R7.R6.R5.R4.)P,(2:.R<.R8.R7.R6.R5.)P,(16.$29.VR,(2;.$3.R<.R8.)VLF,(12.(13.&40.Vsp,)VFS,)(17.VR,)(18.$29.VR,VHIA,R9.)(8.$2<.)R7.R5.)P,(14.$29.R6.)P,Px,$0.P,(21.$29.VR,VHIA,R<.R1.)(21.$29.VR,VHIA,R8.R2.)P,(24.$29.VR,VHIA,R7.R6.VLF,R8.)P,Pb,$3.P,(9.$3.R1.R=.)(9.$3.R2.R9.)(2:.R12.R9.R=.R:.R;.)")
(* [comment removed for export] *).
  Proof.
    intros dE EX v f hc LBc mc dXc m2 h2 LB2 J [E|[DBJ B]] HP MI2 HCS2 HH2 INC; [left; exact E| right; split; [exact DBJ|]].
    eapply (bja_transport _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ _ _ _ _ _ _ J B HP MI2 HCS2 HH2 INC).
  Qed.

  #[using="JC"] Lemma rideA_finish : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey2 ()) "PdE,$6.Pv,$0.Pf,$0.Phd,(1.$29.VR,VHIA,)PLBd,(2.$3.)PAn,$0.Pcnt,$0.Pys,(2.(4.&40.))Pme,P,(4.&40.)(5.(4.&8.))PdXc,$6.Pm5,P,(4.&40.)(5.(4.&8.))P,(2=.$29.VR,VHIA,Vh,VLB,VLF,Vm,VdX,Vsp,Vlo,VFS,VFRAME,R:.R9.R8.R7.R6.R5.R4.R3.R2.)P,(2:.R<.R9.R8.R4.R3.)P,(2>.(19.(1:.$0.$0.)(1;.$0.$0.(1<.VdX,)(1=.(1<.VdX,)+10.))(8.(1:.$0.$0.)))R5.R3.)P,(2?.$29.R6.R4.)(2:.R?.R<.(19.(1:.$0.$0.)(1;.$0.$0.R:.(30.+4.R9.))R;.)R5.(31.(1<.VdX,)(32.R6.)R9.R:.R8.(33.VdX,)$34.))")
(* [comment removed for export] *).
  Proof.
    intros dE v f hd LBd An cnt ys me dXc m5 D [E|[DBJ B]] MU WM; [left; exact E| right; split; [exact DBJ|]].
    eapply (bja_finish _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ _ _ _ _ _ _ D B MU WM).
  Qed.

  #[using="JC"] Lemma rideA_zfree : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey2 ()) "PdE,$6.Pv,$0.Pf,$0.Phc,(1.$29.VR,VHIA,)PLBc,(2.$3.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.PAn,$0.Pcnt,$0.Pys,(2.(4.&40.))Pm4,P,(4.&40.)(5.(4.&8.))Ph4,(1.$29.VR,VHIA,)P,(7.$29.VR,VHIA,Vh,VLB,VLF,Vm,VdX,Vsp,Vlo,VFS,VFRAME,(19.(1:.$0.$0.)(1;.$0.$0.R5.(30.+4.R4.))(8.(1:.$0.$0.)))R;.R:.R9.R8.R7.R6.)P,(35.$29.VR,VLB,VLF,VdX,Vlo,R9.R6.R5.R4.R8.R7.)P,(2:.R>.R;.R:.R9.R8.)P,(1>.$36.(37.R9.)$34.)P,(16.$29.VR,(38.(39.R:.)(19.(1:.$0.$0.)(1;.$0.$0.R9.(30.+4.R8.))R<.))VLF,(12.(13.&40.Vsp,)VFS,)(17.VR,)(18.$29.VR,VHIA,R=.)(19.(1:.$0.$0.)(1;.$0.$0.(39.R:.)(1=.(39.R:.)(30.+4.(3:.R:.))))(8.(1:.$0.$0.)))R;.R6.)P,(14.$29.R7.)P,Px,$0.P,(21.$29.VR,VHIA,R10.R1.)(21.$29.VR,VHIA,R9.R2.)P,(24.$29.VR,VHIA,R8.(38.(39.R=.)(19.(1:.$0.$0.)(1;.$0.$0.R<.(30.+4.R;.))R?.))VLF,R9.)(2:.R14.R9.(38.(39.R>.)R10.)R:.R>.)")
(* [comment removed for export] *).
  Proof.
    intros dE v f hc LBc mc dXc An cnt ys m4 h4 J FBx [E|[DBJ B]] EO HP MI4 HCS4 HH4; [left; exact E| right; split; [exact DBJ|]].
    eapply (bja_zfree _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ _ _ _ _ _ m4 h4 J FBx B EO HP MI4 HCS4 HH4).
  Qed.


  #[using="JC"] Lemma rideA_fresh_munch : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey2 ()) "PdE,$6.Pv,$0.Pf,$0.Phc,(1.$29.VR,VHIA,)PLBc,(2.$3.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.PAn,$0.Pcnt,$0.Pys,(2.(4.&40.))Pk,$0.Pm3,P,(4.&40.)(5.(4.&8.))Pwhi,$0.P,(7.$29.VR,VHIA,Vh,VLB,VLF,Vm,VdX,Vsp,Vlo,VFS,VFRAME,(19.(1:.$0.$0.)(1;.$0.$0.R6.(30.+4.R5.))(8.(1:.$0.$0.)))R<.R;.R:.R9.R8.R7.)P,(35.$29.VR,VLB,VLF,VdX,Vlo,R:.R7.R6.R5.R9.R8.)P,(2:.R?.R<.R;.R:.R9.)P,(10.(11.=R6.)(11.R6.(30.+4.R8.)))P,(11.R5.(13.&40.Vsp,))P,(2>.(19.(1:.$0.$0.)(1;.$0.$0.R;.(1=.R;.R8.))(19.(1:.$0.$0.)(1;.$0.$0.Vlo,R6.)(8.(1:.$0.$0.))))R=.R7.)P,(2?.$29.R>.R8.)P,(3;.(21.$29.VR,VHIA,R11.)(19.(1:.$0.$0.)(1;.$0.$0.R=.(1=.R=.R:.))(19.(1:.$0.$0.)(1;.$0.$0.Vlo,R8.)(8.(1:.$0.$0.)))))(2:.R15.R12.R11.R:.R?.)")
(* [comment removed for export] *).
  Proof.
    intros dE v f hc LBc mc dXc An cnt ys k m3 whi J FBx [E|[DBJ B]] Hk WHI MU WM WC; [left; exact E| right; split; [exact DBJ|]].
    pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC dE DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
    pose proof (bja_fb_apart _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ _ _ _ _ _ J FBx B) as [ESA ELA].
    eapply bja_munch; try eassumption.
    - cbn. split; [clear - ESA Hk; lia|]. split; [clear - ES WHI; lia| exact I].
    - intros BN. cbn. split; [pose proof (ELA BN) as EL; clear - EL Hk; lia|].
      split; [ddestruct (OWNE1 BN) as (_ & _ & _ & _ & EL5 & _); clear - EL5 WHI; lia| exact I].
  Qed.
  #[using="Type"] Lemma lval_app_lA : forall (xs zs : list word) n, 0 <= n <= Z.of_nat (length xs) -> lval (xs ++ zs) n = lval xs n.
  Proof. intros xs zs n Hn. unfold lval. rewrite firstn_app. replace (Z.to_nat n - length xs)%nat with 0%nat by (clear - Hn; lia). cbn [firstn]. rewrite app_nil_r. reflexivity. Qed.

  
  (* [comment removed for export] *)
  #[using="JC"] Lemma rideA_xl_munch : ltac2:(CDefT.buildp (gd_tbl_A_mpi_journey2 ()) "PdE,$6.Pv,$0.Pf,$0.Phc,(1.$29.VR,VHIA,)PLBc,(2.$3.)Pmc,P,(4.&40.)(5.(4.&8.))PdXc,$6.Pa,$0.Pb,$0.Pxs',(2.(4.&40.))Pm3,P,(4.&40.)(5.(4.&8.))Pwhi,$0.P,(7.$29.VR,VHIA,Vh,VLB,VLF,Vm,VdX,Vsp,Vlo,VFS,VFRAME,(8.$3.)R;.R:.R9.R8.R7.R6.)P,(2:.R=.R:.R9.R8.R7.)P,(1>.$36.(37.R8.)$34.)P,(11.(39.R9.)R8.)P,(11.R9.R8.)P,(11.R9.(1=.(39.R;.)(30.+4.(3:.R;.))))P,(11.R7.(13.&40.Vsp,))P,(2>.(19.(1:.$0.$0.)(1;.$0.$0.R<.R;.)(19.(1:.$0.$0.)(1;.$0.$0.Vlo,R8.)(8.(1:.$0.$0.))))R>.R9.)P,(2?.$29.R?.R:.)(2:.R15.R12.R11.R;.(31.(1<.R?.)(32.R?.)(3:.R?.)(39.R?.)R<.(33.R?.)(37.R?.)))")
(* [comment removed for export] *).
  Proof.
    intros dE v f hc LBc mc dXc a b xs' m3 whi J0 [E|[DBJ B]] EO Ha Hab Hb WHI MU WM; [left; exact E| right; split; [exact DBJ|]].
    jc_open; dpose (jca_facts asegs R HIA h LB LF m dX sp lo FS FRAME JC) as (LO0 & LOSP & SP64 & ALO' & ACP' & X0 & X16 & XAL & DSX & LEN & NR).
    pose proof (xa_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ _ _ _ _ _ _ J0) as (ND1 & LEN1 & NR1 & SG1' & CX1 & OWN0 & OWN1).
    ddestruct (OWN1 ltac:(rewrite EO; discriminate)) as (_ & N1 & XIN & XPAL & XARR & P0 & PC & PI & OP & P47).
    pose proof (bja_facts _ _ _ _ _ _ _ _ _ _ _ _ JC _ DBJ _ _ _ _ B) as (E0 & E16 & EAL & LENE & NRE & ES & OWNE0 & OWNE1).
    pose proof (xa_stkhi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J0) as HS1.
    pose proof (hcs_stack asegs R HIA hc) as SCS0. pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP0.
    assert (B3 : BJE dE hc LBc m3 dXc).
    { eapply bja_munch; try eassumption.
      - unfold w_client. apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [eapply aobj_crange; exact OP| clear - Ha; lia| clear - Hab Hb; lia]|].
        apply Forall_cons; [cbn [fst snd]; eapply crange_sub; [exact SCS0| clear - LOS; lia| rewrite HS1; clear - HTOP0 TOP LOSP WHI; lia]| apply Forall_nil].
      - cbn. split; [pose proof (bj_sepS _ _ _ _ _ _ _ _ _ _ B EO) as S1; clear - S1 Ha Hab Hb; lia|]. split; [clear - ES WHI; lia| exact I].
      - intros BN. cbn. split; [pose proof (bj_sepL _ _ _ _ _ _ _ _ _ _ B EO BN) as S2; clear - S2 Ha Hab Hb; lia|].
        split; [ddestruct (OWNE1 BN) as (_ & _ & _ & _ & EL5 & _); clear - EL5 WHI; lia| exact I]. }
    destruct B3 as [A1 A2 A3 A4 A5]. constructor; assumption.
  Qed.

  (* [comment removed for export] *)
  End RIDE.
