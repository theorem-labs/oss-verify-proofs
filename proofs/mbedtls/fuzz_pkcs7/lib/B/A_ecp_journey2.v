(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_grow P_ecp_group_free P_ecp_red P_ecp_mul_mod.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_ecp_stmtA
  A_mpi_opnd A_mpi_journey A_mpi_journey2 A_mpi_copy A_ecp_mul_mod A_ecp_journey.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_ecp_journey2 () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_journey.EJ"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_journey.ejtmp"; "EJ2.edis"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpd_keep"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "EJ2.etri"; "EJ2.eslot"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"].


Section EJ2.
  Local Notation segs := asegs.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA segs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Variables (h : HST segs R HIA) (LB LF : list blk) (m : mem) (SP lo FR : Z) (FRAME : list cell) (XO : list ivl) (MC : Z).
  Hypothesis EC : ECA R HIA h LB LF m SP lo FR FRAME XO MC.
  Local Ltac ec_open := pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC].
  Local Notation EJ0 := (EJ R HIA h LB LF m SP lo FR FRAME XO MC).
  Local Notation TMP := (ejtmp R HIA LB LF).

  (* [comment removed for export] *)
  Definition edis (d1 d2 : mpd) : Prop := md_own d1 = LHeap -> md_own d2 = LHeap -> md_p d1 <> md_p d2.
  #[using="Type"] Lemma edis_sym : forall d1 d2, edis d1 d2 -> edis d2 d1.
  Proof. intros d1 d2 H O2 O1 E. exact (H O1 O2 (eq_sym E)). Qed.

  (* [comment removed for export] *)
  #[using="EC"] Lemma ejtmp_keep : ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey2 ()) "Pv,$0.Pf,$0.Phk,(1.$2.VR,VHIA,)PLBk,(3.$4.)Pmk,P,(5.&40.)(6.(5.&8.))PA,$0.PdYk,$7.PB,$0.PdZ,$7.Pm',P,(5.&40.)(6.(5.&8.))Ph',(1.$2.VR,VHIA,)PLB',(3.$4.)PdY',$7.PSPc,$0.PXs,(3.$8.)P,(9.VR,VHIA,Vh,VLB,VLF,Vm,VSP,Vlo,VFR,VFRAME,VXO,VMC,R?.R>.R=.R<.R;.)P,(:.VR,VHIA,VLB,VLF,R>.R=.R<.R;.R:.)P,(:.VR,VHIA,VLB,VLF,R?.R>.R=.R:.R9.)P,(;.R<.R:.)P,(<.(=.VR,)(>.$4.VLB,(?.VLF,))VSP,(10.$2.VR,VHIA,Vh,)R<.+10.)P,(11.(12.(13.VR,)R7.)(12.R7.VSP,))P,(14.$2.VR,(15.R12.R?.)VLF,R8.(13.VR,)(16.$2.VR,VHIA,R13.)R7.R11.R<.)P,(17.R8.R?.+10.)P,P,(18.$19.(1:.R?.)$1;.)(17.R:.(1<.R10.)(1=.+4.(1>.R10.)))P,(1?.$2.R?.)P,Px,$0.P,(20.$2.VR,VHIA,R18.R1.)(20.$2.VR,VHIA,R11.R2.)P,(21.R17.R14.R?.R>.)P,(22.$2.R12.R10.R?.)P,Pb,$4.P,(23.$4.R1.(24.R11.))(25.(23.$4.R2.(24.R18.))(26.VR,(15.R1;.R18.)VLF,(27.$0.$0.R2.)(28.$0.$0.R2.)))(11.(:.VR,VHIA,VLB,VLF,R13.R12.R14.R16.R15.)(;.R11.R15.))")
(* [comment removed for export] *).
  Proof.
    ec_open. intros until Xs. intros J TY TZ DIS CWB HSP HP DXB DXL MI' HCS' OUT' MY' FRA'.
    dpose TZ as (MZ & EB & NSZ & FRSZ & OAZ). dpose OUT' as (EA' & NS' & O3 & O4 & O5).
    pose proof (ejtmp_blk R HIA h LB LF m SP lo FR FRAME XO MC v f hk LBk mk B dZ J TZ) as BLKZ.
    assert (KS : forall b, In b LB -> In b (mpd_keep LBk dYk)) by (intros b Hb; eapply ej_keep_sub; eassumption).
    assert (ZK : md_own dZ = LHeap -> In (md_p dZ, 4 * md_n dZ) (mpd_keep LBk dYk)).
    { intros EO. destruct (BLKZ EO) as (IN & _). apply In_mpd_keep_intro; [exact IN|].
      intros C. destruct (mpd_blk_heapE _ _ C) as [EOY E]. injection E as E1 E2. exact (DIS EOY EO (eq_sym E1)). }
    assert (CRB : client_range L (mpd_keep LBk dYk ++ fdata LF) SPc B 16).
    { intros a Ha. destruct (CWB a Ha) as [S|[D|(b & Hb & Hr)]]; [left; clear - S HSP; lia| right; left; exact D| right; right; exists b; split; [| exact Hr]].
      apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact (KS b Hb)| right; exact Hb]. }
    split.
    - split; [| split; [exact EB| split; [exact NSZ| split; [exact FRSZ|]]]].
      + split; [| exact (proj2 MZ)]. apply (mpdr_at_LB_one segs) with (LB := mpd_keep LBk dYk ++ fdata LF).
        * eapply (mpdr_at_presx segs L); [exact (proj1 MZ)| exact (presA_presx segs R _ _ _ _ _ _ _ _ HP)| exact (ej_mi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J)| exact MI'| rewrite EB; exact CRB| rewrite EB; exact DXB|].
          intros EO. split; [apply in_or_app; left; exact (ZK EO)| exact (DXL EO)].
        * intros EO. apply O4; [destruct (BLKZ EO) as (IN & _); exact IN|].
          intros C. destruct (mpd_blk_heapE _ _ C) as [EOY E]. injection E as E1 E2. exact (DIS EOY EO (eq_sym E1)).
      + eapply aobj_cs_mono; [exact HCS'|].
        eapply (presA_aobj0 segs R); [exact (hcs_ok segs R HIA hk)| exact HP| exact OAZ| intros x Hx; eapply hcs_below_top; exact Hx|].
        right. split; [exact CRB| exact (proj1 HSP)].
    - intros EOY' EOZ E. pose proof (ZK EOZ) as ZIN. ddestruct (BLKZ EOZ) as (_ & N1Z & _).
      pose proof MY' as [(_ & _ & _ & _ & _ & OW') _]. rewrite EOY' in OW'. destruct OW' as (N1Y & _).
      destruct (FRA' (md_p dY', 4 * md_n dY') ltac:(unfold mpd_blk; rewrite EOY'; left; reflexivity)) as [OLD|(_ & _ & _ & F3)].
      + destruct (mpd_blk_heapE _ _ OLD) as [EOY E2]. injection E2 as E3 E4. apply (DIS EOY EOZ). rewrite <- E3. exact E.
      + cbn [fst snd] in F3. specialize (F3 _ _ ltac:(apply in_or_app; left; exact ZIN)). clear - F3 E N1Z N1Y. lia.
  Qed.

  (* [comment removed for export] *)
  Definition eslot (A : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey2 ()) "(11.(<.(=.VR,)(>.$4.VLB,(?.VLF,))VSP,(10.$2.VR,VHIA,Vh,)O1.+10.)(11.(25.(12.(29.O1.+10.)Vlo,)(12.VSP,O1.))(11.Px,$0.P,(2:.VXO,R1.)(2:.(2;.(2<.$0.$0.)(2=.$0.$0.O1.(29.O1.+10.))(2>.(2<.$0.$0.)))R2.)(25.(12.(29.VMC,+8.)O1.)(12.(29.O1.+10.)VMC,)))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition etri (hk : HST segs R HIA) (LBk : list blk) (mk : mem) (A1 : Z) (d1 : mpd) (A2 : Z) (d2 : mpd) (A3 : Z) (d3 : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey2 ()) "(11.(:.VR,VHIA,VLB,VLF,O9.O8.O7.O6.O5.)(11.(:.VR,VHIA,VLB,VLF,O9.O8.O7.O4.O3.)(11.(:.VR,VHIA,VLB,VLF,O9.O8.O7.O2.O1.)(11.(;.O5.O3.)(11.(;.O5.O1.)(11.(;.O3.O1.)Pb,$4.P,(23.$4.R1.O8.)(25.(23.$4.R2.VLB,)(23.$4.R2.(>.$4.(24.O5.)(>.$4.(24.O3.)(24.O1.)))))))))))")
(* [comment removed for export] *).

  #[using="Type"] Lemma etri_swap12 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey2 ()) "Phk,(1.$2.VR,VHIA,)PLBk,(3.$4.)Pmk,P,(5.&40.)(6.(5.&8.))PA1,$0.Pd1,$7.PA2,$0.Pd2,$7.PA3,$0.Pd3,$7.P,(2?.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(2?.R:.R9.R8.R5.R4.R7.R6.R3.R2.)")
(* [comment removed for export] *).
  Proof.
    (intros hk LBk mk A1 d1 A2 d2 A3 d3 dd_H; ddestruct dd_H as (T1 & T2 & T3 & D12 & D13 & D23 & COV)).
    refine (conj T2 (conj T1 (conj T3 (conj (edis_sym _ _ D12) (conj D23 (conj D13 _)))))).
    intros b Hb. destruct (COV b Hb) as [K|K]; [left; exact K| right]. rewrite !in_app_iff in *. tauto.
  Qed.
  #[using="Type"] Lemma etri_swap13 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey2 ()) "Phk,(1.$2.VR,VHIA,)PLBk,(3.$4.)Pmk,P,(5.&40.)(6.(5.&8.))PA1,$0.Pd1,$7.PA2,$0.Pd2,$7.PA3,$0.Pd3,$7.P,(2?.R9.R8.R7.R6.R5.R4.R3.R2.R1.)(2?.R:.R9.R8.R3.R2.R5.R4.R7.R6.)")
(* [comment removed for export] *).
  Proof.
    (intros hk LBk mk A1 d1 A2 d2 A3 d3 dd_H; ddestruct dd_H as (T1 & T2 & T3 & D12 & D13 & D23 & COV)).
    refine (conj T3 (conj T2 (conj T1 (conj (edis_sym _ _ D23) (conj (edis_sym _ _ D13) (conj (edis_sym _ _ D12) _)))))).
    intros b Hb. destruct (COV b Hb) as [K|K]; [left; exact K| right]. rewrite !in_app_iff in *. tauto.
  Qed.

  (* [comment removed for export] *)
  #[using="EC"] Lemma etri_call : ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey2 ()) "Pv,$0.Pf,$0.Phk,(1.$2.VR,VHIA,)PLBk,(3.$4.)Pmk,P,(5.&40.)(6.(5.&8.))PA1,$0.Pd1,$7.PA2,$0.Pd2,$7.PA3,$0.Pd3,$7.Pm',P,(5.&40.)(6.(5.&8.))Ph',(1.$2.VR,VHIA,)PLB',(3.$4.)Pd1',$7.PSPc,$0.Pdv,$0.Pdf,$0.P,(9.VR,VHIA,Vh,VLB,VLF,Vm,VSP,Vlo,VFR,VFRAME,VXO,VMC,R12.R11.R10.R?.R>.)P,(2?.R11.R10.R?.R>.R=.R<.R;.R:.R9.)P,(30.R?.)P,(30.R>.)P,(30.R=.)P,(25.(12.(29.R12.+10.)R10.)(12.(29.R10.+10.)R12.))P,(25.(12.(29.R13.+10.)R?.)(12.(29.R?.+10.)R13.))P,(11.(12.Vlo,R:.)(12.R:.(31.VSP,VFR,)))P,(12.=R:.)P,(12.=R:.)P,(1?.$2.R11.)P,(32.$2.R12.Vlo,(31.VSP,VFR,))P,(14.$2.VR,(15.R1;.R18.)VLF,R?.(13.VR,)(16.$2.VR,VHIA,R1<.)(2;.(2<.$0.$0.)(2=.$0.$0.R19.(29.R19.+10.))(2>.(2<.$0.$0.)))R1:.R13.)P,(18.$0.(10.$2.VR,VHIA,R13.)(10.$2.VR,VHIA,R1=.))P,(18.$0.(16.$2.VR,VHIA,R14.)(16.$2.VR,VHIA,R1>.))P,(18.$0.(33.$2.VR,VHIA,R15.)(33.$2.VR,VHIA,R1?.))P,Px,$0.P,(20.$2.VR,VHIA,R21.R1.)(20.$2.VR,VHIA,R18.R2.)P,(12.(34.$2.VR,VHIA,R17.)(29.(34.$2.VR,VHIA,R21.)R13.))P,(12.(35.$2.VR,VHIA,R18.)(29.(35.$2.VR,VHIA,R22.)R13.))P,(36.$2.VR,VHIA,R19.R18.VLF,R1:.)P,(22.$2.R1;.R19.R18.)P,(21.R24.R21.R1:.R19.)P,Pb,$4.P,(23.$4.R1.(24.R1;.))(25.(23.$4.R2.(24.R24.))(26.VR,(15.R27.R24.)VLF,(27.$0.$0.R2.)(28.$0.$0.R2.)))(11.(9.VR,VHIA,Vh,VLB,VLF,Vm,VSP,Vlo,VFR,VFRAME,VXO,VMC,(29.R29.R19.)(29.R28.R18.)R1=.R1<.R1>.)(2?.R1=.R1<.R1>.R24.R1;.R22.R21.R20.R1?.))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose (ej_facts R HIA h LB LF m SP lo FR FRAME XO MC EC) as (LO0 & ALO & ACP & MCLO & SPHI).
    intros until df. (intros J dd_H; ddestruct dd_H as (T1 & T2 & T3 & D12 & D13 & D23 & COV); intros dd_H; ddestruct dd_H as (CW1 & SL1 & XI1 & MS1); intros dd_H; ddestruct dd_H as (CW2 & SL2 & _ & _); intros dd_H; ddestruct dd_H as (CW3 & SL3 & _ & _); intros S12 S13 HSP Hdv Hdf MI' ST' HP HT' HS' HF' HCS' HV' HFR' HH' M1' OUT' FRA').
    assert (HSP2 : arl_stklo R <= SPc <= SP) by (clear - HSP LOS FR0; lia).
    assert (CRA : forall A, client_wrange L (LB ++ fdata LF) SP (htop segs R HIA h) A 16 -> client_range L (LB ++ fdata LF) lo A 16).
    { intros A CW a Ha. destruct (CW a Ha) as [S|[D|B]]; [left; clear - S SLO FR0; lia| right; left; exact D| right; right; exact B]. }
    assert (LAP : forall B dZ, TMP hk LBk mk B dZ -> md_own dZ = LHeap -> disjoint_from [(A1, A1 + 16)] (md_p dZ) (4 * md_n dZ)).
    { intros B dZ TZ EO. ddestruct (ejtmp_blk R HIA h LB LF m SP lo FR FRAME XO MC v f hk LBk mk B dZ J TZ EO) as (_ & N1 & _ & _ & _ & _ & FRA).
      destruct (fresh_apart_client R LB LF lo A1 16 _ _ FRA (CRA A1 CW1) ltac:(clear; lia) ltac:(clear - N1; lia) ltac:(clear - ALO LOS; lia)) as [K|K];
        cbn [disjoint_from fst snd]; (split; [clear - K; lia| exact I]). }
    pose proof (ej_aobj_call R HIA h LB LF m SP lo FR FRAME XO MC v f hk LBk mk A1 d1 m' h' SPc _ J T1 CW1 HSP2 HP HCS') as OA1'.
    pose proof (ej_mc_call R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk A1 d1 m' SPc _ J T1 HP ltac:(cbn [disjoint_from fst snd]; split; [clear - MS1; lia| exact I])) as MC'.
    destruct (ej_call R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk A1 d1 m' h' LB' d1' SPc dv df [(A1, A1 + 16)] J T1
                ltac:(clear - HSP; lia) Hdv Hdf MI' ST' HP XI1 ltac:(cbn [disjoint_from fst snd]; split; [clear - SL1 FR0 SLO; lia| exact I]) ltac:(clear - HSP; lia)
                HT' HS' HF' HCS' HV' HFR' HH' M1' OUT' FRA' OA1' MC') as [J' T1'].
    destruct (ejtmp_keep v f hk LBk mk A1 d1 A2 d2 m' h' LB' d1' SPc _ J T1 T2 D12 CW2 HSP2 HP
                ltac:(cbn [disjoint_from fst snd]; split; [clear - S12; lia| exact I]) (LAP A2 d2 T2) MI' HCS' OUT' M1' FRA') as [T2' D12'].
    destruct (ejtmp_keep v f hk LBk mk A1 d1 A3 d3 m' h' LB' d1' SPc _ J T1 T3 D13 CW3 HSP2 HP
                ltac:(cbn [disjoint_from fst snd]; split; [clear - S13; lia| exact I]) (LAP A3 d3 T3) MI' HCS' OUT' M1' FRA') as [T3' D13'].
    split; [exact J'|]. refine (conj T1' (conj T2' (conj T3' (conj D12' (conj D13' (conj D23 _)))))).
    dpose OUT' as (_ & _ & O3 & _ & O5).
    intros b Hb. destruct (O3 b Hb) as [K1|K1]; [| right; apply in_or_app; left; exact K1].
    destruct (COV b K1) as [K2|K2]; [left; exact K2| right]. rewrite !in_app_iff in *. destruct K2 as [K2|K2]; [left; rewrite (O5 b K2 Hb); exact K2| right; exact K2].
    all: match goal with |- ?g => idtac "TRI-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  #[using="EC"] Lemma ejtmp_scratch : ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey2 ()) "Pv,$0.Pf,$0.Phk,(1.$2.VR,VHIA,)PLBk,(3.$4.)Pmk,P,(5.&40.)(6.(5.&8.))PB,$0.PdZ,$7.Pwlo,$0.Pwhi,$0.Pm',P,(5.&40.)(6.(5.&8.))P,(9.VR,VHIA,Vh,VLB,VLF,Vm,VSP,Vlo,VFR,VFRAME,VXO,VMC,R:.R9.R8.R7.R6.)P,(:.VR,VHIA,VLB,VLF,R9.R8.R7.R6.R5.)P,(25.(12.(29.R7.+10.)Vlo,)(12.VSP,R7.))P,(37.(2;.(2<.$0.$0.)(2=.$0.$0.R6.R5.)(2>.(2<.$0.$0.)))R9.R4.)P,(38.$2.R:.R5.)P,(12.Vlo,R8.)P,(12.R8.(31.VSP,VFR,))(:.VR,VHIA,VLB,VLF,R?.R>.R8.R<.R;.)")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose (ej_facts R HIA h LB LF m SP lo FR FRAME XO MC EC) as (LO0 & ALO & ACP & MCLO & SPHI).
    intros v f hk LBk mk B dZ wlo whi m' J T ASL MU WM W1 W2. dpose T as (MY & EA & NS & FRS & OA).
    pose proof (ejtmp_blk R HIA h LB LF m SP lo FR FRAME XO MC v f hk LBk mk B dZ J T) as BLK.
    pose proof (hcs_ok segs R HIA hk) as CSOK.
    assert (SCS : crange (hcs segs R HIA hk) lo (SP - lo)).
    { eapply crange_sub; [exact (hcs_stack segs R HIA hk)| clear - LOS; lia| rewrite (ej_stkhi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J); clear - SPHI; lia]. }
    assert (WC : w_client (hcs segs R HIA hk) [(wlo, whi)]).
    { unfold w_client. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros x Hx. apply SCS. clear - Hx W1 W2 FR0. lia. }
    split; [| split; [exact EA| split; [exact NS| split; [exact FRS|]]]].
    - eapply mpd_at_munch_any; [exact MY| exact MU| exact WM| |].
      + rewrite EA. cbn [disjoint_from fst snd]. split; [clear - ASL W1 W2 FR0; lia| exact I].
      + intros ON. assert (EO : md_own dZ = LHeap) by (destruct (md_own dZ); [exfalso; exact (ON eq_refl)| reflexivity| exfalso; exact (NS eq_refl)]).
        ddestruct (BLK EO) as (_ & _ & _ & B2 & _). cbn [disjoint_from fst snd]. split; [clear - B2 ALO LOS W1; lia| exact I].
    - eapply (aobj_munch segs AL _ CSOK [(wlo, whi)] mk m'); [exact WC| exact MU| exact OA].
  Qed.

  #[using="EC"] Lemma etri_scratch : ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey2 ()) "Pv,$0.Pf,$0.Phk,(1.$2.VR,VHIA,)PLBk,(3.$4.)Pmk,P,(5.&40.)(6.(5.&8.))PA1,$0.Pd1,$7.PA2,$0.Pd2,$7.PA3,$0.Pd3,$7.Pwlo,$0.Pwhi,$0.Pm',P,(5.&40.)(6.(5.&8.))P,(9.VR,VHIA,Vh,VLB,VLF,Vm,VSP,Vlo,VFR,VFRAME,VXO,VMC,R>.R=.R<.R;.R:.)P,(2?.R=.R<.R;.R:.R9.R8.R7.R6.R5.)P,(30.R;.)P,(30.R:.)P,(30.R9.)P,(37.(2;.(2<.$0.$0.)(2=.$0.$0.R8.R7.)(2>.(2<.$0.$0.)))R?.R6.)P,(38.$2.R10.R7.)P,(1?.$2.R8.)P,(32.$2.R9.Vlo,(31.VSP,VFR,))P,(36.$2.VR,VHIA,R15.R14.VLF,R:.)P,(12.Vlo,R=.)P,(12.R=.(31.VSP,VFR,))(11.(9.VR,VHIA,Vh,VLB,VLF,Vm,VSP,Vlo,VFR,VFRAME,VXO,VMC,R1:.R19.R18.R17.R=.)(2?.R18.R17.R=.R15.R14.R13.R12.R11.R10.))")
(* [comment removed for export] *).
  Proof.
    intros until m'. (intros J dd_H; ddestruct dd_H as (T1 & T2 & T3 & D12 & D13 & D23 & COV); intros dd_H; ddestruct dd_H as (_ & SL1 & _); intros dd_H; ddestruct dd_H as (_ & SL2 & _); intros dd_H; ddestruct dd_H as (_ & SL3 & _); intros MU WM MI' ST' HH' W1 W2).
    destruct (ej_scratch R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk A1 d1 wlo whi m' J T1 SL1 MU WM MI' ST' HH' W1 W2) as [J' T1'].
    split; [exact J'|].
    refine (conj T1' (conj (ejtmp_scratch v f hk LBk mk A2 d2 wlo whi m' J T2 SL2 MU WM W1 W2) (conj (ejtmp_scratch v f hk LBk mk A3 d3 wlo whi m' J T3 SL3 MU WM W1 W2) (conj D12 (conj D13 (conj D23 COV)))))).
  Qed.
End EJ2.

