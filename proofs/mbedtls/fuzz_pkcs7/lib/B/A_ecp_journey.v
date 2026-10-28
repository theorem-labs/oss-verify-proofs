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
  A_mpi_opnd A_mpi_journey A_mpi_journey2 A_mpi_copy A_ecp_mul_mod.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_ecp_journey () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "EJ.EJ"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "EJ.ejtmp"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpd_keep"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.outside"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.opnd_sep"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_writableA"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_aobjA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpd_imgA"; "EJ.ej_ext"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.ecp_grp"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_grp_preA"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.grp_mpds"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_sg"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "Stdlib.Lists.List.flat_map"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "Corelib.Init.Datatypes.length"].


Section EJ.
  Local Notation segs := asegs.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA segs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  (* [comment removed for export] *)
  Variables (h : HST segs R HIA) (LB LF : list blk) (m : mem) (SP lo FR : Z) (FRAME : list cell) (XO : list ivl) (MC : Z).

  Record ECA : Prop := {
    eca_NEEDR : 0 <= arl_need_rt R;
    eca_HND : forall h LB LF m, HM segs R HIA h LB LF m -> List.NoDup (map fst LB);
    eca_DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L;
    eca_ROIMG : forall a, ro_addr segs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L;
    eca_HH : HM segs R HIA h LB LF m;
    eca_MI : mem_inv segs m;
    eca_LOS : arl_stklo R <= lo;
    eca_FR0 : 0 <= FR;
    eca_FSZ : Z.of_nat (cells_size FRAME) = FR;
    eca_SLO : lo <= SP - FR;
    eca_TOP : SP <= htop segs R HIA h;
    eca_MCOK : mc_okA R MC;
    eca_XOMC : forall a, outside XO a -> ~ (MC <= a < MC + 8) }.
  Hypothesis EC : ECA.
  Local Ltac ec_open := pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC].

  (* [comment removed for export] *)
  Record EJ (v f : Z) (hk : HST segs R HIA) (LBk : list blk) (mk : mem) : Prop := {
    ej_hm : HM segs R HIA hk LBk LF mk;
    ej_sub : forall b, In b LB -> In b LBk;
    ej_pres : presA segs R LB LF SP (arl_stklo R) (hstkhi segs R HIA h) XO m mk;
    ej_mi : mem_inv segs mk;
    ej_top : htop segs R HIA hk = htop segs R HIA h;
    ej_stkhi : hstkhi segs R HIA hk = hstkhi segs R HIA h;
    ej_flag : hflag segs R HIA hk = hflag segs R HIA h;
    ej_hcs : forall x, hcs segs R HIA h x -> hcs segs R HIA hk x;
    ej_vol : havol segs R HIA hk <= havol segs R HIA h + v;
    ej_frs : hfr segs R HIA hk <= hfr segs R HIA h + f;
    ej_mc : exists c, rw_cells segs mk MC [C8 c];
    ej_stk : stk segs mk lo (SP - FR);
    ej_fr : rw_cells segs mk (SP - FR) FRAME }.

  (* [comment removed for export] *)
  Definition ejtmp (hk : HST segs R HIA) (LBk : list blk) (mk : mem) (A : Z) (d : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey ()) "(0.(1.$2.O3.O4.O1.)(0.(3.$4.(5.O1.)O2.)(0.(6.(3.$7.(8.O1.)$9.))(0.Pb,$:.P,(;.$:.R1.(<.O1.))(0.(6.(;.$:.R2.VLB,))(=.VR,VLB,VLF,(>.$4.$4.R2.)(?.$4.$4.R2.)))(10.$2.(11.VR,)(12.$2.VR,VHIA,O5.)O3.O2.+10.)))))")
(* [comment removed for export] *).

  #[using="LB LF m FR FRAME XO EC"] Lemma ej_facts : ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey ()) "(0.(13.=Vlo,)(0.(13.(14.(15.VR,))(16.VR,))(0.(17.+1000.(14.(15.VR,)))(0.(13.(18.VMC,+8.)Vlo,)(13.VSP,(19.$2.VR,VHIA,Vh,))))))")
(* [comment removed for export] *).
  Proof.
    ec_open. pose proof (art_lo segs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := L)) as ACP. pose proof (art_data_lo segs R HIA) as DLO.
    ddestruct MCOK as (MC1 & MC2 & _). pose proof (hm_top segs R HIA h LB LF m HH) as HT.
    repeat split; try assumption; clear - ALO ACP DLO LOS MC2 HT TOP; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="EC"] Lemma ej_start : ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey ()) "Pm1,P,(1:.&40.)(1;.(1:.&8.))Pcnt,(1:.&40.)P,(1<.(1=.(1>.$4.$4.)(1?.$4.$4.Vlo,VSP,)(20.(1>.$4.$4.)))Vm,R2.)P,(21.$2.Vm,R3.)P,(22.$2.VR,VHIA,Vh,VLB,VLF,R4.)P,(23.$2.R5.)P,(24.$2.R6.Vlo,(25.VSP,VFR,))P,(26.$2.R7.(25.VSP,VFR,)VFRAME,)P,(26.$2.Vm,VMC,(1=.$27.(28.R7.)(20.$27.)))(29.==Vh,VLB,R9.)")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose ej_facts as (LO0 & ALO & ACP & MCLO & SPHI).
    intros m1 cnt MU WM HH1 MI1 ST1 FR1 MC0.
    constructor; try assumption; try reflexivity.
    - intros b Hb; exact Hb.
    - apply presA_nil_any. eapply (presA_tail0 segs R HIA h LB); [exact HH| intros b Hb; exact Hb| exact LOS| exact TOP| exact MU| exact WM].
    - intros x Hx; exact Hx.
    - clear; lia.
    - clear; lia.
    - exists cnt. eapply rw_cells_transport; [exact MC0| exact MU| exact WM|]. cbn [cells_size csize Nat.add disjoint_from fst snd]. split; [clear - MCLO; lia| exact I].
    all: match goal with |- ?g => idtac "START-LEFT:" g end.
  Qed.

  #[using="Type"] Lemma mpd_blk_heapE : forall d b, In b (mpd_blk d) -> md_own d = LHeap /\ b = (md_p d, 4 * md_n d).
  Proof. intros d b Hb. unfold mpd_blk in Hb. destruct (md_own d); [destruct Hb| | destruct Hb]. destruct Hb as [<-|[]]. split; reflexivity. Qed.

  #[using="Type"] Lemma fresh_apart_sub : ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey ()) "PLB1,(2:.$:.)PLB2,(2:.$:.)PN,$4.Pk,$4.P,(=.VR,R4.VLF,R2.R1.)P,Pb,$:.P,(;.$:.R1.R5.)(;.$:.R2.R7.)(=.VR,R5.VLF,R4.R3.)")
(* [comment removed for export] *).
  Proof.
    (intros LB1 LB2 N k dd_H; ddestruct dd_H as (F0 & F1 & F2 & F3); intros SUB). split; [exact F0|]. split; [exact F1|]. split; [exact F2|].
    intros B j Hb. apply F3. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply SUB; exact Hb| right; exact Hb].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma ej_keep_sub : ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey ()) "Pv,$4.Pf,$4.Phk,(2;.$2.VR,VHIA,)PLBk,(2:.$:.)Pmk,P,(1:.&40.)(1;.(1:.&8.))PA,$4.PdYk,$2<.Pb,$:.P,(29.R8.R7.R6.R5.R4.)P,(2=.R7.R6.R5.R4.R3.)P,(;.$:.R3.VLB,)(;.$:.R4.(2>.R8.R5.))")
(* [comment removed for export] *).
  Proof.
    (intros v f hk LBk mk A dYk b J dd_H; ddestruct dd_H as (_ & _ & _ & FRS & _); intros Hb). apply In_mpd_keep_intro; [exact (ej_sub _ _ _ _ _ J b Hb)|].
    intros C. exact (proj1 (FRS b C) Hb).
  Qed.

  (* [comment removed for export] *)
  #[using="EC"] Lemma ej_call : ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey ()) "Pv,$4.Pf,$4.Phk,(2;.$2.VR,VHIA,)PLBk,(2:.$:.)Pmk,P,(1:.&40.)(1;.(1:.&8.))PA,$4.PdYk,$2<.Pm',P,(1:.&40.)(1;.(1:.&8.))Ph',(2;.$2.VR,VHIA,)PLB',(2:.$:.)PdY',$2<.PSPc,$4.Pdv,$4.Pdf,$4.PXs,(2:.$2?.)P,(29.R?.R>.R=.R<.R;.)P,(2=.R>.R=.R<.R;.R:.)P,(13.R6.(25.VSP,VFR,))P,(13.=R6.)P,(13.=R6.)P,(23.$2.R=.)P,(24.$2.R>.Vlo,(25.VSP,VFR,))P,(30.$2.VR,(2>.R13.R10.)VLF,R;.(16.VR,)(19.$2.VR,VHIA,R14.)R8.R12.R?.)P,Px,$4.P,(31.VXO,R1.)(31.R;.R2.)P,(32.R:.(25.VSP,VFR,)VFR,)P,(13.Vlo,R>.)P,(3.$4.(33.$2.VR,VHIA,R12.)(33.$2.VR,VHIA,R18.))P,(3.$4.(19.$2.VR,VHIA,R13.)(19.$2.VR,VHIA,R19.))P,(3.$4.(34.$2.VR,VHIA,R14.)(34.$2.VR,VHIA,R1:.))P,Px,$4.P,(12.$2.VR,VHIA,R1<.R1.)(12.$2.VR,VHIA,R17.R2.)P,(13.(35.$2.VR,VHIA,R16.)(18.(35.$2.VR,VHIA,R1<.)R12.))P,(13.(36.$2.VR,VHIA,R17.)(18.(36.$2.VR,VHIA,R1=.)R12.))P,(22.$2.VR,VHIA,R18.R17.VLF,R19.)P,(1.$2.R1:.R18.R17.)P,(37.R1?.R1<.R19.R18.)P,Pb,$:.P,(;.$:.R1.(<.R1:.))(38.(;.$:.R2.(<.R1?.))(=.VR,(2>.R22.R1?.)VLF,(>.$4.$4.R2.)(?.$4.$4.R2.)))P,(10.$2.(11.VR,)(12.$2.VR,VHIA,R1<.)R1=.R1?.+10.)P,(39.(1:.&40.)Lc,(1:.&40.)(26.$2.R1?.VMC,(1=.$27.(28.R1.)(20.$27.))))(0.(29.(18.R26.R1:.)(18.R25.R19.)R1>.R1=.R1?.)(2=.R1>.R1=.R1?.R21.R1<.))")
(* [comment removed for export] *).
  Proof.
    ec_open. intros until Xs. intros J T HSP Hdv Hdf MI' ST' HP HXs DFR HLO HT' HS' HF' HCS' HV' HFR' HH' MX' OUT' FRA' OA' MC'.
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    dpose T as (MYk & EAk & NSk & FRSk & OAk). dpose OUT' as (EA' & NS' & O3 & O4 & O5).
    assert (KS : forall b, In b LB -> In b (mpd_keep LBk dYk)) by (intros b Hb; eapply ej_keep_sub; eassumption).
    split.
    - constructor; try assumption.
      + intros b Hb. apply O4; [exact (SUBk b Hb)|]. intros C. exact (proj1 (FRSk b C) Hb).
      + eapply presA_trans; [exact PXk|]. rewrite HSk in HP.
        eapply presA_weaken; [exact HP| exact KS| intros b Hb; exact Hb| clear - HSP FR0; lia| apply Z.le_refl| apply Z.le_refl| exact HXs].
      + rewrite HT'. exact HTk.
      + rewrite HS'. exact HSk.
      + rewrite HF'. exact HFk.
      + intros x Hx. apply HCS'. apply HCSk. exact Hx.
      + clear - HVk HV'. lia.
      + clear - HFRk HFR'. lia.
      + eapply (presA_rw_cells segs R); [exact HP| exact FRk| | rewrite FSZ; exact DFR].
        rewrite FSZ. intros x Hx. left. clear - Hx HSP. lia.
    - split; [exact MX'|]. split; [rewrite EA'; exact EAk|]. split; [exact NS'|]. split; [| exact OA'].
      intros b Hb. destruct (FRA' b Hb) as [OLD|NEW]; [exact (FRSk b OLD)|].
      pose proof (fresh_apart_sub _ LB _ _ NEW KS) as FRo. split; [| exact FRo].
      intros C. destruct (mpd_blk_heapE _ _ Hb) as [EO ->]. cbn [fst snd] in *.
      pose proof MX' as [(_ & _ & _ & _ & _ & OW) _]. rewrite EO in OW. destruct OW as (N1 & _).
      ddestruct FRo as (_ & _ & _ & F3). specialize (F3 _ _ ltac:(apply in_or_app; left; exact C)). clear - F3 N1. lia.
    all: match goal with |- ?g => idtac "CALL-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma ejtmp_blk : ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey ()) "Pv,$4.Pf,$4.Phk,(2;.$2.VR,VHIA,)PLBk,(2:.$:.)Pmk,P,(1:.&40.)(1;.(1:.&8.))PA,$4.PdYk,$2<.P,(29.R7.R6.R5.R4.R3.)P,(2=.R6.R5.R4.R3.R2.)P,(3.$7.(8.R3.)$3:.)(0.(;.(1>.$4.$4.)(1?.$4.$4.(3;.R4.)(3<.+4.(3=.R4.)))R7.)(0.(13.+1.(3=.R4.))(0.(17.=(3;.R4.))(0.(13.(18.(3;.R4.)(3<.+4.(3=.R4.)))(14.(15.VR,)))(0.(38.(13.(18.(3;.R4.)(3<.+4.(3=.R4.)))(3>.(15.VR,)))(13.(3?.(15.VR,))(3;.R4.)))(0.(6.(;.(1>.$4.$4.)(1?.$4.$4.(3;.R4.)(3<.+4.(3=.R4.)))VLB,))(=.VR,VLB,VLF,(3;.R4.)(3<.+4.(3=.R4.)))))))))")
(* [comment removed for export] *).
  Proof.
    (intros v f hk LBk mk A dYk J dd_H; ddestruct dd_H as (MY & _ & _ & FRS & _); intros EO).
    pose proof MY as [(_ & _ & _ & _ & _ & OW) _]. rewrite EO in OW. ddestruct OW as (N1 & IN & _).
    destruct (hm_apart segs R HIA hk LBk LF mk (ej_hm _ _ _ _ _ J)) as [HF0 _]. rewrite Forall_forall in HF0.
    destruct (HF0 _ ltac:(apply in_or_app; left; exact IN)) as (B0 & _ & B2 & B3). cbn [fst snd] in B0, B2, B3.
    destruct (FRS (md_p dYk, 4 * md_n dYk) ltac:(unfold mpd_blk; rewrite EO; left; reflexivity)) as [NIN FRA]. cbn [fst snd] in FRA.
    exact (conj IN (conj N1 (conj B0 (conj B2 (conj B3 (conj NIN FRA)))))).
  Qed.

  (* [comment removed for export] *)
  #[using="EC"] Lemma ej_opY : ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey ()) "Pv,$4.Pf,$4.Phk,(2;.$2.VR,VHIA,)PLBk,(2:.$:.)Pmk,P,(1:.&40.)(1;.(1:.&8.))PA,$4.PdYk,$2<.PSPc,$4.P,(29.R8.R7.R6.R5.R4.)P,(2=.R7.R6.R5.R4.R3.)P,(40.(15.VR,)(41.$:.VLB,(42.VLF,))VSP,(33.$2.VR,VHIA,Vh,)R5.+10.)P,(38.(13.(18.R6.+10.)Vlo,)(13.VSP,R6.))P,(0.(13.Vlo,R5.)(13.R5.VSP,))(0.(1.$2.R9.R:.R7.)(0.(6.(3.$7.(8.R7.)$9.))(0.(3.$4.(5.R7.)R8.)(0.(43.R7.R7.Vlo,R6.)(0.(44.(15.VR,)(41.$:.R:.(42.VLF,))Vlo,R8.+10.)(0.P,(3.$7.(8.R7.)$3:.)(44.(15.VR,)(41.$:.R;.(42.VLF,))Vlo,(3;.R8.)(3<.+4.(3=.R8.)))(0.(45.VR,R:.VLF,R6.(33.$2.VR,VHIA,R;.)R7.)(0.P,(6.(3.$7.(8.R7.)$46.))(38.(13.(18.(3;.R8.)(3<.+4.(3=.R8.)))Vlo,)(13.R7.(3;.R8.)))(0.(47.$2.(11.VR,)(12.$2.VR,VHIA,R;.)R9.R7.)(48.R7.))))))))))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose ej_facts as (LO0 & ALO & ACP & MCLO & SPHI).
    intros v f hk LBk mk A dYk SPc J T CWA ASL HSP. dpose T as (MY & EA & NS & FRS & OA).
    pose proof (ejtmp_blk v f hk LBk mk A dYk J T) as BLK.
    assert (OWH : md_own dYk <> LNull -> md_own dYk = LHeap) by (destruct (md_own dYk); [intros C; exfalso; exact (C eq_refl)| reflexivity| intros _; exfalso; exact (NS eq_refl)]).
    assert (CRA : client_range L (LB ++ fdata LF) lo A 16).
    { intros a Ha. destruct (CWA a Ha) as [S|[D|B]]; [left; clear - S SLO FR0; lia| right; left; exact D| right; right; exact B]. }
    assert (SAP : md_own dYk = LHeap -> A + 16 <= md_p dYk \/ md_p dYk + 4 * md_n dYk <= A).
    { intros EO. ddestruct (BLK EO) as (_ & N1 & _ & _ & _ & _ & FRA).
      destruct (fresh_apart_client R LB LF lo A 16 _ _ FRA CRA ltac:(clear; lia) ltac:(clear - N1; lia) ltac:(clear - ALO LOS; lia)) as [K|K]; [right| left]; clear - K; lia. }
    assert (LST : md_own dYk <> LNull -> md_p dYk + 4 * md_n dYk <= lo).
    { intros ON. ddestruct (BLK (OWH ON)) as (_ & _ & _ & B2 & _). clear - B2 ALO LOS. lia. }
    split; [exact MY|]. split; [exact NS|]. split; [exact EA|].
    split.
    { unfold opnd_sep. rewrite EA.
      split; [intros ON; exact (SAP (OWH ON))|]. split; [exact SAP|]. split; [left; reflexivity|].
      split; [clear - ASL HSP; lia|]. intros ON. left. exact (LST ON). }
    split; [intros a Ha; destruct (CRA a Ha) as [S|[D|(b & Hb & Hr)]]; [left; exact S| right; left; exact D| right; right; exists b; split; [| exact Hr]];
            apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; exact (ej_sub _ _ _ _ _ J b Hb)| right; exact Hb]|].
    split.
    { intros EO. destruct (BLK EO) as (IN & _). eapply client_range_block; [apply in_or_app; left; exact IN| clear; lia| clear; lia]. }
    split.
    { split; [| rewrite EA; exact SAP]. rewrite EA, (ej_top _ _ _ _ _ J).
      intros a Ha. destruct (CWA a Ha) as [S|[D|(b & Hb & Hr)]]; [left; clear - S HSP; lia| right; left; exact D| right; right; exists b; split; [| exact Hr]].
      apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; exact (ej_sub _ _ _ _ _ J b Hb)| right; exact Hb]. }
    split; [intros ON; left; exact (LST ON)|].
    split; [split; [rewrite EA; exact OA| intros ES; exfalso; exact (NS ES)]| intros ES; exfalso; exact (NS ES)].
    all: match goal with |- ?g => idtac "OPY-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  Definition ej_ext (A : Z) (e : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey ()) "(0.(1.$2.Vm,VLB,O1.)(0.(44.(15.VR,)(41.$:.VLB,(42.VLF,))Vlo,(5.O1.)+10.)(0.(38.(13.(18.(5.O1.)+10.)Vlo,)(13.VSP,(5.O1.)))(0.P,(6.(3.$7.(8.O1.)$46.))(38.(13.(18.(3;.O1.)(3<.+4.(3=.O1.)))Vlo,)(13.VSP,(3;.O1.)))(0.(32.VXO,(5.O1.)+10.)(0.P,(3.$7.(8.O1.)$3:.)(32.VXO,(3;.O1.)(3<.+4.(3=.O1.)))(0.(38.(13.(18.O2.+10.)(5.O1.))(13.(18.(5.O1.)+10.)O2.))(0.P,(6.(3.$7.(8.O1.)$46.))(38.(13.(18.O2.+10.)(3;.O1.))(13.(18.(3;.O1.)(3<.+4.(3=.O1.)))O2.))(0.(47.$2.(11.VR,)(12.$2.VR,VHIA,Vh,)Vm,O1.)(48.O1.))))))))))")
(* [comment removed for export] *).

  #[using="IMG EC"] Lemma ej_opE : ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey ()) "Pv,$4.Pf,$4.Phk,(2;.$2.VR,VHIA,)PLBk,(2:.$:.)Pmk,P,(1:.&40.)(1;.(1:.&8.))PA,$4.PdYk,$2<.Pe,$2<.PSPc,$4.P,(29.R9.R8.R7.R6.R5.)P,(2=.R8.R7.R6.R5.R4.)P,(49.R6.R4.)P,(0.(13.Vlo,R4.)(13.R4.VSP,))(0.(1.$2.R9.R:.R6.)(0.(4:.R7.R6.)(0.(6.(3.$4.(5.R7.)(5.R6.)))(0.(43.R7.R6.Vlo,R5.)(0.(44.(15.VR,)(41.$:.R:.(42.VLF,))Vlo,(5.R6.)+10.)(0.P,(3.$7.(8.R6.)$3:.)(44.(15.VR,)(41.$:.R;.(42.VLF,))Vlo,(3;.R7.)(3<.+4.(3=.R7.)))(47.$2.(11.VR,)(12.$2.VR,VHIA,R;.)R9.R6.)))))))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose ej_facts as (LO0 & ALO & ACP & MCLO & SPHI).
    (intros v f hk LBk mk A dYk e SPc J T dd_H; ddestruct dd_H as (ME & CRE & ESL & ELL & EXO & EXOL & EAS & EAL & [OAs OAl] & IME); intros HSP).
    dpose T as (MY & EA & NS & FRS & OA). pose proof (ejtmp_blk v f hk LBk mk A dYk J T) as BLK.
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    pose proof ME as [(_ & _ & E0 & ELEN & ENR & EOW) ESG]. unfold MPI_MAX_LIMBS in ENR.
    assert (EIN : md_own e = LHeap -> In (md_p e, 4 * md_n e) LB /\ 1 <= md_n e) by (intros EO; rewrite EO in EOW; ddestruct EOW as (N1 & IN & _); exact (conj IN N1)).
    assert (CRS : client_range L (LB ++ fdata LF) SP (md_addr e) 16).
    { intros a Ha. destruct (CRE a Ha) as [S|[D|B]]; [| right; left; exact D| right; right; exact B].
      destruct ESL as [K|K]; [exfalso; clear - S Ha K; lia| left; clear - Ha K; lia]. }
    split.
    { split; [| exact ESG]. apply (mpdr_at_LB_one segs) with (LB := LB ++ fdata LF).
      - eapply (mpdr_at_presx segs L); [exact (proj1 ME)| exact (presA_presx segs R _ _ _ _ _ _ _ _ PXk)| exact MIm| exact MIk| exact CRS| exact EXO|].
        intros EO. split; [apply in_or_app; left; exact (proj1 (EIN EO))| exact (EXOL EO)].
      - intros EO. exact (SUBk _ (proj1 (EIN EO))). }
    split; [right; rewrite EA; exact EAS|]. split; [rewrite EA; clear - EAS; lia|].
    split.
    { unfold opnd_sep. rewrite EA.
      split; [exact EAL|].
      split.
      { intros EO. ddestruct (BLK EO) as (_ & N1 & _ & _ & _ & _ & FRA).
        destruct (fresh_apart_client R LB LF lo (md_addr e) 16 _ _ FRA CRE ltac:(clear; lia) ltac:(clear - N1; lia) ltac:(clear - ALO LOS; lia)) as [K|K]; [right| left]; clear - K; lia. }
      split.
      { destruct (limb_own_eq_dec (md_own dYk) LHeap) as [EO|NEO]; [| right; left; exact NEO].
        ddestruct (BLK EO) as (_ & N1 & _ & _ & BIMG & _ & (_ & _ & _ & F3)).
        destruct (md_own e) eqn:OE; [right; right; left; reflexivity| |].
        - right; right; right. destruct (EIN eq_refl) as [IN N1e]. specialize (F3 _ _ ltac:(apply in_or_app; left; exact IN)). clear - F3. lia.
        - right; right; right. ddestruct EOW as (N1e & _ & P0 & PB & PRO). pose proof (bytes_at_bound _ _ _ _ PB) as PBB. rewrite u32s_length in PBB.
          pose proof (ROIMG _ (PRO 0 ltac:(clear - N1e; lia)) ltac:(clear - P0 PBB N1e ELEN; lia)) as R0. rewrite Z.add_0_r in R0.
          pose proof (ROIMG _ (PRO (4 * md_n e - 1) ltac:(clear - N1e; lia)) ltac:(clear - P0 PBB N1e ELEN; lia)) as R1.
          clear - BIMG R0 R1. lia. }
      split; [clear - ESL HSP; lia|]. intros ON. destruct (ELL ON) as [K|K]; [left; exact K| right; clear - K HSP; lia]. }
    split; [intros a Ha; destruct (CRE a Ha) as [S|[D|(b & Hb & Hr)]]; [left; exact S| right; left; exact D| right; right; exists b; split; [| exact Hr]];
            apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; exact (SUBk b Hb)| right; exact Hb]|].
    split.
    { intros EO. destruct (EIN EO) as [IN N1]. eapply client_range_block; [apply in_or_app; left; exact (SUBk _ IN)| clear; lia| clear; lia]. }
    split.
    - eapply aobj_cs_mono; [exact HCSk|].
      eapply (presA_aobj0 segs R); [exact (hcs_ok segs R HIA h)| exact PXk| exact OAs| intros x Hx; eapply hcs_below_top; exact Hx|].
      right. split; [exact CRS| clear - LOS SLO FR0; lia].
    - intros ES. eapply (AImgGlobals.aobj_img segs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow segs R HIA); exact HHk| exact (IME ES)].
    all: match goal with |- ?g => idtac "OPE-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  #[using="EC"] Lemma ej_sshad : ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey ()) "Pv,$4.Pf,$4.Phk,(2;.$2.VR,VHIA,)PLBk,(2:.$:.)Pmk,P,(1:.&40.)(1;.(1:.&8.))Pslo,$4.P,(29.R6.R5.R4.R3.R2.)P,(4;.$2.(11.VR,)Vm,R2.VSP,)P,(13.(16.VR,)R3.)(4;.$2.(11.VR,)R5.R4.VSP,)")
(* [comment removed for export] *).
  Proof.
    intros v f hk LBk mk slo J SS HS. dpose ej_facts as (_ & _ & _ & _ & SPHI).
    eapply (presA_sshad segs R); [exact (ej_pres _ _ _ _ _ J)| exact SS| exact HS| exact SPHI].
  Qed.

  (* [comment removed for export] *)
  #[using="EC"] Lemma ej_grp_pre : ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey ()) "PMT,(2:.$4<.)Pv,$4.Pf,$4.Phk,(2;.$2.VR,VHIA,)PLBk,(2:.$:.)Pmk,P,(1:.&40.)(1;.(1:.&8.))PG,$4.Pg,$4=.PSPc,$4.Pd,$4.P,(29.R9.R8.R7.R6.R5.)P,(4>.$2.VR,VHIA,R;.Vh,VLB,VLF,Vm,R5.R4.VMC,Vlo,VSP,R2.)P,(32.VXO,R6.+<0.)P,(13.R5.VSP,)(4>.$2.VR,VHIA,R>.R;.R:.VLF,R9.R8.R7.VMC,Vlo,R6.R5.)")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose ej_facts as (LO0 & ALO & ACP & MCLO & SPHI).
    (intros MT v f hk LBk mk G g SPc d J dd_H; ddestruct dd_H as (GAT & GH1 & GPS & GIMG & GCR & GSP & GMC & GOB & GUW); intros DXO HSP).
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    assert (CRS : client_range L (LB ++ fdata LF) SP G 192).
    { intros a Ha. destruct (GCR a Ha) as [S|[D|B]]; [| right; left; exact D| right; right; exact B].
      destruct GSP as [K|K]; [exfalso; clear - S Ha K; lia| left; clear - Ha K; lia]. }
    unfold ecp_grp_preA.
    split.
    { pose proof (ecp_group_at_LB_any segs MT m LB (LB ++ fdata LF) G g GAT GH1) as GAT0.
      eapply (ecp_group_at_presx segs L MT m mk _ LBk SP XO G g GAT0); [exact (presA_presx segs R _ _ _ _ _ _ _ _ PXk)| exact MIm| exact MIk| exact CRS| exact DXO|].
      intros e He EO. exfalso. exact (grp_static_own segs MT m LB G g e GAT GH1 He EO). }
    split; [exact GH1|]. split; [exact GPS|]. split; [exact GIMG|].
    split; [intros a Ha; destruct (GCR a Ha) as [S|[D|(b & Hb & Hr)]]; [left; exact S| right; left; exact D| right; right; exists b; split; [| exact Hr]];
            apply in_app_iff in Hb; apply in_app_iff; destruct Hb as [Hb|Hb]; [left; exact (SUBk b Hb)| right; exact Hb]|].
    split; [clear - GSP HSP; lia|]. split; [exact GMC|].
    split; [| exact GUW].
    eapply aobj_cs_mono; [exact HCSk|].
    eapply (presA_aobj0 segs R); [exact (hcs_ok segs R HIA h)| exact PXk| exact GOB| intros x Hx; eapply hcs_below_top; exact Hx|].
    right. split; [exact CRS| clear - LOS SLO FR0; lia].
    all: match goal with |- ?g => idtac "GRP-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG FR FRAME EC"] Lemma ej_grp_ext : ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey ()) "PMT,(2:.$4<.)PG,$4.Pg,$4=.Pd,$4.PA,$4.Pe,$2<.Poff,$4.Pcs,(2:.$27.)P,(4>.$2.VR,VHIA,R8.Vh,VLB,VLF,Vm,R7.R6.VMC,Vlo,VSP,R5.)P,(32.VXO,R8.+<0.)P,(;.$2<.R5.(4?.R8.))P,(3.$4.(5.R6.)(18.R:.R5.))P,(13.=R6.)P,(13.(18.R7.+10.)+<0.)P,(38.(3.$4.(50.R9.)+1.)(3.$4.(50.R9.)-1.))P,(38.(13.(18.R;.+10.)R>.)(13.(18.R>.+<0.)R;.))P,(26.$2.Vm,R<.R9.)P,(3.$4.(51.(52.R:.))+10.)(49.R>.R=.)")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose ej_facts as (LO0 & ALO & ACP & MCLO & SPHI). pose proof (alloc_ceiling_lo (L := arl_L R)) as ACL.
    (intros MT G g d A e off cs dd_H; ddestruct dd_H as (GAT & GH1 & GPS & GIMG & GCR & GSP & GMC & GOB & GUW); intros DXO He EAD O0 O1 ESG AG CA CSZ).
    assert (MR : mpdr_at segs m LB e).
    { dpose GAT as (HD & GAL & POS & EP & EA & EB & EN & MP & MA & MB & (EX & EY & EZ & MX & MY & MZ) & MN & HT & REST).
      unfold grp_mpds in He. cbn in He. destruct He as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; assumption. }
    assert (NH : md_own e <> LHeap) by (eapply (grp_static_own segs); [exact GAT| exact GH1| exact He]).
    assert (EIM : mpd_imgA e) by (unfold grp_imgA in GIMG; rewrite Forall_forall in GIMG; exact (GIMG e He)).
    assert (DST : md_own e <> LNull -> 1 <= md_n e /\ 0 < md_p e /\ (forall i, 0 <= i < 4 * md_n e -> ro_addr segs (wa (md_p e + i)) = true)
                                      /\ md_p e + 4 * md_n e <= 0x65f000).
    { intros NN. dpose MR as (_ & _ & _ & DHL & DHN & DHO). unfold mpd_imgA in EIM.
      destruct (md_own e) eqn:OD; [exfalso; apply NN; reflexivity| exfalso; apply NH; reflexivity|].
      ddestruct DHO as (N1 & _ & P0 & PB & PRO).
      destruct (AImgGlobals.img_norz_sound _ _ (EIM eq_refl)) as (_ & _ & IHI & _). unfold AImgGlobals.IMG_HI in IHI.
      split; [exact N1|]. split; [exact P0|]. split; [exact PRO| exact IHI]. }
    unfold ej_ext.
    split; [split; [exact MR| exact ESG]|].
    split; [rewrite EAD; intros x Hx; apply GCR; clear - Hx O0 O1; lia|].
    split; [rewrite EAD; clear - GSP O0 O1; lia|].
    split; [intros NN; ddestruct (DST NN) as (_ & _ & _ & IHI); left; clear - IHI ACL ALO LOS; lia|].
    split; [rewrite EAD; eapply disjoint_from_sub; [exact DXO| clear - O0; lia| clear - O1; lia]|].
    split; [intros EO; exfalso; exact (NH EO)|].
    split; [rewrite EAD; clear - AG O0 O1; lia|].
    split.
    { intros NN. ddestruct (DST NN) as (N1 & P0 & PRO & _).
      pose proof (P_ecp_mul_mod.rw_ro_apart segs m _ _ (md_p e) (4 * md_n e) MIm CA ltac:(rewrite CSZ; clear; lia) ltac:(clear - N1; lia) PRO) as AP.
      rewrite CSZ in AP. clear - AP. lia. }
    split; [| exact EIM].
    split.
    - rewrite EAD. eapply aobj_sub; [exact GOB| clear - O0; lia| clear - O1; lia].
    - intros ES. eapply (AImgGlobals.aobj_img segs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow segs R HIA); exact HH| exact (EIM ES)].
    all: match goal with |- ?g => idtac "GEXT-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  #[using="EC"] Lemma ej_scratch : ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey ()) "Pv,$4.Pf,$4.Phk,(2;.$2.VR,VHIA,)PLBk,(2:.$:.)Pmk,P,(1:.&40.)(1;.(1:.&8.))PA,$4.PdYk,$2<.Pwlo,$4.Pwhi,$4.Pm',P,(1:.&40.)(1;.(1:.&8.))P,(29.R:.R9.R8.R7.R6.)P,(2=.R9.R8.R7.R6.R5.)P,(38.(13.(18.R7.+10.)Vlo,)(13.VSP,R7.))P,(1<.(1=.(1>.$4.$4.)(1?.$4.$4.R6.R5.)(20.(1>.$4.$4.)))R9.R4.)P,(21.$2.R:.R5.)P,(23.$2.R6.)P,(24.$2.R7.Vlo,(25.VSP,VFR,))P,(22.$2.VR,VHIA,R?.R>.VLF,R8.)P,(13.Vlo,R;.)P,(13.R;.(25.VSP,VFR,))(0.(29.R14.R13.R12.R11.R;.)(2=.R12.R11.R;.R?.R>.))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose ej_facts as (LO0 & ALO & ACP & MCLO & SPHI).
    intros v f hk LBk mk A dYk wlo whi m' J T ASL MU WM MI' ST' HH' W1 W2.
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk [ck MCk] STk FRk]. dpose T as (MY & EA & NS & FRS & OA).
    pose proof (ejtmp_blk v f hk LBk mk A dYk J T) as BLK.
    pose proof (hcs_ok segs R HIA hk) as CSOK.
    assert (SCS : crange (hcs segs R HIA hk) lo (SP - lo)).
    { eapply crange_sub; [exact (hcs_stack segs R HIA hk)| clear - LOS; lia| rewrite HSk; clear - SPHI; lia]. }
    assert (WC : w_client (hcs segs R HIA hk) [(wlo, whi)]).
    { unfold w_client. apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros x Hx. apply SCS. clear - Hx W1 W2 FR0. lia. }
    split.
    - constructor; try assumption.
      + eapply presA_trans; [exact PXk|]. apply presA_nil_any.
        eapply (presA_drop_below segs R HIA h LB LF [] wlo whi m mk m' SP HH); [| clear - W2 FR0; lia| clear - W1 LOS; lia].
        rewrite <- HSk.
        eapply presA_weaken; [| exact SUBk| intros b Hb; exact Hb| apply Z.le_refl| apply Z.le_refl| apply Z.le_refl| intros x Hx; exact Hx].
        eapply (presA_of_munch segs R LBk LF SP (arl_stklo R) (hstkhi segs R HIA hk) [(wlo, whi)] mk m' (hcs segs R HIA hk) CSOK); [exact WC| | exact MU| exact WM].
        intros c0 Hc. eapply cshd_hcs; [exact HHk| apply Z.le_refl| exact Hc].
      + exists ck. eapply rw_cells_transport; [exact MCk| exact MU| exact WM|]. cbn [cells_size csize Nat.add disjoint_from fst snd]. split; [clear - MCLO W1; lia| exact I].
      + eapply rw_cells_transport; [exact FRk| exact MU| exact WM|]. rewrite FSZ. cbn [disjoint_from fst snd]. split; [clear - W2; lia| exact I].
    - split; [| split; [exact EA| split; [exact NS| split; [exact FRS|]]]].
      + eapply mpd_at_munch_any; [exact MY| exact MU| exact WM| |].
        * rewrite EA. cbn [disjoint_from fst snd]. split; [clear - ASL W1 W2 FR0; lia| exact I].
        * intros ON. assert (EO : md_own dYk = LHeap) by (destruct (md_own dYk); [exfalso; exact (ON eq_refl)| reflexivity| exfalso; exact (NS eq_refl)]).
          ddestruct (BLK EO) as (_ & _ & _ & B2 & _). cbn [disjoint_from fst snd]. split; [clear - B2 ALO LOS W1; lia| exact I].
      + eapply (aobj_munch segs AL _ CSOK [(wlo, whi)] mk m'); [exact WC| exact MU| exact OA].
    all: match goal with |- ?g => idtac "SCR-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  #[using="EC"] Lemma ej_cnt24 : ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey ()) "Pv,$4.Pf,$4.Phk,(2;.$2.VR,VHIA,)PLBk,(2:.$:.)Pmk,P,(1:.&40.)(1;.(1:.&8.))Pds,(2:.$2<.)P,(29.R6.R5.R4.R3.R2.)P,Pb,$:.P,(;.$:.R1.R5.)(38.(;.$:.R2.VLB,)(;.$:.R2.(53.$2<.$:.$<.R4.)))(13.(54.R5.)(18.(54.VLB,)(51.(55.$2<.R3.))))")
(* [comment removed for export] *).
  Proof.
    ec_open. intros v f hk LBk mk ds J COV.
    pose proof (HND _ _ _ _ (ej_hm _ _ _ _ _ J)) as ND.
    assert (INC : incl LBk (flat_map mpd_blk ds ++ LB)) by (intros b Hb; apply in_or_app; destruct (COV b Hb); [right| left]; assumption).
    pose proof (cnt24_incl LBk (flat_map mpd_blk ds ++ LB) (NoDup_map_inv fst LBk ND) INC) as C1.
    rewrite cnt24_app in C1.
    assert (C2 : cnt24 (flat_map mpd_blk ds) <= Z.of_nat (length ds)).
    { clear. induction ds as [|d r IH]; [cbn [flat_map length]; rewrite cnt24_nil; clear; lia|]. cbn [flat_map length]. rewrite cnt24_app.
      pose proof (cnt24_le_length (mpd_blk d)) as C. assert (Z.of_nat (length (mpd_blk d)) <= 1) by (unfold mpd_blk; destruct (md_own d); cbn; lia). lia. }
    lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma ej_aobj_call : ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey ()) "Pv,$4.Pf,$4.Phk,(2;.$2.VR,VHIA,)PLBk,(2:.$:.)Pmk,P,(1:.&40.)(1;.(1:.&8.))PA,$4.PdYk,$2<.Pm',P,(1:.&40.)(1;.(1:.&8.))Ph',(2;.$2.VR,VHIA,)PSPc,$4.PXs,(2:.$2?.)P,(29.R;.R:.R9.R8.R7.)P,(2=.R:.R9.R8.R7.R6.)P,(40.(15.VR,)(41.$:.VLB,(42.VLF,))VSP,(33.$2.VR,VHIA,Vh,)R8.+10.)P,(0.(13.(16.VR,)R5.)(13.R5.VSP,))P,(30.$2.VR,(2>.R<.R9.)VLF,R6.(16.VR,)(19.$2.VR,VHIA,R=.)R5.R;.R8.)P,Px,$4.P,(12.$2.VR,VHIA,R?.R1.)(12.$2.VR,VHIA,R:.R2.)(10.$2.(11.VR,)(12.$2.VR,VHIA,R9.)R:.R<.+10.)")
(* [comment removed for export] *).
  Proof.
    intros v f hk LBk mk A dYk m' h' SPc Xs J T CWA HSP HP HCS'. dpose T as (_ & _ & _ & _ & OA).
    eapply aobj_cs_mono; [exact HCS'|].
    eapply (presA_aobj0 segs R); [exact (hcs_ok segs R HIA hk)| exact HP| exact OA| intros x Hx; eapply hcs_below_top; exact Hx|].
    right. split; [| exact (proj1 HSP)].
    intros a Ha. destruct (CWA a Ha) as [S|[D|(b & Hb & Hr)]]; [left; clear - S HSP; lia| right; left; exact D| right; right; exists b; split; [| exact Hr]].
    apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; eapply ej_keep_sub; eassumption| right; exact Hb].
  Qed.

  #[using="EC"] Lemma ej_mc_call : ltac2:(CDefT.buildp (gd_tbl_A_ecp_journey ()) "Pv,$4.Pf,$4.Phk,(2;.$2.VR,VHIA,)PLBk,(2:.$:.)Pmk,P,(1:.&40.)(1;.(1:.&8.))PA,$4.PdYk,$2<.Pm',P,(1:.&40.)(1;.(1:.&8.))PSPc,$4.PXs,(2:.$2?.)P,(29.R:.R9.R8.R7.R6.)P,(2=.R9.R8.R7.R6.R5.)P,(30.$2.VR,(2>.R9.R6.)VLF,R4.(16.VR,)(19.$2.VR,VHIA,R:.)R3.R8.R5.)P,(32.R4.VMC,+8.)(39.(1:.&40.)Lc,(1:.&40.)(26.$2.R8.VMC,(1=.$27.(28.R1.)(20.$27.))))")
(* [comment removed for export] *).
  Proof.
    ec_open. intros v f hk LBk mk A dYk m' SPc Xs J T HP DMC. destruct (ej_mc _ _ _ _ _ J) as [c MCk]. ddestruct MCOK as (MC1 & MC2 & MC3 & _).
    exists c. eapply (presA_rw_cells segs R); [exact HP| exact MCk| | exact DMC].
    cbn [cells_size csize Nat.add]. intros x Hx. right. left. split; [clear - Hx MC1 MC2; lia| apply MC3; exact Hx].
  Qed.
End EJ.

