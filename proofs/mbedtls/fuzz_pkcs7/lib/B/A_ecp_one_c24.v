(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts RepEcp EcpFacts EcpCurves EcpLoad.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_grow P_mpi_free P_mpi_copy P_ecp_group_free P_ecp_red P_ecp_mul_mod.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_mpi_stmtA A_mpi_stmtA_sz A_mpi_stmtA_ng_sz A_ecp_stmtA
  A_mpi_opnd A_mpi_journey A_mpi_journey2 A_mpi_copy A_mpi_bitlen A_mpi_cmp_mpi A_mpi_cmp_int A_mpi_free A_ecp_mul_mod A_ecp_journey A_ecp_journey2 A_ecp_pair.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_mpi_stmtA_c24 A_mpi_copy_c24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_A_ecp_one_c24 () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_journey.EJ"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_journey.ejtmp"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_journey2.eslot"; "RocqVerifyHarness.AgentSubmission.B.A_alloc_lib.uw_obj"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.arl_need_ecp"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "E1.E1I"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_addsub.opnd_sep"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_writableA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpd_aobjA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpd_imgA"; "E1.e1_src"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_sep"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.mpd_keep"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_out"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "LinuxProcessSemantics.LinuxProcessSem.Run.config"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.mpi_binop_postA"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_copy_c24.mpi_copy_stmtA_c"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_copy.copy_PHI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_MAX"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_copy.copy_FR"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.FR_MAX"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.cnt24"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_copy_c24.C24_COPY_c"; "RocqVerifyHarness.AgentSubmission.LibA.ACnt24.C24MAX"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_copy.copy_R"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_ng_sz.mpi_binop_ng_stmtA_sz"; "Corelib.Init.Datatypes.nat"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_intop_stmtA_sz"; "Stdlib.ZArith.BinInt.Z.opp"; "Corelib.Init.Peano.le"; "Corelib.Init.Nat.add"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_cmp_mpi.mpi_cmp_mpi_stmtA"; "E1.e1_rdable"; "Stdlib.ZArith.BinInt.Z.sgn"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_cmp_int.mpi_cmp_int_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_free.mpi_free_stmtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_CALL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mkMPD"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"].


Section E1.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Variables (h : HST asegs R HIA) (LB LF : list blk) (m : mem) (mo : Model).
  Variables (SP lo FR : Z) (FRAME : list cell) (XO : list ivl) (MC : Z).
  Hypothesis EC : ECA R HIA h LB LF m SP lo FR FRAME XO MC.
  Variables (gp tp fpw : word) (F : bvmap 5 word) (fc : bv 32) (dd STKMAX : Z).
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis D0 : 0 <= dd.
  Hypothesis SP64 : SP < 2^64.
  Hypothesis SPA : (SP - FR) mod 16 = 0.
  Hypothesis SLOK : lo <= SP - FR - STKMAX - arl_need_ecp R.
  Hypothesis STK0 : 0 <= STKMAX.
  Hypothesis UW0 : uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned fpw) SP dd.
  Hypothesis XOUW : 28 <= dd \/ forall a, SP <= a < hstkhi asegs R HIA h -> outside XO a.

  Local Ltac ec_open := pose proof EC as [NEEDR HND DIMG ROIMG HH MIm LOS FR0 FSZ SLO TOP MCOK XOMC].
  Local Notation EJ0 := (EJ R HIA h LB LF m SP lo FR FRAME XO MC).
  Local Notation TMP := (ejtmp R HIA LB LF).
  Local Notation SLOT := (eslot R HIA h LB LF SP lo XO MC).
  Local Notation SP' := (Z_to_bv 64 (SP - FR)).

  (* [comment removed for export] *)
  Definition E1I (v f : Z) (hk : HST asegs R HIA) (LBk : list blk) (mk : mem) (A1 : Z) (d1 : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_one_c24 ()) "(0.(1.VR,VHIA,Vh,VLB,VLF,Vm,VSP,Vlo,VFR,VFRAME,VXO,VMC,O7.O6.O5.O4.O3.)(0.(2.VR,VHIA,VLB,VLF,O5.O4.O3.O2.O1.)(0.(3.VR,VHIA,Vh,VLB,VLF,VSP,Vlo,VXO,VMC,O2.)(0.(4.VR,O2.+10.Vdd,)Pb,$5.P,(6.$5.R1.O4.)(7.(6.$5.R2.VLB,)(6.$5.R2.(8.O1.)))))))")
(* [comment removed for export] *).

  #[using="HIA h LB LF m FRAME XO MC EC SP64 SPA SLOK STK0"] Lemma e1_base : ltac2:(CDefT.buildp (gd_tbl_A_ecp_one_c24 ()) "(0.(9.=Vlo,)(0.(9.Vlo,(:.(:.VSP,VFR,)VSTKMAX,))(0.(0.(9.=(:.VSP,VFR,))(;.(:.VSP,VFR,)(<.+2.+40.)))(0.(9.=(=.VR,))(0.(9.(>.VR,)Vlo,)(?.$10.(11.(:.VSP,VFR,)+8.)=))))))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose (ej_facts R HIA h LB LF m SP lo FR FRAME XO MC EC) as (LO0 & ALO & ACP & MCLO & SPHI).
    pose proof (arl_need_ecp_rt R) as NER.
    repeat split; try assumption; first [clear - SLOK NER NEEDR; lia | clear - SLOK NER NEEDR LO0 STK0; lia | clear - SP64 FR0; lia | clear - NER NEEDR; lia | clear - SPA; Z.div_mod_to_equations; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="EC STKMAX SP64 SPA SLOK STK0 UW0 XOUW"] Lemma e1_uwc : ltac2:(CDefT.buildp (gd_tbl_A_ecp_one_c24 ()) "Pv,$10.Pf,$10.Phk,(12.$13.VR,VHIA,)PLBk,(14.$5.)Pmk,P,(15.&40.)(16.(15.&8.))P,(1.VR,VHIA,Vh,VLB,VLF,Vm,VSP,Vlo,VFR,VFRAME,VXO,VMC,R5.R4.R3.R2.R1.)(17.$13.R2.(>.VR,)(18.$13.VR,VHIA,R4.)(19.&40.Vfpw,)(:.VSP,VFR,)Vdd,)")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose (ej_facts R HIA h LB LF m SP lo FR FRAME XO MC EC) as (LO0 & ALO & ACP & MCLO & SPHI).
    dpose e1_base as (_ & LOSP & SPR & NE0 & _ & _).
    intros v f hk LBk mk J. rewrite (ej_stkhi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J).
    destruct XOUW as [D28|XOUT]; [apply uwc_cap; exact D28|].
    eapply uwc_floor; [| instantiate (1 := SP); clear - FR0; lia].
    eapply uwc_transport; [exact UW0|]. intros a Ha.
    pose proof (hcs_stack asegs R HIA h) as SCS. pose proof (hm_top asegs R HIA h LB LF m HH) as HT.
    destruct (hcs_app asegs R HIA h _ _ SCS ltac:(clear - HT LOS LOSP TOP STK0 FR0 Ha; lia)) as [[_ K]|[_ K]]; [pose proof (art_stk_high asegs R HIA) as SH; exfalso; clear - K SH HT; lia|].
    destruct (ej_pres _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as [PX _].
    refine (proj1 (PX a ltac:(clear - Ha LO0 LOSP K STK0 FR0; lia) ltac:(left; clear - Ha; lia) _)).
    apply XOUT. exact Ha.
  Qed.

  (* [comment removed for export] *)
  #[using="EC STKMAX SP64 SPA SLOK STK0"] Lemma e1_out : ltac2:(CDefT.buildp (gd_tbl_A_ecp_one_c24 ()) "Pv,$10.Pf,$10.Phk,(12.$13.VR,VHIA,)PLBk,(14.$5.)Pmk,P,(15.&40.)(16.(15.&8.))PA1,$10.Pd1,$1:.P,(1;.R7.R6.R5.R4.R3.R2.R1.)(0.(1<.$13.R4.R5.R2.)(0.(1=.(?.$1>.(1?.R2.)$20.))(0.(?.$10.(21.R2.)R3.)(0.(22.R2.R2.Vlo,(:.VSP,VFR,))(0.(23.(24.VR,)(25.$5.R5.(26.VLF,))Vlo,R3.+10.)(0.P,(?.$1>.(1?.R2.)$27.)(23.(24.VR,)(25.$5.R6.(26.VLF,))Vlo,(28.R3.)(29.+4.(2:.R3.)))(0.(2;.VR,R5.VLF,(:.VSP,VFR,)(2<.$13.VR,VHIA,R6.)R2.)(0.P,(1=.(?.$1>.(1?.R2.)$2=.))(7.(9.(2>.(28.R3.)(29.+4.(2:.R3.)))Vlo,)(9.(:.VSP,VFR,)(28.R3.)))(0.(2?.$13.(30.VR,)(31.$13.VR,VHIA,R6.)R4.R2.)(32.R2.))))))))))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose e1_base as (_ & LOSP & _).
    (intros v f hk LBk mk A1 d1 dd_H; ddestruct dd_H as (J & T1 & (CW1 & SL1 & _) & _)).
    exact (ej_opY R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk A1 d1 (SP - FR) J T1 CW1 SL1 ltac:(clear - LOSP STK0 FR0; lia)).
  Qed.

  (* [comment removed for export] *)
  Definition e1_src (A1 : Z) (d1 e : mpd) : Prop := e = d1 \/ ej_ext R HIA h LB LF m SP lo XO A1 e.

  #[using="IMG EC STKMAX SP64 SPA SLOK STK0"] Lemma e1_opnd : ltac2:(CDefT.buildp (gd_tbl_A_ecp_one_c24 ()) "Pv,$10.Pf,$10.Phk,(12.$13.VR,VHIA,)PLBk,(14.$5.)Pmk,P,(15.&40.)(16.(15.&8.))PA1,$10.Pd1,$1:.Pe,$1:.P,(1;.R8.R7.R6.R5.R4.R3.R2.)P,(33.R4.R3.R2.)(0.(1<.$13.R6.R7.R3.)(0.(34.R4.R3.)(0.(22.R4.R3.Vlo,(:.VSP,VFR,))(0.(23.(24.VR,)(25.$5.R7.(26.VLF,))Vlo,(21.R3.)+10.)(0.P,(?.$1>.(1?.R3.)$27.)(23.(24.VR,)(25.$5.R8.(26.VLF,))Vlo,(28.R4.)(29.+4.(2:.R4.)))(0.(2?.$13.(30.VR,)(31.$13.VR,VHIA,R8.)R6.R3.)(0.(32.R3.)(7.(?.$1:.R3.R4.)(1=.(?.$10.(21.R4.)(21.R3.)))))))))))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose e1_base as (_ & LOSP & _).
    intros v f hk LBk mk A1 d1 e S [E|EX].
    - subst e. ddestruct (e1_out v f hk LBk mk A1 d1 S) as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
      split; [exact XM|]. split; [left; reflexivity|]. split; [exact XOS|]. split; [rewrite XAD; exact XCR|]. split; [exact XCRL|]. split; [exact XAO|]. split; [exact XIM| left; reflexivity].
    - ddestruct S as (J & T1 & _).
      ddestruct (ej_opE R HIA IMG h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk A1 d1 e (SP - FR) J T1 EX ltac:(clear - LOSP STK0 FR0; lia)) as (EM & ESEP & ENE & EOS & ECR & ECRL & EAO).
      split; [exact EM|]. split; [exact ESEP|]. split; [exact EOS|]. split; [exact ECR|]. split; [exact ECRL|]. split; [exact EAO|].
      ddestruct EX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & IME). split; [exact IME| right; exact ENE].
  Qed.

  #[using="EC"] Lemma e1_cnt24 : forall v f hk LBk mk A1 d1, E1I v f hk LBk mk A1 d1 -> cnt24 LBk <= cnt24 LB + 2.
  Proof.
    (intros v f hk LBk mk A1 d1 dd_H; ddestruct dd_H as (J & _ & _ & _ & COV)).
    pose proof (ej_cnt24 R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk [d1] J) as C.
    cbn [flat_map length app] in C. rewrite app_nil_r in C. specialize (C COV). cbn in C. clear - C. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="EC"] Lemma e1_call : ltac2:(CDefT.buildp (gd_tbl_A_ecp_one_c24 ()) "Pv,$10.Pf,$10.Phk,(12.$13.VR,VHIA,)PLBk,(14.$5.)Pmk,P,(15.&40.)(16.(15.&8.))PA1,$10.Pd1,$1:.Pm',P,(15.&40.)(16.(15.&8.))Ph',(12.$13.VR,VHIA,)PLB',(14.$5.)Pd1',$1:.PSPc,$10.Pdv,$10.Pdf,$10.P,(1;.R>.R=.R<.R;.R:.R9.R8.)P,(0.(9.Vlo,R4.)(9.R4.(:.VSP,VFR,)))P,(9.=R4.)P,(9.=R4.)P,(35.$13.R;.)P,(36.$13.R<.Vlo,(:.VSP,VFR,))P,(37.$13.VR,(38.R11.R>.)VLF,R9.(>.VR,)(18.$13.VR,VHIA,R12.)(39.(3:.$10.$10.)(3;.$10.$10.R?.(2>.R?.+10.))(3<.(3:.$10.$10.)))R10.R=.)P,(?.$10.(2<.$13.VR,VHIA,R=.)(2<.$13.VR,VHIA,R13.))P,(?.$10.(18.$13.VR,VHIA,R>.)(18.$13.VR,VHIA,R14.))P,(?.$10.(3=.$13.VR,VHIA,R?.)(3=.$13.VR,VHIA,R15.))P,Px,$10.P,(31.$13.VR,VHIA,R17.R1.)(31.$13.VR,VHIA,R12.R2.)P,(9.(3>.$13.VR,VHIA,R11.)(2>.(3>.$13.VR,VHIA,R17.)R=.))P,(9.(3?.$13.VR,VHIA,R12.)(2>.(3?.$13.VR,VHIA,R18.)R=.))P,(40.$13.VR,VHIA,R13.R12.VLF,R14.)P,(1<.$13.R15.R13.R12.)P,(41.R1:.R17.R14.R13.)P,Pb,$5.P,(6.$5.R1.(8.R15.))(7.(6.$5.R2.(8.R1:.))(42.VR,(38.R1=.R1:.)VLF,(43.$10.$10.R2.)(44.$10.$10.R2.)))(1;.(2>.R1?.R13.)(2>.R1>.R12.)R17.R16.R18.R1:.R15.)")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose (ej_facts R HIA h LB LF m SP lo FR FRAME XO MC EC) as (LO0 & ALO & ACP & MCLO & SPHI).
    intros until df. (intros dd_H; ddestruct dd_H as (J & T1 & S1 & U1 & COV); intros HSP Hdv Hdf MI' ST' HP HT' HS' HF' HCS' HV' HFR' HH' M1' OUT' FRA').
    dpose S1 as (CW1 & SL1 & XI1 & MS1).
    assert (HSP2 : arl_stklo R <= SPc <= SP) by (clear - HSP LOS FR0; lia).
    pose proof (ej_aobj_call R HIA h LB LF m SP lo FR FRAME XO MC v f hk LBk mk A1 d1 m' h' SPc _ J T1 CW1 HSP2 HP HCS') as OA1'.
    pose proof (ej_mc_call R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk A1 d1 m' SPc _ J T1 HP ltac:(cbn [disjoint_from fst snd]; split; [clear - MS1; lia| exact I])) as MC'.
    destruct (ej_call R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk A1 d1 m' h' LB' d1' SPc dv df [(A1, A1 + 16)] J T1
                ltac:(clear - HSP; lia) Hdv Hdf MI' ST' HP XI1 ltac:(cbn [disjoint_from fst snd]; split; [clear - SL1 FR0 SLO; lia| exact I]) ltac:(clear - HSP; lia)
                HT' HS' HF' HCS' HV' HFR' HH' M1' OUT' FRA' OA1' MC') as [J' T1'].
    refine (conj J' (conj T1' (conj S1 (conj U1 _)))).
    dpose OUT' as (_ & _ & O3 & _ & O5).
    intros b Hb. destruct (O3 b Hb) as [K1|K1]; [| right; exact K1].
    destruct (COV b K1) as [K2|K2]; [left; exact K2| right]. rewrite (O5 b K2 Hb). exact K2.
    all: match goal with |- ?g => idtac "E1CALL-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  #[using="EC STKMAX SP64 SPA SLOK STK0"] Lemma e1_after : ltac2:(CDefT.buildp (gd_tbl_A_ecp_one_c24 ()) "Pv,$10.Pf,$10.Phk,(12.$13.VR,VHIA,)PLBk,(14.$5.)Pmk,P,(15.&40.)(16.(15.&8.))PA1,$10.Pd1,$1:.Pdv,$10.Pdf,$10.PRr,P,$10.P,$1:.SpPRET,$10.Pc1,(15.&40.)Pc2,(15.&40.)Pc3,(15.&40.)Pc4,(15.&40.)Pc5,(15.&40.)Pc6,(15.&40.)Pc7,(15.&40.)Pc8,(15.&40.)Pc9,(15.&40.)Pc10,(15.&40.)Pc11,(15.&40.)PQ,P,$45.SpP,(1;.R17.R16.R15.R14.R13.R12.R11.)P,(9.=R11.)P,(9.=R11.)P,(0.(9.=R10.)(;.R10.(<.+2.+40.)))P,(?.$10.(11.R11.+2.)=)P,Ph',(12.$13.VR,VHIA,)PLB',(14.$5.)Pm',P,(15.&40.)(16.(15.&8.))Pd1',$1:.Pr,$10.Pt0',(15.&40.)Pt1',(15.&40.)Pt2',(15.&40.)Pa1',(15.&40.)Pa2',(15.&40.)Pa3',(15.&40.)Pa4',(15.&40.)Pa5',(15.&40.)Pa6',(15.&40.)Pa7',(15.&40.)Pt3',(15.&40.)Pt4',(15.&40.)Pt5',(15.&40.)Pt6',(15.&40.)P,(1;.(2>.R2?.R28.)(2>.R2>.R27.)R13.R12.R11.R2:.R10.)P,A2.R27.R10.R11.(46.$13.(47.$13.VR,VHIA,R15.Vmo,)R1;.(48.(49.(4:.&40.R27.)(4:.&40.(:.VSP,VFR,))Vgp,Vtp,R10.R?.R>.Vfpw,R26.(4:.&40.R11.)R=.R<.R;.R:.R9.R8.R7.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R6.R5.R4.R3.)VF,(4:.&40.R27.)Vfc,(4;.(15.&40.))R13.(4<.$13.)))Pms',$4=.Pmo',$4>.P,(4?.$4>.Lmo1,$4>.(0.(47.$13.VR,VHIA,R1>.Vmo,R1.)(50.$13.VR,VHIA,(4:.&40.R16.)(4:.&40.(:.VSP,VFR,))Vgp,Vtp,Vfpw,R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.VF,Vfc,R1>.R1=.VLF,R1:.R17.R19.R18.Vlo,R1<.R1.(51.R3.R2.))))(52.$13.R:.(51.R3.R2.))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose e1_base as (LO0 & LOSP & SPR & NE0 & LOS' & M8).
    intros until Q. (intros S Hdv Hdf HRET HRE K ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_binop_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & LB2 & dX2 & r & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & MX2 & OUT2 & FRA2 & GR).
    injection E as E1 E2. subst ms' mo'.
    dpose S as (J & (_ & EA1 & _) & _).
    rewrite ?(unsigned_lit (SP - FR)) in ST2, HP2 by exact SPR. rewrite EA1 in HP2.
    rewrite (ret_pc_even RET HRET HRE).
    pose proof (e1_call v f hk LBk mk A1 d1 m2 h2 LB2 dX2 (SP - FR) dv df S ltac:(clear - LOSP STK0; lia) Hdv Hdf MI2 ST2 HP2 HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 FRA2) as S2.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply K; [exact S2| exact GR].
    all: match goal with |- ?g => idtac "AFTER-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG EC TPV D0 SP64 SPA SLOK STK0"] Lemma e1_copy : ltac2:(CDefT.buildp (gd_tbl_A_ecp_one_c24 ()) "PENTRY,$10.P,(53.$13.VR,VHIA,R1.)Pv,$10.Pf,$10.Phk,(12.$13.VR,VHIA,)PLBk,(14.$5.)Pmk,P,(15.&40.)(16.(15.&8.))PA1,$10.Pd1,$1:.PeY,$1:.PRET,$10.Pxt0,(15.&40.)Pxt1,(15.&40.)Pxt2,(15.&40.)Pc1,(15.&40.)Pxa0,(15.&40.)Pxa1,(15.&40.)Pxa2,(15.&40.)Pxa3,(15.&40.)Pxa4,(15.&40.)Pxa5,(15.&40.)Pxa6,(15.&40.)Pxa7,(15.&40.)Pc2,(15.&40.)Pc3,(15.&40.)Pc4,(15.&40.)Pc5,(15.&40.)Pc6,(15.&40.)Pc7,(15.&40.)Pc8,(15.&40.)Pc9,(15.&40.)Pc10,(15.&40.)Pc11,(15.&40.)Pxt3,(15.&40.)Pxt4,(15.&40.)Pxt5,(15.&40.)Pxt6,(15.&40.)PQ,P,$45.SpP,(1;.R24.R23.R22.R21.R20.R1?.R1>.)P,(33.R20.R1?.R1>.)P,(9.+70.VSTKMAX,)P,(9.=(54.R20.))P,(9.(2>.(3>.$13.VR,VHIA,Vh,)(2>.R28.(54.R21.)))$55.)P,(9.(2>.(3?.$13.VR,VHIA,Vh,)(2>.R28.(56.Vdd,)))$57.)P,(9.(2>.(2>.(58.VLB,)+2.)$59.)$5:.)P,(0.(9.=R23.)(;.R23.(<.+2.+40.)))P,(?.$10.(11.R24.+2.)=)P,Ph',(12.$13.VR,VHIA,)PLB',(14.$5.)Pm',P,(15.&40.)(16.(15.&8.))Pd1',$1:.Pr,$10.Pt0',(15.&40.)Pt1',(15.&40.)Pt2',(15.&40.)Pa1',(15.&40.)Pa2',(15.&40.)Pa3',(15.&40.)Pa4',(15.&40.)Pa5',(15.&40.)Pa6',(15.&40.)Pa7',(15.&40.)Pt3',(15.&40.)Pt4',(15.&40.)Pt5',(15.&40.)Pt6',(15.&40.)P,(1;.(2>.R40.(54.R39.))(2>.R3?.(56.Vdd,))R13.R12.R11.R3;.R10.)P,(5;.R3:.R3;.R3>.R10.R11.)(46.$13.(47.$13.VR,VHIA,R15.Vmo,)R1?.(48.(49.(4:.&40.R3:.)(4:.&40.(:.VSP,VFR,))Vgp,Vtp,R10.R?.R>.Vfpw,R36.(4:.&40.R11.)R=.R<.R;.R:.R9.R8.R7.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R6.R5.R4.R3.)VF,(4:.&40.R3:.)Vfc,(4;.(15.&40.))R13.(4<.$13.)))P,(?.(15.&40.)R21.(4:.&40.R29.))P,(?.(15.&40.)R21.(4:.&40.(21.R28.)))(46.$13.(47.$13.VR,VHIA,R2>.Vmo,)R=.(48.(49.(4:.&40.R28.)(4:.&40.(:.VSP,VFR,))Vgp,Vtp,R27.R26.R25.Vfpw,R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)VF,(4:.&40.R32.)Vfc,(4;.(15.&40.))R2<.(4<.$13.)))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose e1_base as (LO0 & LOSP & SPR & NE0 & LOS' & M8). pose proof (arl_need_ecp_rt R) as NER.
    intros ENTRY HC. intros until Q. intros S SY HSTK HPHI HV HF HC24 HRET HRE K E0 E1. subst xa0 xa1.
    ddestruct (e1_out v f hk LBk mk A1 d1 S) as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    ddestruct (e1_opnd v f hk LBk mk A1 d1 eY S SY) as (YM & YSEP & YOS & YCR & YCRL & YAO & YIM & YNE).
    dpose S as (J & T1 & S1 & U1 & COV).
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    assert (FRC0 : 0 <= copy_FR dd) by (rewrite copy_FR_val; clear - D0; lia).
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. unfold mpi_copy_stmtA_c, mpi_copy_stmtA_gen_c in HC.
      eapply HC with (h := hk) (LB := LBk) (LF := LF) (dX := d1) (dY := eY) (lo := lo) (d := dd);
        rewrite ?(unsigned_lit (SP - FR)) by exact SPR.
      - exact HHk.
      - exact HK1.
      - exact XM.
      - exact XNS.
      - exact YM.
      - exact YSEP.
      - ddestruct YOS as (O1 & O2 & O3 & O4 & O5). unfold copy_sep.
        split; [exact O1|]. split; [exact O2|]. split; [exact O3|]. split; [exact O4|]. split; [exact O5|].
        intros a Ha. pose proof YM as [(_ & _ & P0 & _) _]. clear - Ha P0. lia.
      - exact YCR.
      - exact YCRL.
      - exact XWR.
      - exact STk.
      - exact LOS.
      - clear - SLOK HSTK NER. lia.
      - rewrite HTk. clear - TOP FR0. lia.
      - exact SPA.
      - exact TPV.
      - exact MIk.
      - rewrite unsigned_lit by exact HRET. exact HRE.
      - exact (proj1 XAO).
      - exact (proj1 YAO).
      - exact YIM.
      - clear - HV HVk. lia.
      - rewrite XAD. exact U1.
      - clear - HF HFRk. lia.
      - pose proof (e1_cnt24 v f hk LBk mk A1 d1 S) as C24k. clear - HC24 C24k. lia.
      - rewrite XAD. reflexivity.
      - reflexivity. }
    eapply (e1_after v f hk LBk mk A1 d1 (copy_PHI eY) (copy_FR dd) (copy_R eY d1 LBk) RET); try eassumption.
    all: match goal with |- ?g => idtac "COPY-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG EC TPV SP64 SPA SLOK STK0 UW0 XOUW"] Lemma e1_binop_ng : ltac2:(CDefT.buildp (gd_tbl_A_ecp_one_c24 ()) "PENTRY,$10.PSTACK,$10.PPRE,P,$1:.P,$1:.P,$1:.SpPRr,P,(14.$5.)P,$1:.P,$1:.P,$1:.P,$10.P,$1:.SpP,(5<.$13.VR,VHIA,R4.R3.R2.R1.)Pv,$10.Pf,$10.Phk,(12.$13.VR,VHIA,)PLBk,(14.$5.)Pmk,P,(15.&40.)(16.(15.&8.))PA1,$10.Pd1,$1:.PeA,$1:.PeB,$1:.PRET,$10.Pxt0,(15.&40.)Pxt1,(15.&40.)Pxt2,(15.&40.)Pc1,(15.&40.)Pxa0,(15.&40.)Pxa1,(15.&40.)Pxa2,(15.&40.)Pxa3,(15.&40.)Pxa4,(15.&40.)Pxa5,(15.&40.)Pxa6,(15.&40.)Pxa7,(15.&40.)Pc2,(15.&40.)Pc3,(15.&40.)Pc4,(15.&40.)Pc5,(15.&40.)Pc6,(15.&40.)Pc7,(15.&40.)Pc8,(15.&40.)Pc9,(15.&40.)Pc10,(15.&40.)Pc11,(15.&40.)Pxt3,(15.&40.)Pxt4,(15.&40.)Pxt5,(15.&40.)Pxt6,(15.&40.)PQ,P,$45.SpP,(1;.R25.R24.R23.R22.R21.R20.R1?.)P,(33.R21.R20.R1?.)P,(33.R22.R21.R1?.)P,(34.R21.R20.)P,A3.R2<.R23.R22.R21.P,(4.VR,(21.R23.)+10.Vdd,)P,(4.VR,(21.R23.)+10.Vdd,)P,(9.R30.VSTKMAX,)P,(9.(2>.(3>.$13.VR,VHIA,Vh,)R2=.)$55.)P,(9.(2>.(3?.$13.VR,VHIA,Vh,)R2=.)$57.)P,(0.(9.=R26.)(;.R26.(<.+2.+40.)))P,(?.$10.(11.R27.+2.)=)P,Ph',(12.$13.VR,VHIA,)PLB',(14.$5.)Pm',P,(15.&40.)(16.(15.&8.))Pd1',$1:.Pr,$10.Pt0',(15.&40.)Pt1',(15.&40.)Pt2',(15.&40.)Pa1',(15.&40.)Pa2',(15.&40.)Pa3',(15.&40.)Pa4',(15.&40.)Pa5',(15.&40.)Pa6',(15.&40.)Pa7',(15.&40.)Pt3',(15.&40.)Pt4',(15.&40.)Pt5',(15.&40.)Pt6',(15.&40.)P,(1;.(2>.R44.=)(2>.R43.=)R13.R12.R11.R3?.R10.)P,A6.R47.R42.R3?.R3>.R3=.R10.R11.(46.$13.(47.$13.VR,VHIA,R15.Vmo,)R22.(48.(49.(4:.&40.R3=.)(4:.&40.(:.VSP,VFR,))Vgp,Vtp,R10.R?.R>.Vfpw,R39.(4:.&40.R11.)R=.R<.R;.R:.R9.R8.R7.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R6.R5.R4.R3.)VF,(4:.&40.R3=.)Vfc,(4;.(15.&40.))R13.(4<.$13.)))P,(?.(15.&40.)R24.(4:.&40.R2=.))P,(?.(15.&40.)R24.(4:.&40.(21.R2<.)))P,(?.(15.&40.)R24.(4:.&40.(21.R2<.)))(46.$13.(47.$13.VR,VHIA,R33.Vmo,)R11.(48.(49.(4:.&40.R2<.)(4:.&40.(:.VSP,VFR,))Vgp,Vtp,R2;.R2:.R29.Vfpw,R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)VF,(4:.&40.R3:.)Vfc,(4;.(15.&40.))R31.(4<.$13.)))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose e1_base as (LO0 & LOSP & SPR & NE0 & LOS' & M8).
    intros ENTRY STACK PRE Rr HC. intros until Q. intros S SA SB SAB HPRE UWA UWB HSTK HV HF HRET HRE K E0 E1 E2. subst xa0 xa1 xa2.
    ddestruct (e1_out v f hk LBk mk A1 d1 S) as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    ddestruct (e1_opnd v f hk LBk mk A1 d1 eA S SA) as (AM & ASEP & AOS & ACR & ACRL & AAO & AIM & ANE).
    ddestruct (e1_opnd v f hk LBk mk A1 d1 eB S SB) as (BM & BSEP & BOS & BCR & BCRL & BAO & BIM & BNE).
    dpose S as (J & T1 & S1 & U1 & COV).
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. unfold mpi_binop_ng_stmtA_sz in HC.
      eapply HC with (h := hk) (LB := LBk) (LF := LF) (dX := d1) (dA := eA) (dB := eB) (lo := lo) (d := dd);
        rewrite ?(unsigned_lit (SP - FR)) by exact SPR.
      - exact HHk.
      - exact HK1.
      - exact XM.
      - exact AM.
      - exact BM.
      - exact ASEP.
      - exact BSEP.
      - exact SAB.
      - exact XNS.
      - exact HPRE.
      - exact AOS.
      - exact BOS.
      - exact ACR.
      - exact ACRL.
      - exact BCR.
      - exact BCRL.
      - exact XWR.
      - exact XLSq.
      - exact STk.
      - exact LOS.
      - clear - SLOK HSTK. lia.
      - rewrite HTk. clear - TOP FR0. lia.
      - exact SPA.
      - exact TPV.
      - exact MIk.
      - rewrite unsigned_lit by exact HRET. exact HRE.
      - exact XAO.
      - exact AAO.
      - exact BAO.
      - exact AIM.
      - exact BIM.
      - clear - HV HVk. lia.
      - exact (e1_uwc v f hk LBk mk J).
      - rewrite XAD. exact U1.
      - exact UWA.
      - exact UWB.
      - clear - HF HFRk. lia.
      - rewrite XAD. reflexivity.
      - reflexivity.
      - reflexivity. }
    eapply (e1_after v f hk LBk mk A1 d1 0 0 (Rr LBk d1 eA eB) RET); first [ eassumption | (clear; lia) | idtac ].
    all: match goal with |- ?g => idtac "BINOPNG-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG EC TPV SP64 SPA SLOK STK0 UW0 XOUW"] Lemma e1_intop : ltac2:(CDefT.buildp (gd_tbl_A_ecp_one_c24 ()) "PENTRY,$10.PSTACK,$10.PNF,$5=.PC24,$10.PPHI,P,$1:.P,$1:.$10.PFRC,P,$10.$10.PRr,P,(14.$5.)P,$1:.P,$1:.P,$10.P,$10.P,$1:.SpP,(5>.$13.VR,VHIA,R7.R6.R5.R4.R3.R2.R1.)Pv,$10.Pf,$10.Phk,(12.$13.VR,VHIA,)PLBk,(14.$5.)Pmk,P,(15.&40.)(16.(15.&8.))PA1,$10.Pd1,$1:.PeA,$1:.Pb,$10.PRET,$10.Pxt0,(15.&40.)Pxt1,(15.&40.)Pxt2,(15.&40.)Pc1,(15.&40.)Pxa0,(15.&40.)Pxa1,(15.&40.)Pxa2,(15.&40.)Pxa3,(15.&40.)Pxa4,(15.&40.)Pxa5,(15.&40.)Pxa6,(15.&40.)Pxa7,(15.&40.)Pc2,(15.&40.)Pc3,(15.&40.)Pc4,(15.&40.)Pc5,(15.&40.)Pc6,(15.&40.)Pc7,(15.&40.)Pc8,(15.&40.)Pc9,(15.&40.)Pc10,(15.&40.)Pc11,(15.&40.)Pxt3,(15.&40.)Pxt4,(15.&40.)Pxt5,(15.&40.)Pxt6,(15.&40.)PQ,P,$45.SpP,(1;.R25.R24.R23.R22.R21.R20.R1?.)P,(33.R21.R20.R1?.)P,(4.VR,(21.R20.)+10.Vdd,)P,(0.(9.(5?.(<.+2.+1?.))R20.)(;.R20.(<.+2.+1?.)))P,(9.R30.VSTKMAX,)P,(60.(61.(62.$5.VLF,)R30.)#200.)P,(9.=A2.R2?.R25.R24.)P,(9.=A1.R2?.Vdd,)P,(9.(2>.(3>.$13.VR,VHIA,Vh,)(2>.R2=.A2.R31.R27.R26.))$55.)P,(9.(2>.(3?.$13.VR,VHIA,Vh,)(2>.R2=.A1.R31.Vdd,))$57.)P,(9.(2>.(2>.(58.VLB,)+2.)R34.)$5:.)P,(0.(9.=R27.)(;.R27.(<.+2.+40.)))P,(?.$10.(11.R28.+2.)=)P,Ph',(12.$13.VR,VHIA,)PLB',(14.$5.)Pm',P,(15.&40.)(16.(15.&8.))Pd1',$1:.Pr,$10.Pt0',(15.&40.)Pt1',(15.&40.)Pt2',(15.&40.)Pa1',(15.&40.)Pa2',(15.&40.)Pa3',(15.&40.)Pa4',(15.&40.)Pa5',(15.&40.)Pa6',(15.&40.)Pa7',(15.&40.)Pt3',(15.&40.)Pt4',(15.&40.)Pt5',(15.&40.)Pt6',(15.&40.)P,(1;.(2>.R45.A2.R49.R3?.R3>.)(2>.R44.A1.R48.Vdd,)R13.R12.R11.R40.R10.)P,A6.R48.R43.R40.R3?.R3>.R10.R11.(46.$13.(47.$13.VR,VHIA,R15.Vmo,)R23.(48.(49.(4:.&40.R3>.)(4:.&40.(:.VSP,VFR,))Vgp,Vtp,R10.R?.R>.Vfpw,R3:.(4:.&40.R11.)R=.R<.R;.R:.R9.R8.R7.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R6.R5.R4.R3.)VF,(4:.&40.R3>.)Vfc,(4;.(15.&40.))R13.(4<.$13.)))P,(?.(15.&40.)R25.(4:.&40.R2>.))P,(?.(15.&40.)R25.(4:.&40.(21.R2=.)))P,(?.(15.&40.)R25.(4:.&40.R2=.))(46.$13.(47.$13.VR,VHIA,R34.Vmo,)R12.(48.(49.(4:.&40.R2=.)(4:.&40.(:.VSP,VFR,))Vgp,Vtp,R2<.R2;.R2:.Vfpw,R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)VF,(4:.&40.R3>.)Vfc,(4;.(15.&40.))R32.(4<.$13.)))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose e1_base as (LO0 & LOSP & SPR & NE0 & LOS' & M8).
    intros ENTRY STACK NF C24 PHI FRC Rr HC. intros until Q. intros S SA UWA HB HSTK HNF HPHI HFRC HV HF HC24 HRET HRE K E0 E1 E2. subst xa0 xa1 xa2.
    ddestruct (e1_out v f hk LBk mk A1 d1 S) as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    ddestruct (e1_opnd v f hk LBk mk A1 d1 eA S SA) as (AM & ASEP & AOS & ACR & ACRL & AAO & AIM & ANE).
    pose proof (e1_cnt24 v f hk LBk mk A1 d1 S) as C24k. dpose S as (J & T1 & S1 & U1 & COV).
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. unfold mpi_intop_stmtA_sz in HC.
      eapply HC with (h := hk) (LB := LBk) (LF := LF) (dX := d1) (dA := eA) (b := b) (lo := lo) (d := dd);
        rewrite ?(unsigned_lit (SP - FR)) by exact SPR.
      - exact HHk.
      - exact HK1.
      - exact HNF.
      - exact XM.
      - exact AM.
      - exact ASEP.
      - exact XNS.
      - exact AOS.
      - exact ACR.
      - exact ACRL.
      - exact XWR.
      - exact HB.
      - exact XLSq.
      - exact STk.
      - exact LOS.
      - clear - SLOK HSTK. lia.
      - rewrite HTk. clear - TOP FR0. lia.
      - exact SPA.
      - exact TPV.
      - exact MIk.
      - rewrite unsigned_lit by exact HRET. exact HRE.
      - exact XAO.
      - exact AAO.
      - exact AIM.
      - clear - HV HVk. lia.
      - exact (e1_uwc v f hk LBk mk J).
      - rewrite XAD. exact U1.
      - exact UWA.
      - clear - HF HFRk. lia.
      - clear - HC24 C24k. lia.
      - rewrite XAD. reflexivity.
      - reflexivity.
      - reflexivity. }
    eapply (e1_after v f hk LBk mk A1 d1 (PHI d1 eA) (FRC dd) (Rr LBk d1 eA b) RET); try eassumption.
    all: match goal with |- ?g => idtac "INTOP-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  #[using="EC"] Lemma e1_scratch : ltac2:(CDefT.buildp (gd_tbl_A_ecp_one_c24 ()) "Pv,$10.Pf,$10.Phk,(12.$13.VR,VHIA,)PLBk,(14.$5.)Pmk,P,(15.&40.)(16.(15.&8.))PA1,$10.Pd1,$1:.Pm',P,(15.&40.)(16.(15.&8.))P,(1;.R8.R7.R6.R5.R4.R3.R2.)P,(63.(39.(3:.$10.$10.)(3;.$10.$10.Vlo,(:.VSP,VFR,))(3<.(3:.$10.$10.)))R5.R2.)P,(64.$13.R6.R3.)P,(35.$13.R4.)P,(36.$13.R5.Vlo,(:.VSP,VFR,))(1;.R=.R<.R;.R:.R6.R8.R7.)")
(* [comment removed for export] *).
  Proof.
    ec_open. (intros v f hk LBk mk A1 d1 m' dd_H; ddestruct dd_H as (J & T1 & S1 & U1 & COV); intros MU WM MI' ST').
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk]. dpose S1 as (_ & SL1 & _).
    assert (HH' : HM asegs R HIA hk LBk LF m').
    { eapply (hm_munch asegs R HIA hk LBk LF [(lo, SP - FR)] mk m' HHk MU WM).
      apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. intros a Ha. left. left. rewrite HTk. clear - Ha LOS TOP FR0. lia. }
    destruct (ej_scratch R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk A1 d1 lo (SP - FR) m' J T1 SL1 MU WM MI' ST' HH' ltac:(clear; lia) ltac:(clear; lia)) as [J' T1'].
    exact (conj J' (conj T1' (conj S1 (conj U1 COV)))).
  Qed.

  (* [comment removed for export] *)
  Definition e1_rdable (hk : HST asegs R HIA) (LBk : list blk) (mk : mem) (e : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_one_c24 ()) "(0.(1<.$13.O2.O3.O1.)(0.P,(?.$1>.(1?.O1.)$27.)(;.=(28.O1.))(0.(65.$13.(30.VR,)(31.$13.VR,VHIA,O4.)O2.(21.O1.)+10.)(0.P,(9.+1.(2:.O1.))(65.$13.(30.VR,)(31.$13.VR,VHIA,O4.)O2.(28.O1.)(29.+4.(2:.O1.)))(0.(7.(9.(2>.(21.O1.)+10.)Vlo,)(9.(:.VSP,VFR,)(21.O1.)))P,(9.+1.(2:.O1.))(7.(9.(2>.(28.O1.)(29.+4.(2:.O1.)))Vlo,)(9.(:.VSP,VFR,)(28.O1.))))))))")
(* [comment removed for export] *).

  #[using="IMG EC STKMAX SP64 SPA SLOK STK0"] Lemma e1_rd : forall v f hk LBk mk A1 d1 e, E1I v f hk LBk mk A1 d1 -> e1_src A1 d1 e -> e1_rdable hk LBk mk e.
  Proof.
    intros v f hk LBk mk A1 d1 e S SE.
    ddestruct (e1_opnd v f hk LBk mk A1 d1 e S SE) as (EM & _ & (_ & _ & _ & OS4 & OS5) & _ & _ & [AOs AOl] & _ & _).
    destruct S as (J & _). pose proof (ej_hm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J) as HHk.
    pose proof EM as [(_ & _ & _ & _ & _ & OW) _].
    assert (NN : 1 <= md_n e -> md_own e <> LNull) by (intros N1 C; rewrite C in OW; destruct OW as [_ K]; clear - K N1; lia).
    unfold e1_rdable.
    split; [exact EM|].
    split.
    { intros EO. rewrite EO in OW. ddestruct OW as (_ & IN & _).
      destruct (hm_apart asegs R HIA hk LBk LF mk HHk) as [HF _]. rewrite Forall_forall in HF.
      destruct (HF _ ltac:(apply in_app_iff; left; exact IN)) as (B0 & _). exact B0. }
    split; [exact AOs|].
    split.
    { intros N1. destruct (md_own e) eqn:EO; [exfalso; exact (NN N1 eq_refl)| | exact (AOl eq_refl)].
      ddestruct OW as (_ & IN & _). eapply hm_aobj_block; [exact HHk| exact IN]. }
    split; [exact OS4|]. intros N1. exact (OS5 (NN N1)).
  Qed.

  (* [comment removed for export] *)
  #[using="EC SP64 SPA SLOK STK0"] Lemma e1_cmp : ltac2:(CDefT.buildp (gd_tbl_A_ecp_one_c24 ()) "PENTRY,$10.P,(66.$13.(30.VR,)R1.)Pv,$10.Pf,$10.Phk,(12.$13.VR,VHIA,)PLBk,(14.$5.)Pmk,P,(15.&40.)(16.(15.&8.))PA1,$10.Pd1,$1:.PeX,$1:.PeY,$1:.PRET,$10.Pxt0,(15.&40.)Pxt1,(15.&40.)Pxt2,(15.&40.)Pc1,(15.&40.)Pxa0,(15.&40.)Pxa1,(15.&40.)Pxa2,(15.&40.)Pxa3,(15.&40.)Pxa4,(15.&40.)Pxa5,(15.&40.)Pxa6,(15.&40.)Pxa7,(15.&40.)Pc2,(15.&40.)Pc3,(15.&40.)Pc4,(15.&40.)Pc5,(15.&40.)Pc6,(15.&40.)Pc7,(15.&40.)Pc8,(15.&40.)Pc9,(15.&40.)Pc10,(15.&40.)Pc11,(15.&40.)Pxt3,(15.&40.)Pxt4,(15.&40.)Pxt5,(15.&40.)Pxt6,(15.&40.)PQ,P,$45.SpP,(1;.R25.R24.R23.R22.R21.R20.R1?.)P,(67.R24.R23.R22.R1?.)P,(67.R25.R24.R23.R1?.)P,(9.+10.VSTKMAX,)P,(0.(9.=R20.)(;.R20.(<.+2.+40.)))P,(?.$10.(11.R21.+2.)=)P,Pm',P,(15.&40.)(16.(15.&8.))Pt0',(15.&40.)Pt1',(15.&40.)Pt2',(15.&40.)Pa1',(15.&40.)Pa2',(15.&40.)Pa3',(15.&40.)Pa4',(15.&40.)Pa5',(15.&40.)Pa6',(15.&40.)Pa7',(15.&40.)Pt3',(15.&40.)Pt4',(15.&40.)Pt5',(15.&40.)Pt6',(15.&40.)P,(1;.R3:.R39.R38.R37.R?.R35.R34.)(46.$13.(47.$13.VR,VHIA,R39.Vmo,)R17.(48.(49.(4:.&40.R32.)(4:.&40.(:.VSP,VFR,))Vgp,Vtp,R?.R>.R=.Vfpw,R2>.(4:.&40.(68.(:.(69.R34.)(69.R33.))))R<.R;.R:.R9.R8.R7.R6.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R5.R4.R3.R2.)VF,(4:.&40.R32.)Vfc,(4;.(15.&40.))R10.(4<.$13.)))P,(?.(15.&40.)R1>.(4:.&40.(21.R25.)))P,(?.(15.&40.)R1>.(4:.&40.(21.R25.)))(46.$13.(47.$13.VR,VHIA,R2<.Vmo,)R:.(48.(49.(4:.&40.R25.)(4:.&40.(:.VSP,VFR,))Vgp,Vtp,R24.R23.R22.Vfpw,R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.)VF,(4:.&40.R30.)Vfc,(4;.(15.&40.))R2:.(4<.$13.)))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose e1_base as (LO0 & LOSP & SPR & NE0 & LOS' & M8).
    dpose (ej_facts R HIA h LB LF m SP lo FR FRAME XO MC EC) as (_ & ALO & ACP & MCLO & SPHI).
    intros ENTRY HQ. intros until Q. intros S RX RY HSTK HRET HRE K E0 E1. subst xa0 xa1.
    ddestruct RX as (XM & XP0 & XOs & XOl & XSs & XSl). ddestruct RY as (YM & YP0 & YOs & YOl & YSs & YSl).
    pose proof S as (J & _). pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    assert (SCS : crange (hcs asegs R HIA hk) lo (SP - FR - lo)).
    { eapply crange_sub; [exact (hcs_stack asegs R HIA hk)| clear - LOS; lia| rewrite HSk; clear - SPHI FR0; lia]. }
    eapply (aevtA_cut_evtA_KF asegs R HIA hk mo).
    { unfold mpi_cmp_mpi_stmtA in HQ.
      eapply HQ with (CS := hcs asegs R HIA hk) (LB := LBk) (dX := eX) (dY := eY) (lo := lo); rewrite ?(unsigned_lit (SP - FR)) by exact SPR;
        first [ exact XM | exact YM | exact XP0 | exact YP0 | exact MIk | exact (art_alwf asegs R HIA) | exact (hcs_ok asegs R HIA hk) | exact (hm_abase asegs R HIA hk LBk LF mk HHk)
              | exact XOs | exact YOs | exact XOl | exact YOl | exact STk | exact LO0 | exact SPA | exact SCS | exact XSs | exact YSs | exact XSl | exact YSl | reflexivity
              | (clear - LOSP HSTK; lia) | idtac ].
      all: match goal with |- ?g => idtac "CMP-PRE-LEFT:" g end. }
    intros ms' PO. unfold mpi_cmp_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & E & MU2 & WM2 & MI2 & ST2). subst ms'.
    rewrite ?(unsigned_lit (SP - FR)) in MU2, ST2 by exact SPR.
    rewrite (ret_pc_even RET HRET HRE).
    eapply K. exact (e1_scratch v f hk LBk mk A1 d1 m2 S MU2 WM2 MI2 ST2).
    all: match goal with |- ?g => idtac "CMP-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG EC TPV STKMAX SP64 SPA SLOK STK0"] Lemma e1_cmpint : forall ENTRY : Z, mpi_cmp_int_stmtA asegs R HIA ENTRY ->
    forall (v f : Z) (hk : HST asegs R HIA) (LBk : list blk) (mk : mem) (A1 : Z) (d1 eX : mpd) (z RET slo : Z)
      (xt0 xt1 xt2 c1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 xt3 xt4 xt5 xt6 : word) (Q : config -> Prop),
    E1I v f hk LBk mk A1 d1 -> e1_src A1 d1 eX -> (length LF < 512)%nat ->
    sshad asegs AL m slo SP -> arl_stklo R <= slo -> slo <= lo ->
    -2^31 <= z < 2^31 -> MPI_CMP_INT_STACK_A <= STKMAX -> 0 <= RET < 2^64 -> RET mod 2 = 0 ->
    (forall (h' : HST asegs R HIA) (m' : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
       E1I v f h' LBk m' A1 d1 ->
       aevtA asegs (KF asegs R HIA h' mo) Q (MS (mkR (Z_to_bv 64 RET) (Z_to_bv 64 (SP - FR)) gp tp t0' t1' t2' fpw c1
         (Z_to_bv 64 (Z.sgn (mpd_val eX - z))) a1' a2' a3' a4' a5' a6' a7' c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 t3' t4' t5' t6')
         F (Z_to_bv 64 RET) fc None m' (seg_rom asegs))) ->
    xa0 = Z_to_bv 64 (md_addr eX) -> xa1 = Z_to_bv 64 z ->
    aevtA asegs (KF asegs R HIA hk mo) Q (MS (mkR (Z_to_bv 64 RET) (Z_to_bv 64 (SP - FR)) gp tp xt0 xt1 xt2 fpw c1
      xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 ENTRY) fc None mk (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    ec_open. dpose e1_base as (LO0 & LOSP & SPR & NE0 & LOS' & M8).
    intros ENTRY HQ. intros until Q. intros S SE HNF SSm SL1 SL3 HZ HSTK HRET HRE K E0 E1. subst xa0 xa1.
    pose proof (e1_rd v f hk LBk mk A1 d1 eX S SE) as RX.
    ddestruct RX as (XM & XP0 & XOs & XOl & XSs & XSl).
    ddestruct (e1_opnd v f hk LBk mk A1 d1 eX S SE) as (_ & _ & _ & XCR & _ & _ & XIM & _).
    ddestruct (e1_out v f hk LBk mk A1 d1 S) as (DM & DNS & DAD & DOS & DCR & DCRL & _ & _ & _ & _).
    pose proof S as (J & _). pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    pose proof (ej_sshad R HIA h LB LF m SP lo FR FRAME XO MC EC v f hk LBk mk slo J SSm SL1) as SSq.
    pose proof (proj1 (sshad_split asegs AL mk slo (SP - FR) SP SSq ltac:(clear - SL3 LOSP STK0 FR0; lia) M8)) as SSk.
    pose proof (arl_need_ecp_smalloc R) as NSE.
    eapply (aevtA_cut_evtA_KF asegs R HIA hk mo).
    { unfold mpi_cmp_int_stmtA in HQ.
      eapply HQ with (h := hk) (LB := LBk) (LF := LF) (dX := eX) (z := z) (lo := lo) (slo := slo); rewrite ?(unsigned_lit (SP - FR)) by exact SPR;
        first [ exact HHk | exact HNF | exact XM | exact XP0 | exact HZ | exact MIk | exact XOs | exact XOl | exact XCR | exact XIM | exact STk | exact LOS
              | exact SPA | exact TPV | exact SSk | exact SL1 | exact XSs | exact XSl | reflexivity
              | (clear - LOSP HSTK; lia) | (clear - SLOK HSTK NSE; lia) | (rewrite HTk; clear - TOP FR0; lia) | (clear - SL3 LOSP HSTK; lia) | idtac ].
      all: match goal with |- ?g => idtac "CMPINT-PRE-LEFT:" g end. }
    intros ms' PO. unfold mpi_cmp_int_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & h2 & E & MI2 & ST2 & HP2 & HCS2 & HT2 & HS2 & HF2 & HV2 & HFR2 & HKI2 & HH2). subst ms'.
    rewrite ?(unsigned_lit (SP - FR)) in ST2, HP2 by exact SPR.
    rewrite (ret_pc_even RET HRET HRE).
    assert (MX2 : mpd_at asegs m2 LBk d1).
    { destruct DOS as (_ & _ & _ & DS4 & DS5).
      eapply (OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec.MpiOpnd.mpd_at_heap_presx asegs L mk m2 LBk (LBk ++ fdata LF) LBk (SP - FR) [] d1 DM
               (presA_presx asegs R LBk LF (SP - FR) (arl_stklo R) (hstkhi asegs R HIA hk) [] mk m2 HP2) MIk MI2).
      - rewrite DAD in DS4 |- *. eapply client_range_sep; [exact DCR| intros b Hb; exact Hb| exact DS4].
      - intros EO. eapply client_range_sep; [exact (DCRL EO)| intros b Hb; exact Hb| apply DS5; rewrite EO; discriminate].
      - exact I.
      - intros _; exact I.
      - intros b Hb. destruct DM as [(_ & _ & _ & _ & _ & OW) _]. unfold mpd_blk in Hb.
        destruct (md_own d1); first [ destruct Hb as [<-|[]]; destruct OW as (_ & IN & _); exact IN | destruct Hb ]. }
    pose proof (e1_call v f hk LBk mk A1 d1 m2 h2 LBk d1 (SP - FR) 0 0 S ltac:(clear - SLO; lia) ltac:(lia) ltac:(lia) MI2 ST2
                  (presA_weaken asegs R LBk (mpd_keep LBk d1) LF LF (SP - FR) (SP - FR) (arl_stklo R) (arl_stklo R) (hstkhi asegs R HIA hk) (hstkhi asegs R HIA hk)
                     [] [(A1, A1 + 16)] mk m2 HP2 (fun b Hb => OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B.A_mpi_read_binary_stmt.In_mpd_keep LBk d1 b Hb) (fun b Hb => Hb)
                     (Z.le_refl _) (Z.le_refl _) (Z.le_refl _) (fun x _ => I))
                  HT2 HS2 HF2 ltac:(intros x Hx; rewrite HCS2; exact Hx) ltac:(rewrite HV2; lia) ltac:(rewrite HFR2; lia) HH2 MX2 (mpd_out_refl LBk d1 DNS) (fun b Hb => or_introl Hb)) as S2.
    rewrite !Z.add_0_r in S2.
    intros mo1 [K1 K2].
    refine (K h2 m2 y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 S2 mo1 _).
    split; [apply (proj2 (HKI2 mo1)); exact K1| exact K2].
  Qed.

  #[using="h LB m SP lo FR FRAME XO MC EC"] Lemma e1_keep_fresh : ltac2:(CDefT.buildp (gd_tbl_A_ecp_one_c24 ()) "Phq,(12.$13.VR,VHIA,)PLBq,(14.$5.)Pmq,P,(15.&40.)(16.(15.&8.))Pdq,$1:.P,(40.$13.VR,VHIA,R4.R3.VLF,R2.)P,(?.$1>.(1?.R2.)$27.)P,(6.(3:.$10.$10.)(3;.$10.$10.(28.R3.)(29.+4.(2:.R3.)))R5.)(42.VR,(38.R6.R4.)VLF,(28.R4.)(29.+4.(2:.R4.)))")
(* [comment removed for export] *).
  Proof.
    ec_open. intros hq LBq mq dq HHq EO XIN. pose proof (HND _ _ _ _ HHq) as ND.
    destruct (hm_apart asegs R HIA hq LBq LF mq HHq) as [HF BA]. rewrite Forall_forall in HF.
    destruct (HF _ ltac:(apply in_app_iff; left; exact XIN)) as (B0 & _ & BC & BI). cbn [fst snd] in B0, BC, BI.
    split; [exact B0|]. split; [exact BC|]. split; [destruct DIMG as [D1 D2]; clear - BI D1 D2; lia|].
    intros B j Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
    - unfold mpd_keep in Hb. rewrite EO in Hb. apply filter_In in Hb. destruct Hb as [Hb Hne].
      assert (NE : md_p dq <> B).
      { intros E. symmetry in E. revert E. apply (nodup_fst_neq LBq (md_p dq) (4 * md_n dq) B j ND XIN Hb).
        intros E. rewrite E in Hne. unfold blk_eqb in Hne. cbn [fst snd] in Hne. rewrite !Z.eqb_refl in Hne. discriminate Hne. }
      pose proof (blocks_apart_in2 (LBq ++ LF) _ _ _ _ BA ltac:(apply in_app_iff; left; exact XIN) ltac:(apply in_app_iff; left; exact Hb) NE) as K. clear - K. lia.
    - ddestruct (ep_fdata_sub2 LF (B, j) Hb) as ([FBq nq] & Hfb & H1 & H2). cbn [fst snd] in H1, H2.
      pose proof (ep_blocks_apart_app2 LBq LF (md_p dq, 4 * md_n dq) (FBq, nq) BA XIN Hfb) as K. cbn [fst snd] in K. clear - K H1 H2. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="EC TPV D0 SP64 SPA SLOK STK0 XOUW"] Lemma e1_free : ltac2:(CDefT.buildp (gd_tbl_A_ecp_one_c24 ()) "PENTRY,$10.P,(6;.$13.VR,VHIA,R1.)Pv,$10.Pf,$10.Phk,(12.$13.VR,VHIA,)PLBk,(14.$5.)Pmk,P,(15.&40.)(16.(15.&8.))PA1,$10.Pd1,$1:.PRET,$10.Pxt0,(15.&40.)Pxt1,(15.&40.)Pxt2,(15.&40.)Pc1,(15.&40.)Pxa0,(15.&40.)Pxa1,(15.&40.)Pxa2,(15.&40.)Pxa3,(15.&40.)Pxa4,(15.&40.)Pxa5,(15.&40.)Pxa6,(15.&40.)Pxa7,(15.&40.)Pc2,(15.&40.)Pc3,(15.&40.)Pc4,(15.&40.)Pc5,(15.&40.)Pc6,(15.&40.)Pc7,(15.&40.)Pc8,(15.&40.)Pc9,(15.&40.)Pc10,(15.&40.)Pc11,(15.&40.)Pxt3,(15.&40.)Pxt4,(15.&40.)Pxt5,(15.&40.)Pxt6,(15.&40.)PQ,P,$45.SpP,(1;.R23.R22.R21.R20.R1?.R1>.R1=.)P,(9.+40.VSTKMAX,)P,(9.(2>.(3>.$13.VR,VHIA,Vh,)(2>.R25.$6<.))$55.)P,(9.(2>.(3?.$13.VR,VHIA,Vh,)(2>.R25.(6=.Vdd,)))$57.)P,(0.(9.=R20.)(;.R20.(<.+2.+40.)))P,(?.$10.(11.R21.+2.)=)P,Ph',(12.$13.VR,VHIA,)PLB',(14.$5.)Pm',P,(15.&40.)(16.(15.&8.))Pt0',(15.&40.)Pt1',(15.&40.)Pt2',(15.&40.)Pa0',(15.&40.)Pa1',(15.&40.)Pa2',(15.&40.)Pa3',(15.&40.)Pa4',(15.&40.)Pa5',(15.&40.)Pa6',(15.&40.)Pa7',(15.&40.)Pt3',(15.&40.)Pt4',(15.&40.)Pt5',(15.&40.)Pt6',(15.&40.)P,(1;.(2>.R3;.$6<.)(2>.R3:.(6=.Vdd,))R12.R11.R10.R36.(6>.R36.+1.==(3<.(15.&40.))(6?.R35.)$2=.))(46.$13.(47.$13.VR,VHIA,R13.Vmo,)R1:.(48.(49.(4:.&40.R35.)(4:.&40.(:.VSP,VFR,))Vgp,Vtp,R10.R?.R>.Vfpw,R31.R=.R<.R;.R:.R9.R8.R7.R6.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R5.R4.R3.R2.)VF,(4:.&40.R35.)Vfc,(4;.(15.&40.))R11.(4<.$13.)))P,(?.(15.&40.)R1>.(4:.&40.R25.))(46.$13.(47.$13.VR,VHIA,R29.Vmo,)R9.(48.(49.(4:.&40.R24.)(4:.&40.(:.VSP,VFR,))Vgp,Vtp,R23.R22.R21.Vfpw,R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)VF,(4:.&40.R2=.)Vfc,(4;.(15.&40.))R27.(4<.$13.)))")
(* [comment removed for export] *).
  Proof.
    ec_open. dpose e1_base as (LO0 & LOSP & SPR & NE0 & LOS' & M8). pose proof (arl_need_ecp_rt R) as NER.
    intros ENTRY HC. intros until Q. intros S HSTK HV HF HRET HRE K E0. subst xa0.
    ddestruct (e1_out v f hk LBk mk A1 d1 S) as (XM & XNS & XAD & XOS & XCR & XCRL & XWR & XLSq & XAO & XIM).
    dpose S as (J & T1 & S1 & U1 & COV). dpose S1 as (CW1 & SL1 & _).
    pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    pose proof (ejtmp_blk R HIA h LB LF m SP lo FR FRAME XO MC v f hk LBk mk A1 d1 J T1) as BLK.
    pose proof (HND _ _ _ _ HHk) as NDk.
    pose proof XM as [MAT SG1]. dpose MAT as (CX1 & AL1 & X01 & LL1 & NR1 & OW1).
    (* [comment removed for export] *)
    assert (SUBF : forall b, In b LB -> In b (mpi_free_LB (md_own d1) (md_p d1) (md_n d1) LBk)).
    { intros b Hb. unfold mpi_free_LB. destruct (md_own d1) eqn:EO; try exact (SUBk b Hb).
      ddestruct (BLK eq_refl) as (IN & _ & _ & _ & _ & NIN & _). destruct b as [B j]. apply In_lb_remove_keep; [exact (SUBk _ Hb)|].
      apply (nodup_fst_neq LBk (md_p d1) (4 * md_n d1) B j NDk IN (SUBk _ Hb)). intros E. apply NIN. rewrite <- E. exact Hb. }
    eapply aevtA_call.
    { intros mo1 [HK1 MF1]. unfold mpi_free_stmtA in HC.
      eapply HC with (h := hk) (LB := LBk) (LF := LF) (X := md_addr d1) (sw := Z_to_bv 64 (md_sg d1)) (n := md_n d1) (P := md_p d1) (limbs := md_limbs d1)
                     (pad := md_pad d1) (own := md_own d1) (lo := lo) (d := dd);
        rewrite ?(unsigned_lit (SP - FR)) by exact SPR.
      - exact HHk.
      - exact HK1.
      - exact MAT.
      - exact XNS.
      - rewrite XAD, HTk. eapply client_wrange_sp_mono; [| eapply client_wrange_mono; [exact CW1|]].
        + clear - FR0. lia.
        + intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact (SUBF b Hb)| right; exact Hb].
      - intros EO. rewrite XAD. pose proof (proj1 (proj2 XOS) EO) as K1. rewrite XAD in K1. exact K1.
      - exact STk.
      - exact LOS.
      - clear - SLOK HSTK NER. lia.
      - rewrite HTk. clear - TOP FR0. lia.
      - exact SPA.
      - exact TPV.
      - exact MIk.
      - exact (proj1 XAO).
      - clear - HV HVk. lia.
      - rewrite XAD. exact U1.
      - clear - HF HFRk. lia.
      - rewrite XAD. reflexivity. }
    (intros ms' mo' dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)). unfold mpi_free_postA in PO.
    ddestruct PO as (y0 & y1 & y2 & ya0 & ya1 & ya2 & ya3 & ya4 & ya5 & ya6 & ya7 & y3 & y4 & y5 & y6 & m2 & mo2 & h2 & E & MI2 & ST2 & MF2 & HP2 & HT2 & HS2 & HF2 & HK2 & HCS2 & HV2 & HFR2 & HH2 & CX2).
    injection E as E1 E2. subst ms' mo'.
    rewrite ?(unsigned_lit (SP - FR)) in ST2, HP2 by exact SPR. rewrite XAD in HP2, CX2.
    rewrite (ret_pc_even RET HRET HRE).
    set (d1' := mkMPD A1 1 0 0 [] (md_pad d1) LNull).
    set (LB2 := mpi_free_LB (md_own d1) (md_p d1) (md_n d1) LBk) in *.
    assert (MX2 : mpd_at asegs m2 LB2 d1').
    { unfold d1', mpd_at, mpi_at. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own]. rewrite XAD in AL1, X01.
      split; [| left; reflexivity]. split; [exact CX2|]. split; [exact AL1|]. split; [exact X01|]. split; [reflexivity|]. split; [unfold MPI_MAX_LIMBS; clear; lia| split; reflexivity]. }
    assert (OUT2 : mpd_out LBk d1 LB2 d1').
    { unfold mpd_out, d1', LB2, mpi_free_LB. cbn [md_addr md_own]. split; [symmetry; exact XAD|]. split; [discriminate|].
      destruct (md_own d1) eqn:EO.
      - split; [intros b Hb; left; exact Hb|]. split; [intros b Hb _; exact Hb|]. intros b Hb. unfold mpd_blk in Hb. rewrite EO in Hb. destruct Hb.
      - destruct (BLK eq_refl) as (IN & _).
        split; [intros b Hb; left; exact (In_lb_remove _ _ _ Hb)|].
        split.
        + intros [B j] Hb NB. apply In_lb_remove_keep; [exact Hb|].
          apply (nodup_fst_neq LBk (md_p d1) (4 * md_n d1) B j NDk IN Hb). intros E. apply NB. unfold mpd_blk. rewrite EO. left. symmetry. exact E.
        + intros b Hb Hb2. exfalso. unfold mpd_blk in Hb. rewrite EO in Hb. destruct Hb as [<-|[]]. exact (lb_remove_notin LBk (md_p d1) (4 * md_n d1) NDk Hb2).
      - exfalso. exact (XNS eq_refl). }
    assert (HP2' : presA asegs R (mpd_keep LBk d1) LF (SP - FR) (arl_stklo R) (hstkhi asegs R HIA hk) [(A1, A1 + 16)] mk m2).
    { unfold LB2, mpi_free_LB, mpi_free_X in HP2. destruct (md_own d1) eqn:EO.
      - unfold mpd_keep. rewrite EO. exact HP2.
      - destruct (BLK eq_refl) as (IN & _).
        eapply (presA_drop_fresh asegs R HIA hk (mpd_keep LBk d1) LF [(A1, A1 + 16)] (md_p d1) (4 * md_n d1) mk m2 (SP - FR)); [| exact (e1_keep_fresh hk LBk mk d1 HHk EO IN)| clear - LOS LOSP STK0; lia].
        eapply presA_weaken; [exact HP2| | intros b Hb; exact Hb| apply Z.le_refl| apply Z.le_refl| apply Z.le_refl|].
        + intros [B j] Hb. unfold mpd_keep in Hb. rewrite EO in Hb. apply filter_In in Hb. destruct Hb as [Hb Hne].
          apply In_lb_remove_keep; [exact Hb|].
          apply (nodup_fst_neq LBk (md_p d1) (4 * md_n d1) B j NDk IN Hb).
          intros E. rewrite E in Hne. unfold blk_eqb in Hne. cbn [fst snd] in Hne. rewrite !Z.eqb_refl in Hne. discriminate Hne.
        + intros x Hx. cbn [outside fst snd] in *. tauto.
      - exfalso. exact (XNS eq_refl). }
    pose proof (e1_call v f hk LBk mk A1 d1 m2 h2 LB2 d1' (SP - FR) AVOL_CALL (fr_charge dd) S
                ltac:(clear - LOSP STK0; lia) ltac:(unfold AVOL_CALL; clear; lia) ltac:(unfold fr_charge; clear - D0; lia)
                MI2 ST2 HP2' HT2 HS2 HF2 HCS2 HV2 HFR2 HH2 MX2 OUT2 ltac:(intros b Hb; destruct Hb)) as S2'.
    apply (aevtA_enter asegs (KF asegs R HIA h2 mo) _ _ mo2 (conj HK2 (mo_frame_trans _ _ _ MF1 MF2))).
    eapply K. exact S2'.
    all: match goal with |- ?g => idtac "FREE-LEFT:" g end.
  Qed.
End E1.
