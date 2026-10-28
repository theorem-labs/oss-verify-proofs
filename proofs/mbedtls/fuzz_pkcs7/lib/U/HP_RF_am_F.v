(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free MallocTree MallocModel_B F_ntf_A F_ntf_B MallocKit_B MallocKit_B3 F_am_A F_am_K F_am_C F_am_F.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Prog.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import HP_RMallocRep HP_RMallocTree HP_RMallocKit_B HP_RMallocKit_B3 HP_RF_mm_syscalls HP_RF_ntf_A HP_RF_am_A HP_RF_am_K HP_RF_am_C.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_HP_RF_am_F () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.aptr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_avail_meta_area_count"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctx"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.optr"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_avail_meta_areas"; "Corelib.Init.Datatypes.Some"; "stdpp.base.lookup"; "Corelib.Numbers.BinNums.N"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "Corelib.Init.Datatypes.fst"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "RocqVerifyHarness.AgentSubmission.Heap.F_am_C.pgal"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.round_up_pg"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_len"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.conc"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmprotect_entry"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "RocqVerifyHarness.AgentSubmission.U.HP_RF_am_A.ram_fp"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.U.HP_RF_am_A.ram_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.U.HP_RF_am_A.ram_ret_post"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_mem"].


(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L16075393784.51L17210665673.53L17260316077.27L43735480156.51L43737297015.55L53519027360.5100000700?00i01201S01TS2st2CRS1p1r2S0S1p1r2r23SAL2r14RBAL1q2r01H2H02q02H42q12H9S2st1p2PBS3hRP3RCB2st1p1r2S02S13RB03RBC2CpS". (* [comment removed for export] *)
#[using="Type"] Lemma ram_disp_fin : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_F ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pst,$3.Pp,$4.Pr,$5.P,(6.VhRP,R3.R4.)P,(7.(8.$9.(:.(;.R4.))=))P,(<.(=.=(:.(;.R5.)))(>.(:.(;.R5.))(?.+2.+40.)))P,(8.$10.(11.(;.R6.))(12.$4.R5.))P,(8.(2.$5.)(13.$14.$5.(15.$14.$16.$17.$5.)(18.$14.$16.$17.$5.)(19.$14.$9.R6.)(1:.R7.))(12.$5.R5.))P,(1;.(1<.$14.$9.R7.))P,(=.=(1<.$14.$9.R8.))P,(=.(1=.(1<.$14.$9.R9.)+1000.)(1>.(1?.R8.)))(20.$21.Lms',$22.(8.$22.R1.(23.(24.R10.R2;.R2:.R29.R28.R27.R26.(25.&40.+1000.)(25.&40.(26.R<.R;.))(25.&40.=)R23.R22.R21.R20.R1?.R1>.R1=.(25.&40.$27.)(25.&40.$28.)R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.)R?.(25.&40.+40538.)R>.(29.(0.&40.))R=.(2:.$21.)))(23.(24.R?.R2:.R29.R28.R27.R26.R25.(25.&40.+1000.)R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.(25.&40.$27.)(25.&40.$28.)R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.)R>.(25.&40.+40398.)R=.(29.(0.&40.))R<.(2:.$21.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until r. intros MR CNT CR AMA Hr SAL S0 S1.
  dpose MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite AMA in C1.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  dpose WF as (_ & WR & _). destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & _). rceilb.
  pose proof (conc_region' st p r Hr) as Cp. pose proof (round_up_pg_ge (r_len r)) as RU.
  assert (AL : Z.land (conc st p) 4095 = 0).
  { rewrite Cp. unfold pgal in SAL. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
    clear - RBAL SAL S0 RB0. Z.div_mod_to_equations. lia. }
  assert (AL' : Z.land 4095 (conc st p) = 0) by (rewrite Z.land_comm; exact AL).
  assert (PB : 0 <= conc st p < 2^64) by lia.
  clear RBAL RU RBC RL0 WR.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  (* [comment removed for export] *)
  st1. st1.
  assert (CF : negb (bv_eqb (Z_to_bv 64 (c_avail_meta_area_count (ctx st))) (Z_to_bv 64 0)) = true)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Bool.negb_true_iff; apply Z.eqb_neq; exact CNT).
  rewrite CF.
  (* [comment removed for export] *)
  st1. apply Bool.negb_true_iff in CF. rewrite CF. clear CF.
  st1. st1.
  (* [comment removed for export] *)
  st1. st1. rewrite ?AL, ?AL'. st1.
  change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.
  apply evt_done. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="hRP"] Lemma ram_to_mprotect : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_F ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))PP,$9.(20.$21.Lms',$22.(8.$22.R1.(23.(24.(25.&40.+40548.)R22.R21.R20.R1?.R1>.R1=.(25.&40.+1000.)(25.&40.R2.)(25.&40.R2.)(25.&40.+1000.)(25.&40.+3.)R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.)R5.(25.&40.$2;.)R4.(29.(0.&40.))R3.(2:.$21.)))(23.(24.R5.R21.R20.R1?.R1>.R1=.R1<.(25.&40.+1000.)(25.&40.R1.)R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)R4.(25.&40.+40538.)R3.(29.(0.&40.))R2.(2:.$21.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  apply evt_done. unfold rmprotect_entry. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="hRP"] Lemma ram_mp_ok0 : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_F ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))(20.$21.Lms',$22.(8.$22.R1.(23.(24.R5.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.(25.&40.=)R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)R4.(25.&40.+404:8.)R3.(29.(0.&40.))R2.(2:.$21.)))(23.(24.R4.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.(25.&40.=)R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.)R3.(25.&40.+40548.)R2.(29.(0.&40.))R1.(2:.$21.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros.
  st1. rewrite bv_eqb_refl. cbv iota.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L36423605256.60L42838483058.58L44863293554.60L47041257222.58L49345641752.59L5264219782.58 L53682221874.59L64891909666.58L8832910886.61 00000<00B00U00V00Z00[00\00b013S2sp2lo4LOLES1e2ERS3hRP2sp2lo2LO4LOLESS2spSSS1e2ERS2sp2lo4LOLE1x2Hx". (* [comment removed for export] *)
#[using="Type"] Lemma ram_mp_fail : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_F ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)Praw,(0.&40.)Ps0o,(0.&40.)Ps1o,(0.&40.)Ps2o,(0.&40.)Ps3o,(0.&40.)Ps4o,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(2.(0.&8.))Pm,P,(0.&40.)(2.(0.&8.))Pjunk,(2<.(0.&8.))Plo,$9.Pe,$9.Pst,$3.P,(6.VhRP,R1.R5.)P,(2=.$21.R6.)P,(8.(0.&40.)R2:.(25.&40.+5=0<8.))P,(2>.$21.R8.(1=.(2?.&40.R2;.)-:4.)(30.$31.(32.(25.&40.R5.))(33.$31.)))P,(<.(=.+1.R6.)(=.R6.+???.))P,(7.(8.$9.R7.+26.))P,(34.(35.R7.R9.(2?.&40.R30.))R<.R;.)P,(36.$21.R=.R<.)P,(2>.$21.R=.(1=.(2?.&40.R32.)-40.)(37.VhRP,R<.R11.R12.R13.R14.R15.R16.))P,(38.$21.R>.R<.(1=.(2?.&40.R33.)-40.))P,(=.(39.VhRP,)R=.)P,(=.R>.(3:.(2?.&40.R35.)+40.))(20.$21.Lms',$22.(<.(3;.VhRP,R1;.R37.R36.R35.R1:.R19.R18.R17.R16.R27.R26.R25.R24.R23.R22.R21.R15.R14.R10.R>.R13.R>.(25.&40.=)R1.)(2>.$21.(3<.R1.)(1=.(2?.&40.R35.)-:4.)(30.$31.(32.(25.&40.R?.))(33.$31.))))(23.(24.R1;.(25.&40.(1=.(2?.&40.R36.)-40.))R35.R34.R33.R32.R31.R30.R2?.(25.&40.-1.)R2>.R2=.R2<.R2;.R2:.R29.R28.(25.&40.$27.)(25.&40.$28.)R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)R14.(25.&40.+40548.)R13.(29.(0.&40.))R11.(2:.$21.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until st. intros MR MI TP ERR ER E38 PE0 WM0 FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  dpose MR as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
  subst tp. rewrite (unsigned_lit 0x5d0c8) in * by lia. change (381128 + -164) with 380964 in *.
  change (Z_to_bv 64 e) with (wz e) in ERR.
  rceilb; unfold RCTX, RMLOCK, RSSP_GUARD, ram_frame in *.
  (* [comment removed for export] *)
  st1. change (bv_eqb (Z_to_bv 64 (-1)) (Z_to_bv 64 0)) with false. cbv iota.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1. rewrite sx32_wz by lia. st1. st1.
  assert (CF : bv_eqb (wz e) (Z_to_bv 64 38) = false)
    by (unfold bv_eqb, wz; rewrite !unsigned_lit by lia; apply Z.eqb_neq; exact E38).
  rewrite CF; clear CF.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRX : rmrep st mX) end.
  { eapply rmrep_transport_high; [exact MR| exact MU| exact WM|]. intros l h [E|[]]; inversion E; subst; rceilb; lia. }
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. split.
  - unfold ram_ret_post. deexists 15. split; [reflexivity|].
    split.
    { eapply rpres_except_trans; [exact PE0|].
      apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply ram_fp_stack. lia. }
    split; [eapply wmono_trans; [exact WM0| exact WM]|]. split; [assumption|]. split; [exact ST|]. exact MRX.
  - cbn [ms_mem]. change (wz e) with (Z_to_bv 64 e) in ERR. exact ERR.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End RP_1.
