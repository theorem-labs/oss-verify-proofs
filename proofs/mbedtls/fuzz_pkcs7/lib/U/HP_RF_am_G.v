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
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_malloc_free MallocTree MallocModel_B F_ntf_A F_ntf_B MallocKit_B MallocKit_B3 F_am_A F_am_K F_am_C F_am_G.
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
Ltac2 gd_tbl_HP_RF_am_G () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.mstate"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmrep"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_avail_meta_area_count"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.ctx"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.brkstate"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_brk"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.BrkDead"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "RocqVerifyHarness.AgentSubmission.U.HP_F_syscalls.rsegs"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RSSP_GUARD"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.RMLOCK"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.c_meta_alloc_shift"; "Stdlib.ZArith.BinInt.Z.shiftl"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocRep.rmmap_entry"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.U.HP_RMallocTree.rpres_except"; "RocqVerifyHarness.AgentSubmission.U.HP_RF_am_A.ram_fp"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.U.HP_RF_am_A.ram_frame"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Heap.RunParams.rceil"; "RocqVerifyHarness.AgentSubmission.U.HP_RF_am_A.ram_ret_post"; "Corelib.Numbers.BinNums.N"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.region"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.s_regions"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Heap.Malloc.r_base"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Heap.F_am_G.mm_ok_st"].


(* [comment removed for export] *)
(* [comment removed for export] *)
Section RP_1. Context {hRP : run_params}.
#[using="Type"] Lemma ram_disp_dead : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_G ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pst,$3.P,(4.VhRP,R1.R2.)P,(5.$6.(7.(8.R2.))=)P,(5.$9.(:.(8.R3.))$;.)(<.$=.Lms',$>.(5.$>.R1.(?.(10.R9.R24.R23.R22.R21.R20.R1?.(11.&40.+1000.)(11.&40.(12.(13.+2.+40.)+1.))(11.&40.=)(11.&40.-1.)R1;.R1:.R19.R18.R17.R16.(11.&40.$14.)(11.&40.$15.)R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)R8.(11.&40.+40448.)R7.(16.(0.&40.))R6.(17.$=.)))(?.(10.R8.R23.R22.R21.R20.R1?.R1>.(11.&40.+1000.)R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.(11.&40.$14.)(11.&40.$15.)R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.)R7.(11.&40.+40398.)R6.(16.(0.&40.))R5.(17.$=.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until st. intros MR CNT BRK.
  dpose MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
  unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. change (512968 + 912) with 513880 in C6.
  (* [comment removed for export] *)
  st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* [comment removed for export] *)
  st1. st1. st1.
  change (bv_eqb (Z_to_bv 64 (2 ^ 64 - 1)) (Z_to_bv 64 (-1))) with true. cbv iota.
  (* [comment removed for export] *)
  st1. rewrite bv_eqb_refl. cbv iota.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L12589638492.40L16075715145.39L41416074189.39L44418219648.39L45337639803.39L8708555059.39 00000900B00H00Q00Z00cS2st1n2NRS2st2SH1nS2st1nS2st2SH1nS2st2SH1nS2st2SH1n". (* [comment removed for export] *)
#[using="Type"] Lemma ram_to_mmap : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_G ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))Pst,$3.P,(4.VhRP,R1.R2.)P,(18.(19.=(1:.(8.R2.)))(19.(1:.(8.R2.))+28.))Zn,$6.(1;.+2.(1:.(8.R3.)))(<.$=.Lms',$>.(5.$>.R1.(?.(10.(11.&40.+40474.)R24.R23.R22.R21.R20.R1?.(11.&40.+1000.)(11.&40.R2.)(11.&40.=)(11.&40.(1<.R2.+1000.))(11.&40.=)(11.&40.+22.)(11.&40.-1.)(11.&40.=)R17.R16.(11.&40.$14.)(11.&40.$15.)(11.&40.-1.)R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)R8.(11.&40.$1=.)R7.(16.(0.&40.))R6.(17.$=.)))(?.(10.R8.R23.R22.R21.R20.R1?.R1>.(11.&40.+1000.)R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.(11.&40.$14.)(11.&40.$15.)R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.)R7.(11.&40.+40448.)R6.(16.(0.&40.))R5.(17.$=.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until st. intros MR SH n.
  dpose MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  unfold RCTX, RMLOCK, RSSP_GUARD in *.
  (* [comment removed for export] *)
  st1. st1. st1.
  rewrite (Z.mod_small (c_meta_alloc_shift (ctx st)) 64) by lia.
  assert (NR : 0 < Z.shiftl 2 (c_meta_alloc_shift (ctx st)) <= 2^41).
  { rewrite Z.shiftl_mul_pow2 by lia. split; [apply Z.mul_pos_pos; [lia| apply Z.pow_pos_nonneg; lia]|].
    change (2^41) with (2 * 2^40). apply Z.mul_le_mono_nonneg_l; [lia|]. apply Z.pow_le_mono_r; lia. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1.
  apply evt_done. unfold rmmap_entry. subst n. reflexivity.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L36423605256.56L44863293554.56L49345641752.55L8832910886.57 00000<00O00S00dS2sp2lo4LOLES3hRP2sp2lo2LO4LOLES2spS2sp2lo4LOLE1x2Hx". (* [comment removed for export] *)
#[using="Type"] Lemma ram_mm_fail : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_G ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)Praw,(0.&40.)Ps0o,(0.&40.)Ps1o,(0.&40.)Ps2o,(0.&40.)Ps3o,(0.&40.)Ps4o,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(2.(0.&8.))Pm,P,(0.&40.)(2.(0.&8.))Pjunk,(1>.(0.&8.))Plo,$6.Pst,$3.P,(4.VhRP,R1.R4.)P,(1?.$=.R5.)P,(20.(21.R3.R4.(22.&40.R2:.))R7.R6.)P,(23.$=.R8.R7.)P,(24.$=.R8.(25.(22.&40.R2<.)-40.)(26.VhRP,R7.R<.R=.R>.R?.R10.R11.))P,(27.$=.R9.R7.(25.(22.&40.R2=.)-40.))P,(19.(28.VhRP,)R8.)P,(19.R9.(12.(22.&40.R2?.)+40.))(<.$=.(29.VhRP,R15.R30.R2?.R2>.R14.R13.R12.R11.R10.R21.R20.R1?.R1>.R1=.R1<.R1;.R?.R>.R:.R9.R=.R9.(11.&40.=))(?.(10.R16.(11.&40.(25.(22.&40.R30.)-40.))R2?.R2>.R2=.R2<.R2;.R2:.R29.(11.&40.-1.)R28.R27.R26.R25.R24.R23.R22.(11.&40.$14.)(11.&40.$15.)(11.&40.-1.)R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)R?.(11.&40.+40474.)R>.(16.(0.&40.))R<.(17.$=.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until st. intros MR MI PE0 WM0 FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  dpose MR as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
  rceilb; unfold RCTX, RMLOCK, RSSP_GUARD, ram_frame in *.
  (* [comment removed for export] *)
  st1. rewrite bv_eqb_refl. cbv iota. st1. st1. st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRX : rmrep st mX) end.
  { eapply rmrep_transport_high; [exact MR| exact MU| exact WM|]. intros l h [E|[]]; inversion E; subst; rceilb; lia. }
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. unfold ram_ret_post. deexists 15. split; [reflexivity|].
  split.
  { eapply rpres_except_trans; [exact PE0|].
    apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
    cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply ram_fp_stack. lia. }
  split; [eapply wmono_trans; [exact WM0| exact WM]|]. split; [assumption|]. split; [exact ST|]. exact MRX.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00G0?L11601677364.68L17210382573.66L19275818812.70L19420350936.70L19662958168.70L27315737266.68L28046690264.70L28321321048.70L28515593816.70L31120000984.70L33109619485.70L34712365207.73L34712365207.74L36485882968.70L3712931473.72 L37310060433.72L4819329880.70 L52283347613.70L5290001624.70 L5742619051.68 L59192738743.68L66151427842.17L67720908248.7000000>00A00R00S00T00W00X00Y00Z00[00\01D01o02002602G02H02I02J02[02a03:03;S3hRP3RCB1x2XCS1xS3hRP3RCB1x2X02XCSSS1nSSSSSS3hRP3RCB2sp2lo1n2LO4LOLE2HB5Ha_st5Hl_stS3hRP3RCB2sp2lo2st2LO4LOLE2HB5Ha_st5Hl_st1xSS1y2HyS2sp2lo4LOLE1y2HySSSS3hRP3RCB1x2X02XCS1n2NRS1x2r03XAL1q1r1H2H02q02H4S". (* [comment removed for export] *)
#[using="Type"] Lemma ram_mm_ok : ltac2:(CDefT.buildp (gd_tbl_HP_RF_am_G ()) "Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Px1,(0.&40.)Praw,(0.&40.)Ps0o,(0.&40.)Ps1o,(0.&40.)Ps2o,(0.&40.)Ps3o,(0.&40.)Ps4o,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(2.(0.&8.))Pm,P,(0.&40.)(2.(0.&8.))Pjunk,(1>.(0.&8.))Plo,$6.Px,$6.Pn,$6.Pst0,$3.Pst,$3.Prid,$2:.Pr,$2;.P,(4.VhRP,R3.R9.)P,(1?.$=.R:.)P,Pa,$6.P,(21.R7.R:.(22.&40.R2>.)R1.)(21.R7.R;.(22.&40.R2?.)R2.)P,(5.(2.$2;.)(2<.$2:.$2;.(2=.$2:.$2>.$2?.$2;.)(30.$2:.$2>.$2?.$2;.)R5.(31.R6.))(32.$2;.R4.))P,(5.$6.(33.R5.)R:.)P,(5.$6.(34.R;.+1000.)=)P,(35.=R<.)P,(19.(25.R=.+2000.)(28.VhRP,))P,(18.(19.+1.R=.)(35.R=.(13.+2.+3>.)))P,(18.(19.=(1:.(8.R<.)))(35.(1:.(8.R<.))(13.+2.+3>.)))P,(20.(21.R>.R11.(22.&40.R35.))R14.R13.)P,(23.$=.R15.R14.)P,(24.$=.R15.(25.(22.&40.R37.)-40.)(26.VhRP,R14.R19.R1:.R1;.R1<.R1=.R1>.))P,(27.$=.R16.R14.(25.(22.&40.R38.)-40.))P,(19.(28.VhRP,)R15.)P,(19.R16.(12.(22.&40.R3:.)+40.))(<.$=.Lms',$>.(36.P,(0.&40.)(2.(0.&8.))Lm',P,(0.&40.)(2.(0.&8.))(18.(5.$>.R2.(?.(10.R25.(11.&40.(25.(22.&40.R3=.)-40.))R3<.R3;.R3:.R39.R38.(11.&40.+1000.)(11.&40.(25.R18.+1000.))(11.&40.=)(11.&40.(25.(1:.(8.R15.))+1.))(11.&40.(12.R17.+1.))R35.R34.R33.R32.R31.(11.&40.$14.)(11.&40.$15.)(11.&40.-1.)R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.)R1>.(11.&40.+40538.)R1=.(16.(0.&40.))R1.(17.$=.)))(18.(20.(21.R15.R19.(22.&40.R3=.))R1<.R1.)(18.(23.$=.R1<.R1.)(18.(1?.$=.R1.)(18.(24.$=.R1.(25.(22.&40.R3=.)-40.)(26.VhRP,R1:.R1?.R20.R21.R22.R23.R24.))(18.(27.$=.R1.R19.(25.(22.&40.R3=.)-40.))(4.VhRP,(37.R15.R14.R17.)R1.))))))))(?.(10.R23.(11.&40.(25.(22.&40.R3;.)-40.))R3:.R39.R38.R37.R36.(11.&40.+1000.)(11.&40.R15.)(11.&40.R16.)R35.R34.R33.R32.R31.R30.R2?.(11.&40.$14.)(11.&40.$15.)(11.&40.-1.)R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.)R1<.(11.&40.+40474.)R1;.(16.(0.&40.))R19.(17.$=.)))")
(* [comment removed for export] *).
Proof. rceilb.
  intros until r. intros MR MI FP0 Hr RB XAL X0 XC NR SH PE0 WM0 FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  dpose MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  assert (AL : Z.land (x + 4096) 4095 = 0).
  { change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096. clear - XAL X0. Z.div_mod_to_equations. lia. }
  assert (AL' : Z.land 4095 (x + 4096) = 0) by (rewrite Z.land_comm; exact AL).
  change (x mod 4096 = 0) with (pgal x) in XAL.
  rceilb; unfold RCTX, RMLOCK, RSSP_GUARD, ram_frame in *.
  (* [comment removed for export] *)
  st1.
  assert (CF : bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 (-1)) = false)
    by (unfold bv_eqb; rewrite (unsigned_lit x) by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1)%Z; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1.
  replace ((n + -1) * 1) with (n - 1) by lia.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(RCTX + 40, RCTX + 56); (RCTX + 72, RCTX + 80)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
  unfold RCTX in MUc.
  (* [comment removed for export] *)
  st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR2 : rmrep (mm_ok_st st rid n) mX) end.
  { eapply (rmrep_ctx_frameW st _ _ _ _ MR MUc WMc); try reflexivity.
    - intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold ctx_head_cells, RCTX. cbn [ctx mm_ok_st upd_ctx s_ctx set_meta_alloc_shift set_avail_meta_area_count set_avail_meta_areas c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      change (pw (mm_ok_st st rid n) ?q) with (pw st q). unfold pw. cbn [oconc]. change (conc (mm_ok_st st rid n) ?q) with (conc st q).
      rewrite (conc_region' st (rid, 4096) r Hr). cbn [snd]. rewrite RB. unfold wz.
      lazymatch goal with H : rw_cells rsegs ?mX 512968 _ |- _ => exact H end.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[E|[]]]; inversion E; subst; unfold RCTX; lia. }
  clear MUc WMc.
  (* [comment removed for export] *)
  st1. st1. rewrite ?AL, ?AL'. st1. rewrite bv_eqb_refl. cbv iota.
  apply evt_done. eexists. split; [reflexivity|].
  split.
  { eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE0| exact FP0]|].
    apply (rpres_except_of_munch_cov (ram_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
    cbn [ivs_covered]. split; [|split; [|exact I]].
    - intros y Hy. apply ram_fp_stack. lia.
    - intros y Hy. apply ram_fp_ctx. unfold RCTX. lia. }
  split; [first [exact WM0 | eapply wmono_trans; [exact WM0| exact WM]]|]. split; [assumption|]. split; [exact FR|]. split; [exact ST|]. exact MR2.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End RP_1.
