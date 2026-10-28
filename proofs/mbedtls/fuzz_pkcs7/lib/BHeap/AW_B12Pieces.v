(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_exit_lib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_PfLib AW_PfNum AW_PfLib2 AW_PfVsn2 AW_PfShared.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AW_Unwind AW_MmapFixed AW_MmapDie AW_Populate AW_PfEmb.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
#[local] Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | first [tb_light_a a | lia] | first [tb_light_l a | (simpl_sizes; slia)]
                | first [ solve [cbn [inside]; tb_free] | (cbn [inside]; simpl_sizes; slia) ] ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq;
              [ | first [tb_light_a a | lia] | first [tb_light_l a | (simpl_sizes; slia)] ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXAW Require Import LxFlat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P01a4a1fbc7d5d2ed 0 2 0 1 2 1P0e71da1dbaf621e7 0 2 0 1 1 1P0f1940714654f6a2 0 2 0 1 4 1P1c23ae476320cccc 0 2 0 1 5 1P1f9ea0c587b133ef 0 2 0 1 3 1P209d20ef2736c11c 0 2 0 1 3 1P27acd2d8a9a50f5b 0 2 0 1 3 1P2a39f1de72830657 0 2 0 1 4 1P2c13de6d73b57bc3 0 2 0 1 1 1P2d99016b469ae0f3 1 1 9223372036854775808 1 0 1 2 1 1 7 1P32b1303c7016b17a 0 3 0 2 2 1 7 1P338a411bbf7ffd2e 0 3 0 2 1 1 8 1P3cf94cc0a392bba9 0 2 0 1 3 1N05c8bfa786b0f2f8N07d1c4313db035ecN07d4a778e64aa15aN07d84e53a4cb7f71N0ff54fd1a1eab8c2N20adb27d2a493270N31fc778da5cffaccN3305f2ad5fbb06d1"%lxh.
Ltac2 gd_tbl_AW_B12Pieces () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.b12_ro"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Populate.A_EMB"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_PfShared.vsn_call_T"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kEmbBytes"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_PfShared.pf_frames"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_PfNum.pr_range"; "Stdlib.Lists.List.nth_error"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.Some"; "ARUN_1.Pieces.pfirst_facts"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MSsvc"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_PAGESZ_CELL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_MMAP_ECALL"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapDie.md_answered"].

Section ARUN_1. Context {hAR : arun}.

Section Pieces.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma pair_mid : ltac2:(CDefT.buildp (gd_tbl_AW_B12Pieces ()) "Pc,$0.PSP0,$0.Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(2.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(3.(1.&8.))P,(4.(5.+1.R21.)(5.R21.+1?.))P,(6.$7.R2.)(8.$7.VAL,VCS,Lms',$9.(:.(1.&40.)Lw3,(1.&40.)(;.$9.R2.(<.(=.(>.&40.+4<><0.)(>.&40.R24.)R23.R22.R21.R20.R1?.(>.&40.R25.)R1>.(>.&40.+23?;2.)(>.&40.+1000.)(>.&40.R25.)R1.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.)R7.(>.&40.+7===8.)R6.(?.(1.&40.))R5.(10.$7.))))(<.(=.(>.&40.+4<>4<.)(>.&40.R22.)R21.R20.R1?.R1>.R1=.(>.&40.R23.)R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.)R5.(>.&40.+4<>4<.)R4.(?.(1.&40.))R3.(10.$7.)))")
(* [comment removed for export] *).
  Proof.
    intros until m. intros Hc MI.
    pose proof (munch_refl ([] : list ivl) m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    lx_run (PLAN [0x7ddd8] [] 30%N).
    all: subst lxm; apply evtA_done; eexists; lx_mseq.
  Qed.

  (* [comment removed for export] *)
  Lemma b12_ro_tr : ltac2:(CDefT.buildp (gd_tbl_AW_B12Pieces ()) "PW,(11.$12.)Pm,P,(1.&40.)(3.(1.&8.))Pm',P,(1.&40.)(3.(1.&8.))P,(13.R2.)P,(14.R4.R3.R2.)P,PA,$0.Pn,$0.P,(5.+10000.R2.)P,(5.(15.R3.R2.)+65?000.)P,(16.(5.(15.R4.R3.)$17.)(5.(15.$17.+38.)R4.))(18.R:.R5.R4.)(13.R4.)")
(* [comment removed for export] *).
  Proof.
    intros W m m' R MU DJ. unfold b12_ro in *.
    unfold A_TOOLNAME_GOT, A_TOOLNAME, A_REPORT_GOT, A_PRINTF_CB, A_GOT_CFLAGS, A_CF_LOGSYS, A_CFLAGS, A_GOT_PAGESZ, A_PAGESZ_CELL, A_DECORATE, A_MMAP_LIMIT,
      A_GOT_SEALED2, A_DYING, A_INSTANCE, A_EMB in *.
    decompose [and] R. clear R.
    repeat split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ; cbn [cells_size csize Nat.add]; lia]).
  Qed.

  (* [comment removed for export] *)
  Theorem printf_present : ltac2:(CDefT.buildp (gd_tbl_AW_B12Pieces ()) "Pfmt,$0.Plen,$0.PSP0,$0.Plo,$0.Pd,$0.Psz,$0.Px1,(1.&40.)Px2,(1.&40.)Px3,(1.&40.)Px4,(1.&40.)Px5,(1.&40.)Px6,(1.&40.)Px7,(1.&40.)Pra,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(2.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(3.(1.&8.))P,(19.VAL,VCS,R26.R20.R1?.R1>.R1=.R1<.R1;.R1:.R25.)P,(4.(5.+1.R26.)(1:.R26.+18?.))P,(4.(1:.=R28.)(1:.R28.(1;.+2.+2?.)))P,(13.R4.)P,(1<.$7.R5.$17.(1=.$1>.(1?.(>.&40.(15.$17.+20.)))(20.$1>.)))P,(1<.$7.R6.(15.$17.+10.)(1=.$1>.(1?.(>.&40.=))(20.$1>.)))P,(1<.$7.R7.(15.$17.+20.)(1=.$1>.(1?.(>.&40.R28.))(1=.$1>.(1?.(>.&40.$21.))(1=.$1>.(1?.(>.&40.R27.))(20.$1>.)))))P,(22.$7.R8.R29.$21.)P,(23.VCS,R2:.$21.)P,(5.+65?000.R2;.)P,(5.(15.R2<.$21.)R2=.)P,(4.(5.=R2<.)(5.R2<.(15.(24.+3>.+80.)+80.)))P,(25.$7.R=.R2?.R30.)P,(5.+65?000.R30.)P,(5.R31.(26.R32.+450.))P,(5.R33.(1;.+2.+3?.))P,(23.VCS,R33.(26.R34.R33.))P,(6.$7.R12.)(8.$7.VAL,VCS,Lms',$9.(:.(1.&40.)Lt0',(1.&40.)(:.(1.&40.)Lt1',(1.&40.)(:.(1.&40.)Lt2',(1.&40.)(:.(1.&40.)La0',(1.&40.)(:.(1.&40.)La1',(1.&40.)(:.(1.&40.)La2',(1.&40.)(:.(1.&40.)La3',(1.&40.)(:.(1.&40.)La4',(1.&40.)(:.(1.&40.)La5',(1.&40.)(:.(1.&40.)La6',(1.&40.)(:.(1.&40.)La7',(1.&40.)(:.(1.&40.)Lt3',(1.&40.)(:.(1.&40.)Lt4',(1.&40.)(:.(1.&40.)Lt5',(1.&40.)(:.(1.&40.)Lt6',(1.&40.)(:.P,(1.&40.)(3.(1.&8.))Lm',P,(1.&40.)(3.(1.&8.))(4.(;.$9.R11.(<.(=.R3<.(>.&40.R47.)R3;.R3:.R10.R?.R>.R36.R35.R=.R<.R;.R:.R9.R8.R7.R6.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R5.R4.R3.R2.)R26.(27.R3<.)R25.(?.(1.&40.))R1.(10.$7.)))(4.(13.R1.)(4.(1<.$7.R1.$17.(1=.$1>.(1?.(>.&40.(15.$17.+20.)))(20.$1>.)))(4.(1<.$7.R1.(15.$17.+10.)(1=.$1>.(1?.(>.&40.=))(20.$1>.)))(4.(1<.$7.R1.(15.$17.+20.)(1=.$1>.(1?.(>.&40.R45.))(1=.$1>.(1?.(>.&40.$21.))(1=.$1>.(1?.(>.&40.(15.R48.R44.)))(20.$1>.)))))(4.(22.$7.R1.R45.$21.)(4.(25.$7.R1.R46.R47.)(4.(14.(1=.(28.$0.$0.)(29.$0.$0.R46.R47.)(1=.(28.$0.$0.)(29.$0.$0.$17.(15.$17.+38.))(1=.(28.$0.$0.)(29.$0.$0.R45.(15.R45.$21.))(20.(28.$0.$0.)))))R24.R1.)(4.(2:.$7.R24.R1.)(6.$7.R1.))))))))))))))))))))))))))(<.(=.R2;.(>.&40.R36.)R2:.R29.R28.R27.R26.R25.R24.(>.&40.R38.)R32.R31.R30.R2?.R2>.R2=.R2<.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R15.(>.&40.+7===8.)R14.(?.(1.&40.))R13.(10.$7.)))")
(* [comment removed for export] *).
  Proof.
    intros until m. intros VSN HL HF RO EP EMX EV WRB CRD DLO DHI SZB ST LOIMG SPL SPH SCS MI.
    pose proof RO as RO0. unfold b12_ro in RO0. decompose [and] RO0. clear RO0.
    eapply (evtA_cut asegs AL CS).
    { eapply (printf_pre AL IMG ALWF CS CSOK fmt len SP0 lo x1 x2 x3 x4 x5 x6 x7); try eassumption. }
    cbn beta. unfold printf_pre_post. intros ms' (t0p & t1p & t2p & a2p & a3p & a4p & a5p & a6p & a7p & t3p & t4p & bs1 & m1 & -> & PF & OUT & LB & PR & NUL & ST1 & MU1 & WM1 & MI1).
    flat constr:((out_cstr m1 (SP0 + -512) bs1 len OUT ltac:(lia) PR NUL)) 3%nat. intros CSTR NOZ SLEN.
    assert (RO1 : b12_ro m1). { eapply (b12_ro_tr _ m m1 RO MU1). intros A n Ha1 Ha2 Ha3. cbn [disjoint_from]. lia. }
    assert (TR1 : forall A cs, rw_cells asegs m A cs -> A + Z.of_nat (cells_size cs) <= 0x65f000 -> rw_cells asegs m1 A cs).
    { intros A cs Hrc HA. eapply rw_cells_transport; [exact Hrc| exact MU1| exact WM1|]. cbn [disjoint_from]. lia. }
    apply TR1 in EP; [| unfold A_EMB; cbn; lia]. apply TR1 in EMX; [| unfold A_EMB; cbn; lia]. apply TR1 in EV; [| unfold A_EMB; cbn; lia].
    apply (wr_at_transport asegs m m1 d kEmbBytes) in WRB; [| exact WM1].
    eapply (evtA_cut asegs AL CS).
    { eapply (emb_cb_present AL IMG ALWF CS CSOK (firstn (Z.to_nat len) bs1) (SP0 + -512) (SP0 + -640) lo d sz); try eassumption; try rewrite SLEN; try lia.
      all: intros x Hx; apply SCS; lia. }
    cbn beta. unfold emb_cb_post. intros ms' (t0c & t1c & t2c & a0c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m2 & -> & EP2 & EMX2 & EV2 & WRB2 & ST2 & MU2 & WM2 & MI2).
    assert (RO2 : b12_ro m2). { eapply (b12_ro_tr _ m1 m2 RO1 MU2). intros A n Ha1 Ha2 Ha3. unfold A_EMB, kEmbBytes in *. cbn [disjoint_from]. lia. }
    assert (TR2 : forall A cs, rw_cells asegs m1 A cs -> SP0 + -640 <= A -> rw_cells asegs m2 A cs).
    { intros A cs Hrc HA. eapply rw_cells_transport; [exact Hrc| exact MU2| exact WM2|]. unfold A_EMB, kEmbBytes in *. cbn [disjoint_from]. lia. }
    assert (PF2 : pf_frames SP0 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 fmt m2).
    { flat constr:(PF) 12%nat. flclear PF. intros j8 y1 y2 y3 y4 y5 y6 y7 P1 P2 P3 P4. exists j8, y1, y2, y3, y4, y5, y6, y7.
      split; [apply TR2; [exact P1| lia]|]. split; [apply TR2; [exact P2| lia]|]. split; [apply TR2; [exact P3| lia]| apply TR2; [exact P4| lia]]. }
    assert (OUT2 : u8arr asegs m2 (SP0 + -512) bs1).
    { eapply u8arr_transport; [exact OUT| exact MU2| exact WM2|]. unfold A_EMB, kEmbBytes in *. cbn [disjoint_from]. lia. }
    pose proof RO2 as RO2'. unfold b12_ro in RO2'. flat constr:(RO2') 7%nat. flclear RO2'. intros _ _ _ _ GC2 LS2 _.
    ret_lit.
    eapply (evtA_mono asegs AL CS).
    { eapply (printf_post AL IMG ALWF CS CSOK fmt len SP0 lo bs1 ra) with (m0 := m2); try eassumption; try apply munch_refl; try apply wmono_refl. }
    cbn beta. intros ms' (t0q & t1q & t2q & a0q & a1q & a2q & a3q & a4q & a5q & a6q & a7q & t3q & t4q & t5q & t6q & m3 & -> & ST3 & MU3 & WM3 & MI3).
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m3. split; [reflexivity|].
    assert (TR3 : forall A cs, rw_cells asegs m2 A cs -> A + Z.of_nat (cells_size cs) <= 0x65f000 -> rw_cells asegs m3 A cs).
    { intros A cs Hrc HA. eapply rw_cells_transport; [exact Hrc| exact MU3| exact WM3|]. cbn [disjoint_from]. lia. }
    split. { eapply (b12_ro_tr _ m2 m3 RO2 MU3). intros A n Ha1 Ha2 Ha3. cbn [disjoint_from]. lia. }
    split; [apply TR3; [exact EP2| unfold A_EMB; cbn; lia]|]. split; [apply TR3; [exact EMX2| unfold A_EMB; cbn; lia]|].
    split; [rewrite SLEN in EV2; apply TR3; [exact EV2| unfold A_EMB; cbn; lia]|].
    split; [eapply wr_at_transport; [exact WRB2| exact WM3]|].
    split; [exact ST3|].
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1]|]. { unfold sub_fp; cbn [outside]; intros x Hx; lia. }
             eapply munch_trans; [eapply munch_weaken; [| exact MU2]|]. { unfold sub_fp; cbn [outside]; intros x Hx; lia. }
             eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]; intros x Hx; lia. }
    split; [eapply wmono_trans; [exact WM1| eapply wmono_trans; [exact WM2| exact WM3]]| exact MI3].
  Qed.

  (* [comment removed for export] *)
  Definition pfirst_facts (fmt len SP0 lo : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word) (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_B12Pieces ()) "(:.(11.(1.&8.))Lfr,(11.(1.&8.))(:.(11.(1.&8.))Lj8,(11.(1.&8.))(:.(11.(1.&8.))Lbs1,(11.(1.&8.))(4.(1<.$7.O1.(15.(15.O>.-280.)-;0.)(1=.$1>.(2;.#4.R3.)(1=.$1>.(2<.(>.&40.+22.))(1=.$1>.(1?.(>.&40.+10000000000.))(1=.$1>.(1?.(>.&40.+1994:0.))(1=.$1>.(1?.(>.&40.+10000.))(1=.$1>.(1?.(>.&40.+109288.))(1=.$1>.(1?.(>.&40.+6?62<.))(20.$1>.)))))))))(4.(1<.$7.O1.(15.(15.O>.-280.)-80.)(1=.$1>.(1?.(>.&40.+109288.))(1=.$1>.(1?.(>.&40.(15.O>.-200.)))(1=.$1>.(1?.(>.&40.+109280.))(1=.$1>.(1?.(>.&40.+6;:7<.))(20.$1>.))))))(4.(1<.$7.O1.(15.(15.O>.-280.)-60.)(1=.$1>.(2;.#8.R2.)(1=.$1>.(1?.O2.)(1=.$1>.(1?.O3.)(1=.$1>.(1?.O4.)(1=.$1>.(1?.O5.)(1=.$1>.(1?.(>.&40.O?.))(1=.$1>.(1?.O7.)(1=.$1>.(1?.(>.&40.+190.))(1=.$1>.(1?.(>.&40.(15.O>.-200.)))(1=.$1>.(1?.(>.&40.=))(1=.$1>.(1?.(>.&40.O10.))(1=.$1>.(1?.(>.&40.+7>4?4.))(20.$1>.))))))))))))))(4.(1<.$7.O1.$17.(1=.$1>.(1?.(>.&40.(15.$17.+20.)))(20.$1>.)))(4.(1<.$7.O1.(15.$17.+10.)(1=.$1>.(1?.(>.&40.+1000000000000000.))(20.$1>.)))(4.(1<.$7.O1.(15.$17.+20.)(1=.$1>.(1?.(>.&40.=))(1=.$1>.(1?.(>.&40.=))(1=.$1>.(1?.(>.&40.=))(20.$1>.)))))(4.(2=.O>.O<.O;.O:.O9.O8.O7.O6.O5.O4.O3.O2.O10.O1.)(4.(2>.$7.O1.(15.O>.-200.)R1.)(4.(;.$0.(2?.(30.(1.&8.)R1.))+190.)(4.(31.R1.=O?.)(4.(;.(3.(1.&8.))(32.(1.&8.)R1.(33.O?.))(34.(1.&8.)(>.&8.=)))(4.(13.O1.)(4.(25.$7.O1.O=.(15.(15.O>.-280.)-;0.))(6.$7.O1.)))))))))))))))))")
(* [comment removed for export] *).

  Lemma pfirst_facts_tr : ltac2:(CDefT.buildp (gd_tbl_AW_B12Pieces ()) "Pfmt,$0.Plen,$0.PSP0,$0.Plo,$0.Pra,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Pua,$0.Pn,$0.Pm,P,(1.&40.)(3.(1.&8.))Pm',P,(1.&40.)(3.(1.&8.))P,(35.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.R2.)P,(14.(1=.(28.$0.$0.)(29.$0.$0.R5.(15.R5.R4.))(20.(28.$0.$0.)))R3.R2.)P,(2:.$7.R4.R3.)P,(6.$7.R4.)P,(5.+65?000.R8.)P,(5.(15.R9.R8.)R15.)P,(5.+65?000.R16.)P,(5.R17.(26.R18.+450.))(35.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R9.)")
(* [comment removed for export] *).
  Proof.
    intros fmt len SP0 lo ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 ua n m m' (fr & j8 & bs1 & F1 & F2 & F3 & EP & EMX & EV & PF & OUT & LB & PR & NUL & RO & ST & MI) MU WM MI' UA UH LOIMG SPL.
    assert (TRS : forall A cs, rw_cells asegs m A cs -> lo <= A -> rw_cells asegs m' A cs).
    { intros A cs Hrc HA. eapply rw_cells_transport; [exact Hrc| exact MU| exact WM|]. cbn [disjoint_from]. lia. }
    assert (TRI : forall A cs, rw_cells asegs m A cs -> A + Z.of_nat (cells_size cs) <= 0x65f000 -> rw_cells asegs m' A cs).
    { intros A cs Hrc HA. eapply rw_cells_transport; [exact Hrc| exact MU| exact WM|]. cbn [disjoint_from]. lia. }
    exists fr, j8, bs1.
    split; [apply TRS; [exact F1| lia]|]. split; [apply TRS; [exact F2| lia]|]. split; [apply TRS; [exact F3| lia]|].
    split; [apply TRI; [exact EP| unfold A_EMB; cbn; lia]|]. split; [apply TRI; [exact EMX| unfold A_EMB; cbn; lia]|]. split; [apply TRI; [exact EV| unfold A_EMB; cbn; lia]|].
    split. { flat constr:(PF) 12%nat. flclear PF. intros k8 y1 y2 y3 y4 y5 y6 y7 P1 P2 P3 P4. exists k8, y1, y2, y3, y4, y5, y6, y7.
             split; [apply TRS; [exact P1| lia]|]. split; [apply TRS; [exact P2| lia]|]. split; [apply TRS; [exact P3| lia]| apply TRS; [exact P4| lia]]. }
    split. { eapply u8arr_transport; [exact OUT| exact MU| exact WM|]. cbn [disjoint_from]. lia. }
    split; [exact LB|]. split; [exact PR|]. split; [exact NUL|].
    split. { eapply (b12_ro_tr _ m m' RO MU). intros A k Ha1 Ha2 Ha3. cbn [disjoint_from]. lia. }
    split; [| exact MI']. eapply stk_transport_disjoint; [exact ST| exact MU| exact WM|]. cbn [disjoint_from]. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem printf_first_pre : ltac2:(CDefT.buildp (gd_tbl_AW_B12Pieces ()) "Pfmt,$0.Plen,$0.PSP0,$0.Plo,$0.Px1,(1.&40.)Px2,(1.&40.)Px3,(1.&40.)Px4,(1.&40.)Px5,(1.&40.)Px6,(1.&40.)Px7,(1.&40.)Pra,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(2.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(3.(1.&8.))P,(19.VAL,VCS,R24.R20.R1?.R1>.R1=.R1<.R1;.R1:.R23.)P,(4.(5.+1.R24.)(1:.R24.+18?.))P,(4.(1:.=R26.)(1:.R26.(1;.+2.+2?.)))P,(13.R4.)P,(1<.$7.R5.$17.(1=.$1>.(1?.(>.&40.=))(20.$1>.)))P,(1<.$7.R6.(15.$17.+10.)(1=.$1>.(1?.(>.&40.=))(20.$1>.)))P,(1<.$7.R7.(15.$17.+20.)(1=.$1>.(1?.(>.&40.=))(1=.$1>.(1?.(>.&40.=))(1=.$1>.(1?.(>.&40.=))(20.$1>.)))))P,(25.$7.R8.R28.R29.)P,(5.+65?000.R29.)P,(5.R2:.(26.R2;.+450.))P,(5.R2<.(1;.+2.+3?.))P,(23.VCS,R2<.(26.R2=.R2<.))P,(6.$7.R=.)(8.$7.VAL,VCS,Lms',$9.(:.(1.&40.)Lt0',(1.&40.)(:.(1.&40.)Lt1',(1.&40.)(:.(1.&40.)Lt2',(1.&40.)(:.(1.&40.)Lt3',(1.&40.)(:.(1.&40.)Lt4',(1.&40.)(:.(1.&40.)Lt5',(1.&40.)(:.(1.&40.)Lt6',(1.&40.)(:.(1.&40.)La6',(1.&40.)(:.P,(1.&40.)(3.(1.&8.))Lmm,P,(1.&40.)(3.(1.&8.))(4.(;.$9.R:.(36.(=.(>.&40.+7<9;8.)(>.&40.(15.(15.R39.-280.)-;0.))R2?.R2>.R9.R8.R7.(>.&40.+1.)(>.&40.+221:5.)(>.&40.=)(>.&40.(24.(37.(15.+10000.+???.)+1000.)+1000.))(>.&40.+3.)(>.&40.+22.)(>.&40.-1.)(>.&40.=)R2.(>.&40.+=>.)(>.&40.(24.(37.(15.+10000.+???.)+1000.)+1000.))(>.&40.$38.)(>.&40.+109268.)(>.&40.+2000000000000000.)(>.&40.+109278.)(>.&40.+1000000000000000.)(>.&40.+10000000000?????.)(>.&40.+=???????????????.)R20.R1?.R6.R5.R4.R3.)R1:.(>.&40.$39.)(>.&40.+=>.)R19.(?.(1.&40.))R1.(10.$7.)))(4.(35.R3;.R3:.R39.R38.R30.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R1.)(4.(14.(1=.(28.$0.$0.)(29.$0.$0.R38.R39.)(1=.(28.$0.$0.)(29.$0.$0.$17.(15.$17.+38.))(20.(28.$0.$0.))))R18.R1.)(2:.$7.R18.R1.)))))))))))))(<.(=.R26.(>.&40.R2?.)R25.R24.R23.R22.R21.R20.R1?.(>.&40.R31.)R2=.R2<.R2;.R2:.R29.R28.R27.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.)R10.(>.&40.+7===8.)R?.(?.(1.&40.))R>.(10.$7.)))")
(* [comment removed for export] *).
  Proof.
    intros until m. intros VSN HL HF RO EP EMX EV ST LOIMG SPL SPH SCS MI.
    pose proof RO as RO0. unfold b12_ro in RO0. flat constr:(RO0) 5%nat. flclear RO0. intros _ _ RGOT RCB _.
    eapply (evtA_cut asegs AL CS).
    { eapply (printf_pre AL IMG ALWF CS CSOK fmt len SP0 lo x1 x2 x3 x4 x5 x6 x7); try eassumption. }
    cbn beta. unfold printf_pre_post. intros ms' (t0p & t1p & t2p & a2p & a3p & a4p & a5p & a6p & a7p & t3p & t4p & bs1 & m1 & -> & PF & OUT & LB & PR & NUL & ST1 & MU1 & WM1 & MI1).
    assert (RO1 : b12_ro m1). { eapply (b12_ro_tr _ m m1 RO MU1). intros A n Ha1 Ha2 Ha3. cbn [disjoint_from]. lia. }
    assert (TR1 : forall A cs, rw_cells asegs m A cs -> A + Z.of_nat (cells_size cs) <= 0x65f000 -> rw_cells asegs m1 A cs).
    { intros A cs Hrc HA. eapply rw_cells_transport; [exact Hrc| exact MU1| exact WM1|]. cbn [disjoint_from]. lia. }
    apply TR1 in EP; [| unfold A_EMB; cbn; lia]. apply TR1 in EMX; [| unfold A_EMB; cbn; lia]. apply TR1 in EV; [| unfold A_EMB; cbn; lia].
    pose proof RO1 as RO1'. unfold b12_ro in RO1'. flat constr:(RO1') 10%nat. flclear RO1'. intros _ _ _ _ GC1 _ GP1 PC1 DE1 _.
    eapply (evtA_mono asegs AL CS).
    { eapply (emb_cb_first_pre AL IMG ALWF CS CSOK (SP0 + -512) (SP0 + -640) lo); try eassumption; try lia.
      intros x Hx. apply SCS. lia. }
    cbn beta. unfold emb_first_svc_post. intros ms' (t0c & t1c & t2c & t3c & t4c & t5c & t6c & a6c & mm & fr & j8 & -> & MU2 & WM2 & MI2 & F1 & F2 & F3 & EP2 & EMX2 & EV2 & ST2).
    assert (TR2 : forall A cs, rw_cells asegs m1 A cs -> SP0 + -640 <= A -> rw_cells asegs mm A cs).
    { intros A cs Hrc HA. eapply rw_cells_transport; [exact Hrc| exact MU2| exact WM2|]. unfold A_EMB in *. cbn [disjoint_from]. lia. }
    eexists t0c, t1c, t2c, t3c, t4c, t5c, t6c, a6c, mm. split; [reflexivity|].
    split.
    { exists fr, j8, bs1. split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact EP2|]. split; [exact EMX2|]. split; [exact EV2|].
      split. { flat constr:(PF) 12%nat. flclear PF. intros k8 y1 y2 y3 y4 y5 y6 y7 P1 P2 P3 P4. exists k8, y1, y2, y3, y4, y5, y6, y7.
               split; [apply TR2; [exact P1| lia]|]. split; [apply TR2; [exact P2| lia]|]. split; [apply TR2; [exact P3| lia]| apply TR2; [exact P4| lia]]. }
      split. { eapply u8arr_transport; [exact OUT| exact MU2| exact WM2|]. unfold A_EMB in *. cbn [disjoint_from]. lia. }
      split; [exact LB|]. split; [exact PR|]. split; [exact NUL|].
      split. { eapply (b12_ro_tr _ m1 mm RO1 MU2). intros A n Ha1 Ha2 Ha3. unfold A_EMB in *. cbn [disjoint_from]. lia. }
      split; [exact ST2| exact MI2]. }
    split. { eapply munch_trans; [eapply munch_weaken; [| exact MU1]|]. { unfold sub_fp; cbn [outside]; intros x Hx; lia. }
             eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros x Hx; lia. }
    eapply wmono_trans; [exact WM1| exact WM2].
  Qed.

  (* [comment removed for export] *)
  Theorem printf_first_post : ltac2:(CDefT.buildp (gd_tbl_AW_B12Pieces ()) "Pfmt,$0.Plen,$0.PSP0,$0.Plo,$0.Pa,(1.&40.)Pra,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)Pa6,(1.&40.)PF,(2.&5.(1.&40.))Pfc,(1.&20.)Pm0,P,(1.&40.)(3.(1.&8.))Pmm,P,(1.&40.)(3.(1.&8.))P,(35.R20.R1?.R1>.R1=.R1;.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R1.)P,(4.(5.+1.R20.)(1:.R20.+18?.))P,(5.+65?000.(3:.&40.R1>.))P,(5.(15.(3:.&40.R1?.)$21.)(3;.VhAR,))P,(5.(15.(3:.&40.R20.)$21.)R21.)P,(22.$7.R6.(3:.&40.R21.)$21.)P,(23.VCS,(3:.&40.R22.)$21.)P,(5.+65?000.R24.)P,(5.R25.(26.R26.+450.))P,(5.R27.(1;.+2.+3?.))P,(23.VCS,R27.(26.R28.R27.))P,(14.(1=.(28.$0.$0.)(29.$0.$0.R28.R29.)(1=.(28.$0.$0.)(29.$0.$0.$17.(15.$17.+38.))(1=.(28.$0.$0.)(29.$0.$0.(3:.&40.R27.)(15.(3:.&40.R27.)$21.))(20.(28.$0.$0.)))))R=.R<.)P,(2:.$7.R>.R=.)(8.$7.VAL,VCS,Lms',$9.(:.(1.&40.)Lt0',(1.&40.)(:.(1.&40.)Lt1',(1.&40.)(:.(1.&40.)Lt2',(1.&40.)(:.(1.&40.)La0',(1.&40.)(:.(1.&40.)La1',(1.&40.)(:.(1.&40.)La2',(1.&40.)(:.(1.&40.)La3',(1.&40.)(:.(1.&40.)La4',(1.&40.)(:.(1.&40.)La5',(1.&40.)(:.(1.&40.)La6',(1.&40.)(:.(1.&40.)La7',(1.&40.)(:.(1.&40.)Lt3',(1.&40.)(:.(1.&40.)Lt4',(1.&40.)(:.(1.&40.)Lt5',(1.&40.)(:.(1.&40.)Lt6',(1.&40.)(:.P,(1.&40.)(3.(1.&8.))Lm',P,(1.&40.)(3.(1.&8.))(4.(;.$9.R11.(<.(=.R39.(>.&40.R3<.)R38.R37.R10.R?.R>.R33.R32.R=.R<.R;.R:.R9.R8.R7.R6.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R5.R4.R3.R2.)R22.(27.R39.)R21.(?.(1.&40.))R1.(10.$7.)))(4.(13.R1.)(4.(1<.$7.R1.$17.(1=.$1>.(1?.(>.&40.(15.$17.+20.)))(20.$1>.)))(4.(1<.$7.R1.(15.$17.+10.)(1=.$1>.(1?.(>.&40.=))(20.$1>.)))(4.(1<.$7.R1.(15.$17.+20.)(1=.$1>.(1?.(>.&40.(3:.&40.R3:.)))(1=.$1>.(1?.(>.&40.$21.))(1=.$1>.(1?.(>.&40.R3=.))(20.$1>.)))))(4.(22.$7.R1.(3:.&40.R3:.)$21.)(4.(25.$7.R1.R3;.R3<.)(4.(14.(1=.(28.$0.$0.)(29.$0.$0.R3;.R3<.)(1=.(28.$0.$0.)(29.$0.$0.$17.(15.$17.+38.))(1=.(28.$0.$0.)(29.$0.$0.(3:.&40.R3:.)(15.(3:.&40.R3:.)$21.))(20.(28.$0.$0.)))))R20.R1.)(4.(2:.$7.R20.R1.)(6.$7.R1.))))))))))))))))))))))))))(3<.R29.(15.(15.R2;.-280.)-80.)R27.R26.R25.R24.R23.(>.&40.+109268.)(>.&40.+2000000000000000.)(>.&40.+109278.)(>.&40.+1000000000000000.)(>.&40.+10000000000?????.)(>.&40.+=???????????????.)R18.R17.R16.R15.R14.R13.R12.R11.R10.+10000.+221:5.+1.R>.))")
(* [comment removed for export] *).
  Proof.
    intros until mm. intros (fr & j8 & bs1 & F1 & F2 & F3 & EP & EMX & EV & PF & OUT & LB & PR & NUL & RO & ST & MI) HL ALO ACE AHI WRB CRD LOIMG SPL SPH SCS MU WM.
    set (ua := bv_unsigned a) in *.
    flat constr:((out_cstr mm (SP0 + -512) bs1 len OUT ltac:(lia) PR NUL)) 3%nat. intros CSTR NOZ SLEN.
    pose proof RO as RO0. unfold b12_ro in RO0. flat constr:(RO0) 11%nat. flclear RO0. intros _ _ _ _ GC0 _ _ _ _ LIM0 _.
    eapply (evtA_cut asegs AL CS).
    { eapply (emb_cb_first_post_ok AL IMG ALWF CS CSOK (firstn (Z.to_nat len) bs1) (SP0 + -512) (SP0 + -640) lo a fr j8 (Z_to_bv 64 0x7e4f4)) with (m0 := mm);
        fold ua; try eassumption; try rewrite SLEN; try lia; try apply munch_refl; try apply wmono_refl.
      - intros x Hx. apply SCS. lia.
      - intros x Hx. apply SCS. lia. }
    cbn beta. unfold emb_cb_post. fold ua. intros ms' (t0c & t1c & t2c & a0c & a1c & a2c & a3c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & m2 & -> & EP2 & EMX2 & EV2 & WRB2 & ST2 & MU2 & WM2 & MI2).
    assert (RO2 : b12_ro m2). { eapply (b12_ro_tr _ mm m2 RO MU2). intros A n Ha1 Ha2 Ha3. unfold A_EMB, kEmbBytes in *. cbn [disjoint_from]. lia. }
    assert (TR2 : forall A cs, rw_cells asegs mm A cs -> SP0 + -640 <= A -> rw_cells asegs m2 A cs).
    { intros A cs Hrc HA. eapply rw_cells_transport; [exact Hrc| exact MU2| exact WM2|]. unfold A_EMB, kEmbBytes in *. cbn [disjoint_from]. lia. }
    assert (PF2 : pf_frames SP0 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 fmt m2).
    { flat constr:(PF) 12%nat. flclear PF. intros k8 y1 y2 y3 y4 y5 y6 y7 P1 P2 P3 P4. exists k8, y1, y2, y3, y4, y5, y6, y7.
      split; [apply TR2; [exact P1| lia]|]. split; [apply TR2; [exact P2| lia]|]. split; [apply TR2; [exact P3| lia]| apply TR2; [exact P4| lia]]. }
    assert (OUT2 : u8arr asegs m2 (SP0 + -512) bs1).
    { eapply u8arr_transport; [exact OUT| exact MU2| exact WM2|]. unfold A_EMB, kEmbBytes in *. cbn [disjoint_from]. lia. }
    pose proof RO2 as RO2'. unfold b12_ro in RO2'. flat constr:(RO2') 7%nat. flclear RO2'. intros _ _ _ _ GC2 LS2 _.
    ret_lit.
    eapply (evtA_mono asegs AL CS).
    { eapply (printf_post AL IMG ALWF CS CSOK fmt len SP0 lo bs1 ra) with (m0 := m2); try eassumption; try apply munch_refl; try apply wmono_refl. }
    cbn beta. intros ms' (t0q & t1q & t2q & a0q & a1q & a2q & a3q & a4q & a5q & a6q & a7q & t3q & t4q & t5q & t6q & m3 & -> & ST3 & MU3 & WM3 & MI3).
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, m3. split; [reflexivity|].
    assert (TR3 : forall A cs, rw_cells asegs m2 A cs -> A + Z.of_nat (cells_size cs) <= 0x65f000 -> rw_cells asegs m3 A cs).
    { intros A cs Hrc HA. eapply rw_cells_transport; [exact Hrc| exact MU3| exact WM3|]. cbn [disjoint_from]. lia. }
    split. { eapply (b12_ro_tr _ m2 m3 RO2 MU3). intros A n Ha1 Ha2 Ha3. cbn [disjoint_from]. lia. }
    split; [apply TR3; [exact EP2| unfold A_EMB; cbn; lia]|]. split; [apply TR3; [exact EMX2| unfold A_EMB; cbn; lia]|].
    split; [rewrite SLEN, Z.add_0_r in EV2; apply TR3; [exact EV2| unfold A_EMB; cbn; lia]|].
    split; [eapply wr_at_transport; [exact WRB2| exact WM3]|].
    split; [exact ST3|].
    split. { eapply munch_trans; [exact MU|].
             eapply munch_trans; [eapply munch_weaken; [| exact MU2]|]. { unfold sub_fp; cbn [outside]; intros x Hx; lia. }
             eapply munch_weaken; [| exact MU3]. unfold sub_fp; cbn [outside]; intros x Hx; lia. }
    split; [eapply wmono_trans; [exact WM| eapply wmono_trans; [exact WM2| exact WM3]]| exact MI3].
  Qed.
End Pieces.
End ARUN_1.
