(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import ZBridge Mem Arr Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_lib A_amem_lib A_icpt_str.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance Lib.PropExec.fx0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
Ltac2 gd_tbl_AW_PfLib () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.not"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.or"; "Walk.imcpy_post"].


Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Theorem istrlen_spec : ltac2:(CDefT.buildp (gd_tbl_AW_PfLib ()) "Ps,(0.(1.&8.))PP,$2.Pra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(3.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(4.(1.&8.))P,(5.$6.R1.R23.(7.(1.&8.)R24.(8.(1.&8.)(9.&8.=)(:.(1.&8.)))))P,(;.(<.(1.&8.)(9.&8.=)R25.))P,(=.VCS,R25.(>.(?.(10.(1.&8.)R26.))+1.))P,(11.=R26.)P,(11.(>.(>.R27.(?.(10.(1.&8.)R28.)))+1.)(12.+2.+3?.))P,(13.(1.&40.)R1>.(9.&40.R28.))(14.$6.VAL,VCS,Lms',$15.(16.(1.&40.)La1',(1.&40.)(16.(1.&40.)La2',(1.&40.)(13.$15.R3.(17.(18.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.(9.&40.(?.(10.(1.&8.)R2=.)))R2.R1.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.)R<.(19.R2;.)R;.(1:.(1.&40.))R:.(1;.$6.)))))(17.(18.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.R<.R;.R:.)R9.(9.&40.+7:;:<.)R8.(1:.(1.&40.))R7.(1;.$6.)))")
(* [comment removed for export] *).
  Proof.
    intros until m. intros BY NZ CR P0 PH ->. al_facts.
    zstep.
    eapply (evtA_cut asegs AL CS).
    { eapply (istrlen_loop AL IMG ALWF CS CSOK (length s) 0 s P); try eassumption; try reflexivity; lia. }
    cbn beta. intros ms' ->. zstep. zstep. apply evtA_done.
    eexists _, _. replace (Z.of_nat (length s) + 1 + -1) with (Z.of_nat (length s)) by lia. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Definition imcpy_post (ra sp gp tp t0 t1 t2 s0 s1 a0 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word)
      (PC : word) (fc : bv 32) (D S n : Z) (ss : list byte) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_PfLib ()) "Lms',$15.(16.(1.&40.)La4',(1.&40.)(16.P,(1.&40.)(4.(1.&8.))Lm',P,(1.&40.)(4.(1.&8.))(1<.(13.$15.R3.(17.(18.O23.O22.O21.O20.O1?.O1>.O1=.O1<.O1;.O1:.(9.&40.(>.O4.O3.))(9.&40.(>.O5.O3.))(9.&40.(>.O5.O3.))R2.O19.O18.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.)O8.O7.O6.(1:.(1.&40.))R1.(1;.$6.)))(1<.(1=.(8.(1>.$2.$2.)(1?.$2.$2.O5.(>.O5.O3.))(:.(1>.$2.$2.)))O1.R1.)(1<.(20.$6.O1.R1.)(1<.(21.$6.R1.)(1<.(5.$6.R1.O4.O2.)(22.$6.R1.O5.O3.))))))))")
(* [comment removed for export] *).

  #[using="IMG ALWF CSOK"] Lemma imcpy_loop : ltac2:(CDefT.buildp (gd_tbl_AW_PfLib ()) "Pk,$23.Pi,$2.Pn,$2.PD,$2.PS,$2.Pcs,$2.Pcd,$2.Pss,(0.(1.&8.))Pra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(3.&5.(1.&40.))Pfc,(1.&20.)Pm0,P,(1.&40.)(4.(1.&8.))Pm,P,(1.&40.)(4.(1.&8.))P,(13.$2.R23.(>.R24.R27.))P,(13.$2.R23.(>.R26.R28.))P,(13.$2.R29.(24.R28.(?.R2:.)))P,(1<.(25.=R2:.)(11.R2:.R29.))P,(13.$2.(?.(10.(1.&8.)R25.))R2:.)P,(5.$6.R6.R29.R26.)P,(22.$6.R7.R2;.R2<.)P,(=.VCS,R2<.R2=.)P,(=.VCS,R2<.R2>.)P,(26.(25.(>.R2>.R2?.)R2=.)(25.(>.R2=.R2?.)R2>.))P,(11.=R2?.)P,(11.(>.R30.R31.)(12.+2.+3?.))P,(11.=R30.)P,(11.(>.R31.R33.)(12.+2.+3?.))P,(1=.(8.(1>.$2.$2.)(1?.$2.$2.R33.(>.R33.R34.))(:.(1>.$2.$2.)))R10.R?.)P,(20.$6.R11.R10.)P,(21.$6.R11.)(14.$6.VAL,VCS,(27.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.(9.&40.+7:9?<.)R14.R36.R35.R37.R32.R13.)(17.(18.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.(9.&40.R34.)(9.&40.(>.R36.R37.))(9.&40.R33.)R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R15.(9.&40.+7:9>8.)R14.(1:.(1.&40.))R12.(1;.$6.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until m; intros -> -> Hi Hin LEN BY WR CRD CRS SEP D0 DH S0 SH MU WM MI; [lia|]. al_facts.
    assert (SOK : store_ok asegs m (Z_to_bv 64 (D + i)) 1 = true).
    { change (Z_to_bv 64 (D + i)) with (wa (D + i)). apply (wr_at_store_ok asegs m D n i 1 WR); [lia| cbn; lia]. }
    pose proof (bytes_at_rdn asegs m S _ (Z.to_nat i) 1 BY ltac:(lia)) as RD. rewrite Z2Nat.id in RD by lia.
    destruct (skipn (Z.to_nat i) ss) as [|b rest] eqn:SK.
    { exfalso. apply (f_equal (@length byte)) in SK. rewrite length_skipn in SK. cbn in SK. lia. }
    cbn [firstn] in RD. unfold wa in RD. rewrite <- ov_rdn in RD.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep.
    change (le1 (Z_to_bv 64 (bv_unsigned b))) with (le1 (zxb b)). rewrite le1_zxb.
    set (m1 := write_to_mem m (wa (D + i)) [b]) in *. change (write_to_mem m (Z_to_bv 64 (D + i)) [b]) with m1.
    assert (MU1 : munch [(D, D + n)] m0 m1).
    { subst m1. eapply munch_trans; [exact MU|]. apply munch_write; [apply munch_refl | lia | cbn; lia | cbn; left; lia]. }
    assert (WM1 : wmono asegs m0 m1) by (subst m1; eapply wmono_trans; [exact WM | apply wmono_write; apply wmono_refl]).
    assert (MI1 : mem_inv asegs m1) by (subst m1; apply mem_inv_store; [exact MI | exact SOK]).
    assert (BY1 : bytes_at asegs m1 S ss) by (subst m1; apply bytes_at_write_other; [exact BY| lia| cbn; lia| cbn [length]; lia]).
    assert (WR1 : wr_at asegs m1 D n) by (subst m1; apply wr_at_write; exact WR).
    destruct (Z.eq_dec (i + 1) n) as [EQ|NE].
    - if_falseU. apply evtA_done. dexists (Z_to_bv 64 (bv_unsigned b)), m1.
      split; [replace (S + i + 1) with (S + n) by lia; replace (D + i + 1) with (D + n) by lia; reflexivity|].
      split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact BY1| exact WR1].
    - if_trueU. eapply (IH (i + 1) n D S (S + i + 1) (D + i + 1) ss); try eassumption; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Theorem imcpy_spec : ltac2:(CDefT.buildp (gd_tbl_AW_PfLib ()) "Pn,$2.PD,$2.PS,$2.Pss,(0.(1.&8.))Pra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(3.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(4.(1.&8.))P,(25.=R26.)P,(13.$2.(?.(10.(1.&8.)R24.))R27.)P,(5.$6.R3.R26.R25.)P,(22.$6.R4.R28.R29.)P,(=.VCS,R29.R2:.)P,(=.VCS,R29.R2;.)P,(26.(25.(>.R2;.R2<.)R2:.)(25.(>.R2:.R2<.)R2;.))P,(11.=R2<.)P,(11.(>.R2=.R2>.)(12.+2.+3?.))P,(11.=R2=.)P,(11.(>.R2>.R30.)(12.+2.+3?.))P,(21.$6.R<.)P,(13.(1.&40.)R25.(9.&40.R31.))P,(13.(1.&40.)R25.(9.&40.R31.))P,(13.(1.&40.)R25.(9.&40.R34.))(14.$6.VAL,VCS,Lms',$15.(16.(1.&40.)La1',(1.&40.)(16.(1.&40.)La2',(1.&40.)(16.(1.&40.)La3',(1.&40.)(16.(1.&40.)La4',(1.&40.)(16.P,(1.&40.)(4.(1.&8.))Lm',P,(1.&40.)(4.(1.&8.))(1<.(13.$15.R6.(17.(18.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R5.R4.R3.R2.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R18.(19.R37.)R17.(1:.(1.&40.))R1.(1;.$6.)))(1<.(1=.(8.(1>.$2.$2.)(1?.$2.$2.R3:.(>.R3:.R3;.))(:.(1>.$2.$2.)))R16.R1.)(1<.(20.$6.R16.R1.)(1<.(21.$6.R1.)(1<.(5.$6.R1.R39.R38.)(22.$6.R1.R3:.R3;.)))))))))))(17.(18.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R12.(9.&40.+7:9=<.)R11.(1:.(1.&40.))R10.(1;.$6.)))")
(* [comment removed for export] *).
  Proof.
    intros until m. intros N0 LEN BY WR CRD CRS SEP D0 DH S0 SH MI -> -> ->. al_facts.
    zstep. destruct (Z.eq_dec n 0) as [->|NZ].
    - if_trueU. zstep. apply evtA_done. eexists _, _, _, _, m. split; [reflexivity|].
      split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact MI|]. split; [exact BY| exact WR].
    - if_falseU. zstep. zstep.
      eapply (evtA_cut asegs AL CS).
      { eapply (imcpy_loop (Z.to_nat n) 0 n D S S D ss); try eassumption; try lia; [apply munch_refl| apply wmono_refl]. }
      cbn beta. (intros ms' dd_H; ddestruct dd_H as (a4' & m' & -> & MU' & WM' & MI' & BY' & WR')). zstep. apply evtA_done.
      eexists _, _, _, _, m'. split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact BY'| exact WR'].
  Qed.
End Walk.
