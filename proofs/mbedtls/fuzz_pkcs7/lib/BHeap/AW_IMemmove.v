(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import ZBridge Mem Arr Frame Image.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import SeqExec EnframeArith.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT ARestrict A_exit_lib A_amem_lib A_imsetv A_vsnp_num A_icpt_str.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_PfLib AW_PfNum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AEvtA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance Lib.PropExec.fx0.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
Ltac2 gd_tbl_AW_IMemmove () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.lt"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "Stdlib.Lists.List.nth_error"; "Corelib.Init.Datatypes.Some"; "Corelib.Lists.ListDef.skipn"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.S"; "Corelib.Lists.ListDef.firstn"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.nil"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"].


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

  #[using="Type"] Lemma nth_skipn_cons : ltac2:(CDefT.buildp (gd_tbl_AW_IMemmove ()) "Pss,(0.(1.&8.))Pi,$2.P,(3.R1.(4.(1.&8.)R2.))(5.(1.&8.)Lb,(1.&8.)(6.(7.(8.(1.&8.))(9.(1.&8.)R4.R3.)(:.(1.&8.)R1.))(6.(7.(0.(1.&8.))(;.(1.&8.)R3.R4.)(<.(1.&8.)R1.(;.(1.&8.)(=.R3.)R4.)))(7.(0.(1.&8.))(>.(1.&8.)(=.R3.)R4.)(?.(1.&8.)(>.(1.&8.)R3.R4.)(<.(1.&8.)R1.(10.(1.&8.))))))))")
(* [comment removed for export] *).
  Proof.
    intros ss i Hi. destruct (nth_error ss i) as [b|] eqn:E; [| apply nth_error_None in E; lia]. exists b. split; [reflexivity|].
    destruct (nth_error_split _ _ _ E) as (pre & post & -> & Hl). subst i.
    split.
    - rewrite skipn_app, skipn_all, Nat.sub_diag. cbn [skipn app]. replace (S (length pre)) with (length pre + 1)%nat by lia.
      rewrite skipn_app, skipn_all2 by lia. replace (length pre + 1 - length pre)%nat with 1%nat by lia. reflexivity.
    - replace (S (length pre)) with (length pre + 1)%nat by lia. rewrite !firstn_app, firstn_all2 by lia.
      rewrite firstn_all. replace (length pre + 1 - length pre)%nat with 1%nat by lia. rewrite Nat.sub_diag. cbn [firstn]. rewrite app_nil_r. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma immv_floop : ltac2:(CDefT.buildp (gd_tbl_AW_IMemmove ()) "Pk,$2.Pi,$11.Pn,$11.PD,$11.PS,$11.Pss,(0.(1.&8.))Pra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(12.&5.(1.&40.))Pfc,(1.&20.)Pm0,P,(1.&40.)(8.(1.&8.))Pm,P,(1.&40.)(8.(1.&8.))P,(7.$11.R25.(13.R24.(14.R26.)))P,(6.(15.=R26.)(16.R26.R25.))P,(7.$11.(14.(4.(1.&8.)R23.))R26.)P,(16.R26.R25.)P,(17.$18.R5.R27.(>.(1.&8.)(19.R29.)R25.))P,(17.$18.R6.(1:.R27.R2:.)(;.(1.&8.)(19.R2:.)R26.))P,(1;.$18.R7.R29.R2:.)P,(1<.VCS,R2:.R2;.)P,(1<.VCS,R2:.R2<.)P,(16.=R2<.)P,(16.(1:.R2<.R2>.)(1=.+2.+3?.))P,(1>.(<.(1?.$11.$11.)(20.$11.$11.R2>.(1:.R2>.R2?.))(10.(1?.$11.$11.)))R=.R<.)P,(21.$18.R>.R=.)P,(22.$18.R>.)(23.$18.VAL,VCS,Lms',$24.(5.(1.&40.)La4',(1.&40.)(5.P,(1.&40.)(8.(1.&8.))Lm',P,(1.&40.)(8.(1.&8.))(6.(7.$24.R3.(25.(26.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.(27.&40.(1:.R33.R35.))(27.&40.(1:.R34.R35.))(27.&40.(1:.R34.R35.))R2.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R15.(27.&40.+7::24.)R14.(28.(1.&40.))R1.(29.$18.)))(6.(1>.(<.(1?.$11.$11.)(20.$11.$11.R34.(1:.R34.R35.))(10.(1?.$11.$11.)))R13.R1.)(6.(21.$18.R13.R1.)(6.(22.$18.R1.)(6.(17.$18.R1.R34.R32.)(1;.$18.R1.R34.R35.))))))))(25.(26.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.(27.&40.(1:.R30.R33.))(27.&40.(1:.R31.R32.))(27.&40.(1:.R31.R33.))R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R12.(27.&40.+7::10.)R11.(28.(1.&40.))R?.(29.$18.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until m; intros Hi Hin LEN DS BD BS WR CRD CRS D0 SH MU WM MI; [lia|]. al_facts.
    ddestruct (nth_skipn_cons ss (Z.to_nat i) ltac:(lia)) as (b & NB & SK & FS).
    assert (SOK : store_ok asegs m (Z_to_bv 64 (D + i)) 1 = true).
    { change (Z_to_bv 64 (D + i)) with (wa (D + i)). apply (wr_at_store_ok asegs m D n i 1 WR); [lia| cbn; lia]. }
    pose proof (bytes_at_rdn asegs m (S + i) _ 0 1 BS ltac:(rewrite SK; cbn; lia)) as RD. rewrite SK in RD. cbn [skipn firstn Z.of_nat] in RD.
    rewrite Z.add_0_r in RD. unfold wa in RD. rewrite <- ov_rdn in RD.
    zstep. zstep. zstep. zstep. zstep.
    change (le1 (Z_to_bv 64 (bv_unsigned b))) with (le1 (zxb b)). rewrite le1_zxb.
    set (m1 := write_to_mem m (wa (D + i)) [b]) in *. change (write_to_mem m (Z_to_bv 64 (D + i)) [b]) with m1.
    assert (MU1 : munch [(D, D + n)] m0 m1).
    { subst m1. apply munch_write; [exact MU | lia | cbn; lia | cbn; left; lia]. }
    assert (WM1 : wmono asegs m0 m1) by (subst m1; apply wmono_write; exact WM).
    assert (MI1 : mem_inv asegs m1) by (subst m1; apply mem_inv_store; [exact MI | exact SOK]).
    assert (WR1 : wr_at asegs m1 D n) by (subst m1; apply wr_at_write; exact WR).
    assert (LF : length (firstn (Z.to_nat i) ss) = Z.to_nat i) by (rewrite length_firstn; lia).
    assert (BD1 : bytes_at asegs m1 D (firstn (Z.to_nat (i + 1)) ss)).
    { replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat i)) by lia. rewrite FS. apply bytes_at_app. split.
      - subst m1. apply bytes_at_write_other; [exact BD| lia| cbn; lia| rewrite LF; cbn [length]; lia].
      - rewrite LF. replace (D + Z.of_nat (Z.to_nat i)) with (D + i) by lia. subst m1. apply bytes_at_write_same; cbn [length]; lia. }
    assert (BS1 : bytes_at asegs m1 (S + (i + 1)) (skipn (Z.to_nat (i + 1)) ss)).
    { replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat i)) by lia. rewrite SK in BS. change (b :: skipn (Datatypes.S (Z.to_nat i)) ss) with ([b] ++ skipn (Datatypes.S (Z.to_nat i)) ss) in BS.
      apply bytes_at_app in BS. destruct BS as [_ BS]. cbn [length] in BS. replace (S + i + Z.of_nat 1) with (S + (i + 1)) in BS by lia.
      subst m1. apply bytes_at_write_other; [exact BS| lia| cbn; lia| cbn [length]; lia]. }
    clearbody m1. clear SOK RD.
    destruct (Z.eq_dec (i + 1) n) as [EQ|NE].
    - if_falseU. apply evtA_done. dexists (Z_to_bv 64 (bv_unsigned b)), m1.
      split; [replace (S + i + 1) with (S + n) by lia; replace (D + i + 1) with (D + n) by lia; reflexivity|].
      split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [| exact WR1].
      replace (Z.to_nat (i + 1)) with (length ss) in BD1 by lia. rewrite firstn_all in BD1. exact BD1.
    - if_trueU. replace (S + i + 1) with (S + (i + 1)) by lia. replace (D + i + 1) with (D + (i + 1)) by lia.
      eapply (IH (i + 1) n D S ss); try eassumption; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma immv_bloop : ltac2:(CDefT.buildp (gd_tbl_AW_IMemmove ()) "Pk,$2.Pi,$11.Pn,$11.PD,$11.PS,$11.Pss,(0.(1.&8.))Pra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(12.&5.(1.&40.))Pfc,(1.&20.)Pm0,P,(1.&40.)(8.(1.&8.))Pm,P,(1.&40.)(8.(1.&8.))P,(7.$11.R24.(14.R25.))P,(6.(15.=R25.)(16.R25.R24.))P,(7.$11.(14.(4.(1.&8.)R22.))R25.)P,(16.R24.R25.)P,(17.$18.R5.(1:.R26.(1:.R28.+1.))(;.(1.&8.)(19.(1:.R28.+1.))R24.))P,(17.$18.R6.R26.(>.(1.&8.)(19.(1:.R29.+1.))R25.))P,(1;.$18.R7.R28.R29.)P,(1<.VCS,R29.R2:.)P,(1<.VCS,R29.R2;.)P,(16.=R2:.)P,(16.(1:.R2<.R2=.)(1=.+2.+3?.))P,(1>.(<.(1?.$11.$11.)(20.$11.$11.R2=.(1:.R2=.R2>.))(10.(1?.$11.$11.)))R=.R<.)P,(21.$18.R>.R=.)P,(22.$18.R>.)(23.$18.VAL,VCS,Lms',$24.(5.(1.&40.)La3',(1.&40.)(5.(1.&40.)La4',(1.&40.)(5.(1.&40.)La5',(1.&40.)(5.(1.&40.)La6',(1.&40.)(5.P,(1.&40.)(8.(1.&8.))Lm',P,(1.&40.)(8.(1.&8.))(6.(7.$24.R6.(25.(26.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.(27.&40.R36.)(27.&40.R35.)(27.&40.+1.)R5.R4.R3.R2.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R18.(27.&40.+7::54.)R17.(28.(1.&40.))R1.(29.$18.)))(6.(1>.(<.(1?.$11.$11.)(20.$11.$11.R36.(1:.R36.R37.))(10.(1?.$11.$11.)))R16.R1.)(6.(21.$18.R16.R1.)(6.(22.$18.R1.)(6.(17.$18.R1.R36.R34.)(1;.$18.R1.R36.R37.)))))))))))(25.(26.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.(27.&40.R30.)(27.&40.R2?.)(27.&40.+1.)(27.&40.R32.)R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.)R12.(27.&40.+7::38.)R11.(28.(1.&40.))R?.(29.$18.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until m; intros Hi Hin LEN DS BD BS WR CRD CRS S0 DH MU WM MI; al_facts.
    all: ddestruct (nth_skipn_cons ss (Z.to_nat i) ltac:(lia)) as (b & NB & SK & FS).
    all: assert (SOK : store_ok asegs m (Z_to_bv 64 (D + i)) 1 = true)
           by (change (Z_to_bv 64 (D + i)) with (wa (D + i)); apply (wr_at_store_ok asegs m D n i 1 WR); [lia| cbn; lia]).
    all: replace (Z.to_nat (i + 1)) with (Datatypes.S (Z.to_nat i)) in * by lia.
    all: assert (LF : length (firstn (Z.to_nat i) ss) = Z.to_nat i) by (rewrite length_firstn; lia).
    all: pose proof BS as BS0; rewrite FS in BS0; apply bytes_at_app in BS0; destruct BS0 as [BSP BSB]; rewrite LF in BSB;
         replace (S + Z.of_nat (Z.to_nat i)) with (S + i) in BSB by lia.
    all: pose proof (bytes_at_rdn asegs m (S + i) [b] 0 1 BSB ltac:(cbn; lia)) as RD; cbn [skipn firstn Z.of_nat] in RD;
         rewrite Z.add_0_r in RD; unfold wa in RD; rewrite <- ov_rdn in RD.
    all: zstep; zstep; zstep; zstep; zstep; zstep; zstep.
    all: change (le1 (Z_to_bv 64 (bv_unsigned b))) with (le1 (zxb b)); rewrite le1_zxb.
    all: set (m1 := write_to_mem m (wa (D + i)) [b]) in *; change (write_to_mem m (Z_to_bv 64 (D + i)) [b]) with m1.
    all: assert (MU1 : munch [(D, D + n)] m0 m1) by (subst m1; apply munch_write; [exact MU | lia | cbn; lia | cbn; left; lia]).
    all: assert (WM1 : wmono asegs m0 m1) by (subst m1; apply wmono_write; exact WM).
    all: assert (MI1 : mem_inv asegs m1) by (subst m1; apply mem_inv_store; [exact MI | exact SOK]).
    all: assert (WR1 : wr_at asegs m1 D n) by (subst m1; apply wr_at_write; exact WR).
    all: assert (BD1 : bytes_at asegs m1 (D + i) (skipn (Z.to_nat i) ss)).
    1,3: (rewrite SK; change (b :: skipn (Datatypes.S (Z.to_nat i)) ss) with ([b] ++ skipn (Datatypes.S (Z.to_nat i)) ss); apply bytes_at_app; split;
          [ subst m1; apply bytes_at_write_same; cbn [length]; lia
          | cbn [length]; replace (D + i + Z.of_nat 1) with (D + (i + 1)) by lia; subst m1; apply bytes_at_write_other; [exact BD| lia| cbn; lia| cbn [length]; lia] ]).
    all: assert (BS1 : bytes_at asegs m1 S (firstn (Z.to_nat i) ss)) by (subst m1; apply bytes_at_write_other; [exact BSP| lia| cbn; lia| rewrite LF; cbn [length]; lia]).
    all: clearbody m1; clear SOK RD.
    - (* [comment removed for export] *)
      assert (I0 : i = 0) by lia. subst i. if_falseU. apply evtA_done. eexists _, _, _, _, m1. split; [reflexivity|].
      split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [| exact WR1].
      cbn [Z.to_nat skipn] in BD1. rewrite Z.add_0_r in BD1. exact BD1.
    - if_trueU. replace (Z_to_bv 64 (i + -1)) with (Z_to_bv 64 (i - 1)) by (f_equal; lia).
      eapply (IH (i - 1) n D S ss); try eassumption; try lia.
      + replace (i - 1 + 1) with i by lia. exact BD1.
      + replace (i - 1 + 1) with i by lia. exact BS1.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Theorem imemmove_spec : ltac2:(CDefT.buildp (gd_tbl_AW_IMemmove ()) "Pn,$11.PD,$11.PS,$11.Pss,(0.(1.&8.))Pra,(1.&40.)Psp,(1.&40.)Pgp,(1.&40.)Ptp,(1.&40.)Pt0,(1.&40.)Pt1,(1.&40.)Pt2,(1.&40.)Ps0,(1.&40.)Ps1,(1.&40.)Pa0,(1.&40.)Pa1,(1.&40.)Pa2,(1.&40.)Pa3,(1.&40.)Pa4,(1.&40.)Pa5,(1.&40.)Pa6,(1.&40.)Pa7,(1.&40.)Ps2,(1.&40.)Ps3,(1.&40.)Ps4,(1.&40.)Ps5,(1.&40.)Ps6,(1.&40.)Ps7,(1.&40.)Ps8,(1.&40.)Ps9,(1.&40.)Ps10,(1.&40.)Ps11,(1.&40.)Pt3,(1.&40.)Pt4,(1.&40.)Pt5,(1.&40.)Pt6,(1.&40.)PF,(12.&5.(1.&40.))Pfc,(1.&20.)Pm,P,(1.&40.)(8.(1.&8.))P,(6.(15.=R26.)(16.R26.(1=.+2.+3>.)))P,(7.$11.(14.(4.(1.&8.)R24.))R27.)P,(17.$18.R3.R26.R25.)P,(1;.$18.R4.R28.R29.)P,(1<.VCS,R29.R2:.)P,(1<.VCS,R29.R2;.)P,(16.=R2;.)P,(16.(1:.R2<.R2=.)(1=.+2.+3?.))P,(16.=R2<.)P,(16.(1:.R2=.R2?.)(1=.+2.+3?.))P,(22.$18.R;.)P,(7.(1.&40.)R24.(27.&40.R30.))P,(7.(1.&40.)R24.(27.&40.R30.))P,(7.(1.&40.)R24.(27.&40.R33.))(23.$18.VAL,VCS,Lms',$24.(5.(1.&40.)La1',(1.&40.)(5.(1.&40.)La2',(1.&40.)(5.(1.&40.)La3',(1.&40.)(5.(1.&40.)La4',(1.&40.)(5.(1.&40.)La5',(1.&40.)(5.(1.&40.)La6',(1.&40.)(5.P,(1.&40.)(8.(1.&8.))Lm',P,(1.&40.)(8.(1.&8.))(6.(7.$24.R8.(25.(26.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R7.R6.R5.R4.R3.R2.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R19.(2:.R38.)R18.(28.(1.&40.))R1.(29.$18.)))(6.(1>.(<.(1?.$11.$11.)(20.$11.$11.R3;.(1:.R3;.R3<.))(10.(1?.$11.$11.)))R17.R1.)(6.(21.$18.R17.R1.)(6.(22.$18.R1.)(6.(17.$18.R1.R3;.R39.)(1;.$18.R1.R3;.R3<.)))))))))))))(25.(26.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)R11.(27.&40.+7::00.)R10.(28.(1.&40.))R?.(29.$18.)))")
(* [comment removed for export] *).
  Proof.
    intros until m. intros N0 LEN BS WR CRD CRS D0 DH S0 SH MI -> -> ->. al_facts.
    pose proof (munch_refl [(D, D + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NIL : n = 0 -> bytes_at asegs m D ss).
    { intros ->. destruct ss; [|cbn in LEN; lia]. apply bytes_at_nil. lia. }
    zstep.
    destruct (Z_lt_le_dec D S) as [LT|GE].
    - if_falseU. zstep.
      rewrite bv_lts_zero_l, unsigned_lit by lia.
      destruct (Z.eq_dec n 0) as [N|N].
      + replace ((0 <? n) && (n <? 2 ^ 63))%bool with false by (symmetry; apply andb_false_iff; left; apply Z.ltb_ge; lia). cbn [negb]. cbv iota.
        zstep. apply evtA_done. eexists _, _, _, _, _, _, m. split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact (NIL N)| exact WR].
      + replace ((0 <? n) && (n <? 2 ^ 63))%bool with true by (symmetry; apply andb_true_iff; split; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
        zstep. zstep.
        replace (Z_to_bv 64 S) with (Z_to_bv 64 (S + 0)) by (f_equal; lia). replace (Z_to_bv 64 D) with (Z_to_bv 64 (D + 0)) by (f_equal; lia).
        eapply (evtA_cut asegs AL CS).
        { eapply (immv_floop (Z.to_nat n) 0 n D S ss); try eassumption; try lia.
          - cbn [Z.to_nat firstn]. apply bytes_at_nil. lia.
          - cbn [Z.to_nat skipn]. rewrite Z.add_0_r. exact BS. }
        cbn beta. (intros ms' dd_H; ddestruct dd_H as (a4' & m' & -> & MU' & WM' & MI' & BD' & WR')).
        zstep. zstep. apply evtA_done. eexists _, _, _, _, _, _, m'. split; [reflexivity|].
        split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact BD'| exact WR'].
    - if_trueU. zstep.
      destruct (Z.eq_dec D S) as [E|NE].
      + (* [comment removed for export] *)
        subst S. if_trueU. zstep. apply evtA_done. eexists _, _, _, _, _, _, m. split; [reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact BS| exact WR].
      + if_falseU. zstep.
        rewrite bv_lts_zero_l, unsigned_lit by lia.
        destruct (Z.eq_dec n 0) as [N|N].
        * replace ((0 <? n) && (n <? 2 ^ 63))%bool with false by (symmetry; apply andb_false_iff; left; apply Z.ltb_ge; lia). cbn [negb]. cbv iota.
          zstep. apply evtA_done. eexists _, _, _, _, _, _, m. split; [reflexivity|].
          split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact (NIL N)| exact WR].
        * replace ((0 <? n) && (n <? 2 ^ 63))%bool with true by (symmetry; apply andb_true_iff; split; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
          zstep. zstep.
          replace (Z_to_bv 64 (n + -1)) with (Z_to_bv 64 (n - 1)) by (f_equal; lia).
          eapply (evtA_cut asegs AL CS).
          { eapply (immv_bloop (Z.to_nat (n - 1)) (n - 1) n D S ss); try eassumption; try lia.
            - replace (n - 1 + 1) with n by lia. replace (Z.to_nat n) with (length ss) by lia. rewrite skipn_all. apply bytes_at_nil. lia.
            - replace (n - 1 + 1) with n by lia. replace (Z.to_nat n) with (length ss) by lia. rewrite firstn_all. exact BS. }
          cbn beta. (intros ms' dd_H; ddestruct dd_H as (a3' & a4' & a5' & a6' & m' & -> & MU' & WM' & MI' & BD' & WR')).
          zstep. apply evtA_done. eexists _, _, _, _, _, _, m'. split; [reflexivity|].
          split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact BD'| exact WR'].
  Qed.
End Walk.
