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
Ltac2 gd_tbl_AW_PfLib2 () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_PfNum.pr_range"; "Corelib.Init.Logic.eq"; "Stdlib.Lists.List.nth_error"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.Some"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "Corelib.Init.Datatypes.app"; "Corelib.Lists.ListDef.firstn"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.not"; "Stdlib.Lists.List.In"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.nat"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.zxb"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "Corelib.Lists.ListDef.repeat"].


Lemma upd_same : forall {X} (l : list X) i x, nth_error l i = Some x -> upd l i x = l.
Proof. intros X l; induction l as [|y l IH]; intros [|i] x H; cbn in *; try discriminate; [injection H as ->; reflexivity| f_equal; apply IH; exact H]. Qed.

Lemma pr_not0 : forall b, pr b -> b <> Z_to_bv 8 0.
Proof. intros b [H0 _] E. apply H0. rewrite E. reflexivity. Qed.

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
  #[using="Type"] Lemma out_cstr : ltac2:(CDefT.buildp (gd_tbl_AW_PfLib2 ()) "Pm,P,(0.&40.)(1.(0.&8.))PBUF,$2.Pbs,(3.(0.&8.))Plen,$2.P,(4.$5.R4.R3.R2.)P,(6.=R2.)P,(7.R4.=R3.)P,(8.(1.(0.&8.))(9.(0.&8.)R5.(:.R4.))(;.(0.&8.)(<.&8.=)))(=.(>.$5.R8.R7.(?.(0.&8.)(10.(0.&8.)(:.R5.)R6.)(11.(0.&8.)(<.&8.=)(12.(0.&8.)))))(=.(13.(14.(0.&8.)(<.&8.=)(10.(0.&8.)(:.R5.)R6.)))(8.$2.(15.(16.(0.&8.)(10.(0.&8.)(:.R5.)R6.)))R5.)))")
(* [comment removed for export] *).
  Proof.
    intros m BUF bs len [BY _] L0 PR NUL.
    pose proof (nth_error_lt _ _ _ NUL) as LT.
    assert (LF : length (firstn (Z.to_nat len) bs) = Z.to_nat len) by (rewrite length_firstn; lia).
    split; [|split; [|lia]].
    - destruct (nth_error_split _ _ _ NUL) as (pre & post & E & Hlen).
      assert (EF : firstn (Z.to_nat len) bs = pre) by (rewrite E, <- Hlen, firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r; reflexivity).
      rewrite EF. rewrite E in BY. replace (pre ++ Z_to_bv 8 0 :: post) with ((pre ++ [Z_to_bv 8 0]) ++ post) in BY by (rewrite <- app_assoc; reflexivity).
      apply bytes_at_app in BY. exact (proj1 BY).
    - intros IN. apply In_nth_error in IN. destruct IN as (i & Hi).
      pose proof (nth_error_lt _ _ _ Hi) as Li. rewrite LF in Li.
      rewrite nth_error_firstn in Hi. replace (i <? Z.to_nat len)%nat with true in Hi by (symmetry; apply Nat.ltb_lt; lia).
      ddestruct (PR (Z.of_nat i) ltac:(lia)) as (x & Hx & PX). rewrite Nat2Z.id in Hx. rewrite Hx in Hi. injection Hi as ->.
      exact (pr_not0 _ PX eq_refl).
  Qed.

  #[using="Type"] Lemma bytes_at_read1 : ltac2:(CDefT.buildp (gd_tbl_AW_PfLib2 ()) "Pm,P,(0.&40.)(1.(0.&8.))PP,$2.Pbs,(3.(0.&8.))Pj,$2.Px,(0.&8.)P,(>.$5.R5.R4.R3.)P,(8.(1.(0.&8.))(9.(0.&8.)R4.(:.R3.))(;.(0.&8.)R2.))P,(6.=R4.)(8.(1.(3.(0.&8.)))(17.$5.R8.(<.&40.(18.R7.R5.))#1.)(;.(3.(0.&8.))(11.(0.&8.)R4.(12.(0.&8.)))))")
(* [comment removed for export] *).
  Proof.
    intros m P bs j x BY Hn Hj. pose proof (nth_error_lt _ _ _ Hn) as LT.
    change (Z_to_bv 64 (P + j)) with (wa (P + j)). rewrite (bytes_at_read asegs m P bs j 1 BY Hj ltac:(lia)).
    destruct (nth_error_split _ _ _ Hn) as (pre & post & E & Hlen). rewrite E at 1.
    rewrite skipn_app, skipn_all2, Hlen, Nat.sub_diag by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma rma_loop : ltac2:(CDefT.buildp (gd_tbl_AW_PfLib2 ()) "Pk,$19.Pi,$2.Plen,$2.PP,$2.Pbs,(3.(0.&8.))Pb,(0.&8.)Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1:.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(1.(0.&8.))P,(8.$2.(1;.(1;.R21.+1.)R22.)(15.R23.))P,(6.=R23.)P,(>.$5.R3.R22.R21.)P,(1<.VCS,R23.(18.R24.+1.))P,(1=.=R24.)P,(1=.(18.(18.R25.R26.)+1.)(1>.+2.+3?.))P,(7.R25.=R27.)P,(8.(1.(0.&8.))(9.(0.&8.)R26.(:.R28.))(;.(0.&8.)(<.&8.=)))P,(8.(1.(0.&8.))(9.(0.&8.)R27.(:.R2:.))(;.(0.&8.)R26.))(1?.$5.VAL,VCS,Lms',$20.(8.$20.R1.(21.(22.R27.R26.R25.R24.R23.R22.R21.(<.&40.(18.R2:.R2;.))(<.&40.+1;.)(<.&40.(18.R2:.R2;.))(<.&40.=)R20.(<.&40.(18.(18.R2:.R2;.)-1.))R1>.R1=.R1<.R1;.(<.&40.+5;.)R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.)R=.(<.&40.+76>5<.)R<.(23.(0.&40.))R;.(24.$5.)))(21.(22.R26.R25.R24.R23.R22.R21.R20.(<.&40.(18.R29.R2;.))(<.&40.+1;.)(<.&40.(18.R29.R2;.))(25.R27.)R1?.R1>.R1=.R1<.R1;.R1:.(<.&40.+5;.)R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R?.R>.R=.)R<.(<.&40.+76>0<.)R;.(23.(0.&40.))R:.(24.$5.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros until m; intros Hk Hi BY CR P0 PH PR NUL NB; al_facts.
    all: ddestruct (PR i ltac:(lia)) as (b' & NB' & [B0 B27]); rewrite NB in NB'; injection NB' as <-.
    all: pose proof (bv_unsigned_in_range 8 b) as BR; unfold bv_modulus in BR; cbn [Z.pow Z.of_N Pos.pow] in BR.
    all: pose proof (nth_error_lt _ _ _ NUL) as LT.
    all: zstep; zstep; if_falseU; zstep; if_trueU; zstep; if_trueU.
    all: pose proof (nth_error_lt _ _ _ NB) as LTi.
    - replace (i + 1) with len in * by lia.
      pose proof (bytes_at_read1 m P bs (i + 1) _ BY ltac:(replace (i + 1) with len by lia; exact NUL) ltac:(lia)) as RD.
      zstep. zstep. zstep. zstep.
      replace (P + i + 1) with (P + len) by lia. replace (P + i) with (P + len + -1) by lia. apply evtA_done. reflexivity.
    - ddestruct (PR (i + 1) ltac:(lia)) as (b2 & NB2 & [B20 B227]).
      pose proof (bv_unsigned_in_range 8 b2) as BR2; unfold bv_modulus in BR2; cbn [Z.pow Z.of_N Pos.pow] in BR2.
      pose proof (bytes_at_read1 m P bs (i + 1) _ BY NB2 ltac:(lia)) as RD.
      zstep. zstep. zstep. zstep. if_trueU.
      replace (P + i + 1) with (P + (i + 1)) by lia. change (Z_to_bv 64 (bv_unsigned b2)) with (zxb b2).
      eapply (IH (i + 1) len P bs b2); try eassumption; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Theorem rma_spec : ltac2:(CDefT.buildp (gd_tbl_AW_PfLib2 ()) "Plen,$2.PP,$2.PSP,$2.Plo,$2.Pbs,(3.(0.&8.))Pra,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1:.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(1.(0.&8.))P,(6.+1.R26.)P,(4.$5.R2.R26.R23.)P,(7.R24.=R28.)P,(8.(1.(0.&8.))(9.(0.&8.)R25.(:.R29.))(;.(0.&8.)(<.&8.=)))P,(1<.VCS,R29.(15.(16.(0.&8.)R26.)))P,(1=.=R2:.)P,(1=.(18.R2;.(15.(16.(0.&8.)R28.)))(1>.+2.+3?.))P,(26.$5.R8.R2:.R2;.)P,(6.+65?000.R2;.)P,(6.R2<.(1;.R2=.+20.))P,(1<.VCS,R2=.(1;.R2>.R2=.))P,(6.R2?.R30.)P,(27.$5.R=.)P,(8.(0.&40.)R26.(<.&40.R32.))(1?.$5.VAL,VCS,Lms',$20.(28.(0.&40.)La0',(0.&40.)(28.(0.&40.)La1',(0.&40.)(28.(0.&40.)La3',(0.&40.)(28.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(=.(8.$20.R5.(21.(22.R34.(<.&40.R37.)R33.R32.R31.R30.R2?.R2>.R2=.R4.R3.R2:.R2.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)R16.(29.R34.)R15.(23.(0.&40.))R1.(24.$5.)))(=.(26.$5.R1.R36.R37.)(=.(4.$5.R1.R38.R35.)(=.(2:.(11.(2;.$2.$2.)(2<.$2.$2.R36.R37.)(11.(2;.$2.$2.)(2<.$2.$2.R38.(18.R38.(15.(16.(0.&8.)R35.))))(12.(2;.$2.$2.))))R14.R1.)(=.(2=.$5.R14.R1.)(27.$5.R1.))))))))))(21.(22.R2?.(<.&40.R32.)R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.)R11.(<.&40.+76=>0.)R10.(23.(0.&40.))R?.(24.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros until m. intros L1 OUT PR NUL CRB P0 PH ST LOIMG SPL SCS SPP MI ->. al_facts.
    pose proof (munch_refl [(lo, SP); (P, P + Z.of_nat (length bs))] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (nth_error_lt _ _ _ NUL) as LT.
    ddestruct (PR 0 ltac:(lia)) as (b0 & NB0 & [B00 B027]).
    pose proof (bv_unsigned_in_range 8 b0) as BR0; unfold bv_modulus in BR0; cbn [Z.pow Z.of_N Pos.pow] in BR0.
    carve_frame 32%nat ST.
    zstep. zstep. zstep. zstep. zstep. zstep. if_falseU.
    pose proof (bytes_at_read1 m1 P bs 0 b0 (proj1 OUT) NB0 ltac:(lia)) as RD. rewrite Z.add_0_r in RD.
    zstep. zstep. if_falseU. zstep. zstep. zstep.
    replace (Z_to_bv 64 P) with (Z_to_bv 64 (P + 0)) by (f_equal; lia).
    eapply (evtA_cut asegs AL CS).
    { change (Z_to_bv 64 (bv_unsigned b0)) with (zxb b0).
      eapply (rma_loop (Z.to_nat (len - 1)) 0 len P bs b0); try eassumption; try lia; [exact (proj1 OUT)|].
      intros x Hx. apply CRB. lia. }
    cbn beta. intros ms' ->.
    zstep.
    pose proof (u8arr_store_ok asegs m1 P bs len (Z_to_bv 64 (P + len)) OUT ltac:(lia) eq_refl) as SOK.
    zstep.
    rewrite (le1_lit 0) by lia.
    pose proof (u8arr_write asegs m1 P bs len (Z_to_bv 8 0) OUT ltac:(lia)) as OUT2. rewrite (upd_same bs _ _ NUL) in OUT2.
    store_done.
    zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FR ST SP.
    apply evtA_done. eexists _, _, _, m0. split; [reflexivity|].
    split; [exact ST|]. split; [exact OUT2|]. split; [exact MU|]. split; [exact WM| exact MI].
  Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Theorem rawwrite_spec : ltac2:(CDefT.buildp (gd_tbl_AW_PfLib2 ()) "Ps,(3.(0.&8.))PP,$2.PSP,$2.Plo,$2.Pra,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1:.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(1.(0.&8.))P,(>.$5.R1.R24.(?.(0.&8.)R25.(11.(0.&8.)(<.&8.=)(12.(0.&8.)))))P,(13.(14.(0.&8.)(<.&8.=)R26.))P,(1<.VCS,R26.(18.(15.(16.(0.&8.)R27.))+1.))P,(1=.=R27.)P,(1=.(18.(18.R28.(15.(16.(0.&8.)R29.)))+1.)(1>.+2.+3?.))P,(2>.$5.R6.+?6:18.(11.$2?.(30.(<.&40.+1.))(12.$2?.)))P,(26.$5.R7.R28.R29.)P,(6.+65?000.R29.)P,(6.R2:.(1;.R2;.+10.))P,(1<.VCS,R2;.(1;.R2<.R2;.))P,(6.R2=.R2>.)P,(27.$5.R<.)P,(8.(0.&40.)R25.(<.&40.R30.))(1?.$5.VAL,VCS,Lms',$20.(28.(0.&40.)La0',(0.&40.)(28.(0.&40.)La1',(0.&40.)(28.(0.&40.)La2',(0.&40.)(28.(0.&40.)La3',(0.&40.)(28.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(=.(8.$20.R6.(21.(22.R34.(<.&40.R36.)R33.R32.R31.R30.R2?.R2>.R2=.R5.R4.R3.R2.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.)R16.(29.R34.)R15.(23.(0.&40.))R1.(24.$5.)))(=.(26.$5.R1.R35.R36.)(=.(2:.(11.(2;.$2.$2.)(2<.$2.$2.R35.R36.)(12.(2;.$2.$2.)))R14.R1.)(=.(2=.$5.R14.R1.)(27.$5.R1.))))))))))(21.(22.R2>.(<.&40.R30.)R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.)R10.(<.&40.+7790<.)R?.(23.(0.&40.))R>.(24.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros until m. intros BY NZ CR P0 PH GOT ST LOIMG SPL SCS SPP MI ->. al_facts.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    carve_frame 16%nat ST.
    zstep. zstep. zstep. zstep. zstep.
    eapply (evtA_cut asegs AL CS).
    { eapply (istrlen_spec AL IMG ALWF CS CSOK s P); try eassumption; try reflexivity; try lia. }
    cbn beta. (intros ms' dd_H; ddestruct dd_H as (a1s & a2s & ->)).
    ret_lit.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. zstep. zstep.
    release_frame FR ST SP.
    apply evtA_done. eexists _, _, _, _, m1. split; [reflexivity|].
    split; [exact ST|]. split; [exact MU|]. split; [exact WM| exact MI].
  Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Theorem imsetw_spec : ltac2:(CDefT.buildp (gd_tbl_AW_PfLib2 ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1:.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(1.(0.&8.))PP,$2.Pn,$2.Pb,(0.&8.)P,(31.$5.R4.R3.R2.)P,(1=.=R3.)P,(1<.VCS,R5.R4.)P,(1=.=R6.)P,(1=.(18.R7.R6.)(1>.+2.+3?.))P,(27.$5.R9.)P,(8.(0.&40.)R22.(<.&40.R9.))P,(8.(0.&40.)R22.(25.R8.))P,(8.(0.&40.)R22.(<.&40.R:.))(1?.$5.VAL,VCS,Lms',$20.(28.(0.&40.)La1',(0.&40.)(28.(0.&40.)La3',(0.&40.)(28.P,(0.&40.)(1.(0.&8.))Lm',P,(0.&40.)(1.(0.&8.))(=.(8.$20.R4.(21.(22.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R3.(<.&40.(18.R10.R?.))R2.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)R13.(29.R32.)R12.(23.(0.&40.))R1.(24.$5.)))(=.(2:.(11.(2;.$2.$2.)(2<.$2.$2.R10.(18.R10.R?.))(12.(2;.$2.$2.)))R11.R1.)(=.(2=.$5.R11.R1.)(=.(27.$5.R1.)(4.$5.R1.R10.(32.(0.&8.)R>.(:.R?.))))))))))(21.(22.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.)R?.(<.&40.+7::58.)R>.(23.(0.&40.))R=.(24.$5.)))")
(* [comment removed for export] *).
  Proof.
    intros until b. intros WR N1 CR P0 PH MI -> -> ->. al_facts.
    assert (VF : vfill m P 0 n b). { unfold vfill. split; [cbn [Z.to_nat repeat]; apply bytes_at_nil; lia|]. split; [exact WR| lia]. }
    pose proof (munch_refl [(P, P + n)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (B15 : 0 <= Z.land (Z.lor n P) 15 < 16).
    { change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2^4) with 16. apply Z.mod_pos_bound. lia. }
    zstep. zstep. zstep.
    destruct (Z.eq_dec (Z.land (Z.lor n P) 15) 0) as [AL16|NA].
    - destruct (land15_lor_zero n P ltac:(lia) ltac:(lia) AL16) as [Mn Mp].
      if_trueU. zstep. if_falseU. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      eapply (evtA_cut asegs AL CS).
      { eapply (imsv_wloop AL IMG ALWF CS CSOK (Z.to_nat (n / 16)) 0 n P P b (pat8 b)); [exact (le8_pat8 b) | ..]; try eassumption; try lia. }
      cbn beta. (intros ms' dd_H; ddestruct dd_H as (a3' & m' & -> & MU' & WM' & MI' & ARR')). zstep. apply evtA_done.
      eexists _, _, m'. split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'| exact ARR'].
    - if_falseU. zstep. if_falseU. zstep. zstep.
      eapply (evtA_cut asegs AL CS).
      { eapply (imsv_bloop AL IMG ALWF CS CSOK (Z.to_nat n) 0 n P P b); try eassumption; try lia. }
      cbn beta. (intros ms' dd_H; ddestruct dd_H as (a3' & m' & -> & MU' & WM' & MI' & ARR')). zstep. apply evtA_done.
      eexists _, _, m'. split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'| exact ARR'].
  Qed.
End Walk.
