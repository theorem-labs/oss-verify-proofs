(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_MmapFixed.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00807012ba9b01dd 0 2 0 1 28 1P03addec8aedf1ac3 0 2 0 1 28 1P03c07186138045f8 0 2 0 1 28 1P03f69e1e98b6d1f5 0 3 1 1 29 1 30 1P04a90f1054fcd1c0 0 2 0 1 32 1P04fbcde9560bccb6 0 2 0 1 28 1P0514994dc8e16ca6 0 2 0 1 28 1P05a1aa50b35ca1d3 0 3 1 1 29 1 30 1P08760e6c036fc170 0 2 0 1 28 1P088a8b7712859ea3 0 3 1 1 29 1 30 1P0977ebfbf16cd3b2 0 2 0 1 28 1P09cfb1f2230d4298 0 3 1 1 29 1 30 1P0a00afdf0d7e6ef5 0 2 0 1 32 1P0af5151cb78603e6 0 2 0 1 28 1P0af924644da98a31 0 2 0 1 28 1P0b76ac4109b7dd4d 0 2 0 1 28 1P0d318ac3f92716c5 0 3 1 1 29 1 30 1P0dbe8dd92779534b 0 2 0 1 32 1P0dcbcc2f0915834a 0 2 0 1 28 1P0fab69dd0c8b183f 0 3 0 1 20 1 29 1P104d470da8843d5d 0 2 0 1 28 1P12016a44c44f3b40 0 2 0 1 28 1P131943ace7f2cd34 0 2 0 1 28 1P13520189870f7acd 0 3 1 1 29 1 30 1P1371774f2856603b 0 3 1 1 29 1 30 1P13be0b453c7efae2 0 3 1 1 29 1 30 1P13e36358139601b3 0 3 1 1 29 1 30 1P1428d6aada4e0c74 0 2 0 1 28 1P14b10f650855de2e 0 2 0 1 28 1P16a98a9dce4d3df8 0 2 0 1 32 1P17248e5897132466 0 2 0 1 28 1P175ee133f7a044a7 0 3 1 1 29 1 30 1P17a3730a711f86d3 0 2 0 1 28 1P18cacdf49d98d75f 0 2 0 1 28 1P19d9602e2254b73c 0 3 1 1 29 1 30 1P1a11a51c580f604a 0 2 0 1 28 1P1a6100a72675f376 0 2 0 1 28 1P1a8322ca2dea08d9 0 3 1 1 29 1 30 1P1aaef3607b781d8f 0 2 0 1 28 1P1c04df1091a14fc6 0 2 0 1 28 1P1c43d9c02cc3359e 0 2 0 1 32 1P1c665fe53639b36e 0 2 0 1 28 1P1cce910c8fedd320 0 3 0 1 20 1 29 1P1e2a08e231dd019d 0 3 1 1 29 1 30 1P1ea4021545ebd8b7 0 2 0 1 28 1P1f13307fc47d9159 0 2 0 1 28 1P1f2ff24f200370b5 0 3 1 1 29 1 30 1P1fd96cdf8796502a 0 2 0 1 28 1P205b34b23462869d 0 3 1 1 29 1 30 1P205d67fef4c7b7ad 0 2 0 1 32 1P20686386dfecad49 0 3 1 1 29 1 30 1P20fcd2f2ad413629 0 2 0 1 28 1P21c614005d6e3f53 0 3 1 1 33 1 34 1P231c1b6e374a59e3 0 2 0 1 28 1P24cb5d0d4486da67 0 2 0 1 32 1P24d8dee6b397ab79 0 3 1 1 29 1 30 1P2521282837394862 0 2 0 1 28 1P2679bc810b4c93d9 0 2 0 1 28 1P267fc2efc3855a3a 0 3 1 1 29 1 30 1P295248f0cab207f9 0 3 1 1 29 1 30 1P296a791db63a0ef5 0 3 1 1 29 1 30 1P2b96383792fac241 0 3 1 1 33 1 34 1P2c179a2fc6ae725c 0 3 1 1 29 1 30 1P2ce95ada5f311cc6 0 3 1 1 29 1 30 1P2d087ae48bc26fbd 0 2 0 1 32 1P2d18a02a5034ded5 0 2 0 1 28 1P2d6b0f4fa216ecdc 0 3 1 1 29 1 30 1P2e7712f2fe6abfd8 0 2 0 1 28 1P2ea75a50101827d6 0 2 0 1 28 1P2f41c80b06ba586c 0 2 0 1 28 1P2fec9136f9bc02fc 0 2 0 1 28 1P31b0f6b0c06a7907 0 2 0 1 28 1P33334346e4dfe360 0 3 1 1 29 1 30 1P33fee23546371e1c 0 2 0 1 21 1P345cd5e1c4bd1476 0 2 0 1 28 1P36e955f5d845498e 0 2 0 1 28 1P389aef683b284eb3 0 3 1 1 29 1 30 1P393ad642c2a94ba4 0 2 0 1 28 1P3983de6c9c0eb1f2 0 2 0 1 28 1P3a1770f695fb4bf0 0 3 1 1 29 1 30 1P3bd31b21c85590a2 0 3 1 1 29 1 30 1P3e6e14999b2f5ac6 0 2 0 1 32 1P3e9589bb20d12425 0 2 0 1 28 1P3f4e72d82a19d7c9 0 3 1 1 29 1 30 1N1183ae467c97cb08"%lxh.
Ltac2 gd_tbl_AW_MapOrDie () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MSsvc"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_PAGESZ_CELL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_MMAP_ECALL"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_GOT_PAGESZ"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.MapOrDie.mod_pre_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "ARUN_1.A_MAPORDIE"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_MMAP_LIMIT"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.mf_ret_post"; "ARUN_1.MapOrDie.mod_answered"].

Section ARUN_1. Context {hAR : arun}.
Definition A_MAPORDIE : Z := 0x0852f4.      (* [comment removed for export] *)

Section MapOrDie.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  Definition mod_pre_post (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (addr size lo : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MapOrDie ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lmm,P,(2.&40.)(3.(2.&8.))(1.(4.(2.&8.))Lfr,(4.(2.&8.))(5.(6.$0.R;.(7.(8.(9.&40.+7=01<.)(9.&40.(:.O15.-60.))O14.O13.R:.R9.R8.(9.&40.(;.(<.(:.O3.+???.)+1000.)+1000.))(9.&40.=)(9.&40.O4.)(9.&40.(;.(<.(:.O3.+???.)+1000.)+1000.))(9.&40.+3.)(9.&40.+32.)(9.&40.-1.)(9.&40.=)R3.(9.&40.+=>.)(9.&40.O4.)(9.&40.=)(9.&40.$=.)O=.O<.O;.O:.O9.O8.O7.R7.R6.R5.R4.)O6.(9.&40.$>.)(9.&40.+=>.)O5.(?.(2.&40.))R2.(10.$11.)))(5.(12.(13.(14.$15.$15.)(16.$15.$15.O2.O15.)(17.(14.$15.$15.)))O1.R2.)(5.(18.$11.O1.R2.)(5.(19.$11.R2.)(5.(1:.$11.R2.(:.O15.-60.)(13.$1;.(1<.(9.&40.+32.))(13.$1;.(1=.#2<.R1.)(13.$1;.(1>.O>.)(13.$1;.(1>.O?.)(13.$1;.(1>.O10.)(13.$1;.(1>.O11.)(13.$1;.(1>.O12.)(13.$1;.(1>.O16.)(17.$1;.))))))))))(1?.$11.R2.O2.(:.O15.-60.)))))))))))))))))")
(* [comment removed for export] *).

  #[using="IMG ALWF CSOK"] Lemma mapordie_pre : ltac2:(CDefT.buildp (gd_tbl_AW_MapOrDie ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa0,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)PSP,$15.PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Paddr,$15.Psize,$15.Plo,$15.P,(5.(21.=R3.)(22.R3.(23.+2.+2?.)))P,(6.$15.(24.R4.+1000.)=)P,(5.(22.=R4.)(21.R4.(23.+2.+28.)))P,(25.$11.R7.$26.(13.$1;.(1>.(9.&40.$=.))(17.$1;.)))P,(25.$11.R8.$=.(13.$1;.(1>.(9.&40.+1000.))(17.$1;.)))P,(1?.$11.R9.R6.R<.)P,(21.+65?000.R7.)P,(21.R8.(27.R>.+170.))P,(21.R?.(23.+2.+3?.))P,(28.VCS,R:.(27.R10.R:.))P,(19.$11.R>.)(29.$11.VAL,VCS,(2:.R2=.R12.R2<.R2;.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R11.R10.R>.R=.R<.R?.)(2;.(8.R2=.(9.&40.R12.)R2<.R2;.R2:.R29.R28.R27.R26.R17.(9.&40.R>.)(9.&40.R=.)(9.&40.=)R16.R15.R14.R13.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R11.(9.&40.$2<.)R10.(?.(2.&40.))R?.(10.$11.)))")
(* [comment removed for export] *).
  Proof.
    pose proof (I : lx_noaceil) as LXNOACEIL.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a0 a4 a5 a6 a7 SP F fc m addr size lo
      AB AAL SZ GOT PGS ST LOIMG SPL SPH SCS MI.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold A_MAPORDIE, A_GOT_PAGESZ, A_PAGESZ_CELL in *. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x7b25c] [] 100%N).
    lx_stk_grow_to lo (SP + -96).
    try rewrite (Z.land_comm (-4096) addr) in *.
    try (rewrite (lxw_land_m4096 addr) in * by (clear -AB; lia); replace (addr / 4096 * 4096) with addr in * by (pose proof (Z.div_mod addr 4096 ltac:(lia)); clear -H0 AAL; lia)).
    try rewrite (lxw_land_m4096 (size + 4095)) in * by (clear -SZ; lia).
    stepA_ecall.
    lazymatch goal with FRw : rw_cells _ ?mx (SP + -96) _, FRh : rw_cells _ ?mx (SP + -48) _, STj : stk _ ?mx (SP + -92) (SP + -48) |- _ =>
      lx_junk STj 44%nat fr FRj; chunk_join FRw FRj FRa; chunk_join FRa FRh FRb end.
    unfold mod_pre_post, A_MMAP_ECALL, A_PAGESZ_CELL. lx_exs; lx_ands; [ lx_mseq | assumption | assumption | assumption | exact FRb | assumption ].
  Qed.

  (* [comment removed for export] *)
  Definition mod_answered (r : word) (SP : Z) (gp tp t0 t1 t2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 : word)
      (F : bvmap 5 word) (fc : bv 32) (addr size : Z) (mm : mem) : machine_state := ltac2:(CDefT.buildp (gd_tbl_AW_MapOrDie ()) "(2;.(8.(9.&40.+7=01<.)(9.&40.(:.O17.-60.))O16.O15.O14.O13.O12.(9.&40.(;.(<.(:.O2.+???.)+1000.)+1000.))(9.&40.=)O18.(9.&40.(;.(<.(:.O2.+???.)+1000.)+1000.))(9.&40.+3.)(9.&40.+32.)(9.&40.-1.)(9.&40.=)O6.(9.&40.+=>.)(9.&40.O3.)(9.&40.=)(9.&40.$=.)O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.)O5.(9.&40.+7;260.)O4.(?.(2.&40.))O1.(10.$11.))")
(* [comment removed for export] *).

  #[using="IMG ALWF CSOK"] Lemma mapordie_post_ok : ltac2:(CDefT.buildp (gd_tbl_AW_MapOrDie ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa6,(2.&40.)PSP,$15.PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Paddr,$15.Psize,$15.Plo,$15.Pfr,(4.(2.&8.))P,(5.(22.=R4.)(22.R4.(2=.VhAR,)))P,(5.(22.=R4.)(21.R4.(23.+2.+28.)))P,(1:.$11.R7.(:.R;.-60.)(13.$1;.(1<.(9.&40.+32.))(13.$1;.(1=.#2<.R3.)(13.$1;.(1>.R18.)(13.$1;.(1>.R19.)(13.$1;.(1>.R1:.)(13.$1;.(1>.R1;.)(13.$1;.(1>.R1<.)(13.$1;.(1>.R22.)(17.$1;.))))))))))P,(25.$11.R8.$2>.(13.$1;.(1>.(9.&40.$2?.))(17.$1;.)))P,(25.$11.R9.$30.(13.$1;.(1>.(9.&40.=))(17.$1;.)))P,(1?.$11.R:.R7.(:.R>.-60.))P,(21.+65?000.R8.)P,(21.R9.(27.R10.+170.))P,(21.R11.(23.+2.+3?.))P,(12.(13.(14.$15.$15.)(16.$15.$15.R;.R12.)(17.(14.$15.$15.)))R?.R>.)P,(18.$11.R10.R?.)P,(19.$11.R10.)P,(28.VCS,R>.(27.R15.R>.))(29.$11.VAL,VCS,(31.R2=.R16.R2<.R2;.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R15.R14.R11.R?.R13.)(32.(9.&40.R11.)R16.R2<.R2;.R2:.R29.R28.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R15.R14.R11.R10.R12.))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 SP F fc m0 mm addr size lo fr
      AB SZ FR GOTF LIM ST LOIMG SPL SPH MU WM MI SCS.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    unfold mod_answered, A_PAGESZ_CELL, A_GOT_CFLAGS, A_CFLAGS, A_MMAP_LIMIT in *. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 80%N). lx_postw.
  Qed.
End MapOrDie.

End ARUN_1.
