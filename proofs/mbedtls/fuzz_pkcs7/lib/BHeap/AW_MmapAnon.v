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
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00e2134c5ed7ec8d 0 3 1 1 33 1 34 1P01198e97cdc48fe9 0 3 1 1 33 1 34 1P015ec397311edb76 0 2 0 1 32 1P019fb509ac410638 0 3 1 1 33 1 34 1P0223121e73c14b21 0 2 0 1 24 1P023e8ce03a42432c 0 3 1 1 33 1 34 1P0298877fc41ff0a5 0 2 0 1 25 1P02e3dee152b1cafd 0 2 0 1 32 1P0377362020c5e647 0 3 1 1 33 1 34 1P039cff2bf82f3995 0 2 0 1 32 1P049ae9152c4b6d43 0 4 0 1 21 1 29 1 34 1P04d0bf0af3ef39a3 0 2 0 1 32 1P05f0af778d73a3ea 0 2 0 1 32 1P0628455d5f9c3241 0 3 1 1 33 1 34 1P0633d2364c6f28e4 0 3 1 1 33 1 34 1P07df407db3670076 0 3 1 1 33 1 34 1P0a2228ff87a60742 0 2 0 1 24 1P0a39534693da3971 0 2 0 1 32 1P0a6d3a32ee97dd16 0 2 0 1 32 1P0b4c60aa890d687b 0 2 0 1 32 1P0c25337bb3acaea2 0 2 0 1 39 1P0c2cac5066cc50b9 0 2 0 1 32 1P0ca21d8af38f1f0f 0 2 0 1 32 1P0cefcaaa1f8a2c57 0 3 1 1 33 1 34 1P0d69ca10984dc049 0 2 0 1 32 1P0da0a02cca66f595 0 3 1 1 33 1 34 1P0f18d1c3d1a90b51 0 2 0 1 23 1P10298cafcf731450 0 2 0 1 32 1P117b5db179733dfa 0 2 0 1 24 1P121a0adaea5229ef 0 3 1 1 33 1 34 1P12bb4f2a780372e7 0 2 0 1 25 1P13bc89d9470b3f87 0 2 0 1 32 1P14924d978d578a29 0 2 0 1 32 1P14d9379e1309a344 0 2 0 1 32 1P1507162541dc4390 0 2 0 1 24 1P168588bcb0ba8b87 0 3 1 1 33 1 34 1P17b264695b99a4e6 0 3 1 1 33 1 34 1P186d147f51cab125 0 2 0 1 32 1P191e5156ab9cd878 0 2 0 1 32 1P1a7108b9acccb595 0 2 0 1 24 1P1b2de3c120090b34 0 3 1 1 33 1 34 1P1b5e7f4a0747e804 0 2 0 1 32 1P1d0c11c6620c4ed3 0 2 0 1 32 1P1d71672cd23cb09b 0 3 1 1 33 1 34 1P1daeede54bf2707d 0 3 1 1 33 1 34 1P1db9b22c4ff7335a 0 2 0 1 24 1P1df89e08ef36318b 0 2 0 1 32 1P1e13796ba7ddb8d8 0 3 1 1 33 1 34 1P1e3ccfb2b38b9e5f 0 3 1 1 33 1 34 1P1e69224be00dacef 0 2 0 1 32 1P1e7045e62a4591ed 0 2 0 1 32 1P20a0fa000c8583d2 0 3 1 1 33 1 34 1P22fa650f71803fc5 0 3 1 1 33 1 34 1P232ec0869d08309f 0 2 0 1 32 1P23885ba8bede30df 0 3 1 1 33 1 34 1P23cdb9ab4c284083 0 2 0 1 32 1P23d1c7038c0e6ab4 0 2 0 1 32 1P23ffdac8626b5046 0 2 0 1 32 1P244360e61bd24c6c 0 3 1 1 33 1 34 1P24db195b3c8e773c 0 2 0 1 32 1P25178b76c22b19ef 0 3 1 1 33 1 34 1P25225874100eefbc 0 2 0 1 24 1P26129ea3eaf6093e 0 3 1 1 33 1 34 1P2714d860495c5d19 0 2 0 1 2 1P282c04502066b664 0 2 0 1 32 1P28991e6eb76a32f5 0 3 1 1 33 1 34 1P2987a319d20fd6c1 0 3 1 1 33 1 34 1P2a4d3d00f99a214a 0 3 1 1 33 1 34 1P2a6ae20e12c6df81 0 3 1 1 33 1 34 1P2b5e43aa03296ee1 0 2 0 1 32 1P2c58d14880fb38fa 0 2 0 1 32 1P2d2284529e84f202 0 2 0 1 2 1P2e8620f56b8c8db9 0 2 0 1 32 1P2f92b394231872df 0 2 0 1 32 1P3016fd6f09185a35 0 3 1 1 33 1 34 1P302b206d7e41fe53 0 3 1 1 33 1 34 1P3059f6ffe66d0234 0 2 0 1 32 1P3090de5e29832fbe 0 2 0 1 32 1P310506b51f8cd59f 0 2 0 1 32 1P3196a95b752cd2ee 0 3 1 1 33 1 34 1P31af50cac15d141e 0 2 0 1 32 1P32508e541fc1c02b 0 2 0 1 32 1P329416d05c8502f8 0 2 0 1 32 1P332e5916e8d58408 0 2 0 1 32 1P342a61b8bc705415 0 3 1 1 33 1 34 1P3461fd4fff7e341f 0 3 1 1 33 1 34 1P34ad7bb10ea77124 0 2 0 1 35 1P351ea2c864210798 0 3 1 1 33 1 34 1P355f4186ca125739 0 3 1 1 33 1 34 1P35f0a0c99cb7c616 0 2 0 1 32 1P37107b8ecaed85d2 0 3 1 1 33 1 34 1P37461adbfc621ff7 0 3 1 1 33 1 34 1P375410a36dc91344 0 2 0 1 32 1P379399f45dfdc6f4 0 3 1 1 33 1 34 1P37b1f764d4b35659 0 2 0 1 32 1P37ce4eee04cfb75b 0 2 0 1 24 1P37cf74d4714d0172 0 3 1 1 33 1 34 1P38df0662786be3df 0 2 0 1 32 1P390b895794c9770b 0 3 1 1 33 1 34 1P3b50a9e2b0d77ca5 0 3 1 1 33 1 34 1P3f614f7c5ae4f08d 0 3 1 1 33 1 34 1P3f6f3e83d897458c 0 3 1 1 33 1 34 1N056d3cea6a544593N25c5b11dbb1a08ebN28e7cfbef15f7a98N363ecbbb78d1e0c8N3b053fd141957e6e"%lxh.
Ltac2 gd_tbl_AW_MmapAnon () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MSsvc"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_PAGESZ_CELL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_MMAP_ECALL"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_GOT_PAGESZ"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_DECORATE"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.MmapAnon.ma_pre_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "ARUN_1.A_MMAP_ANON_TOL"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "ARUN_1.MmapAnon.ma_ret_post"; "ARUN_1.MmapAnon.ma_answered"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_MMAP_LIMIT"].

Section ARUN_1. Context {hAR : arun}.
Definition A_MMAP_ANON_TOL : Z := 0x7cb24.

Section MmapAnon.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  Definition ma_pre_post (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (size name lo : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MmapAnon ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lmm,P,(2.&40.)(3.(2.&8.))(1.(4.(2.&8.))Lfr,(4.(2.&8.))(5.(6.$0.R;.(7.(8.(9.&40.+7<;:<.)(9.&40.(:.O15.-30.))O14.O13.R:.R9.R8.(9.&40.O3.)(9.&40.(;.(<.(:.O4.+???.)+1000.)+1000.))(9.&40.=)(9.&40.(;.(<.(:.O4.+???.)+1000.)+1000.))(9.&40.+3.)(9.&40.+22.)(9.&40.-1.)(9.&40.=)R3.(9.&40.+=>.)(9.&40.$=.)O?.O>.O=.O<.O;.O:.O9.O8.O7.R7.R6.R5.R4.)O6.(9.&40.$>.)(9.&40.+=>.)O5.(?.(2.&40.))R2.(10.$11.)))(5.(12.(13.(14.$15.$15.)(16.$15.$15.O2.O15.)(17.(14.$15.$15.)))O1.R2.)(5.(18.$11.O1.R2.)(5.(19.$11.R2.)(5.(1:.$11.R2.(:.O15.-30.)(13.$1;.(1<.#<.R1.)(13.$1;.(1=.(9.&40.+22.))(13.$1;.(1>.O10.)(13.$1;.(1>.O11.)(13.$1;.(1>.O12.)(13.$1;.(1>.O16.)(17.$1;.))))))))(1?.$11.R2.O2.(:.O15.-30.)))))))))))))))))")
(* [comment removed for export] *).

  #[using="IMG ALWF CSOK"] Lemma mmapanon_pre : ltac2:(CDefT.buildp (gd_tbl_AW_MmapAnon ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)PSP,$15.PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Psize,$15.Pname,$15.Plo,$15.P,(5.(21.=R3.)(22.R3.(23.+2.+28.)))P,(5.(21.=R3.)(21.R3.(23.+2.+2?.)))P,(24.$11.R6.$25.(13.$1;.(1>.(9.&40.$=.))(17.$1;.)))P,(24.$11.R7.$=.(13.$1;.(1>.(9.&40.+1000.))(17.$1;.)))P,(24.$11.R8.$26.(13.$1;.(1>.(9.&40.$27.))(17.$1;.)))P,(24.$11.R9.$28.(13.$1;.(29.(9.&8.=))(17.$1;.)))P,(1?.$11.R:.R7.R=.)P,(22.+65?000.R8.)P,(22.R9.(2:.R?.+140.))P,(22.R10.(23.+2.+3?.))P,(2;.VCS,R;.(2:.R11.R;.))P,(19.$11.R?.)(2<.$11.VAL,VCS,(2=.R2?.R13.R2>.R2=.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R12.R11.R?.R>.R=.R10.)(2>.(8.R2?.(9.&40.R13.)R2>.R2=.R2<.R2;.R2:.R29.R28.(9.&40.R?.)(9.&40.R>.)R19.R18.R17.R16.R15.R14.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R12.(9.&40.$2?.)R11.(?.(2.&40.))R10.(10.$11.)))")
(* [comment removed for export] *).
  Proof.
    pose proof (I : lx_noaceil) as LXNOACEIL.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a2 a3 a4 a5 a6 a7 SP F fc m size name lo
      SZ NM GOT PGS GOTF DEC ST LOIMG SPL SPH SCS MI.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold A_MMAP_ANON_TOL, A_GOT_PAGESZ, A_PAGESZ_CELL, A_GOT_CFLAGS, A_CFLAGS, A_DECORATE in *.
    lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x7b25c] [] 80%N).
    lx_stk_grow_to lo (SP + -48).
    try rewrite (lxw_land_m4096 (size + 4095)) by (clear -SZ; lia).
    stepA_ecall.
    lazymatch goal with STl : stk _ ?mx lo (SP + -48), FRl : rw_cells _ ?mx (SP + -36) ?cs |- _ =>
      destruct (stk_split _ mx lo (SP + -48) (SP + -36)) as [_ STj]; [exact STl| clear -SPL; lia|] || idtac;
      first [ destruct (stk_carve _ mx (SP + -48) (SP + -36) 12 ltac:(match goal with K : stk _ mx (SP + -48) (SP + -36) |- _ => exact K end) ltac:(clear; lia)) as [_ [fr FRj]]
            | fail "carve" ];
      replace (SP + -36 - Z.of_nat 12) with (SP + -48) in FRj by (clear; lia);
      assert (FRa : rw_cells asegs mx (SP + -48) ([CB 12 fr] ++ cs))
        by (apply (proj2 (rw_cells_app _ _ _ _ _)); split; [exact FRj| cbn [cells_size csize Nat.add]; replace (SP + -48 + Z.of_nat 12) with (SP + -36) by (clear; lia); exact FRl]);
      cbn [List.app] in FRa
    end.
    unfold ma_pre_post, A_MMAP_ECALL. lx_exs; lx_ands; [ lx_mseq | assumption | assumption | assumption | exact FRa | assumption ].
  Qed.

  Definition ma_answered (r : word) (SP : Z) (gp tp t0 t1 t2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 : word)
      (F : bvmap 5 word) (fc : bv 32) (size name : Z) (mm : mem) : machine_state := ltac2:(CDefT.buildp (gd_tbl_AW_MmapAnon ()) "(2>.(8.(9.&40.+7<;:<.)(9.&40.(:.O19.-30.))O18.O17.O16.O15.O14.(9.&40.O2.)(9.&40.(;.(<.(:.O3.+???.)+1000.)+1000.))O1:.(9.&40.(;.(<.(:.O3.+???.)+1000.)+1000.))(9.&40.+3.)(9.&40.+22.)(9.&40.-1.)(9.&40.=)O6.(9.&40.+=>.)(9.&40.$=.)O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.)O5.(9.&40.+7;260.)O4.(?.(2.&40.))O1.(10.$11.))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition ma_ret_post (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (res : word) (lo : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MmapAnon ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lmm,P,(2.&40.)(3.(2.&8.))(5.(6.$0.R10.(2>.(8.O15.(9.&40.O14.)O13.O12.R?.R>.R=.O11.O10.O3.R<.R;.R:.R9.R8.R7.R6.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.R5.R4.R3.R2.)O5.(30.O15.)O4.(?.(2.&40.))R1.(10.$11.)))(5.(12.(13.(14.$15.$15.)(16.$15.$15.O2.O14.)(17.(14.$15.$15.)))O1.R1.)(5.(18.$11.O1.R1.)(5.(19.$11.R1.)(1?.$11.R1.O2.O14.))))))))))))))))))))")
(* [comment removed for export] *).

  #[using="IMG ALWF CSOK"] Lemma mmapanon_post_enomem : ltac2:(CDefT.buildp (gd_tbl_AW_MmapAnon ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa6,(2.&40.)PSP,$15.PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Psize,$15.Pname,$15.Plo,$15.Pfr,(4.(2.&8.))P,(5.(21.=R4.)(22.R4.(23.+2.+28.)))P,(1:.$11.R6.(:.R:.-30.)(13.$1;.(1<.#<.R2.)(13.$1;.(1=.(9.&40.+22.))(13.$1;.(1>.R19.)(13.$1;.(1>.R1:.)(13.$1;.(1>.R1;.)(13.$1;.(1>.R21.)(17.$1;.))))))))P,(1?.$11.R7.R4.(:.R;.-30.))P,(22.+65?000.R5.)P,(22.R6.(2:.R=.+140.))P,(22.R>.(23.+2.+3?.))P,(12.(13.(14.$15.$15.)(16.$15.$15.R8.R?.)(17.(14.$15.$15.)))R<.R;.)P,(18.$11.R=.R<.)P,(19.$11.R=.)P,(2;.VCS,R;.(2:.R12.R;.))(2<.$11.VAL,VCS,(31.R2:.R13.R29.R28.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R12.R11.(9.&40.=)R<.R10.)(32.(9.&40.(2:.(23.+2.+40.)+<.))R13.R29.R28.R27.R26.R25.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R12.R11.R>.R=.R?.))")
(* [comment removed for export] *).
  Proof.
    pose proof (I : lx_noaceil) as LXNOACEIL.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 SP F fc m0 mm size name lo fr
      SZ FR ST LOIMG SPL SPH MU WM MI SCS.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    unfold ma_answered, A_PAGESZ_CELL. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 60%N). lx_postw.
  Qed.

  #[using="IMG ALWF CSOK"] Lemma mmapanon_post_ok : ltac2:(CDefT.buildp (gd_tbl_AW_MmapAnon ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa6,(2.&40.)PSP,$15.PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Psize,$15.Pname,$15.Plo,$15.Pfr,(4.(2.&8.))Pa,(2.&40.)P,(5.(21.=R5.)(22.R5.(23.+2.+28.)))P,(21.=(33.&40.R2.))P,(22.(:.(33.&40.R3.)R7.)(34.VhAR,))P,(1:.$11.R9.(:.R=.-30.)(13.$1;.(1<.#<.R5.)(13.$1;.(1=.(9.&40.+22.))(13.$1;.(1>.R1<.)(13.$1;.(1>.R1=.)(13.$1;.(1>.R1>.)(13.$1;.(1>.R24.)(17.$1;.))))))))P,(24.$11.R:.$26.(13.$1;.(1>.(9.&40.$27.))(17.$1;.)))P,(24.$11.R;.$35.(13.$1;.(1>.(9.&40.=))(17.$1;.)))P,(1?.$11.R<.R9.(:.R10.-30.))P,(22.+65?000.R:.)P,(22.R;.(2:.R12.+140.))P,(22.R13.(23.+2.+3?.))P,(12.(13.(14.$15.$15.)(16.$15.$15.R=.R14.)(17.(14.$15.$15.)))R11.R10.)P,(18.$11.R12.R11.)P,(19.$11.R12.)P,(2;.VCS,R10.(2:.R17.R10.))(2<.$11.VAL,VCS,(31.R2?.R18.R2>.R2=.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R17.R16.R?.R11.R15.)(32.R?.R18.R2>.R2=.R2<.R2;.R2:.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R17.R16.R13.R12.R14.))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 SP F fc m0 mm size name lo fr a
      SZ A0 ACE FR GOTF LIM ST LOIMG SPL SPH MU WM MI SCS.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    pose proof (bv_unsigned_in_range 64 a) as AR.
    rewrite <- (Z_to_bv_bv_unsigned a).
    unfold ma_answered, A_PAGESZ_CELL, A_GOT_CFLAGS, A_CFLAGS, A_MMAP_LIMIT in *. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 60%N). lx_postw.
  Qed.
End MmapAnon.

End ARUN_1.
