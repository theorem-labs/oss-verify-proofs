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
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00648cfcac4da219 0 2 0 1 32 1P02c17d5f46a12960 0 2 0 1 26 1P040d42c6b6f31c51 0 2 0 1 32 1P090ef946e63b02b0 0 2 0 1 17 1P1049a6d16f1bcb1a 0 2 0 1 26 1P1377047f91f99462 0 2 0 1 32 1P14961e76031de4fc 0 2 0 1 26 1P1595047781346a8d 0 2 0 1 26 1P15c1f7bdbfd7cf55 0 2 0 1 32 1P164873a1a72ec555 0 2 0 1 32 1P18646aaf7ef60f6c 0 3 1 1 33 1 34 1P1958f230ceb8a51f 0 2 0 1 32 1P1a513526f6c91808 0 2 0 1 14 1P1a779b09bc095d7c 0 2 0 1 26 1P1ab853ddfd534fc7 0 2 0 1 26 1P1c3c2704148e60c8 0 2 0 1 15 1P1d6995e130f2626c 0 2 0 1 32 1P2a4fa7f6bb772c1e 0 2 0 1 16 1P2ab4c82165cff8e9 0 3 1 1 33 1 34 1P2d717bda8ac3ae9b 0 2 0 1 26 1P2f0fe1906005e6a3 0 2 0 1 15 1P31e670f54bda55bc 0 2 0 1 26 1P35d18bec771b156b 0 2 0 1 26 1P3696fb72120eb7a3 0 2 0 1 26 1P3744186099ca092a 0 2 0 1 26 1P37590e8832c45cb3 0 2 0 1 17 1P38f284b1fff3b371 0 2 0 1 26 1N06f65ef662e810f3N0e7af8ea57240572N38535b00e27b38acN3aedbc3c371f8203"%lxh.
Ltac2 gd_tbl_AW_Munmap () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MSsvc"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "ARUN_1.A_MUNMAP_ECALL"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.Munmap.mu_pre_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "ARUN_1.A_UNMAP_OR_DIE"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_MMAP_LIMIT"; "ARUN_1.Munmap.mu_ret_post"; "ARUN_1.Munmap.mu_answered"].

Section ARUN_1. Context {hAR : arun}.
Definition A_UNMAP_OR_DIE : Z := 0x7caa8.
Definition A_MUNMAP_ECALL : Z := 0x7b268.

Section Munmap.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  Definition mu_pre_post (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (addr size raw lo : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Munmap ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lmm,P,(2.&40.)(3.(2.&8.))(1.(4.(2.&8.))Lfr,(4.(2.&8.))(5.(6.$0.R?.(7.(8.(9.&40.+7<:=8.)(9.&40.(:.O16.-30.))O15.O14.R>.R=.R<.(9.&40.O4.)(9.&40.O3.)(9.&40.O5.)(9.&40.O4.)R7.R6.R5.R4.R3.(9.&40.+=7.)(9.&40.O5.)O10.O?.O>.O=.O<.O;.O:.O9.O8.R;.R:.R9.R8.)O7.(9.&40.$;.)(9.&40.+=7.)O6.(<.(2.&40.))R2.(=.$>.)))(5.(?.(10.(11.$12.$12.)(13.$12.$12.O2.O16.)(14.(11.$12.$12.)))O1.R2.)(5.(15.$>.O1.R2.)(5.(16.$>.R2.)(5.(17.$>.R2.(:.O16.-30.)(10.$18.(19.#10.R1.)(10.$18.(1:.O11.)(10.$18.(1:.O12.)(10.$18.(1:.O13.)(10.$18.(1:.O17.)(14.$18.)))))))(1;.$>.R2.O2.(:.O16.-30.)))))))))))))))))))))")
(* [comment removed for export] *).

  #[using="IMG ALWF CSOK"] Lemma munmap_pre : ltac2:(CDefT.buildp (gd_tbl_AW_Munmap ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)PSP,$12.PF,(1<.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Paddr,$12.Psize,$12.Praw,$12.Plo,$12.P,(5.(1=.=R4.)(1=.R4.(1>.+2.+2?.)))P,(5.(1=.=R4.)(1=.R4.(1>.+2.+2?.)))P,(5.(1?.=R4.)(1=.R4.+2.))P,(1;.$>.R8.R4.R;.)P,(1?.+65?000.R5.)P,(1?.R6.(20.R=.+30.))P,(1?.R>.(1>.+2.+3?.))P,(21.VCS,R8.(20.R?.R8.))P,(16.$>.R=.)(22.$>.VAL,VCS,(23.R2=.R11.R2<.R2;.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R10.R?.R=.R<.R;.R:.R>.)(24.(8.R2=.(9.&40.R11.)R2<.R2;.R2:.R29.R28.R27.R26.(9.&40.R=.)(9.&40.R<.)(9.&40.R;.)R16.R15.R14.R13.R12.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R10.(9.&40.$25.)R?.(<.(2.&40.))R>.(=.$>.)))")
(* [comment removed for export] *).
  Proof.
    pose proof (I : lx_noaceil) as LXNOACEIL.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a2 a3 a4 a5 a6 a7 SP F fc m addr size raw lo
      AB SZ RW ST LOIMG SPL SPH SCS MI.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold A_UNMAP_OR_DIE in *. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x7b268] [] 30%N).
    stepA_ecall.
    lazymatch goal with FRh : rw_cells _ ?mx (SP + -32) _, STl : stk _ ?mx lo (SP + -32) |- _ =>
      destruct (stk_split _ mx lo (SP + -48) (SP + -32) STl ltac:(clear -SPL; lia)) as [STlo STj]; clear STl;
      lx_junk STj 16%nat fr FRj; chunk_join FRj FRh FRa end.
    unfold mu_pre_post, A_MUNMAP_ECALL. lx_exs; lx_ands; [ lx_mseq | assumption | assumption | assumption | exact FRa | assumption ].
  Qed.

  Definition mu_answered (SP : Z) (gp tp t0 t1 t2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a2 a3 a4 a5 a6 : word)
      (F : bvmap 5 word) (fc : bv 32) (addr size raw : Z) (mm : mem) : machine_state := ltac2:(CDefT.buildp (gd_tbl_AW_Munmap ()) "(24.(8.(9.&40.+7<:=8.)(9.&40.(:.O1>.-30.))O1=.O1<.O1;.O1:.O19.(9.&40.O3.)(9.&40.O2.)(9.&40.=)(9.&40.O3.)O;.O:.O9.O8.O7.(9.&40.+=7.)(9.&40.O4.)O18.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.)O6.(9.&40.+7;26<.)O5.(<.(2.&40.))O1.(=.$>.))")
(* [comment removed for export] *).

  Definition mu_ret_post (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Munmap ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lmm,P,(2.&40.)(3.(2.&8.))(5.(6.$0.R11.(24.(8.O14.(9.&40.O13.)O12.O11.R10.R?.R>.O10.O?.R=.R<.R;.R:.R9.R8.R7.R6.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.R5.R4.R3.R2.)O4.(26.O14.)O3.(<.(2.&40.))R1.(=.$>.)))(5.(?.(10.(11.$12.$12.)(13.$12.$12.O2.O13.)(14.(11.$12.$12.)))O1.R1.)(5.(15.$>.O1.R1.)(5.(16.$>.R1.)(1;.$>.R1.O2.O13.)))))))))))))))))))))")
(* [comment removed for export] *).

  #[using="IMG ALWF CSOK"] Lemma munmap_post_ok : ltac2:(CDefT.buildp (gd_tbl_AW_Munmap ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)PSP,$12.PF,(1<.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Paddr,$12.Psize,$12.Praw,$12.Plo,$12.Pfr,(4.(2.&8.))P,(5.(1=.=R5.)(1=.R5.(1>.+2.+2?.)))P,(5.(1=.=R5.)(1=.R5.(1>.+2.+2?.)))P,(5.(1?.=R5.)(1=.R5.+2.))P,(17.$>.R9.(:.R=.-30.)(10.$18.(19.#10.R4.)(10.$18.(1:.R20.)(10.$18.(1:.R21.)(10.$18.(1:.R22.)(10.$18.(1:.R28.)(14.$18.)))))))P,(27.$>.R:.$28.(10.$18.(1:.(9.&40.$29.))(14.$18.)))P,(27.$>.R;.$2:.(10.$18.(1:.(9.&40.=))(14.$18.)))P,(1;.$>.R<.R8.(:.R10.-30.))P,(1?.+65?000.R9.)P,(1?.R:.(20.R12.+30.))P,(1?.R13.(1>.+2.+3?.))P,(?.(10.(11.$12.$12.)(13.$12.$12.R<.R14.)(14.(11.$12.$12.)))R11.R10.)P,(15.$>.R12.R11.)P,(16.$>.R12.)P,(21.VCS,R?.(20.R17.R?.))(22.$>.VAL,VCS,(2;.R33.R18.R32.R31.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R17.R16.R10.R15.)(2<.R18.R32.R31.R30.R2?.R2>.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R17.R16.R13.R12.R11.R14.))")
(* [comment removed for export] *).
  Proof.
    pose proof (I : lx_noaceil) as LXNOACEIL.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a2 a3 a4 a5 a6 SP F fc m0 mm addr size raw lo fr
      AB SZ RW FR GOTF LIM ST LOIMG SPL SPH MU WM MI SCS.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    unfold mu_answered, A_GOT_CFLAGS, A_CFLAGS, A_MMAP_LIMIT in *. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 40%N). lx_postw.
  Qed.
End Munmap.

End ARUN_1.
