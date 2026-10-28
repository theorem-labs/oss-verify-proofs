(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_MmapFixed AW_MmapAnon AW_MmapDie.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0094bd70c7b61078 0 2 0 1 30 1P0177ed10381b5260 0 2 0 1 30 1P040ba7e61bef1d0f 0 2 0 1 30 1P04911dff59af04f6 0 2 0 1 30 1P0514c7c352e9faa6 0 2 0 1 39 1P05392224abb8e6a9 0 3 1 1 31 1 32 1P05f24100694020b9 0 3 1 1 44 1 45 1P06456048b5c115ce 0 3 1 1 31 1 32 1P066429d2fa3fefb5 0 2 0 1 43 1P069f5e6ae1abd2ff 0 3 1 1 31 1 32 1P07aa301aa7599c2f 0 2 0 1 30 1P07d87c8750c07a39 0 2 0 1 29 1P08002cfd0fe83760 0 2 0 1 38 1P088e3fbc5698b3e8 0 3 1 1 31 1 32 1P08a530baf9f3a72c 0 2 0 1 30 1P0900942a17bafd8f 0 3 1 1 31 1 32 1P092cac01cf7c4d0b 0 3 1 1 31 1 32 1P095128cc22c1d8a4 0 2 0 1 43 1P099073adf5cfc57d 0 3 1 1 31 1 32 1P09abfa7f5602a03b 0 3 1 1 31 1 32 1P09acb55f15ec338b 0 2 0 1 30 1P09dac39da546dc8b 0 3 1 1 31 1 32 1P0a0506960fa52638 0 3 1 1 39 1 40 1P0a0d4da9ac549c54 0 3 1 1 31 1 32 1P0ac7af0c3bb8c54b 0 2 0 1 30 1P0b8ea3f5406c57a8 0 2 0 1 30 1P0bb1a1b6c5a398c9 0 2 0 1 30 1P0c688b2da5c972e9 0 3 1 1 31 1 32 1P0dbb49e6e2d328a5 0 2 0 1 28 1P0e1956cb0220234d 0 2 0 1 30 1P0e617d97a463752d 0 2 0 1 38 1P0e84293b6f9b52d9 0 2 0 1 30 1P0fb84a9f632c982e 0 2 0 1 30 1P103a417c85405b3f 0 2 0 1 30 1P10e779f86c18ebbc 0 2 0 1 30 1P111b6411041486dd 0 2 0 1 30 1P113a529c6938a77f 0 3 1 1 31 1 32 1P114979148709ff26 0 3 1 1 31 1 32 1P115fef61bfee2a74 0 2 0 1 30 1P118419a0858861ac 0 2 0 1 43 1P11bbfa6eacd1896c 0 2 0 1 43 1P11d19b00ce9e7ff0 0 2 0 1 30 1P12c10495b10fc474 0 2 0 1 30 1P12e62a91ab7d846c 0 2 0 1 38 1P12fc7af75fdbb8c4 0 2 0 1 30 1P141084a2e8ea652c 0 2 0 1 43 1P1417a059aec4b41b 0 3 1 1 39 1 40 1P14753353d565d8a2 0 2 0 1 30 1P1546a8358e57902e 0 2 0 1 6 1P15ba18ee65227d12 0 3 1 1 31 1 32 1P15e634270c03ba0d 0 2 0 1 30 1P16a694b98128f523 0 3 1 1 31 1 32 1P17d3e8101ed97be3 0 2 0 1 43 1P185bd98c0bc996f2 0 2 0 1 30 1P193a7ff08e228095 0 2 0 1 38 1P194c707e0ee97523 0 3 1 1 31 1 32 1P1a0a29058279015c 0 3 1 1 31 1 32 1P1aa4d4d5bf8b963e 0 2 0 1 30 1P1aa928f576c95eef 0 2 0 1 30 1P1ba8e59aec5e2909 0 2 0 1 39 1P1bd3d5b0db7f816c 0 3 1 1 31 1 32 1P1c4de053c600d013 0 2 0 1 43 1P1d23ce6c5172527e 0 3 1 1 31 1 32 1P1d26b4444d859007 0 2 0 1 38 1P1d47c8e57856b6c2 0 2 0 1 43 1P1f1ba24f916012bd 0 3 1 1 31 1 32 1P2064ccc48bf6d2b4 0 2 0 1 30 1P2227b30ef7cf6380 0 2 0 1 30 1P229272dbecbf71af 0 3 1 1 31 1 32 1P22df06b05933b353 0 3 1 1 31 1 32 1P234d1f978df18623 0 2 0 1 43 1P23a6e906a4c43fa4 0 2 0 1 30 1P23f6d9f4d1693383 0 2 0 1 6 1P2416f70008ba063a 0 2 0 1 43 1P2498bc0891003581 0 2 0 1 30 1P24fc14aeb1f135f9 0 2 0 1 30 1P2521eb692068a1b2 0 3 1 1 31 1 32 1P253fbd4ccc70e9e7 0 3 1 1 31 1 32 1P258779662afe2c8e 0 3 1 1 44 1 45 1P26ff17323a4a5f73 0 2 0 1 30 1P2707269100c674be 0 2 0 1 30 1P282d0abe522f4658 0 2 0 1 43 1P292fa7ecaaa263fd 0 2 0 1 30 1P299091d6c1afd63f 0 2 0 1 30 1P29dc431e14223ffb 0 2 0 1 38 1P29ebd02055511175 0 2 0 1 30 1P2a47c10a1dbde75e 0 3 1 1 39 1 40 1P2a5d37fcf20cebf0 0 2 0 1 30 1P2a7a8a61d324c2e0 0 3 1 1 31 1 32 1P2ae91eab751a116e 0 3 1 1 31 1 32 1P2b363243750412cc 0 3 1 1 31 1 32 1P2b56d4122f64ac04 0 3 1 1 31 1 32 1P2ba3cd016d5badba 0 2 0 1 30 1P2c5d842265e28fb6 0 2 0 1 30 1P2c985aa7027b40d8 0 2 0 1 30 1P2db148c9efad7490 0 2 0 1 30 1P2f6d3b1eaf472089 0 2 0 1 30 1P2f763000ef2128f6 0 3 1 1 31 1 32 1P2f7e64e0891f07b8 0 2 0 1 30 1P2fb4587009eee0a7 0 3 1 1 44 1 45 1P2fd022a99d2082ba 0 3 1 1 31 1 32 1P30210436cdd1fc9d 0 2 0 1 30 1P304e212871be652a 0 2 0 1 43 1P30dca1d299b02c3c 0 2 0 1 30 1P3151099aa14ebd0a 0 3 1 1 31 1 32 1P3163a894bd78468e 0 2 0 1 43 1P31d47694bd7abeda 0 3 1 1 31 1 32 1P3226dd0576f38092 0 2 0 1 30 1P3250b276504788a8 0 2 0 1 30 1P32519ad79bf48cb9 0 2 0 1 30 1P327c1eda93bcae25 0 3 1 1 31 1 32 1P338425a8411badc3 0 2 0 1 30 1P346bef5ac9bef73f 0 2 0 1 30 1P34c8fe205b396f36 0 2 0 1 30 1P34edc49dd77b159a 0 2 0 1 43 1P359d068de299aa3e 0 2 0 1 30 1P363346392772ae17 0 2 0 1 30 1P3698ab76f8f3e4b5 0 3 1 1 31 1 32 1P36ebd747b633275b 0 2 0 1 30 1P37c8c49918dfc1ab 0 2 0 1 30 1P37f1e64c24576f97 0 2 0 1 30 1P3818c0a59bde5d29 0 3 1 1 31 1 32 1P382f6bf2dd373733 0 3 1 1 31 1 32 1P385162f15788065e 0 3 1 1 31 1 32 1P38c601bf453856e7 0 2 0 1 30 1P399580514a85a88f 0 2 0 1 30 1P39c4a31b39ad4ffb 0 2 0 1 43 1P39e75150d444bf54 0 2 0 1 39 1P3a411ed2778125e9 0 3 1 1 31 1 32 1P3a651eb5f3a42d26 0 2 0 1 37 1P3aab847dbabf41b5 0 3 1 1 31 1 32 1P3c1d0b0585f00989 0 2 0 1 30 1P3c96e63920aadef4 0 2 0 1 30 1P3c9e860a0dca0e7a 0 2 0 1 43 1P3d47209ecd9e8a1a 0 2 0 1 28 1P3d5730e238899851 0 3 1 1 31 1 32 1P3da54d8002f3664d 0 2 0 1 38 1P3e2587108e105ab7 0 2 0 1 30 1P3e48004312bf393c 0 2 0 1 38 1P3e633e9244f43697 0 3 1 1 31 1 32 1P3efbca2f55c5baba 0 3 1 1 44 1 45 1P3f5a538f27e629d1 0 2 0 1 30 1P3f8d963b7657360b 0 2 0 1 30 1P3f9e58a0150d1864 0 3 1 1 31 1 32 1P3fef0ef0bf339f21 0 2 0 1 30 1N042bfa610124fcf7N05fa7f3c8d3afe24N1585196e3cbdbdf9N339d9a40ccd5c6e2N3c6bb6a870265684"%lxh.
Ltac2 gd_tbl_AW_MmapFixedNR () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MSsvc"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_PAGESZ_CELL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_MMAP_ECALL"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_GOT_PAGESZ"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.MmapFixedNR.mfnr_pre_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "ARUN_1.A_MMAP_FIXED_SUPER_NR"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_SEALED2"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_DYING"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_DYING"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapDie.die_post"; "ARUN_1.A_SPIN_MMAPFNR"; "ARUN_1.MmapFixedNR.mfnr_answered"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_MMAP_LIMIT"; "ARUN_1.A_MADV_FLAG"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "ARUN_1.MmapFixedNR.mfnr_ret_post"].

Section ARUN_1. Context {hAR : arun}.
Definition A_MMAP_FIXED_SUPER_NR : Z := 0x085048.
Definition A_SPIN_MMAPFNR : Z := 0x084fdc.
(* [comment removed for export] *)
Definition A_MADV_FLAG : Z := 0x19b61c.     (* [comment removed for export] *)

Section MmapFixedNR.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  Definition mfnr_pre_post (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (addr size lo : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MmapFixedNR ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lmm,P,(2.&40.)(3.(2.&8.))(1.(4.(2.&8.))Lfr0,(4.(2.&8.))(1.(4.(2.&8.))Lfr1,(4.(2.&8.))(5.(6.$0.R<.(7.(8.(9.&40.+7<:80.)(9.&40.(:.O15.-80.))O14.O13.R;.R:.R9.(9.&40.+3.)(9.&40.(;.(<.(:.O3.+???.)+1000.)+1000.))(9.&40.O4.)(9.&40.(;.(<.(:.O3.+???.)+1000.)+1000.))(9.&40.+3.)(9.&40.+4032.)(9.&40.-1.)(9.&40.=)R4.(9.&40.+=>.)(9.&40.O4.)(9.&40.$=.)O>.O=.O<.O;.O:.O9.O8.O7.R8.R7.R6.R5.)O6.(9.&40.$>.)(9.&40.+=>.)O5.(?.(2.&40.))R3.(10.$11.)))(5.(12.(13.(14.$15.$15.)(16.$15.$15.O2.O15.)(17.(14.$15.$15.)))O1.R3.)(5.(18.$11.O1.R3.)(5.(19.$11.R3.)(5.(1:.$11.R3.(:.O15.-20.)(13.$1;.(1<.O10.)(13.$1;.(1<.O11.)(13.$1;.(1<.O12.)(13.$1;.(1<.O16.)(17.$1;.))))))(5.(1:.$11.R3.(:.O15.-50.)(13.$1;.(1=.#8.R2.)(13.$1;.(1<.O?.)(13.$1;.(1<.O10.)(13.$1;.(1<.(9.&40.O4.))(13.$1;.(1<.(9.&40.O3.))(13.$1;.(1<.(9.&40.+85068.))(17.$1;.))))))))(5.(1:.$11.R3.(:.O15.-80.)(13.$1;.(1=.#<.R1.)(13.$1;.(1>.(9.&40.+4032.))(13.$1;.(1<.(9.&40.O4.))(13.$1;.(1<.(9.&40.=))(13.$1;.(1<.(9.&40.(;.(<.(:.O3.+???.)+1000.)+1000.)))(13.$1;.(1<.(9.&40.+84?:4.))(17.$1;.))))))))(1?.$11.R3.O2.(:.O15.-80.))))))))))))))))))))")
(* [comment removed for export] *).

  Lemma mfnr_pre : ltac2:(CDefT.buildp (gd_tbl_AW_MmapFixedNR ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)PSP,$15.PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Paddr,$15.Psize,$15.Plo,$15.P,(5.(21.=R3.)(21.R3.(22.+2.+2?.)))P,(6.$15.(23.R4.+1000.)=)P,(5.(21.=R4.)(24.R4.(22.+2.+28.)))P,(25.$11.R7.$26.(13.$1;.(1<.(9.&40.$=.))(17.$1;.)))P,(25.$11.R8.$=.(13.$1;.(1<.(9.&40.+1000.))(17.$1;.)))P,(1?.$11.R9.R6.R<.)P,(24.+65?000.R7.)P,(24.R8.(27.R>.+190.))P,(24.R?.(22.+2.+3?.))P,(28.VCS,R:.(27.R10.R:.))P,(19.$11.R>.)(29.$11.VAL,VCS,(2:.R2=.R12.R2<.R2;.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R11.R10.R>.R=.R<.R?.)(2;.(8.R2=.(9.&40.R12.)R2<.R2;.R2:.R29.R28.R27.R26.(9.&40.R>.)(9.&40.R=.)(9.&40.=)R17.R16.R15.R14.R13.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R11.(9.&40.$2<.)R10.(?.(2.&40.))R?.(10.$11.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a3 a4 a5 a6 a7 SP F fc m addr size lo
      AB AAL SZ GOT PGS ST LOIMG SPL SPH SCS MI.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold A_MMAP_FIXED_SUPER_NR, A_GOT_PAGESZ, A_PAGESZ_CELL in *. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x7b25c] [] 100%N).
    lx_stk_grow_to lo (SP + -128).
    try rewrite (Z.land_comm (-4096) addr) in *.
    try (rewrite (lxw_land_m4096 addr) in * by (clear -AB; lia); replace (addr / 4096 * 4096) with addr in * by (pose proof (Z.div_mod addr 4096 ltac:(lia)); clear -H0 AAL; lia)).
    try rewrite (lxw_land_m4096 (size + 4095)) in * by (clear -SZ; lia).
    stepA_ecall.
    lazymatch goal with FRa : rw_cells _ ?mx (SP + -72) _, STa : stk _ ?mx (SP + -80) (SP + -72),
                        FRb : rw_cells _ ?mx (SP + -116) _, STb : stk _ ?mx (SP + -128) (SP + -116) |- _ =>
      chunk_split FRa 5%nat FRa5 FRtop; replace (SP + -72 + 40) with (SP + -32) in FRtop by (clear; lia);
      lx_junk STa 8%nat fr0 FRj0; chunk_join FRj0 FRa5 FRmid;
      lx_junk STb 12%nat fr1 FRj1; chunk_join FRj1 FRb FRbot end.
    unfold mfnr_pre_post, A_MMAP_ECALL, A_PAGESZ_CELL. lx_exs; lx_ands;
      [ lx_mseq | assumption | assumption | assumption | exact FRtop | exact FRmid | exact FRbot | assumption ].
  Qed.
  Definition mfnr_answered (r : word) (SP : Z) (gp tp t0 t1 t2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 : word)
      (F : bvmap 5 word) (fc : bv 32) (addr size : Z) (mm : mem) : machine_state := ltac2:(CDefT.buildp (gd_tbl_AW_MmapFixedNR ()) "(2;.(8.(9.&40.+7<:80.)(9.&40.(:.O18.-80.))O17.O16.O15.O14.O13.(9.&40.+3.)(9.&40.(;.(<.(:.O2.+???.)+1000.)+1000.))O19.(9.&40.(;.(<.(:.O2.+???.)+1000.)+1000.))(9.&40.+3.)(9.&40.+4032.)(9.&40.-1.)(9.&40.=)O6.(9.&40.+=>.)(9.&40.O3.)(9.&40.$=.)O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.)O5.(9.&40.+7;260.)O4.(?.(2.&40.))O1.(10.$11.))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Lemma mfnr_post_die : ltac2:(CDefT.buildp (gd_tbl_AW_MmapFixedNR ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa6,(2.&40.)PSP,$15.PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Paddr,$15.Psize,$15.Plo,$15.Pfr0,(4.(2.&8.))Pfr1,(4.(2.&8.))P,(5.(21.=R5.)(21.R5.(22.+2.+2?.)))P,(5.(21.=R5.)(24.R5.(22.+2.+28.)))P,(1:.$11.R8.(:.R<.-20.)(13.$1;.(1<.R1;.)(13.$1;.(1<.R1<.)(13.$1;.(1<.R1=.)(13.$1;.(1<.R23.)(17.$1;.))))))P,(1:.$11.R9.(:.R=.-50.)(13.$1;.(1=.#8.R5.)(13.$1;.(1<.R1;.)(13.$1;.(1<.R1<.)(13.$1;.(1<.(9.&40.R8.))(13.$1;.(1<.(9.&40.R7.))(13.$1;.(1<.(9.&40.+85068.))(17.$1;.))))))))P,(1:.$11.R:.(:.R>.-80.)(13.$1;.(1=.#<.R5.)(13.$1;.(1>.(9.&40.+4032.))(13.$1;.(1<.(9.&40.R9.))(13.$1;.(1<.(9.&40.=))(13.$1;.(1<.(9.&40.(;.(<.(:.R8.+???.)+1000.)+1000.)))(13.$1;.(1<.(9.&40.+84?:4.))(17.$1;.))))))))P,(25.$11.R;.$2=.(13.$1;.(1<.(9.&40.+1.))(17.$1;.)))P,(25.$11.R<.$2>.(13.$1;.(1<.(9.&40.$2?.))(17.$1;.)))P,(25.$11.R=.$2?.(13.$1;.(1>.(9.&40.=))(17.$1;.)))P,(1?.$11.R>.R;.(:.R12.-80.))P,(24.+65?000.R<.)P,(24.R=.(27.R14.+190.))P,(24.R15.(22.+2.+3?.))P,(12.(13.(14.$15.$15.)(16.$15.$15.R?.R16.)(17.(14.$15.$15.)))R13.R12.)P,(18.$11.R14.R13.)P,(19.$11.R14.)P,(28.VCS,R12.(27.R19.R12.))(29.$11.VAL,VCS,(30.R18.$31.)(32.(9.&40.(27.(22.+2.+40.)+<.))R1:.R30.R2?.R2>.R2=.R2<.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R19.R18.R15.R14.R16.))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 SP F fc m0 mm addr size lo fr0 fr1
      AB SZ FR FR0 FR1 SEAL GDY DY ST LOIMG SPL SPH MU WM MI SCS.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    unfold mfnr_answered, A_PAGESZ_CELL, A_GOT_SEALED2, A_GOT_DYING, A_DYING, A_SPIN_MMAPFNR in *. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x084fdc] [] 60%N).
    apply evtA_done. unfold die_post. do 3 eexists. reflexivity.
  Qed.

  Definition mfnr_ret_post (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MmapFixedNR ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lmm,P,(2.&40.)(3.(2.&8.))(5.(6.$0.R10.(2;.(8.O14.(9.&40.O13.)O12.O11.R?.R>.R=.O10.O?.(9.&40.+1.)R<.R;.R:.R9.R8.R7.R6.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.R5.R4.R3.R2.)O4.(33.O14.)O3.(?.(2.&40.))R1.(10.$11.)))(5.(12.(13.(14.$15.$15.)(16.$15.$15.O2.O13.)(17.(14.$15.$15.)))O1.R1.)(5.(18.$11.O1.R1.)(5.(19.$11.R1.)(1?.$11.R1.O2.O13.))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Lemma mfnr_post_ok : ltac2:(CDefT.buildp (gd_tbl_AW_MmapFixedNR ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa6,(2.&40.)PSP,$15.PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Paddr,$15.Psize,$15.Plo,$15.Pfr0,(4.(2.&8.))Pfr1,(4.(2.&8.))Pmadv,(2.&8.)P,(5.(21.=R6.)(21.R6.(22.+2.+2?.)))P,(5.(21.=R6.)(24.R6.(22.+2.+28.)))P,(1:.$11.R9.(:.R=.-20.)(13.$1;.(1<.R1<.)(13.$1;.(1<.R1=.)(13.$1;.(1<.R1>.)(13.$1;.(1<.R24.)(17.$1;.))))))P,(1:.$11.R:.(:.R>.-50.)(13.$1;.(1=.#8.R6.)(13.$1;.(1<.R1<.)(13.$1;.(1<.R1=.)(13.$1;.(1<.(9.&40.R9.))(13.$1;.(1<.(9.&40.R8.))(13.$1;.(1<.(9.&40.+85068.))(17.$1;.))))))))P,(1:.$11.R;.(:.R?.-80.)(13.$1;.(1=.#<.R6.)(13.$1;.(1>.(9.&40.+4032.))(13.$1;.(1<.(9.&40.R:.))(13.$1;.(1<.(9.&40.=))(13.$1;.(1<.(9.&40.(;.(<.(:.R9.+???.)+1000.)+1000.)))(13.$1;.(1<.(9.&40.+84?:4.))(17.$1;.))))))))P,(25.$11.R<.$34.(13.$1;.(1<.(9.&40.$35.))(17.$1;.)))P,(25.$11.R=.$36.(13.$1;.(1<.(9.&40.=))(17.$1;.)))P,(25.$11.R>.$37.(13.$1;.(38.R8.)(17.$1;.)))P,(25.$11.R?.$2=.(13.$1;.(1<.(9.&40.+1.))(17.$1;.)))P,(1?.$11.R10.R=.(:.R14.-80.))P,(24.+65?000.R>.)P,(24.R?.(27.R16.+190.))P,(24.R17.(22.+2.+3?.))P,(12.(13.(14.$15.$15.)(16.$15.$15.R11.R18.)(17.(14.$15.$15.)))R15.R14.)P,(18.$11.R16.R15.)P,(19.$11.R16.)P,(28.VCS,R14.(27.R1;.R14.))(29.$11.VAL,VCS,(39.R33.R1<.R32.R31.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R1;.R1:.R15.R19.)(32.(9.&40.R17.)R1<.R32.R31.R30.R2?.R2>.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1;.R1:.R17.R16.R18.))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 SP F fc m0 mm addr size lo fr0 fr1 madv
      AB SZ FR FR0 FR1 GOTF LIM MADV SEAL ST LOIMG SPL SPH MU WM MI SCS.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    pose proof (bv_unsigned_in_range 8 madv) as MR.
    unfold mfnr_answered, A_PAGESZ_CELL, A_GOT_CFLAGS, A_CFLAGS, A_MMAP_LIMIT, A_MADV_FLAG, A_GOT_SEALED2 in *.
    lx_c1_norm. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 80%N). lx_postw.
  Qed.
End MmapFixedNR.

End ARUN_1.
