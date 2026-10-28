(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00fba123e18a236f 0 3 1 1 35 1 36 1P017ba5726e68f59e 0 2 0 1 34 1P018c3648bf5947d9 0 3 1 1 35 1 36 1P01aacef0d8cd2694 0 3 1 1 35 1 36 1P020b61f02007f3d0 0 2 0 1 34 1P028f6b50272ba2d2 0 2 0 1 34 1P02f631a18ee6d5f6 0 3 1 1 35 1 36 1P02fdf21f664b7471 0 2 0 1 26 1P030bf61519b9adb9 0 2 0 1 34 1P03c7164e79a3675e 0 2 0 1 34 1P048740c1e5d9a4fc 0 3 1 1 33 1 34 1P04a35eb45746727f 0 3 1 1 35 1 36 1P0555cac0769373ac 0 3 1 1 35 1 36 1P055d48fe816296f1 0 3 1 1 35 1 36 1P0657e096ed27043a 0 2 0 1 32 1P07099c61734abbcb 0 2 0 1 34 1P072a925a785f8af4 0 2 0 1 28 1P075d9ee5c5a632d0 0 2 0 1 33 1P075f5a0806b1f7be 0 3 1 1 35 1 36 1P07a0fdc8eaf95bb6 0 2 0 1 34 1P07b7ae0005193845 0 2 0 1 34 1P07be2c296ea993e3 0 3 1 1 35 1 36 1P07c8720db497bcd9 0 2 0 1 34 1P0852fbd3b05ac557 0 2 0 1 32 1P08e9d29d8390606b 0 3 1 1 35 1 36 1P092f07ed0ecb0a74 0 2 0 1 34 1P0955c1e98e4d50c5 0 2 0 1 34 1P09f50599a0d9e66f 0 2 0 1 34 1P0a0038b3d781706d 0 2 0 1 34 1P0a37fb38336c9ee3 0 2 0 1 34 1P0a804b7574e5b0c7 0 3 1 1 35 1 36 1P0c08848cb1016677 0 3 1 1 35 1 36 1P0cd1b815f7f5a422 0 3 1 1 35 1 36 1P0e31534727ade9b7 0 3 1 1 35 1 36 1P0edd7a3df3d476e4 0 2 0 1 32 1P0ede80084f599f59 0 2 0 1 34 1P0f0a6df9b46a7c00 0 2 0 1 32 1P0f64f03491db846a 0 2 0 1 34 1P0f75458eef239024 0 2 0 1 34 1P0f901b7e1ee87f9d 0 2 0 1 34 1P10077c9e47eef272 0 3 1 1 35 1 36 1P103a3bfe20393983 0 2 0 1 26 1P1058debe0555087f 0 2 0 1 28 1P105c483237dee95c 0 2 0 1 27 1P1077fb290af8de2c 0 3 1 1 35 1 36 1P108c418b4ce3c8d0 0 3 1 1 35 1 36 1P10e4b1cd7b29f293 0 2 0 1 34 1P11e4f0ebb4f3f9d1 0 2 0 1 34 1P12534aaa0ffe6019 0 3 1 1 35 1 36 1P12924810aa14b2e0 0 2 0 1 32 1P12d184f87fa6e47e 0 2 0 1 34 1P12fa7d7237c1f931 0 2 0 1 34 1P1316c17f1a8e29e5 0 3 1 1 35 1 36 1P13ab5305e20d53c3 0 3 1 1 35 1 36 1P13cdf2d3f6770805 0 3 1 1 35 1 36 1P13f6f61109e8c8b8 0 3 1 1 35 1 36 1P153c05d25008045b 0 2 0 1 34 1P1574e9814c04f84e 0 3 1 1 35 1 36 1P15bf0bdc921907d8 0 3 1 1 35 1 36 1P15eb574c0e77944f 0 3 1 1 35 1 36 1P166a0e6765df34b7 0 2 0 1 32 1P16822fa60089ebf5 0 3 1 1 35 1 36 1P16d48dbd66bb1d7d 0 2 0 1 34 1P192343966976b7f2 0 3 1 1 35 1 36 1P19946565317ed6aa 0 3 1 1 35 1 36 1P19bba239480a276e 0 3 0 1 20 1 29 1P19dd7f31d0b68d9c 0 2 0 1 32 1P19e1bd3b581cbb04 0 3 1 1 35 1 36 1P1ad7b16052fa44b1 0 2 0 1 28 1P1b0d4dfea9c5054c 0 2 0 1 26 1P1b470d32c9a743bc 0 3 1 1 33 1 34 1P1b823ee58f199cb5 0 2 0 1 28 1P1bf1a1b65a34f977 0 3 1 1 35 1 36 1P1cec8d3759c5ceb8 0 3 1 1 35 1 36 1P1d859d2e78a8726d 0 3 1 1 35 1 36 1P1e66a5439ad01bbf 0 3 1 1 35 1 36 1P1e6c187cc6156a11 0 3 1 1 35 1 36 1P1e7c90d4be1d5bd9 0 2 0 1 2 1P201b093cf1e89f70 0 2 0 1 26 1P2177391b2f30fecb 0 2 0 1 26 1P2187749352ffa2ab 0 2 0 1 34 1P21f9d430d0806021 0 2 0 1 34 1P22300d43c109f3aa 0 2 0 1 34 1P224415ea27b087a0 0 3 1 1 35 1 36 1P22e6a5c49c16d43b 0 2 0 1 34 1P234b445675e69b39 0 2 0 1 34 1P237c6b2df1866c8b 0 2 0 1 34 1P237e7648545e49f4 0 2 0 1 28 1P24039840c896c90d 0 2 0 1 28 1P24a1f5d4a65859b8 0 2 0 1 28 1P24b83d8cf4966090 0 3 1 1 35 1 36 1P25ca099aea9533b3 0 2 0 1 26 1P27034edc426189be 0 2 0 1 34 1P27479a798da74896 0 3 0 1 20 1 29 1P274d379c94be1791 0 3 1 1 35 1 36 1P276d0ab77ca61f42 0 2 0 1 2 1P27c77d8a3769ce18 0 2 0 1 34 1P2801c7aead833dc9 0 2 0 1 34 1P295c3a7c0ea83706 0 2 0 1 34 1P29698b2f2389c440 0 3 1 1 35 1 36 1P29c885e5424e8d19 0 2 0 1 34 1P2a12240b5993a245 0 3 1 1 35 1 36 1P2a257b607b007dd0 0 2 0 1 34 1P2a43c4c15f1888c9 0 3 1 1 35 1 36 1P2a5770917ecafe50 0 2 0 1 32 1P2adfc93b31e9ba9e 0 3 1 1 35 1 36 1P2aff0e3bb9cf386d 0 3 1 1 35 1 36 1P2b2082e87e5b60c5 0 3 1 1 35 1 36 1P2b3c883b9c6bd69b 0 2 0 1 34 1P2b74939da93570e6 0 3 1 1 35 1 36 1P2b7ab8c113f7cda5 0 3 1 1 35 1 36 1P2cc17921c3429f79 0 2 0 1 34 1P2d49262447ff52d1 0 3 1 1 35 1 36 1P2d49dcf9a81b5eca 0 3 1 1 35 1 36 1P2dbeb1a49f058b6a 0 3 1 1 35 1 36 1P2e494426917c4860 0 3 1 1 35 1 36 1P2e9a4071df06dbce 0 2 0 1 34 1P2f0871931ef223e0 0 3 1 1 35 1 36 1P2f350d3d9f4904c6 0 2 0 1 34 1P2fc44e382d4e51e5 0 2 0 1 34 1P30aae131bea7433c 0 3 1 1 35 1 36 1P31a3ca1355fb9a7d 0 3 1 1 35 1 36 1P32276115789599e0 0 3 1 1 35 1 36 1P326c8db2a930fa62 0 3 1 1 35 1 36 1P32acbd0cf3ef57c3 0 2 0 1 26 1P32b2f9a5b928eaed 0 2 0 1 34 1P32d8104ea9a55444 0 2 0 1 32 1P32e7aff1e34d9ca1 0 2 0 1 34 1P333373f696fe682e 0 2 0 1 21 1P340045f7270b4a00 0 2 0 1 34 1P341838dd6a582f3b 0 2 0 1 34 1P342914c6220862be 0 2 0 1 28 1P34b51a89a4bb2fa4 0 2 0 1 34 1P34e97a685d4d1740 0 2 0 1 27 1P3566a9b3ce67f91a 0 2 0 1 26 1P360e6a63b3ce0adc 0 3 1 1 35 1 36 1P3615427d65d7183d 0 2 0 1 4 1P370ef7da2f45376f 0 2 0 1 28 1P3738fc5746218a5d 0 2 0 1 25 1P378a78719f7a2802 0 2 0 1 34 1P37d56f12e539678c 0 3 1 1 35 1 36 1P3902b7479935c040 0 2 0 1 34 1P395fc8032b1afe59 0 2 0 1 34 1P3994c09c7d416f92 0 2 0 1 26 1P39d4573049b629b8 0 3 1 1 35 1 36 1P3a1b71abd351cdbe 0 2 0 1 34 1P3a57b332372075d1 0 2 0 1 28 1P3b07c6ecc1652de5 0 3 1 1 35 1 36 1P3bd03b61ba1c6ec8 0 2 0 1 34 1P3c3bab62a086fbed 0 2 0 1 4 1P3c837db5228d4615 0 2 0 1 26 1P3cbe954fc808cfa5 0 2 0 1 34 1P3dbf81156625af57 0 3 1 1 35 1 36 1P3dbfcb2e169050a4 0 2 0 1 34 1P3e9e2c5e4e89e87e 0 3 1 1 35 1 36 1P3f214f7e38028b52 0 3 1 1 35 1 36 1P3f425a5c6e0b55af 0 2 0 1 34 1P3fa4a4cb4ab412fc 0 3 1 1 35 1 36 1N00d13a5f2b89fc51N0bae2ead9c873499N21e965a262ecf5f9N26d9fd3ff7c2322dN28f9d72c92a3533fN2ce7ffa447c829dbN3bd68f131704b699"%lxh.
Ltac2 gd_tbl_AW_MmapFixed () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MSsvc"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_PAGESZ_CELL"; "ARUN_1.A_MMAP_ECALL"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_GOT_PAGESZ"; "ARUN_1.A_GOT_CFLAGS"; "ARUN_1.A_CFLAGS"; "ARUN_1.A_DECORATE"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.MmapFixed.mf_pre_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "ARUN_1.A_MMAPFIXED_TOL"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "ARUN_1.MmapFixed.mf_ret_post"; "ARUN_1.MmapFixed.mf_answered"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "ARUN_1.A_MMAP_LIMIT"; "ARUN_1.A_MAP_RET1"; "ARUN_1.MmapFixed.map_pre_post"; "ARUN_1.A_RAR_MAP"; "ARUN_1.A_GOT_SEALED2"; "ARUN_1.MmapFixed.map_norep_svc"; "ARUN_1.MmapFixed.map_norep_answered"; "Corelib.Init.Logic.not"; "ARUN_1.A_GOT_DYING"; "ARUN_1.A_DYING"; "ARUN_1.MmapFixed.map_spin_post"].

Section ARUN_1. Context {hAR : arun}.
Definition A_RAR_MAP : Z := 0x0851a8.        (* [comment removed for export] *)
Definition A_MMAPFIXED_TOL : Z := 0x7d0e8.  (* [comment removed for export] *)
Definition A_MAP_RET1 : Z := 0x851d4.       (* [comment removed for export] *)
Definition A_MAP_SPIN : Z := 0x852dc.       (* [comment removed for export] *)
Definition A_GOT_SEALED2 : Z := 0x0f5e90.   (* [comment removed for export] *)
Definition A_GOT_DYING : Z := 0x0f5e98.     (* [comment removed for export] *)
Definition A_DYING : Z := 0x19b51c.         (* [comment removed for export] *)
Definition A_MMAP_ECALL : Z := 0x7b25c.
Definition A_GOT_CFLAGS : Z := 0x0f5e40.
Definition A_CFLAGS : Z := 0x19b528.         (* [comment removed for export] *)
Definition A_DECORATE : Z := 0x19b62c.       (* [comment removed for export] *)
Definition A_MMAP_LIMIT : Z := 0x19b5b8.     (* [comment removed for export] *)

Section MmapFixed.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition mf_pre_post (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (addr size name lo : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MmapFixed ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lmm,P,(2.&40.)(3.(2.&8.))(1.(4.(2.&8.))Lfr,(4.(2.&8.))(5.(6.$0.R;.(7.(8.(9.&40.+7=01<.)(9.&40.(:.O16.-60.))O15.O14.R:.R9.R8.(9.&40.(;.(<.(:.O4.+???.)+1000.)+1000.))(9.&40.+1.)(9.&40.O5.)(9.&40.(;.(<.(:.O4.+???.)+1000.)+1000.))(9.&40.+3.)(9.&40.+32.)(9.&40.-1.)(9.&40.=)R3.(9.&40.+=>.)(9.&40.O5.)(9.&40.O3.)(9.&40.$=.)O>.O=.O<.O;.O:.O9.O8.R7.R6.R5.R4.)O7.(9.&40.$>.)(9.&40.+=>.)O6.(?.(2.&40.))R2.(10.$11.)))(5.(12.(13.(14.$15.$15.)(16.$15.$15.O2.O16.)(17.(14.$15.$15.)))O1.R2.)(5.(18.$11.O1.R2.)(5.(19.$11.R2.)(5.(1:.$11.R2.(:.O16.-60.)(13.$1;.(1<.(9.&40.+32.))(13.$1;.(1=.#2<.R1.)(13.$1;.(1>.O?.)(13.$1;.(1>.O10.)(13.$1;.(1>.O11.)(13.$1;.(1>.O12.)(13.$1;.(1>.O13.)(13.$1;.(1>.O17.)(17.$1;.))))))))))(1?.$11.R2.O2.(:.O16.-60.)))))))))))))))))")
(* [comment removed for export] *).

  #[using="IMG ALWF CSOK"] Lemma mmapfixed_pre : ltac2:(CDefT.buildp (gd_tbl_AW_MmapFixed ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa0,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)PSP,$15.PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Paddr,$15.Psize,$15.Pname,$15.Plo,$15.P,(5.(21.=R4.)(22.R4.(23.+2.+2?.)))P,(6.$15.(24.R5.+1000.)=)P,(5.(22.=R5.)(21.R5.(23.+2.+28.)))P,(5.(22.=R5.)(22.R5.(23.+2.+2?.)))P,(25.$11.R9.$26.(13.$1;.(1>.(9.&40.$=.))(17.$1;.)))P,(25.$11.R:.$=.(13.$1;.(1>.(9.&40.+1000.))(17.$1;.)))P,(25.$11.R;.$27.(13.$1;.(1>.(9.&40.$28.))(17.$1;.)))P,(25.$11.R<.$29.(13.$1;.(2:.(9.&8.=))(17.$1;.)))P,(1?.$11.R=.R9.R10.)P,(21.+65?000.R:.)P,(21.R;.(2;.R12.+170.))P,(21.R13.(23.+2.+3?.))P,(2<.VCS,R=.(2;.R14.R=.))P,(19.$11.R12.)(2=.$11.VAL,VCS,(2>.R31.R16.R30.R2?.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R15.R14.R12.R11.R10.R?.R13.)(2?.(8.R31.(9.&40.R16.)R30.R2?.R2>.R2=.R2<.R2;.R2:.(9.&40.R12.)(9.&40.R11.)(9.&40.R10.)R1;.R1:.R19.R18.R17.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)R15.(9.&40.$30.)R14.(?.(2.&40.))R13.(10.$11.)))")
(* [comment removed for export] *).
  Proof.
    pose proof (I : lx_noaceil) as LXNOACEIL.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a0 a4 a5 a6 a7 SP F fc m addr size name lo
      AB AAL SZ NM GOT PGS GOTF DEC ST LOIMG SPL SPH SCS MI.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold A_MMAPFIXED_TOL, A_GOT_PAGESZ, A_PAGESZ_CELL, A_GOT_CFLAGS, A_CFLAGS, A_DECORATE in *.
    lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x7b25c] [] 100%N).
    lx_stk_grow_to lo (SP + -96).
    try rewrite (lxw_land_m4096 (size + 4095)) by (clear -SZ; lia).
    stepA_ecall.
    lazymatch goal with STl : stk _ ?mx lo (SP + -96), FRw : rw_cells _ ?mx (SP + -96) _, FRh : rw_cells _ ?mx (SP + -48) _, STj : stk _ ?mx (SP + -92) (SP + -48) |- _ =>
      lx_junk STj 44%nat fr FRj; chunk_join FRw FRj FRa; chunk_join FRa FRh FRb end.
    unfold mf_pre_post, A_MMAP_ECALL. lx_exs; lx_ands; [ lx_mseq | assumption | assumption | assumption | exact FRb | assumption ].
  Qed.

  (* [comment removed for export] *)
  Definition mf_answered (r : Z) (SP : Z) (gp tp t0 t1 t2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 : word)
      (F : bvmap 5 word) (fc : bv 32) (addr size name : Z) (mm : mem) : machine_state := ltac2:(CDefT.buildp (gd_tbl_AW_MmapFixed ()) "(2?.(8.(9.&40.+7=01<.)(9.&40.(:.O18.-60.))O17.O16.O15.O14.O13.(9.&40.(;.(<.(:.O3.+???.)+1000.)+1000.))(9.&40.+1.)(9.&40.O19.)(9.&40.(;.(<.(:.O3.+???.)+1000.)+1000.))(9.&40.+3.)(9.&40.+32.)(9.&40.-1.)(9.&40.=)O7.(9.&40.+=>.)(9.&40.O4.)(9.&40.O2.)(9.&40.$=.)O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.)O6.(9.&40.+7;260.)O5.(?.(2.&40.))O1.(10.$11.))")
(* [comment removed for export] *).

  Definition mf_ret_post (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (res lo : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MmapFixed ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lmm,P,(2.&40.)(3.(2.&8.))(5.(6.$0.R10.(2?.(8.O15.(9.&40.O14.)O13.O12.R?.R>.R=.O11.O10.(9.&40.O3.)R<.R;.R:.R9.R8.R7.R6.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.R5.R4.R3.R2.)O5.(31.O15.)O4.(?.(2.&40.))R1.(10.$11.)))(5.(12.(13.(14.$15.$15.)(16.$15.$15.O2.O14.)(17.(14.$15.$15.)))O1.R1.)(5.(18.$11.O1.R1.)(5.(19.$11.R1.)(1?.$11.R1.O2.O14.))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma mmapfixed_post_enomem : ltac2:(CDefT.buildp (gd_tbl_AW_MmapFixed ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa6,(2.&40.)PSP,$15.PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Paddr,$15.Psize,$15.Pname,$15.Plo,$15.Pfr,(4.(2.&8.))P,(5.(21.=R5.)(22.R5.(23.+2.+2?.)))P,(5.(22.=R5.)(21.R5.(23.+2.+28.)))P,(1:.$11.R8.(:.R<.-60.)(13.$1;.(1<.(9.&40.+32.))(13.$1;.(1=.#2<.R3.)(13.$1;.(1>.R19.)(13.$1;.(1>.R1:.)(13.$1;.(1>.R1;.)(13.$1;.(1>.R1<.)(13.$1;.(1>.R1=.)(13.$1;.(1>.R23.)(17.$1;.))))))))))P,(1?.$11.R9.R5.(:.R=.-60.))P,(21.+65?000.R6.)P,(21.R7.(2;.R?.+170.))P,(21.R10.(23.+2.+3?.))P,(12.(13.(14.$15.$15.)(16.$15.$15.R9.R11.)(17.(14.$15.$15.)))R>.R=.)P,(18.$11.R?.R>.)P,(19.$11.R?.)P,(2<.VCS,R<.(2;.R14.R<.))(2=.$11.VAL,VCS,(32.R2<.R15.R2;.R2:.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R14.R13.=R=.R12.)(33.(2;.(23.+2.+40.)+<.)R15.R2;.R2:.R29.R28.R27.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R14.R13.R10.R?.R>.R11.))")
(* [comment removed for export] *).
  Proof.
    pose proof (I : lx_noaceil) as LXNOACEIL.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 SP F fc m0 mm addr size name lo fr
      AB SZ FR ST LOIMG SPL SPH MU WM MI SCS.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    unfold mf_answered, A_PAGESZ_CELL. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 60%N). lx_postw.
  Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma mmapfixed_post_ok : ltac2:(CDefT.buildp (gd_tbl_AW_MmapFixed ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa6,(2.&40.)PSP,$15.PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Paddr,$15.Psize,$15.Pname,$15.Plo,$15.Pfr,(4.(2.&8.))P,(5.(22.=R5.)(22.R5.(34.VhAR,)))P,(5.(22.=R5.)(21.R5.(23.+2.+28.)))P,(1:.$11.R8.(:.R<.-60.)(13.$1;.(1<.(9.&40.+32.))(13.$1;.(1=.#2<.R3.)(13.$1;.(1>.R19.)(13.$1;.(1>.R1:.)(13.$1;.(1>.R1;.)(13.$1;.(1>.R1<.)(13.$1;.(1>.R1=.)(13.$1;.(1>.R23.)(17.$1;.))))))))))P,(25.$11.R9.$27.(13.$1;.(1>.(9.&40.$28.))(17.$1;.)))P,(25.$11.R:.$35.(13.$1;.(1>.(9.&40.=))(17.$1;.)))P,(1?.$11.R;.R7.(:.R?.-60.))P,(21.+65?000.R8.)P,(21.R9.(2;.R11.+170.))P,(21.R12.(23.+2.+3?.))P,(12.(13.(14.$15.$15.)(16.$15.$15.R;.R13.)(17.(14.$15.$15.)))R10.R?.)P,(18.$11.R11.R10.)P,(19.$11.R11.)P,(2<.VCS,R>.(2;.R16.R>.))(2=.$11.VAL,VCS,(32.R2>.R17.R2=.R2<.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R16.R15.R12.R?.R14.)(33.R12.R17.R2=.R2<.R2;.R2:.R29.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R16.R15.R12.R11.R10.R13.))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 SP F fc m0 mm addr size name lo fr
      AB SZ FR GOTF LIM ST LOIMG SPL SPH MU WM MI SCS.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    unfold mf_answered, A_PAGESZ_CELL, A_GOT_CFLAGS, A_CFLAGS, A_MMAP_LIMIT in *. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 60%N). lx_postw.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Let nZ_ (size : Z) : Z := (size + 4095) / 4096 * 4096.

  (* [comment removed for export] *)
  Definition map_pre_post (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (addr size name lo : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MmapFixed ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lmm,P,(2.&40.)(3.(2.&8.))(1.(4.(2.&8.))Lfr,(4.(2.&8.))(5.(6.$0.R;.(7.(8.(9.&40.+7=01<.)(9.&40.(:.(:.O16.-20.)-60.))O15.O14.R:.R9.R8.(9.&40.(;.(<.(:.O4.+???.)+1000.)+1000.))(9.&40.+1.)(9.&40.O5.)(9.&40.(;.(<.(:.O4.+???.)+1000.)+1000.))(9.&40.+3.)(9.&40.+32.)(9.&40.-1.)(9.&40.=)R3.(9.&40.+=>.)(9.&40.O5.)(9.&40.O3.)(9.&40.$=.)O>.O=.O<.O;.O:.O9.O8.R7.R6.R5.R4.)O7.(9.&40.$>.)(9.&40.+=>.)O6.(?.(2.&40.))R2.(10.$11.)))(5.(12.(13.(14.$15.$15.)(16.$15.$15.O2.O16.)(17.(14.$15.$15.)))O1.R2.)(5.(18.$11.O1.R2.)(5.(19.$11.R2.)(5.(1:.$11.R2.(:.O16.-20.)(13.$1;.(1>.O11.)(13.$1;.(1>.O12.)(13.$1;.(1>.O13.)(13.$1;.(1>.O17.)(17.$1;.))))))(5.(1:.$11.R2.(:.(:.O16.-20.)-60.)(13.$1;.(1<.(9.&40.+32.))(13.$1;.(1=.#2<.R1.)(13.$1;.(1>.O?.)(13.$1;.(1>.O10.)(13.$1;.(1>.O11.)(13.$1;.(1>.(9.&40.O5.))(13.$1;.(1>.(9.&40.O4.))(13.$1;.(1>.(9.&40.$36.))(17.$1;.))))))))))(1?.$11.R2.O2.(:.(:.O16.-20.)-60.))))))))))))))))))")
(* [comment removed for export] *).

  #[using="IMG ALWF CSOK"] Lemma map_pre : ltac2:(CDefT.buildp (gd_tbl_AW_MmapFixed ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa0,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)PSP,$15.PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Paddr,$15.Psize,$15.Pname,$15.Plo,$15.P,(5.(21.=R4.)(22.R4.(23.+2.+2?.)))P,(6.$15.(24.R5.+1000.)=)P,(5.(22.=R5.)(21.R5.(23.+2.+28.)))P,(5.(22.=R5.)(22.R5.(23.+2.+2?.)))P,(25.$11.R9.$26.(13.$1;.(1>.(9.&40.$=.))(17.$1;.)))P,(25.$11.R:.$=.(13.$1;.(1>.(9.&40.+1000.))(17.$1;.)))P,(25.$11.R;.$27.(13.$1;.(1>.(9.&40.$28.))(17.$1;.)))P,(25.$11.R<.$29.(13.$1;.(2:.(9.&8.=))(17.$1;.)))P,(1?.$11.R=.R9.R10.)P,(21.+65?000.R:.)P,(21.R;.(2;.R12.+190.))P,(21.R13.(23.+2.+3?.))P,(2<.VCS,R=.(2;.R14.R=.))P,(19.$11.R12.)(2=.$11.VAL,VCS,(37.R31.R16.R30.R2?.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R15.R14.R12.R11.R10.R?.R13.)(2?.(8.R31.(9.&40.R16.)R30.R2?.R2>.R2=.R2<.R2;.R2:.R1;.(9.&40.R12.)(9.&40.R11.)(9.&40.R10.)R1:.R19.R18.R17.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.)R15.(9.&40.$38.)R14.(?.(2.&40.))R13.(10.$11.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a0 a4 a5 a6 a7 SP F fc m addr size name lo
      AB AAL SZ NM GOT PGS GOTF DEC ST LOIMG SPL SPH SCS MI.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold A_RAR_MAP, A_GOT_PAGESZ, A_PAGESZ_CELL, A_GOT_CFLAGS, A_CFLAGS, A_DECORATE in *.
    (* [comment removed for export] *)
    carve_frame 32%nat ST.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    eapply evtA_mono.
    { eapply mmapfixed_pre with (lo := lo); try eassumption; try lia.
      eapply (crange_sub CS lo (SP - lo)); [exact SCS| lia| lia]. }
    cbn beta. intros ms1 (y5 & y6 & y7 & y28 & y29 & y30 & y31 & ya6 & mm & fr & -> & MU2 & WM2 & MI2 & FR2 & ST2).
    unfold map_pre_post. do 10 eexists. split; [reflexivity|].
    split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp; cbn [outside]; intros; lia. }
    split; [eapply wmono_trans; [exact WM| exact WM2]|]. split; [exact MI2|].
    split. { match goal with H : rw_cells _ _ (SP + -32) _ |- _ => eapply rw_cells_transport; [exact H| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; split; [lia| exact I]] end. }
    split; [exact FR2| exact ST2].
  Qed.

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma map_post_ok : ltac2:(CDefT.buildp (gd_tbl_AW_MmapFixed ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa6,(2.&40.)PSP,$15.PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Paddr,$15.Psize,$15.Pname,$15.Plo,$15.Pfr,(4.(2.&8.))P,(5.(22.=R5.)(22.R5.(34.VhAR,)))P,(5.(22.=R5.)(21.R5.(23.+2.+28.)))P,(1:.$11.R8.(:.R<.-20.)(13.$1;.(1>.R1;.)(13.$1;.(1>.R1<.)(13.$1;.(1>.R1=.)(13.$1;.(1>.R23.)(17.$1;.))))))P,(1:.$11.R9.(:.(:.R=.-20.)-60.)(13.$1;.(1<.(9.&40.+32.))(13.$1;.(1=.#2<.R4.)(13.$1;.(1>.R1:.)(13.$1;.(1>.R1;.)(13.$1;.(1>.R1<.)(13.$1;.(1>.(9.&40.R8.))(13.$1;.(1>.(9.&40.R7.))(13.$1;.(1>.(9.&40.$36.))(17.$1;.))))))))))P,(25.$11.R:.$27.(13.$1;.(1>.(9.&40.$28.))(17.$1;.)))P,(25.$11.R;.$35.(13.$1;.(1>.(9.&40.=))(17.$1;.)))P,(1?.$11.R<.R8.(:.(:.R10.-20.)-60.))P,(21.+65?000.R9.)P,(21.R:.(2;.R12.+190.))P,(21.R13.(23.+2.+3?.))P,(12.(13.(14.$15.$15.)(16.$15.$15.R<.R14.)(17.(14.$15.$15.)))R11.R10.)P,(18.$11.R12.R11.)P,(19.$11.R12.)P,(2<.VCS,R?.(2;.R17.R?.))(2=.$11.VAL,VCS,(32.R2?.R18.R2>.R2=.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R17.R16.R13.R10.R15.)(33.R13.(:.R18.-20.)R2>.R2=.R2<.R2;.R2:.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R17.R16.R13.R12.R11.R14.))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 SP F fc m0 mm addr size name lo fr
      AB SZ FRM FR GOTF LIM ST LOIMG SPL SPH MU WM MI SCS.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    aceilb.
    unfold A_MAP_RET1 in *. unfold mf_answered.
    callxA (eapply (mmapfixed_post_ok (Z_to_bv 64 0x851d4) gp tp t0 t1 t2 (Z_to_bv 64 size) (Z_to_bv 64 addr) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 (SP + -32) F fc mm mm addr size name lo fr);
              try eassumption; try lia; [apply munch_refl| apply wmono_refl| eapply (crange_sub CS lo (SP - lo)); [exact SCS| lia| lia]]).
    (* [comment removed for export] *)
    zstep. if_cases Kz; zify_cond Kz. { exfalso. lia. }
    zstep. zstep. zstep. zstep. zstep.
    replace (SP + -32 + 32) with SP by lia. zstep.
    match goal with H : rw_cells _ _ (SP + -32) _, S : stk _ _ lo (SP + -32) |- _ => release_frame H S SP end.
    apply evtA_done. unfold mf_ret_post. do 15 eexists.
    split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption| eassumption].
  Qed.

  (* [comment removed for export] *)
  Definition map_norep_svc (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (addr size lo : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MmapFixed ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lmm,P,(2.&40.)(3.(2.&8.))(5.(6.$0.R:.(7.(8.(9.&40.+852;0.)(9.&40.(:.O15.-40.))O14.O13.R9.R8.R7.(9.&40.O4.)(9.&40.(;.(<.(:.O3.+???.)+1000.)+1000.))(9.&40.O4.)(9.&40.(;.(<.(:.O3.+???.)+1000.)+1000.))(9.&40.=)(9.&40.+104022.)(9.&40.-1.)(9.&40.=)R2.(9.&40.+=>.)(9.&40.$=.)O?.O>.O=.O<.O;.O:.O9.O8.O7.R6.R5.R4.R3.)O6.(9.&40.$>.)(9.&40.+=>.)O5.(?.(2.&40.))R1.(10.$11.)))(5.(12.(13.(14.$15.$15.)(16.$15.$15.O2.O15.)(17.(14.$15.$15.)))O1.R1.)(5.(18.$11.O1.R1.)(5.(19.$11.R1.)(5.(1:.$11.R1.(:.O15.-20.)(13.$1;.(1>.O10.)(13.$1;.(1>.O11.)(13.$1;.(1>.O12.)(13.$1;.(1>.O16.)(17.$1;.))))))(5.(1:.$11.R1.(:.O15.-40.)(13.$1;.(1>.(9.&40.=))(13.$1;.(1>.(9.&40.O4.))(13.$1;.(1>.(9.&40.O3.))(13.$1;.(1>.(9.&40.+85200.))(17.$1;.))))))(1?.$11.R1.O2.(:.O15.-40.)))))))))))))))))")
(* [comment removed for export] *).

  #[using="IMG ALWF CSOK"] Lemma map_refused_pre : ltac2:(CDefT.buildp (gd_tbl_AW_MmapFixed ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa6,(2.&40.)PSP,$15.PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Paddr,$15.Psize,$15.Pname,$15.Plo,$15.Pfr,(4.(2.&8.))P,(5.(21.=R5.)(22.R5.(23.+2.+2?.)))P,(6.$15.(24.R6.+1000.)=)P,(5.(22.=R6.)(21.R6.(23.+2.+28.)))P,(1:.$11.R9.(:.R=.-20.)(13.$1;.(1>.R1<.)(13.$1;.(1>.R1=.)(13.$1;.(1>.R1>.)(13.$1;.(1>.R24.)(17.$1;.))))))P,(1:.$11.R:.(:.(:.R>.-20.)-60.)(13.$1;.(1<.(9.&40.+32.))(13.$1;.(1=.#2<.R5.)(13.$1;.(1>.R1;.)(13.$1;.(1>.R1<.)(13.$1;.(1>.R1=.)(13.$1;.(1>.(9.&40.R9.))(13.$1;.(1>.(9.&40.R8.))(13.$1;.(1>.(9.&40.$36.))(17.$1;.))))))))))P,(25.$11.R;.$39.(13.$1;.(1>.(9.&40.+1.))(17.$1;.)))P,(25.$11.R<.$26.(13.$1;.(1>.(9.&40.$=.))(17.$1;.)))P,(25.$11.R=.$=.(13.$1;.(1>.(9.&40.+1000.))(17.$1;.)))P,(1?.$11.R>.R:.(:.(:.R12.-20.)-60.))P,(21.+65?000.R;.)P,(21.R<.(2;.R14.+190.))P,(21.R15.(23.+2.+3?.))P,(12.(13.(14.$15.$15.)(16.$15.$15.R>.R16.)(17.(14.$15.$15.)))R13.R12.)P,(18.$11.R14.R13.)P,(19.$11.R14.)P,(2<.VCS,R11.(2;.R19.R11.))(2=.$11.VAL,VCS,(3:.R31.R1:.R30.R2?.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R19.R18.R15.R14.R12.R17.)(33.(2;.(23.+2.+40.)+<.)(:.R1:.-20.)R30.R2?.R2>.R2=.R2<.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R19.R18.R15.R14.R13.R16.))")
(* [comment removed for export] *).
  Proof.
    pose proof (I : lx_noaceil) as LXNOACEIL.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 SP F fc m0 mm addr size name lo fr
      AB AAL SZ FRM FR SEAL GOT PGS ST LOIMG SPL SPH MU WM MI SCS.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    unfold A_MAP_RET1, A_GOT_SEALED2, A_GOT_PAGESZ, A_PAGESZ_CELL in *. unfold mf_answered. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x7b25c] [] 120%N).
    lx_stk_grow_to lo (SP + -64).
    match goal with K : rw_cells _ _ (SP + -64) [_; _; _; _; _; _; _; _] |- _ =>
      chunk_split K 4%nat FRlo FRhi; replace (SP + -64 + 32) with (SP + -32) in FRhi by (clear; lia) end.
    try rewrite (lxw_land_m4096 (size + 4095)) by (clear -SZ; lia).
    stepA_ecall.
    unfold map_norep_svc, A_MMAP_ECALL, A_PAGESZ_CELL. lx_exs; lx_ands; [ lx_mseq | assumption | assumption | assumption | assumption | assumption | assumption ].
  Qed.

  (* [comment removed for export] *)
  Definition map_norep_answered (r : Z) (SP : Z) (gp tp t0 t1 t2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 : word)
      (F : bvmap 5 word) (fc : bv 32) (addr size : Z) (mm : mem) : machine_state := ltac2:(CDefT.buildp (gd_tbl_AW_MmapFixed ()) "(2?.(8.(9.&40.+852;0.)(9.&40.(:.O19.-40.))O18.O17.O16.O15.O14.(9.&40.O3.)(9.&40.(;.(<.(:.O2.+???.)+1000.)+1000.))(9.&40.O1:.)(9.&40.(;.(<.(:.O2.+???.)+1000.)+1000.))(9.&40.=)(9.&40.+104022.)(9.&40.-1.)(9.&40.=)O6.(9.&40.+=>.)(9.&40.$=.)O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.)O5.(9.&40.+7;260.)O4.(?.(2.&40.))O1.(10.$11.))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma map_norep_post_ok : ltac2:(CDefT.buildp (gd_tbl_AW_MmapFixed ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa6,(2.&40.)PSP,$15.PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Paddr,$15.Psize,$15.Plo,$15.P,(5.(21.=R3.)(22.R3.(23.+2.+2?.)))P,(5.(22.=R3.)(21.R3.(23.+2.+28.)))P,(1:.$11.R6.(:.R:.-20.)(13.$1;.(1>.R19.)(13.$1;.(1>.R1:.)(13.$1;.(1>.R1;.)(13.$1;.(1>.R21.)(17.$1;.))))))P,(1:.$11.R7.(:.R;.-40.)(13.$1;.(1>.(9.&40.=))(13.$1;.(1>.(9.&40.R6.))(13.$1;.(1>.(9.&40.R5.))(13.$1;.(1>.(9.&40.+85200.))(17.$1;.))))))P,(1?.$11.R8.R5.(:.R<.-40.))P,(21.+65?000.R6.)P,(21.R7.(2;.R>.+190.))P,(21.R?.(23.+2.+3?.))P,(12.(13.(14.$15.$15.)(16.$15.$15.R9.R10.)(17.(14.$15.$15.)))R=.R<.)P,(18.$11.R>.R=.)P,(19.$11.R>.)P,(2<.VCS,R<.(2;.R13.R<.))(2=.$11.VAL,VCS,(32.R2;.R14.R2:.R29.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R13.R12.=R=.R11.)(3;.R?.R14.R2:.R29.R28.R27.R26.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R13.R12.R?.R>.R10.))")
(* [comment removed for export] *).
  Proof.
    pose proof (I : lx_noaceil) as LXNOACEIL.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 SP F fc m0 mm addr size lo
      AB SZ FRM FRH ST LOIMG SPL SPH MU WM MI SCS.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    unfold map_norep_answered, A_PAGESZ_CELL. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 30%N). lx_postw.
  Qed.

  (* [comment removed for export] *)
  Definition map_spin_post (fc : bv 32) : machine_state -> Prop :=
    fun ms' => exists r F' mm, ms' = MS r F' (Z_to_bv 64 A_MAP_SPIN) fc None mm (seg_rom asegs).

  #[using="IMG ALWF CSOK"] Lemma map_norep_post_spin : ltac2:(CDefT.buildp (gd_tbl_AW_MmapFixed ()) "Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa6,(2.&40.)PSP,$15.PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pmm,P,(2.&40.)(3.(2.&8.))Paddr,$15.Psize,$15.Pr,$15.Plo,$15.P,(5.(21.=R4.)(22.R4.(23.+2.+2?.)))P,(5.(21.=R3.)(22.R3.(23.+2.+40.)))P,(3<.(6.$15.R4.R6.))P,(25.$11.R8.$3=.(13.$1;.(1>.(9.&40.$3>.))(17.$1;.)))P,(25.$11.R9.$3>.(13.$1;.(1<.(9.&40.=))(17.$1;.)))P,(1?.$11.R:.R6.(:.R=.-40.))P,(21.+65?000.R7.)P,(21.R8.(2;.R?.+190.))P,(21.R10.(23.+2.+3?.))P,(19.$11.R>.)P,(2<.VCS,R;.(2;.R12.R;.))(2=.$11.VAL,VCS,(3?.R11.)(3;.R=.R13.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R12.R11.R?.R>.R10.))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 SP F fc mm addr size r lo
      AB RB RNE GOTD DY ST LOIMG SPL SPH MI SCS.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    unfold map_norep_answered, A_PAGESZ_CELL, A_GOT_DYING, A_DYING, A_MAP_SPIN in *.
    (* [comment removed for export] *)
    zstep. zstep. if_cases Kne; zify_cond Kne. 2:{ exfalso. rewrite ?unsigned_lit in Kne by lia. lia. }
    zstep. zstep. zstep. zstep.
    apply evtA_done. unfold map_spin_post. do 3 eexists. reflexivity.
  Qed.
End MmapFixed.

End ARUN_1.
