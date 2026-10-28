(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_MmapFixed AW_MmapAnon AW_MmapDie AW_DepotA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0075fed36beefd6a 0 4 0 1 24 1 32 1 33 1P01ac468f8b0f50bc 0 4 0 1 24 1 30 1 31 1P01f87af00192eeb1 0 4 0 1 22 1 28 1 29 1P026ccf662980246a 0 2 0 1 30 1P03c9a5c3cf4335be 1 1 4 2 0 1 29 1 3 25 1 28 1 30 4P03f8c9086aae2db6 1 1 16 3 1 1 29 1 31 1 4 25 1 26 1 32 1 33 16P050a8e0a0afbd2bb 0 4 0 1 25 1 31 1 32 1P05dadf0977193d51 1 1 8 1 0 1 2 31 1 32 1P077ab1a14e147022 0 4 0 1 28 1 32 1 33 1P07cb54a06a3185b3 0 4 0 1 22 1 28 1 29 1P083f2ec982f1822d 0 4 0 1 25 1 31 1 32 1P08c317fc78d3f11b 1 1 4 2 0 1 28 1 3 26 1 29 1 30 4P08fbebeaac7ec33a 1 2 16 2 0 1 34 1 16 2 1 1 33 1 2 35 1 36 1P0960dbe548bb8aaf 1 2 16 2 0 1 34 1 16 2 1 1 33 1 2 35 1 36 1P098ed69b401e1389 0 4 0 1 28 1 32 1 33 1P0a5044a24f2e174e 0 4 0 1 24 1 32 1 33 1P0a55e26288e2613d 0 4 0 1 22 1 28 1 29 1P0a7c2d6ac8096d46 0 4 0 1 25 1 31 1 32 1P0c10bd6ca4f7637f 0 2 0 1 24 1P0c8aa796e9b8c049 0 4 0 1 24 1 30 1 31 1P0cbcd45b343f17a2 1 2 4 3 1 1 29 1 32 1 16 3 26 1 31 1 33 4 4 23 1 28 1 30 1 34 16P0d42b4273ac05902 0 4 0 1 22 1 28 1 29 1P0d61076a8ed0d15e 0 4 0 1 24 1 30 1 31 1P0e639f9056c666ac 1 1 16 2 1 1 33 1 4 29 1 30 1 34 1 35 16P0e8bfe95b6ab3f20 0 4 0 1 24 1 30 1 31 1P0f14847ebcaeafd2 1 1 16 2 0 1 33 1 4 27 1 28 1 34 1 35 16P0f8197d773a94e66 0 4 0 1 26 1 32 1 33 1P0f91c01e7fca2330 0 4 0 1 22 1 28 1 29 1P104cf97b2b57cc44 0 2 0 1 24 1P106d7231febc4615 0 4 0 1 22 1 28 1 29 1P107859c312e966c0 0 4 0 1 26 1 32 1 33 1P1143ee8a6ac16ea6 0 2 0 1 23 1P1148d2bf5d3eaac1 0 4 0 1 22 1 28 1 29 1P1165c618a123c9a8 0 4 0 1 22 1 28 1 29 1P1193d8cd23c4109d 1 1 16 2 1 1 33 1 4 29 1 30 1 34 1 35 16P123307a2df3a3306 0 4 0 1 24 1 30 1 31 1P146c36d71124dfd5 1 2 4 3 1 1 29 1 32 1 16 3 26 1 31 1 33 4 4 23 1 28 1 30 1 34 16P148711d714d9289e 0 4 0 1 26 1 32 1 33 1P14c4f4812d0b9d19 1 2 4 3 1 1 29 1 32 1 16 3 26 1 31 1 33 4 4 23 1 28 1 30 1 34 16P1530a54ca15fe904 0 4 0 1 24 1 30 1 31 1P156cb025dfdb062a 0 2 0 1 32 1P15c4bffc19dbeb3e 1 2 16 2 0 1 34 1 16 2 1 1 33 1 2 35 1 36 1P1858b20790b63f84 1 1 8 1 0 1 2 30 1 32 1P189db913acd9a81c 0 4 0 1 24 1 30 1 31 1P18ed62904a53e85e 1 1 8 1 0 1 2 31 1 32 1P190f42ac941c8c4c 0 4 0 1 28 1 32 1 33 1P19dea8ec3f2a2ddd 1 1 8 1 0 1 2 33 1 34 1P1a6cc58610b0e01f 1 1 16 3 0 1 31 1 33 1 4 25 1 26 1 34 1 35 16P1d616177adba2b32 0 4 0 1 24 1 32 1 33 1P1e96d0f143d78eb5 0 2 0 1 31 1P1e9ae8d2777554fc 1 2 16 2 0 1 34 1 16 2 1 1 33 1 2 35 1 36 1P1f287ec85125daea 0 4 0 1 24 1 30 1 31 1P1f8f1da1980e7d5f 0 4 0 1 22 1 28 1 29 1P1f9b3e3471ba370f 0 4 0 1 25 1 31 1 32 1P21b832e83f4950df 1 1 16 3 1 1 29 1 31 1 4 25 1 26 1 32 1 33 16P221ec0dce3b4e2df 0 4 0 1 25 1 31 1 32 1P2270d95ff3dc2fb8 1 1 16 2 1 1 31 1 4 25 1 26 1 32 1 33 16P22f3280889295817 0 4 0 1 24 1 30 1 31 1P234333a23b8f59a1 1 1 8 2 1 1 33 1 5 29 2 30 2 31 16 34 2 35 16P24eb78d2aafdb643 0 4 0 1 22 1 28 1 29 1P24ec7112452449c5 0 4 0 1 22 1 28 1 29 1P27424ac848058658 0 2 0 1 24 1P275cdd224a6729f7 0 4 0 1 24 1 30 1 31 1P27d7cb8916cb27b8 1 1 8 2 0 1 33 1 5 27 2 28 2 31 16 34 2 35 16P2865c2f30d47fabf 0 2 0 1 23 1P29278b1fb767bd44 1 1 16 3 1 1 29 1 31 1 4 25 1 26 1 32 1 33 16P2987491200dc9c3c 0 4 0 1 22 1 28 1 29 1P29e17439d678becf 0 4 0 1 28 1 32 1 33 1P2a88d0351cc5f537 1 1 8 2 1 1 33 1 5 29 2 30 2 31 16 34 2 35 16P2a91df7c55be848d 1 1 8 1 0 1 2 32 1 34 1P2c19d656eb7921b1 0 4 0 1 28 1 32 1 33 1P2c3a8798d73b8607 1 1 16 3 1 1 29 1 31 1 4 25 1 26 1 32 1 33 16P2c963c0ef6028358 1 2 16 2 0 1 34 1 16 2 1 1 33 1 2 35 1 36 1P2d467a52b220cf7f 0 4 0 1 22 1 28 1 29 1P2e38588427bca5dc 0 4 0 1 28 1 32 1 33 1P2e7ff9e7323d9139 0 4 0 1 24 1 32 1 33 1P2e969cb60fe8d053 0 4 0 1 28 1 32 1 33 1P2ea07829d9d07103 1 1 16 3 0 1 31 1 33 1 4 25 1 26 1 34 1 35 16P2f167c24ef581995 1 2 16 2 0 1 32 1 16 2 1 1 31 1 2 33 1 34 1P2f1e56958fd1b585 1 1 8 1 1 1 2 32 1 33 1P2fb08a7762c7e0df 1 1 16 2 1 1 33 1 4 29 1 30 1 34 1 35 16P2fde3296c3ed99d6 1 1 16 2 1 1 33 1 4 29 1 30 1 34 1 35 16P3101d887bff09014 0 4 0 1 26 1 32 1 33 1P315247b9b9f9b65f 0 4 0 1 28 1 32 1 33 1P31d19f67d9e20887 1 2 4 3 1 1 29 1 32 1 16 3 26 1 31 1 33 4 4 23 1 28 1 30 1 34 16P326e6fc4e071888f 0 2 0 1 30 1P328bcc6cf52dc3ce 0 2 0 1 30 1P32c35bc9298aec9d 1 1 16 2 1 1 31 1 4 25 1 26 1 32 1 33 16P3374d708c24ce535 1 1 16 2 1 1 33 1 4 29 1 30 1 34 1 35 16P33d75a478bfe2e31 0 2 0 1 23 1P3453e8b51c929346 0 5 0 16 27 16 28 16 33 16 34 16P345932d1b32350e5 0 4 0 1 24 1 30 1 31 1P372a75a4620a3c6f 1 2 16 2 0 1 32 1 16 2 1 1 31 1 2 33 1 34 1P372d8f0dfa01db0e 0 4 0 1 28 1 32 1 33 1P3746a27a590d234f 0 4 0 1 28 1 32 1 33 1P37b9a074cdfa2dd7 0 4 0 1 22 1 28 1 29 1P38ab0ef81cb6ca94 1 2 4 3 1 1 29 1 32 1 16 3 26 1 31 1 33 4 4 23 1 28 1 30 1 34 16P38af186c07683d03 0 4 0 1 28 1 32 1 33 1P38d83f69525139c1 0 4 0 1 22 1 28 1 29 1P39b78c144d67cb17 0 2 0 1 32 8P3a519377420d624b 0 2 0 1 31 1P3af0e99c720f4608 1 1 8 2 1 1 33 1 5 29 2 30 2 31 16 34 2 35 16P3b8eaf75c1060a3c 0 4 0 1 24 1 30 1 31 1P3b91693473f4f1c9 0 4 0 1 24 1 32 1 33 1P3c3257c3dcf11137 1 2 16 2 0 1 34 1 16 2 1 1 33 1 2 35 1 36 1P3c8b123dc7a73c67 0 4 0 1 25 1 31 1 32 1P3cd492b3708f18e9 0 2 0 1 31 1P3d09b29e0cee2887 0 4 0 1 26 1 32 1 33 1P3da842a54cbfbb3c 1 1 8 2 1 1 33 1 5 29 2 30 2 31 16 34 2 35 16P3df52e18e46f278d 1 1 16 2 1 1 33 1 4 29 1 30 1 34 1 35 16P3e5d2275c0f18f15 0 4 0 1 28 1 32 1 33 1N060975892944ced8N07ded8bb4d8037f8N097ca6bbc3571087N09bb16e8c29b3513N0ba255f4c7079fdcN0f5104495805f0b1N0f8b03e6e15b07eaN11b0db5cb3bcdc19N1679264fba99ac09N18ac91413375b260N1eff8e30d54a74e9N210c6e414e47c2b8N24cc6c362e793b0bN25614b44a7d7f30fN267f73c836882fb5N2a46f77e2388ee54N301f4902147d2b68N30be4854bd53822eN3216abb90983dea5N3417331f4c53ac14N3471b87507579107N39246b130a633b78N3acd1a171969332fN3bef5cda74a07553N3d3841d5ca554a30N3e64879b8cd221a1"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_DepotB () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "ARUN_1.A_DLOCK"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_DEP_NODES"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotA.A_DEP_MAP1"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_GOT_PAGESZ"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_PAGESZ_CELL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapDie.A_MMAP_OR_DIE"; "ARUN_1.A_TLM_CREATE"; "ARUN_1.A_SS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapDie.A_MMAP_NORESERVE_OR_DIE"; "ARUN_1.A_BI_CREATE"; "Corelib.Init.Datatypes.list"].

Section ARUN_1. Context {hAR : arun}.
Definition A_DLOCK : Z := 0x089d34.
Definition A_TLM_CREATE : Z := 0x089dc4.
Definition A_BI_CREATE : Z := 0x087ab0.
Definition A_SS : Z := 0x1db8c8.                  (* [comment removed for export] *)

Section DepotB.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0?L1610371401.71 L2114062161.65 L2116217729.66 L21265136719.66L21267271839.65L26555743700.65L26557845764.66L29440527249.69L29440528133.68L42628420821.66L42630576133.65L44196198388.67L44198304548.68L45299693460.67L45301799748.68L45677353968.68L53520021460.66L53522094852.65L58591417776.3 L59310732048.2 L59310733188.2 L59848750459.66L59850856875.65L60938531490.70L61962423859.6900000\00k01:01I01X01Y01Z01n02B02M02X02^02d03203@03F03P03Z03e03l04304:04A04T04aS2SP1B1v2lo5LOIMG3BLO3BHI3SPL2HB5Ha_st5Hl_stS2AL1B3BLO4IMG'S2AL1B3BLO4IMG'S2AL1B3BHI4IMG'S2AL1B3BHI4IMG'FFS2SP1B1v3VBa3VBb3KeqS2SP1B1v3Kne3VBa3VBbS1B3BLO3BHIS1B3BLO3BHIS2SP1BS2SP1BS2SP1B3BLO3BALS2SP1B3BLO3BALS2SP1BS2AL5ALWF'S2AL5ALWF'S1v3VBa3VBbS1v3KeqS1v3KneS1B3BLOS1B3BLOS2SP1B3BHI2HB5Ha_stS2SP1B3BLO2HB". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma dlock_spec : ltac2:(CDefT.buildp (gd_tbl_AW_DepotB ()) "Pra,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)PSP,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(3.(0.&8.))PB,$1.Pv,$1.Plo,$1.P,(4.+65?000.R1.)P,(4.+10000.R4.)P,(4.(5.R5.+4.)+65?000.)P,(6.$1.(7.R6.+4.)=)P,(8.(4.=R6.)(9.R6.(:.+2.+1?.)))P,(;.$<.R9.R8.(=.$>.(?.(10.&40.R7.))(11.$>.)))P,(12.$<.R:.R7.R=.)P,(4.R8.(13.R>.+30.))P,(4.R?.(:.+2.+3?.))P,(6.$1.(7.R10.+10.)=)P,(14.VCS,R;.(13.R11.R;.))P,(15.$<.R?.)(16.$<.VAL,VCS,Lms',$17.(18.(0.&40.)Lx1,(0.&40.)(18.(0.&40.)Lx2,(0.&40.)(18.(0.&40.)Lx3,(0.&40.)(18.(0.&40.)Lx4,(0.&40.)(18.(0.&40.)Llockw,(0.&40.)(18.P,(0.&40.)(3.(0.&8.))Lmm,P,(0.&40.)(3.(0.&8.))(8.(6.$17.R7.(19.(1:.R37.(10.&40.R1:.)R36.R35.R34.R33.R32.R31.R30.(10.&40.R15.)R6.R5.R4.R3.R1=.R1<.R1;.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.)R19.(1;.R37.)R18.(1<.(0.&40.))R1.(1=.$<.)))(8.(1>.(=.(1?.$1.$1.)(20.$1.$1.R14.R1:.)(=.(1?.$1.$1.)(20.$1.$1.R16.(5.R16.+4.))(11.(1?.$1.$1.))))R17.R1.)(8.(21.$<.R17.R1.)(8.(15.$<.R1.)(8.(;.$<.R1.R16.(=.$>.(?.R2.)(11.$>.)))(12.$<.R1.R14.R1:.))))))))))))(19.(1:.R30.(10.&40.R13.)R2?.R2>.R2=.R2<.R2;.R2:.R29.(10.&40.R?.)R1:.R19.R18.R17.R16.R15.R14.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R12.(10.&40.$22.)R11.(1<.(0.&40.))R10.(1=.$<.)))")
(* [comment removed for export] *).
  Proof.
    pose proof (I : lx_noaceil) as LXNOACEIL.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a1 a2 a3 a4 a5 a6 a7 SP F fc m B v lo
      LOIMG BLO BHI BAL VB BC ST SPL SPH SPA SCS MI.
    facts. pose proof (munch_refl [(lo, SP); (B, B + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold A_DLOCK. destruct VB as [VBa VBb]. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x89d78] [] 20%N).

    (* [comment removed for export] *)
    zstep. rewrite (sx32_small v) by (clear -VBa VBb; lia).
    zstep. if_cases Kne; zify_cond Kne. { exfalso. clear -Kne; lia. }
    zstep. zstep. zstep. if_cases Keq; zify_cond Keq. 2:{ exfalso. clear -Keq; lia. }
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 20%N). lx_same.
    apply evtA_done. lx_exs. lx_ands; [> lx_mseq | ..]; lx_close.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00A0?L17882783852.71L22968557704.70L24855863521.68L26142702700.71L27463137702.67L27736837337.2 L31211073049.71L35513334182.67L38180794554.67L41877884652.67L50983652295.71L53051764561.0 L53522095243.67L55347286967.1 L56914399217.69L57486777565.77L60176135857.6700000C00P00e01801901:01`01i01j02302S02T02^02a02h02n02oS2SP2HB5Ha_st5Hl_stS2SP2HB5Ha_stS2SP2lo5LOIMG3SPL3SPAS2SP2HB5Ha_st5Hl_stSFS2SP1k2lo3KBa5LOIMG3SPL2HB5Ha_st5Hl_stS2AL4IMG'SS2AL4IMG'S2SP2lo5LOIMG3SPL2HB5Ha_st5Hl_stSS2AL5ALWF'S1kS2SP2HBS2SP1kF". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma tc_A : ltac2:(CDefT.buildp (gd_tbl_AW_DepotB ()) "Pra,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)PSP,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(3.(0.&8.))Pk,$1.Plo,$1.P,(8.(4.=R2.)(9.R2.+8000.))P,(;.$<.R4.$23.(=.$>.(?.(10.&40.=))(11.$>.)))P,(;.$<.R5.(5.$24.(25.+8.R4.))(=.$>.(26.(10.&40.=))(11.$>.)))P,(27.$<.R6.$28.(=.$>.(26.(10.&40.$29.))(11.$>.)))P,(27.$<.R7.$29.(=.$>.(26.(10.&40.+1000.))(11.$>.)))P,(12.$<.R8.R6.R;.)P,(4.+65?000.R7.)P,(4.R8.(13.R=.+20.))P,(4.R>.(:.+2.+3?.))P,(6.$1.(7.R?.+10.)=)P,(14.VCS,R;.(13.R10.R;.))P,(15.$<.R>.)(16.$<.VAL,VCS,Lms',$17.(18.(0.&40.)Lx3,(0.&40.)(18.(0.&40.)Lx4,(0.&40.)(18.(0.&40.)Lx5,(0.&40.)(18.P,(0.&40.)(3.(0.&8.))Lmm,P,(0.&40.)(3.(0.&8.))(8.(6.$17.R5.(19.(1:.(10.&40.+89>68.)(10.&40.(5.R17.-20.))R32.R31.R30.R2?.R2>.(10.&40.$23.)(10.&40.(5.$23.(25.+8.R13.)))(10.&40.+100000.)(10.&40.+240;:.)(10.&40.=)R4.R3.R2.R19.R18.(10.&40.$29.)R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R16.(10.&40.$2:.)R15.(1<.(0.&40.))R1.(1=.$<.)))(8.(1>.(=.(1?.$1.$1.)(20.$1.$1.R12.R17.)(=.(1?.$1.$1.)(20.$1.$1.$23.(5.$23.+4.))(11.(1?.$1.$1.))))R14.R1.)(8.(21.$<.R14.R1.)(8.(15.$<.R1.)(8.(;.$<.R1.(5.R17.-20.)(=.$>.(26.R2;.)(=.$>.(26.R2<.)(=.$>.(26.R2=.)(=.$>.(26.R33.)(11.$>.))))))(8.(;.$<.R1.$23.(=.$>.(?.(10.&40.+1.))(11.$>.)))(8.(;.$<.R1.(5.$24.(25.+8.R13.))(=.$>.(26.(10.&40.=))(11.$>.)))(12.$<.R1.R12.(5.R17.-20.)))))))))))))(19.(1:.R2>.(10.&40.R12.)R2=.R2<.R2;.R2:.R29.R28.R27.(10.&40.$23.)(10.&40.R>.)R18.R17.R16.R15.R14.R13.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R11.(10.&40.$2;.)R10.(1<.(0.&40.))R?.(1=.$<.)))")
(* [comment removed for export] *).
  Proof.
    pose proof (I : lx_noaceil) as LXNOACEIL.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a2 a3 a4 a5 a6 a7 SP F fc m k lo
      KB MX M1 GOT PGS ST LOIMG SPL SPH SPA SCS MI.
    facts. pose proof (munch_refl [(lo, SP); (A_DEP_NODES, A_DEP_NODES + 4)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold A_TLM_CREATE, A_DEP_NODES, A_DEP_MAP1, A_GOT_PAGESZ, A_PAGESZ_CELL, A_MMAP_OR_DIE in *. destruct KB as [KBa KBb]. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x89de8] [] 20%N).

    (* [comment removed for export] *)
    zstep. rewrite (sx32_small 0) by (clear; lia).
    do 8 zstep.
    (* [comment removed for export] *)
    lx_run (PLAN [0x7c928] [] 40%N).
    apply evtA_done. lx_exs. lx_ands; [> lx_mseq | ..]; lx_close.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L51489811886.60L55347286967.1 00000>00AS2SP1k2lo1y2HyS1k". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma tc_B : ltac2:(CDefT.buildp (gd_tbl_AW_DepotB ()) "Pra,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)PSP,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(3.(0.&8.))Pmm,P,(0.&40.)(3.(0.&8.))Pk,$1.Pa,$1.Plo,$1.P,(8.(4.=R3.)(9.R3.+8000.))P,(8.(9.=R3.)(9.R3.(:.+2.+2?.)))P,(;.$<.R6.(5.R:.-20.)(=.$>.(26.R1?.)(=.$>.(26.R20.)(=.$>.(26.R21.)(=.$>.(26.R27.)(11.$>.))))))P,(;.$<.R7.$23.(=.$>.(?.(10.&40.+1.))(11.$>.)))P,(;.$<.R8.(5.$24.(25.+8.R7.))(=.$>.(26.(10.&40.=))(11.$>.)))P,(12.$<.R9.R6.(5.R=.-20.))P,(4.+65?000.R7.)P,(4.R8.(13.R?.+20.))P,(4.R10.(:.+2.+3?.))P,(6.$1.(7.R11.+10.)=)P,(1>.(=.(1?.$1.$1.)(20.$1.$1.R;.R12.)(=.(1?.$1.$1.)(20.$1.$1.$23.(5.$23.+4.))(=.(1?.$1.$1.)(20.$1.$1.(5.$24.(25.+8.R=.))(5.(5.$24.(25.+8.R=.))+8.))(11.(1?.$1.$1.)))))R?.R>.)P,(21.$<.R10.R?.)P,(15.$<.R10.)P,(14.VCS,R>.(13.R15.R>.))(16.$<.VAL,VCS,Lms',$17.(18.P,(0.&40.)(3.(0.&8.))Lm',P,(0.&40.)(3.(0.&8.))(8.(6.$17.R2.(19.(1:.R35.(10.&40.R18.)R34.R33.R32.R31.R30.R2?.R2>.(10.&40.R12.)R1?.R1>.R1=.R1<.R1;.R1:.R19.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.)R17.(1;.R35.)R16.(1<.(0.&40.))R1.(1=.$<.)))(8.(1>.(=.(1?.$1.$1.)(20.$1.$1.R11.R18.)(=.(1?.$1.$1.)(20.$1.$1.$23.(5.$23.+4.))(=.(1?.$1.$1.)(20.$1.$1.(5.$24.(25.+8.R13.))(5.(5.$24.(25.+8.R13.))+8.))(11.(1?.$1.$1.)))))R15.R1.)(8.(21.$<.R15.R1.)(8.(15.$<.R1.)(8.(;.$<.R1.$23.(=.$>.(?.(10.&40.=))(11.$>.)))(8.(;.$<.R1.(5.$24.(25.+8.R13.))(=.$>.(26.(10.&40.R12.))(11.$>.)))(12.$<.R1.R11.R18.))))))))(19.(1:.(10.&40.+89>68.)(10.&40.(5.R16.-20.))R32.R31.R30.R2?.R2>.(10.&40.$23.)(10.&40.(5.$23.(25.+8.R11.)))(10.&40.R10.)R1=.R1<.R1;.R1:.R19.R18.R17.(10.&40.$29.)R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.)R15.(10.&40.+89>68.)R14.(1<.(0.&40.))R12.(1=.$<.)))")
(* [comment removed for export] *).
  Proof.
    pose proof (I : lx_noaceil) as LXNOACEIL.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a1 a2 a3 a4 a5 a6 a7 SP F fc m0 mm k a lo
      KB AB FR MX M1 ST LOIMG SPL SPH SPA MU WM MI SCS.
    facts. unfold A_DEP_NODES, A_DEP_MAP1, A_PAGESZ_CELL in *. destruct KB as [KBa KBb]. destruct AB as [ABa ABb]. lx_aceil.
    (* [comment removed for export] *)
    apply (rw_cells_reshape asegs mm 6207712 _ [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) in MX;
      [| cbn; tauto | vm_compute; reflexivity].
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 20%N).
    match goal with H : rw_cells _ lxm 6207712 _ |- _ =>
      apply (rw_cells_reshape asegs lxm 6207712 _ [C4 (Z_to_bv 64 0)]) in H; [| cbn; tauto | vm_compute; reflexivity] end.
    apply evtA_done. lx_exs. lx_ands; [> lx_mseq | ..]; lx_close.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L15062148515.8L5744833530.8 000001007SS1x2Hx". (* [comment removed for export] *)
  #[using="Type"] Lemma land_align2 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551612 = x / 4 * 4.
  Proof.
    intros x Hx. change 18446744073709551612 with (Z.land (Z.ones 64) (Z.lnot (Z.ones 2))).
    rewrite land_clear_low by lia. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L12671229966.70L29492035091.65L29998951241.70L32195638050.69L34545489520.65L34545489520.67L41302095817.65L43978099342.65L4743335024.67 L50565076305.65L53522094981.65L55152813832.68L6636494756.67 L67814467315.6700000J00Z01D01X01c02102902:02Z02j03403B03J03jS2SP3SSB2B02HB5Ha_st5Hl_stS2AL3SSB2B04IMG'S2SP3SSB2lo2B02B15LOIMG3SPL2HB5Ha_st5Hl_stS2SP3SSB2B12HB5Ha_stS3SSB2B02B1S2SP3SSB2B02B1S3SSB2B0FS2SP3SSB2lo2B03BAL5LOIMG3SPL3SPAS2AL3SSB2B14IMG'S2AL5ALWF'S2SP3SSB2B02HBS2SP3SSBS2SP3SSB2lo2B03BAL5LOIMG3SPL3SPA". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma bc_A : ltac2:(CDefT.buildp (gd_tbl_AW_DepotB ()) "Pra,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pstored,(0.&40.)Palloc,(0.&40.)PSP,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(3.(0.&8.))PSSB,$1.Plo,$1.P,(4.(5.$2<.+10.)R2.)P,(4.(5.R3.+10.)(5.(5.$2<.+10.)(25.+10.+1000.)))P,(6.$1.(7.R4.+10.)+8.)P,(;.$<.R6.R5.(=.$>.(26.(10.&40.=))(=.$>.(?.R;.)(=.$>.(?.(10.&40.=))(11.$>.)))))P,(;.$<.R7.(5.$2<.+8.)(=.$>.(26.R;.)(11.$>.)))P,(12.$<.R8.R6.R;.)P,(4.+65?000.R7.)P,(4.R8.(13.R=.+20.))P,(4.R>.(:.+2.+3?.))P,(6.$1.(7.R?.+10.)=)P,(14.VCS,R;.(13.R10.R;.))P,(15.$<.R>.)(16.$<.VAL,VCS,Lms',$17.(18.(0.&40.)Lx2,(0.&40.)(18.(0.&40.)Lx3,(0.&40.)(18.(0.&40.)Lx4,(0.&40.)(18.(0.&40.)Lx5,(0.&40.)(18.(0.&40.)Lalloc',(0.&40.)(18.P,(0.&40.)(3.(0.&8.))Lmm,P,(0.&40.)(3.(0.&8.))(8.(6.$17.R7.(19.(1:.(10.&40.+87;20.)(10.&40.(5.R19.-20.))R36.R35.R34.R33.R32.(10.&40.(5.R15.+<.))(10.&40.R15.)(10.&40.+800000.)(10.&40.+2424:.)R6.R5.R4.R3.R1=.R1<.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.)R18.(10.&40.$2=.)R17.(1<.(0.&40.))R1.(1=.$<.)))(8.(1>.(=.(1?.$1.$1.)(20.$1.$1.R14.R19.)(=.(1?.$1.$1.)(20.$1.$1.R15.(5.R15.+10.))(=.(1?.$1.$1.)(20.$1.$1.(5.$2<.+8.)(5.$2<.+10.))(11.(1?.$1.$1.)))))R16.R1.)(8.(21.$<.R16.R1.)(8.(15.$<.R1.)(8.(;.$<.R1.(5.R19.-20.)(=.$>.(26.R2?.)(=.$>.(26.R30.)(=.$>.(26.R31.)(=.$>.(26.R37.)(11.$>.))))))(8.(;.$<.R1.R15.(=.$>.(26.(10.&40.=))(=.$>.(?.R1;.)(=.$>.(?.(10.&40.+1.))(11.$>.)))))(8.(;.$<.R1.(5.$2<.+8.)(=.$>.(26.R2.)(11.$>.)))(12.$<.R1.R14.(5.R19.-20.)))))))))))))))(19.(1:.R30.(10.&40.R12.)R2?.R2>.R2=.R2<.R2;.R2:.R29.(10.&40.R>.)(10.&40.$2<.)R1:.R19.R18.R17.R16.R15.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R11.(10.&40.$2>.)R10.(1<.(0.&40.))R?.(1=.$<.)))")
(* [comment removed for export] *).
  Proof.
    pose proof (I : lx_noaceil) as LXNOACEIL.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a2 a3 a4 a5 a6 a7 stored alloc SP F fc m SSB lo
      B0 B1 BAL BX AX ST LOIMG SPL SPH SPA SCS MI.
    facts. pose proof (munch_refl [(lo, SP); (SSB, SSB + 16); (A_SS + 8, A_SS + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold A_BI_CREATE, A_SS, A_MMAP_NORESERVE_OR_DIE in *. change (1947848 + 8) with 1947856 in *. change (1947848 + 16) with 1947864 in *.
    rewrite <- (Z_to_bv_bv_unsigned alloc) in AX. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x87ad0] [] 20%N).
    (* [comment removed for export] *)
    zstep. rewrite (land_align2 (SSB + 12)) by lia. replace ((SSB + 12) / 4 * 4) with (SSB + 12) by lia.
    zstep.
    (* [comment removed for export] *)
    zstep. rewrite (sx32_small 0) by lia.
    do 8 zstep.
    (* [comment removed for export] *)
    lx_run (PLAN [0x7ce60] [] 20%N).
    apply evtA_done. lx_exs. lx_ands; [> lx_mseq | ..]; lx_close.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma bc_B : ltac2:(CDefT.buildp (gd_tbl_AW_DepotB ()) "Pra,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pstored,(0.&40.)PSP,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(3.(0.&8.))Pmm,P,(0.&40.)(3.(0.&8.))PSSB,$1.Pa,$1.Plo,$1.PW,(2?.(1?.$1.$1.))P,(4.(5.$2<.+10.)R4.)P,(4.(5.R5.+10.)(5.(5.$2<.+10.)(25.+10.+1000.)))P,(6.$1.(7.R6.+10.)+8.)P,(8.(9.=R6.)(9.R6.(:.+2.+2?.)))P,(;.$<.R9.(5.R=.-20.)(=.$>.(26.R23.)(=.$>.(26.R24.)(=.$>.(26.R25.)(=.$>.(26.R2;.)(11.$>.))))))P,(;.$<.R:.R9.(=.$>.(26.(10.&40.=))(=.$>.(?.R?.)(=.$>.(?.(10.&40.+1.))(11.$>.)))))P,(12.$<.R;.R8.(5.R?.-20.))P,(4.+65?000.R9.)P,(4.R:.(13.R11.+20.))P,(4.R12.(:.+2.+3?.))P,(6.$1.(7.R13.+10.)=)P,(1>.(=.(1?.$1.$1.)(20.$1.$1.R=.R14.)(=.(1?.$1.$1.)(20.$1.$1.R?.(5.R?.+10.))R<.))R11.R10.)P,(21.$<.R12.R11.)P,(15.$<.R12.)P,(14.VCS,R10.(13.R17.R10.))(16.$<.VAL,VCS,Lms',$17.(18.P,(0.&40.)(3.(0.&8.))Lm',P,(0.&40.)(3.(0.&8.))(8.(6.$17.R2.(19.(1:.R38.(10.&40.R1:.)R37.R36.R35.R34.R33.R32.R31.(10.&40.R14.)R22.R21.R20.R1?.R1>.R1=.R1<.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.)R19.(1;.R38.)R18.(1<.(0.&40.))R1.(1=.$<.)))(8.(1>.(=.(1?.$1.$1.)(20.$1.$1.R13.R1:.)(=.(1?.$1.$1.)(20.$1.$1.R15.(5.R15.+10.))R12.))R17.R1.)(8.(21.$<.R17.R1.)(8.(15.$<.R1.)(8.(;.$<.R1.R15.(=.$>.(26.(10.&40.R14.))(=.$>.(?.R1;.)(=.$>.(?.(10.&40.=))(11.$>.)))))(12.$<.R1.R13.R1:.)))))))(19.(1:.(10.&40.+87;20.)(10.&40.(5.R18.-20.))R35.R34.R33.R32.R31.(10.&40.(5.R13.+<.))(10.&40.R13.)(10.&40.R12.)R20.R1?.R1>.R1=.R1<.R1;.R1:.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.)R17.(10.&40.+87;20.)R16.(1<.(0.&40.))R14.(1=.$<.)))")
(* [comment removed for export] *).
  Proof.
    pose proof (I : lx_noaceil) as LXNOACEIL.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a1 a2 a3 a4 a5 a6 a7 stored SP F fc m0 mm SSB a lo W
      B0 B1 BAL AB FR BX ST LOIMG SPL SPH SPA MU WM MI SCS.
    facts. unfold A_SS in *. destruct AB as [ABa ABb]. lx_aceil.
    (* [comment removed for export] *)
    apply (rw_cells_reshape asegs mm SSB _ [C8 (Z_to_bv 64 0); C4 stored; C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]) in BX;
      [| cbn; tauto | cbn [cells_bytes cbytes app]; rewrite !app_nil_r; reflexivity ].
    lx_hide MU. lx_hide WM. pose proof (munch_refl [(lo, SP); (SSB, SSB + 16)] mm) as MU1. pose proof (wmono_refl asegs mm) as WM1.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 20%N). lx_unhide.
    match goal with H : rw_cells _ lxm SSB _ |- _ =>
      apply (rw_cells_reshape asegs lxm SSB _ [C8 (Z_to_bv 64 a); C4 stored; C4 (Z_to_bv 64 0)]) in H;
      [| cbn; tauto | cbn [cells_bytes cbytes app]; rewrite !app_nil_r; reflexivity] end.
    apply evtA_done. lx_exs. lx_ands; [> lx_mseq | match goal with MUl : munch _ mm ?mx |- _ => lx_munch MU MUl end
      | match goal with WMl : wmono _ mm ?mx |- wmono _ _ ?mx' => lx_wmono WM WMl end | ..]; lx_close.
  Qed.
End DepotB.

End ARUN_1.
