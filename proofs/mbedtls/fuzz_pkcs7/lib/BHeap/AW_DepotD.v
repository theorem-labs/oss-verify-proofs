(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_MmapFixed AW_MmapAnon AW_MmapDie AW_DepotA AW_DepotB AW_DepotC.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00157c5fa4bfa042 0 8 0 1 34 8 39 1 45 1 52 1 53 1 71 1 72 1P0038944ff0290baa 0 4 0 1 25 1 37 1 38 1P00f3497b5fd45796 0 4 0 16 24 16 31 16 32 16P0129f21fc1c68426 0 2 0 1 66 1P018da53ff17012f1 0 2 0 1 34 1P02339cb89d5b61c6 0 8 0 1 34 8 39 1 45 1 52 1 53 1 71 1 72 1P02aea24a60257656 0 4 0 1 52 1 71 1 72 1P02e3bae7195ec7be 0 2 0 1 13 1P047d75ef5e55e9be 0 8 0 1 34 8 39 1 45 1 52 1 53 1 71 1 72 1P05a1484557247432 1 1 8 3 0 1 36 1 37 1 4 28 2 35 2 38 2 39 16P05fabf4620f85ac5 1 1 8 2 0 1 72 1 7 38 1 42 16 53 1 54 1 60 1 73 1 74 8P0713f773c8c87e6d 0 4 0 1 24 1 34 1 35 1P07848970eb37d879 0 2 0 1 33 1P07efedf04a81e8f7 0 4 0 1 24 1 34 1 35 1P07ff40a1eea7d0ea 0 11 0 1 36 8 37 1 42 8 43 1 50 1 51 1 57 1 68 8 69 1 70 1P083f672b50a392f7 1 1 16 2 1 1 44 1 5 34 1 38 1 39 1 45 1 46 16P0859af8128639fd6 0 4 0 1 24 1 34 1 35 1P086e4dcdf3bd9c4f 0 8 0 1 34 8 39 1 45 1 52 1 53 1 71 1 72 1P08f4a992940b1361 0 4 0 1 37 1 43 1 44 1P09131d8191bf5dd6 0 2 0 1 71 1P0934a2b559749103 0 4 0 1 26 1 38 1 39 1P09a2b6755aed79d8 0 4 0 1 24 1 34 1 35 1P09d971b1d90cb6fd 1 1 8 3 0 1 36 1 37 1 4 28 2 35 2 38 2 39 16P0a4577bb59aeeb3a 0 5 1 1 37 8 42 1 43 16 48 1P0ab3f48a8f512017 0 2 0 1 66 1P0abf8c2ba5a1babb 0 4 0 1 24 1 34 1 35 1P0b0a55817ef48839 0 2 0 1 31 1P0b66edba5efa5648 0 5 0 1 25 1 30 1 37 1 38 1P0bda38c15b4b2bd8 0 5 1 1 33 8 38 1 39 16 44 1P0c17f55050716a16 0 4 0 1 24 1 34 1 35 1P0c924aa3d9e0cf28 0 8 0 1 34 8 39 1 45 1 52 1 53 1 71 1 72 1P0ca936664a9fb6d6 0 4 0 1 24 1 34 1 35 1P0d571c717af01e38 0 4 0 1 37 1 43 1 44 1P0e5c007dd21a611a 0 4 0 1 52 1 71 1 72 1P0e994d7e0db2e360 0 4 0 1 52 1 71 1 72 1P0f3a10df3df80102 1 1 8 3 1 1 39 1 40 1 4 31 2 38 2 41 2 42 16P10d43b02e4dac9b6 0 2 0 1 34 1P117f8d1c375b27d0 1 1 16 1 0 1 2 41 1 71 1P11d20f39c75a3ea9 0 4 0 1 26 1 38 1 39 1P120f2242ee4a3948 1 2 16 3 0 1 43 1 46 1 16 3 1 1 44 1 45 1 2 47 1 48 1P125772b42f2ae2b0 0 2 0 1 71 1P12e0f1b00af104ce 0 5 0 8 16 1 44 8 60 1 65 8P12fe880b4a22ca93 0 2 0 1 14 1P1373e5cae8fbb6a6 0 4 0 1 37 1 43 1 44 1P13a53f377530df6b 0 4 0 1 37 1 43 1 44 1P13d8f2bf715f7d08 0 4 0 1 52 1 71 1 72 1P148c9d6141c1c1b2 0 4 0 1 37 1 43 1 44 1P14cdda323127c330 0 4 0 1 24 1 34 1 35 1P14e9fb562e8c0d02 1 1 8 3 0 1 36 1 37 1 4 28 2 35 2 38 2 39 16P15222f2097fe25d8 1 1 17592186044416 1 0 1 2 25 1 28 1P15908d38b775d558 0 11 2 8 40 64 41 8 46 64 47 8 54 8 55 8 61 8 62 8 73 8 74 8P15f8227e6e648ed0 1 1 16 3 1 1 32 1 35 1 5 25 1 27 1 33 1 34 1 36 16P16a8bd2b79641c8d 0 4 0 1 32 8 37 1 43 1P16bc52fe9df13e10 0 8 0 1 32 8 37 1 43 1 50 1 51 1 69 1 70 1P16d60e405d0fa5dd 0 4 0 16 24 16 31 16 32 16P173ffc991e3a11f3 0 2 0 1 64 256P17ffee4ccc655140 0 4 0 1 52 1 71 1 72 1P18134eec27813a41 0 4 0 16 24 16 31 16 32 16P183c0d82ace8bce0 0 4 0 16 24 16 31 16 32 16P1849028ac19a7f4d 0 4 0 1 37 1 43 1 44 1P18ffd2c8a4e9920b 1 1 8 3 0 1 36 1 37 1 4 30 2 35 2 38 2 39 16P190c824497696f93 1 1 8 2 1 1 72 1 7 38 1 42 16 53 1 54 1 60 1 73 1 74 8P191b6556ccf7ecf9 1 1 16 3 1 1 44 1 47 1 6 38 1 39 1 40 1 45 1 46 1 48 16P194fb3d9e063b5c8 1 1 8 3 0 1 39 1 40 1 4 29 2 38 2 41 2 42 16P19573576995c7038 0 4 1 1 33 8 38 1 44 1P1a637653fdeda65f 0 4 0 1 26 1 38 1 39 1P1ba56d09492344b5 1 1 8 3 1 1 73 1 74 1 4 60 1 72 1 75 1 76 8P1c38746c4b4dc0df 0 4 0 16 24 16 31 16 32 16P1c659dd94bbc3a60 1 1 8 3 0 1 36 1 37 1 4 28 2 35 2 38 2 39 16P1dbffb06e9aeed01 1 1 8 1 0 1 2 67 1 68 1P1df254e5d6438c15 0 4 0 1 37 1 43 1 44 1P1df39e0b47e0a41c 0 2 0 1 33 1P1ea41b0fbc5cbcdc 0 4 0 1 52 1 71 1 72 1P1f75bc96ab0147ae 0 4 0 16 24 16 31 16 32 16P1facf43ddac36fa4 1 1 16 2 0 1 72 1 6 38 1 42 16 53 1 54 1 73 1 74 16P1fc109bc490918d4 0 5 0 1 52 1 59 1 71 1 72 1P206559dc624d3589 0 4 0 1 24 1 34 1 35 1P20f843335f442c25 0 2 0 1 31 1P21656713845345d7 1 1 8 3 0 1 36 1 37 1 4 30 2 35 2 38 2 39 16P218dea7e174c63d9 1 1 16 3 0 1 32 1 35 1 5 25 1 27 1 33 1 34 1 36 16P219d8fdc811a051c 0 2 0 1 31 1P21c55b1d3ac03241 1 1 8 3 0 1 36 1 37 1 4 30 2 35 2 38 2 39 16P2229caa52eb63e9a 0 2 0 1 30 1P22681631987b9dda 0 4 0 1 37 1 43 1 44 1P22794f449e8f701c 0 4 0 16 24 16 31 16 32 16P2288c266d81d4e68 0 2 0 1 33 1P22b5dd1872da043e 0 2 0 1 32 1P22d39878a23cb030 0 4 0 1 26 1 38 1 39 1P230f3e4fe4cd3191 1 1 8 3 0 1 36 1 37 1 4 28 2 35 2 38 2 39 16P23d0b235062588fc 1 1 16 2 1 1 44 1 5 34 1 38 1 39 1 45 1 46 16P23dbe1714fbae57e 0 4 0 1 24 1 34 1 35 1P24365da232289631 0 4 0 1 37 1 43 1 44 1P247970df9c5eeb45 0 8 0 1 34 8 39 1 45 1 52 1 53 1 71 1 72 1P24aa02ad3b827637 0 4 0 1 22 1 28 1 29 1P24bcf488e6e44d2d 0 4 0 1 24 1 34 1 35 1P265aee143191e022 0 4 0 1 37 1 43 1 44 1P265fe4d908e399d2 1 1 16 3 0 1 43 1 46 1 6 37 1 38 1 39 1 44 1 45 1 47 16P268acc2b00814900 1 2 16 2 0 1 44 1 16 2 1 1 43 1 2 45 1 46 1P26a2db7d4d4aa238 0 4 0 1 24 1 34 1 35 1P2876725d5613c40e 1 1 8 3 0 1 36 1 37 1 4 30 2 35 2 38 2 39 16P28c0833069f804fc 1 1 8 2 0 1 72 1 7 38 1 42 16 53 1 54 1 58 1 73 1 74 8P28c1fc5175a1e6ac 0 2 0 1 31 1P28c7f3a88db28fc8 0 2 0 1 71 1P29619cd32a261460 0 4 0 1 24 1 34 1 35 1P29925dd626ca8813 0 4 0 1 37 1 43 1 44 1P29cf94b2260edb34 0 2 0 1 71 1P29e8eb5d69132b0e 1 2 16 2 0 1 45 1 16 2 1 1 44 1 2 46 1 47 1P2a04ad4243b6ebf9 1 1 8 3 0 1 36 1 37 1 4 30 2 35 2 38 2 39 16P2ad0824549de1292 0 4 0 1 25 1 37 1 38 1P2b72481e721d4bc7 0 11 0 1 36 8 37 1 42 8 43 1 50 1 51 1 55 1 68 8 69 1 70 1P2b90d5140130a917 0 8 0 1 34 8 39 1 45 1 52 1 53 1 71 1 72 1P2bbc3aff25af04c3 1 1 16 3 1 1 44 1 47 1 6 38 1 39 1 40 1 45 1 46 1 48 16P2c2e2fd205cbc900 0 4 0 1 24 1 34 1 35 1P2cfe0ebb85cad141 0 8 0 1 34 8 39 1 45 1 52 1 53 1 71 1 72 1P2d6062f4c1a81f44 0 4 0 1 36 1 42 1 43 1P2da4fea7f46d0056 0 2 0 1 33 1P2dc147d261074ee8 0 2 0 1 33 1P2dd41a87a6419310 0 2 0 1 30 1P2e5e684157b262b1 1 1 8 3 0 1 36 1 37 1 4 28 2 35 2 38 2 39 16P2e8e513c0cc95a1e 1 1 256 1 0 1 2 65 1 68 1P2e98624c363db82b 1 1 16 1 0 1 2 42 1 71 1P2eb8450f26184248 0 4 0 1 24 1 34 1 35 1P2eeb0ae30c6feaf7 0 4 0 16 24 16 31 16 32 16P2f38996290218b82 1 1 8 2 1 1 72 1 6 38 1 53 1 54 1 60 1 73 1 74 8P2fb7257395150f6d 0 4 0 1 24 1 34 1 35 1P30842f76a5a70b5d 0 4 0 1 37 1 43 1 44 1P312723c7c3051109 1 1 16 3 1 1 32 1 35 1 5 25 1 27 1 33 1 34 1 36 16P31c819de3b36ffec 0 4 0 1 24 1 34 1 35 1P32c2263c843b3ec0 0 4 0 1 24 1 34 1 35 1P333bd400903c1b46 0 4 0 1 26 1 38 1 39 1P345385be3117372b 0 4 0 1 26 1 38 1 39 1P34c94ee270a5fab3 1 1 8 3 0 1 36 1 37 1 4 30 2 35 2 38 2 39 16P35123e4a677c012b 0 4 0 1 24 1 34 1 35 1P35685515a39213ee 0 4 0 16 24 16 31 16 32 16P35a6cc35f494643c 1 1 8 3 0 1 39 1 40 1 4 31 2 38 2 41 2 42 16P35ae4a7ab892c358 1 1 8 3 0 1 36 1 37 1 4 30 2 35 2 38 2 39 16P35f5f34c79fa616d 0 4 0 1 25 1 37 1 38 1P36764c6f4b26a91e 0 2 0 1 34 1P373a764756818faa 1 1 16 1 1 1 2 43 1 72 1P384b067ae36d6da8 0 4 0 1 26 1 38 1 39 1P385250bd6b532d25 0 4 0 1 37 1 43 1 44 1P385b49a9fc1951ec 0 4 0 1 52 1 71 1 72 1P3a20f5d9d32cbf6b 0 2 0 1 34 1P3a254dbc5e8b05b1 1 1 8 3 0 1 36 1 37 1 4 28 2 35 2 38 2 39 16P3aae46ba21610df0 0 4 0 1 24 1 34 1 35 1P3acd130c3327dda0 0 4 0 1 52 1 71 1 72 1P3b11c9649ebd9d4d 0 2 0 1 32 1P3c0b0ac64e8aae4e 1 2 16 2 0 1 44 1 16 2 1 1 43 1 2 45 1 46 1P3c418f14ce2df196 0 4 0 1 37 1 43 1 44 1P3c49a3cce56cd36e 1 2 16 2 0 1 45 1 16 2 1 1 44 1 2 46 1 47 1P3c532b576f148ba0 1 1 16 3 1 1 32 1 35 1 5 25 1 27 1 33 1 34 1 36 16P3ca3e103c5db9498 0 11 1 8 39 64 40 8 45 64 46 8 53 8 54 8 60 8 71 64 72 8 73 8P3cc133b92d559e69 0 5 0 1 36 8 41 1 42 16 47 1P3cecd745f4ff805b 0 2 0 1 32 1P3d6938db728487e8 0 4 0 1 22 1 28 1 29 1P3e46d4cf6a3cef3b 0 4 0 1 24 1 34 1 35 1P3eac1e59e0f9dea5 0 4 0 1 37 1 43 1 44 1P3ebf85c9893dae1d 0 4 0 1 26 1 38 1 39 1P3ef892fc17064255 0 4 0 1 52 1 71 1 72 1P3f711009b636a36d 0 4 0 1 22 1 28 1 29 1P3f94d0385c04fd9c 1 1 16 3 0 1 43 1 46 1 6 37 1 38 1 39 1 44 1 45 1 47 16P3fe3d0a6791c95bb 0 2 0 1 34 1N0113924e42eb95d4N0259ca6bbd39c13dN03c0027b336a9158N05973c0fe9fb847fN07eaa1343e2bd0beN0b0c2ddd4ce7b2bdN0bd48d5456817711N0c0dcd87257b500cN0d73ddbd649c6c19N0db3a44fbed9786bN0dc98a9191ef062eN0e4cf95c79841d08N0ed18f8ba81ccba7N1204e850dab4edf9N125f3ed9d9e8ce15N15a9a436f112e049N18b51760c1d3fa9eN19635a084bcf9ea0N196bfa715bd2e104N1986f53551cd1a0dN1a9b6eb134d1c111N1d567921cc1113b5N1ee2a375fbf44427N1ef3bf75198b660fN20a949f3f40c7dc0N23e91bda9b7d0accN249d4066dce98e9dN255f0d81febc6b45N269815ad5b4abd59N26bc4403ef3e6eb5N26e641b9adb2165fN280ec2482a583540N2917abf0e756203bN2b2b8cab5996e940N2d5facc6768152aaN2f0402648e4ab65cN2f262b133848c0f9N305a086ab5c56cc3N31e8cb66c6b81039N3401dc99611e1149N35870937cf3305a6N35d9a33d61d0eb09N37244b9b196b94ecN387861ca565fd3afN38b1479f5d126407N391e68b54a61a08bN397a4a80bc6caac9N39e77c5310c6f3deN3aafaeb926997865N3ca87f08a115219dN3d56f3cc38646953N3e89d8648fb124a7N3eda44d3527cfaa1N3f060c481b8d2dd1N3f1522a6b62ddfa7N3f1de24360592e1d"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_DepotD () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotB.A_SS"; "ARUN_1.A_SS_STORE"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "ARUN_1.A_DNODE_STORE"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotC.A_SS_ALLOC"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotC.sblk"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_DepotC.dblocks"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8ro"; "Corelib.Init.Logic.or"].

Section ARUN_1. Context {hAR : arun}.
Definition A_SS_STORE : Z := 0x086fa4.
Definition A_DNODE_STORE : Z := 0x0892b8.

Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L21755615567.3L24263045810.3L25160782343.3L30429790369.3L56093676630.3L65502424806.300000600900:00;00A00BS1x2HxS1xSSS1x2HxS". (* [comment removed for export] *)
#[using="Type"] Lemma shr16_land_m16 : forall x, 0 <= x < 2^64 -> Z.land (Z.shiftr x 16) 18446744073709551600 = 16 * (x / 2^20).
Proof.
  intros x Hx. rewrite land_align4 by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  rewrite Z.shiftr_div_pow2 by lia. change (2^20) with (2^16 * 16). rewrite <- Z.div_div by lia. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section DepotD.
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
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L17641836897.1L38884636053.0L56440035712.300000700800GS5startSS5start3SBa3SBb". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma ss_alloc_C : ltac2:(CDefT.buildp (gd_tbl_AW_DepotD ()) "Pra,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)PSP,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(3.(0.&8.))Pm,P,(0.&40.)(3.(0.&8.))Pa,$1.Pstart,$1.Plo,$1.PW,(4.(5.$1.$1.))P,(6.(7.=R4.)(7.R4.(8.+2.+2?.)))P,(6.(9.=R4.)(7.R4.(8.+2.+20.)))P,(:.$;.R7.(<.R;.-10.)(=.$>.(?.R22.)(=.$>.(?.R28.)(10.$>.))))P,(11.$;.R8.R5.(<.R<.-10.))P,(9.+65?000.R6.)P,(9.R7.(12.R>.+10.))P,(9.R?.(8.+2.+3?.))P,(13.$1.(14.R10.+10.)=)P,(15.VCS,R:.(12.R11.R:.))P,(16.(=.(5.$1.$1.)(17.$1.$1.R;.R12.)R:.)R?.R>.)P,(18.$;.R10.R?.)P,(19.$;.R10.)(1:.$;.VAL,VCS,Lms',$1;.(1<.P,(0.&40.)(3.(0.&8.))Lm',P,(0.&40.)(3.(0.&8.))(6.(13.$1;.R2.(1=.(1>.R34.(1?.&40.R17.)R33.R32.R31.R30.R2?.R2>.R2=.(1?.&40.(<.R12.(20.+8.(14.R11.(8.+2.+14.)))))R1>.R1=.R1<.R1;.R1:.R19.R18.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R16.(21.R34.)R15.(22.(0.&40.))R1.(23.$;.)))(6.(16.(=.(5.$1.$1.)(17.$1.$1.R10.R17.)R?.)R14.R1.)(6.(18.$;.R14.R1.)(6.(19.$;.R1.)(11.$;.R1.R10.R17.))))))(1=.(1>.(1?.&40.+871=<.)(1?.&40.(<.R15.-10.))R31.R30.R2?.R2>.R2=.(1?.&40.R?.)R2;.(1?.&40.R10.)R1<.R1;.R1:.R19.R18.R17.R16.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.)R14.(1?.&40.+871=<.)R13.(22.(0.&40.))R11.(23.$;.)))")
(* [comment removed for export] *).
  Proof.
    pose proof (I : lx_noaceil) as LXNOACEIL.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a1 a2 a3 a4 a5 a6 a7 SP F fc m0 m a start lo W
      AB SB FR ST LOIMG SPL SPH SPA SCS MU WM MI.
    facts. destruct AB as [ABa ABb]. destruct SB as [SBa SBb]. lx_aceil.
    lx_hide MU. lx_hide WM. pose proof (munch_refl [(lo, SP)] m) as MU1. pose proof (wmono_refl asegs m) as WM1.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 20%N). lx_unhide.
    match goal with |- context [?e ≫ 41] =>
      replace (e ≫ 41) with (8 * (start mod 2 ^ 20)) by (rewrite <- (shl44_shr41 start) by (clear -SBa SBb; lia);
         rewrite Z.shiftl_mul_pow2 by (clear; lia); unfold zlow; f_equal; f_equal; clear; lia) end.
    apply evtA_done. lx_exs. lx_ands; [> lx_mseq | match goal with MUl : munch _ m ?mx |- _ => lx_munch MU MUl end
      | match goal with WMl : wmono _ m ?mx |- wmono _ _ ?mx' => lx_wmono WM WMl end | ..]; lx_close.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L21118651370.1 L24524508047.56L3504570907.75 L48946057699.2 L53716433642.1 L54658177319.2 L7005163614.1  00000400H00I00J00N00O00PS2SPS3hAR2SP4NODE2lo3SPLFFS2SPFF". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma dnode_store_A : ltac2:(CDefT.buildp (gd_tbl_AW_DepotD ()) "Pra,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pa1,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Phsh,(0.&40.)Psid,(0.&40.)Plnk,$1.PSP,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(3.(0.&8.))PNODE,$1.PARGS,$1.Ph,$1.Plo,$1.P,(6.(9.=R2.)(7.R2.(8.+2.+40.)))P,(9.+65?000.R5.)P,(9.(<.R6.+10.)(24.VhAR,))P,(13.$1.(14.R7.+10.)=)P,(15.VCS,R8.+10.)P,(9.(<.R9.+10.)R6.)P,(:.$;.R;.R:.(=.$>.(?.R11.)(=.$>.(25.(1?.&40.R?.))(=.$>.(25.R10.)(10.$>.)))))P,(11.$;.R<.R8.R?.)P,(9.+65?000.R9.)P,(9.R:.(12.R11.+20.))P,(9.R12.(8.+2.+3?.))P,(13.$1.(14.R13.+10.)=)P,(15.VCS,R=.(12.R14.R=.))P,(19.$;.R12.)(1:.$;.VAL,VCS,Lms',$1;.(1<.P,(0.&40.)(3.(0.&8.))Lm',P,(0.&40.)(3.(0.&8.))(1<.(4.(0.&8.))Lfr,(4.(0.&8.))(6.(13.$1;.R3.(1=.(1>.(1?.&40.+892>4.)(1?.&40.(<.R19.-20.))R36.R35.R34.R33.R32.(1?.&40.R15.)R30.(1?.&40.$26.)(1?.&40.R14.)(1?.&40.(<.R19.-18.))(1?.&40.R13.)R20.R1?.R1>.R1=.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.)R18.(1?.&40.$27.)R17.(22.(0.&40.))R2.(23.$;.)))(6.(16.(=.(5.$1.$1.)(17.$1.$1.R12.R19.)(=.(5.$1.$1.)(17.$1.$1.R15.(<.R15.+10.))(10.(5.$1.$1.))))R16.R2.)(6.(18.$;.R16.R2.)(6.(19.$;.R2.)(6.(:.$;.R2.(<.R19.-20.)(=.$>.(28.#8.R1.)(10.$>.)))(6.(:.$;.R2.(<.R19.-18.)(=.$>.(?.(1?.&40.=))(10.$>.)))(6.(:.$;.R2.(<.R19.-10.)(=.$>.(?.R31.)(=.$>.(?.R37.)(10.$>.))))(6.(:.$;.R2.R15.(=.$>.(?.(1?.&40.R13.))(=.$>.(25.(1?.&40.R1:.))(=.$>.(25.R1;.)(10.$>.)))))(11.$;.R2.R12.(<.R19.-20.))))))))))))(1=.(1>.R34.(1?.&40.R16.)R33.R32.R31.R30.R2?.R2>.R2=.(1?.&40.R12.)R1>.(1?.&40.R11.)(1?.&40.R10.)R1=.R1<.R1;.R1:.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R15.(1?.&40.$29.)R14.(22.(0.&40.))R13.(23.$;.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a1 a4 a5 a6 a7 hsh sid lnk SP F fc m NODE ARGS h lo
      HR N0 N1 NAL NCS NLO NC ST LOIMG SPL SPH SPA SCS MI.
    facts. unfold A_DNODE_STORE, A_SS_STORE, A_SS.
    pose proof (munch_refl [(lo, SP); (NODE, NODE + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    destruct HR as [HRa HRb]. rewrite <- (Z_to_bv_bv_unsigned sid) in NC. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x86fa4] [] 20%N).

    lazymatch goal with ST' : stk _ lxm lo ?top |- _ =>
      lx_carve ST' 8%nat ST2 FRj fr;
      match goal with H : rw_cells _ lxm top _ |- _ =>
        pose proof (proj1 (rw_cells_app asegs lxm top [C8 _] _) H) as [F2 F3]; cbn [cells_size csize Nat.add] in F3 end end.
    apply evtA_done. lx_exs. lx_ands; [> lx_mseq | ..]; lx_close.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac dnB_leaf lo MU WM := lx_unhide; lx_stk_grow lo; apply evtA_done; lx_exs;
      lx_ands; [> lx_mseq | match goal with MUl : munch _ ?m ?mx, WMl : wmono _ ?m ?mx |- munch _ _ ?mx => lx_munch MU MUl end
               | match goal with WMl : wmono _ ?m ?mx |- wmono _ _ ?mx => lx_wmono WM WMl end | ..]; lx_close.
  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0?L19495415587.2 L2121541086.1  L23406774706.1 L29108423139.64L31510112766.1 L34194295638.2 L37481943406.1 L44888174350.1 L48379654119.2 L49484650222.1 L52997233623.2 L61544436598.1 L63957897683.64L64551628823.64L7005163614.1  00000100200600J00N00O00S00W00X00Y00Z00^01201F01GFFS2SPS3hAR2SP4NODE2lo3SPLS2SPFS2SPS2SPFFFS2SPS3hAR2SP4NODE2lo3SPLS3hAR2SP4NODE2lo3SPLF". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma dnode_store_B : ltac2:(CDefT.buildp (gd_tbl_AW_DepotD ()) "Pra,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Psid',(0.&40.)Phsh,(0.&40.)Psid,(0.&40.)Ppkw,(0.&40.)Plnkw,(0.&40.)PSP,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(3.(0.&8.))Pm,P,(0.&40.)(3.(0.&8.))PNODE,$1.Plo,$1.Pfr,(4.(0.&8.))PW,(4.(5.$1.$1.))P,(9.+65?000.R4.)P,(9.(<.R5.+10.)(24.VhAR,))P,(13.$1.(14.R6.+10.)=)P,(15.VCS,R7.+10.)P,(:.$;.R9.(<.R=.-20.)(=.$>.(28.#8.R6.)(10.$>.)))P,(:.$;.R:.(<.R>.-18.)(=.$>.(?.R10.)(10.$>.)))P,(:.$;.R;.(<.R?.-10.)(=.$>.(?.R2;.)(=.$>.(?.R31.)(10.$>.))))P,(:.$;.R<.R;.(=.$>.(?.R14.)(=.$>.(25.R11.)(=.$>.(25.R13.)(10.$>.)))))P,(2:.$;.R=.$2;.(=.$>.(?.(1?.&40.$2<.))(10.$>.)))P,(2:.$;.R>.(<.$2<.+?0.)(=.$>.(25.(1?.&40.=))(10.$>.)))P,(11.$;.R?.R=.(<.R13.-20.))P,(9.(24.VhAR,)R>.)P,(9.R?.(12.R15.+30.))P,(9.R16.(8.+2.+3?.))P,(13.$1.(14.R17.+10.)=)P,(15.VCS,R12.(12.R18.R12.))P,(16.(=.(5.$1.$1.)(17.$1.$1.R13.R19.)(=.(5.$1.$1.)(17.$1.$1.R14.(<.R14.+10.))R11.))R16.R15.)P,(18.$;.R17.R16.)P,(19.$;.R17.)(1:.$;.VAL,VCS,Lms',$1;.(1<.(0.&40.)Lx0,(0.&40.)(1<.(0.&40.)Lx1,(0.&40.)(1<.(0.&40.)Lsidw,(0.&40.)(1<.P,(0.&40.)(3.(0.&8.))Lm',P,(0.&40.)(3.(0.&8.))(6.(13.$1;.R5.(1=.(1>.R43.(1?.&40.R21.)R42.R41.R40.R3?.R3>.R3=.R3<.R4.R3.R2<.R2;.R2:.R29.R28.R27.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.)R20.(21.R43.)R1?.(22.(0.&40.))R1.(23.$;.)))(6.(16.(=.(5.$1.$1.)(17.$1.$1.R1;.R21.)(=.(5.$1.$1.)(17.$1.$1.R1<.(<.R1<.+10.))R19.))R1>.R1.)(6.(18.$;.R1>.R1.)(6.(19.$;.R1.)(6.(:.$;.R1.R1<.(=.$>.(?.R25.)(=.$>.(25.R22.)(=.$>.(25.R2.)(10.$>.)))))(11.$;.R1.R1;.R21.))))))))))(1=.(1>.(1?.&40.+892>4.)(1?.&40.(<.R1<.-20.))R3=.R3<.R3;.R3:.R39.(1?.&40.R17.)R37.R21.R28.R27.R26.R25.R24.R23.R22.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.)R1;.(1?.&40.+892>4.)R1:.(22.(0.&40.))R18.(23.$;.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a1 a2 a3 a4 a5 a6 a7 sid' hsh sid pkw lnkw SP F fc m0 m NODE lo fr W
      N0 N1 NAL NCS F1 F2 F3 NC GOTF CF ST LOIMG SPL SPH SPA SCS MU WM MI.
    facts. unfold A_GOT_CFLAGS, A_CFLAGS in *. change (1684776 + 240) with 1685016 in *.
    pose proof (bv_unsigned_in_range 64 pkw) as PKR. unfold bv_modulus in PKR. change (2 ^ Z.of_N 64) with 18446744073709551616 in PKR. destruct PKR as [PKa PKb].
    rewrite <- (Z_to_bv_bv_unsigned pkw) in F2. rewrite <- (Z_to_bv_bv_unsigned sid') .
    lx_hide MU. lx_hide WM. pose proof (munch_refl [(lo, SP); (NODE, NODE + 16)] m) as MU1. pose proof (wmono_refl asegs m) as WM1. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 40%N).
    all: dnB_leaf lo MU WM.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L53519168656.11L59308579281.11L9410801332.11 00000100P015SS4size3tag3SZa3TGa3LXE2H02H12H2S4size3tag3SZa3SZb3TGa3TGb1H2H02H12H2". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma ss_store_A : ltac2:(CDefT.buildp (gd_tbl_AW_DepotD ()) "Pra,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ppkw,(0.&40.)PSP,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(3.(0.&8.))PARGS,$1.PPACK,$1.PTR,$1.Psize,$1.Ptag,$1.Plo,$1.P,(6.(9.+1.R3.)(9.R3.+1>.))P,(6.(9.=R3.)(7.R3.+100.))P,(2:.$;.R9.R8.(=.$>.(?.(1?.&40.R6.))(=.$>.(25.(1?.&40.R5.))(=.$>.(25.(1?.&40.R4.))(10.$>.)))))P,(:.$;.R:.R8.(=.$>.(?.R>.)(10.$>.)))P,(9.R>.R9.)P,(9.(<.R:.+8.)(8.+2.+3?.))P,(13.$1.(14.R;.+8.)=)P,(15.VCS,R<.+8.)P,(9.R12.R>.)P,(9.(<.R?.+10.)(8.+2.+3?.))P,(13.$1.(14.R10.+8.)=)P,(15.VCS,R11.+10.)P,(11.$;.R13.R=.R16.)P,(9.+65?000.R>.)P,(9.R?.(12.R18.+40.))P,(9.R19.(8.+2.+3?.))P,(13.$1.(14.R1:.+10.)=)P,(15.VCS,R12.(12.R1;.R12.))P,(19.$;.R19.)(1:.$;.VAL,VCS,Lms',$1;.(1<.P,(0.&40.)(3.(0.&8.))Lm',P,(0.&40.)(3.(0.&8.))(6.(13.$1;.R2.(1=.(1>.(1?.&40.+8701<.)(1?.&40.(<.R1?.-40.))R3:.R39.R38.R37.R36.(1?.&40.R1:.)(1?.&40.$26.)(1?.&40.$26.)(1?.&40.(<.R18.+1.))(1?.&40.(<.R1?.-40.))(1?.&40.R1:.)R24.R23.R22.R21.(1?.&40.(<.R18.+1.))(1?.&40.R1;.)(1?.&40.R18.)(1?.&40.R17.)R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.)R1>.(1?.&40.$2=.)R1=.(22.(0.&40.))R1.(23.$;.)))(6.(16.(=.(5.$1.$1.)(17.$1.$1.R16.R1?.)(=.(5.$1.$1.)(17.$1.$1.R1:.(<.R1:.+8.))(10.(5.$1.$1.))))R1<.R1.)(6.(18.$;.R1<.R1.)(6.(19.$;.R1.)(6.(:.$;.R1.(<.R1?.-40.)(=.$>.(?.(1?.&40.=))(=.$>.(?.R30.)(=.$>.(?.R31.)(=.$>.(?.R32.)(=.$>.(?.R33.)(=.$>.(?.R34.)(=.$>.(?.R35.)(=.$>.(?.R3;.)(10.$>.))))))))))(6.(:.$;.R1.R1:.(=.$>.(?.(1?.&40.=))(10.$>.)))(11.$;.R1.R16.(<.R1?.-40.)))))))))(1=.(1>.R39.(1?.&40.R1=.)R38.R37.R36.R35.R34.R33.R32.(1?.&40.$26.)(1?.&40.R19.)(1?.&40.R18.)R23.R22.R21.R20.R1?.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.)R1<.(1?.&40.$27.)R1;.(22.(0.&40.))R1:.(23.$;.)))")
(* [comment removed for export] *).
  Proof.
    pose proof (I : lx_noaceil) as LXNOACEIL.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a3 a4 a5 a6 a7 pkw SP F fc m ARGS PACK TR size tag lo
      SZ TG AR PX P0 P1 PAL PCS A0 A1 AAL ACS ST LOIMG SPL SPH SPA SCS MI.
    facts. unfold A_SS_STORE, A_SS_ALLOC, A_SS.
    pose proof (munch_refl [(lo, SP); (PACK, PACK + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    destruct SZ as [SZa SZb]. destruct TG as [TGa TGb]. rewrite <- (Z_to_bv_bv_unsigned pkw) in PX. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x870c8] [] 40%N).
    2: { (* [comment removed for export] *)
         exfalso. clear -LXKF SZa SZb TGa TGb. lx_bool_norm.
         pose proof (Z.add_lor_land size tag). pose proof (Z.land_nonneg size tag). pose proof (Z.lor_nonneg size tag).
         pose proof (proj1 (Z.lor_eq_0_iff size tag)).
         match goal with K : context [zlow 64 (Z.lor size tag)] |- _ => unfold zlow in K; rewrite !Z.mod_small in K by lia end. lia. }
    apply evtA_done. lx_exs. lx_ands; [> lx_mseq | ..]; lx_close.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0110@L10105082325.139L11801586693.139L12990851393.133L14193870298.133L14446456502.140L15356495653.135L18926375243.106L18928761373.105L18928845742.108L18928859419.101L18933043916.107L18948131869.151L19848182124.101L20379586926.133L20721966059.148L22329762169.133L22706564936.140L25662132824.133L25669137098.133L26485397226.119L26682560564.105L27093306110.133L29640030297.117L29693764446.133L30264375051.150L31920398846.141L32406018003.151L32610790911.2  L33215085262.111L35155120135.101L40470042928.130L40551545283.133L41124817077.16 L41679436175.139L42878765528.133L44484923210.138L45291350887.105L45291351008.98 L47191757171.134L47214579400.149L50453190795.139L51125630956.1  L51489811758.105L51489811759.105L54784554794.113L55539028805.151L55626344680.151L55755038203.1  L56454697590.134L56454697590.136L58804783273.133L59726336417.0  L60106036803.103L62416617628.133L62541917565.139L6391859077.133 L65514616842.134L6574046823.130 L67345469530.108L7239719492.111 L855329896.108  L8635801058.119 L8765792224.151 L8767966915.121 L9607942022.133 00000l02V04;05Z07?08908f09S0:@0:k0;X0=40>@0?S0@M0@N0AS0BP0Cd0E50F50GL0HY0HZ0JB0Kg0ML0MR0NA0Nl0Oa0Q=0Qn0SY0U30VY0Xj0Ze0\J0^70^80^90`40a40bI0ck0eN0eQ0fW0g]0iC0iD0jU0l=0mY0o50oo10`11o13J14d16717317o19LS3hAR2SP4ARGS4PACK4size5start2bl2ss5count1B1P2S03DBL4junk2LJS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1B1P2S03DBL2P02A05LOIMG3SPL3off2HP2HC2B02B12PB4junk2LJ1j2JL2SMS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1B1P2S03DBL2P02A05LOIMG3SPL3off2HP2HC2B02B12SM2PB4junk2LJS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1B1P2S03DBL2P02A05LOIMG3SPL3off2HP2HC2B02PB4junk2LJS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1B1P2S03DBL2P02A05LOIMG3SPL3off2HP2HC2B02B12SM2PB4junk2LJS3hAR2SP4ARGS4PACK4size5start2bl2ss5count1B2S03DBL4junk2LJS3hAR2SP4ARGS4PACK5start2bl2ss5count1B2S03DBLS3hAR2SP4ARGS4PACK5start2bl2ss5count1B2S03DBLS3hAR2SP4ARGS4PACK5start2bl2ss5count1B2S03DBLS3hAR2SP4ARGS4PACK5start2bl2ss5count2S03DBLS3hAR2SP4ARGS4PACK5start2bl2ss5count1B2S03DBLS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1B1P3SZa2S03DBL2LS2P02A05LOIMG3SPL2HC2B04junk2LJS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count2S02S13DBL2LS2P02A05LOIMG3SPL2HCS3hAR2SP4ARGS4PACK2TR4size5start2lo2bl2ss5count1B2S03DBL2A02T05LOIMG3SPL2B04junk2LJS3hAR2SP4ARGS4PACK4size5start2bl2ss5count1B2S03DBL4junk2LJFS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1B1P2S03DBL4junk2LJ2x32H7S3hAR2SP4ARGS4PACK2TR4size5start2bl2ss5count1B2S03DBL4junk2LJS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1B3SZa2S03DBL2P02A05LOIMG3SPL2B04junk2LJS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1B2SZ2S03DBL2LS2P02A05LOIMG3SPL2HC2B0S3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1j1B2S04junk2LJ1y2HyS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1B3SZa2S03DBL2P02A05LOIMG3SPL2HC2B04junk2LJS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1B1P2S03DBL2LS2P02A05LOIMG3SPL2B0FS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1j1B1P2S03DBL2LS2P02A05LOIMG3SPL3off2HP3JBb2B02B12SM4junk2LJS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1B1P2S03DBL2P02A05LOIMG3SPL3off2HP2HC2B02B12SM2PB4junk2LJS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1B1P2S03DBL2LS2P02A05LOIMG3SPL3off2HP2HC2B02SM2PB4junk2LJS1j2j0S3hAR2SP4ARGS4PACK5start2bl2ss5count1j1B2S03DBLS3hAR2SP4ARGS4PACK5start2bl2ss5count2S03DBLS3hAR2SP4size5start2lo2bl2ss5count2S03DBL3SPL4junk2LJS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1B1P2S03DBL2P02A05LOIMG3SPL3off2HP2B02SM4junk2LJS3hAR2SP4PACK2lo1j1B2P05LOIMG3SPL3JBb2B02j02Hj2NES3hAR2SP4ARGS4PACK2TR4size5start2lo2bl2ss5count1B1P2S03DBL2LS2P02A02T05LOIMG3SPL3off2HP2HC2B02B12PB4junk2LJS3hAR2SP4ARGS4PACK2TR4size5start2lo2bl2ss5count1B3SZb2S03DBL2P02A05LOIMG3SPL2HC2B04junk2LJS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1B1P3SZa2S03DBL2P02A05LOIMG3SPL3off2HP2HC2B02B12PB4junk2LJS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1j1B1P3SZa2S02S12LS2P03PAL2A03AAL5LOIMG3SPL3SPA2HJ3off2HP2HC2B02B12SM2PB4junk2LJ1y2Hy3H173H193H183H20S3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1j1B1P2S02SJ2LS2P03PAL2A03AAL5LOIMG3SPL3SPA2HJ3off2HP2HC2B02B12PB4junk2LJ1y3H12S3hAR2SP4ARGS4PACK2TR4size5start2lo2bl2ss5count1B1P2S03DBL2P02A02T05LOIMG3SPL3off2HP2B02B12SM4junk2LJS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1j1B1P2S02JL3DBL2LS2P02A05LOIMG3SPL3off2HP2HC2B02B12SM2PB4junk2LJFFS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1j1B3SZa2S02S12LS2P03PAL2A03AAL5LOIMG3SPL3SPA2HJ2HC2B04junk2LJ1y2Hy3H183H173H19S3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1j1B2S04junk2LJ1y2HyS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1B2S03DBL2LS2P02A05LOIMG3SPL3off2HC2B02PBS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1B1P2S03DBL2LS2P02A05LOIMG3SPL3off2HP2HC2B02PB4junk2LJS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1B1P3SZa2S03DBL2P02A05LOIMG3SPL3off2HP2HC2B02PB4junk2LJS1jS3hAR2SP4ARGS4PACK4size5start2bl2ss5count1B2S02S13DBL2LS2HC2B04junk2LJS3hAR2SP4ARGS4PACK4size5start2bl2ss5count1B2S02S13DBL2LS2HC2B04junk2LJS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1B1P3SZa2S03DBL2P02A05LOIMG3SPL3off2HP2HC2B02B12PB4junk2LJSS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1j2SZ2S02JL3DBL2P02A05LOIMG3SPL2HJ2HCS3hAR2SP4ARGS4PACK2TR4size5start2lo2bl2ss5count1B1P2S03DBL2P02A02T05LOIMG3SPL3off2HP2HC2B02B12PB4junk2LJS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1B1P2S03DBL2P02A05LOIMG3SPL3off2HP2B02SM4junk2LJS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1B1P2S03DBL2P02A05LOIMG3SPL3off2HP2B02SM4junk2LJS3hAR2SP4ARGS4PACK4size5start2bl2ss5count1B2S03DBL4junk2LJS3hAR2SP4size5start2lo2bl2ss5count2S03DBL4junk2LJS3hAR2SP4ARGS4PACK5start2lo2bl2ss5count1B1P2S03DBL2P02A05LOIMG3SPL3off2HP2B02SMS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1B2SZ2S03DBL2LS2P02A05LOIMG3SPL3off2HC2B02SM2PBS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1B1P2S03DBL2LS2P02A05LOIMG3SPL3off2HP2HC2B02PBS3hAR2SP4ARGS4PACK4size5start2lo2bl2ss5count1B1P2SZ2S03DBL2LS2P02A05LOIMG3SPL2HC2B0S3hAR2SP4ARGS4PACK4size5start2bl2ss5count1B1P2S03DBL4junk2LJS3hAR2SP4ARGS4PACK4size5start2bl2ss5count1B1P2S03DBL4junk2LJS3hAR2SP4ARGS4PACK2TR4size5start2lo2bl2ss5count1B3SZb2S03DBL2P02A02T15LOIMG3SPL2HC2B04junk2LJ". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma ss_store_B : ltac2:(CDefT.buildp (gd_tbl_AW_DepotD ()) "Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)Pa2,(0.&40.)Pa4,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Pa1,(0.&40.)Pa3,(0.&40.)Pa5,(0.&40.)Palloc,(0.&40.)Ppkw,(0.&40.)Pra0,(0.&40.)Pq0,(0.&40.)Pq1,(0.&40.)Pq2,(0.&40.)Pq3,(0.&40.)Pq4,(0.&40.)Pq5,(0.&40.)PSP,$1.PF,(2.&5.(0.&40.))Pfc,(0.&20.)Pm0,P,(0.&40.)(3.(0.&8.))Pm,P,(0.&40.)(3.(0.&8.))PARGS,$1.PPACK,$1.PTR,$1.Psize,$1.Ptag,$1.Pstart,$1.Plo,$1.Pbl,(4.$1.)Pss,(4.(0.&8.))Zcount,$1.(<.R6.+1.)Zj,$1.(2>.R5.(8.+2.+14.))ZB,$1.(2?.R4.R1.)ZP,$1.(<.R1.(20.+8.(14.R7.(8.+2.+14.))))P,(6.(9.+1.R:.)(9.R:.+1>.))P,(6.(9.=R:.)(7.R:.+100.))P,(9.=R:.)P,(7.(<.R;.R7.)(8.+2.+20.))P,(13.$1.R7.(2>.(12.(<.R<.R8.)+1.)(8.+2.+14.)))P,(7.R8.(30.(31.$1.R;.)))P,(:.$;.R14.(<.R18.-40.)(=.$>.(?.(1?.&40.R>.))(=.$>.(?.R19.)(=.$>.(?.R1:.)(=.$>.(?.R1;.)(=.$>.(?.R1<.)(=.$>.(?.R1=.)(=.$>.(?.R1>.)(=.$>.(?.R1?.)(10.$>.))))))))))P,(:.$;.R15.$26.(=.$>.(?.(1?.&40.(<.R?.R;.)))(=.$>.(?.R22.)(10.$>.))))P,(32.VhAR,R16.R>.)P,(:.$;.R17.R15.(=.$>.(?.R23.)(10.$>.)))P,(2:.$;.R18.R17.(=.$>.(?.(1?.&40.R15.))(=.$>.(25.(1?.&40.R14.))(=.$>.(25.(1?.&40.R13.))(10.$>.)))))P,(33.$;.R19.R16.R10.)P,(13.$1.(30.(31.(0.&8.)R11.))(20.+8.R16.))P,(11.$;.R1;.R?.(<.R?.(8.+2.+17.)))P,(15.VCS,R10.(8.+2.+17.))P,(9.R21.R1;.)P,(9.(<.R1<.+8.)(8.+2.+3?.))P,(13.$1.(14.R1=.+8.)=)P,(15.VCS,R1>.+8.)P,(9.R25.R20.)P,(9.(<.R21.+10.)(8.+2.+3?.))P,(13.$1.(14.R22.+8.)=)P,(15.VCS,R23.+10.)P,(9.R29.R22.)P,(9.(<.R23.+?0.)(8.+2.+3?.))P,(15.VCS,R24.+?0.)P,(34.(9.(<.R27.+10.)R26.)(9.(<.R26.+8.)R27.))P,(34.(9.(<.R26.+?0.)R27.)(9.(<.R27.+8.)R26.))P,(11.$;.R2:.R23.(<.R2>.-40.))P,(9.(24.VhAR,)R24.)P,(9.R25.(12.(12.R30.+40.)+10.))P,(9.R31.(8.+2.+3?.))P,(13.$1.(14.R32.+10.)=)P,(15.VCS,R28.(12.R33.R28.))P,(16.(=.(5.$1.$1.)(17.$1.$1.R29.R34.)(=.(5.$1.$1.)(17.$1.$1.R2>.(<.R2>.+8.))(=.(5.$1.$1.)(17.$1.$1.$26.(<.(<.$26.+10.)(20.+10.+1000.)))(=.(5.$1.$1.)(17.$1.$1.R24.(<.R24.(8.+2.+17.)))(10.(5.$1.$1.))))))R31.R30.)P,(18.$;.R32.R31.)P,(19.$;.R32.)(1:.$;.VAL,VCS,Lms',$1;.(1<.(0.&40.)Lx5,(0.&40.)(1<.(0.&40.)Lx6,(0.&40.)(1<.(0.&40.)Lx7,(0.&40.)(1<.(0.&40.)Lx10,(0.&40.)(1<.(0.&40.)Lx11,(0.&40.)(1<.(0.&40.)Lx12,(0.&40.)(1<.(0.&40.)Lx13,(0.&40.)(1<.(0.&40.)Lx14,(0.&40.)(1<.(0.&40.)Lx16,(0.&40.)(1<.(0.&40.)Lx17,(0.&40.)(1<.(0.&40.)Lx28,(0.&40.)(1<.(0.&40.)Lpkw',(0.&40.)(1<.P,(0.&40.)(3.(0.&8.))Lm',P,(0.&40.)(3.(0.&8.))(6.(13.$1;.R>.(1=.(1>.R4<.(1?.&40.R45.)R64.R63.R=.R<.R;.R4;.R4:.R:.R9.R8.R7.R6.R4?.R5.R4.R49.R48.R47.R46.R5?.R5>.R5=.R5<.R5;.R5:.R3.R58.R57.R56.)R44.(21.R4<.)R43.(22.(0.&40.))R1.(23.$;.)))(6.(16.(=.(5.$1.$1.)(17.$1.$1.R3:.R45.)(=.(5.$1.$1.)(17.$1.$1.R3?.(<.R3?.+8.))(=.(5.$1.$1.)(17.$1.$1.$26.(<.(<.$26.+10.)(20.+10.+1000.)))(=.(5.$1.$1.)(17.$1.$1.R35.(<.R35.(8.+2.+17.)))(10.(5.$1.$1.))))))R42.R1.)(6.(18.$;.R42.R1.)(6.(19.$;.R1.)(6.(:.$;.R1.$26.(=.$>.(?.(1?.&40.(<.R3;.R37.)))(=.$>.(?.R4>.)(10.$>.))))(6.(32.VhAR,R1.R39.)(6.(:.$;.R1.R3?.(=.$>.(?.R2.)(10.$>.)))(6.(11.$;.R1.R35.(<.R35.(8.+2.+17.)))(11.$;.R1.R3:.R45.))))))))))))))))))))))(1=.(1>.(1?.&40.+8701<.)(1?.&40.(<.R37.-40.))R56.R55.R54.R53.R52.(1?.&40.R31.)(1?.&40.$26.)(1?.&40.R26.)R43.R47.R42.R46.R41.R45.R44.(1?.&40.R29.)(1?.&40.R32.)(1?.&40.R2?.)(1?.&40.R2>.)R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.)R36.(1?.&40.+8701<.)R35.(22.(0.&40.))R33.(23.$;.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a2 a4 a6 a7 a1 a3 a5 alloc pkw ra0 q0 q1 q2 q3 q4 q5 SP F fc m0 m
      ARGS PACK TR size tag start lo bl ss count j B P
      SZ TG S0 S1 SJ JL FR SSX DB PX AR HS LS STB BCS P0 P1 PAL PCS A0 A1 AAL ACS T0 T1 TCS AP TP ST LOIMG SPL SPH SPA SCS MU WM MI.
    facts. unfold A_SS in *. change (1947848 + 16) with 1947864 in *.
    change (2^20) with 1048576 in *.
    assert (HJ : j = start / 1048576) by reflexivity. assert (HB : B = sblk bl j) by reflexivity.
    assert (HP : P = B + 8 * (start mod 1048576)) by reflexivity. assert (HC : count = size + 1) by reflexivity.
    clearbody P B j count.
    destruct DB as (DB1 & DBF & DBL).
    assert (JB : 0 <= j < 4096) by (rewrite HJ; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    pose proof (Forall_nth (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl) as FN.
    destruct (proj1 FN DBF (Z.to_nat j) 0 ltac:(lia)) as (B0 & B1 & BA). clear FN. fold (sblk bl j) in B0, B1, BA. rewrite <- HB in B0, B1, BA.
    pose proof (Z.mod_pos_bound start 1048576 ltac:(lia)) as SM.
    assert (PB : start mod 1048576 + count <= 1048576).
    { pose proof (Z.div_mod start 1048576 ltac:(lia)). pose proof (Z.div_mod (start + count - 1) 1048576 ltac:(lia)).
      pose proof (Z.mod_pos_bound (start + count - 1) 1048576 ltac:(lia)). rewrite HJ in SJ. clear - H H0 H1 SJ SM S0 S1 HC SZ. nia. }
    (* [comment removed for export] *)
    set (off := start mod 1048576) in *. clearbody off.
    assert (PRCS : crange CS P (8 + 8 * size)) by (eapply (crange_sub CS B (2^23)); [exact BCS| lia| lia]).
    destruct (DB1 j JB) as (stw & BC). unfold A_SS in BC. replace (1947848 + 16 + 16 * j) with (1947864 + 16 * j) in BC by lia.
    assert (OTH : forall j', 0 <= j' < 4096 -> ~ (j' = j) ->
              exists st, rw_cells asegs m (A_SS + 16 + 16 * j') [C8 (Z_to_bv 64 (sptr bl j')); C4 st; C4 (Z_to_bv 64 0)])
      by (intros j' H1 H2; apply DB1; exact H1).
    clear DB1.
    pose proof (munch_refl [(lo, SP); (PACK, PACK + 8); (1947864 + 16 * j, 1947864 + 16 * j + 16); (B, B + 2^23)] m) as MU2.
    pose proof (wmono_refl asegs m) as WM2.
    (* [comment removed for export] *)
    destruct (stk_split asegs m B P (B + 2^23) STB ltac:(subst P; lia)) as [STlo STx].
    destruct (stk_split asegs m P (P + (8 + 8 * size)) (B + 2^23) STx ltac:(subst P; lia)) as [STmid SThi].
    destruct (stk_carve asegs m P (P + (8 + 8 * size)) (Z.to_nat (8 + 8 * size)) STmid ltac:(lia)) as [_ [junk PR]].
    replace (P + (8 + 8 * size) - Z.of_nat (Z.to_nat (8 + 8 * size))) with P in PR by lia.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs m P [] (Z.to_nat (8 + 8 * size)) junk [] [8%nat; Z.to_nat (8 * size)]) in PR; [| cbn; lia].
    cbn [mk_CB_cells app] in PR.
    assert (LJ : length (firstn (Z.to_nat (8 * size)) (skipn 8 junk)) = Z.to_nat (8 * size)).
    { destruct PR as [[[WF1 [WF2 _]] _] _]. exact WF2. }
    apply (proj1 (rw_cells_app asegs m P [CB 8 (firstn 8 junk)] _)) in PR. destruct PR as [PH PBODY].
    cbn [cells_size csize Nat.add] in PBODY. replace (P + Z.of_nat 8) with (P + 8) in PBODY by lia.
    apply u8arr_of_rw_cells in PBODY.
    destruct SZ as [SZa SZb]. destruct TG as [TGa TGb]. destruct JB as [JBa JBb]. rewrite <- (Z_to_bv_bv_unsigned pkw) in PX.
    match type of BC with rw_cells _ _ _ [_; C4 ?stv; _] => rewrite <- (Z_to_bv_bv_unsigned stv) in BC end.
    clear STB STx STmid.
    lx_hide MU. lx_hide WM. lx_hide PBODY. lx_hide HS. lx_hide STlo. lx_hide SThi. lx_hide MU2. lx_hide WM2. lx_aceil.
    pose proof (munch_refl [(lo, SP + -64); (P, P + 8)] m) as MUa. pose proof (wmono_refl asegs m) as WMa.
    (* [comment removed for export] *)
    lx_run (PLAN [0x7a9dc] [] 20%N).

    lx_unhide1 PBODY. lx_unhide1 HS.
    lazymatch goal with MUl : munch _ m ?mc, WMl : wmono _ m ?mc |- evtA _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
      pose proof (u8arr_transport asegs _ m mc _ _ PBODY MUl WMl ltac:(rewrite LJ; cbn; lia)) as PBODY';
      pose proof (u8ro_transport asegs _ m mc _ _ HS MUl ltac:(cbn; lia)) as HS' end.
    (* [comment removed for export] *)
    lazymatch goal with MUl : munch _ m ?mc, WMl : wmono _ m ?mc |- evtA _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (MUb : munch [(lo, SP + -64); (P, P + (8 + 8 * size))] m mc) by (eapply munch_weaken; [| exact MUl]; lx_subfp);
      clear MUl; repeat match goal with K : stk _ mc P _ |- _ => clear K end end.
    clear PBODY HS. replace (Z_to_bv 64 (Z.of_nat (length ss))) with (Z_to_bv 64 (8 * size)) by (rewrite LS; reflexivity).
    callxA (eapply (imemcpy_spec AL IMG ALWF CS CSOK (8 * size) (P + 8) TR _ ss); try eassumption; try lia;
            [ eapply (crange_sub CS B (2^23)); [exact BCS| lia| lia]
            | eapply (crange_sub CS TR 240); [exact TCS| lia| lia] ]).

    (* [comment removed for export] *)
    zstep. zstep. zstep. rewrite (shr16_land_m16 start) by lia. change (2^20) with 1048576. rewrite <- HJ.
    (* [comment removed for export] *)
    match goal with H : rw_cells _ ?mx (SP + -64) (C8 (Z_to_bv 64 start) :: ?rest) |- _ =>
      apply (rw_cells_reshape asegs mx (SP + -64) _ (C4 (Z_to_bv 64 start) :: C4 (Z_to_bv 64 (start / 2^32)) :: rest)) in H;
      [| cbn; tauto
       | cbn [cells_bytes cbytes app]; rewrite (le8_split4 (Z_to_bv 64 start)), unsigned_lit by lia; rewrite <- !app_assoc; reflexivity ] end.

    (* [comment removed for export] *)
    lx_run (PLAN [] [] 40%N).

    lx_unhide.
    (* [comment removed for export] *)
    lazymatch goal with MUl : munch _ m lxm |- _ =>
      assert (MU2' : munch [(lo, SP); (PACK, PACK + 8); (1947864 + 16 * j, 1947864 + 16 * j + 16); (B, B + 2^23)] m lxm)
        by (eapply munch_weaken; [| exact MUl]; lx_subfp) end.
    lazymatch goal with WMl : wmono _ m lxm |- _ => rename WMl into WM2' end.
    (* [comment removed for export] *)
    assert (STB' : stk asegs lxm B (B + 2^23)).
    { match goal with H : rw_cells _ lxm P [C8 ?w] |- _ => pose proof (stk_of_rw_cells asegs lxm P [C8 w] H) as ST1; cbn [cells_size csize Nat.add] in ST1 end.
      match goal with H : u8arr _ lxm (P + 8) ss |- _ => pose proof (stk_of_rw_cells asegs lxm (P + 8) _ (rw_cells_of_u8arr asegs lxm (P + 8) ss H)) as ST2;
        cbn [cells_size csize Nat.add] in ST2; rewrite Nat.add_0_r in ST2 end.
      lazymatch goal with MUl : munch _ m lxm, MU2x : munch _ m lxm |- _ =>
        first [ assert (STlo' : stk asegs lxm B P) by (eapply stk_transport_disjoint; [exact STlo| exact MUl| exact WM2'| cbn; lia])
              | assert (STlo' : stk asegs lxm B P) by (eapply stk_transport_disjoint; [exact STlo| exact MU2x| exact WM2'| cbn; lia]) ];
        first [ assert (SThi' : stk asegs lxm (P + (8 + 8 * size)) (B + 2^23)) by (eapply stk_transport_disjoint; [exact SThi| exact MUl| exact WM2'| cbn; lia])
              | assert (SThi' : stk asegs lxm (P + (8 + 8 * size)) (B + 2^23)) by (eapply stk_transport_disjoint; [exact SThi| exact MU2x| exact WM2'| cbn; lia]) ] end.
      eapply stk_merge; [exact STlo'| |lia].
      eapply stk_merge; [exact ST1| |lia].
      eapply stk_merge; [| exact SThi'| lia]. replace (P + Z.of_nat 8) with (P + 8) by lia.
      replace (P + (8 + 8 * size)) with (P + 8 + Z.of_nat (length ss)) by lia. exact ST2. }
    apply evtA_done. lx_exs. lx_ands;
      [> lx_mseq
      | lx_munch MU MU2'
      | lx_wmono WM WM2'
      | lx_close | lx_close
      | lazymatch goal with |- dblocks ?mf bl =>
          eapply (dblocks_reest (fun j' => j' = j) _ m mf); [exact OTH| | intros j0; clear; lia| exact DBF| exact DBL| exact MU2'| exact WM2'|];
          [ intros j0 Hj ->; eexists; unfold A_SS;
            match goal with K : rw_cells _ mf (16 * j + 1947864) _ |- _ => lx_rwx K end
          | intros j0 Hj NE; unfold A_SS; cbn; clear - Hj NE JBa JBb P0 LOIMG SPL B0 B1; lia ] end
      | lx_close | exact STB' | lx_close ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End DepotD.

End ARUN_1.
