(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_MmapFixed AW_MmapAnon.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00e2134c5ed7ec8d 0 3 1 1 33 1 34 1P01198e97cdc48fe9 0 3 1 1 33 1 34 1P015ec397311edb76 0 2 0 1 32 1P019fb509ac410638 0 3 1 1 33 1 34 1P01b3108f0f06c469 0 2 0 1 28 1P01c8c3610d53a91f 0 2 0 1 28 1P01d70e9d5bde41c1 0 2 0 1 24 1P01fb5c8e94cc58d1 0 2 0 1 28 1P02373fd8f909491b 0 3 1 1 35 1 36 1P023e8ce03a42432c 0 3 1 1 33 1 34 1P02902e57770b597a 0 2 0 1 32 1P0298877fc41ff0a5 0 2 0 1 25 1P02e3dee152b1cafd 0 2 0 1 32 1P030414c25e291ac3 0 3 1 1 35 1 36 1P036e9667aff7a3d8 0 2 0 1 34 1P0377362020c5e647 0 3 1 1 33 1 34 1P039cff2bf82f3995 0 2 0 1 32 1P040cc489d9f0b53d 0 2 0 1 28 1P049ae9152c4b6d43 0 4 0 1 21 1 29 1 34 1P04d0bf0af3ef39a3 0 2 0 1 32 1P05a9a39db084b8f4 0 2 0 1 32 1P05f0af778d73a3ea 0 2 0 1 32 1P061bbd39a50e4b74 0 2 0 1 34 1P0628455d5f9c3241 0 3 1 1 33 1 34 1P0633d2364c6f28e4 0 3 1 1 33 1 34 1P068b8aa35f8296b0 0 2 0 1 28 1P06b70ee0e0e11589 0 3 1 1 35 1 36 1P072d2ca28525ab64 0 2 0 1 34 1P0785aa6cd6100d28 0 2 0 1 28 1P07df407db3670076 0 3 1 1 33 1 34 1P08029b10bddc8d8d 0 3 1 1 29 1 30 1P08ab6bf7bda00856 0 2 0 1 28 1P08c902d57e6f7100 0 2 0 1 35 1P08dce4701b32ffff 0 2 0 1 28 1P09563349849c908a 0 3 1 1 35 1 36 1P0984bfd775544538 0 3 1 1 35 1 36 1P0a1c9376aba25ffc 0 2 0 1 2 1P0a39534693da3971 0 2 0 1 32 1P0a6d3a32ee97dd16 0 2 0 1 32 1P0b1c70bb4c8727d5 0 2 0 1 28 1P0b4c60aa890d687b 0 2 0 1 32 1P0b5db7bcb7da1ea4 0 2 0 1 34 1P0bb659fc51b180f1 0 2 0 1 25 1P0c25337bb3acaea2 0 2 0 1 39 1P0c2cac5066cc50b9 0 2 0 1 32 1P0c5a297bd66458cc 0 2 0 1 28 1P0ca21d8af38f1f0f 0 2 0 1 32 1P0cefcaaa1f8a2c57 0 3 1 1 33 1 34 1P0d0912e907733518 0 2 0 1 2 1P0d1ab37c9ce9e2b0 0 3 1 1 29 1 30 1P0d69ca10984dc049 0 2 0 1 32 1P0da0a02cca66f595 0 3 1 1 33 1 34 1P0dfbd2d94906b0da 0 3 1 1 35 1 36 1P0e3a81fcd83e8c1f 0 3 1 1 35 1 36 1P0e566c0c0ba227f0 0 2 0 1 34 1P0e65edc4d5f92134 0 2 0 1 34 1P0e7621ceed0f2315 0 2 0 1 34 1P0eeadb6ea76f52d4 0 3 1 1 35 1 36 1P0f14eb3237043492 0 3 1 1 29 1 30 1P0f3bc9d7d2b9aa07 0 2 0 1 34 1P0faa3d3bbaa98d4e 0 3 1 1 35 1 36 1P0fae1cd36cfe9d76 0 3 1 1 29 1 30 1P10298cafcf731450 0 2 0 1 32 1P1068c7a4604a737b 0 3 1 1 35 1 36 1P1098fc19a3274914 0 3 1 1 35 1 36 1P10a4ebeedbdfae66 0 3 1 1 35 1 36 1P118553c8192a933c 0 3 1 1 35 1 36 1P121a0adaea5229ef 0 3 1 1 33 1 34 1P123b2d0750c00f3c 0 3 1 1 33 1 34 1P1281c5e278f35b83 0 3 1 1 35 1 36 1P12bb4f2a780372e7 0 2 0 1 25 1P138a0f5ea8db067e 0 3 1 1 35 1 36 1P13bc89d9470b3f87 0 2 0 1 32 1P14924d978d578a29 0 2 0 1 32 1P14d9379e1309a344 0 2 0 1 32 1P1507162541dc4390 0 2 0 1 24 1P1593c6ae486d6bb3 0 3 1 1 29 1 30 1P15d5217429651902 0 2 0 1 28 1P15f43a694a458208 0 3 1 1 35 1 36 1P166e256a75ca9832 0 3 1 1 35 1 36 1P168588bcb0ba8b87 0 3 1 1 33 1 34 1P16a1c9bb01db6995 0 2 0 1 28 1P16a1fb24c7e0ff5c 0 2 0 1 34 1P179fdb1e11abf058 0 2 0 1 34 1P17b264695b99a4e6 0 3 1 1 33 1 34 1P186d147f51cab125 0 2 0 1 32 1P18767d17f0515cab 0 2 0 1 34 1P18dc7b05a0e34ea1 0 2 0 1 28 1P191e5156ab9cd878 0 2 0 1 32 1P194aa30f87e023ea 0 3 1 1 35 1 36 1P1a81634a01d81ac7 0 2 0 1 28 1P1ab991357c00c1fa 0 2 0 1 28 1P1ae7305d1bf06b18 0 2 0 1 34 1P1b2de3c120090b34 0 3 1 1 33 1 34 1P1b5e7f4a0747e804 0 2 0 1 32 1P1ba77113a38ea6bb 0 2 0 1 34 1P1bcfa5624d516876 0 3 1 1 29 1 30 1P1beea0e0c8a2e308 0 2 0 1 34 1P1c73a968c75daef9 0 3 1 1 29 1 30 1P1ca7f9fd437e09c2 0 2 0 1 28 1P1d0c11c6620c4ed3 0 2 0 1 32 1P1d35af38124fb14b 0 2 0 1 32 1P1d5e5fc2968dbddb 0 2 0 1 34 1P1d71672cd23cb09b 0 3 1 1 33 1 34 1P1d7ef916cdf971eb 0 3 1 1 35 1 36 1P1daeede54bf2707d 0 3 1 1 33 1 34 1P1df89e08ef36318b 0 2 0 1 32 1P1e13796ba7ddb8d8 0 3 1 1 33 1 34 1P1e3ccfb2b38b9e5f 0 3 1 1 33 1 34 1P1e69224be00dacef 0 2 0 1 32 1P1e7045e62a4591ed 0 2 0 1 32 1P1ecd51b8bcf8402e 0 2 0 1 34 1P1f3df86683c31866 0 3 1 1 35 1 36 1P1f8ceaa75fd4c803 0 2 0 1 34 1P1fd34811af24c741 0 3 1 1 29 1 30 1P1fe03323a57c3d9b 0 2 0 1 28 1P1fe767f6215c5906 0 2 0 1 28 1P1ffe47f84e875a08 0 2 0 1 28 1P201b057f2b9382d0 0 2 0 1 28 1P20a0fa000c8583d2 0 3 1 1 33 1 34 1P2166ace968e4c126 0 2 0 1 32 1P21f541d334fb986c 0 3 1 1 35 1 36 1P2259f1e8fd2a4ef8 0 3 1 1 35 1 36 1P22c483bec2a6e92b 0 3 1 1 29 1 30 1P22f41e8e827dc44e 0 3 1 1 29 1 30 1P22fa650f71803fc5 0 3 1 1 33 1 34 1P232ec0869d08309f 0 2 0 1 32 1P233a6141fa1318e6 0 3 1 1 29 1 30 1P2347827efde3cc46 0 2 0 1 34 1P23885ba8bede30df 0 3 1 1 33 1 34 1P23b32c9ba071f519 0 2 0 1 34 1P23cdb9ab4c284083 0 2 0 1 32 1P23d1c7038c0e6ab4 0 2 0 1 32 1P23ffdac8626b5046 0 2 0 1 32 1P2406e083c59719fc 0 2 0 1 34 1P241514cad2f51ef8 0 2 0 1 28 1P244360e61bd24c6c 0 3 1 1 33 1 34 1P24c497174f7b497d 0 3 1 1 29 1 30 1P24db195b3c8e773c 0 2 0 1 32 1P25178b76c22b19ef 0 3 1 1 33 1 34 1P25783b5e9eb14d0f 0 2 0 1 34 1P25ebcd8dc254c6c3 0 2 0 1 34 1P26129ea3eaf6093e 0 3 1 1 33 1 34 1P263dc9804dbbd3c2 0 2 0 1 28 1P26a9e071b5ff1ece 0 2 0 1 28 1P2707bb7fa01442e3 0 3 1 1 29 1 30 1P272cb1c03339f182 0 2 0 1 34 1P27ae33bc11f380ee 0 3 1 1 35 1 36 1P27b2929eb28f46fa 0 2 0 1 28 1P27efa936b8f52d28 0 3 1 1 29 1 30 1P282c04502066b664 0 2 0 1 32 1P28991e6eb76a32f5 0 3 1 1 33 1 34 1P29827766be26d736 0 2 0 1 27 1P2987a319d20fd6c1 0 3 1 1 33 1 34 1P29ef00ce43b9e035 0 3 1 1 29 1 30 1P29fdfa5bbe1a5af5 0 3 1 1 29 1 30 1P2a4804cc0cf68d14 0 3 1 1 35 1 36 1P2a4d3d00f99a214a 0 3 1 1 33 1 34 1P2a6ae20e12c6df81 0 3 1 1 33 1 34 1P2ab0d6ceca9fbfd1 0 3 1 1 35 1 36 1P2b507facdecc2646 0 3 1 1 29 1 30 1P2b5e43aa03296ee1 0 2 0 1 32 1P2bf6142f12fa764a 0 2 0 1 34 1P2c05bbf2ab439a6d 0 2 0 1 34 1P2c58d14880fb38fa 0 2 0 1 32 1P2d10260083e9c921 0 2 0 1 25 1P2d4e7a64e1cd828d 0 2 0 1 32 1P2d5fb7fbe600f6ab 0 2 0 1 34 1P2ddc1e62fc3c1cf1 0 2 0 1 32 1P2e35c175fcc8cbac 0 2 0 1 34 1P2e8620f56b8c8db9 0 2 0 1 32 1P2e9c7f982181051e 0 3 1 1 29 1 30 1P2ea97dedefc6ab17 0 2 0 1 34 1P2ee1682811940d2c 0 2 0 1 32 1P2eea83d9debcfa66 0 2 0 1 32 1P2ef106825010cd77 0 3 1 1 35 1 36 1P2f4096c365bbd407 0 3 1 1 35 1 36 1P2f73f8d560828dca 0 2 0 1 34 1P2f7cb3157c5c3288 0 2 0 1 28 1P2f92b394231872df 0 2 0 1 32 1P3016fd6f09185a35 0 3 1 1 33 1 34 1P302b206d7e41fe53 0 3 1 1 33 1 34 1P3059f6ffe66d0234 0 2 0 1 32 1P3090de5e29832fbe 0 2 0 1 32 1P30e4016abc89e17a 0 2 0 1 28 1P310506b51f8cd59f 0 2 0 1 32 1P3152c579475bb71d 0 3 1 1 29 1 30 1P3196a95b752cd2ee 0 3 1 1 33 1 34 1P31af50cac15d141e 0 2 0 1 32 1P31db81e8ec61534f 0 3 1 1 29 1 30 1P3207e4f02f0187d1 0 3 1 1 35 1 36 1P3240eb7770005aff 0 2 0 1 28 1P32508e541fc1c02b 0 2 0 1 32 1P327b67878d323cbf 0 3 1 1 29 1 30 1P329416d05c8502f8 0 2 0 1 32 1P32b54d9630fc64df 0 3 1 1 35 1 36 1P32c7c62090fdbcce 0 2 0 1 34 1P32c7f377fde1e823 0 2 0 1 28 1P332e5916e8d58408 0 2 0 1 32 1P33646a5e34d5dc12 0 3 1 1 35 1 36 1P3387f8454bdcd737 0 3 1 1 35 1 36 1P34052d3577dd986a 0 2 0 1 28 1P342a61b8bc705415 0 3 1 1 33 1 34 1P344a7485bb0c1a62 0 3 1 1 35 1 36 1P3451f0f3a244953d 0 3 1 1 35 1 36 1P3461fd4fff7e341f 0 3 1 1 33 1 34 1P347b96f8b549945d 0 3 0 1 28 1 29 1P3485922cfdaa4799 0 3 1 1 35 1 36 1P34ad7bb10ea77124 0 2 0 1 35 1P351dad402f9ef24c 0 3 1 1 35 1 36 1P351ea2c864210798 0 3 1 1 33 1 34 1P355f4186ca125739 0 3 1 1 33 1 34 1P3564b4271516e24e 0 2 0 1 28 1P35a30c5256df58fb 0 2 0 1 39 1P35f0a0c99cb7c616 0 2 0 1 32 1P36028b218ba9dd9e 0 2 0 1 34 1P365d3c8dab65f715 0 4 0 1 21 1 29 1 34 1P36e72de21ab71147 0 3 1 1 35 1 36 1P36e86761176a37ed 0 3 1 1 29 1 30 1P37107b8ecaed85d2 0 3 1 1 33 1 34 1P37461adbfc621ff7 0 3 1 1 33 1 34 1P375410a36dc91344 0 2 0 1 32 1P379399f45dfdc6f4 0 3 1 1 33 1 34 1P37b1f764d4b35659 0 2 0 1 32 1P37cf74d4714d0172 0 3 1 1 33 1 34 1P37d20c3b48cf91ca 0 3 1 1 35 1 36 1P37d2a7095ffa3bc4 0 2 0 1 34 1P38593debdec3d0ad 0 2 0 1 28 1P38972e269e38f2e4 0 3 1 1 35 1 36 1P38df0662786be3df 0 2 0 1 32 1P390b895794c9770b 0 3 1 1 33 1 34 1P392b3483f2168125 0 2 0 1 28 1P394b1ea7e5f39157 0 2 0 1 34 1P396a6e5a74ba9491 0 2 0 1 28 1P39783b8881317ec4 0 3 1 1 35 1 36 1P397f8538ee7fedbf 0 2 0 1 2 1P3a3c3e618501ae92 0 2 0 1 28 1P3a5cd1cc5f455c0c 0 2 0 1 34 1P3a773e914bc1c78e 0 3 1 1 35 1 36 1P3aca739fd3e0bac8 0 3 1 1 35 1 36 1P3b50a9e2b0d77ca5 0 3 1 1 33 1 34 1P3b7addf7db57f81f 0 2 0 1 34 1P3c0b551ca2607cd4 0 2 0 1 34 1P3cb80a4d01dc9f7b 0 3 1 1 35 1 36 1P3cbc0ab07a69040b 0 2 0 1 27 1P3ccc69d41ca99bc4 0 3 1 1 33 1 34 1P3d0e29e56a4d3fe8 0 2 0 1 34 1P3d4acd89328baac6 0 2 0 1 34 1P3e896473c47075c4 0 3 1 1 29 1 30 1P3ed2e92ff4b45027 0 3 1 1 29 1 30 1P3f1b5119816c69a4 0 2 0 1 34 1P3f1c5fa9c6885881 0 3 1 1 35 1 36 1P3f614f7c5ae4f08d 0 3 1 1 33 1 34 1P3f6f3e83d897458c 0 3 1 1 33 1 34 1N00e76616611ca990N01a6215b3a79787aN056d3cea6a544593N05e1633590ce4059N1dea7b6c732e6debN25c5b11dbb1a08ebN2b0650f94a6d8186N30aa9cfedd7968e3N321415c96d3f4ebeN363ecbbb78d1e0c8"%lxh.
Ltac2 gd_tbl_AW_MmapDie () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MSsvc"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_PAGESZ_CELL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_MMAP_ECALL"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_GOT_PAGESZ"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_DECORATE"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.MmapDie.md_pre_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "ARUN_1.A_MMAP_OR_DIE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_SEALED2"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_DYING"; "ARUN_1.MmapDie.die_post"; "ARUN_1.A_SPIN_MMAPDIE"; "ARUN_1.MmapDie.md_answered"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_MMAP_LIMIT"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapAnon.ma_ret_post"; "ARUN_1.MmapDie.mnr_pre_post"; "ARUN_1.A_MMAP_NORESERVE_OR_DIE"; "ARUN_1.MmapDie.mnr_answered"].

Section ARUN_1. Context {hAR : arun}.
Definition A_MMAP_OR_DIE : Z := 0x7c928.
Definition A_MMAP_NORESERVE_OR_DIE : Z := 0x7ce60.
(* [comment removed for export] *)
Definition A_SPIN_MMAPDIE : Z := 0x76ad4.

Section MmapDie.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition die_post (fc : bv 32) (SPIN : Z) : machine_state -> Prop :=
    fun ms' => exists r F' mm, ms' = MS r F' (Z_to_bv 64 SPIN) fc None mm (seg_rom asegs).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition md_pre_post (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (size name raw lo : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MmapDie ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lmm,P,(2.&40.)(3.(2.&8.))(1.(4.(2.&8.))Lfr,(4.(2.&8.))(5.(6.$0.R;.(7.(8.(9.&40.+7<9;8.)(9.&40.(:.O16.-30.))O15.O14.R:.R9.R8.(9.&40.O3.)(9.&40.O4.)(9.&40.=)(9.&40.(;.(<.(:.O5.+???.)+1000.)+1000.))(9.&40.+3.)(9.&40.+22.)(9.&40.-1.)(9.&40.=)R3.(9.&40.+=>.)(9.&40.(;.(<.(:.O5.+???.)+1000.)+1000.))(9.&40.$=.)O?.O>.O=.O<.O;.O:.O9.O8.R7.R6.R5.R4.)O7.(9.&40.$>.)(9.&40.+=>.)O6.(?.(2.&40.))R2.(10.$11.)))(5.(12.(13.(14.$15.$15.)(16.$15.$15.O2.O16.)(17.(14.$15.$15.)))O1.R2.)(5.(18.$11.O1.R2.)(5.(19.$11.R2.)(5.(1:.$11.R2.(:.O16.-30.)(13.$1;.(1<.#4.R1.)(13.$1;.(1=.(9.&40.+22.))(13.$1;.(1>.O10.)(13.$1;.(1>.O11.)(13.$1;.(1>.O12.)(13.$1;.(1>.O13.)(13.$1;.(1>.O17.)(17.$1;.)))))))))(1?.$11.R2.O2.(:.O16.-30.)))))))))))))))))")
(* [comment removed for export] *).

  #[using="IMG ALWF CSOK"] Lemma mmapdie_pre : ltac2:(CDefT.buildp (gd_tbl_AW_MmapDie ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)PSP,$15.PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Psize,$15.Pname,$15.Praw,$15.Plo,$15.P,(5.(21.=R4.)(22.R4.(23.+2.+28.)))P,(5.(21.=R4.)(21.R4.(23.+2.+2?.)))P,(5.(22.=R4.)(21.R4.+2.))P,(24.$11.R8.$25.(13.$1;.(1>.(9.&40.$=.))(17.$1;.)))P,(24.$11.R9.$=.(13.$1;.(1>.(9.&40.+1000.))(17.$1;.)))P,(24.$11.R:.$26.(13.$1;.(1>.(9.&40.$27.))(17.$1;.)))P,(24.$11.R;.$28.(13.$1;.(29.(9.&8.=))(17.$1;.)))P,(1?.$11.R<.R8.R?.)P,(22.+65?000.R9.)P,(22.R:.(2:.R11.+140.))P,(22.R12.(23.+2.+3?.))P,(2;.VCS,R<.(2:.R13.R<.))P,(19.$11.R11.)(2<.$11.VAL,VCS,(2=.R30.R15.R2?.R2>.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R14.R13.R11.R10.R?.R>.R12.)(2>.(8.R30.(9.&40.R15.)R2?.R2>.R2=.R2<.R2;.R2:.R29.(9.&40.R11.)(9.&40.R10.)(9.&40.R?.)R1:.R19.R18.R17.R16.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R14.(9.&40.$2?.)R13.(?.(2.&40.))R12.(10.$11.)))")
(* [comment removed for export] *).
  Proof.
    pose proof (I : lx_noaceil) as LXNOACEIL.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a3 a4 a5 a6 a7 SP F fc m size name raw lo
      SZ NM RAW GOT PGS GOTF DEC ST LOIMG SPL SPH SCS MI.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold A_MMAP_OR_DIE, A_GOT_PAGESZ, A_PAGESZ_CELL, A_GOT_CFLAGS, A_CFLAGS, A_DECORATE in *.
    lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x7b25c] [] 100%N).
    lx_stk_grow_to lo (SP + -48).
    try rewrite (lxw_land_m4096 (size + 4095)) in * by (clear -SZ; lia).
    stepA_ecall.
    lazymatch goal with STj : stk _ ?mx (SP + -48) ?t, FRc : rw_cells _ ?mx ?t _ |- _ =>
      lx_junk STj 4%nat fr FRj; chunk_join FRj FRc FRa end.
    unfold md_pre_post, A_MMAP_ECALL. lx_exs; lx_ands; [ lx_mseq | assumption | assumption | assumption | exact FRa | assumption ].
  Qed.

  Definition md_answered (r : word) (SP : Z) (gp tp t0 t1 t2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 : word)
      (F : bvmap 5 word) (fc : bv 32) (size name raw : Z) (mm : mem) : machine_state := ltac2:(CDefT.buildp (gd_tbl_AW_MmapDie ()) "(2>.(8.(9.&40.+7<9;8.)(9.&40.(:.O19.-30.))O18.O17.O16.O15.O14.(9.&40.O2.)(9.&40.O3.)O1:.(9.&40.(;.(<.(:.O4.+???.)+1000.)+1000.))(9.&40.+3.)(9.&40.+22.)(9.&40.-1.)(9.&40.=)O7.(9.&40.+=>.)(9.&40.(;.(<.(:.O4.+???.)+1000.)+1000.))(9.&40.$=.)O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.)O6.(9.&40.+7;260.)O5.(?.(2.&40.))O1.(10.$11.))")
(* [comment removed for export] *).

  #[using="IMG ALWF CSOK"] Lemma mmapdie_post_die : ltac2:(CDefT.buildp (gd_tbl_AW_MmapDie ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa6,(2.&40.)PSP,$15.PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Psize,$15.Pname,$15.Praw,$15.Plo,$15.Pfr,(4.(2.&8.))P,(5.(21.=R5.)(22.R5.(23.+2.+28.)))P,(1:.$11.R7.(:.R;.-30.)(13.$1;.(1<.#4.R2.)(13.$1;.(1=.(9.&40.+22.))(13.$1;.(1>.R19.)(13.$1;.(1>.R1:.)(13.$1;.(1>.R1;.)(13.$1;.(1>.R1<.)(13.$1;.(1>.R22.)(17.$1;.)))))))))P,(24.$11.R8.$30.(13.$1;.(1>.(9.&40.+1.))(17.$1;.)))P,(24.$11.R9.$31.(13.$1;.(1=.(9.&40.=))(17.$1;.)))P,(1?.$11.R:.R6.(:.R>.-30.))P,(22.+65?000.R7.)P,(22.R8.(2:.R10.+140.))P,(22.R11.(23.+2.+3?.))P,(12.(13.(14.$15.$15.)(16.$15.$15.R:.R12.)(17.(14.$15.$15.)))R?.R>.)P,(18.$11.R10.R?.)P,(19.$11.R10.)P,(2;.VCS,R=.(2:.R15.R=.))(2<.$11.VAL,VCS,(32.R14.$33.)(34.(9.&40.(2:.(23.+2.+40.)+<.))R16.R2<.R2;.R2:.R29.R28.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R15.R14.R11.R10.R?.R12.))")
(* [comment removed for export] *).
  Proof.
    pose proof (I : lx_noaceil) as LXNOACEIL.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 SP F fc m0 mm size name raw lo fr
      SZ FR SEAL DY ST LOIMG SPL SPH MU WM MI SCS.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    unfold md_answered, A_PAGESZ_CELL, A_GOT_SEALED2, A_DYING, A_SPIN_MMAPDIE in *. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x76ad4] [] 80%N).
    apply evtA_done. unfold die_post. do 3 eexists. reflexivity.
  Qed.

  #[using="IMG ALWF CSOK"] Lemma mmapdie_post_ok : ltac2:(CDefT.buildp (gd_tbl_AW_MmapDie ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa6,(2.&40.)PSP,$15.PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Psize,$15.Pname,$15.Praw,$15.Plo,$15.Pfr,(4.(2.&8.))Pa,(2.&40.)P,(5.(21.=R6.)(22.R6.(23.+2.+28.)))P,(21.=(35.&40.R2.))P,(22.(:.(35.&40.R3.)R8.)(36.VhAR,))P,(1:.$11.R:.(:.R>.-30.)(13.$1;.(1<.#4.R5.)(13.$1;.(1=.(9.&40.+22.))(13.$1;.(1>.R1<.)(13.$1;.(1>.R1=.)(13.$1;.(1>.R1>.)(13.$1;.(1>.R1?.)(13.$1;.(1>.R25.)(17.$1;.)))))))))P,(24.$11.R;.$26.(13.$1;.(1>.(9.&40.$27.))(17.$1;.)))P,(24.$11.R<.$37.(13.$1;.(1>.(9.&40.=))(17.$1;.)))P,(1?.$11.R=.R9.(:.R11.-30.))P,(22.+65?000.R:.)P,(22.R;.(2:.R13.+140.))P,(22.R14.(23.+2.+3?.))P,(12.(13.(14.$15.$15.)(16.$15.$15.R=.R15.)(17.(14.$15.$15.)))R12.R11.)P,(18.$11.R13.R12.)P,(19.$11.R13.)P,(2;.VCS,R10.(2:.R18.R10.))(2<.$11.VAL,VCS,(38.R30.R19.R2?.R2>.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R18.R17.R?.R11.R16.)(34.R?.R19.R2?.R2>.R2=.R2<.R2;.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R18.R17.R14.R13.R12.R15.))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 SP F fc m0 mm size name raw lo fr a
      SZ A0 ACE FR GOTF LIM ST LOIMG SPL SPH MU WM MI SCS.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    pose proof (bv_unsigned_in_range 64 a) as AR.
    rewrite <- (Z_to_bv_bv_unsigned a).
    unfold md_answered, A_PAGESZ_CELL, A_GOT_CFLAGS, A_CFLAGS, A_MMAP_LIMIT in *. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 80%N). lx_postw.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition mnr_pre_post (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (F : bvmap 5 word) (fc : bv 32) (size name lo : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_MmapDie ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lmm,P,(2.&40.)(3.(2.&8.))(1.(4.(2.&8.))Lfr,(4.(2.&8.))(5.(6.$0.R;.(7.(8.(9.&40.+7<>><.)(9.&40.(:.O15.-30.))O14.O13.R:.R9.R8.(9.&40.O3.)(9.&40.(;.(<.(:.O4.+???.)+1000.)+1000.))(9.&40.=)(9.&40.(;.(<.(:.O4.+???.)+1000.)+1000.))(9.&40.+3.)(9.&40.+4022.)(9.&40.-1.)(9.&40.=)R3.(9.&40.+=>.)(9.&40.$=.)O?.O>.O=.O<.O;.O:.O9.O8.O7.R7.R6.R5.R4.)O6.(9.&40.$>.)(9.&40.+=>.)O5.(?.(2.&40.))R2.(10.$11.)))(5.(12.(13.(14.$15.$15.)(16.$15.$15.O2.O15.)(17.(14.$15.$15.)))O1.R2.)(5.(18.$11.O1.R2.)(5.(19.$11.R2.)(5.(1:.$11.R2.(:.O15.-30.)(13.$1;.(1<.#<.R1.)(13.$1;.(1=.(9.&40.+4022.))(13.$1;.(1>.O10.)(13.$1;.(1>.O11.)(13.$1;.(1>.O12.)(13.$1;.(1>.O16.)(17.$1;.))))))))(1?.$11.R2.O2.(:.O15.-30.)))))))))))))))))")
(* [comment removed for export] *).

  #[using="IMG ALWF CSOK"] Lemma mmapnrdie_pre : ltac2:(CDefT.buildp (gd_tbl_AW_MmapDie ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)PSP,$15.PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Psize,$15.Pname,$15.Plo,$15.P,(5.(21.=R3.)(22.R3.(23.+2.+28.)))P,(5.(21.=R3.)(21.R3.(23.+2.+2?.)))P,(24.$11.R6.$25.(13.$1;.(1>.(9.&40.$=.))(17.$1;.)))P,(24.$11.R7.$=.(13.$1;.(1>.(9.&40.+1000.))(17.$1;.)))P,(24.$11.R8.$26.(13.$1;.(1>.(9.&40.$27.))(17.$1;.)))P,(24.$11.R9.$28.(13.$1;.(29.(9.&8.=))(17.$1;.)))P,(1?.$11.R:.R7.R=.)P,(22.+65?000.R8.)P,(22.R9.(2:.R?.+140.))P,(22.R10.(23.+2.+3?.))P,(2;.VCS,R;.(2:.R11.R;.))P,(19.$11.R?.)(2<.$11.VAL,VCS,(39.R2?.R13.R2>.R2=.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R12.R11.R?.R>.R=.R10.)(2>.(8.R2?.(9.&40.R13.)R2>.R2=.R2<.R2;.R2:.R29.R28.(9.&40.R?.)(9.&40.R>.)R19.R18.R17.R16.R15.R14.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R12.(9.&40.$3:.)R11.(?.(2.&40.))R10.(10.$11.)))")
(* [comment removed for export] *).
  Proof.
    pose proof (I : lx_noaceil) as LXNOACEIL.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a2 a3 a4 a5 a6 a7 SP F fc m size name lo
      SZ NM GOT PGS GOTF DEC ST LOIMG SPL SPH SCS MI.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold A_MMAP_NORESERVE_OR_DIE, A_GOT_PAGESZ, A_PAGESZ_CELL, A_GOT_CFLAGS, A_CFLAGS, A_DECORATE in *.
    lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x7b25c] [] 100%N).
    lx_stk_grow_to lo (SP + -48).
    try rewrite (lxw_land_m4096 (size + 4095)) in * by (clear -SZ; lia).
    stepA_ecall.
    lazymatch goal with STj : stk _ ?mx (SP + -48) ?t, FRc : rw_cells _ ?mx ?t _ |- _ =>
      lx_junk STj 12%nat fr FRj; chunk_join FRj FRc FRa end.
    unfold mnr_pre_post, A_MMAP_ECALL. lx_exs; lx_ands; [ lx_mseq | assumption | assumption | assumption | exact FRa | assumption ].
  Qed.

  Definition mnr_answered (r : word) (SP : Z) (gp tp t0 t1 t2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 : word)
      (F : bvmap 5 word) (fc : bv 32) (size name : Z) (mm : mem) : machine_state := ltac2:(CDefT.buildp (gd_tbl_AW_MmapDie ()) "(2>.(8.(9.&40.+7<>><.)(9.&40.(:.O19.-30.))O18.O17.O16.O15.O14.(9.&40.O2.)(9.&40.(;.(<.(:.O3.+???.)+1000.)+1000.))O1:.(9.&40.(;.(<.(:.O3.+???.)+1000.)+1000.))(9.&40.+3.)(9.&40.+4022.)(9.&40.-1.)(9.&40.=)O6.(9.&40.+=>.)(9.&40.$=.)O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.)O5.(9.&40.+7;260.)O4.(?.(2.&40.))O1.(10.$11.))")
(* [comment removed for export] *).

  #[using="IMG ALWF CSOK"] Lemma mmapnrdie_post_die : ltac2:(CDefT.buildp (gd_tbl_AW_MmapDie ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa6,(2.&40.)PSP,$15.PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Psize,$15.Pname,$15.Plo,$15.Pfr,(4.(2.&8.))P,(5.(21.=R4.)(22.R4.(23.+2.+28.)))P,(1:.$11.R6.(:.R:.-30.)(13.$1;.(1<.#<.R2.)(13.$1;.(1=.(9.&40.+4022.))(13.$1;.(1>.R19.)(13.$1;.(1>.R1:.)(13.$1;.(1>.R1;.)(13.$1;.(1>.R21.)(17.$1;.))))))))P,(24.$11.R7.$30.(13.$1;.(1>.(9.&40.+1.))(17.$1;.)))P,(24.$11.R8.$31.(13.$1;.(1=.(9.&40.=))(17.$1;.)))P,(1?.$11.R9.R6.(:.R=.-30.))P,(22.+65?000.R7.)P,(22.R8.(2:.R?.+140.))P,(22.R10.(23.+2.+3?.))P,(12.(13.(14.$15.$15.)(16.$15.$15.R:.R11.)(17.(14.$15.$15.)))R>.R=.)P,(18.$11.R?.R>.)P,(19.$11.R?.)P,(2;.VCS,R=.(2:.R14.R=.))(2<.$11.VAL,VCS,(32.R13.$33.)(3;.(9.&40.(2:.(23.+2.+40.)+<.))R15.R2;.R2:.R29.R28.R27.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R14.R13.R10.R?.R11.))")
(* [comment removed for export] *).
  Proof.
    pose proof (I : lx_noaceil) as LXNOACEIL.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 SP F fc m0 mm size name lo fr
      SZ FR SEAL DY ST LOIMG SPL SPH MU WM MI SCS.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    unfold mnr_answered, A_PAGESZ_CELL, A_GOT_SEALED2, A_DYING, A_SPIN_MMAPDIE in *. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x76ad4] [] 80%N).
    apply evtA_done. unfold die_post. do 3 eexists. reflexivity.
  Qed.

  #[using="IMG ALWF CSOK"] Lemma mmapnrdie_post_ok : ltac2:(CDefT.buildp (gd_tbl_AW_MmapDie ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa6,(2.&40.)PSP,$15.PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Psize,$15.Pname,$15.Plo,$15.Pfr,(4.(2.&8.))Pa,(2.&40.)P,(5.(21.=R5.)(22.R5.(23.+2.+28.)))P,(21.=(35.&40.R2.))P,(22.(:.(35.&40.R3.)R7.)(36.VhAR,))P,(1:.$11.R9.(:.R=.-30.)(13.$1;.(1<.#<.R5.)(13.$1;.(1=.(9.&40.+4022.))(13.$1;.(1>.R1<.)(13.$1;.(1>.R1=.)(13.$1;.(1>.R1>.)(13.$1;.(1>.R24.)(17.$1;.))))))))P,(24.$11.R:.$26.(13.$1;.(1>.(9.&40.$27.))(17.$1;.)))P,(24.$11.R;.$37.(13.$1;.(1>.(9.&40.=))(17.$1;.)))P,(1?.$11.R<.R9.(:.R10.-30.))P,(22.+65?000.R:.)P,(22.R;.(2:.R12.+140.))P,(22.R13.(23.+2.+3?.))P,(12.(13.(14.$15.$15.)(16.$15.$15.R=.R14.)(17.(14.$15.$15.)))R11.R10.)P,(18.$11.R12.R11.)P,(19.$11.R12.)P,(2;.VCS,R10.(2:.R17.R10.))(2<.$11.VAL,VCS,(38.R2?.R18.R2>.R2=.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R17.R16.R?.R11.R15.)(3;.R?.R18.R2>.R2=.R2<.R2;.R2:.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R17.R16.R13.R12.R14.))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a6 SP F fc m0 mm size name lo fr a
      SZ A0 ACE FR GOTF LIM ST LOIMG SPL SPH MU WM MI SCS.
    pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'; unfold al_wf in ALWF'. pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
    pose proof (bv_unsigned_in_range 64 a) as AR.
    rewrite <- (Z_to_bv_bv_unsigned a).
    unfold mnr_answered, A_PAGESZ_CELL, A_GOT_CFLAGS, A_CFLAGS, A_MMAP_LIMIT in *. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 80%N). lx_postw.
  Qed.
End MmapDie.

End ARUN_1.
