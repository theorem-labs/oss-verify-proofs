(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0000f65925e091ec 1 1 8 2 28 1 59 1 3 0 1 60 1 61 8P00021d7fc494831d 0 2 0 1 39 1P0026dd2b8f600683 0 2 0 1 41 1P002f64c696ed4e3e 0 2 0 1 54 1P0057bdd72ff75613 0 2 0 1 62 1P0070d87073f35390 0 2 0 1 51 1P009448b9e4520fa8 0 2 0 1 38 1P00b608409f227114 0 2 0 1 64 1P00c027240344d09d 0 2 0 1 51 1P01051b1c6e3187b2 0 3 1 1 55 1 56 1P013d321c188d9add 0 2 0 1 59 1P017c78a0cf0179f6 0 2 0 1 54 1P01f2dcce396b8670 0 2 1 1 55 1P0289eefa29e0059e 0 5 0 8 38 8 44 8 48 8 49 8P02d22c5421da6484 0 2 0 1 42 1P02e2d24a578c4e6a 0 2 0 1 65 1P03426d0ac09ea647 1 1 8 1 0 1 2 4 1 53 1P035655d62ad9423d 0 2 0 1 54 1P03bacf47597ab91d 0 2 0 1 27 1P03c804de2b77c37f 0 2 1 1 54 1P04045270a1644539 0 6 0 1 47 1 52 1 54 1 60 1 61 1P04ee1075c11478c7 0 2 0 1 51 1P056bdcb6a31985ee 0 3 1 1 55 1 56 1P05932f5403fd16c6 0 3 0 1 4 1 36 1P060fd8693ba4eb7e 1 1 8 1 0 1 2 53 1 61 1P0690875777f42ef2 0 5 0 8 39 8 45 8 48 8 49 8P06c813a348c213a5 0 7 0 1 5 8 44 1 49 1 56 1 62 1 63 1P0700b0884aa26702 0 2 1 1 55 1P0703dbcc4df1ddcc 0 3 1 1 55 1 56 1P07fbffc9fcc92689 0 1 1 1P080470ebc3048476 0 2 0 1 33 1P081953b454a98ce7 0 4 1 1 54 1 55 1 56 1P083add02e96a967c 0 2 0 1 65 1P08b3107a30d3c42c 0 3 1 1 55 1 56 1P08cd262ee3c484b3 1 1 8 1 0 1 2 53 1 61 1P08da60fd6599af56 0 2 0 1 54 1P08ded290080c51c7 0 2 0 1 30 1P098f61d55d41e064 0 5 0 8 43 8 49 8 55 8 56 8P09b158679c3ce071 0 6 0 1 45 1 50 1 57 1 63 1 64 1P09e954e57664b7ef 0 3 0 1 43 1 45 1P0a293bb360b9e841 0 4 1 1 54 1 55 1 56 1P0ac5fc37bc589c1b 0 2 0 1 54 1P0b331a0b5e73a4d8 0 2 1 1 55 1P0b6889d0ad6105f4 0 2 0 1 54 1P0b6f853425ef8f34 0 2 0 1 54 1P0d0b882631fc2b78 0 5 0 8 44 8 50 8 55 8 56 8P0d827c40e922ed58 0 2 0 1 60 1P0db01eedbe875a33 0 2 0 1 54 1P0eafd2184981547c 0 6 0 1 47 1 52 1 54 1 60 1 61 1P0ef2b2b6a7338538 0 2 0 1 27 1P0f82735e21780d6a 0 6 0 1 47 1 52 1 54 1 60 1 61 1P101c89371f92ce82 0 5 0 8 42 8 48 8 53 8 54 8P1099a31a08d04d0b 0 5 0 8 28 8 51 8 57 8 58 8P10d275a90bf932bf 0 5 0 1 48 1 55 1 61 1 62 1P116a532f6a21e4d0 0 3 0 4096 44 1 59 1P11ff7484b55e8fe2 1 1 8 2 0 1 59 1 3 8 1 60 1 61 8P129f2893da47601e 0 6 0 8 37 8 42 8 48 8 53 8 54 8P12d30366895d165b 1 1 8 2 0 1 60 1 3 9 1 61 1 62 8P12db3a53f373675d 1 1 8 2 0 1 55 1 4 31 1 50 1 56 1 57 8P131953a21cd96349 0 2 0 1 33 1P134fbf47cf616680 0 3 1 1 55 1 56 1P138d66f3e80490a8 0 2 0 1 51 1P145bccc57e8125d7 1 1 8 3 28 1 56 1 63 1 3 0 1 64 1 65 8P14a77fd333a88ba7 0 2 0 1 62 1P14c0f9284b266b98 1 1 8 1 1 1 2 47 1 54 1P14f041467abaee2f 0 2 0 1 54 1P1560fa179c77308a 0 2 0 1 54 1P159f056d4e6c8366 0 2 0 1 48 1P15c2f648c4de3a53 0 2 0 1 37 1P15e879728340ced3 0 2 0 1 28 1P1651205c41aa9aba 0 2 0 1 59 1P16669e3123b5fc16 0 6 0 1 47 1 52 1 54 1 60 1 61 1P1721364862571c1f 0 3 1 1 55 1 56 1P179adc7a2e1ed10a 1 1 8 1 0 1 2 4 1 53 1P17a89eefdc72f943 0 5 0 1 45 1 52 1 56 1 57 1P17c17dd95308f9e0 0 2 0 1 60 1P17ffd6166ea78d09 0 2 0 1 34 1P18449fb371a55931 0 5 0 1 47 1 52 1 60 1 61 1P18a69018a88ed6fc 0 3 1 1 55 1 56 1P18bef8069a2262b6 0 1 1 1P1903d7f228b511dc 0 2 0 1 66 1P19e71c290af2674e 0 2 0 1 35 1P1a0238d84b8bf0d7 0 5 0 1 47 1 52 1 60 1 61 1P1ac7bf4d557339a3 0 2 0 1 29 1P1acab40a87e8c13d 0 2 0 1 3 1P1adae6fea05258c8 1 1 8 2 0 1 61 1 3 12 1 62 1 63 8P1adb4c31cd94082d 0 5 0 8 44 8 50 8 55 8 56 8P1b06a1ff55479c8d 0 6 0 1 44 1 49 1 56 1 62 1 63 1P1b29b6cc26f77127 0 5 0 8 41 8 47 8 53 8 54 8P1bd0a98579206510 0 3 0 1 53 1 54 1P1bef3a94de043ace 0 6 0 1 47 1 52 1 54 1 60 1 61 1P1c34ccca2430813d 0 2 0 1 54 1P1c8b09b2f5e795d3 1 1 8 1 0 1 2 46 1 53 1P1c9bf26ac531fe01 0 2 0 1 45 1P1ca56ad618946d7d 0 2 0 1 36 1P1ce5357862c13b7f 0 2 0 1 51 1P1d9649f4a64ba718 0 2 0 1 51 1P1dcc16ac51c3e9ce 0 3 0 1 42 1 44 1P1e023495eb8fe727 0 1 1 1P1e568f8b7147535c 0 2 0 1 54 1P1e78b5474d650f0b 0 2 0 1 61 1P1f8aa34ef1daeec2 1 1 8 1 1 1 2 54 1 62 1P1f9d8a702500e4c8 0 2 0 1 51 1P1fb17460ba5b9e27 0 2 0 1 54 1P1fba97dc2234db46 0 2 0 1 39 1P1fbbd8f9c236fcc4 1 1 8 1 0 1 2 4 1 61 1P205ae2f1bf9d2af8 0 6 0 1 47 1 52 1 54 1 60 1 61 1P20a7ed40732cdfa0 0 2 0 1 46 1P21247792588f62d4 0 2 0 1 54 1P22a4e5a59d78a2b8 0 2 0 1 35 1P22b5a3aa0855d4f0 0 2 0 1 54 1P22dc915a472dc9be 0 2 0 1 54 1P23c0e54cb5288597 0 2 0 1 59 1P23d9dc603dc53d9c 0 2 0 1 35 1P24a2588049911d6e 0 2 1 1 54 1P24ce54124ffd1293 0 5 0 8 39 8 45 8 48 8 49 8P24f277335ecf4455 0 2 0 1 64 1P25474e25a94ec468 0 2 0 1 2 1P2580fe71bbdaa876 0 2 0 1 30 1P2660525d97917f87 0 6 0 8 37 8 42 8 48 8 53 8 54 8P270398d9deeb0648 0 5 0 8 38 8 44 8 48 8 49 8P2770905da62fc748 0 5 0 8 41 8 47 8 53 8 54 8P27a4b5af710e8bc1 0 5 0 8 42 8 48 8 53 8 54 8P2841378d37ab97ba 0 3 1 1 55 1 56 1P289ddf537115fd6e 0 6 0 1 47 1 52 1 54 1 60 1 61 1P28b5b6edb0adfe6b 0 2 0 1 54 1P2912d92bf37565fe 0 2 0 1 54 1P2927fdf4b90a9d00 0 6 0 1 40 1 45 1 52 1 56 1 57 1P296390d4caab4b01 1 1 8 2 0 1 57 1 4 33 1 52 1 58 1 59 8P299e0176604f9261 0 2 0 1 46 1P299e2fd34db05048 0 2 0 1 66 1P2a75b5fcf8e3932d 0 2 0 1 44 1P2b38f9b379b5d7d2 0 2 0 1 26 1P2bf9d530e0516012 0 2 0 1 54 1P2c26470ec7d7d6bf 0 3 0 1 4 1 40 1P2c6778c510cff3fc 0 3 1 1 55 1 56 1P2c9fe9afe5e5efcb 0 2 0 1 54 1P2ca5053e150393e7 0 2 1 1 55 1P2e51e02e3de3be74 0 2 1 1 55 1P2e9a41256029cc71 0 2 0 1 54 1P2eb461a0f95da3a4 0 5 0 1 44 1 51 1 56 1 57 1P2ee9d99f6b2fa6fb 0 3 1 1 55 1 56 1P2ef0c5936b2e416d 0 2 0 1 54 1P2f0460ff71498220 0 2 0 1 51 1P2f553ef304d87c22 0 2 0 1 63 1P2f92e3a28de4635c 0 2 0 1 63 1P2f988c7446a7a5d4 0 5 0 1 49 1 56 1 63 1 64 1P2fdc9204d8f12602 0 2 0 1 54 1P2fdffbca18730c6a 0 2 0 1 28 1P2fe2d8fcb6879a24 0 2 0 1 2 1P302571626a6fcf90 0 2 0 1 49 1P307ec0f3e730f93c 0 2 0 1 54 1P314d10d5b8ab4c83 0 2 0 1 29 1P3243baf20fa780a3 0 5 0 8 43 8 49 8 55 8 56 8P32631b7815937d34 0 2 1 1 55 1P32a5b613959b2945 1 1 8 1 0 1 2 4 1 61 1P32c5de3b4d57ec1e 0 2 0 1 34 1P334da68d9d0afb83 1 1 8 1 0 1 2 46 1 53 1P337c5a90f007745f 0 2 1 1 55 1P338a60cdd6980a34 0 5 0 1 45 1 52 1 56 1 57 1P3431326295ff2c4e 1 1 8 2 0 1 63 1 3 14 1 64 1 65 8P34968aa6e0750118 0 2 0 1 28 1P34be92140218a57a 0 2 0 1 54 1P35401bf158e8fec0 0 5 0 1 44 1 51 1 56 1 57 1P3596111dc87740f2 0 2 0 1 54 1P35b2c7c42efa53aa 0 2 0 1 27 1P363ac92408ed1c6f 0 2 0 1 42 1P374d0a13000b3e4e 0 2 1 1 55 1P377b98f52c32beb6 1 1 8 1 0 1 2 46 1 53 1P3814eb42c6672759 0 6 0 8 39 8 44 8 50 8 55 8 56 8P383197a2d3694b6f 0 6 0 8 34 8 39 8 45 8 48 8 49 8P3871b5075dbbbcff 0 2 0 1 54 1P38a431169171fa1a 0 2 0 1 53 1P38ebd01ea69b069a 0 5 0 1 50 1 57 1 63 1 64 1P38f05b87685968c7 0 2 0 1 61 1P3900701c7718c933 0 3 1 1 55 1 56 1P3908cfbeede66a88 0 4 1 1 54 1 55 1 56 1P392c7e67289dc778 0 4 1 1 54 1 55 1 56 1P396d2852361b4640 0 2 0 1 29 1P398d2eaf24a39664 0 2 0 1 54 1P3a14eb7375963e2b 0 5 0 8 26 8 49 8 55 8 56 8P3a1d46fa298fc34d 1 1 8 2 29 1 60 1 3 0 1 61 1 62 8P3a2109869e7c6182 0 6 0 1 43 1 48 1 55 1 61 1 62 1P3a65d12c9f1fad20 0 2 0 1 54 1P3a99f6133ea784b8 0 2 0 1 51 1P3ade6e8122c3fa8e 0 2 0 1 63 1P3b074b2a0f221590 0 3 0 1 53 1 54 1P3b413e297caa1d14 0 2 0 1 54 1P3bc907ea209f7e23 0 2 0 1 54 1P3be1333a34076afe 0 3 1 1 55 1 56 1P3cb1009351213b7e 0 3 1 1 55 1 56 1P3ccde8d686f9afdc 0 5 0 1 47 1 54 1 61 1 62 1P3d803e995ebbf1eb 0 2 0 1 65 1P3df360d4d2ea1f69 0 6 0 1 47 1 52 1 54 1 60 1 61 1P3e081cc32c58f6dd 0 2 0 1 61 1P3e0d02288fb26690 0 2 0 1 3 1P3e6c20b35cb7c82e 1 1 8 1 0 1 2 53 1 61 1P3e724d17442c235b 0 2 0 1 32 1P3ec5b06deb51a039 0 3 1 1 55 1 56 1P3efa8d462f14b5b2 0 3 1 1 55 1 56 1P3f05470ff2fd8c9d 1 1 8 3 26 1 54 1 61 1 3 0 1 62 1 63 8P3f209678374b5c47 0 3 1 1 55 1 56 1P3f6de643c50cbcaf 0 2 0 1 54 1P3fdb7855ab746438 0 2 0 1 45 1N0096adce48ee1c49N00cef78eef9f20c5N0169661478e8df91N01775595c68ea434N017fd8e79b5805a5N0353616bd6d85bd9N03e478507c2ea907N041678a85fbab923N059d77ffc7ca87b3N06d007642bd7b6daN071f9870ba920f71N07dd8a852869c953N08a0212b2e2eb58aN08ecc02c0d72b653N0a18813fd196361bN0c5ed8001ce6be7bN0cafca4af855f30cN0cbe4947a67ff35cN0da28fb0e5b47f4dN0dae925b7043cadfN0e1d725781e2ed75N0e2ded7938c74187N0eb7cca67eb9bf89N0fb2fefada0bf5abN1154a6dab8b480b5N118ad2cc3ca1979fN119ff9e37a9f4b85N11c6fdbad317b465N130ae10255301d29N1323fef66827cc8dN1497a1fe4f3e1a7cN15050a51825d0881N1562b00cbd7f0cd6N156536fa52b431dfN165db3482e1a8a7dN16cad726fb27d654N1768b87a71cfcba6N1773fc66fb5162bbN189ee3be5c921215N191ff19fd84f52b9N1a21f1576217e1b5N1b1390ee4eb380ceN1b1f43761c604c52N1b9fd6b6ff52f441N20648df341a4ea1bN2072a79259680075N20ac8ea29b97da4aN227ee3a5675e450eN229c0811376db6fcN22de8e2ca5a55c80N230cb24cfde60bd9N23165aee9751231cN2392a273638b902bN2574f5f1e52c34eaN25792f033f0d58d3N25acf9daa8b86f30N25e3e3d61af6d25cN26294231f45f655bN268fa9715a5d8da2N2825a0aa0d295928N28331e56c8df7d2cN2882a300f724a4b3N28e28557d6f84d20N28f4ec8728defcaeN2907a775dfd01873N2a08648b885d4001N2a137b908c83f238N2a9f2b45389d6e24N2bb22e8c5debd128N2bcd110c055ba4beN2c04654e94a8f5e4N2d4c992b06a58a01N2dd26ac6678c884dN2e18e0e52b783fe9N2ec93886e113689cN306ef074fc121138N3092fbf11a1f7dd3N31dadb503aab53dfN341fd3b1cc8dbb7dN3480f9d932729245N34908704abe17c97N34b3f2a1959d897eN35a703b322ca434eN35bf66e160ab2ac3N3655f8c1d6b02af5N365c432e06c3064dN36b422414a8fead0N36f5b3ed01dd6d86N3721d2a48b9725a7N3779af921a22a95bN383559f18d6e43d4N384665643e945322N39276f3366e55088N39757c1d9f09847dN39e937e6c81b9181N3a04374641e911fcN3b9cd24f1429b36eN3cf848fd24fcc8faN3d6c7ff33b921ff5N3e3741ead7acd30dN3ed0185318a6bd42N3f5d4bea65786198"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_Unwind () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.eq"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ov_read_bytes"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "Corelib.Init.Datatypes.Some"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.le8"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "ARUN_1.A_UF_EXIT"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u64arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.UnwindFast.uf_exit_post"; "ARUN_1.A_UF_LOOP"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.LibA.AUnw.uwc"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "ARUN_1.UnwindFast.uf_post"; "ARUN_1.A_GOT_PAGESZ"; "ARUN_1.A_PAGESZ_CELL"; "ARUN_1.A_UNWIND_FAST"].

Section ARUN_1. Context {hAR : arun}.
Definition A_UNWIND_FAST : Z := 0x089f2c.
Definition A_UF_LOOP : Z := 0x089fec.
Definition A_UF_EXIT : Z := 0x08a028.
Definition A_PAGESZ_CELL : Z := 0x1994a0.
Definition A_GOT_PAGESZ : Z := 0x0f5e30.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L10621326139.9 L28130280371.16L58789506866.14L59626434633.11L65164544592.1000000?00M00X00[00dS2lo2hi1a2H12H2S1a2bs4Hlen2L8S1a2bs4HlenS1aS2hi1a2H2". (* [comment removed for export] *)
Lemma stk_read8 : ltac2:(CDefT.buildp (gd_tbl_AW_Unwind ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))Plo,$4.Phi,$4.Pa,$4.P,(5.R5.R4.R3.R2.)P,(6.R4.R2.)P,(6.(7.R3.+8.)R4.)(8.(2.&40.)Lv,(2.&40.)(9.(3.(0.(2.&8.)))(:.R9.R8.(;.R5.)#8.)(<.(0.(2.&8.))(=.R1.))))")
(* [comment removed for export] *).
Proof.
  intros segs m lo hi a ST H1 H2.
  destruct (stk_split segs m lo a hi ST ltac:(lia)) as [_ ST1].
  destruct (stk_split segs m a (a + 8) hi ST1 ltac:(lia)) as [ST2 _].
  destruct (stk_bytes segs m a (a + 8) ST2 ltac:(lia)) as (bs & Hlen & HB).
  exists (le_bytes_to_word bs).
  assert (L8 : (0 + 8 <= length bs)%nat) by (rewrite Hlen; lia).
  pose proof (bytes_at_ov_read segs m a bs 0 8 HB L8) as R.
  assert (L8' : length bs = 8%nat) by (rewrite Hlen; lia).
  rewrite Z.add_0_r, skipn_O in R. rewrite firstn_all2 in R by (rewrite L8'; apply Nat.le_refl).
  rewrite le8_le_bytes_to_word by exact L8'. exact R.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L47747484763.6000001S". (* [comment removed for export] *)
Lemma cell8_read : forall segs m a w,
  ro_cells segs m a [C8 w] -> ov_read_bytes segs m (wa a) 8 = Some (le8 w).
Proof.
  intros segs m a w [_ HB]. cbn [cells_bytes cbytes app] in HB. rewrite app_nil_r in HB.
  pose proof (bytes_at_ov_read segs m a (le8 w) 0 8 HB ltac:(rewrite length_le8; lia)) as R.
  rewrite Z.add_0_r, skipn_O in R. rewrite firstn_all2 in R by (rewrite length_le8; apply Nat.le_refl). exact R.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section UnwindFast.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variables (STK PC BP TOP BOT : Z).
  (* [comment removed for export] *)
  Variables (RLO RHI : Z).
  Hypothesis RNG : RLO <= BP - 16 /\ TOP - 16 <= RHI /\ 0 <= RLO /\ RHI <= 2^63.
  Hypothesis RCS : crange CS RLO (RHI - RLO).
  Hypothesis STKCS : crange CS STK 2064.
  Hypothesis STKB : 0 <= STK /\ STK + 2064 <= RLO.   (* [comment removed for export] *)
  Hypothesis TOPB : 2^23 <= TOP /\ TOP <= 2^47 /\ BOT = TOP - 2^23.
  Hypothesis PCB : 4096 <= PC < 2^47.
  Hypothesis BPB : 0 <= BP < 2^47.

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Definition uf_exit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (B : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Unwind ()) "Lms',$>.(8.(2.&40.)La2,(2.&40.)(8.(2.&40.)La4,(2.&40.)(8.(2.&40.)La5,(2.&40.)(8.(2.&40.)La6,(2.&40.)(8.(2.&40.)La7,(2.&40.)(8.P,(2.&40.)(3.(2.&8.))Lmm,P,(2.&40.)(3.(2.&8.))(8.(0.(2.&40.))Lws,(0.(2.&40.))(8.$4.Lsize,$4.(?.(9.$>.R9.(10.(11.O1;.O1:.O19.O18.O;.O:.O9.O17.O16.(12.&40.VSTK,)(12.&40.VPC,)R8.(12.&40.+1000.)R7.R6.R5.R4.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O8.O7.O6.O5.)O4.(12.&40.$13.)O3.(14.(2.&40.))R3.(15.$16.)))(?.(17.(18.(19.$4.$4.)(1:.$4.$4.(7.VSTK,+8.)(7.VSTK,+<.))(18.(19.$4.$4.)(1:.$4.$4.(7.VSTK,+10.)(7.VSTK,+100.))(1;.(19.$4.$4.))))O1.R3.)(?.(1<.$16.O1.R3.)(?.(1=.$16.R3.)(?.(1>.$16.R3.(7.VSTK,+8.)(18.$1?.(20.(12.&40.R1.))(1;.$1?.)))(?.(21.$16.R3.(7.VSTK,+10.)R2.)(?.(?.(6.+1.R1.)(6.R1.+1>.))(?.(6.R1.O2.)(9.$22.(23.(2.&40.)R2.)#1>.)))))))))))))))))")
(* [comment removed for export] *).

  Ltac uf_exit :=
    apply evtA_done; unfold uf_exit_post; do 8 eexists;
    split; [ first [ reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity ] |];
    split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
    split; [eassumption|]; split; [eassumption|];
    split; [lia|]; split; [lia| first [assumption | rewrite upd_length; lia] ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac uf_lx_exit := apply evtA_done; unfold uf_exit_post; do 8 eexists;
    split; [lx_mseq|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
    split; [eassumption|]; split; [eassumption|]; split; [lia|]; split; [lia| first [assumption | rewrite upd_length; lia] ].
  Ltac uf_lx_loop IH B :=
    match goal with K : context [zlow 64 (Z.land ?f 7) =? zlow 64 0], U : u64arr _ ?mx (STK + 16) ?ws', Z : rw_cells _ ?mx (STK + 8) [C4 (Z_to_bv 64 ?sz)] |- _ =>
      let HA := fresh "HAl" in
      assert (HA : (zlow 64 f) mod 8 = 0) by (rewrite land7_mod in K; clear -K; lx_klin; unfold zlow; lia);
      replace (Z_to_bv 64 f) with (Z_to_bv 64 (zlow 64 f)) by (rewrite <- (lx_bvu64 f); first [apply Z_to_bv_bv_unsigned | symmetry; apply Z_to_bv_bv_unsigned]);
      eapply (IH (zlow 64 f) sz B) with (ws := ws');
      try eassumption; try (rewrite upd_length; lia); unfold zlow in *; lia
    end.
  Ltac uf_lx_leaf IH B :=
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch pc with 0x8a028 => uf_lx_exit | 0x89fec => uf_lx_loop IH B end end.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00Q0@L13630378087.103L13630384185.97 L13630384190.99 L13630384191.101L14081750770.97 L14081750772.101L14081750773.99 L26349714833.63 L31845829426.99 L31845829427.101L31845829429.97 L31845839723.103L50896616134.101L50896616134.103L50896616134.86 L50896616134.91 L50896616134.99 L52446493258.103L52446493258.105L53504412434.2  L53506509622.2  L57597071270.103L57597071270.105L59743733596.101L59743733596.103L59743733596.86 L59743733596.91 L59743733596.99 L59754153783.105L64210782430.2  L64212879610.2  L6578611204.2   L6580708384.2   00001301n02i03d04c05c06c08c09J0:10:W0;I0<E0=A0>=0?80@40AD0BW0B]0Bc0Co0E90E\0F?0Fb0GE0Gh0HZ0H`0Hf0I20I=S3STK2BP3TOP3RLO1N5frame4size2ws2HN3HF12HL2R12K02K13HLz3lxv4lxv02H5S3STK2BP3TOP3RLO1N5frame4size2ws2HN3HF12HL2R12K02K13HLz3lxvS3STK2BP3TOP3RLO1N5frame4size2ws2HN3HF12HL2R12K02K13HLz3lxvS3STK2BP3TOP3RLO1N5frame4size2ws2HN3HF12HL2R12K02K13HLz3lxvS3STK2BP3TOP3RLO1N5frame4size1B2ws2HN2HB3HF12HL2R12K02K13lxv2H9S3STK2BP3TOP3RLO1N5frame4size1B2ws2HN2HB3HF12HL2R12K02K13lxv3H11S3STK2BP3TOP3RLO1N5frame4size1B2ws2HN2HB3HF12HL2R12K02K13lxv3H10S2AL2CS3STK2PC2BP3TOP5frame4size1B2ra2sp2gp2tp2s22s32s42s52s62s72s82s93s103s112t02t12t22t32t42t52t62a62a71F2fc2m02mm2ws2HN2HF2HLS3TOP1N5frame4size2ws2HN3HS12HL3lxv3H10S3TOP1N5frame4size2ws2HN3HS12HL3lxv3H11S3TOP1N5frame4size2ws2HN3HS12HL3lxv2H9S2PC3TOP1N5frame4size2ws2HN3HS12HL3lxv4lxv02H33H12S3STK2BP3TOP3RLO1N5frame4size1B2ws2HN2HB3HF12HL2R12K02K13H11S3STK2BP3TOP3RLO1N5frame4size1B2ws2HN2HB3HF12HL2R12K02K13H12S3STK2BP3TOP3RLO1N5frame4size1B2ws2HN2HB3HF13HS22HL2R12K02K1S3STK2BP3TOP3RLO1N5frame4size1B2ws2HN2HB3HF12HL2R12K02K12H5S3STK2BP3TOP3RLO1N5frame4size1B2ws2HN2HB3HF12HL2R12K02K13H10S3STK2PC2BP3TOP3RLO3PCB1N5frame4size2ws2HN3HF12HA2HL2R12K02K13lxv4lxv02H32H53HAlS3STK2PC2BP3TOP3RLO3PCB1N5frame4size2ws2HN3HF12HA2HL2R12K02K13lxv4lxv02H32H52H93HAlS4lxv0S4lxv0S3STK2PC2BP3TOP3RLO3PCB1N5frame4size2ws2HN3HF12HL2R12K02K13lxv4lxv02H32H42H5S3STK2PC2BP3TOP3RLO3PCB1N5frame2ws2HN3HF12HL2R12K02K13lxv4lxv02H32H42H52H9S3TOP1N5frame4size2ws2HN3HS13HS22HLS3TOP1N5frame4size2ws2HN3HS13HS22HLS3TOP1N5frame4size2ws2HN3HS13HS22HLS3TOP1N5frame4size2ws2HN3HS13HS22HLS3TOP1N5frame4size2ws2HN3HS13HS22HLS2PC3TOP1N5frame4size2ws2HN3HS13HS22HL3lxv4lxv02H3S4lxv0S4lxv0S4lxv05LXKT0S4lxv04LXKT". (* [comment removed for export] *)
  Lemma uf_loop : ltac2:(CDefT.buildp (gd_tbl_AW_Unwind ()) "PN,$22.Pframe,$4.Psize,$4.PB,$4.Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)PF,(24.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Pws,(0.(2.&40.))P,(6.(25.(25.VTOP,+10.)R1?.)(26.+8.(27.R20.)))P,(6.+1>.R1>.)P,(?.(6.VBP,R21.)(28.R21.(25.VTOP,+10.)))P,(9.$4.(29.R22.+8.)=)P,(?.(6.+1.R22.)(6.R22.+1>.))P,(9.$22.(23.(2.&40.)R6.)#1>.)P,(1>.$16.R8.(7.VSTK,+8.)(18.$1?.(20.(12.&40.R24.))(1;.$1?.)))P,(21.$16.R9.(7.VSTK,+10.)R8.)P,(5.$16.R:.VRLO,VRHI,)P,(17.(18.(19.$4.$4.)(1:.$4.$4.(7.VSTK,+8.)(7.VSTK,+<.))(18.(19.$4.$4.)(1:.$4.$4.(7.VSTK,+10.)(7.VSTK,+100.))(1;.(19.$4.$4.))))R<.R;.)P,(1<.$16.R=.R<.)P,(1=.$16.R=.)(2:.$16.VAL,VCS,(2;.R28.R27.R26.R25.(12.&40.+1>.)(12.&40.(25.VTOP,+10.))R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R11.R10.R29.R?.)(10.(11.R28.R27.R26.R25.R1:.R19.R18.(12.&40.+1>.)(12.&40.(25.VTOP,+10.))(12.&40.VSTK,)(12.&40.VPC,)(12.&40.R2;.)(12.&40.+1000.)(12.&40.(7.VSTK,+10.))(12.&40.R2:.)R13.R12.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R17.R16.R15.R14.)R11.(12.&40.$2<.)R10.(14.(2.&40.))R>.(15.$16.)))")
(* [comment removed for export] *).
  Proof.
    induction N as [|N IH]; intros frame size B ra sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a6 a7 F fc m0 mm ws
      HN HB HF HA HS HL HSZ HTR SR MU WM MI; [lia|].
    facts. destruct RNG as (R1 & R2 & R3 & R4). destruct STKB as [K0 K1].
    unfold A_UF_LOOP, A_UF_EXIT in *. assert (HLz : Z.of_nat (length ws) = 30) by (rewrite HL; reflexivity). destruct HF as [HF1 HF2]. destruct HS as [HS1 HS2].
    (* [comment removed for export] *)
    lx_run (PLAN [0x89fec; 0x8a028] [] 40%N).
    all: uf_lx_leaf IH B.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Variables (LO TOPU : Z).
  Hypothesis LOB : LO <= BP.
  Hypothesis TOPUB : TOP <= TOPU <= 2^64.

  (* [comment removed for export] *)
  Ltac uf_lx_loopd IH B CH0 :=
    match goal with K : context [zlow 64 (Z.land ?f 7) =? zlow 64 0], U : u64arr _ ?mx (STK + 16) ?ws', Z : rw_cells _ ?mx (STK + 8) [C4 (Z_to_bv 64 ?sz)] |- _ =>
      let HA := fresh "HAl" in
      assert (HA : f mod 8 = 0) by (rewrite land7_mod in K; clear -K; lx_klin; lia);
      unfold zlow in *; rewrite ?(Z.mod_small f (2 ^ 64)) in * by lia;
      lx_unhide; inversion CH0; subst;
      [ exfalso; lia
      | lazymatch goal with CH' : uwc _ _ _ _ ?v' f ?d1, LNK' : ro_cells _ _ (f - 16) _ |- _ =>
          eapply (IH f sz B v' d1) with (ws := ws'); try eassumption; try lia;
          try (rewrite upd_length; lia); try (replace (f + -16) with (f - 16) by lia; exact LNK') end
      | exfalso; lia ]
    end.
  Ltac uf_lx_leafd IH B CH0 :=
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch pc with 0x8a028 => uf_lx_exit | 0x89fec => uf_lx_loopd IH B CH0 end end.
  Local Ltac2 Set LiaOrc.tbl := fun () => "00[0@L13630384184.109L13630384185.111L13630384190.113L14081750770.111L14081750771.109L14081750773.113L1409796735.2   L1411893851.2   L25069384037.90 L26349714833.72 L31845829426.113L31845829428.109L31845829429.111L31845829556.123L33364669280.76 L50896616134.101L50896616134.106L50896616134.111L50896616134.113L50896616134.115L51681067586.123L51681067587.123L52482273985.123L53504412434.2  L53506509622.2  L54162290236.123L54162290237.123L58951069478.2  L58953166594.2  L59310676308.116L59310676309.116L59310676309.117L59310676314.117L59517409678.115L59517409678.117L59743733596.101L59743733596.106L59743733596.111L59743733596.113L59743733596.115L59754168297.123L60558716898.123L67591795767.12300000k01f02a03b04c05d05o06906g08g09N0:40:Z0;K0<O0=L0>I0?F0@C0A@0BL0CV0DG0DL0DQ0E^0Fm0G20G70Gk0HZ0JC0Ko0L[0MB0Me0NH0Nk0ON0P10Pb0R00RaS3STK2BP3TOP3RLO1N5frame4size2ws2HN3HF12HL2R12K02K13HLz3lxvS3STK2BP3TOP3RLO1N5frame4size2ws2HN3HF12HL2R12K02K13HLz3lxvS3STK2BP3TOP3RLO1N5frame4size2ws2HN3HF12HL2R12K02K13HLz3lxvS3STK2BP3TOP3RLO1N5frame4size1B1d2ws2HN2HB3HF12HL2D02R12K02K13lxvS3STK2BP3TOP3RLO1N5frame4size1B1d2ws2HN2HB3HF12HL2D02R12K02K13lxvS3STK2BP3TOP3RLO1N5frame4size1B1d2ws2HN2HB3HF12HL2D02R12K02K13lxvS3nfv5LXKT0S3nfv4LXKTS3STK2BP3TOP3RLO1N5frame2ws2HN3HF12HL2R12K02K1S2AL2CS3STK2PC2BP3TOP5frame4size1B2ra2sp2gp2tp2s22s32s42s52s62s72s82s93s103s112t02t12t22t32t42t52t62a62a71F2fc2m02mm2ws2HN2HF2HLS3TOP1N5frame4size2ws2HN3HS12HL3lxv3H10S3TOP1N5frame4size2ws2HN3HS12HL3lxv2H8S3TOP1N5frame4size2ws2HN3HS12HL3lxv2H9S2PC3TOP1N5frame4size3nfv2ws2HN3HS12HL3lxv2H43H11S3STK2BP3TOP3RLO3RHI3RNG4STKB1N5frame4size1B1d2ws2HN2HB2HF2HS2HL3CAPS3STK2BP3TOP3RLO1N5frame4size1B1d2ws2HN2HB3HF12HL2D02R12K02K1S3STK2BP3TOP3RLO1N5frame4size1B1d2ws2HN2HB3HF12HL2D02R12K02K1S3STK2BP3TOP3RLO1N5frame4size1B1d2ws2HN2HB3HF12HL2D02R12K02K1S3STK2BP3TOP3RLO1N5frame4size1B1d2ws2HN2HB3HF12HL2D02R12K02K1S3STK2BP3TOP3RLO1N5frame4size1B1d2ws2HN2HB3HF12HL2D02R12K02K1S3STK2PC2BP3TOP3RLO3PCB1N5frame4size3nfv2ws2HN2VR3HF12HL2R12K02K13lxv2H43H15S3STK2PC2BP3TOP3RLO3PCB1N5frame3nfv2ws2HN2VR3HF12HL2R12K02K13lxv2H42H83H16S2PC3TOP1N5frame4size1B3nfv2ws2HN2d02HB2HL3lxv2H4S3nfvS3nfvS3STK2PC2BP3TOP3RLO3PCB1N5frame3nfv2ws2HN2VR3HF12HL2R12K02K13lxv2H42H52H83H16S3STK2PC2BP3TOP3RLO3PCB1N5frame4size3nfv2ws2HN2VR3HF12HL2R12K02K13lxv2H42H53H15S3nfvS3nfvS2PC3TOP1N5frame4size3nfv1d2ws2HN2HL4NCAP3lxv2H43H15S2PC3TOP1N5frame3nfv1d2ws2HN2HL4NCAP3lxv2H43H16S3STK2PC2BP3TOP3RLO3PCB2LO4TOPU3LOB1N5frame4size3nfv2ws2HN2VR3HF12HA2HL2R12K02K13TU13lxv2H42H52H63HAl3H16S3STK2PC2BP3TOP3RLO3PCB2LO4TOPU3LOB1N5frame4size3nfv2ws2HN2VR3HF12HA2HL2R12K02K13TU13lxv2H42H52H62H83HAl3H17S2PC3TOP1N5frame4size3nfv2ws2HN2VR2HL3lxv2H4S2PC3TOP1N5frame3nfv2ws2HN2VR2HL3lxv2H4S3TOP1N5frame4size2ws2HN3HS13HS22HLS3TOP1N5frame4size2ws2HN3HS13HS22HLS3TOP1N5frame4size2ws2HN3HS13HS22HLS3TOP1N5frame4size2ws2HN3HS13HS22HLS3TOP1N5frame4size2ws2HN3HS13HS22HLS2PC3TOP1N5frame4size3nfv2ws2HN3HS13HS22HL3lxv2H4S3STK2PC2BP3TOP3RLO3PCB1N5frame4size3nfv2ws2HN2VR3HF12HL2R12K02K13lxv5LXlen2H4S2PC3TOP1N5frame4size1B3nfv2ws2HN2d02HB2HL3lxv2H4". (* [comment removed for export] *)
  Lemma uf_loop_d : ltac2:(CDefT.buildp (gd_tbl_AW_Unwind ()) "PN,$22.Pframe,$4.Psize,$4.PB,$4.Pnfv,$4.Pd,$4.Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)PF,(24.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Pws,(0.(2.&40.))P,(6.(25.(25.VTOP,+10.)R21.)(26.+8.(27.R22.)))P,(6.(7.(7.R21.R1>.)+1.)R20.)P,(?.(6.=R20.)(28.R20.(2=.+2.+40.)))P,(?.(6.VBP,R24.)(28.R24.(25.VTOP,+10.)))P,(9.$4.(29.R25.+8.)=)P,(?.(6.+1.R25.)(6.R25.+1>.))P,(9.$22.(23.(2.&40.)R7.)#1>.)P,(1>.$16.R9.(7.VSTK,+8.)(18.$1?.(20.(12.&40.R27.))(1;.$1?.)))P,(21.$16.R:.(7.VSTK,+10.)R9.)P,(5.$16.R;.VRLO,VRHI,)P,(2>.$16.R=.(7.R2;.-10.)(18.$1?.(2?.(12.&40.R28.))(1;.$1?.)))P,(30.$16.R>.VLO,VTOPU,R29.R2<.R28.)P,(17.(18.(19.$4.$4.)(1:.$4.$4.(7.VSTK,+8.)(7.VSTK,+<.))(18.(19.$4.$4.)(1:.$4.$4.(7.VSTK,+10.)(7.VSTK,+100.))(1;.(19.$4.$4.))))R?.R>.)P,(1<.$16.R10.R?.)P,(1=.$16.R10.)(2:.$16.VAL,VCS,(2;.R2;.R2:.R29.R28.(12.&40.+1>.)(12.&40.(25.VTOP,+10.))R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R14.R13.R2>.R12.)(10.(11.R2;.R2:.R29.R28.R1=.R1<.R1;.(12.&40.+1>.)(12.&40.(25.VTOP,+10.))(12.&40.VSTK,)(12.&40.VPC,)(12.&40.R30.)(12.&40.+1000.)(12.&40.(7.VSTK,+10.))(12.&40.R2?.)R16.R15.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1:.R19.R18.R17.)R14.(12.&40.$2<.)R13.(14.(2.&40.))R11.(15.$16.)))")
(* [comment removed for export] *).
  Proof.
    induction N as [|N IH]; intros frame size B nfv d ra sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a6 a7 F fc m0 mm ws
      HN HB VR HF HA HS HL HSZ HTR SR LNK0 CH0 MU WM MI; [lia|].
    pose proof (uwc_nonneg _ _ _ _ _ _ _ CH0) as D0.
    (* [comment removed for export] *)
    destruct (Z_le_gt_dec 28 d) as [CAP|NCAP].
    { eapply (uf_loop (S N) frame size B); try eassumption; lia. }
    facts. destruct RNG as (R1 & R2 & R3 & R4). destruct STKB as [K0 K1]. destruct TOPUB as [TU1 TU2].
    unfold A_UF_LOOP, A_UF_EXIT in *. assert (HLz : Z.of_nat (length ws) = 30) by (rewrite HL; reflexivity).
    destruct HF as [HF1 HF2]. destruct HS as [HS1 HS2].
    assert (LNK : ro_cells asegs mm (frame + -16) [C8 (Z_to_bv 64 nfv)]) by (eapply ro_cells_transport; [exact LNK0| exact MU| cbn; lia]).
    lx_hide CH0. lx_hide LNK0.
    (* [comment removed for export] *)
    lx_run (PLAN [0x89fec; 0x8a028] [] 40%N).
    all: uf_lx_leafd IH B CH0.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition uf_post (ra : word) (SP : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (lo B : Z) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Unwind ()) "Lms',$>.(8.(2.&40.)La0,(2.&40.)(8.(2.&40.)La1,(2.&40.)(8.(2.&40.)La2,(2.&40.)(8.(2.&40.)La3,(2.&40.)(8.(2.&40.)La4,(2.&40.)(8.(2.&40.)La5,(2.&40.)(8.(2.&40.)La6,(2.&40.)(8.(2.&40.)La7,(2.&40.)(8.P,(2.&40.)(3.(2.&8.))Lmm,P,(2.&40.)(3.(2.&8.))(8.(0.(2.&40.))Lws,(0.(2.&40.))(8.$4.Lsize,$4.(?.(9.$>.R<.(10.(11.O1<.(12.&40.O1;.)O1:.O19.O<.O;.O:.O18.O17.R;.R:.R9.R8.R7.R6.R5.R4.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O9.O8.O7.O6.)O5.(31.O1<.)O4.(14.(2.&40.))R3.(15.$16.)))(?.(17.(18.(19.$4.$4.)(1:.$4.$4.(7.VSTK,+8.)(7.VSTK,+<.))(18.(19.$4.$4.)(1:.$4.$4.(7.VSTK,+10.)(7.VSTK,+100.))(18.(19.$4.$4.)(1:.$4.$4.O3.O1;.)(1;.(19.$4.$4.)))))O1.R3.)(?.(1<.$16.O1.R3.)(?.(1=.$16.R3.)(?.(1>.$16.R3.(7.VSTK,+8.)(18.$1?.(20.(12.&40.R1.))(1;.$1?.)))(?.(21.$16.R3.(7.VSTK,+10.)R2.)(?.(?.(6.+1.R1.)(6.R1.+1>.))(?.(6.R1.O2.)(?.(9.$22.(23.(2.&40.)R2.)#1>.)(?.(5.$16.R3.O3.O1;.)(5.$16.R3.VRLO,VRHI,))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Lemma uf_epilogue : ltac2:(CDefT.buildp (gd_tbl_AW_Unwind ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PSP,$4.Px8,(2.&40.)Px9,(2.&40.)Px18,(2.&40.)Px19,(2.&40.)Px20,(2.&40.)Px21,(2.&40.)Px22,(2.&40.)Pa2,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)PF,(24.&5.(2.&40.))Pfc,(2.&20.)Pm0,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))Pws,(0.(2.&40.))Psize,$4.Plo,$4.PB,$4.P,(1>.$16.R5.(7.R15.-40.)(18.$1?.(2?.R>.)(18.$1?.(2?.R?.)(18.$1?.(2?.R10.)(18.$1?.(2?.R11.)(18.$1?.(2?.R12.)(18.$1?.(2?.R13.)(18.$1?.(2?.R14.)(18.$1?.(2?.R2;.)(1;.$1?.))))))))))P,(5.$16.R6.R3.(7.R16.-40.))P,(6.+65?000.R4.)P,(6.R5.(25.R18.+40.))P,(6.(7.R19.+8.)VSTK,)P,(1>.$16.R:.(7.VSTK,+8.)(18.$1?.(20.(12.&40.R8.))(1;.$1?.)))P,(21.$16.R;.(7.VSTK,+10.)R:.)P,(?.(6.+1.R:.)(6.R:.+1>.))P,(6.R;.R9.)P,(9.$22.(23.(2.&40.)R=.)#1>.)P,(17.(18.(19.$4.$4.)(1:.$4.$4.(7.VSTK,+8.)(7.VSTK,+<.))(18.(19.$4.$4.)(1:.$4.$4.(7.VSTK,+10.)(7.VSTK,+100.))(18.(19.$4.$4.)(1:.$4.$4.R<.R1?.)(1;.(19.$4.$4.)))))R10.R?.)P,(1<.$16.R11.R10.)P,(1=.$16.R11.)P,(5.$16.R12.VRLO,VRHI,)P,(32.VCS,R10.(25.R23.R10.))(2:.$16.VAL,VCS,(33.R3:.R24.R39.R38.R23.R22.R21.R20.R1?.R1>.R1=.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R17.R16.R11.R10.R15.)(10.(11.R3:.(12.&40.(7.R24.-40.))R39.R38.R2;.R2:.R29.R37.R36.(12.&40.VSTK,)(12.&40.VPC,)R1<.(12.&40.+1000.)R1;.R1:.R19.R18.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R28.R27.R26.R25.)R17.(12.&40.$13.)R16.(14.(2.&40.))R14.(15.$16.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 SP x8 x9 x18 x19 x20 x21 x22 a2 a4 a5 a6 a7 F fc
      m0 mm ws size lo B FR ST LOIMG SPL SPK HSZ HTR HS HSB HL MU WM MI SR SCS.
    facts. destruct STKB as [K0 K1]. unfold A_UF_EXIT. assert (HLz : Z.of_nat (length ws) = 30) by (rewrite HL; reflexivity).
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 20%N). lx_same.
    apply evtA_done. unfold uf_post. lx_exs. lx_ands; [> lx_mseq | ..]; first [eassumption | lia].
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0@L12300011935.107L12428150072.117L1662257670.107 L17210582737.90 L25006922291.107L25076071819.118L28571791405.109L28618380761.90 L32128404131.118L34993750853.107L37698010799.107L39042354655.107L39056978580.107L39056978583.105L46034004545.105L46034004546.107L49743793558.90 L51521466385.107L57622410744.119L58355878514.118L60556677161.107L60558716769.105L60558716770.107L7608133464.117 L9471306659.118 00000H00c01701A01R02802m03D03m04>04Z04g05405A05S05e05o06>06j07;07R07i08@08^09GS2PC2BP3TOP3BPB2ws2HL2H7S3STK2PC2BP2SP2ws2lo2HL3SPKS2PC2BP3TOP2ws2HL2H7S2BP2ws2HLS2PC2BP3TOP2ws2HLS3STK2PC2BP2SP2ws2HL3SPK3RLO3BPB2R12K1S3STK2PC2BP3RLO3BPB4TOPU2SP2ws2lo2HL3SPK2R12K12a'3Ha'S2BP3TOP3BOT4TOPB2ws2HLS3STK2PC2BP3BPB2SP2ws2lo2HL5LOIMG3SPL3SPKS2PC2BP3BPB2ws2HLS2PC2BP3TOP4TOPU5TOPUB2ws2HLS2PC2BP2ws2HLS2PC2BP2ws2HLS2PC2BP2ws2HLS2PC2BP2ws1d2HL2D0S2PC2BP2ws1d2HL2D0S2BP2ws2HLS2PC2BP2ws1d2HLS3STK2PC2BP2SP2ws2lo1d2HL2x42x52x64POST2x71HS3STK2PC2BP2ws2HLS2PC2BP3BPB2ws2HL5LXlenS2PC2BP3BPB2ws2HL5LXlenS2PC2BP3BPB2ws2HL5LXlenS3STK2PC2BP3RLO3RHI4STKB2ws2HLS3STK2PC2BP3BPB2SP2ws2lo2HL5LOIMG3SPL3SPK". (* [comment removed for export] *)
  Lemma unwind_fast_spec : ltac2:(CDefT.buildp (gd_tbl_AW_Unwind ()) "Pra,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pszj,(2.&40.)PSP,$4.PF,(24.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))Pws,(0.(2.&40.))Plo,$4.Pv,$4.Pd,$4.P,(9.$4.(29.VBP,+8.)=)P,(9.$22.(23.(2.&40.)R5.)#1>.)P,(1>.$16.R7.(7.VSTK,+8.)(18.$1?.(20.R;.)(1;.$1?.)))P,(21.$16.R8.(7.VSTK,+10.)R7.)P,(5.$16.R9.VRLO,VRHI,)P,(2>.$16.R:.(7.VBP,-10.)(18.$1?.(2?.(12.&40.R7.))(1;.$1?.)))P,(30.$16.R;.VLO,VTOPU,R8.VBP,R7.)P,(?.(6.=R9.)(28.R9.(2=.+2.+40.)))P,(2>.$16.R=.$34.(18.$1?.(2?.(12.&40.$35.))(1;.$1?.)))P,(2>.$16.R>.$35.(18.$1?.(2?.(12.&40.+1000.))(1;.$1?.)))P,(5.$16.R?.R=.R12.)P,(6.+65?000.R>.)P,(6.R?.(25.R14.+40.))P,(6.(7.R15.+8.)VSTK,)P,(32.VCS,R11.(25.R16.R11.))P,(1=.$16.R14.)(2:.$16.VAL,VCS,(33.R31.R18.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R17.R16.R13.(7.R11.+2.)R15.)(10.(11.R31.(12.&40.R18.)R30.R2?.R22.R21.R20.R2>.R2=.(12.&40.VSTK,)(12.&40.VPC,)(12.&40.VBP,)(12.&40.VTOP,)(12.&40.VBOT,)(12.&40.+1>.)R1;.R1:.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R1?.R1>.R1=.R1<.)R17.(12.&40.$36.)R16.(14.(2.&40.))R15.(15.$16.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a6 a7 szj SP F fc m ws lo v d
      BPA HL HSZ HTR SR LNK0 CH0 VR GOT PGS ST LOIMG SPL SPK SCS MI.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ CH0) as D0.
    facts. destruct RNG as (R1 & R2 & R3 & R4). destruct STKB as [K0 K1]. destruct TOPB as (T1 & T2 & T3). destruct TOPUB as [TU1 TU2].
    pose proof (munch_refl [(STK + 8, STK + 12); (STK + 16, STK + 256); (lo, SP)] m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    unfold A_UNWIND_FAST, A_GOT_PAGESZ, A_PAGESZ_CELL, A_UF_EXIT in *.
    assert (TPG : 2048 <= Z.shiftr TOP 12) by (rewrite Z.shiftr_div_pow2 by lia; apply Z.div_le_lower_bound; lia).
    lx_hide CH0. assert (HLz : Z.of_nat (length ws) = 30) by (rewrite HL; reflexivity).
    (* [comment removed for export] *)
    lx_run (PLAN [0x89fec; 0x8a028] [] 40%N).
    all: lazymatch goal with |- evtA _ _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch pc with
      | 0x8a028 => first
          [ exfalso; match goal with K : context [Z.land ?bp 7] |- _ => rewrite land7_mod, BPA in K; clear -K; lx_klin; lia end
          | eapply uf_epilogue; try eassumption; try lia; rewrite upd_length; lia ]
      | 0x89fec => idtac
      end end.
    replace (TOP + -16) with (TOP - 16) by lia.
    (* [comment removed for export] *)
    lx_unhide.
    lazymatch goal with MU' : munch _ m ?mx |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (CHx : uwc asegs mx LO TOPU v BP d)
        by (eapply (uwc_munch asegs); [exact CH0| exact MU'| lia| lia| intros a' Ha'; cbn; lia]);
      assert (LNKx : ro_cells asegs mx (BP + -16) [C8 (Z_to_bv 64 v)])
        by (first [assumption | (eapply ro_cells_transport; [exact LNK0| exact MU'| cbn; lia])]);
      clear CH0; try clear LNK0
    end.
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
    callxA (eapply (uf_loop_d (Z.to_nat ((TOP - 16 - BP) / 8 + 1)) BP 1 (d + 2) v d) with (ws := upd ws (Z.to_nat 0) (Z_to_bv 64 PC)) (m0 := mx);
            try eassumption; try apply munch_refl; try apply wmono_refl; try lia;
            try (rewrite upd_length; lia);
            pose proof (Z.div_mod (TOP - 16 - BP) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (TOP - 16 - BP) 8 ltac:(lia)); nia)
    end.
    eapply uf_epilogue; try eassumption; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End UnwindFast.

End ARUN_1.
