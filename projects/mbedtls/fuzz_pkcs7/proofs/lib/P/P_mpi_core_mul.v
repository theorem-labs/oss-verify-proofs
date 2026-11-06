(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux MpiWalkAux.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg P_string P_mpi_core_mla.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPMpiTac LxP_SumsArr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P001f0c737d6103e6 0 4 0 1 27 1 47 1 48 1P0171dfc87c238e0c 1 1 4 3 1 1 50 1 51 1 6 2 1 20 4 37 4 49 1 52 1 53 4P0224a3be462a6988 2 23 1 1 4 3 3 1 36 1 37 1 7 0 1 17 4 22 1 29 4 35 1 38 1 39 4 1 1 4 3 2 1 35 1 38 1 4 0 1 36 1 37 1 39 4P044f27d393b2f39a 1 1 4 3 1 1 35 1 36 1 4 2 4 34 4 37 4 38 16P061eb7bd384e992f 1 1 16 2 25 1 47 1 3 0 1 48 1 49 16P071bfe785cb4e04a 1 1 4 3 1 1 50 1 51 1 4 2 1 49 1 52 1 53 4P08078b27bbb3c5af 2 23 1 1 4 3 3 1 36 1 37 1 7 0 1 17 4 22 1 29 4 35 1 38 1 39 4 1 1 4 3 2 1 35 1 38 1 4 0 1 36 1 37 1 39 4P090417af5efe1cc7 1 1 4 3 1 1 50 1 51 1 4 2 4 49 4 52 4 53 16P0a3acf0d88db5af8 1 1 4 2 23 1 47 1 5 0 1 13 4 29 4 48 1 49 4P0abf7fb32296cb9f 1 1 4 4 1 1 42 4 50 1 53 1 5 3 1 33 4 51 1 52 1 54 4P0b77798be160e481 1 1 4 3 1 1 49 1 52 1 5 2 4 32 16 50 4 51 4 53 16P0b87aff3c13ccd13 1 1 4 5 0 1 2 1 20 4 51 1 52 1 2 37 1 53 1P0b970bbcc7b880a8 1 1 4 1 0 1 2 29 1 47 1P0bb4131c7fc9de9e 1 1 4 4 1 1 44 4 51 1 52 1 5 3 1 30 1 50 1 53 1 54 4P0bb5160b72e4dc01 0 3 0 1 15 1 16 1P0bc60aa1a4f3c80d 1 1 4 1 0 1 2 29 1 47 1P0c17620784dfaf81 2 23 1 1 4 3 3 1 36 1 37 1 7 0 1 17 4 22 1 29 4 35 1 38 1 39 4 1 1 4 3 2 1 35 1 38 1 4 0 1 36 1 37 1 39 4P0d06325e668a9e9d 0 4 0 1 27 1 47 1 48 1P0d230120e0a9a701 1 1 4 2 0 1 47 1 4 24 1 30 4 48 1 49 4P0d340ab193c15d77 1 1 4 4 0 1 43 4 49 1 52 1 4 2 1 50 1 51 1 53 4P0d6606acf75953da 1 1 4 2 2 1 50 1 3 1 1 49 1 51 4P0ddea282b5179fbd 1 1 4 2 22 1 32 1 6 0 1 2 4 14 4 26 4 33 1 34 4P0e77559344e1c026 1 1 4 1 0 1 3 28 1 29 1 32 1P0f5d98da38b81639 1 1 4 4 1 1 42 4 51 1 52 1 5 3 1 30 1 50 1 53 1 54 4P10c48105c76627bc 0 5 0 1 2 1 28 4 36 1 37 1P10ca49a9e51a96ee 1 1 4 3 1 1 34 1 37 1 4 2 4 35 4 36 4 38 16P10d40182e6681c8c 1 1 16 2 0 1 47 1 3 8 1 48 1 49 16P11af37986fe3efba 1 1 4 4 1 1 44 4 50 1 53 1 5 3 1 33 4 51 1 52 1 54 4P120a875853ccd2fe 1 1 4 3 1 1 50 1 51 1 5 2 4 32 16 49 4 52 4 53 16P143531099f528315 0 5 0 4 24 4 30 16 47 4 48 4P15efdc2b0b5f2327 0 2 0 1 28 1P1635e046ac957aee 1 1 4 5 0 1 2 1 20 4 51 1 52 1 2 31 1 53 1P165dbb1b40b9230f 1 1 4 2 21 1 47 1 4 0 1 41 4 48 1 49 4P1709ac00ed91c97b 1 1 4 1 0 1 3 28 1 29 1 32 1P18377eff0cdc4bfc 0 4 0 1 20 1 33 1 34 1P18d6dc7fde655697 0 3 0 1 27 1 29 1P1934df51cd75323a 0 2 0 1 17 4P1a0b4f8fdef37094 1 1 4 3 0 1 50 1 51 1 7 2 1 20 4 29 1 31 4 49 1 52 1 53 4P1af53e28aaaf420a 1 1 4 2 0 1 48 1 6 9 1 13 4 29 4 40 4 47 1 49 4P1caafd54430569af 1 1 4 3 0 1 35 1 36 1 6 2 1 21 1 28 4 34 1 37 1 38 4P1cd52e8e065c4863 2 23 1 1 4 3 3 1 36 1 37 1 7 0 1 17 4 22 1 29 4 35 1 38 1 39 4 1 1 4 3 2 1 35 1 38 1 4 0 1 36 1 37 1 39 4P1cedadcc5a644d76 1 1 4 1 0 1 2 29 1 47 1P1e1ddbe1521e6cf6 1 1 4 1 0 1 2 30 1 47 1P1e355c31c77bba77 2 23 1 1 4 3 3 1 36 1 37 1 7 0 1 17 4 22 1 29 4 35 1 38 1 39 4 1 1 4 3 2 1 35 1 38 1 4 0 1 36 1 37 1 39 4P1f2ae019459ce710 0 3 3 1 32 1 33 1P1f4c8b64dfb96e8e 1 1 4 1 0 1 2 30 1 47 1P1f4d7709e7760f94 1 1 4 2 0 1 47 1 4 24 1 30 4 48 1 49 4P1fe48ce190831624 2 23 1 1 4 3 3 1 36 1 37 1 7 0 1 17 4 22 1 29 4 35 1 38 1 39 4 1 1 4 3 2 1 35 1 38 1 4 0 1 36 1 37 1 39 4P206cae7872b8b522 0 2 0 1 17 1P20a0645de9efa0d6 1 1 4 1 0 1 2 17 1 47 1P22a6ce9bebbd6b2f 0 3 0 1 17 4 30 4P22f1346e11b5c17b 2 23 1 1 4 3 3 1 36 1 37 1 7 0 1 17 4 22 1 29 4 35 1 38 1 39 4 1 1 4 3 2 1 35 1 38 1 4 0 1 36 1 37 1 39 4P256cfdbed4b36a28 1 1 4 3 0 1 50 1 53 1 4 3 1 51 1 52 1 54 4P25def47887ed90ff 1 1 4 1 0 1 2 15 1 32 1P263ec428817c2db6 0 5 0 1 17 4 29 4 30 4 36 4P26d1ea1aa83d5b85 0 5 0 1 2 1 43 4 51 1 52 1P26ee902b44cc86a1 1 1 4 2 0 1 47 1 4 16 4 24 1 48 1 49 4P27a61363dbdf2cd5 0 3 0 1 29 1 30 1P284f43a8ae178382 0 4 0 1 29 1 50 1 51 1P29600e8bcda5c0d4 0 4 0 1 15 1 29 1 30 1P29824fedad8b2ee8 1 1 4 1 0 1 3 29 1 36 1 47 1P298d2f7f66f9bdba 0 4 0 1 17 4 29 4 36 4P2bb3c95299d6d9f1 1 1 4 1 0 1 2 28 1 45 1P2c4a4455b185f4ad 1 1 4 3 0 1 51 1 52 1 6 3 1 21 4 32 4 50 1 53 1 54 4P2cfbc548d04801bb 0 4 0 1 17 4 29 4 36 4P2db403fb79121d41 0 2 0 1 2 1P2e117dd8309d3b26 0 2 0 1 28 1P2e9a2aecf789c3ba 1 1 4 2 23 1 47 1 4 0 1 13 4 48 1 49 4P2fae1ff10fe1ed42 1 2 4 2 0 1 48 1 4 2 23 1 47 1 3 13 1 49 1 50 1P2fd0d05db334c3ea 0 3 0 1 27 1 29 1P300d4b063996cb86 0 3 0 1 17 4 30 4P3065d2d3affaef2c 1 1 4 2 19 1 47 1 5 0 1 18 4 35 4 48 1 49 4P316a51b802a40862 1 1 4 3 0 1 51 1 52 1 6 3 1 21 4 32 4 50 1 53 1 54 4P33d54e4bd2c82e5d 1 1 4 2 23 1 33 1 3 0 1 32 1 34 4P35aa51e6667a26c6 1 1 4 3 0 1 50 1 53 1 4 3 1 51 1 52 1 54 4P3641d2794b1171bd 0 6 0 4 24 4 29 16 30 16 47 4 48 4P38af2a1e2395e10b 0 3 0 1 31 1 32 1P39f0bd373c9fe4a0 1 1 4 2 20 1 48 1 3 0 1 47 1 49 4P3c3473548957d597 0 2 0 1 28 1P3c637ea6ca54f48c 1 1 4 1 0 1 4 11 1 27 1 38 1 45 1P3c9800352aa848a8 0 2 0 1 17 1P3eba79f8d067652d 0 3 0 1 14 1 42 1N005ba443cac08d6fN010a7dc8c553df96N016e449af873af31N01baeb8085c89689N01ff2f7d9c8b3ad6N024369029b0a6fedN03522ba5910e880fN04359191439e0f53N057feecf6945168fN06aff6682e1d29efN08271d9c37c9a561N0843786818fd1aabN084aa0a510ec7a93N0963f539c00f3aceN0a22965c42f7f97bN0b60b0caf1539000N0d008750706e5165N0d193bfc3206849aN0d5f1bc955a2fb2fN0defcf93a373a634N0f564b14d01027a1N0fa9f8bdbaf2277cN0fc533e9b9df75efN0fc782f9d5cce352N10c87aee83318174N1114475f5bff2d1bN11265953d2e2b836N1128a037a656448dN114d6a88c8a6606fN12236e947fed3ee5N124e93cf06a1dad4N12e031ce51e18adfN13293aa02b288538N133f6d61c0810e09N136bd93ad8cb9977N137b1126025e5784N1391a12355b626f8N15ebb7c595982742N1606197e836e27b2N1634cfc6344d6ebbN173243c4f9af417fN178045fce0e81a47N17d94fadbb54ef35N17dffe14dd0bc983N18675b9da211489aN1877084e0977e319N18b1b58a6a9097b9N18ccbe16e0743903N1923610695b9b05fN1940cf9f1d81823eN1977bcd93116226bN1a33cc6384284550N1b981edc0ea45f59N1bb33fa9f69eb1b1N1c506381c309cdc4N1c6718d3563c880aN1e86613f4c852acfN1eaaaad67d64fe4bN1f1ec0944a07a384N1f6d3ea8fdc2bf3dN1fab53fe28e56272N2190bc9e1be2bdc8N22383d06fc4c38a5N224a14649fcc7380N227c1c5646ec1564N23748e90efef0c39N23e42a154915f5f5N23f62ceaa3156f15N25e0c0dfeca7724bN2605923247e7fa8aN2825e646e757f30bN28fc89e6229bfb33N298ad7248a85d6cfN29f153ba097c6fb0N2b8991619c828b4eN2c019af4b30e7233N2ca308fefafc6dd0N2cb9a1c232d22056N2dc1f7c08a9e5ffbN2e0a5a12567f0194N2f23f3a006a54a8dN2f6382459205d0edN30073522db35d37aN302cddb6e8997da0N305b0e329014f1d4N316084d22320afe7N323b611f5ad3383eN32c32c8abee558c3N330a85c15fa19062N33507be70f2303a6N33972eec1a0a2c52N33c288ba77559222N33ed409e88726b48N34258b13eb6a5180N34b70a44811f2c0bN34c4a01d578abb31N34dc6e63245e06aeN3538c6582f830c6cN35f3c4fab2b25341N3682305f930e61b9N36e17784396f0f72N3721c7822c001660N372c950f49618726N373eaeb692ddb08bN37c970b80b0be3cbN37d5b7d36442cdeaN3857158f4eeb278aN38ea2543e7c27fb9N396442398ed9d7e9N39662607733b3440N396f9a6c457dcdbaN398d119fad670fe7N39cbcc5a94625f1fN3a0e028c47bc8829N3abc90793f4a4c72N3b672117eeed7ea1N3bda988e0de8bc15N3c51e19434b9164bN3d3f168149fcb58fN3e29b483615bdf08"%lxh.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LiaOrcKlia. (* [comment removed for export] *)
Local Ltac klia ::= orc_klia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_core_mul () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "MPI_CORE_MUL_STACK"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "OSSVerify.KrLib.Lib.Mem.bytes_at"; "OSSVerify.KrLib.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Lib.Exec.evt"; "mpi_core_mul_post"; "Corelib.Init.Peano.le"; "Corelib.Init.Nat.add"; "OSSVerify.KrLib.Lib.MpiCoreAux.same_from"; "Corelib.Init.Datatypes.app"; "Corelib.Lists.ListDef.firstn"; "OSSVerify.KrLib.P.PImg.psegs"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Cells.C8"].



Definition P_MPI_CORE_MUL : Z := 0x22c3c.
Definition MPI_CORE_MUL_STACK : Z := 176.

Definition mpi_core_mul_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X n : Z) (xs : list word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mul ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Lxs',(4.(2.&40.))(5.(6.$0.R12.(7.(8.O17.O16.O15.O14.R11.R10.R?.O13.O12.R>.R=.R<.R;.R:.R9.R8.R7.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R6.R5.R4.R3.)O7.(9.O17.)O6.(:.(2.&40.))R2.(;.O18.)))(5.(<.(=.(>.$?.$?.)(10.$?.$?.O5.(11.O5.(12.+4.O4.)))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.O16.)$15.)(14.&40.O16.))(16.(>.$?.$?.))))O1.R2.)(5.(17.O18.O1.R2.)(5.(18.O18.R2.)(5.(19.O18.R2.O5.R1.)(5.(6.$1:.(1;.(2.&40.)R1.)(1;.(2.&40.)O3.))(5.(6.(4.(2.&40.))(1<.(2.&40.)(1=.O4.)R1.)(1<.(2.&40.)(1=.O4.)O3.))(1>.O18.R2.O2.(14.&40.O16.))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_mul_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mul ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(1?.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PX,$?.PA,$?.Pan,$?.PB,$?.Pbn,$?.Plo,$?.Pxs,(4.(2.&40.))Pys,(4.(2.&40.))Pzs,(4.(2.&40.))P,(19.O2.R:.R9.R3.)P,(20.O2.R;.R9.(21.R3.))P,(20.O2.R<.R8.(21.R3.))P,(22.=R:.)P,(22.=R9.)P,(22.(11.R<.R:.)+2710.)P,(22.(11.R=.R;.)(23.(1;.(2.&40.)R9.)))P,(22.R>.(23.(1;.(2.&40.)R9.)))P,(22.R=.(23.(1;.(2.&40.)R9.)))P,(24.(22.(11.R11.(12.+4.(23.(1;.(2.&40.)R;.))))R12.)(22.(11.R12.(12.+4.(23.(1;.(2.&40.)R<.))))R11.))P,(24.(22.(11.R10.(12.+4.(23.(1;.(2.&40.)R;.))))R13.)(22.(11.R13.(12.+4.(23.(1;.(2.&40.)R=.))))R10.))P,(6.$?.(25.R14.+4.)=)P,(6.$?.(25.R14.+4.)=)P,(6.$?.(25.R13.+4.)=)P,(26.=R17.)P,(24.(6.$?.R16.=)(26.=R17.))P,(24.(6.$?.R15.=)(26.=R16.))P,(26.(11.R1:.(12.+4.(23.(1;.(2.&40.)R14.))))(27.+2.+40.))P,(26.(11.R1:.(12.+4.(23.(1;.(2.&40.)R14.))))(27.+2.+40.))P,(26.(11.R19.(12.+4.(23.(1;.(2.&40.)R14.))))(27.+2.+40.))P,(1>.O2.R1>.R18.(14.&40.R3>.))P,(22.R19.(13.(14.&40.R3?.)$15.))P,(6.$?.(25.(14.&40.R40.)+10.)=)P,(24.(22.(11.R20.(12.+4.(23.(1;.(2.&40.)R1:.))))R1;.)(22.(14.&40.R41.)R20.))P,(24.(22.(11.R20.(12.+4.(23.(1;.(2.&40.)R1:.))))R1<.)(22.(14.&40.R42.)R20.))P,(24.(22.(11.R1?.(12.+4.(23.(1;.(2.&40.)R1:.))))R1=.)(22.(14.&40.R43.)R1?.))P,(18.O2.R24.)P,(6.$?.(25.(14.&40.R46.)+2.)=)P,(6.(2.&40.)R3>.(28.&40.R25.))P,(6.(2.&40.)R3>.(28.&40.R25.))P,(6.(2.&40.)R3>.(28.&40.R25.))P,(6.(2.&40.)R3>.(28.&40.R25.))P,(6.(2.&40.)R3>.(28.&40.R25.))(29.O2.(2:.O2.R4<.R4;.R4:.R49.R45.R44.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R2=.R2<.R2:.(11.R28.R26.)R24.R25.R2;.)(7.(8.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.)R2=.(28.&40.O1.)R2<.(:.(2.&40.))R2;.(;.O2.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L11066734223.13L17187524197.13L17412818593.13L24204441423.13L51288638096.13L67085962724.1300000M00j01G01d02A02^S1i1k1n2xs3ds'1L3Hik1q2Hq3HltS1i1k1n2xs3ds'1L3Hik1q2Hq3HltS1i1k1n2xs3ds'1L3Hik1q2Hq3HgeS1i1k1n2xs3ds'1L3Hik1q2Hq3HltS1i1k1n2xs3ds'1L3Hik1q2Hq3HltS1i1k1n2xs3ds'1L3Hik1q2Hq3Hge". (* [comment removed for export] *)
Lemma same_from_mla : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mul ()) "Pi,$1:.Pk,$1:.Pn,$1:.Pxs,(4.(2.&40.))Pds',(4.(2.&40.))Pxs0,(4.(2.&40.))P,(6.$1:.(1;.(2.&40.)R2.)(1;.(2.&40.)(1<.(2.&40.)R6.R3.)))P,(6.(4.(2.&40.))(1<.(2.&40.)R6.R3.)(1<.(2.&40.)R6.(1<.(2.&40.)R7.R4.)))P,(2;.(2<.R8.R7.)R6.)P,(2=.(2.&40.)R7.R6.R4.)(2=.(2.&40.)R8.(2>.(2.&40.)(2?.(2.&40.)R:.R7.)R6.)R5.)")
(* [comment removed for export] *).
Proof.
  intros i k n xs ds' xs0 L SK Hik FS q Hq.
  destruct (Nat.lt_ge_cases q (length xs)) as [Hlt|Hge].
  - rewrite nth_error_app2 by (rewrite firstn_length; lia). rewrite firstn_length, Nat.min_l by lia.
    rewrite <- (FS q Hq). transitivity (nth_error (skipn k ds') (q - i - k)).
    { rewrite nth_error_skipn. f_equal. lia. }
    rewrite SK, !nth_error_skipn. f_equal. lia.
  - rewrite <- (FS q Hq). rewrite (proj2 (nth_error_None xs q)) by lia. apply nth_error_None.
    rewrite app_length, firstn_length, L, skipn_length. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac mul_dinv_tac X n m lo sp W :=
  let mx := lx_cur_mem in
  lazymatch goal with Hu : u32arr _ mx X ?l |- _ =>
  lazymatch goal with Hl : Z.of_nat (length l) = _ |- _ =>
  lazymatch goal with Hm : munch _ m mx |- _ =>
  lazymatch goal with Hw : wmono _ m mx |- _ =>
  lazymatch goal with Hi' : mem_inv _ mx |- _ =>
  lazymatch goal with Hs : stk _ mx lo _ |- _ =>
    assert (DI' : u32arr psegs mx X l /\ Z.of_nat (length l) = n
                  /\ munch W m mx /\ wmono psegs m mx /\ mem_inv psegs mx /\ stk psegs mx lo (bv_unsigned sp + -64));
    [split; [exact Hu| split; [rewrite ?upd_length; first [exact Hl | assumption | rewrite Hl; assumption | etransitivity; [exact Hl|]; assumption] | split; [first [exact Hm | eapply munch_weaken; [|exact Hm]; intros x Hx; cbn [outside] in *; clear -Hx; lia]
      | split; [exact Hw| split; [exact Hi'| exact Hs]]]]] |]
  end end end end end end.

Section Walk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X A an B bn lx la lb lo : Z) (xs0 ys zs : list word) (junk : list byte).
  Hypothesis Han : 0 <= an /\ 0 <= bn /\ an + bn <= 10000.
  Hypothesis Ln : an + bn <= lx /\ an <= la /\ bn <= lb.
  Hypothesis L0 : Z.of_nat (length xs0) = lx.
  Hypothesis LA : Z.of_nat (length ys) = la.
  Hypothesis LB : Z.of_nat (length zs) = lb.
  Hypothesis DA : A + 4 * la <= X \/ X + 4 * lx <= A.
  Hypothesis DB : B + 4 * lb <= X \/ X + 4 * lx <= B.
  Hypothesis XB : 0 < X /\ X + 4 * lx < 2^64.
  Hypothesis AB : 0 <= A /\ A + 4 * la < 2^64.
  Hypothesis BB : 0 <= B /\ B + 4 * lb < 2^64.
  Hypothesis NZA : an <= 0 \/ 1 <= A.
  Hypothesis NZB : bn <= 0 \/ 1 <= B.
  Hypothesis ALX : X mod 4 = 0.
  Hypothesis ALA : A mod 4 = 0.
  Hypothesis ALB : B mod 4 = 0.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis LO : 0 <= lo <= bv_unsigned sp - 176.
  Hypothesis SX : X + 4 * lx <= lo \/ bv_unsigned sp <= X.
  Hypothesis SA : A + 4 * la <= lo \/ bv_unsigned sp <= A.
  Hypothesis SBB : B + 4 * lb <= lo \/ bv_unsigned sp <= B.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  (* [comment removed for export] *)
  Hypothesis HA0 : bytes_at psegs m A (u32s ys).
  Hypothesis HB0 : bytes_at psegs m B (u32s zs).
  (* [comment removed for export] *)
  Hypothesis HXhi : u32arr psegs m (X + 4 * (an + bn)) (skipn (Z.to_nat (an + bn)) xs0).

  Notation POST := (mpi_core_mul_post psegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X (an + bn) xs0 lo m).
  Notation W := [(X, X + 4 * (an + bn)); (bv_unsigned sp - 176, bv_unsigned sp)].
  Notation FRAME mm := (rw_cells psegs mm (bv_unsigned sp + -64) [CB 8 junk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  (* [comment removed for export] *)
  Notation DINV mm xs := (u32arr psegs mm X xs /\ Z.of_nat (length xs) = an + bn
                          /\ munch W m mm /\ wmono psegs m mm /\ mem_inv psegs mm /\ stk psegs mm lo (bv_unsigned sp + -64)).

  Ltac mul_dinv := mul_dinv_tac X constr:(an + bn) m lo sp constr:(W).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L35876709422.5 L36962904668.11L58790393654.5 L59904178890.5 L6330159503.14 00000B00g01501E021S2an2bn3Han3xs'2LXS2an2bn2lx2la2lb3xs03Han2Ln2L03xs'2LXS2an2bn3xs'2LXS1X2an2bn3xs'2LXS2sp1X2an2bn2lx2la2lb2lo3xs03Han2Ln2L02LO2SX". (* [comment removed for export] *)
  Lemma fin_post : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mul ()) "Pm',P,(2.&40.)(3.(2.&8.))Pxs',(4.(2.&40.))Pyt0,(2.&40.)Pyt1,(2.&40.)Pyt2,(2.&40.)Pya0,(2.&40.)Pya1,(2.&40.)Pya2,(2.&40.)Pya3,(2.&40.)Pya4,(2.&40.)Pya5,(2.&40.)Pya6,(2.&40.)Pya7,(2.&40.)Pyt3,(2.&40.)Pyt4,(2.&40.)Pyt5,(2.&40.)Pyt6,(2.&40.)P,(<.(=.(>.$?.$?.)(10.$?.$?.VX,(11.VX,(12.+4.(11.Van,Vbn,))))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.Vsp,)+;0.)(14.&40.Vsp,))(16.(>.$?.$?.))))Vm,R11.)P,(17.$30.Vm,R12.)P,(18.$30.R13.)P,(1>.$30.R14.Vlo,(14.&40.Vsp,))P,(19.$30.R15.VX,R14.)P,(6.$?.(23.(1;.(2.&40.)R15.))(11.Van,Vbn,))(2:.$30.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,(11.Van,Vbn,)Vxs0,Vlo,Vm,(7.(8.Vra,Vsp,Vgp,Vtp,R15.R14.R13.Vs0,Vs1,R12.R11.R10.R?.R>.R=.R<.R;.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(9.Vra,)Vfc,(:.(2.&40.))R17.(;.$30.)))")
(* [comment removed for export] *).
  Proof.
    intros until yt6. intros MU WM MI ST HX LX.
    unfold mpi_core_mul_post, MPI_CORE_MUL_STACK.
    flexi 16%nat. exists (xs' ++ skipn (Z.to_nat (an + bn)) xs0). split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    split. { apply u32arr_app. split; [exact HX|]. replace (X + 4 * Z.of_nat (length xs')) with (X + 4 * (an + bn)) by xlia LX.
             eapply u32arr_transport; [exact HXhi | exact MU | exact WM |]. cbn [disjoint_from]. rewrite skipn_length. clear -Han Ln L0 SX LO. lia. }
    split. { rewrite app_length, skipn_length. xlia LX L0 Ln Han. }
    split. { rewrite skipn_app, skipn_all2 by xlia LX Han. replace (Z.to_nat (an + bn) - length xs')%nat with 0%nat by xlia LX Han. reflexivity. }
    exact ST.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac mul_ret :=
    try rewrite (Z_to_bv_bv_unsigned sp); first [ apply evt_done | idtac ];
    let mx := lx_cur_mem in
    lazymatch goal with Hu : u32arr _ mx X ?l |- _ =>
    lazymatch goal with Hl : Z.of_nat (length l) = _ |- _ =>
    lazymatch goal with Hm : munch _ m mx |- _ =>
    lazymatch goal with Hw : wmono _ m mx |- _ =>
    lazymatch goal with Hi' : mem_inv _ mx |- _ =>
    lazymatch goal with Hs : stk _ mx lo (bv_unsigned sp) |- _ =>
      eapply (fin_post mx l);
      [ first [exact Hm | eapply munch_weaken; [|exact Hm]; intros x Hx; cbn [outside] in *; clear -Hx; lia]
      | exact Hw | exact Hi' | exact Hs | exact Hu
      | rewrite ?upd_length; first [exact Hl | assumption | rewrite Hl; assumption | etransitivity; [exact Hl|]; assumption] ]
    end end end end end end.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0080@L18575561859.16 L19150057859.2  L47252709405.5  L49849035919.2  L51209438901.16 L57628700040.6  L59308586248.4  M20904411576.12300000Z00_00m01201[01l02802DS2sp1X2an1B2bn2lx2la2lb2lo2zs2Ln2DB2LO3SBBS1X1iS2bn1k1i2Hk2HiS1B1iS2sp1X1A2an2bn2lx2la2lb2lo2ys2Ln2DA2LO2SAS2sp1X2an2bn1x2HxS2bn1i2Hk2HiS2bn1i2Hi2H4". (* [comment removed for export] *)
  Lemma loop_walk : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_mul ()) "Pk,$1:.Pi,$?.Pxs,(4.(2.&40.))Pmm,P,(2.&40.)(3.(2.&8.))Pxra,(2.&40.)Pxt0,(2.&40.)Pxt1,(2.&40.)Pxt2,(2.&40.)Pxa0,(2.&40.)Pxa1,(2.&40.)Pxa2,(2.&40.)Pxa3,(2.&40.)Pxa4,(2.&40.)Pxa5,(2.&40.)Pxa6,(2.&40.)Pxa7,(2.&40.)Pxt3,(2.&40.)Pxt4,(2.&40.)Pxt5,(2.&40.)Pxt6,(2.&40.)Pwpb,(2.&40.)Pwpx,(2.&40.)Pwe,(2.&40.)Pw4,(2.&40.)P,(6.$1:.(1=.(13.Vbn,R17.))R18.)P,(5.(22.=R18.)(26.R18.Vbn,))P,(6.(2.&40.)R6.(28.&40.(11.VB,(12.+4.R19.))))P,(6.(2.&40.)R6.(28.&40.(11.VX,(12.+4.R1:.))))P,(6.(2.&40.)R6.(28.&40.(11.VB,(12.+4.Vbn,))))P,(6.(2.&40.)R6.(28.&40.(11.Van,+1.)))P,(5.(19.$30.R1;.VX,R1<.)(5.(6.$?.(23.(1;.(2.&40.)R1<.))(11.Van,Vbn,))(5.(<.(=.(>.$?.$?.)(10.$?.$?.VX,(11.VX,(12.+4.(11.Van,Vbn,))))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.Vsp,)+;0.)(14.&40.Vsp,))(16.(>.$?.$?.))))Vm,R1;.)(5.(17.$30.Vm,R1;.)(5.(18.$30.R1;.)(1>.$30.R1;.Vlo,(11.(14.&40.Vsp,)-40.)))))))P,(31.$30.R1<.(11.(14.&40.Vsp,)-40.)(=.$32.(33.#8.Vjunk,)(=.$32.(34.Vs5,)(=.$32.(34.Vs4,)(=.$32.(34.Vs3,)(=.$32.(34.Vs2,)(=.$32.(34.Vs1,)(=.$32.(34.Vs0,)(=.$32.(34.Vra,)(16.$32.))))))))))(29.$30.(2:.$30.Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,VX,(11.Van,Vbn,)Vxs0,Vlo,Vm,)(7.(8.R1<.(28.&40.(11.(14.&40.Vsp,)-40.))Vgp,Vtp,R1;.R1:.R19.R<.(28.&40.Van,)R18.R17.R16.R15.R14.R13.R12.R11.(28.&40.VA,)R;.R9.R:.Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R10.R?.R>.R=.)VF,(28.&40.+22<90.)Vfc,(:.(2.&40.))R1=.(;.$30.)))")
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i xs mm xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 wpb wpx we w4 Hk Hi -> -> -> ->
      (HX & LX & MU & WM & MI & ST) FR; [exfalso; xlia Hk Hi|].
    pose proof (u32ro_transport _ _ _ _ _ _ HB0 MU ltac:(cbn [disjoint_from]; rewrite LB; clear -Han Ln LB DB SBB LO; lia)) as HB.
    pose proof (u32ro_transport _ _ _ _ _ _ HA0 MU ltac:(cbn [disjoint_from]; rewrite LA; clear -Han Ln LA DA SA LO; lia)) as HA.
    pose proof (sumsarr_ok [X]) as LXSUMS.
    lx_run_tac (PLANS [0x22c90] [] 60%N SUMSARR); lx_tree.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 0x22c90) _ _ _ _) =>
             mul_dinv; eapply (IH (i + 1)); [xlia Hk Hi | klia | f_equal; xlia0 | f_equal; xlia0 | f_equal; xlia0 | f_equal; xlia0 | exact DI' | assumption]
         | |- _ => mul_ret
         end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Local Ltac2 Set LiaOrc.tbl := fun () => "00J0@L17646078182.77 L40809331205.4  L42753029872.6  L43061838864.75 L57628700040.6  L59904178890.7  L8918007599.4   M21516638002.117M28131417803.117M29308210991.117M31127766590.117M320818155.115  M3229439818.117 M35186828887.117M37456913856.117M41713521204.115M41715690921.117M43287135843.117M43289311742.115M50954204102.117M50956094555.115M56527448794.117M58437184390.117M60291254327.117M63188472851.117M6653323451.117 00000P00Z00o01U01f02=02G02N02O02P02\02o03;03<03C03U03g04:04M04f05?05L05M05P05S05TS2ra2sp1X1A2an1B2bn2xs2ys2zs3SPRS1B2bn3NZBS2an2bn2xs3Han3Hbn2LXS2ra2sp1X1A2an1B2bn2lo2xs2ys2zs2LO3SPRS2sp1X2an2bn1x2HxS1X2an2bn2xs3Han3Hbn2LXS1A2an3NZAS2bn2H2FFS1B2zs2BT2BBS2sp1X2lo2xs2SX3SPRS1A2ys2AT2ABFS2bn2H2S2sp2lo2LO3SPR3LO0S2sp2lo2LO3SPR3LO0S2an2bn3Han3Hbn3HabS2an2bn3Han3Hbn3HabS2an2bn2xs2ys2zs2LX2LA2LBS2an2bn2xs2ys2zs2LX2LA2LBS1X2xs3NZX2XTFS1XS1BF". (* [comment removed for export] *)
Lemma P_mpi_core_mul_spec : mpi_core_mul_stmt psegs P_MPI_CORE_MUL.
Proof.
  unfold mpi_core_mul_stmt, P_MPI_CORE_MUL.
  intros until zs. intros HX HA HB Han Hbn Hab LX LA LB DA DB ALX ALA ALB NZX NZA NZB XT AT BT ST LO SPA SX SA SB MI RA -> -> -> -> ->.
  unfold MPI_CORE_MUL_STACK in *.
  pose proof (u32arr_bound _ _ _ _ HX) as XB. pose proof (u32ro_bound _ _ _ _ HA) as AB. pose proof (u32ro_bound _ _ _ _ HB) as BB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (LO0 : 0 <= lo) by ((flat constr:(ST) 2%nat; flclear ST; intros ? _); assumption).
  assert (NZA' : an <= 0 \/ 1 <= A) by (clear -NZA Han; lia). assert (NZB' : bn <= 0 \/ 1 <= B) by (clear -NZB Hbn; lia). clear NZA NZB.
  pose proof (munch_refl [(X, X + 4 * (an + bn)); (bv_unsigned sp - 176, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  (* [comment removed for export] *)
  rewrite <- (firstn_skipn (Z.to_nat (an + bn)) xs) in HX. apply u32arr_app in HX. flat constr:(HX) 2%nat. flclear HX. intros HXlo HXhi.
  rewrite firstn_length in HXhi. replace (X + 4 * Z.of_nat (Nat.min (Z.to_nat (an + bn)) (length xs))) with (X + 4 * (an + bn)) in HXhi by xlia LX Han Hbn.
  assert (LXlo : Z.of_nat (length (firstn (Z.to_nat (an + bn)) xs)) = an + bn) by (rewrite firstn_length; xlia LX Han Hbn).
  pose proof (lock HXhi) as HXhi'. pose proof (lock HA) as HA'. pose proof (lock HB) as HB'. clear HXhi HA HB.
  carve_frame 64%nat ST. lxp_split_frame [8;8;8;8;8;8;8;8]%nat.
  pose proof (sumsarr_ok [X]) as LXSUMS.
  lx_run_tac (PLANS [0x22c90] [] 40%N SUMSARR); lx_tree.
  all: lxp_unjunk.
  all: lazymatch goal with
       | |- evt _ _ (MS _ _ (Z_to_bv 64 0x22c90) _ _ _ _) =>
         mul_dinv_tac X constr:(an + bn) m lo sp constr:([(X, X + 4 * (an + bn)); (bv_unsigned sp - 176, bv_unsigned sp)]);
         eapply (@loop_walk) with (k := Z.to_nat bn) (i := 0) (A := A) (B := B) (lx := Z.of_nat (length xs)) (la := Z.of_nat (length ys))
             (lb := Z.of_nat (length zs)) (ys := ys) (zs := zs) (xs0 := xs);
           try eassumption; try reflexivity; try klia; try (f_equal; klia);
         first [exact (unlock _ HA') | exact (unlock _ HB') | exact (unlock _ HXhi') | idtac]
       | |- _ =>
         (* [comment removed for export] *)
         try rewrite (Z_to_bv_bv_unsigned sp); first [ apply evt_done | idtac ];
         let mx := lx_cur_mem in let xX := constr:(X) in let xm := constr:(m) in let xlo := constr:(lo) in let xsp := constr:(sp) in
         lazymatch goal with Hu : u32arr _ mx xX ?l |- _ =>
         lazymatch goal with Hl : Z.of_nat (length l) = _ |- _ =>
         lazymatch goal with Hm : munch _ xm mx |- _ =>
         lazymatch goal with Hw : wmono _ xm mx |- _ =>
         lazymatch goal with Hi' : mem_inv _ mx |- _ =>
         lazymatch goal with Hs : stk _ mx xlo (bv_unsigned xsp) |- _ =>
           eapply fin_post with (lx := Z.of_nat (length xs)) (la := Z.of_nat (length ys)) (lb := Z.of_nat (length zs)) (xs0 := xs);
           first [ exact Hw | exact Hi' | exact Hs | exact Hu | exact (unlock _ HXhi') | exact eq_refl
                 | eapply munch_weaken; [|exact Hm]; intros x Hx; cbn [outside] in *; clear -Hx; lia
                 | rewrite Hl; exact LXlo | klia ]
         end end end end end end
       end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
