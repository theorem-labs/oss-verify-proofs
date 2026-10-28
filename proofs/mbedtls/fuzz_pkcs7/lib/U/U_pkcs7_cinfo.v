(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux X509Aux AStep CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sums2.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0069efeb3995cb69 0 1 1 1P0144280da92fba53 0 2 0 1 3 1P03151bf13898fc17 1 1 8 3 0 1 40 1 43 1 4 2 2 41 2 42 2 44 16P043e788ae0c652de 2 18 1 1 8 3 2 1 32 1 33 1 5 0 2 20 2 31 2 34 2 35 16 1 1 8 3 1 1 31 1 34 1 4 0 2 32 2 33 2 35 16P04c829664a1fccf7 0 2 0 1 1 1P0511467211debeb2 2 35 1 1 8 3 1 1 50 1 51 1 5 0 2 38 2 49 2 52 2 53 16 1 1 8 3 2 1 49 1 52 1 4 0 2 50 2 51 2 53 16P05d15ffa222f7dc0 2 19 1 1 8 3 2 1 32 1 33 1 5 0 2 20 2 31 2 34 2 35 16 1 1 8 3 1 1 31 1 34 1 4 0 2 32 2 33 2 35 16P06457d3752d28717 2 18 1 1 8 3 2 1 32 1 33 1 5 0 2 20 2 31 2 34 2 35 16 1 1 8 3 1 1 31 1 34 1 4 0 2 32 2 33 2 35 16P068d34ce08bbb312 2 16 0 5 0 1 3 1 21 1 32 1 33 1 0 4 0 1 2 1 32 1 33 1P06e28874cf4cc307 0 2 0 1 19 1P07fd5ab0ec3254a1 2 37 1 1 8 3 1 1 48 1 49 1 5 0 2 36 2 47 2 50 2 51 16 1 1 8 3 2 1 47 1 50 1 4 0 2 48 2 49 2 51 16P08f60847406be033 1 1 8 3 0 1 41 1 42 1 5 2 2 29 2 40 2 43 2 44 16P090aed44324d6d98 0 2 0 1 1 1P0917f3743536aaa9 1 1 8 3 0 1 32 1 33 1 5 2 2 20 2 31 2 34 2 35 16P0aff9f396a5535d0 1 1 8 2 31 1 39 1 3 0 1 38 1 40 8P0b58ab9edaea0218 0 2 0 1 7 1P0bfdc2e5cd9f3049 0 4 0 1 2 1 33 1 34 1P0c204ad17efc29ab 0 2 0 1 5 1P0c4b2ea5551be8e1 0 2 0 1 1 1P0c7f1b15517d4a3c 0 4 0 1 34 1 45 1 46 1P0ca1d629363a2c00 2 37 1 1 8 3 1 1 50 1 51 1 5 0 2 38 2 49 2 52 2 53 16 1 1 8 3 2 1 49 1 52 1 4 0 2 50 2 51 2 53 16P0fe6eea8df5505d9 0 2 0 1 32 1P1054f904af1b328d 0 4 0 1 2 1 42 1 43 1P115058665346649e 0 5 1 1 2 1 29 1 40 1 41 1P12a4dec29e72bb84 2 18 1 1 8 3 2 1 32 1 33 1 5 0 2 20 2 31 2 34 2 35 16 1 1 8 3 1 1 31 1 34 1 4 0 2 32 2 33 2 35 16P134e4ed02b95f2d7 1 1 8 3 0 1 31 1 34 1 4 2 2 32 2 33 2 35 16P13685445e8cef0a3 2 17 1 1 8 3 2 1 32 1 33 1 5 0 2 20 2 31 2 34 2 35 16 1 1 8 3 1 1 31 1 34 1 4 0 2 32 2 33 2 35 16P13b9c09dbac709d4 0 5 1 1 2 1 20 1 31 1 32 1P14212e48a1d99808 1 1 8 3 0 1 31 1 34 1 4 2 2 32 2 33 2 35 16P15269f1633de39f0 2 35 1 1 8 3 1 1 50 1 51 1 5 0 2 38 2 49 2 52 2 53 16 1 1 8 3 2 1 49 1 52 1 4 0 2 50 2 51 2 53 16P1526a1d7d181422d 1 1 8 3 1 1 41 1 42 1 5 2 2 29 2 40 2 43 2 44 16P157b27bdb7ff98d3 2 17 1 1 8 3 2 1 32 1 33 1 5 0 2 20 2 31 2 34 2 35 16 1 1 8 3 1 1 31 1 34 1 4 0 2 32 2 33 2 35 16P15c32675a8fb36fa 0 4 0 1 25 1 36 1 37 1P162bc9d95b7bcbc9 0 3 0 1 4 1 33 1P169ab1c492ecfd7d 0 2 0 1 28 1P17230f090279d6ac 1 1 8 3 1 1 41 1 42 1 5 2 2 29 2 40 2 43 2 44 16P17a5b6db81a6dc0c 1 1 8 3 0 1 41 1 42 1 5 2 2 29 2 40 2 43 2 44 16P197df4c96d9888f1 0 4 0 1 36 1 47 1 48 1P197e695649ce9339 2 16 0 5 0 1 3 1 21 1 32 1 33 1 0 4 0 1 2 1 32 1 33 1P199a51798e238aea 0 2 0 1 7 1P1a179b4044cf0c00 0 4 0 1 25 1 36 1 37 1P1a7e2b001abff97f 1 1 16 4 16 1 17 1 18 1 30 1 3 0 1 29 1 31 16P1ace7fe48088257c 0 3 0 1 5 1 35 1P1bef7e2a08a50701 0 2 0 1 5 1P1d13b2b073fb9fad 2 19 1 1 8 3 2 1 32 1 33 1 5 0 2 20 2 31 2 34 2 35 16 1 1 8 3 1 1 31 1 34 1 4 0 2 32 2 33 2 35 16P1d83b11c463d28f5 1 1 8 2 22 1 30 1 3 0 1 29 1 31 8P1d9aea5646b2c4b3 0 5 1 1 3 1 21 1 32 1 33 1P1dfe5b3399f320e6 0 2 0 1 25 1P1ef5bf1748684918 2 19 1 1 8 3 2 1 32 1 33 1 5 0 2 20 2 31 2 34 2 35 16 1 1 8 3 1 1 31 1 34 1 4 0 2 32 2 33 2 35 16P1f3bbab5c6898480 2 37 1 1 8 3 1 1 50 1 51 1 5 0 2 38 2 49 2 52 2 53 16 1 1 8 3 2 1 49 1 52 1 4 0 2 50 2 51 2 53 16P209a40e4f54aa0d1 0 2 0 1 1 1P20da601efb1c3bf7 1 1 8 3 1 1 40 1 43 1 4 2 2 41 2 42 2 44 16P21c1dc04cf1c9703 0 4 0 1 2 1 31 1 32 1P22a866dc8de9cfea 1 1 8 3 1 1 31 1 34 1 4 2 2 32 2 33 2 35 16P23567eeebbfac5b4 2 35 1 1 8 3 1 1 50 1 51 1 5 0 2 38 2 49 2 52 2 53 16 1 1 8 3 2 1 49 1 52 1 4 0 2 50 2 51 2 53 16P24b131ea8a909271 0 4 0 1 36 1 47 1 48 1P2670890fb6e9ecba 2 27 1 1 8 3 1 1 41 1 42 1 5 0 2 29 2 40 2 43 2 44 16 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P268b51ff8d356753 0 2 0 1 23 1P272bf1100216b8f9 0 2 0 1 24 1P278aea2739ab3b15 1 1 8 3 1 1 32 1 33 1 4 2 2 31 2 34 2 35 16P27bfaec0a55ff2cd 2 35 1 1 8 3 1 1 50 1 51 1 5 0 2 38 2 49 2 52 2 53 16 1 1 8 3 2 1 49 1 52 1 4 0 2 50 2 51 2 53 16P27e7c3a6dda31713 2 16 0 5 0 1 3 1 21 1 32 1 33 1 0 4 0 1 2 1 32 1 33 1P29a89991bc3bf659 0 2 0 1 5 1P29b9c2927326e276 2 17 1 1 8 3 2 1 32 1 33 1 5 0 2 20 2 31 2 34 2 35 16 1 1 8 3 1 1 31 1 34 1 4 0 2 32 2 33 2 35 16P2a3650684a77d55b 0 2 0 1 5 1P2a65d97515fc51b7 2 18 1 1 8 3 2 1 32 1 33 1 5 0 2 20 2 31 2 34 2 35 16 1 1 8 3 1 1 31 1 34 1 4 0 2 32 2 33 2 35 16P2c08771e728fbd23 0 2 0 1 26 1P2cdfff2203ff9b03 2 17 1 1 8 3 2 1 32 1 33 1 5 0 2 20 2 31 2 34 2 35 16 1 1 8 3 1 1 31 1 34 1 4 0 2 32 2 33 2 35 16P2da4509008737823 1 1 16 4 25 1 26 1 27 1 39 1 3 0 1 38 1 40 16P2e7c980673113c4c 2 37 1 1 8 3 1 1 48 1 49 1 5 0 2 36 2 47 2 50 2 51 16 1 1 8 3 2 1 47 1 50 1 4 0 2 48 2 49 2 51 16P2ebc8fdf768f5787 2 16 0 5 0 1 3 1 21 1 32 1 33 1 0 4 0 1 2 1 32 1 33 1P2eea9a817be2d805 0 4 0 1 34 1 45 1 46 1P2f4cc0fff53d5ebe 2 19 1 1 8 3 2 1 32 1 33 1 5 0 2 20 2 31 2 34 2 35 16 1 1 8 3 1 1 31 1 34 1 4 0 2 32 2 33 2 35 16P2f87af91c4b5c2de 2 27 1 1 8 3 1 1 41 1 42 1 5 0 2 29 2 40 2 43 2 44 16 1 1 8 3 2 1 40 1 43 1 4 0 2 41 2 42 2 44 16P2fc531a41795f744 1 1 8 3 1 1 41 1 42 1 4 2 2 40 2 43 2 44 16P3011dc0cad75f027 0 2 0 1 5 1P3206ac3d50685dfe 1 1 8 3 1 1 40 1 43 1 4 2 2 41 2 42 2 44 16P320ab72fd525d13f 0 2 0 1 6 1P329b8d92fb806eea 1 1 8 3 0 1 32 1 33 1 5 2 2 20 2 31 2 34 2 35 16P32b5e46045406ca4 1 1 8 3 1 1 31 1 34 1 4 2 2 32 2 33 2 35 16P32fde7eff29cca17 0 4 0 1 2 1 40 1 41 1P3345f7720dbdb4ea 2 35 1 1 8 3 1 1 50 1 51 1 5 0 2 38 2 49 2 52 2 53 16 1 1 8 3 2 1 49 1 52 1 4 0 2 50 2 51 2 53 16P33732b494c58d3f3 0 5 1 1 3 1 30 1 41 1 42 1P33deea29cf8e435b 2 19 1 1 8 3 2 1 32 1 33 1 5 0 2 20 2 31 2 34 2 35 16 1 1 8 3 1 1 31 1 34 1 4 0 2 32 2 33 2 35 16P34f33e6fe2f93aa3 0 2 0 1 5 1P3527b4b9c9d4aaa8 1 1 8 3 1 1 32 1 33 1 5 2 2 20 2 31 2 34 2 35 16P366fe7ae7c6ae5a3 0 1 1 1P36f489b85a61a485 1 1 8 3 1 1 32 1 33 1 5 2 2 20 2 31 2 34 2 35 16P382888f2bae3da2d 2 18 1 1 8 3 2 1 32 1 33 1 5 0 2 20 2 31 2 34 2 35 16 1 1 8 3 1 1 31 1 34 1 4 0 2 32 2 33 2 35 16P393210e9457f467b 2 16 0 5 0 1 3 1 21 1 32 1 33 1 0 4 0 1 2 1 32 1 33 1P39ac6c18d15292e5 2 28 1 1 8 3 1 1 39 1 40 1 5 0 2 27 2 38 2 41 2 42 16 1 1 8 3 2 1 38 1 41 1 4 0 2 39 2 40 2 42 16P39b9d718181f0d5a 0 4 0 1 3 1 41 1 42 1P3b4148679cc2b012 2 16 0 5 0 1 3 1 21 1 32 1 33 1 0 4 0 1 2 1 32 1 33 1P3c04c4f7c3a50446 0 2 0 1 6 1P3c1ee42e123d862b 2 18 1 1 8 3 2 1 32 1 33 1 5 0 2 20 2 31 2 34 2 35 16 1 1 8 3 1 1 31 1 34 1 4 0 2 32 2 33 2 35 16P3d6e1ebd3a6abd8e 2 17 1 1 8 3 2 1 32 1 33 1 5 0 2 20 2 31 2 34 2 35 16 1 1 8 3 1 1 31 1 34 1 4 0 2 32 2 33 2 35 16P3d7371cf44e5ca61 1 1 8 3 0 1 40 1 43 1 4 2 2 41 2 42 2 44 16P3d817611a8cb9d1a 2 17 1 1 8 3 2 1 32 1 33 1 5 0 2 20 2 31 2 34 2 35 16 1 1 8 3 1 1 31 1 34 1 4 0 2 32 2 33 2 35 16P3e73c201c3597710 2 28 1 1 8 3 1 1 39 1 40 1 5 0 2 27 2 38 2 41 2 42 16 1 1 8 3 2 1 38 1 41 1 4 0 2 39 2 40 2 42 16P3e9b8ed3f47c1fc2 2 35 1 1 8 3 1 1 50 1 51 1 5 0 2 38 2 49 2 52 2 53 16 1 1 8 3 2 1 49 1 52 1 4 0 2 50 2 51 2 53 16P3f1f53a4973a5eaa 0 4 0 1 3 1 32 1 33 1P3fc2ae8012f19016 2 19 1 1 8 3 2 1 32 1 33 1 5 0 2 20 2 31 2 34 2 35 16 1 1 8 3 1 1 31 1 34 1 4 0 2 32 2 33 2 35 16N0021d6a000f3df06N009485c2cd62bba7N00c70c65db201b6dN00f23ccce6d26703N010ca345b84eacbaN01e0c3bdcc087f4cN0206ee8c107bdcddN021121aefee3c5aaN02d86985b8e197ebN037669490ccdb97bN03a336cdd75334efN03c5fb77c39f05d1N04130d246f64c7cbN0421e84577d0d746N043e0c5ff832b46bN044267a02af1aaedN045b42a6057e36f6N0476e4b98ffd81fcN0535a61653117c00N0562aea3c279c53cN05c6a704c596abf3N05e61e01b75afca1N05fe0855b6c0423eN072a68e603785262N07a089171959cccfN086041994896b776N09a4a0cc6c4ede46N09b8442b19cd170cN0aadb2a0d231d30fN0b0bb64014863517N0ba4259a7b04d0d4N0bb49ad17690dd9eN0bf531bc615e1785N0c201b757270e6bbN0c61bea869578266N0e39240f85ce4d74N0e593c2f26daac12N0e760be99ba139eeN0e87d1966df2b932N0f52ad5cbfb439f3N0f64feefeb8af774N0fb5c1b992ad9933N0fc9040b1cfe1d2dN10d5790db4e88cf0N114ae1f44f28832cN11816d1f976dd486N1222029e39bbbdb7N1259fcc0b1a1b48aN13253d1e8f10fff3N13741b83e57d467fN13be62c2a076aa44N14bb1a08d8e5c93dN14bce6aeb213e824N14e0a7faee0add98N14fe336bcf5bd632N158e8f1972b6bddcN15c4cc9076553ed7N16530bd72ce2b88eN16c23ab39c36268bN17d223c501808869N189259c2d68c2856N198260d68fed1a7fN19c374dd33e52c06N19d8661e06d36c78N1a24f417fb4b30f6N1afddb4472e78bd2N1babae27a4524318N1c1bb42559a3f234N1c994679f41d75edN1d16ab1d073f5d68N1d43a10b55633ef0N1d466606f60d4e66N1d7ca953642a73bbN1da82092f38541b3N1dfbf0e5eb57321aN201606ebdf278228N2019165a76fbb131N20e3063aa386d781N220cb392556c18f3N221c49f23998c487N229182a800a59bc6N22dfb634af92b3f2N233033a444d73140N23594c803a881f05N238d5f4d59c90bc4N239caf090f806a4cN241aeedc361b54bfN24599dbc42a06339N2547abec20ed360fN25e1186bac740a16N263652696ddeb4fbN263c48c9efc84fb9N26e03fd2f795b5d7N27364deda949335dN27c50174f5c8fb8bN27efeac7bb54cc80N28e505e25274e9d6N2918c22928ffc6c4N2969f59a35db7350N29a4a80626f159b6N2a0430777d7a952cN2a1c3c4150a8d78cN2a1cec92ce8b52b7N2a44ff86e3f9b4e5N2aa77b2c3a7ce669N2bcd76aaf3c3e8b6N2bfc92e940f73d72N2c7b9fa40d946174N2cebadfceac65d6aN2de0586347a0e1edN2e03b426693e9a8fN2e560b3a974e8fdbN2e989a741cd347e1N2ebc691e980eca53N2f660c964f72d900N2f828745b3e63054N2f9ea9380b20aa54N3011aa198aa667d3N30a18f6d2868276bN30b12f71f4c97fceN30f06aa2f1e69749N32354e94d947a86cN328e67cec051eea1N332533d20c2d2999N334bde9548de12f9N334e8b47a79c3b4dN33d2f5f64216db12N33f03a94a4eed701N346ab044466212d3N35256c020d06ba0bN3534f9a0f02c96c3N355979174dc50863N357d54223d6563dcN366dd096e0469d86N377ec349c6d67965N391d8e3f2188c610N392d4411ccfcbc8cN3a44dc138ae1aaf6N3a60a5b208be8c5eN3a6abfbf6d40a0c6N3b483c17584cbf89N3bad6d295aa1f4e3N3bd6cab3e5cffea8N3ca9eb0e09f8f50bN3d2ef48731bc4b3cN3d43f1bb4828903bN3d57d01abb335255N3dc3e42cb4337a4dN3e3f15e9198d6b60N3ef2ac53637d3291N3f3ddd29918b7c44N3f41c8be45f92f03"%lxh.
Ltac2 gd_tbl_P_pkcs7_cinfo () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.buf_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"].


Definition U_PKCS7_CINFO : Z := 0x1ddb4.
Notation PKCS7_CINFO_STACK := 48 (only parsing).

Definition pkcs7_cinfo_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (PP SEQE BS P END lo : Z) (pad : word) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_pkcs7_cinfo ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.$4.Lr,$4.(1.$4.Lp',$4.(1.$4.Lse,$4.(1.(2.&40.)Ltg,(2.&40.)(1.$4.Llen,$4.(1.$4.Lq,$4.(5.(6.$0.R17.(7.(8.O1:.O19.O18.O17.R16.R15.R14.O16.O15.R13.R12.R11.R10.R?.R>.R=.R<.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.R;.R:.R9.R8.)O:.(9.O1:.)O9.(:.(2.&40.))R7.(;.O1;.)))(5.(<.(=.(>.$4.$4.)(?.$4.$4.O8.(10.O8.+8.))(=.(>.$4.$4.)(?.$4.$4.O7.(10.O7.+8.))(=.(>.$4.$4.)(?.$4.$4.O6.(10.O6.+18.))(=.(>.$4.$4.)(?.$4.$4.(11.(12.&40.O19.)+30.)(12.&40.O19.))(13.(>.$4.$4.))))))O1.R7.)(5.(14.O1;.O1.R7.)(5.(15.O1;.R7.)(5.(6.(2.&40.)R13.(16.&40.R6.))(5.(5.(17.-5600.R6.)(18.R6.=))(5.(19.O1;.R7.O8.(=.$1:.(1;.(16.&40.R5.))(13.$1:.)))(5.(19.O1;.R7.O7.(=.$1:.(1;.(16.&40.R4.))(13.$1:.)))(5.(19.O1;.R7.O6.(1<.R3.O2.R2.R1.))(5.(1=.O1;.R7.O3.(12.&40.O19.))(5.(5.(18.O5.R5.)(18.R5.O4.))P,(6.$4.R6.=)(5.(6.(2.&40.)R4.(16.&40.+6.))(5.(18.(10.O5.+4.)R2.)(5.(18.=R3.)(5.(6.$4.(10.R2.R3.)R6.)(5.(18.R6.R5.)(18.R5.O4.)))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition pkcs7_cinfo_stmt {L : heap_layout} (segs : list Segment) (ENTRY : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (PP SEQE BS P END BUF lo : Z) (bs : list byte) (sev tg0 pad : word) (len0 q0 : Z),
  rw_cells segs m PP [C8 (Z_to_bv 64 P)] ->
  rw_cells segs m SEQE [C8 sev] ->
  rw_cells segs m BS (buf_cells tg0 pad len0 q0) ->
  bytes_at segs m BUF bs ->
  BUF <= P -> P <= END -> END <= BUF + Z.of_nat (length bs) -> BUF + Z.of_nat (length bs) < 2^63 ->
  (PP + 8 <= SEQE \/ SEQE + 8 <= PP) -> (PP + 8 <= BS \/ BS + 24 <= PP) -> (SEQE + 8 <= BS \/ BS + 24 <= SEQE) ->
  (PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP) ->
  (SEQE + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= SEQE) ->
  (BS + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= BS) ->
  PP mod 8 = 0 -> SEQE mod 8 = 0 -> BS mod 8 = 0 -> 0 < PP -> 0 < SEQE -> 0 < BS -> 0 < BUF ->
  stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PKCS7_CINFO_STACK -> alloc_ceiling <= lo ->
  bv_unsigned sp mod 16 = 0 ->
  (PP + 8 <= lo \/ bv_unsigned sp <= PP) -> (SEQE + 8 <= lo \/ bv_unsigned sp <= SEQE) -> (BS + 24 <= lo \/ bv_unsigned sp <= BS) ->
  (BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF) ->
  mem_inv segs m ->
  a0 = Z_to_bv 64 PP -> a1 = Z_to_bv 64 END -> a2 = Z_to_bv 64 SEQE -> a3 = Z_to_bv 64 BS ->
  evt segs (pkcs7_cinfo_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP SEQE BS P END lo pad m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Lemma U_pkcs7_cinfo_spec {L : heap_layout} : pkcs7_cinfo_stmt usegs U_PKCS7_CINFO.
Proof.
  unfold pkcs7_cinfo_stmt, U_PKCS7_CINFO.
  intros until q0.
  intros HPP HSE HBS HBUF B1 B2 B3 B4 D1 D2 D3 D4 D5 D6 AL1 AL2 AL3 NZ1 NZ2 NZ3 NZ4 ST SLO ACL SPA DS1 DS2 DS3 DS4 MI -> -> -> ->.
  pose proof alloc_ceiling_pos as ACP.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  unfold bv_modulus in SPR.
  cbn in SPR.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB.
  change (Z.of_nat 8) with 8 in PPB.
  pose proof (rw_cells_bound _ _ _ _ HSE) as SEB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SEB.
  change (Z.of_nat 8) with 8 in SEB.
  pose proof (rw_cells_bound _ _ _ _ HBS) as BSB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ buf_cells] in BSB.
  change (Z.of_nat 24) with 24 in BSB.
  pose proof (munch_refl [(PP, PP + 8); (SEQE, SEQE + 8); (BS, BS + 24); (bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold buf_cells in HBS.
  rewrite <- (Z_to_bv_bv_unsigned sev) in HSE.
  carve_frame 48%nat ST.
  lxp_split_frame [8;8;8;8;8;8]%nat. lxp_seps 48.
  (* [comment removed for export] *)
  pose proof (@sums2_ok _) as LXSUMS.
  lxp_run (PLANS [] [] 64%N SUMS2).
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
Qed.
