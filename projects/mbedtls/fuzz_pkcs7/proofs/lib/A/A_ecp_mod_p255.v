(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_grow P_ecp_red.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_mpi_stmtA A_mpi_stmtA_sz A_ecp_stmtA
     A_mpi_opnd A_mpi_journey A_mpi_grow A_mpi_core_mla A_mpi_core_add A_ecp_red_lib A_mpi_add_int.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxA LxSum.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxATac LxARt LxAEcpSums.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw TacA.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxFlat.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00192d4a98a77d96 1 1 16 4 1 1 35 1 37 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P006307772cc952d8 1 1 4 1 0 1 2 64 1 100 1P00cba1e6a478444c 1 2 16 3 1 1 33 1 62 1 16 3 0 1 34 1 63 1 2 64 1 65 1P011502ab91c0df02 0 7 0 1 64 1 72 1 73 1 76 1 84 1 85 1P01659e4a5d21327e 1 1 16 2 75 1 103 1 3 0 1 102 1 104 16P01e41ed3662e59be 1 1 16 3 1 1 33 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P0216d0f0e8348e84 2 86 1 1 8 3 2 1 112 1 115 1 4 0 2 113 2 114 2 116 16 1 1 8 3 1 1 113 1 114 1 5 0 1 70 4 112 1 115 1 116 8P021beb6d1294bc84 1 1 8 3 0 1 113 1 114 1 5 2 1 70 4 112 1 115 1 116 8P0224d32fa54a7567 1 1 16 3 0 1 103 1 104 1 4 39 1 102 1 105 1 106 16P02254829dbad8833 1 1 16 3 0 1 111 1 112 1 11 46 1 68 4 78 1 87 1 89 1 96 1 97 1 100 1 110 1 113 1 114 16P023f18c41aa470ff 1 1 16 3 0 1 102 1 103 1 4 38 2 101 2 104 2 105 32P0251dc84c26e754a 1 1 4 1 0 1 2 62 1 102 1P0259858c2a5e92e9 0 2 0 1 1 1P0259c1a1e7515ccd 1 1 4 3 1 1 105 1 108 1 5 3 4 68 16 106 4 107 4 109 16P0269139ea6c78c58 0 2 0 1 2 1P026d86307465c9cc 0 4 0 1 85 1 110 1 111 1P02ec0bf8a7d8ef2b 1 1 16 4 1 1 35 1 37 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P03828de12c6d666a 1 1 16 2 1 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P03df4e08612c69c4 1 1 16 2 1 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P03f051aed8d7d170 1 1 16 3 0 1 83 1 84 1 4 57 1 82 1 85 1 86 16P04337b5706d5c863 1 1 64 2 1 1 102 1 4 49 1 76 1 101 1 103 64P043d2875789dd68e 0 4 0 1 48 1 61 1 62 1P04aed4d5c853021c 1 1 4 1 0 1 3 62 1 74 1 102 1P04dcd60e4dd6da7d 0 7 0 1 45 1 49 1 50 1 53 1 61 1 62 1P0506612c5d3d1ef5 1 2 16 2 0 1 63 1 16 2 1 1 62 1 2 64 1 65 1P05167ea51ed01989 0 6 0 1 55 1 56 1 68 1 81 1 82 1P053670ef47c7c93c 0 4 0 1 48 1 61 1 62 1P057582f778b486e7 1 1 16 2 1 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P057b5c5072cc11ea 0 2 0 1 89 1P05952ffa0bc68230 1 1 16 3 0 1 110 1 111 1 9 82 1 86 1 88 1 95 1 96 1 99 1 109 1 112 1 113 16P05d424633e8205eb 0 4 0 1 79 1 102 1 103 1P061f83dd5e2d9b43 1 1 64 2 0 1 81 1 3 6 1 82 1 83 64P062e276c05c4a008 0 4 0 1 48 1 61 1 62 1P067afc9755658d93 0 7 0 1 52 1 60 1 61 1 64 1 72 1 73 1P06a02ecdbd60fa1b 0 6 0 1 45 1 49 1 53 1 61 1 62 1P06c23ded959943f7 1 1 16 3 0 1 104 1 105 1 4 40 2 103 2 106 2 107 32P06d1ec92e877dd33 0 7 0 1 45 1 49 1 50 1 53 1 61 1 62 1P071627238eeda7c1 1 1 16 3 0 1 105 1 106 1 5 2 1 64 4 104 1 107 1 108 16P07965e7a172418d6 0 7 0 1 64 1 72 1 73 1 76 1 84 1 85 1P07c8db51221bd7ad 0 2 0 1 66 4P07dbb7d904a479bb 1 1 16 3 0 1 106 1 107 1 13 41 32 63 128 73 32 82 32 84 32 91 32 92 32 95 32 103 32 104 32 105 32 108 32 109 512P08365a9ed7f066a3 0 7 0 1 40 1 81 1 90 1 94 1 102 1 103 1P083f44387360f5bb 1 1 64 2 5 1 81 1 3 0 1 82 1 83 64P088c2fc588796390 0 7 0 1 63 4 73 1 84 1 92 1 105 1 106 1P08fbe816f7aaac3a 1 1 8 3 1 1 112 1 115 1 4 2 2 113 2 114 2 116 16P09369898d35774a1 1 1 32 3 0 1 104 1 105 1 12 39 64 76 64 80 64 82 64 89 64 90 64 93 64 101 64 102 64 103 64 106 64 107 2048P093c9d586c2c595f 1 1 16 2 0 1 61 1 3 4 1 62 1 63 16P093f9ba3b58c0b83 0 4 0 1 48 1 61 1 62 1P0949adfc9813ce48 1 1 16 3 0 1 101 1 102 1 4 37 1 100 1 103 1 104 16P0967d1f2414b6823 0 7 0 1 60 4 70 1 81 1 89 1 100 1 101 1P096c33263ed5c7f5 1 3 4 3 1 1 105 1 106 1 8 2 67 1 108 1 32 9 42 1 79 1 83 1 85 1 92 1 93 1 96 1 104 1 107 1 2 109 2 110 2P098780d25bce78ae 0 5 0 1 39 1 71 1 84 1 85 1P09d38b2c8f75fac0 1 1 4 1 0 1 2 68 1 110 1P0a04faec01607b59 0 6 0 16 45 16 110 16 111 16 112 16 113 16P0a1bf323a5e40d6b 0 4 1 1 80 1 103 1 104 1P0a3349483d1f9bd6 1 1 4 4 0 1 80 4 112 1 113 1 10 47 1 79 1 88 1 90 1 97 1 98 1 101 1 111 1 114 1 115 4P0a511dc350a0210b 0 7 0 1 37 1 65 1 69 1 73 1 81 1 82 1P0a9b04d28ccbfd6b 1 1 16 3 0 1 104 1 105 1 11 41 2 63 8 73 2 82 2 84 2 91 2 92 2 95 2 103 2 106 2 107 32P0ab146620a0ad6b0 1 1 4 1 0 1 2 81 1 112 1P0b05e7bbe4ed1235 0 4 0 16 3 16 61 16 62 16P0b57d5f2112e1cb2 0 3 0 1 38 1 40 1P0b80f9fcddde7524 1 1 16 3 0 1 103 1 106 1 4 3 1 104 1 105 1 107 16P0bcb4a27f562816e 1 1 16 3 0 1 85 1 86 1 4 27 1 84 1 87 1 88 16P0c1bbf077af05782 0 5 0 1 39 1 71 1 84 1 85 1P0c32c9fa70d6a209 0 12 0 16 62 64 72 16 81 16 83 16 90 16 91 16 94 16 102 16 103 16 104 16 105 16P0c9022cce9322622 1 2 16 2 0 1 104 1 16 2 77 1 105 1 2 106 1 107 1P0cc4ad9438bf5d5b 1 2 32 3 0 1 103 1 104 1 32 9 40 1 77 1 81 1 83 1 90 1 91 1 94 1 102 1 105 1 2 106 1 107 1P0ce95be89b843b91 0 5 0 1 39 1 71 1 84 1 85 1P0d1dba4294ebcfc7 0 2 0 1 66 4P0d3c423679a33c71 0 6 0 1 37 1 86 1 87 1 100 1 101 1P0db206f397f47ebf 1 1 16 3 0 1 104 1 105 1 11 41 2 63 8 73 2 82 2 84 2 91 2 92 2 95 2 103 2 106 2 107 32P0de72a90344e6190 1 2 32 3 1 1 104 1 105 1 32 9 41 1 78 1 82 1 84 1 91 1 92 1 95 1 103 1 106 1 2 107 1 108 1P0e14aef4e079560c 0 2 0 1 74 1P0e16265686460ca3 0 7 0 1 64 1 72 1 73 1 76 1 84 1 85 1P0f2cc7be0133bb50 0 6 0 1 45 1 49 1 53 1 61 1 62 1P0faead55850c059c 1 1 16 3 1 1 33 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P0fc97fa8999d1367 1 2 16 2 0 1 63 1 16 2 1 1 62 1 2 64 1 65 1P0ff2d6371f686aca 0 2 0 1 1 1P0ff7e244c1037dbe 1 1 16 3 0 1 85 1 86 1 4 27 1 84 1 87 1 88 16P1000ebc2a9661ef3 1 1 16 3 0 1 104 1 105 1 10 63 4 73 1 82 1 84 1 91 1 92 1 95 1 103 1 106 1 107 16P1025289db2e19f28 0 4 1 1 56 1 82 1 90 1P1035898bbd88c24b 1 2 32 3 0 1 102 1 103 1 32 9 39 1 76 1 80 1 82 1 89 1 90 1 93 1 101 1 104 1 2 105 1 106 1P106990514acafd63 0 2 0 1 64 4P10a549fea0fcf528 0 2 0 1 72 1P10b751217b2701b9 0 3 0 1 41 1 45 1P1106c87eed84e5d1 0 2 0 1 2 1P113d03c73c3212c6 1 1 16 4 1 1 35 1 37 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P114d1d4e7a378b58 1 2 4 3 0 1 112 1 115 1 4 2 73 1 116 1 4 2 4 113 4 114 4 117 64P1153572449f5a4e4 1 1 16 2 1 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P11828268733c706f 1 1 16 3 0 1 101 1 102 1 9 75 1 79 1 81 1 88 1 89 1 92 1 100 1 103 1 104 16P11c78f77a3d011f1 1 1 16 3 0 1 74 1 75 1 9 49 1 53 1 55 1 61 1 62 1 65 1 73 1 76 1 77 16P11f8aa119bae7c51 0 2 0 1 97 1P126cf299fa9a0583 1 1 16 2 1 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P12a2b56bbf23a820 0 12 0 16 62 64 72 16 81 16 83 16 90 16 91 16 94 16 102 16 103 16 104 16 105 16P12f1098be63714d2 1 3 4 3 0 1 112 1 113 1 8 2 72 1 115 1 32 9 47 1 84 1 88 1 90 1 97 1 98 1 101 1 111 1 114 1 2 116 2 117 2P1313533236d0c771 0 7 0 1 46 1 87 1 96 1 100 1 110 1 111 1P135670621aaf87fa 1 1 32 2 0 1 110 1 3 62 1 111 1 112 32P135ad739ca0fd602 0 2 0 1 64 4P1364ab77097c7f50 0 2 0 1 2 1P138997df442d61a7 0 7 0 1 40 1 69 1 81 1 90 1 102 1 103 1P13f9b1ff46d66d32 0 7 0 1 62 4 72 1 83 1 91 1 102 1 103 1P14648c4a5bb22411 1 1 16 3 0 1 83 1 84 1 9 45 1 66 1 68 1 70 1 71 1 74 1 82 1 85 1 86 16P14a7e9c26557025d 1 1 16 3 0 1 101 1 102 1 9 75 1 79 1 81 1 88 1 89 1 92 1 100 1 103 1 104 16P14a8f5209ff7d81c 1 1 16 4 1 1 35 1 37 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P14c6d5f6847c1545 0 6 0 1 45 1 49 1 53 1 61 1 62 1P1551da757a1e1560 1 1 16 3 0 1 103 1 104 1 11 40 2 62 8 72 2 81 2 83 2 90 2 91 2 94 2 102 2 105 2 106 32P157ff405fa63f748 1 2 32 3 0 1 102 1 103 1 32 9 39 1 76 1 80 1 82 1 89 1 90 1 93 1 101 1 104 1 2 105 1 106 1P1599c37a44dd8eff 0 6 0 1 45 1 49 1 53 1 61 1 62 1P159fd53002dd224a 0 7 0 1 45 1 49 1 50 1 53 1 61 1 62 1P15a9cd114decbd0a 0 2 0 1 64 4P15c75c139db92d7d 1 1 16 3 0 1 111 1 112 1 11 46 1 68 4 78 1 87 1 89 1 96 1 97 1 100 1 110 1 113 1 114 16P166ffe8bcebdaff9 0 7 0 1 45 1 49 1 50 1 53 1 61 1 62 1P16791ae0f8c57918 1 2 16 2 0 1 109 1 16 2 82 1 110 1 2 111 1 112 1P16cad21656b74be5 1 1 16 3 0 1 113 1 114 1 5 2 1 70 4 112 1 115 1 116 16P16d342afe72ffd2e 1 1 4 4 1 1 81 1 104 1 105 1 2 67 1 108 1P17065098aa838d34 0 6 0 1 39 1 88 1 89 1 102 1 103 1P173588e93f536026 1 1 64 2 1 1 72 1 3 0 1 73 1 74 64P17ce3befc4e38e00 1 1 4 1 0 1 3 62 1 74 1 102 1P17d0ca5b9689f535 0 4 0 1 48 1 61 1 62 1P1832797b9984a8b9 1 1 16 3 0 1 112 1 113 1 4 46 1 111 1 114 1 115 16P1834dbb9199ea733 0 6 0 1 45 1 49 1 53 1 61 1 62 1P186632b6c0e198ca 0 4 0 1 48 1 61 1 62 1P1871ceb7d5ff3d8e 0 7 0 1 63 4 73 1 84 1 92 1 105 1 106 1P192534cba6d4a569 2 83 1 1 4 3 3 1 113 1 116 1 5 0 4 74 16 114 4 115 4 117 16 1 1 16 3 2 1 114 1 115 1 5 0 1 71 4 113 1 116 1 117 16P1975c26b17fb3335 0 2 0 1 73 1P1996b33d52d921ef 0 2 0 1 2 1P19b8e077ec208ca6 1 1 16 2 1 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P19c4e392c55e15c0 0 6 0 1 45 1 49 1 53 1 61 1 62 1P19d3a87eb1adc8ed 0 7 0 1 45 1 49 1 50 1 53 1 61 1 62 1P19e3a41b2f87e03e 1 2 32 3 0 1 73 1 76 1 32 3 1 1 74 1 75 1 2 77 2 78 2P1a2eca1f842a9b30 0 7 0 1 40 1 81 1 90 1 94 1 102 1 103 1P1a4437baa2cf924e 1 2 16 2 0 1 63 1 16 2 1 1 62 1 2 64 1 65 1P1a919f9e3ae3904f 1 1 8 3 1 1 104 1 107 1 4 2 2 105 2 106 2 108 16P1ac9717e5bc51a86 1 1 4 1 0 1 2 62 1 102 1P1acd4400d7ae9cd6 1 1 16 3 0 1 112 1 113 1 11 47 2 69 8 79 2 88 2 90 2 97 2 98 2 101 2 111 2 114 2 115 32P1ad9b9495e285a44 1 1 16 3 0 1 105 1 106 1 5 2 1 64 4 104 1 107 1 108 16P1b17c609be6366a9 1 1 4 3 1 1 105 1 108 1 5 3 4 68 16 106 4 107 4 109 16P1b1d0d54e5bbb14c 1 1 4 4 1 1 81 4 113 1 114 1 4 2 1 112 1 115 1 116 4P1b25e4d045e79d3a 1 1 16 3 0 1 106 1 107 1 5 3 4 65 16 105 4 108 4 109 64P1b46ee20aa7a6849 1 2 32 3 0 1 82 1 85 1 32 3 1 1 83 1 84 1 2 86 2 87 2P1b67da8781d6b5e8 0 6 0 1 27 1 39 1 59 1 72 1 73 1P1b8850993e1c6a57 1 1 64 2 0 1 110 1 3 10 1 111 1 112 64P1ba7db320f44dc88 1 2 16 2 0 1 63 1 16 2 1 1 62 1 2 64 1 65 1P1ba8ec43bf3be06e 0 6 0 1 45 1 49 1 53 1 61 1 62 1P1bb05318d6adcb44 0 2 0 1 2 1P1be78817ff412232 1 1 16 3 0 1 112 1 113 1 11 47 2 69 8 79 2 88 2 90 2 97 2 98 2 101 2 111 2 114 2 115 32P1bffee487514f070 0 4 0 1 48 1 61 1 62 1P1c0981aa8a6f10a4 0 12 0 16 62 64 72 16 81 16 83 16 90 16 91 16 94 16 102 16 103 16 104 16 105 16P1c6a2ae286c79f94 0 7 0 1 46 1 87 1 96 1 100 1 110 1 111 1P1c8c0195d5c8f133 1 1 16 3 0 1 83 1 84 1 9 45 1 66 1 68 1 70 1 71 1 74 1 82 1 85 1 86 16P1c8dc6030c8e236f 0 6 0 1 45 1 49 1 53 1 61 1 62 1P1ca3a80020838198 0 7 0 1 45 1 49 1 50 1 53 1 61 1 62 1P1cd8166704510cbe 0 7 0 1 64 1 72 1 73 1 76 1 84 1 85 1P1cdcd6bc8e382492 0 13 0 16 46 16 68 64 78 16 87 16 89 16 96 16 97 16 100 16 110 16 111 16 112 16 113 16P1ced6411b276fea8 0 8 0 1 37 1 65 1 69 1 70 1 73 1 81 1 82 1P1d07da84bac61b85 0 8 0 1 37 1 51 1 85 1 86 1 87 1 100 1 101 1P1d336100f6fae604 1 1 16 4 1 1 35 1 37 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P1d4e2fcaefc26365 1 1 16 3 1 1 33 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P1d9503be2e3eac63 1 1 32 2 9 1 102 1 3 0 1 103 1 104 32P1daa00b95ebba65a 0 7 0 1 45 1 49 1 50 1 53 1 61 1 62 1P1e27b1428e7a941e 2 80 1 1 16 3 2 1 111 1 114 1 4 0 1 112 1 113 1 115 16 1 1 4 4 3 1 80 4 112 1 113 1 4 0 1 111 1 114 1 115 4P1e6f1ae9559991c8 1 1 4 1 0 1 2 63 1 100 1P1eb6ff7cafbaf610 0 4 0 1 85 1 110 1 111 1P1ec5dee937185a6a 0 5 0 1 39 1 71 1 84 1 85 1P1eecbd3d4d623e79 0 2 0 1 72 1P1f0b49b175fcb21b 0 6 0 16 45 16 110 16 111 16 112 16 113 16P1f5889853e0961e0 1 1 16 3 0 1 112 1 113 1 11 47 2 69 8 79 2 88 2 90 2 97 2 98 2 101 2 111 2 114 2 115 32P1f6e4af1ead83009 0 2 0 1 70 1P1ff80089356326b1 1 2 32 3 0 1 81 1 84 1 32 9 37 1 44 1 65 1 67 1 69 1 70 1 73 1 82 1 83 1 2 85 1 86 1P20040e3b1ca260cd 0 6 0 1 45 1 94 1 95 1 110 1 111 1P2029cd55fa9dfedf 1 1 32 2 0 1 102 1 3 56 1 103 1 104 32P20ae5bdf4e7523ef 1 1 16 4 1 1 35 1 37 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P20ae87b98cd4b794 0 8 0 1 46 1 87 1 96 1 97 1 100 1 110 1 111 1P20b4941eb89462a9 0 7 0 1 64 1 72 1 73 1 76 1 84 1 85 1P20decd5aa562b627 0 13 0 32 40 32 62 128 72 32 81 32 83 32 90 32 91 32 94 32 102 32 103 32 104 32 105 32P210d56174477d16d 1 1 16 3 0 1 114 1 115 1 5 3 1 71 4 113 1 116 1 117 16P21234b2d211d2e98 0 5 0 1 39 1 59 1 72 1 73 1P2139208732c52cb3 0 2 0 1 91 1P2161e22c7a2350a2 1 1 16 3 0 1 82 1 83 1 9 44 1 65 1 67 1 69 1 70 1 73 1 81 1 84 1 85 16P216632fa055f277a 1 1 16 3 0 1 104 1 105 1 11 41 2 63 8 73 2 82 2 84 2 91 2 92 2 95 2 103 2 106 2 107 32P21853cc1caf2f0f5 0 2 0 1 1 1P21db7a6df16a874e 0 7 0 1 64 1 72 1 73 1 76 1 84 1 85 1P223746a0c2f371c8 0 2 0 1 2 1P22862e47833ed436 1 2 16 3 1 1 33 1 62 1 16 3 0 1 34 1 63 1 2 64 1 65 1P22b485dc516b8601 2 83 1 1 16 3 2 1 112 1 115 1 4 0 1 113 1 114 1 116 16 1 1 16 3 1 1 113 1 114 1 5 0 4 70 16 112 4 115 4 116 64P236625cd2301ce8c 0 7 0 1 73 1 74 4 84 1 92 1 105 1 106 1P237881841c5c42d4 0 4 0 1 48 1 61 1 62 1P23b3125d504147c2 1 1 4 1 0 1 2 67 1 107 1P23d5adab18a99442 1 2 16 3 1 1 33 1 62 1 16 3 0 1 34 1 63 1 2 64 1 65 1P23f3c136075d32a7 0 12 0 16 68 64 78 16 87 16 89 16 96 16 97 16 100 16 110 16 111 16 112 16 113 16P241073ff87d9a480 0 7 0 1 64 1 72 1 73 1 76 1 84 1 85 1P24e0b54ef0da9c82 0 12 0 16 68 64 78 16 87 16 89 16 96 16 97 16 100 16 110 16 111 16 112 16 113 16P24fac366b45754ae 0 7 0 1 38 1 79 1 88 1 92 1 100 1 101 1P254b843a049ddaa6 1 1 16 3 1 1 104 1 107 1 4 2 1 105 1 106 1 108 16P258011d2f39a52e1 0 8 0 1 40 1 81 1 90 1 91 1 94 1 102 1 103 1P259dd4d22f99bb9b 0 4 0 1 48 1 61 1 62 1P25a7740b56601091 0 8 0 1 28 1 52 1 60 1 61 1 64 1 72 1 73 1P25bcd25082b15e5f 1 1 16 4 1 1 35 1 37 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P25d68d2bb7061da2 0 3 0 1 62 4 74 4P25fa7c3b70ac014b 1 1 16 4 1 1 35 1 37 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P26080165e9349311 0 5 0 1 39 1 71 1 84 1 85 1P26254296287bdc0d 0 6 0 16 39 16 102 16 103 16 104 16 105 16P266d3e83c2d1776c 0 2 0 1 1 1P26a1390a59fa5127 1 1 32 2 7 1 100 1 3 0 1 101 1 102 32P26e77ab7b44e1ee7 1 1 16 3 0 1 111 1 112 1 4 45 1 110 1 113 1 114 16P27a859c43cc15593 0 6 0 1 65 1 69 1 73 1 81 1 82 1P27b4a368dd668881 0 4 0 1 77 1 100 1 101 1P27d49a77e719b6e3 1 1 16 4 1 1 35 1 37 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P280eb549e3540354 0 7 0 1 45 1 49 1 50 1 53 1 61 1 62 1P2856289e9b14793f 1 1 16 3 0 1 83 1 84 1 9 45 1 66 1 68 1 70 1 71 1 74 1 82 1 85 1 86 16P287b9219ac356f70 0 7 0 1 45 1 49 1 50 1 53 1 61 1 62 1P28a87ef83d308551 1 1 16 3 0 1 85 1 86 1 4 27 1 84 1 87 1 88 16P28adf4b87ae61332 1 1 16 3 0 1 112 1 113 1 10 69 4 79 1 88 1 90 1 97 1 98 1 101 1 111 1 114 1 115 16P28e41a122e47188c 1 1 16 4 1 1 35 1 37 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P296872bcc6491979 1 1 4 4 0 1 78 1 103 1 104 1 2 64 1 105 1P2994a8c7278530ad 0 7 0 1 64 1 72 1 73 1 76 1 84 1 85 1P29a0f5d83c59171a 0 5 0 1 39 1 71 1 84 1 85 1P29bc310a15e7bf15 1 2 4 3 1 1 113 1 116 1 4 2 74 1 117 1 4 3 1 114 1 115 1 118 16P29c5354f0b9ddfec 1 1 4 1 0 1 2 73 1 102 1P2a18a60c92133fb7 1 1 32 2 0 1 100 1 3 54 1 101 1 102 32P2a352efbca13d10a 0 7 0 1 38 1 67 1 79 1 88 1 100 1 101 1P2a50d1a7e14bb9c7 0 2 0 1 1 1P2a682ac563e86146 0 7 0 1 28 1 64 1 72 1 76 1 84 1 85 1P2a708930e99d585d 0 7 0 1 45 1 49 1 50 1 53 1 61 1 62 1P2a7e61ce3901e005 1 1 4 4 1 1 74 4 104 1 105 1 4 3 1 103 1 106 1 107 4P2a8c07466ede4576 0 12 0 16 62 64 72 16 81 16 83 16 90 16 91 16 94 16 102 16 103 16 104 16 105 16P2b60a2e3242e83fb 1 2 32 3 0 1 101 1 102 1 32 9 38 1 75 1 79 1 81 1 88 1 89 1 92 1 100 1 103 1 2 104 1 105 1P2b75c18f1cfbc063 1 1 16 3 0 1 112 1 113 1 10 69 4 79 1 88 1 90 1 97 1 98 1 101 1 111 1 114 1 115 16P2c05363ff521fe76 0 7 0 1 45 1 49 1 50 1 53 1 61 1 62 1P2c162c834e957c54 0 3 0 1 62 4 74 4P2c256e9fe97c4a20 0 5 0 1 39 1 71 1 84 1 85 1P2c34d1bad7689748 0 6 0 1 45 1 49 1 53 1 61 1 62 1P2c4fbeceaed03dbb 0 7 0 1 64 1 72 1 73 1 76 1 84 1 85 1P2c5f1303da22049a 1 2 16 3 1 1 33 1 62 1 16 3 0 1 34 1 63 1 2 64 1 65 1P2c88fc222f1629cc 0 3 0 1 68 4 80 4P2c8e4bc7e952214a 1 2 16 3 1 1 33 1 62 1 16 3 0 1 34 1 63 1 2 64 1 65 1P2c9d8ec198de308a 1 1 16 2 1 1 104 1 5 51 1 63 4 73 1 103 1 105 16P2cd05098a1f61851 1 1 16 4 1 1 35 1 37 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P2cd5cef7c54cd41a 1 1 64 2 0 1 72 1 3 2 1 73 1 74 64P2cf36e08e2a32b5b 0 5 0 1 39 1 71 1 84 1 85 1P2d7cd8ce1e214c66 0 4 1 1 78 1 101 1 102 1P2e03a43f33dbeb53 1 1 16 3 1 1 112 1 115 1 4 2 1 113 1 114 1 116 16P2e2f8dcf1f51da30 1 2 64 2 0 1 100 1 64 2 76 1 101 1 2 102 1 103 1P2e6dce1faeeaf3ea 1 1 16 3 0 1 104 1 105 1 10 63 4 73 1 82 1 84 1 91 1 92 1 95 1 103 1 106 1 107 16P2e78eca3cb9c23f8 0 4 0 1 48 1 61 1 62 1P2e95f5a37f6a14c5 0 4 0 1 48 1 61 1 62 1P2e9a58b825d5da83 1 1 16 3 0 1 106 1 107 1 13 41 32 63 128 73 32 82 32 84 32 91 32 92 32 95 32 103 32 104 32 105 32 108 32 109 512P2ea1b853fecc6725 1 2 16 2 0 1 63 1 16 2 1 1 62 1 2 64 1 65 1P2f17f66331d43112 0 7 0 1 64 1 72 1 73 1 76 1 84 1 85 1P2fafaa91e9e1f456 1 2 16 3 1 1 33 1 62 1 16 3 0 1 34 1 63 1 2 64 1 65 1P303ac12f9fa84e5e 0 6 0 16 39 16 102 16 103 16 104 16 105 16P3060e1cfa9e323c4 1 2 16 3 1 1 33 1 62 1 16 3 0 1 34 1 63 1 2 64 1 65 1P310981e45f3e3bfe 0 6 0 1 37 1 86 1 87 1 100 1 101 1P31103eb73a4099c1 1 2 32 3 0 1 110 1 111 1 32 3 1 1 109 1 112 1 2 113 2 114 2P316504d22a417bd4 0 7 0 1 45 1 49 1 50 1 53 1 61 1 62 1P3192f7d330ac10d6 1 2 32 3 1 1 112 1 113 1 32 9 47 1 84 1 88 1 90 1 97 1 98 1 101 1 111 1 114 1 2 115 1 116 1P3211f050445c9567 1 1 16 3 0 1 103 1 104 1 11 40 2 62 8 72 2 81 2 83 2 90 2 91 2 94 2 102 2 105 2 106 32P32239c509d1688da 1 1 16 3 0 1 104 1 105 1 11 41 2 63 8 73 2 82 2 84 2 91 2 92 2 95 2 103 2 106 2 107 32P324346f3f07d9520 0 2 0 1 71 1P32baac9ea5af9b7c 1 1 16 4 1 1 35 1 37 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P32bd4892bb92461f 0 4 0 1 48 1 61 1 62 1P32c9b2521e337b89 1 1 16 2 81 1 111 1 3 0 1 110 1 112 16P33633fb097d06b27 1 1 64 2 49 1 73 1 3 0 1 72 1 74 64P33ad469e7dc1b9b1 0 5 0 1 39 1 71 1 84 1 85 1P33c5a081f14c5d84 0 5 0 1 39 1 71 1 84 1 85 1P33da338f91500782 0 7 0 1 64 1 72 1 73 1 76 1 84 1 85 1P33e6753627af6f3e 0 2 0 1 89 1P340cc6693dbeff4e 1 1 16 3 0 1 114 1 115 1 13 47 32 69 128 79 32 88 32 90 32 97 32 98 32 101 32 111 32 112 32 113 32 116 32 117 512P340f5e8471e2e166 0 2 0 1 91 1P345106b4b051ea4e 1 1 16 4 1 1 35 1 37 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P346cd22e76eb31a8 0 6 0 1 45 1 49 1 53 1 61 1 62 1P34d563eac0324786 1 1 4 1 0 1 3 66 1 78 1 108 1P34d8283afd8dc50d 0 13 0 32 40 32 62 128 72 32 81 32 83 32 90 32 91 32 94 32 102 32 103 32 104 32 105 32P351bcd00c281ed29 1 2 32 3 0 1 101 1 102 1 32 9 38 1 75 1 79 1 81 1 88 1 89 1 92 1 100 1 103 1 2 104 1 105 1P35324ef22c89f2ca 0 3 0 1 68 1 80 1P35a0012a5d5b5a6e 0 2 0 1 63 1P35d3e8b5a65b069b 1 1 4 1 0 1 2 73 1 112 1P35f6723262a89ea4 1 1 4 1 0 1 2 69 1 109 1P3639fbe6759332b8 0 7 0 1 45 1 49 1 50 1 53 1 61 1 62 1P364c6a7620cfcad3 0 7 0 1 40 1 81 1 90 1 94 1 102 1 103 1P372fa1f7c33bb4c7 2 84 1 1 8 3 2 1 104 1 107 1 8 0 1 42 1 83 1 92 1 96 1 105 1 106 1 108 8 1 1 8 3 1 1 105 1 106 1 4 0 1 104 1 107 1 108 8P38100a53e0736b00 1 2 16 2 0 1 63 1 16 2 1 1 62 1 2 64 1 65 1P384d36ac834cb79c 1 1 4 1 0 1 2 66 1 108 1P38c8171db290d61c 0 7 0 1 69 4 79 1 90 1 98 1 113 1 114 1P390e8daea453a15e 0 7 0 1 38 1 79 1 88 1 92 1 100 1 101 1P39143b7ceccbf6ff 2 91 1 1 8 3 2 1 112 1 115 1 8 0 1 48 1 89 1 98 1 102 1 113 1 114 1 116 8 1 1 8 3 1 1 113 1 114 1 4 0 1 112 1 115 1 116 8P393a91c42964b312 1 1 8 3 1 1 104 1 107 1 4 2 2 105 2 106 2 108 16P395fb85426b0fe1b 1 2 16 2 0 1 63 1 16 2 1 1 62 1 2 64 1 65 1P3971ae1192ffe96f 1 2 32 3 0 1 81 1 84 1 32 9 37 1 44 1 65 1 67 1 69 1 70 1 73 1 82 1 83 1 2 85 1 86 1P397580db47b1b721 1 2 32 3 0 1 103 1 104 1 32 9 40 1 77 1 81 1 83 1 90 1 91 1 94 1 102 1 105 1 2 106 1 107 1P397cbe82d8f2f7b9 1 1 8 3 0 1 105 1 106 1 5 2 1 64 4 104 1 107 1 108 8P39a62eb3ef63815b 1 1 16 3 1 1 33 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P3a1b98565e0f67ee 1 1 16 3 1 1 33 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P3aa9dde6c89c7622 1 1 32 2 15 1 110 1 3 0 1 111 1 112 32P3ad777c3eb50703b 0 2 0 1 64 1P3ae046f7675e14fb 1 2 32 3 0 1 82 1 85 1 32 3 1 1 83 1 84 1 2 86 2 87 2P3b05698b7fe85bb6 1 1 4 1 0 1 2 68 1 110 1P3ba21da151bdb798 0 7 0 1 64 1 72 1 73 1 76 1 84 1 85 1P3c3aef5da12f66c4 1 1 16 3 0 1 102 1 103 1 9 76 1 80 1 82 1 89 1 90 1 93 1 101 1 104 1 105 16P3c96eb072b6f68ff 0 4 0 1 79 1 102 1 103 1P3cd583be27995280 1 2 32 3 0 1 83 1 84 1 32 3 1 1 82 1 85 1 2 86 2 87 2P3cecd726e168b898 1 1 16 3 1 1 104 1 107 1 4 2 1 105 1 106 1 108 16P3cf4b6d3c2484c6c 1 3 4 3 1 1 113 1 114 1 8 2 73 1 116 1 32 9 48 1 85 1 89 1 91 1 98 1 99 1 102 1 112 1 115 1 2 117 2 118 2P3d05756caf09ddec 1 1 8 3 0 1 105 1 106 1 5 2 1 64 4 104 1 107 1 108 8P3d68aa0ce00957a3 1 2 32 3 1 1 82 1 85 1 32 9 38 1 45 1 66 1 68 1 70 1 71 1 74 1 83 1 84 1 2 86 1 87 1P3d6cc18a5144e5e4 0 5 0 1 39 1 71 1 84 1 85 1P3d7474cd79c15c44 0 4 0 1 77 1 100 1 101 1P3da79f8f2bb8300d 0 6 0 1 45 1 49 1 53 1 61 1 62 1P3dacad2bb47de106 1 1 16 3 0 1 104 1 105 1 4 40 1 103 1 106 1 107 16P3db10a03f9986f9f 0 4 0 1 48 1 61 1 62 1P3de5586feb8e909f 1 2 16 2 0 1 107 1 16 2 80 1 108 1 2 109 1 110 1P3e2e7fe7ea2552f0 1 1 16 3 0 1 85 1 86 1 4 27 1 84 1 87 1 88 16P3e40cf074c882482 1 1 16 3 0 1 103 1 104 1 11 40 2 62 8 72 2 81 2 83 2 90 2 91 2 94 2 102 2 105 2 106 32P3e8879f0644a02c2 0 7 1 1 72 1 73 4 83 1 91 1 102 1 103 1P3eab0049d191fc90 0 2 0 1 1 1P3eaef353b9fb009d 0 6 0 16 50 16 72 16 73 64 102 16 103 16P3eb1c24397216625 1 1 16 3 1 1 33 1 62 1 8 40 1 46 1 48 1 50 1 51 1 54 1 63 1 64 16P3ef35b85a7f195a0 1 2 32 3 0 1 111 1 112 1 32 9 46 1 83 1 87 1 89 1 96 1 97 1 100 1 110 1 113 1 2 114 1 115 1P3f2ec426f29a9bf7 0 5 0 1 39 1 71 1 84 1 85 1P3f4647d707f5c547 0 4 0 1 78 1 103 1 104 1P3f528d1ab1bc716f 1 2 32 3 0 1 82 1 85 1 32 3 1 1 83 1 84 1 2 86 2 87 2P3f539fbb482ec074 0 6 0 1 45 1 49 1 53 1 61 1 62 1P3f70af92b26dfc67 1 1 16 3 0 1 82 1 83 1 4 56 1 81 1 84 1 85 16P3f838e1d1f5cbbc7 0 2 0 1 64 4P3f8eb5048cb6d9cb 1 1 16 3 0 1 106 1 107 1 5 3 4 65 16 105 4 108 4 109 64P3fa0337722c7d59c 0 6 0 64 48 64 63 256 75 64 100 64 101 64P3fb0c5a7fd8766cb 1 1 16 2 0 1 105 1 5 52 1 64 4 74 1 104 1 106 16P3fbfca50eaf2f7f3 0 8 0 1 39 1 53 1 87 1 88 1 89 1 102 1 103 1P3fdd666235e2fd1a 0 6 0 1 45 1 49 1 53 1 61 1 62 1P3fe4104bd6aa6c29 0 6 0 1 39 1 88 1 89 1 102 1 103 1P3ff91fe183f8ec88 1 2 32 3 0 1 111 1 112 1 32 9 46 1 83 1 87 1 89 1 96 1 97 1 100 1 110 1 113 1 2 114 1 115 1P3ffe5d82926e06af 0 8 0 1 45 1 59 1 93 1 94 1 95 1 110 1 111 1N000c790a8b530fb9N002c14b8e9fe2361N0030257dfea1da75N003d7aa04877ea37N004574c540177cb6N0052035f305a4c25N005e7f8fcb5994e1N0065954cbcaf89ecN008f8e80037de05eN00b9c30178fae78eN015d1dc80182779dN01639fa81f8fcf13N019c28d3459da8b9N01b160ce5e1df1fcN01d1262760b0423fN01fbcc91cd2336bcN02295a1187f0203fN0231a701ae30bd9cN02d773b59f589f5cN031a9854bb9c63cbN0343722ddc83950fN034a08d2a7eb219fN037c75ce7f363e48N03ac3e80a479af53N03e9ffadf34922fcN0412e8486fe44015N0433ba7954c68f34N044a85b1904dfc45N04a0200a563fb66fN05510c70e56b7439N05a4e46c43f12403N05d2a7bfd70244ecN05e9ef430675b77bN0646f4a2b774716dN06bf4807957f4038N06c8af6c623d7552N0700342ea0ffc751N0704cabe0d2082f4N0722c95b2ce3058cN0757793e55b703e1N07a3218fe7111494N07b986be9b53e5e2N07e1afc55a353fc0N07f81286e7ebf607N08ba14d089208023N08c8a3795bd14f5fN08d635c18d55612bN08d7725b4dd625e8N0925dad7dc16567aN093c9d4425fa2e9fN093e84e6f0a816e9N09542f99d4738544N099df69f439b78e2N09df549a1212b12aN0a340817aabef6f9N0aaf58455f981428N0ad61c2cdd39e96aN0aeff4d9d07854e7N0b123c20d0e18bd5N0b359ab09a63d456N0b46078b44acf6b8N0b75370e63751437N0c113bf915e3c14cN0c78d57ce0707eb8N0c839eaff4f798a3N0c8c30e31b4d0d3dN0d098dde79afa32dN0d1f733ffdd5f4b3N0d3aedd02c9464cfN0d3b796508fcd993N0d3d15d9a0251a4aN0d6fac9a13feb49aN0d8d2544f8764473N0dc5b2d43d9a4e0eN0dda7908c96d79fcN0de726d094682dfaN0ded58a6cc70d1d4N0e0bda8fdcc9ddb1N0e1386879e558124N0e2faade7c5f035aN0ebf90597b721394N0eff275280948dcaN0f2659c296ef7f7aN0f27cc7c38c7bdc2N0f560d2bcbd5845bN0f67a362eb61b6f0N0f6d894a7b3733d3N0f767a1992017f44N0f788494e4e59d25N0f97547696d08c8dN0fdff96c9c5c4981N10446a1e63047ba9N1105c1f242a97039N1127414248b9161eN1129e183c626c386N115d4df93ee0308bN11c425349dc61e30N120bd8b780eafd3cN12341ba8f1a5c377N123857dd5faa6495N1259b6e91015da79N125bffb4883d491aN12dcbbdea3627c84N13132063fbbd7daaN132e459bd2644e45N1375fdb5ef6d349dN13ef29ea763493eaN146e75ca5dd5a3e4N146f8ae2aa82f05fN14750ce8a7e17e6cN14ad948bf4f7e2c4N14b27a7eb501885cN1509a289a49f3ac3N153404ff89748c06N153d215c6644e935N154fd036e003dc53N1555e50b0201fa3aN1570baffeeec8480N1581e46f3bce86c1N15e703189719749dN15f9bebf5d4f7f83N161d55da88ed4cb7N164d356240c96accN1663e22a83f48ca3N16714932aef21bb0N1691857c3da08344N169613b1dca79cecN170de4e68ebca90bN17148f7324e264b5N17334677d9affc09N1755b4c96f113c87N1765337b827c7951N1782d11eab2c846dN17a4a8583ddae883N17bbd5c726867220N17c173028e3e58bbN17c41401ace93b1aN1846938179558701N184c253e7bb275a5N1893695019183a74N189b6e9d4b48b920N18a5959f18c819f6N18dba736ee96d904N18dbf145a2e81811N18e45dbad3142856N18e63bf8b4167539N18e8160432689adaN18f09b1b98cdbeffN190d909f476828bcN19108e9d89576d8cN194adea0cef82813N194df94c39f9cd38N195f1d43461edfe2N1967b6f996ce992dN196f96f78e4dacbbN1971b4b933f45584N19c7965b41484e98N19ec4ec16b1cc921N19f9420542d769b9N1a3b6e23a5682df0N1a54d6071b74cdc0N1a8d9add6a8dd9faN1b1f010f57834936N1b321d2a624bc88fN1b39fca438a14e5eN1b3acb57c48d1915N1b6004212fe9f38eN1b92f56054b528eaN1c05a13ca9aacc26N1cb963a575c0eb46N1cc101954327b1f2N1cce82ad90ca886dN1cd3652ffec5bd89N1d186213a2234340N1d2eee5895807f52N1d3a436aee3f991dN1dea174d194b0dfdN1e152cbe7c768a21N1e3f99eca03b96c7N1e59fb5e9eddf819N1e5f178f43b1865dN1e6aa231bb57bae1N1e8a8eb24f37d5e3N1e9625cc36711839N1e98fcef5b5f8098N1e9b9455b97a2791N1ea2ff1bdd8e5bfbN1eaa0d940e718a93N1f018f97e503544bN1f114e12a9c37723N1f257fe8560f9080N1f9c7ec6f9267aa7N1f9cf5d2c5a4bdd9N1fb91a1fa8f24633N1fcd4275b32a6cb1N1fd26f10cc48acdfN1fd4d38868057170N1fddee8cc6ef23b2N1fe2198a8cacc4beN1ff5d07e91ed3499N20098f443816b0daN204d09bb639150e3N205995a9d578ed01N2060207e54de58c6N2066e8edbff95c8bN2074e725b068b0d0N20bde9d699b2f559N20d7464d9190b92bN2107db4f85ac5164N2181951a2e2dcd2aN218c2ce33a3be659N219eb4340c033921N21aad07b261b5b40N21c19726ebd440a8N22279707640a3edfN22b90fc598434709N22c07841f0b6104fN2300454a71a1e744N2333d63142adbafbN23631f1506ea0727N236a7f40cc2bcb87N23acdf4d0961795fN23bd4b67657c55edN2433297ae25e0703N2446362c7c185df7N248f180b810e72ebN24bbd4f4e5125e95N24d0ed654b0e50edN24d90f70a4325613N24e4b0bf1d96b7f3N24f240fe75896500N251435e2518d5723N251f594e6288ebfaN253670af16217a7eN25421dfe7727e9a9N254d7c12ccaa0b7eN255057a585f578c1N25929d8f407399e3N25b8e49ebb8d5563N26146d1c8958f996N2644863bb8ec055bN264b348a2ec91608N264d4c2415798e4dN26b526302af4a69fN26cb672d2568f7b7N26d260a426ddbf73N26da364393ffc7d7N272a07c2a4e581e4N277a07e795579c01N27beed33f77d6e95N27d847e4465e0f29N2808b0d1f86f1ad3N28713b25a3d77b77N2871c59119345438N288f0c2f7e068a60N28930a5a28011611N28a169f1d57ee8a5N28e7b0f4751e9506N28ef5d9d9e78c17fN2900d9ff3b6eaaf1N290a8d20fad291b9N291fe344914efaf6N29a7f726845128bcN29e101217dd8a0b0N29f287420c55395eN2a05fb098cc0ef6fN2a241af9e321b3d0N2a45cd7a3ce2b930N2a4776d1ced7da6fN2a4ed0d33cd3fd41N2af014b1267c2c3dN2b3286dd5dbe9126N2b3bd866729d2923N2b566fd2c87ecb63N2b7d0bfc91468efdN2ba8888d3944669bN2bea2ca6878666dbN2bf063443ebd7280N2c5321b564ea92e8N2c6b9f6124e0e276N2c96061c86543f67N2d10661a72560753N2d293b936d03e27eN2d7112b3db6c9826N2d7bece1a7ec5731N2d909bcaabfa0112N2d969f336f4c8c67N2da8b55b6fb15517N2db541a987446a07N2de41db746908194N2de785c52f85ce4cN2dec8cbd2dd6dc1fN2e4997d43e2ada82N2e66635e0fade6c3N2e7c5ea97a7e1ce6N2e8141f875cac1c5N2f0090ad3660e30bN2f40e0b09a6bf8caN2f442c8bd4df4701N2f52d8a9979991d0N2f785bd4b10795a1N2f87e6d8f41fc5b7N2f8afafe6dda4480N2fa16b9518722998N2fb271071f3138a1N2fb7436b300dc35cN2fc17ff6f15583c6N2fcab34f7d047466N2fefdad27c0b2f73N2ff47fec8c8dd34eN30070b760273ff8cN3057a1d55f83b114N3057af7fa798cd70N30774491f0a65c25N308acb664c38ef36N3092cb78c3095268N311462ae312b80bfN3132a22568d139aeN31638f8839940ffaN316d6e2919163b18N317e237fab125911N31a4b5cc8d25eb3aN31a6a84346f64a49N31b93855fb23ad3dN31ddcb401ac40f04N31ead4f4185f2c1aN31f31ba3d25ccb25N3232dc57b85f876bN323f4cc59cebebd8N325e4206e405a7aaN329073e9967f9edfN32a1aedd0c015967N32c041360ae3f3f9N32ff03933f781767N334835c0958e6536N33a90fe85b7eb51eN33b7b6a9db7a67bdN33c27271709dd2eaN33f6f22477c4c976N3406b1408f7ac5d3N346e7d75b81db17aN349a1de5c3ccdb0fN34a994a59e4febceN34f0855e2c1e8cfeN34fc1d9535b54f29N3512050710588cb2N352b6bea81c1be32N3557f91cc436bc53N3569dba2e7ce7459N3588254e7b5dffa2N3597588dc8c4e7b5N35c4a9221c7d6354N3644cf6dc2a66b6cN3654d39ed987e6d5N36bdaccc60f30a2eN36da459f73b6c52cN36fbab8e85bb57bfN36ffb285746ec67eN37c97f2d3297ac5eN37cd9ec822658444N380179f4438e60ebN3812c7c743573260N388b00ee4ffe6477N388c3e08ee5d5952N389e625ac9def173N38f6d9ab6c87995eN39a3a1d5023b0e0aN39b503b0150ed371N39cc8e0b9b4f6f10N39dcaac2c3985a7fN39dcd741ab9e7a91N39f4362a45b43256N3a16b6a5e55055e7N3a2341a7f3766af6N3a38e3efd4dbe996N3a70334101f1f67cN3aa3141a45952d03N3aaed2ec9c4a5f43N3aee80980c0f5b7fN3b8fba4eb0dcac5fN3ba0c45b198c9f04N3bb5e078d03f8e06N3bc6e7a137910b5aN3bea4f4168063b35N3beff90cbd00773eN3c1d0492affa74e7N3c3220263c181657N3c7fbca604d9a706N3c968e5549f95125N3ca1d7965412f04dN3d1f1b0a09c795b3N3d9db57c8ddeb033N3dce3682736a8898N3e017bfeb175a317N3e08b0092bd3bc48N3e1b30681329c9c7N3e2ff067ff4cfa38N3e650dbb45db0b7eN3eb456a87cb9841cN3ebd77861390f81fN3ec7590b9ecd8ca0N3ef785c414f451b0N3efbfbd7a38bc037N3f0724fa827f3f36N3f3ef08dd3dbffaaN3fb32878932e5e5bN3fea38b95cc4882d"%lxh.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import LiaOrcFF5. (* [comment removed for export] *)
Local Ltac lia_t12 ::= orc_lia_t12. (* [comment removed for export] *)
Local Ltac ff5_rlia ::= orc_ff5_rlia. (* [comment removed for export] *)
Local Ltac ff5_overlap_ctx A2 n2 a len ::= orc_ff5_overlap_ctx A2 n2 a len. (* [comment removed for export] *)
Local Ltac ff5_overlap A2 n2 a len ::= orc_ff5_overlap A2 n2 a len. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_ff5_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.
Ltac2 gd_tbl_A_ecp_mod_p255 () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.LibA.ARt.HST"; "OSSVerify.KrLib.A.AImg.asegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.shiftr"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "OSSVerify.KrLib.A.A_mpi_stmtA.A_MPI_GROW"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.LibA.ARt.HM"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.LibA.ARt.hcs"; "OSSVerify.KrLib.LibA.ARt.htop"; "OSSVerify.KrLib.LibA.ARt.hstkhi"; "OSSVerify.KrLib.LibA.ARt.hflag"; "OSSVerify.KrLib.LibA.ARt.havol"; "OSSVerify.KrLib.LibA.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "OSSVerify.KrLib.LibA.ARt.HK"; "OSSVerify.KrLib.LibA.ARt.fresh_apart"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Cells.C1"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.LibA.ARt.presW"; "OSSVerify.KrLib.LibA.ARt.arl_stklo"; "OSSVerify.KrLib.Lib.Frame.ivl"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "RED.Call.S1P"; "A_ECP_MOD_P255"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "OSSVerify.KrLib.LibA.ALazy.crange"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "RED.Call.EPOST"; "OSSVerify.KrLib.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Spec.Rep.mpi_cells"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.LibA.ARt.wcover"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RED.Call.MIDQ"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "OSSVerify.KrLib.A.A_mpi_read_binary_stmt.mpd_keep"; "OSSVerify.KrLib.A.A_mpi_stmtA.mpd_aobjA"; "OSSVerify.KrLib.LibA.AUnw.uwc"; "OSSVerify.KrLib.LibA.AEvtS.aevtS"; "OSSVerify.KrLib.A.A_mpi_stmtA.mpi_binop_postA"; "OSSVerify.KrLib.P.P_ecp_red.reducer_R"; "OSSVerify.KrLib.A.A_mpi_stmtA.grow_PHI"; "OSSVerify.KrLib.A.A_ecp_stmtA.red_FRn"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "OSSVerify.KrLib.A.A_ecp_stmtA.ecp_reducer_stmtA"; "OSSVerify.KrLib.LibA.ARt.art_layout"; "OSSVerify.KrLib.LibA.ARt.artA"; "OSSVerify.KrLib.A.AImg.asan_img_ok"; "OSSVerify.KrLib.LibA.ARt.arl_uar_got"; "A_UAR_GOT_R"; "OSSVerify.KrLib.LibA.ARt.arl_smalloc"; "A_SMALLOC_1_R"; "OSSVerify.KrLib.LibA.ARt.arl_need_smalloc"; "OSSVerify.KrLib.A.A_mpi_read_binary_stmt.arl_need_rt"; "OSSVerify.KrLib.A.A_mpi_stmtA_sz.mpi_grow_stmtA_sz"; "OSSVerify.KrLib.LibA.ARt.arl_amemset"; "OSSVerify.KrLib.A.A_ecp_red_lib.A_ASAN_MEMSET_EC"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.LibA.ARt.arl_L"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"].


Definition A_SMALLOC_1_R : Z := 0x52af8.          (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_UAR_GOT_R : Z := 0x0f2ae8.           (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_ECP_MOD_P255 : Z := 0xd3dbc.         (* [comment removed for export] *)

Section RED.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT_R.
  Hypothesis SM1 : arl_smalloc R 1 = A_SMALLOC_1_R.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis GROW : mpi_grow_stmtA_sz asegs R HIA A_MPI_GROW.
  Hypothesis AMS : arl_amemset R = A_ASAN_MEMSET_EC.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis ROIMG : forall a, ro_addr asegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (dX : mpd) (lo d : Z).
  Local Notation X := (md_addr dX).
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 320 - arl_need_ecp R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF + 1 <= 512)%nat.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT_R in UARG; unfold A_SMALLOC_1_R in SM1;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (arl_need_ecp_rt R) as NER; pose proof (arl_need_ecp_smalloc R) as NES;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation FSHXL :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248);
     C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Local Notation SAVEL := [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Definition S1P : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p255 ()) "Lms,$0.(1.$2.LFB,$2.(1.$2.Lsp1,$2.(1.(3.$4.VR,VHIA,)Lh1,(3.$4.VR,VHIA,)(1.P,(5.&40.)(6.(5.&8.))Lm1,P,(5.&40.)(6.(5.&8.))(1.(5.&40.)Lt0,(5.&40.)(1.(5.&40.)Lt1,(5.&40.)(1.(5.&40.)Lt2,(5.&40.)(1.(5.&40.)La2,(5.&40.)(1.(5.&40.)La3,(5.&40.)(1.(5.&40.)La4,(5.&40.)(1.(5.&40.)La5,(5.&40.)(1.(5.&40.)La6,(5.&40.)(1.(5.&40.)La7,(5.&40.)(1.(5.&40.)Lt3,(5.&40.)(1.(5.&40.)Lt4,(5.&40.)(1.(5.&40.)Lt5,(5.&40.)(1.(5.&40.)Lt6,(5.&40.)(1.(5.&40.)Lw0,(5.&40.)(1.(5.&40.)Lw1,(5.&40.)(1.(5.&40.)Lw2,(5.&40.)(1.(7.(5.&8.))Ljmp,(7.(5.&8.))(8.(9.$0.R16.(:.(;.(<.&40.+=3>=8.)(<.&40.R14.)Vgp,Vtp,R11.R10.R?.Vsp,(<.&40.R14.)(<.&40.(=.VdX,))(<.&40.+10.)R>.R=.R<.R;.R:.R9.(<.&40.R15.)(<.&40.(=.VdX,))Vs4,Vs5,Vs6,(<.&40.(>.(?.R15.+3.)(10.(11.VR,))))(<.&40.R15.)(<.&40.(10.(11.VR,)))Vs10,Vs11,R8.R7.R6.R5.)VF,(<.&40.$12.)Vfc,(13.(5.&40.))R12.(14.$4.)))(8.(8.(15.(16.(17.&40.Vsp,)+90.)R14.)(15.R14.(16.(17.&40.Vsp,)+80.)))(8.(9.$2.(18.R14.+20.)=)(8.(19.$4.VR,VHIA,R13.VLB,(1:.(1;.$2.$2.)(1<.$2.$2.R15.+80.)VLF,)R12.)(8.(9.P,$2.Sp(1=.$4.VR,VHIA,R13.)(1=.$4.VR,VHIA,Vh,))(8.(9.$2.(1>.$4.VR,VHIA,R13.)(1>.$4.VR,VHIA,Vh,))(8.(9.$2.(1?.$4.VR,VHIA,R13.)(1?.$4.VR,VHIA,Vh,))(8.(9.$2.(20.$4.VR,VHIA,R13.)(20.$4.VR,VHIA,Vh,))(8.(9.$2.(21.$4.VR,VHIA,R13.)(21.$4.VR,VHIA,Vh,))(8.(9.$2.(22.$4.VR,VHIA,R13.)(22.$4.VR,VHIA,Vh,))(8.Pmo,$23.(24.(25.$4.VR,VHIA,R14.R1.)(25.$4.VR,VHIA,Vh,R1.))(8.(9.$2.(18.R15.+40.)=)(8.(26.VR,VLB,VLF,R15.+80.)(8.(27.$4.R12.R15.(1:.$28.(29.R4.)(1:.$28.(29.R3.)(1:.$28.(29.R2.)(2:.$28.)))))(8.(27.$4.R12.(>.R15.+20.)(1:.$28.(2;.#20.R1.)(2:.$28.)))(8.(27.$4.R12.(>.(?.R15.+3.)(10.(11.VR,)))(1:.$28.(2<.(<.&8.+?1.))(1:.$28.(2<.(<.&8.+?1.))(1:.$28.(2<.(<.&8.+?1.))(1:.$28.(2<.(<.&8.+?1.))(1:.$28.(2<.(<.&8.+?8.))(1:.$28.(2<.(<.&8.+?8.))(1:.$28.(2<.(<.&8.+?8.))(1:.$28.(2<.(<.&8.+?8.))(1:.$28.(2<.(<.&8.+?3.))(1:.$28.(2<.(<.&8.+?3.))(1:.$28.(2<.(<.&8.+?3.))(1:.$28.(2<.(<.&8.+?3.))(1:.$28.(2<.(<.&8.=))(1:.$28.(2<.(<.&8.=))(1:.$28.(2<.(<.&8.=))(1:.$28.(2<.(<.&8.=))(2:.$28.))))))))))))))))))(8.(27.$4.R12.(>.(17.&40.Vsp,)-60.)(1:.$28.(29.Vs10,)(1:.$28.(29.Vs9,)(1:.$28.(29.Vs8,)(1:.$28.(29.Vs7,)(1:.$28.(29.Vs6,)(1:.$28.(29.Vs5,)(1:.$28.(29.Vs4,)(1:.$28.(29.Vs3,)(1:.$28.(29.Vs2,)(1:.$28.(29.Vs1,)(1:.$28.(29.Vs0,)(1:.$28.(29.Vra,)(2:.$28.))))))))))))))(8.(27.$4.R12.(>.R14.+18.)(1:.$28.(29.(<.&40.R15.))(2:.$28.)))(8.(2=.$4.R12.R14.(>.R14.+18.))(8.(2=.$4.R12.(>.R14.+20.)(>.(17.&40.Vsp,)-60.))(8.(2=.$4.R12.Vlo,R14.)(8.(2>.$4.R12.)(2?.$4.VR,VHIA,Vh,VLB,VLF,(17.&40.Vsp,)(30.VR,)(2:.$31.)Vm,R12.))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01>0@D18607476203.116D19965288045.118D2457697676.144 D29569067328.144D32458983511.144D32604263317.145D3375410824.143 D45716866873.143D50254960491.117D50254960491.121D54591688987.120D560335984.90   D62011770190.145D62012280210.90 D6395731754.121 D65360381163.119D68407129291.143D6911780558.143 L10647102888.2  L10989370580.8  L12583266295.21 L13424450160.128L15629995721.2  L19546883925.128L19980016842.11 L19980537034.6  L2275137097.0   L24131365019.124L27188209011.148L29738741675.1  L33483560980.12 L33485826452.1  L33485826452.3  L38431952710.3  L38996969702.80 L43061657906.78 L43139178913.0  L43554043994.139L44847795975.1  L46938848127.1  L47230721790.124L48117620902.125L48117620911.79 L55351494680.13 L57355539152.126L58789625892.5  L58790154276.11 L59308677456.14 L59351324120.1  L61437265048.2  L62018535662.1  L6395777846.140 L6912107244.124 L9356559645.12  Q10533598597.92 Q10592386206.149Q1530342990.121 Q23937998252.92 Q24131365019.150Q24137657765.148Q30223088059.149Q32440833928.148Q35653441506.73 Q40271359350.121Q47241206720.92 Q48117620904.149Q48132302231.148Q56531220660.149Q59310664043.148Q59310664043.92 Q59321150548.149Q60109315147.73 Q6192914196.115 Q62012212072.121Q62022254708.92 Q6897428434.148 Q6912107244.150 Q9356560156.102 00000100200300J00a01A01B01Y01Z01[01\02402M02_03703803903P03X04504]05C05K05l06D06E06F06V07207607707807907E07P08008108H08L08Q08d09O0::0:J0:K0:L0:e0:o0;40;<0;?0;Z0;j0<Y0<k0=;0=S0>40>D0>T0>d0>e0?D0?Y0?l0@W0AB0AC0AD0AE0AF0AW0Ah0B70BF0BV0Bf0C<FFFS2LF2sp3LFB4lxHn3sp12FBS2LF2sp3LFB4lxHn3sp12FBS1R3HIA2LF2sp3LFB4lxHn3sp12h12FBFS2LF2sp3LFB4lxHn3sp12FBFFFS1R3HIA1h2LF2sp3LFB4lxHnS1R2LF2sp3LFB4lxHn3sp12FBS1R2LF2sp3LFB4lxHnS2LF2sp3LFB4lxHn3sp13H13FFS2LF2sp3LFB4lxHn3sp12FBS2LF3LFBS1R3NS12sp2lo3SLO3NES3sp13SP1S2sp2r03SPA3sp11r4SP1M3H123H131q1H2q02H4S2LF2sp3LFB3SPR4lxHn3sp14SP1R2FB2F02F8S2LF3LFBS2LF2sp3LFB3SPR4lxHn3sp12FB2F02F8S1R3HIA1h2sp3TOP3sp13SP1FSS2LF3LFB4lxHn2FBS2LF2sp3LFB4lxHn3sp12FB1c2HcS2FBFFFS2sp3sp13SP1S2LF2sp3LFBS1R3NS12LF2sp2lo3SLO3LFB3NES3SPRSS2LF2sp3LFB4lxHn3sp12FBS2spS3sp1S1R2LF3LFB3ALO4lxHnS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NER4lxHnS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NER4lxHnS1R3ACV2FB2F02F1FFS1R2sp2lo3SLO3NES3sp13SP1S2FB2Kb2F0S3sp1S2LF3LFBS1RS2LF2sp3LFB4lxHn3sp13H132FBS2LF3LFB4lxHn2FBS1R5NEEDR2sp2lo3LOS3SLO3ALO3ACV3NER3SPR3sp13SP1S1R2LF2sp3LFB4lxHnS2LF3LFB4lxHn2FBS2LF2sp3LFB4lxHn3sp13H13S1R3HIA1h2LF2sp3TOP3LFB4HTOP4lxHnS2LF3LFB4lxHn2FBS2LF3LFB4lxHn2FBS2LF3LFB4lxHn2FBFS1R3HIA1h2LF2sp2lo3TOP3LFB4HTOPS1R3HIA1h2LF3LFB4lxHnS1R2LF3LFB3ALO4lxHnS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NER4lxHnS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NER4lxHnFFFFS1R2LF2lo3LOS3LFBS2LF3LFB4lxHn3sp1S1R2LF3LFB4lxHnS1R2LF3LFB4lxHnS2LF3LFB4lxHn2FBS2LF3LFB4lxHn2FBS2LF3LFB4lxHn3sp14SP1R". (* [comment removed for export] *)
  Lemma pro_walk : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p255 ()) "Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Pa1,(5.&40.)Pa2,(5.&40.)Pa3,(5.&40.)Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)P,(19.$4.VR,VHIA,Vh,VLB,VLF,Vm,)P,(2=.$4.Vm,Vlo,(17.&40.Vsp,))P,(2>.$4.Vm,)(32.$4.(11.VR,)(1=.$4.VR,VHIA,Vh,)$33.(:.(;.Vra,Vsp,Vgp,Vtp,R11.R10.R?.Vs0,Vs1,(<.&40.(=.VdX,))R>.R=.R<.R;.R:.R9.R8.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R7.R6.R5.R4.)VF,(<.&40.$34.)Vfc,(13.(5.&40.))Vm,(14.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros HH ST MI. unfold A_ECP_MOD_P255. rt_facts.
    pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
    pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
    pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [] HH ltac:(clear; lia)) as PRES.
    flat constr:(IMG') 3%nat. flclear IMG'. intros EGOT ELO EHI.
    (* [comment removed for export] *)
    zstep. carve_frame 128%nat ST.
    (* [comment removed for export] *)
    pose proof (hm_abase asegs R HIA h LB LF m HH) as AB.
    pose proof (abase_got _ _ _ AB) as GOT; pose proof (abase_gsb _ _ _ AB) as GSB.
    flat constr:((hm_auar asegs R HIA h LB LF m HH)) 2%nat. intros UGOT UFLAG.
    pose proof (hm_flag_img asegs R HIA h LB LF m HH) as FLIMG.
    rewrite EGOT in GOT. rewrite UARG in UGOT.
    pose (lxi := lxA_img (arl_AL R) IMG).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52af8] [] 80%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    clear GOT GSB UGOT UFLAG AB FLIMG ST.
    lx_align32 sp1.
    match goal with Hm : sp1 mod 32 = 0 |- _ => rename Hm into SP1M end.
    assert (SP1 : bv_unsigned sp - 144 <= sp1 <= bv_unsigned sp - 128)
      by (match goal with H1 : 0 <= sp1 + _, H2 : 0 <= - sp1 + _ |- _ => clear - H1 H2 SP1M SPA SPR end; Z.div_mod_to_equations; lia).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR NER; lia).
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
    match goal with H : stk _ m1 lo (bv_unsigned sp + -128) |- _ => rename H into ST end.
    destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -128) ST ltac:(clear - SP1 SLO NS1 NES; lia)) as [ST1 ST2]. clear ST.
    replace (Z_to_bv 64 338680) with (Z_to_bv 64 (arl_smalloc R 1)) by (rewrite SM1; reflexivity).
    lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
    callrt sp1 (eapply (art_smalloc asegs R HIA 1) with (lo := lo) (sz := 96); rewrite ?(unsigned_lit sp1) by exact SP1R;
                first [ exact HHc | reflexivity | exact TPV | exact LOS | exact ST1
                | clear - LFB; lia
                | clear - SLO SP1 TOP NS1 NES; lia
                | clear; lia
                | assumption | match goal with |- ?g => idtac "SMPRE-LEFT:" g end ])
    end.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "SMALLOC-LEFT:" g end.
    clear ST1.
    lazymatch goal with H : presA _ _ _ _ _ _ _ _ m1 ?m2 |- _ => rename H into HP1; rename m2 into m2' end.
    clear HH.
    presA_transport HP1. clear HP1.
    lazymatch goal with H : exists h' : HST _ _ _, _ |- _ =>
      (flat constr:(H) 9%nat; flclear H; intros h1 Ehcs Ehtop Estk Eflag Evol Efr HKI SMC) end.
    flat constr:(SMC) 8%nat. flclear SMC. intros FB junkf Ea0 F64 FRSH HH1 FRM FSH. lazymatch type of Ea0 with ?x = _ => subst x end.
    cbn [Z.mul Z.pow Z.pow_pos Pos.iter Pos.mul Z.to_nat Pos.to_nat Pos.iter_op Nat.add Nat.mul] in FRSH, HH1, FRM, FSH.
    (* [comment removed for export] *)
    zstep. zstep.
    zstep. if_cases Kb; zify_cond Kb.
    2:{ exfalso. flat constr:(FRSH) 3%nat. flclear FRSH. intros F0 F1 _.
        try (change 18446744073709551615 with (Z.ones 64) in Kb; rewrite Z.land_ones in Kb by (clear; lia)).
        rewrite ?Z.mod_small in Kb by (clear - F0 F1 ALO ACV LOS SLO SPR NER NEEDR; lia). clear - Kb F0 F1 ALO ACV LOS SLO SPR NER NEEDR. lia. }
    clear Kb.
    change (64 * 2 ^ 1) with 128 in *. change (8 * 2 ^ 1) with 16 in FSH. change (Z.to_nat 128) with 128%nat in FRM. change (Z.to_nat 16) with 16%nat in FSH.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
    (* [comment removed for export] *)
    destruct (frame_factsA R HIA CS h1 LB LF m3 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (128 / 8) with 16 in SBND, APS. change (128 - 40) with 88 in IND.
    pose proof (art_stk_high asegs R HIA) as STKH.
    (* [comment removed for export] *)
    lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -128) _ |- _ => chunk_split FRx 2%nat FRa SAVE end.
    replace (bv_unsigned sp + -128 + 32) with (bv_unsigned sp + -96) in SAVE by (clear; lia).
    lazymatch goal with STx : stk _ m3 sp1 (bv_unsigned sp + -128) |- _ => release_frame FRa STx (bv_unsigned sp + -96); rename STx into STJ end.
    destruct (stk_split asegs m3 sp1 (sp1 + 32) (bv_unsigned sp + -96) STJ ltac:(clear - SP1; lia)) as [STlo SThi]. clear STJ.
    destruct (stk_carve asegs m3 sp1 (sp1 + 32) 8 STlo ltac:(clear; lia)) as [STlo' [jslot SLOT]].
    replace (sp1 + 32 - Z.of_nat 8) with (sp1 + 24) in STlo', SLOT by (clear; lia). clear STlo. rename STlo' into STlo.
    cb8_to_c8 SLOT (@nil cell).
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs m3 FB [] 128 junkf [] [8; 8; 8; 8; 32; 64]%nat) in FRM; [| reflexivity].
    cbn [mk_CB_cells app] in FRM.
    chunk_split FRM 3%nat FHD FRM1. chunk_split FRM1 1%nat FLNK FRM2. chunk_split FRM2 1%nat MPB FREST.
    lazymatch type of MPB with rw_cells _ _ ?a _ => replace a with (FB + 32) in MPB by (clear; lia) end.
    clear FLNK FREST.
    cb8_to_c8 FHD (@nil cell).
    cbn [zcells] in FSH.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [A_MPI_GROW] [] 80%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    lazymatch type of MPB with rw_cells _ _ _ [CB _ ?j] => set (jmp := j) in MPB end.
    apply evtA_done. unfold S1P.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx end.
    do 13 eexists.
    lazymatch goal with H : rw_cells _ ?mx FB [C8 ?a; C8 ?b; C8 ?c] |- context [MS _ _ _ _ _ ?mx _] => exists a, b, c end. exists jmp.
    split; [reflexivity|].
    repeat (split; [first [eassumption | exact SP1 | exact SP1M] |]). first [eassumption | idtac].
    all: match goal with |- ?g => idtac "PRO-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition EPOST (h3 : HST asegs R HIA) (LBa LBb : list blk) (m0 m2x : mem) (WA WB : list ivl) (r : Z)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p255 ()) "Lms,$0.(1.P,(5.&40.)(6.(5.&8.))Lm',P,(5.&40.)(6.(5.&8.))(1.(3.$4.VR,VHIA,)Lh4,(3.$4.VR,VHIA,)(1.(5.&40.)Lt0,(5.&40.)(1.(5.&40.)Lt1,(5.&40.)(1.(5.&40.)Lt2,(5.&40.)(1.(5.&40.)La1,(5.&40.)(1.(5.&40.)La2,(5.&40.)(1.(5.&40.)La3,(5.&40.)(1.(5.&40.)La4,(5.&40.)(1.(5.&40.)La5,(5.&40.)(1.(5.&40.)La6,(5.&40.)(1.(5.&40.)La7,(5.&40.)(1.(5.&40.)Lt3,(5.&40.)(1.(5.&40.)Lt4,(5.&40.)(1.(5.&40.)Lt5,(5.&40.)(1.(5.&40.)Lt6,(5.&40.)(8.(9.$0.R11.(:.(;.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(<.&40.O1.)R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(35.Vra,)Vfc,(13.(5.&40.))R10.(14.$4.)))(8.(2>.$4.R10.)(8.(2=.$4.R10.Vlo,(17.&40.Vsp,))(8.(2?.$4.VR,VHIA,O8.O7.VLF,(17.&40.Vsp,)(30.VR,)O3.O5.R10.)(8.(2?.$4.VR,VHIA,O8.O6.VLF,(17.&40.Vsp,)(30.VR,)O2.O4.R10.)(8.(9.P,$2.Sp(1=.$4.VR,VHIA,R?.)(1=.$4.VR,VHIA,O8.))(8.(9.$2.(1>.$4.VR,VHIA,R?.)(1>.$4.VR,VHIA,O8.))(8.(9.$2.(1?.$4.VR,VHIA,R?.)(1?.$4.VR,VHIA,O8.))(8.(9.$2.(20.$4.VR,VHIA,R?.)(20.$4.VR,VHIA,O8.))(8.(9.$2.(21.$4.VR,VHIA,R?.)(21.$4.VR,VHIA,O8.))(8.(9.$2.(22.$4.VR,VHIA,R?.)(22.$4.VR,VHIA,O8.))(8.Pmo,$23.(24.(25.$4.VR,VHIA,R10.R1.)(25.$4.VR,VHIA,O8.R1.))(19.$4.VR,VHIA,R?.O6.VLF,R10.)))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01L0@D10777814275.139D2457561357.172 D2459793318.139 D32452690557.139D3375480366.172 D3376374386.138 D38334478296.172D43016287773.140D45717900227.138D62011770188.140D62012166606.172D68407932977.138D6911601204.138 L10048050688.9  L13312155929.172L13424450162.122L13424450175.126L17832996913.175L19546883927.122L19546883930.126L2275137097.0   L24131365012.122L24131365017.118L24433106123.7  L27188209011.143L35655538631.10 L39332637397.0  L39540652971.1  L39716638549.0  L4022451686.1   L42411609006.0  L47801025711.138L47801036031.138L48117620903.123L48117620904.119L48132302223.139L48132302231.138L50790761713.7  L5162232212.2   L57570196295.2  L60098763854.3  L62018535662.1  L6899380056.1   L6912107235.122 L6912107246.118 L9356559676.12  P5152549648.176 P57577290179.177Q10592386204.144Q10592386207.148Q12191695080.174Q12191695088.175Q21715049793.175Q21715049817.174Q21721340005.145Q21721340008.149Q22358563588.147Q24131365012.149Q24131365017.145Q24137657765.143Q24137657789.147Q30132769282.175Q30147450662.145Q30223088057.144Q30223088058.148Q30871588746.175Q31314676345.143Q34796740410.148Q4125667684.174 Q4279611329.175 Q48117620905.148Q48117620906.144Q48132302223.147Q48132302231.143Q52741535643.175Q5935758158.175 Q59666529497.174Q59668625896.149Q60382659730.149Q60382659743.145Q60397339043.174Q60397339067.175Q64133651577.175Q67397950268.144Q6897428426.147 Q6897428434.143 Q6912107235.149 Q6912107246.145 Q7902384038.174 Q7902384062.175 Q7917062807.149 Q7917062810.145 00000G00H00I00`00a00b01B01b02902R02k02l03C03f04B04h05N05O06006Q06R06b07207M07i08B08C08G08H08L08M08N08O09:09e0:P0;;0;V0;W0;X0;b0;e0;i0<90<I0=80=90=:0=J0=Z0=[0=\0=]0=^0=_0=`0=a0>10>A0>Q0>a0>b0>c0?30?C0?X0?Y0?Z0?l0@>0@i0AT0B?0Bj0C?0CQ0CR0CS0CT0CU0CV0CW0Ci0Cj0D:0DJ0DZ0Dj0EC0E\0F50FNS2LF2sp3LFB2FB3sp14lxHnFFS2LF2sp3LFB2FB3sp14lxHnFFS1R3HIA2LF2sp3LFB2FB3sp14lxHn2h4S1R3HIA2LF2sp3LFB2h32FB3sp14lxHnS2LF2sp3LFB2FB3sp14lxHnS1R2LF2sp3LFB2FB3sp14lxHnS1R2LF2sp3LFB2FB3sp14lxHnFS2LF2sp3LFB2FB3sp14lxHnS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13NERS2LF2sp3LFB2FB3sp14lxHn1p2PBS2LF2sp3LFB2FB3sp13SPR4SP1R2F82F04lxHnS2LF2sp3LFB2FB3sp13SPR4SP1R2F82F04lxHnFS2LF2sp3LFB2FB3sp13SPR2F82F04lxHnS2LF2sp3LFB2FB3sp13SPR2F82F04lxHnSS2LF3LFB2FB4lxHnS2LF3LFB2FB4lxHnS1R5NEEDR2sp2lo3LOS3SLO3NERS2LF2sp3LFB2FB3sp14lxHn1c2HcS1R3HIA1h2sp2lo3TOP5HTOP3SS2FBSS2FBSFFS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NER4lxHnS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NER4lxHnS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NER4lxHnS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NER4lxHnS1R5NEEDR2sp2lo3LOS3SLO3NERFFS1R2lo3LOSS1RS2FBS2LF3LFB2FB4lxHnS2LF3LFB2FB4lxHnS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3NER3SPRFFS2LF3LFB2FB4lxHnS2LF3LFB2FB4lxHnFFFFFFFS2LF3LFB2FB4lxHnS2LF3LFB2FB4lxHnS2LF3LFB2FB4lxHnS2LF3LFB2FB4lxHnFFS2LF3LFB2FB4lxHnS2LF3LFB2FB4lxHnS2LF3LFB2FB4lxHn1p2PBFFS2LF3LFB4lxHn1p2PBS2LF3LFB4lxHn1p2PBS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NER4lxHnS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NER4lxHnS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NER4lxHnS1R5NEEDR2LF2sp2lo3LOS3SLO3LFB3ALO3NER4lxHnS2LF3LFB2FB4lxHn1p2PBS2LF3LFB4lxHn1p2PBFFFFFFS2LF3LFB4lxHn1p2PBFS2LF3LFB2FB4lxHnS2LF3LFB2FB4lxHnS2LF3LFB2FB4lxHnS2LF3LFB2FB4lxHnS1R2LF3LFB2FB3ALO2F14lxHnS1R2LF3LFB2FB3ALO2F14lxHnS1R2LF3LFB2FB3ALO2F14lxHnS1R2LF3LFB2FB3ALO2F14lxHn". (* [comment removed for export] *)
  Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p255 ()) "Ph3,(3.$4.VR,VHIA,)PLBa,(7.$36.)PLBb,(7.$36.)Pm0,P,(5.&40.)(6.(5.&8.))Pm2x,P,(5.&40.)(6.(5.&8.))Pmm,P,(5.&40.)(6.(5.&8.))PWA,(7.$31.)PWB,(7.$31.)PFB,$2.Psp1,$2.Pxra,(5.&40.)Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Pa1,(5.&40.)Pa2,(5.&40.)Pa3,(5.&40.)Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)Ps3v,(5.&40.)Ps4v,(5.&40.)Ps5v,(5.&40.)Ps6v,(5.&40.)Ps9v,(5.&40.)Ps10v,(5.&40.)Pw0,(5.&40.)Pw1,(5.&40.)Pw2,(5.&40.)Pr,$2.P,(19.$4.VR,VHIA,R23.R21.(1:.(1;.$2.$2.)(1<.$2.$2.R1;.+80.)VLF,)R1>.)P,Px,$2.P,(1=.$4.VR,VHIA,Vh,R1.)(1=.$4.VR,VHIA,R26.R2.)P,(9.$2.(1>.$4.VR,VHIA,R25.)(1>.$4.VR,VHIA,Vh,))P,(9.$2.(1?.$4.VR,VHIA,R26.)(1?.$4.VR,VHIA,Vh,))P,(8.(15.(16.(17.&40.Vsp,)+90.)R1>.)(15.R1>.(16.(17.&40.Vsp,)+80.)))P,(9.$2.(18.R1?.+20.)=)P,(9.$2.(18.R21.+40.)=)P,(26.VR,R29.VLF,R22.+80.)P,(26.VR,R29.VLF,R23.+80.)P,(37.(1=.$4.VR,VHIA,Vh,)R24.+80.)P,PB,$2.Pj,$2.P,(38.(1;.$2.$2.)(1<.$2.$2.R2.R1.)VLF,)(39.(15.(>.R28.+80.)R3.)(15.(>.R3.R2.)R28.))P,Pb',$36.P,(38.$36.R1.R2>.)(38.$36.R2.R2>.)P,(27.$4.R2:.R27.(1:.$28.(29.R10.)(1:.$28.(29.R?.)(1:.$28.(29.R>.)(2:.$28.)))))P,(27.$4.R2;.(>.(?.R28.+3.)(10.(11.VR,)))(1:.$28.(2<.(<.&8.+?1.))(1:.$28.(2<.(<.&8.+?1.))(1:.$28.(2<.(<.&8.+?1.))(1:.$28.(2<.(<.&8.+?1.))(1:.$28.(2<.(<.&8.+?8.))(1:.$28.(2<.(<.&8.+?8.))(1:.$28.(2<.(<.&8.+?8.))(1:.$28.(2<.(<.&8.+?8.))(1:.$28.(2<.(<.&8.+?3.))(1:.$28.(2<.(<.&8.+?3.))(1:.$28.(2<.(<.&8.+?3.))(1:.$28.(2<.(<.&8.+?3.))(1:.$28.(2<.(<.&8.=))(1:.$28.(2<.(<.&8.=))(1:.$28.(2<.(<.&8.=))(1:.$28.(2<.(<.&8.=))(2:.$28.))))))))))))))))))P,(27.$4.R2<.(>.(17.&40.Vsp,)-60.)(1:.$28.(29.Vs10,)(1:.$28.(29.Vs9,)(1:.$28.(29.Vs8,)(1:.$28.(29.Vs7,)(1:.$28.(29.Vs6,)(1:.$28.(29.Vs5,)(1:.$28.(29.Vs4,)(1:.$28.(29.Vs3,)(1:.$28.(29.Vs2,)(1:.$28.(29.Vs1,)(1:.$28.(29.Vs0,)(1:.$28.(29.Vra,)(2:.$28.))))))))))))))P,(27.$4.R2=.(>.R29.+18.)(1:.$28.(29.(<.&40.R2:.))(2:.$28.)))P,(2=.$4.R2>.R2:.(>.R2:.+18.))P,(2=.$4.R2?.(>.R2;.+20.)(>.(17.&40.Vsp,)-60.))P,(2=.$4.R30.Vlo,R2<.)P,(2>.$4.R31.)P,(2?.$4.VR,VHIA,R37.R36.VLF,(17.&40.Vsp,)(30.VR,)R31.R34.R32.)P,(2?.$4.VR,VHIA,R38.R36.VLF,(17.&40.Vsp,)(30.VR,)R31.R34.R33.)(32.$4.(11.VR,)(1=.$4.VR,VHIA,R39.)(3:.R39.R38.R37.R36.R35.R33.R32.R17.)(:.(;.R2?.(<.&40.R30.)Vgp,Vtp,R2>.R2=.R2<.Vsp,(<.&40.R30.)(<.&40.R17.)R2;.R2:.R29.R28.R27.R26.R25.(<.&40.R31.)R20.R1?.R1>.R1=.(<.&40.(>.(?.R31.+3.)(10.(11.VR,))))(<.&40.R31.)R1<.R1;.Vs11,R24.R23.R22.R21.)VF,(<.&40.+=3?;8.)Vfc,(13.(5.&40.))R34.(14.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros until r. intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB AP SUBK FHD FSH SAVE SLOT ST24 SThi STlo MI PRES PRES2.
    rt_facts.
    pose proof (hcs_ok asegs R HIA h3) as CSOK3.
    pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3. rewrite ET3, ES3 in HTOP3.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR NER; lia).
    assert (CFB3 : crange (hcs asegs R HIA h3) FB 128) by (eapply crange_mono; [exact HCS3| exact CFB]).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NEEDR NER TOP HTOP3; lia]).
    assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS3| exact SCS]).
    assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS3| exact SCS0]).
    destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 LBb LF mm FB 128 lo HH3 eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (_ & INF & INH3 & IND3 & _ & _ & F8 & FBLO & SBND & APS). change (128 / 8) with 16 in SBND, APS.
    pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'. flat constr:(FRSH') 4%nat. flclear FRSH'. intros F0 F1 F2 F3.
    pose proof (art_stk_high asegs R HIA) as STKH.
    pose proof (hm_wlow asegs R HIA h3 _ _ _ HH3) as WL3.
    (* [comment removed for export] *)
    pose (lxi := lxA_img (arl_AL R) IMG).
    assert (SFF : shadow_free R LBa LF (arl_stklo R) (hstkhi asegs R HIA h3) FB 128)
      by (eapply shadow_free_fresh; [exact FRSH | exact (proj2 (proj2 (proj2 PRES))) | clear; lia | clear; lia | exact ALO | exact AP]).
    assert (SFF2 : shadow_free R LBb LF (arl_stklo R) (hstkhi asegs R HIA h3) FB 128)
      by (eapply shadow_free_fresh; [exact FRSH3 | exact (proj2 (proj2 (proj2 PRES2))) | clear; lia | clear; lia | exact ALO | exact AP]).
    lx_pre. lxe_pose. lx_run_tac (PLAN [0xd400c] [] 80%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
    (* [comment removed for export] *)
    match goal with H : HM _ _ _ h3 _ _ me |- _ => rename H into HHe end.
    destruct (hm_fake_free asegs R HIA h3 LBb ((FB, 128) :: LF) me FB 128 HHe ltac:(left; reflexivity))
      as (p & h4 & ROp & [old Hold] & CRp & NCp & NSp & HM4 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4).
    replace (FB + 128 - 8) with (FB + 120) in ROp by (clear; lia).
    pose proof (rw_cells_bound _ _ _ _ Hold) as PB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
    pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp. clear Hold.
    assert (SUB1 : forall b', In b' (LBa ++ fdata LF) -> In b' (LBb ++ fdata ((FB, 128) :: LF))).
    { intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply SUBK; exact Hb| right].
      eapply fdata_incl; [| exact Hb]. intros fb Hfb. right. exact Hfb. }
    assert (SUB2 : forall b', In b' (LBb ++ fdata LF) -> In b' (LBb ++ fdata ((FB, 128) :: LF))) by (intros b' Hb; apply fdata_cons_sub; exact Hb).
    assert (NP5 : bv_unsigned sp + -96 + 96 <= p \/ p + 1 <= bv_unsigned sp + -96).
    { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; clear - SLO LOS NEEDR NER; lia| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
    assert (NP6 : sp1 + 24 + 8 <= p \/ p + 1 <= sp1 + 24).
    { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; clear - SLO LOS SP1 NEEDR NER; lia| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
    assert (WCp1 : wcover R LBa LF (bv_unsigned sp) WA p 1) by (eapply wcover_nc; [exact NCp| exact SUB1| clear - LOS SLO NEEDR NER; lia]).
    assert (WCp2 : wcover R LBb LF (bv_unsigned sp) WB p 1) by (eapply wcover_nc; [exact NCp| exact SUB2| clear - LOS SLO NEEDR NER; lia]).
    clear HHe NCp NSp FHD.
    repeat match goal with H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL) _ |- _ => clear H | H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL + _) _ |- _ => clear H end.
    zstep. zstep.
    fake_free_done p HSp.
    (* [comment removed for export] *)
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [] [] 40%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mf end.
    cbn [lb_remove fst Z.eqb] in HM4. rewrite Z.eqb_refl in HM4.
    apply evtA_done. unfold EPOST.
    exists mf, h4. do 14 eexists.
    split; [reflexivity|].
    split; [assumption|].
    split; [assumption|].   (* [comment removed for export] *)
    split; [exact PRES|]. split; [exact PRES2|].
    split; [rewrite E4cs; reflexivity|]. split; [exact E4top|]. split; [exact E4stk|]. split; [exact E4flag|]. split; [exact E4vol|]. split; [exact E4fr|].
    split; [exact HKI4|]. exact HM4.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition MIDQ (h3 : HST asegs R HIA) (LBa LBb : list blk) (m0 mm : mem) (WA : list ivl) (FB sp1 : Z) (cX : list cell)
      (p3 : Z) (xs3 : list word) (r : Z) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p255 ()) "Lms,$0.(1.P,(5.&40.)(6.(5.&8.))Lmm',P,(5.&40.)(6.(5.&8.))(1.(7.(5.&40.))Lxs',(7.(5.&40.))(1.(5.&40.)Lxra,(5.&40.)(1.(5.&40.)Lt0,(5.&40.)(1.(5.&40.)Lt1,(5.&40.)(1.(5.&40.)Lt2,(5.&40.)(1.(5.&40.)La1,(5.&40.)(1.(5.&40.)La2,(5.&40.)(1.(5.&40.)La3,(5.&40.)(1.(5.&40.)La4,(5.&40.)(1.(5.&40.)La5,(5.&40.)(1.(5.&40.)La6,(5.&40.)(1.(5.&40.)La7,(5.&40.)(1.(5.&40.)Lt3,(5.&40.)(1.(5.&40.)Lt4,(5.&40.)(1.(5.&40.)Lt5,(5.&40.)(1.(5.&40.)Lt6,(5.&40.)(1.(5.&40.)Ls3v,(5.&40.)(1.(5.&40.)Ls4v,(5.&40.)(1.(5.&40.)Ls5v,(5.&40.)(1.(5.&40.)Ls6v,(5.&40.)(1.(5.&40.)Ls9v,(5.&40.)(1.(5.&40.)Ls10v,(5.&40.)(1.(5.&40.)Lw0,(5.&40.)(1.(5.&40.)Lw1,(5.&40.)(1.(5.&40.)Lw2,(5.&40.)(8.(9.$0.R1;.(:.(;.R18.(<.&40.O5.)Vgp,Vtp,R17.R16.R15.Vsp,(<.&40.O5.)(<.&40.O1.)R14.R13.R12.R11.R10.R?.R>.(<.&40.O6.)R9.R8.R7.R6.(<.&40.(>.(?.O6.+3.)(10.(11.VR,))))(<.&40.O6.)R5.R4.Vs11,R=.R<.R;.R:.)VF,(<.&40.+=3?;8.)Vfc,(13.(5.&40.))R1:.(14.$4.)))(8.(19.$4.VR,VHIA,O<.O:.(1:.(1;.$2.$2.)(1<.$2.$2.O6.+80.)VLF,)R1:.)(8.(27.$4.R1:.O6.(1:.$28.(29.R3.)(1:.$28.(29.R2.)(1:.$28.(29.R1.)(2:.$28.)))))(8.(27.$4.R1:.(>.(?.O6.+3.)(10.(11.VR,)))(1:.$28.(2<.(<.&8.+?1.))(1:.$28.(2<.(<.&8.+?1.))(1:.$28.(2<.(<.&8.+?1.))(1:.$28.(2<.(<.&8.+?1.))(1:.$28.(2<.(<.&8.+?8.))(1:.$28.(2<.(<.&8.+?8.))(1:.$28.(2<.(<.&8.+?8.))(1:.$28.(2<.(<.&8.+?8.))(1:.$28.(2<.(<.&8.+?3.))(1:.$28.(2<.(<.&8.+?3.))(1:.$28.(2<.(<.&8.+?3.))(1:.$28.(2<.(<.&8.+?3.))(1:.$28.(2<.(<.&8.=))(1:.$28.(2<.(<.&8.=))(1:.$28.(2<.(<.&8.=))(1:.$28.(2<.(<.&8.=))(2:.$28.))))))))))))))))))(8.(27.$4.R1:.(>.(17.&40.Vsp,)-60.)(1:.$28.(29.Vs10,)(1:.$28.(29.Vs9,)(1:.$28.(29.Vs8,)(1:.$28.(29.Vs7,)(1:.$28.(29.Vs6,)(1:.$28.(29.Vs5,)(1:.$28.(29.Vs4,)(1:.$28.(29.Vs3,)(1:.$28.(29.Vs2,)(1:.$28.(29.Vs1,)(1:.$28.(29.Vs0,)(1:.$28.(29.Vra,)(2:.$28.))))))))))))))(8.(27.$4.R1:.(>.O5.+18.)(1:.$28.(29.(<.&40.O6.))(2:.$28.)))(8.(2=.$4.R1:.O5.(>.O5.+18.))(8.(2=.$4.R1:.(>.O5.+20.)(>.(17.&40.Vsp,)-60.))(8.(2=.$4.R1:.Vlo,O5.)(8.(2>.$4.R1:.)(8.(2?.$4.VR,VHIA,O<.O;.VLF,(17.&40.Vsp,)(30.VR,)O7.O9.R1:.)(8.(27.$4.R1:.(=.VdX,)O4.)(8.P,(9.$2.O1.=)(8.(3;.$4.R1;.O3.R1:.)(9.$3<.(3=.(5.&40.)R1:.)(3=.(5.&40.)O2.)))P,(3>.(9.$2.O1.=))(9.P,(5.&40.)(6.(5.&8.))R1;.O8.))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "02W0@D2459793318.174 D29571162986.174D29681627768.175D32452690557.174D32458983511.176D3376374386.173 D39949789673.176D39960273859.174D43016287775.177D45717900227.173D62011770190.177D62012280210.173D62022258533.174D63451679468.175D68407932977.173D6911601204.173 L13422353013.147L1685717371.0   L17865848063.6  L19548981072.147L19548981075.146L2275137097.0   L23120422503.1  L24023900370.0  L24133462173.140L24133462174.141L27188209011.180L27188209011.181L27458424627.5  L27817705643.162L28168625444.2  L29010569984.136L32454903270.1  L34963265526.146L35655538631.10 L38948636245.0  L4022451686.1   L42411609006.0  L47939126700.4  L48119718061.142L48132321165.8  L50450596075.2  L54327868068.147L54379423251.148L57333296984.163L57333296984.164L5754747288.4   L59308586248.2  L59314873579.5  L59875636758.4  L60098763854.3  L63464815849.1  L64148832490.163L64148832490.164L6899380056.1   L6910010089.141 L6910010090.140 L7021541395.5   L9356559676.12  P21100806189.169P21100806189.170P55504651468.169P55504651468.170Q10048134299.163Q10523111606.185Q10592318618.165Q10592386193.184Q10592386207.182Q11799173861.169Q11799173861.170Q12450551966.158Q13268231764.164Q14701703927.156Q17639591956.184Q17639591962.182Q17841111254.166Q19547000785.162Q20505632399.181Q22358563612.181Q23399781729.156Q23927511199.185Q24133462174.187Q24137657765.181Q24165117164.155Q24167257676.156Q24169528968.162Q24333641986.181Q24337837113.187Q24439217129.164Q2457697673.182 Q25902788969.182Q27113329801.185Q27487439902.165Q28408016783.187Q29681627761.183Q29822288321.184Q29822288335.182Q30223088052.184Q30223088058.182Q32440833928.181Q32458983506.182Q32458983516.184Q33310975513.164Q33647212822.164Q3373771439.187 Q34796740404.184Q35802808482.182Q37224318474.185Q38921014052.164Q40145493800.163Q40354196046.169Q40354196046.170Q40360481330.159Q4133274105.164 Q43015051994.182Q4327589509.185 Q44115560389.182Q44115560395.184Q44298944140.159Q44298944140.165Q44301027056.169Q44301027056.170Q45055249104.187Q45702645285.181Q45715227421.186Q45715227422.187Q46192070061.155Q47228431932.169Q47228431932.170Q47230721779.185Q47814410910.158Q48117620903.184Q48117620905.182Q48119910507.169Q48119910507.170Q48132302231.181Q48189906827.164Q48196145590.164Q52946523988.164Q53314967860.184Q53314967866.182Q5540636085.165 Q5596578838.169 Q5596578838.170 Q56531220661.182Q56531220667.184Q57387563567.155Q58623094108.187Q59617553652.164Q59619599049.164Q59668625898.185Q62011770183.185Q63435846322.165Q63451679461.183Q64228675114.168Q64228675114.169Q64814344398.182Q65314988264.156Q66901779611.165Q68405358828.187Q6897428434.181 Q6910010089.187 Q6910010090.186 Q6912043752.166 Q8253422473.164 Q9159097516.162 Q9644353070.162 00000100V01>01c02H02I02n02o03]04B04i05P06706\06]07B08<08=08R09G0:<0:=0:A0:B0:Z0;20;\0<F0<T0=30=;0=<0=@0>:0>S0>T0>X0>Y0>\0?M0?l0@30@U0A40A50A60AB0AH0AS0A\0Af0Aj0Bk0Cl0D00DH0D`0E10E`0FV0GL0H<0Hl0J20JL0K20KJ0Kb0LN0M:0MO0Md0Me0Mf0Mg0NM0O<0O=0O>0Od0PN0Pf0Q>0QP0Qb0RH0RI0RJ0SH0SI0SJ0SK0T10T20TM0TN0TO0Tg0U?0U@0UX0V00VE0W>0W?0W@0WA0Wj0X?0Y@0Yl0ZX0[20[G0[H0[I0[J0[b0\<0\V0]B0]n0]o0^G0^_0^`0_20_b0`R0`m0aB0b30bd0cl0e40ee0f:0fO0fd0fe0ff0g@0gA0gB0gC0gD0gV0gW0gX0gY0gZ0h10h20hJ0iU0j`0ja0k30kM0kN0kf0l>0lV0m<0mQ0n70nOFS2LF2sp2dX3LFB2FB3sp12p33xs33ml04lxHnS2LF2sp2dX3LFB2FB3sp12p32n33xs33ml04lxHnS2LF2sp2dX3LFB2FB3sp12p33xs33ml04lxHnS2LF2sp2dX3LFB2FB3sp12p33xs33ml04lxHnFS2LF2sp2dX3LFB2FB3sp12p33xs33ml04lxHnFS1R3HIA2LF2sp2dX3LFB2h32FB3sp12p33xs33ml04lxHnS2LF2sp2dX3LFB2FB3sp12p33xs33ml04lxHnS1R2LF2sp2dX3LFB2FB3sp12p33xs33ml04lxHnS1R2LF2sp2dX3LFB2FB3sp12p33xs33ml04lxHnS1R2LF2sp2dX3LFB2FB3sp12p33xs33ml04lxHnS2LF2sp2dX3LFB2FB3sp12p33xs33ml04lxHnFS2LF2sp2dX3LFB2FB3sp12p33xs33ml04lxHnS2LF2sp2dX3LFB2FB3sp12p33xs32X03SPR4SP1R2F82F02P03ml04lxHnSS2sp2dX2lo3sp13SP12XSS2LF2sp2dX3LFB2FB3sp12p33xs32X03SPR2F82F02P03ml04lxHnS2LF2sp2dX3LFB2FB3sp12p33xs32X03SPR2F82F02P03ml04lxHnSS2FBSS2LF3LFB2FB3xs33ml04lxHnS2LF3LFB2FB3xs33ml04lxHnS2LF2sp2dX3LFB2FB3sp12p33xs33ml04lxHn1c2HcS2LF2sp2dX3LFB2FB3sp12p33xs33ml04lxHn1c2HcS1R2FB2p32n31KS2LF2sp2dX3LFB2FB3sp12p33xs32XBS2n33N16FS2FBS2LF2sp2dX3LFB2FB3sp12p33xs32X03SPR4SP1R2F82F02P03ml04lxHnS1R3HIA1h2sp2lo3TOP5HTOP3SS2FBSS1rS1R3NS12LF2sp2lo3LOS3SLO3LFB3xs33ALO3NES3ml04lxHnS1R5NEEDR2sp2lo3LOS3SLO3ALO3NERS2p32n3S2LF2sp2dX3LFB2FB3sp12p33xs32X02XBS2LF2sp2dX3LFB2FB3sp12p33xs32XBFFS2FB2p32n31KS1i2HiS1r2HR2KR1HS1r2HR2NES1R2lo3LOSS2p3S1R2LF2sp2dX3LFB2FB3sp12p33xs32XB2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2LF2sp2dX3LFB2FB3sp12p33xs32XB2HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS2FBS2LF3LFB2FB3xs33ml04lxHnS2LF3LFB2FB3xs33ml04lxHnS3xs34lxl26LXlen0S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3NER3SPRS1R2LF2dX3LFB2FB2p32n33xs32XB3PFB2HB5Ha_st5Hl_st5SAEstS1R2LF2dX3LFB2FB2p32n33xs32XB3PFB2HB5Ha_st5Hl_st5SAEstS1R2LF2dX3LFB2FB3xs33APX2XB2HB5Ha_st5Hl_st5SAEstS1R2LF2dX3LFB2FB3xs33APX2XB2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp2dX2lo3LOS3SLO3LFB2FB3sp13xs33SP13NER2XB2HB5Ha_st5Hl_stS1R2LF2sp3LFB3xs33ml04lxHnS1R2LF2dX3LFB2FB3xs32XB2HB5Ha_st5Hl_stS2LF3LFB2FB3xs33ml04lxHnS2LF3LFB2FB3xs33ml04lxHnS1R2LF2dX3LFB2FB3xs32XB2HB5Ha_st5Hl_st5SAEstS1R2LF2dX3LFB2FB3xs32XB2HB5Ha_st5Hl_st5SAEstS2LF2dX3LFB2FB3xs32XBS2LF2dX3LFB2FB3xs32XBFFFS1R2LF2dX3LFB2FB3xs32XB2HB5Ha_st5Hl_stS2LF2sp2dX3LFB2FB3sp12p33xs32X03SPR2F82F02XB2P0FFS2LF2sp2dX3LFB2FB3sp12p33xs33XAL2X02XBS1R3HIA1h2LF2sp3TOP3LFB3xs35HTOP33ml04lxHnS2LF3LFB2FB3xs33ml04lxHnS2LF3LFB2FB3xs33ml04lxHnS2LF2dX3LFB3xs32XBS2LF2dX3LFB3xs32XBS1R2LF2dX3LFB2FB3xs32XB2HB5Ha_st5Hl_stFFS1R5NEEDR2LF2sp2dX2lo3LOS3SLO3LFB2FB3xs33NER2XB2HB5Ha_st5Hl_stFFFS1R2LF2dX3LFB2FB3xs32XB2HB5Ha_st5Hl_stFS2LF3LFB2p32n33xs33ml04lxHnFFS2LF3LFB2FB3xs33ml04lxHnS2LF3LFB2FB3xs33ml04lxHnFS2LF3LFB2FB3xs33ml04lxHnS2LF3LFB2FB3xs33ml04lxHnS2LF2dX3LFB2FB3xs32XBS1R3HIA1h2LF2sp2dX3TOP3LFB2FB3xs35HTOP32XB2HB5Ha_st5Hl_stFFFS1R2LF3LFB2p32n33xs33ALO3N163FX13ml04lxHnS2LF2dX3LFB2FB3xs32XBS1R3HIA1h2LF2sp2dX3TOP3LFB2FB3sp13xs33SP15HTOP32XB2HB5Ha_st5Hl_stS1R2LF2dX3LFB2FB3xs32XB2HB5Ha_st5Hl_st5SAEstS1R2LF2dX3LFB2FB3xs32XB2HB5Ha_st5Hl_st5SAEstS1R2LF2dX3LFB2FB3xs32XB2HBS2LF2dX3LFB2FB3xs32XBFFFS2LF3LFB2FB3xs33ml04lxHnS1R2LF2dX3LFB2FB3xs32XB2HBS1R2LF2dX3LFB2FB3xs32XB2HBS1R2LF2dX3LFB2FB3xs32XB2HB5Ha_st5Hl_st5SAEstS1R2LF2dX3LFB2FB3xs32XB2HB5Ha_st5Hl_st5SAEstFS2LF3LFB2FB3xs33ml04lxHnS2LF3LFB2FB3xs33ml04lxHnFS2LF2dX3LFB3xs32XBS1R2LF2dX3LFB2FB3xs33ALO2XB2HB5Ha_st5Hl_st5SAEstS1R2LF2dX3LFB2FB3xs33ALO2XB2HB5Ha_st5Hl_st5SAEstS1R2LF3LFB3xs33ALO3ml04lxHnS2LF2dX3LFB2FB3xs32XBS1R3NS12LF2sp2lo3LOS3SLO3LFB3xs33ALO3NES3ml04lxHnS1R3NS12LF2sp2lo3LOS3SLO3LFB3xs33ALO3NES3ml04lxHnS1R5NEEDR2LF2sp2dX2lo3LOS3SLO3LFB2FB3xs33ALO3NER2XB2HB5Ha_st5Hl_st5SAEstS1R5NEEDR2LF2sp2dX2lo3LOS3SLO3LFB2FB3xs33ALO3NER2XB2HB5Ha_st5Hl_st5SAEstS1R3NS12LF2sp2lo3LOS3SLO3LFB3xs33ALO3NES3ml04lxHnS2LF2dX3LFB2FB3xs32XBS2LF2dX3LFB2FB3xs32XBS2LF2dX3LFB2FB3xs32XBFFS1R2LF2dX3LFB2FB3xs32XB2HBFFFFS2LF2dX3LFB3xs32XBFFFFS1R2LF3LFB3xs33ml04lxHnFS2LF3LFB2p33xs33ml04lxHnS1R2LF2sp2dX3LFB2FB3sp12p33xs32X03SPR4SP1R2F82F02XB2P02HB5Ha_st5Hl_st5SAEstS1R2LF2sp2dX3LFB2FB3sp12p33xs32X03SPR4SP1R2F82F02XB2P02HB5Ha_st5Hl_st5SAEstFS2LF2dX3LFB3xs32XBS1R2LF2dX3LFB2FB3xs32XB2HBFS2LF3LFB2FB3xs33ml04lxHnS2LF3LFB2FB3xs33ml04lxHnS2LF3LFB2FB3xs33ml04lxHnS1R2LF2dX3LFB2FB3xs32XB2HB5Ha_st5Hl_stS2LF2dX3LFB2FB3xs32XBS1R2LF2dX3LFB2FB3xs32XB2HB5Ha_st5Hl_stS2LF2dX3LFB2FB3xs32F02XB". (* [comment removed for export] *)
  Lemma mid_walk : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p255 ()) "Ph3,(3.$4.VR,VHIA,)PLBa,(7.$36.)PLBb,(7.$36.)Pm0,P,(5.&40.)(6.(5.&8.))Pmm,P,(5.&40.)(6.(5.&8.))PWA,(7.$31.)PFB,$2.Psp1,$2.Pp3,$2.Pn3,$2.Psgw,(5.&40.)Ppadw,(5.&40.)Pxs3,(7.(5.&40.))Pjmp,(7.(5.&8.))Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Pa1,(5.&40.)Pa2,(5.&40.)Pa3,(5.&40.)Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)Pw0,(5.&40.)Pw1,(5.&40.)Pw2,(5.&40.)Pr,$2.P,(19.$4.VR,VHIA,R20.R1>.(1:.(1;.$2.$2.)(1<.$2.$2.R1:.+80.)VLF,)R1<.)P,Px,$2.P,(1=.$4.VR,VHIA,Vh,R1.)(1=.$4.VR,VHIA,R23.R2.)P,(9.$2.(1>.$4.VR,VHIA,R22.)(1>.$4.VR,VHIA,Vh,))P,(9.$2.(1?.$4.VR,VHIA,R23.)(1?.$4.VR,VHIA,Vh,))P,(8.(15.(16.(17.&40.Vsp,)+90.)R1=.)(15.R1=.(16.(17.&40.Vsp,)+80.)))P,(9.$2.(18.R1>.+20.)=)P,(9.$2.(18.R20.+40.)=)P,(26.VR,R26.VLF,R21.+80.)P,(26.VR,R26.VLF,R22.+80.)P,(37.(1=.$4.VR,VHIA,Vh,)R23.+80.)P,PB,$2.Pj,$2.P,(38.(1;.$2.$2.)(1<.$2.$2.R2.R1.)VLF,)(39.(15.(>.R27.+80.)R3.)(15.(>.R3.R2.)R27.))P,(27.$4.R27.R25.(1:.$28.(29.R?.)(1:.$28.(29.R>.)(1:.$28.(29.R=.)(2:.$28.)))))P,(27.$4.R28.(>.R26.+20.)(1:.$28.(2;.#20.R1?.)(2:.$28.)))P,(27.$4.R29.(>.(?.R27.+3.)(10.(11.VR,)))(1:.$28.(2<.(<.&8.+?1.))(1:.$28.(2<.(<.&8.+?1.))(1:.$28.(2<.(<.&8.+?1.))(1:.$28.(2<.(<.&8.+?1.))(1:.$28.(2<.(<.&8.+?8.))(1:.$28.(2<.(<.&8.+?8.))(1:.$28.(2<.(<.&8.+?8.))(1:.$28.(2<.(<.&8.+?8.))(1:.$28.(2<.(<.&8.+?3.))(1:.$28.(2<.(<.&8.+?3.))(1:.$28.(2<.(<.&8.+?3.))(1:.$28.(2<.(<.&8.+?3.))(1:.$28.(2<.(<.&8.=))(1:.$28.(2<.(<.&8.=))(1:.$28.(2<.(<.&8.=))(1:.$28.(2<.(<.&8.=))(2:.$28.))))))))))))))))))P,(27.$4.R2:.(>.(17.&40.Vsp,)-60.)(1:.$28.(29.Vs10,)(1:.$28.(29.Vs9,)(1:.$28.(29.Vs8,)(1:.$28.(29.Vs7,)(1:.$28.(29.Vs6,)(1:.$28.(29.Vs5,)(1:.$28.(29.Vs4,)(1:.$28.(29.Vs3,)(1:.$28.(29.Vs2,)(1:.$28.(29.Vs1,)(1:.$28.(29.Vs0,)(1:.$28.(29.Vra,)(2:.$28.))))))))))))))P,(27.$4.R2;.(>.R28.+18.)(1:.$28.(29.(<.&40.R29.))(2:.$28.)))P,(2=.$4.R2<.R29.(>.R29.+18.))P,(2=.$4.R2=.(>.R2:.+20.)(>.(17.&40.Vsp,)-60.))P,(2=.$4.R2>.Vlo,R2;.)P,(2>.$4.R2?.)P,(2?.$4.VR,VHIA,R34.R33.VLF,(17.&40.Vsp,)(30.VR,)R2?.R31.R30.)P,(27.$4.R31.(=.VdX,)(3?.R2=.R2;.R2<.R2:.))P,(40.$4.(11.VR,)(1=.$4.VR,VHIA,R36.)R32.(=.VdX,)+10.)P,(9.$2.(18.(=.VdX,)+8.)=)P,(41.=(=.VdX,))P,(39.(15.(>.R33.+80.)(=.VdX,))(15.(>.(=.VdX,)+10.)R33.))P,(39.(15.(>.(=.VdX,)+10.)Vlo,)(15.(17.&40.Vsp,)(=.VdX,)))P,(42.VR,R3:.VLF,(17.&40.Vsp,)R36.(=.VdX,)+10.)P,(8.(41.(43.(44.+2.+1?.))R1=.)(15.R1=.=))P,P,(9.$2.R1>.=)(8.(8.(15.+10.R35.)(15.R35.+2710.))(8.(38.(1;.$2.$2.)(1<.$2.$2.R36.(45.+4.R35.))R3<.)(8.(9.$2.(18.R36.+10.)=)(8.(41.=R36.)(8.(3;.$4.R3:.R36.R32.)(8.(9.$2.(46.(3=.(5.&40.)R32.))R35.)(8.(26.VR,R3=.VLF,R36.(45.+4.R35.))(39.(15.(>.(=.VdX,)+10.)R36.)(15.(>.R36.(45.+4.R35.))(=.VdX,))))))))))(32.$4.(11.VR,)(1=.$4.VR,VHIA,R3>.)(47.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.(3?.R36.R34.R35.R33.)R36.R32.R1?.)(:.(;.(<.&40.+=3>=8.)(<.&40.R37.)Vgp,Vtp,R30.R2?.R2>.Vsp,(<.&40.R37.)(<.&40.R1?.)R2=.R2<.R2;.R2:.R29.R28.R27.(<.&40.R38.)(<.&40.(=.VdX,))Vs4,Vs5,Vs6,(<.&40.(>.(?.R38.+3.)(10.(11.VR,))))(<.&40.R38.)(<.&40.(10.(11.VR,)))Vs10,Vs11,R26.R25.R24.R23.)VF,(<.&40.+=3>=8.)Vfc,(13.(5.&40.))R3:.(14.$4.)))")
(* [comment removed for export] *).
  Proof.
    intros until r. intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB AP FHD MPB FSH SAVE SLOT ST24 SThi STlo MI PRES CX OX XAL X0 APX XS WCX HR LIM.
    rt_facts.
    pose proof (hcs_ok asegs R HIA h3) as CSOK3.
    pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3. rewrite ET3, ES3 in HTOP3.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR NER; lia).
    assert (CFB3 : crange (hcs asegs R HIA h3) FB 128) by (eapply crange_mono; [exact HCS3| exact CFB]).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NEEDR NER TOP HTOP3; lia]).
    assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS3| exact SCS]).
    assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS3| exact SCS0]).
    destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 LBb LF mm FB 128 lo HH3 eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (_ & INF & INH3 & IND3 & _ & _ & F8 & FBLO & SBND & APS). change (128 / 8) with 16 in SBND, APS. change (128 - 40) with 88 in IND3.
    pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'. flat constr:(FRSH') 4%nat. flclear FRSH'. intros F0 F1 F2 F3.
    pose proof (art_stk_high asegs R HIA) as STKH.
    pose proof (hm_wlow asegs R HIA h3 _ _ _ HH3) as WL3.
    assert (WLa : wlow R LBa LF) by (split; [exact (proj2 (proj2 (proj2 PRES)))| apply (art_data_lo asegs R HIA)]).
    assert (XS1 : X + 16 <= lo \/ sp1 <= X) by (clear - XS SP1; lia).
    pose proof (rw_cells_bound _ _ _ _ CX) as XB. unfold mpi_cells in XB, CX. cbn [cells_size csize Nat.add] in XB.
    (* [comment removed for export] *)
    zstep. if_cases KR; zify_cond KR.
    { assert (RNZ : r <> 0) by (intros C; apply KR; rewrite C; reflexivity).
      apply evtA_done. unfold MIDQ. exists mm, xs3. do 24 eexists.
      split; [reflexivity|].
      split; [exact HH3|]. split; [exact FHD|]. split; [exact FSH|]. split; [exact SAVE|]. split; [exact SLOT|]. split; [exact ST24|]. split; [exact SThi|].
      split; [exact STlo|]. split; [exact MI|]. split; [exact PRES|]. split; [exact CX|].
      split; [intros C; exfalso; exact (RNZ C)| intros _; reflexivity]. }
    assert (R0 : r = 0).
    { destruct (Z.eq_dec r 0) as [E|NE]; [exact E| exfalso].
      clear - KR HR NE. assert (r mod 18446744073709551616 = r + 18446744073709551616) by (symmetry; apply (Z.mod_unique r 18446744073709551616 (-1)); lia). lia. }
    subst r. clear KR.
    flat constr:((LIM eq_refl)) 8%nat. intros N16 XIN PAL P0 XARR LENX FRX XPS. clear LIM.
    pose proof LENX as LENX0.
    pose proof FRX as FRX'. unfold fresh_apart in FRX'. flat constr:(FRX') 4%nat. flclear FRX'. intros FX0 FX1 FX2 FX3.
    assert (OP : aobj asegs AL (hcs asegs R HIA h3) mm p3 (4 * n3)) by (eapply hm_aobj_block; [exact HH3| exact XIN]).
    assert (CWP : client_wrange L (LBb ++ fdata ((FB, 128) :: LF)) (arl_stklo R) (htop asegs R HIA h3) p3 (4 * n3))
      by (eapply client_wrange_block; [apply in_or_app; left; exact XIN| clear; lia| clear; lia]).
    assert (PFB : FB + 128 <= p3 \/ p3 + 4 * n3 <= FB).
    { flat constr:(FRSH3) 4%nat. flclear FRSH3. intros _ _ _ G3. pose proof (G3 _ _ ltac:(apply in_app_iff; left; exact XIN)) as K. clear - K. lia. }
    assert (WCP : wcover R LBa LF (bv_unsigned sp) WA p3 (4 * n3)) by (eapply wcover_fresh; [exact FRX| clear; lia| clear; lia| clear - LOS SLO ALO NER NEEDR; lia]).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    assert (XSH : forall ma m' ws, u32arr asegs ma p3 ws -> Z.of_nat (length ws) = n3 -> munch [(Z.shiftr FB 3 + al_sb AL, Z.shiftr FB 3 + al_sb AL + 16)] ma m' -> wmono asegs ma m' -> u32arr asegs m' p3 ws)
      by (intros ma m' ws HA HL MUq WMq; eapply (u32arr_transport asegs); [exact HA| exact MUq| exact WMq|]; rewrite HL; cbn [disjoint_from fst snd]; split; [| exact I];
          pose proof (apart_client_shadow AL (hcs asegs R HIA h3) p3 (4 * n3) FB (Z.shiftr FB 3 + al_sb AL) 16 CSOK3 ltac:(eapply aobj_crange; exact OP) CFB3 ltac:(shadow_addr_eq) ltac:(clear - N16; lia) ltac:(clear; lia)) as K; clear - K; lia).
    (* [comment removed for export] *)
    pose proof (munch_refl [(Z.shiftr FB 3 + al_sb AL, Z.shiftr FB 3 + al_sb AL + 16)] mm) as MUs. pose proof (wmono_refl asegs mm) as WMs.
    pose proof (conj XARR I) as XARRb. clear XARR.
    zstep. zstep. zstep. zstep.
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSH2 end.
    flat constr:(XARRb) 2%nat. flclear XARRb. intros XARR _. apply (XSH _ _ _ XARR LENX MUs) in WMs. clear XARR MUs. rename WMs into XARR.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
    frame_aobj FSH2 (FB + 32) 4%nat as OMP.
    (* [comment removed for export] *)
    lx_mkR. pose proof (arl_need_rt_amem R) as LXNRA.
    pose proof (cells_at_wf _ _ _ _ (proj1 MPB)) as WF. cbn [cells_wf cell_wf] in WF. flat constr:(WF) 2%nat. flclear WF. intros LJM _.
    apply (u8arr_of_rw_cells asegs) in MPB.
    destruct (MpiWalkAux.u32arr_of_u8arr asegs m4 (FB + 32) _ 8 MPB ltac:(rewrite LJM; reflexivity)) as (ml0 & MARR & LENM0).
    assert (LENM : Z.of_nat (length ml0) = 8) by (rewrite LENM0; reflexivity). clear MPB LENM0 LJM.
    pose proof (hm_abase asegs R HIA h3 _ _ m4 HH3) as ABm. pose (lxi := lxA_img (arl_AL R) IMG).
    assert (CW_1 : client_wrange L (LBb ++ fdata ((FB, 128) :: LF)) (arl_stklo R) (htop asegs R HIA h3) (FB + 32) (4 * 8)) by (eapply client_wrange_block; [exact IND3| clear; lia| clear; lia]).
    assert (SFF : shadow_free R LBa LF (arl_stklo R) (hstkhi asegs R HIA h3) FB 128)
      by (eapply shadow_free_fresh; [exact FRSH | exact (proj2 (proj2 (proj2 PRES))) | clear; lia | clear; lia | exact ALO | exact AP]).
    lx_pre. lxe_pose. lxe_sums [SUM_amemsetWinA 4 5; SUM_amemsetWinA 6 7; SUM_coreaddXXBA; SUM_mlaWin1A 4 5] [p3; n3; FB + 32; 8].
    lx_pre. lx_run_tac (PLANS [0xd3fb8] [(0xd3eec, DJoin); (0xd3f58, DJoin); (0xd3f7c, DJoin)] 1000%N [SUM_amemsetWinA 4 5; SUM_amemsetWinA 6 7; SUM_coreaddXXBA; SUM_mlaWin1A 4 5]). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    (* [comment removed for export] *)
    apply evtA_done. unfold MIDQ.
    lazymatch goal with H : u32arr asegs ?mx p3 ?l |- context [MS _ _ _ _ _ ?mx _] => exists mx, l end. do 24 eexists.
    split; [reflexivity|].
    repeat (split; [eassumption|]).
    split; [ intros _; split; [ eassumption
                              | lazymatch goal with HL : Z.of_nat (length ?l) = _ |- length ?l = _ =>
                                  rewrite ?upd_length in HL; rewrite ?upd_length; clear - HL LENX0; lia end ]
           | intros C; exfalso; apply C; reflexivity ].
    all: match goal with |- ?g => idtac "MID-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis MX : mpd_at asegs m LB dX.
  Hypothesis NST : md_own dX <> LStatic.
  Hypothesis XW : mpd_writableA R LB LF (bv_unsigned sp) (htop asegs R HIA h) dX.
  Hypothesis XLS : md_own dX <> LNull -> md_p dX + 4 * md_n dX <= lo \/ bv_unsigned sp <= md_p dX.
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis BUD : havol asegs R HIA h + grow_PHI 16 <= AVOL_MAX.
  Hypothesis UWX : uw_obj R X 16 d.
  Hypothesis BUDF : hfr asegs R HIA h + red_FRn d <= FR_MAX.
  Hypothesis C24H : cnt24 LB + C24_ECP_RED <= C24MAX.
  Hypothesis HND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L60572539508.4L60572539508.8L66825651888.500000:00Q00`S2dX1B1j1KS2dX1B1j3FBq2nq2H12H21KS1R2dX2BI2D12D2". (* [comment removed for export] *)
  Lemma keep_block_fresh : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p255 ()) "Phq,(3.$4.VR,VHIA,)Pmq,P,(5.&40.)(6.(5.&8.))P,(19.$4.VR,VHIA,R2.VLB,VLF,R1.)P,(9.$48.(49.VdX,)$4:.)P,(38.(1;.$2.$2.)(1<.$2.$2.(4;.VdX,)(45.+4.(4<.VdX,)))VLB,)(26.VR,(4=.VLB,VdX,)VLF,(4;.VdX,)(45.+4.(4<.VdX,)))")
(* [comment removed for export] *).
  Proof.
    intros hq mq HHq EO XIN. pose proof (HND _ _ _ _ HHq) as ND.
    flat constr:((hm_apart asegs R HIA hq LB LF mq HHq)) 2%nat. intros HF BA. rewrite Forall_forall in HF.
    destruct (HF _ ltac:(apply in_app_iff; left; exact XIN)) as (B0 & _ & BC & BI). cbn [fst snd] in B0, BC, BI.
    split; [exact B0|]. split; [exact BC|]. split; [(flat constr:(DIMG) 2%nat; intros D1 D2); clear - BI D1 D2; lia|].
    intros B j Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
    - unfold mpd_keep in Hb. rewrite EO in Hb. apply filter_In in Hb. flat constr:(Hb) 2%nat. flclear Hb. intros Hb Hne.
      assert (NE : md_p dX <> B).
      { intros E. symmetry in E. revert E. apply (nodup_fst_neq LB (md_p dX) (4 * md_n dX) B j ND XIN Hb).
        intros E. rewrite E in Hne. unfold blk_eqb in Hne. cbn [fst snd] in Hne. rewrite !Z.eqb_refl in Hne. discriminate Hne. }
      pose proof (blocks_apart_in2 (LB ++ LF) _ _ _ _ BA ltac:(apply in_app_iff; left; exact XIN) ltac:(apply in_app_iff; left; exact Hb) NE) as K. clear - K. lia.
    - flat constr:((fdata_sub2 LF (B, j) Hb)) 4%nat. intros (FBq & nq) Hfb H1 H2. cbn [fst snd] in H1, H2.
      pose proof (blocks_apart_app2 LB LF (md_p dX, 4 * md_n dX) (FBq, nq) BA XIN Hfb) as K. cbn [fst snd] in K. clear - K H1 H2. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00i0?L10183286230.3 L1181568746.4  L13645206873.0 L14487559459.8 L1540877545.3  L1916651063.3  L19980016842.7 L21052112672.10L21388473101.1 L2275137097.0  L23929348277.7 L2397676628.0  L24166965860.1 L25263700820.1 L25869546893.3 L25961767577.3 L25985555144.1 L26615256798.1 L26892418956.1 L27188209011.3 L28390317327.1 L28615016913.5 L29702969659.4 L29773195157.0 L29956516996.0 L31918344096.10L31995967304.1 L32454903270.1 L35653441506.10L3617752057.1  L37156630869.0 L37594587805.2 L37761451993.4 L38948636245.0 L40281191306.3 L41508823959.4 L42317116952.3 L44150806992.5 L48132321165.8 L49799904432.3 L50790761713.7 L53209925281.0 L58071657357.3 L5856141729.0  L60098763854.3 L61887524866.10L62018535662.1 L62037211595.8 L6203936179.1  L64163467803.1 L66151427842.16L67028235242.9 L6899380056.1  L696052593.2   L774551903.6   L9356559645.12 L9631767084.2  00000<00A00B00_00k01601N02302702802Q02R02V02Z02d02o03403803<03E03I03N03a03b03c04H04M04Q04i04l04m05105A05B05K05V05a06206Q06]07807907E07F07P08508808W08\08`09C09f09j0:20:I0;80;?S2dX3dX33GNNS3dXfSS1R5NEEDR2sp2dX2lo3SLO3NER2XSS2sp3sp13SP1S2dX2FB3APXS1R3HIA1h2sp3TOP3sp13SP1S1R5NEEDR2sp2dX2lo3SLO3NER2XS3sp13SP1S2spSS1R2sp2lo3SLO3NER3sp13SP1SS2dXS2FBS2dX3dX31KS2dX3dX32K2S3sp1S2FBS2spS2FB1c2HcS2FBS3dXfS3dX34LEN33xs'4LEN'SSS1R5NEEDR2sp2dX2lo3SLO3NER2XS3sp13SP1S3sp1S2FBS1R3HIA1h2sp2lo3TOP4HTOPS1dSS2dXS2dX3dX33NR33GNNSS1R3HIA1hS2dX1A1k2HAS2dX2FB3APXS2sp2dX3sp13SP11KS1R5NEEDR2sp2lo3LOS3SLO3ALO3NERS2sp3sp13SP1S1R5NEEDR2sp2lo3LOS3SLO3NERSS2sp3sp13SP1SS1R2lo3LOSS1R5NEEDR2sp2dX2lo3SLO3NER2XS3sp13SP1S1RS1R5NEEDR2sp2lo3LOS3SLO3NER3SPRS3sp1S2dXS2sp2r03SPA1q1r1H2H02q02H43sp14SP1MS1R5NEEDR2sp2lo3LOS3SLO3NER3sp13SP1S2FBS2sp3SPRS1R5NEEDR2sp2lo3SLO3NERS1R5NEEDR2sp2lo3LOS3SLO3ALO3ACV3NER3SPR3sp13SP1S2FB2F0". (* [comment removed for export] *)
  Lemma r_main : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p255 ()) "Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Pa1,(5.&40.)Pa2,(5.&40.)Pa3,(5.&40.)Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)P,(19.$4.VR,VHIA,Vh,VLB,VLF,Vm,)P,(25.$4.VR,VHIA,Vh,Vmo0,)P,(2=.$4.Vm,Vlo,(17.&40.Vsp,))P,(2>.$4.Vm,)P,(4>.$4.(11.VR,)(1=.$4.VR,VHIA,Vh,)Vm,VdX,)P,(4?.$4.Vm,(30.VR,)(1?.$4.VR,VHIA,Vh,)(17.&40.Vs0,)(17.&40.Vsp,)Vd,)(50.$4.(51.$4.VR,VHIA,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,(52.+10.VdX,VLB,)(53.+10.)(54.Vd,)Vlo,Vm,Vmo0,)(55.(:.(;.Vra,Vsp,Vgp,Vtp,R14.R13.R12.Vs0,Vs1,(<.&40.(=.VdX,))R11.R10.R?.R>.R=.R<.R;.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R:.R9.R8.R7.)VF,(<.&40.$34.)Vfc,(13.(5.&40.))Vm,(14.$4.))Vmo0,))")
(* [comment removed for export] *).
  Proof.
    intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HH HK0 ST MI OXA UW.
    rt_facts.
    pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NEEDR NER TOP HTOP; lia]).
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    flat constr:(MX) 2%nat. intros FLt1 SGX. flat constr:(FLt1) 6%nat. flclear FLt1. intros CX0 XAL X0 LENX NRX OWNX.
    flat constr:(XW) 2%nat. intros XCW XP.
    pose proof (rw_cells_bound _ _ _ _ CX0) as XB. unfold mpi_cells in XB. cbn [cells_size csize Nat.add] in XB.
    pose proof (client_wrange_where_A asegs R HIA h LB LF m LB (bv_unsigned sp) X 16 lo HH ltac:(intros b' Hb; exact Hb) XCW ltac:(clear; lia) LOS ltac:(clear - SLO NEEDR NER; lia)) as XS.
    flat constr:((hm_apart asegs R HIA h LB LF m HH)) 2%nat. intros HBR _. rewrite Forall_forall in HBR.
    apply (aevtA_enter asegs (KF asegs R HIA h mo0) _ _ _ (conj HK0 (mo_frame_refl mo0))).
    (* [comment removed for export] *)
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo0).
    { eapply pro_walk; eassumption. }
    intros ms1 P1.
    destruct P1 as (FB & sp1 & h1 & m1 & y0 & y1 & y2 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & w0 & w1 & w2 & jmp
                   & Ems & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & MPB & FSHX
                   & SAVE & SLOT & ST24 & SThi & STlo & MI1 & PRES0).
    subst ms1.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR NER; lia).
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (128 / 8) with 16 in SBND, APS. change (128 - 40) with 88 in IND.
    pose proof (presW_presA asegs R HIA h LB LF _ _ _ m m1 PRES0) as HP01.
    pose proof (presA_presx asegs R _ _ _ _ _ _ _ _ HP01) as HPX01.
    assert (CRXs : client_range L (LB ++ fdata LF) (bv_unsigned sp) X 16) by (eapply client_range_of_w; exact XCW).
    assert (CRXL : md_own dX = LHeap -> client_range L (LB ++ fdata LF) (bv_unsigned sp) (md_p dX) (4 * md_n dX)).
    { intros EO. rewrite EO in OWNX. flat constr:(OWNX) 3%nat. flclear OWNX. intros N1 XIN _. eapply client_range_block; [apply in_app_iff; left; exact XIN| clear; lia| clear - N1; lia]. }
    assert (MX1 : mpd_at asegs m1 LB dX).
    { eapply (mpd_at_heap_presx asegs L); [exact MX| exact HPX01| exact MI| exact MI1| exact CRXs| exact CRXL| exact I| intros _; exact I| intros b' Hb; unfold mpd_blk in Hb; destruct (md_own dX) eqn:EO; try (destruct Hb; fail); destruct Hb as [<-|[]]; (flat constr:(OWNX) 3%nat; flclear OWNX; intros _ XIN _); exact XIN]. }
    assert (TOPCS : forall x, CS x -> x < hstkhi asegs R HIA h) by (intros x Hx; eapply hcs_below_top; exact Hx).
    assert (OXA1 : mpd_aobjA asegs AL (hcs asegs R HIA h1) m1 dX).
    { rewrite Ehcs. flat constr:(OXA) 2%nat. flclear OXA. intros OX1 _. split; [| intros EO; exfalso; exact (NST EO)].
      eapply (presA_aobj asegs R); [exact CSOK| exact HP01| exact OX1| exact CRXs| clear - LOS SLO NEEDR NER; lia| exact TOPCS]. }
    assert (UW1 : uwc asegs m1 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
    { eapply (uwc_presA R); [exact HP01| exact UW| clear; lia| intros a Ha; exact I| clear - SPR; lia| apply hstkhi_le64; clear - LOS SLO SPR NEEDR NER; lia]. }
    assert (UWF : uwc asegs m1 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned sp) sp1 (d + 1)).
    { pose proof SAVE as SV. chunk_split SV 10%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
      replace (bv_unsigned sp + -96 + 80) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
      eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UW1| clear - SP1; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0]. }
    clear UW1.
    assert (APX : FB + 128 <= X \/ X + 16 <= FB) by (eapply (frame_apart_obj R HIA); [exact FRSH| exact XCW| clear; lia| clear; lia| clear - LOS SLO NEEDR NER; lia]).
    pose proof (AIh_laws asegs R HIA h) as LAWS. pose proof (KF_kinv asegs R HIA h mo0) as KINV.
    pose proof GROW as GROW'. unfold mpi_grow_stmtA_sz in GROW'.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply GROW' with (h := h1) (LB := LB) (LF := (FB, 128) :: LF) (dX := dX) (v := 16) (lo := lo) (d := d + 1);
        rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?Ehcs, ?Ehtop, ?Estk, ?Evol, ?Efr;
        first [ exact HH1 | exact MX1 | exact NST | exact STlo | exact LOS | exact MI1 | exact TPV | exact UWF | reflexivity
              | lazymatch goal with
                | |- HK _ _ _ h1 mo1 => apply (proj2 (HKI mo1)); exact HK1
                | |- 0 <= 16 < _ => clear; lia
                | |- mpd_writableA _ _ _ _ _ dX => split; [eapply client_wrange_sp_mono; [| eapply client_wrange_mono; [exact XCW| intros b' Hb; apply fdata_cons_sub; exact Hb]]; clear - SP1; lia| exact XP]
                | |- md_own dX <> LNull -> _ => intros XN; destruct (XLS XN) as [K|K]; [left; exact K| right; clear - K SP1; lia]
                | |- lo <= sp1 - _ - _ => clear - SLO SP1 NER; lia
                | |- sp1 <= htop _ _ _ _ => clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => reflexivity
                | |- mpd_aobjA _ _ _ _ dX => rewrite <- Ehcs; exact OXA1
                | |- havol _ _ _ _ + _ <= AVOL_MAX => exact BUD
                | |- uw_obj _ (md_addr dX) 16 _ => eapply uw_obj_mono_d; [exact UWX| clear; lia]
                | |- hfr _ _ _ _ + _ <= FR_MAX => unfold red_FRn in BUDF; exact BUDF
                | |- cnt24 LB + _ <= C24MAX => unfold C24_GROW; unfold C24_ECP_RED in C24H; exact C24H
                end
              | match goal with |- ?g => idtac "CALL-PRE-LEFT:" g end ]. }
    cbv beta. intros ms4 mo4 (mo1 & [HK1 MF1] & PO).
    destruct PO as (q0 & q1 & q2 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m2 & mo2 & h3 & LB3 & dX3 & r
                    & E4 & MI2 & ST2 & MF2 & HP2 & HT3 & HS3 & HF3 & HK3 & HCS3 & HV3 & HFR3 & HH3 & MX3 & OUT3 & FRS3 & GR).
    injection E4 as Ems Emo. subst ms4 mo4.
    replace (ret_pc (Z_to_bv 64 0xd3ed8)) with (Z_to_bv 64 0xd3ed8 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST2, HP2 by exact SP1R.
    rewrite Ehtop in HT3. rewrite Estk in HS3, HP2. rewrite Eflag in HF3. rewrite Evol in HV3. rewrite Efr in HFR3.
    assert (HCSh3 : forall x, hcs asegs R HIA h x -> hcs asegs R HIA h3 x) by (intros x Hx; apply HCS3; rewrite Ehcs; exact Hx).
    pose proof (hcs_ok asegs R HIA h3) as CSOK3.
    (* [comment removed for export] *)
    assert (HP2' : presA asegs R (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m1 m2).
    { eapply presA_weaken; [exact HP2| intros b' Hb; exact Hb| intros b' Hb; right; exact Hb| clear - SP1; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
    assert (PRESb : presW asegs R HIA h (mpd_keep LB dX) LF (bv_unsigned sp) (arl_stklo R) [(X, X + 16)] m m2).
    { pose proof (presW_sub_blocks asegs R HIA h LB (mpd_keep LB dX) LF _ _ _ m m1 PRES0 ltac:(intros b' Hb; eapply In_mpd_keep; exact Hb)) as (P0 & C1 & C2 & C3).
      split; [| split; [exact C1| split; [exact C2| exact C3]]].
      eapply presA_trans; [| exact HP2'].
      eapply presA_weaken; [exact P0| intros b' Hb; exact Hb| intros b' Hb; exact Hb| clear; lia| clear; lia| clear; lia| intros x _; exact I]. }
    pose proof (fresh_apart_relist R HIA h3 LB LB3 LF m2 FB 128 FRSH HH3) as FRSH3.
    (* [comment removed for export] *)
    assert (CSHD : forall LBq SSPq TOPq c, FB <= c < FB + 128 -> cshd R LBq ((FB, 128) :: LF) SSPq TOPq c).
    { intros LBq SSPq TOPq c Hc. right; right; left. exists (FB, 128). split; [left; reflexivity| cbn; exact Hc]. }
    assert (DJX : forall A k, (A + k <= X \/ X + 16 <= A) -> disjoint_from [(X, X + 16)] A k).
    { intros A k HA. cbn [disjoint_from]. split; [clear - HA; lia| exact I]. }
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA h) (mpd_keep LB dX) ((FB, 128) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA h) [(X, X + 16)] m1 m2 FB _ CSOK) in FSHX;
      [| cbn [cells_size csize Nat.add]; eapply crange_sub; [exact CFB| clear; lia| clear; lia] | exact F8 | clear - F0; lia | exact HP2 | cbn [cells_size csize Nat.add]; intros c Hc; apply CSHD; clear - Hc; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 FB _ HP2) in FHD;
      [| cbn [cells_size csize Nat.add]; eapply client_range_block; [apply in_app_iff; right; left; reflexivity| clear; lia| clear; lia]
       | apply DJX; cbn [cells_size csize Nat.add]; clear - APX; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 (FB + 32) _ HP2) in MPB;
      [| cbn [cells_size csize Nat.add]; eapply client_range_block; [apply in_app_iff; right; right; left; reflexivity| clear; lia| clear; lia]
       | apply DJX; cbn [cells_size csize Nat.add]; clear - APX; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in SAVE; [| apply client_range_stack; clear - SP1; lia| apply DJX; cbn [cells_size csize Nat.add]; clear - XS SLO NEEDR NER; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in SLOT; [| apply client_range_stack; clear; lia| apply DJX; cbn [cells_size csize Nat.add]; clear - XS SLO NEEDR NER SP1; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in ST24; [| clear; lia| apply DJX; clear - XS SLO NEEDR NER SP1; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ m1 m2 _ _ HP2) in SThi; [| clear; lia| apply DJX; clear - XS SLO NEEDR NER SP1; lia].
    (* [comment removed for export] *)
    flat constr:(OUT3) 5%nat. intros OU1 OU2 OU3 OU4 OU5.
    flat constr:(MX3) 2%nat. intros FLt2 SG3. flat constr:(FLt2) 6%nat. flclear FLt2. intros CX3 XAL3 X03 LEN3 NR3 OWN3. rewrite OU1 in CX3.
    assert (CRXk : client_range L (mpd_keep LB dX ++ fdata LF) (bv_unsigned sp) X 16) by (eapply client_range_of_w; eapply mpd_writableA_keep; exact XW).
    assert (OX3 : aobj asegs AL (hcs asegs R HIA h3) m2 X 16).
    { eapply aobj_cs_mono; [exact HCS3|]. rewrite Ehcs.
      eapply (presA_aobj asegs R); [exact CSOK| exact HP2| rewrite <- Ehcs; exact (proj1 OXA1)| | clear - LOS SLO NEEDR NER SP1; lia| exact TOPCS].
      eapply client_range_temp; [exact CRXk| clear - SP1; lia| intros b' Hb; apply fdata_cons_sub; exact Hb]. }
    assert (HR : -2^31 < r <= 0).
    { destruct GR as [[(R0 & _)|(RF & _)] _]; subst r; [clear; lia| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia]. }
    assert (LIM : r = 0 -> 16 <= md_n dX3 <= 10000 /\ In (md_p dX3, 4 * md_n dX3) LB3 /\ md_p dX3 mod 16 = 0 /\ 0 < md_p dX3 /\ u32arr asegs m2 (md_p dX3) (md_limbs dX3)
                  /\ Z.of_nat (length (md_limbs dX3)) = md_n dX3
                  /\ fresh_apart R (mpd_keep LB dX) LF (md_p dX3) (4 * md_n dX3) /\ (X + 16 <= md_p dX3 \/ md_p dX3 + 4 * md_n dX3 <= X)).
    { intros R0. subst r.
      destruct (grow_ok_facts asegs m2 LB3 LB dX dX3 16 MX3 OUT3 GR ltac:(clear; lia)) as (GO & GNN & _ & _ & _ & GLEN & GIN & GPAL & GARR).
      flat constr:((hm_apart asegs R HIA h3 _ _ _ HH3)) 2%nat. intros HBR3 _. rewrite Forall_forall in HBR3.
      destruct (HBR3 _ ltac:(apply in_app_iff; left; exact GIN)) as (GP0 & _ & _). cbn [fst snd] in GP0.
      unfold MPI_MAX_LIMBS in NR3.
      assert (FRX : fresh_apart R (mpd_keep LB dX) LF (md_p dX3) (4 * md_n dX3)).
      { destruct (FRS3 (md_p dX3, 4 * md_n dX3) ltac:(unfold mpd_blk; rewrite GO; left; reflexivity)) as [K|K].
        - unfold mpd_blk in K. destruct (md_own dX) eqn:EO; try (destruct K; fail). destruct K as [K|[]]. injection K as K1 K2.
          flat constr:(OWNX) 3%nat. flclear OWNX. intros _ XIN _. rewrite <- K1. replace (4 * md_n dX3) with (4 * md_n dX) by (clear - K2; lia).
          exact (keep_block_fresh h m HH EO XIN).
        - cbn [fst snd] in K. flat constr:(K) 4%nat. flclear K. intros K0 K1 K2 K3. split; [exact K0|]. split; [exact K1|]. split; [exact K2|].
          intros B j HB. apply K3. apply fdata_cons_sub. exact HB. }
      split; [rewrite GNN; clear - NR3 GNN; lia|]. split; [exact GIN|]. split; [exact GPAL|]. split; [exact GP0|]. split; [exact GARR|]. split; [exact GLEN|].
      split; [exact FRX|].
      pose proof (fresh_apart_client R (mpd_keep LB dX) LF (bv_unsigned sp) X 16 _ _ FRX CRXk ltac:(clear; lia) ltac:(clear - GNN; lia) ltac:(clear - ALO LOS SLO NER NEEDR; lia)) as K.
      clear - K. lia. }
    clear HP2 HP2' MX1 OXA1 UWF HH1 STlo MI1 HP01 HPX01 PRES0.
    (* [comment removed for export] *)
    apply (aevtA_enter asegs (KF asegs R HIA h3 mo0) _ _ _ (conj HK3 (mo_frame_trans _ _ _ MF1 MF2))).
    clear LAWS KINV. pose proof (AIh_laws asegs R HIA h3) as LAWS. pose proof (KF_kinv asegs R HIA h3 mo0) as KINV.
    clear HK1 MF1 MF2 mo1.
    pose proof (presW_hmono R HIA h h3 (mpd_keep LB dX) LF _ _ _ m _ PRESb HCSh3 HS3) as PRESb3.
    eapply (aevtA_cut_evtA_KF asegs R HIA h3 mo0).
    { eapply mid_walk with (h3 := h3) (LBa := mpd_keep LB dX) (LBb := LB3) (m0 := m) (WA := [(X, X + 16)]) (p3 := md_p dX3) (n3 := md_n dX3)
                           (sgw := Z_to_bv 64 (md_sg dX3)) (padw := md_pad dX3) (xs3 := md_limbs dX3) (r := r);
        first [ exact HH3 | exact HCSh3 | exact PRESb3 | exact FRSH3 | exact CFB | exact AP | exact CX3 | exact OX3 | exact HR | exact LIM | exact APX | exact XS | exact X0 | exact XAL
              | exact FHD | exact MPB | exact FSHX | exact SAVE | exact SLOT | exact ST24 | exact SThi | exact ST2 | exact MI2 | exact SP1 | exact SP1M | exact F64 | exact HT3 | exact HS3
              | lazymatch goal with
                | |- fresh_apart _ (mpd_keep LB dX) LF FB 128 => apply fresh_apart_keep; exact FRSH
                | |- wcover _ _ _ _ _ _ _ => apply wcover_inside; cbn [inside]; left; clear; lia
                end
              | match goal with |- ?g => idtac "MID-PRE-LEFT:" g end ]. }
    cbv beta. intros ms5 MQ.
    destruct MQ as (mm' & xs' & k0 & k1 & k2 & k3 & ka1 & ka2 & ka3 & ka4 & ka5 & ka6 & ka7 & k4 & k5 & k6 & k7 & ks3 & ks4 & ks5 & ks6 & ks9 & ks10 & kw0 & kw1 & kw2
                & -> & HH5 & FHD5 & FSH5 & SAVE5 & SLOT5 & ST245 & SThi5 & STlo5 & MI5 & PRES5 & CX5 & XOK & XNE).
    (* [comment removed for export] *)
    set (dXf := if Z.eq_dec r 0 then relimb dX3 xs' else dX3).
    assert (MXf : mpd_at asegs mm' LB3 dXf).
    { unfold dXf. destruct (Z.eq_dec r 0) as [R0|RN].
      - flat constr:((XOK R0)) 2%nat. intros XARR' LEN'. subst r.
        destruct (grow_ok_facts asegs m2 LB3 LB dX dX3 16 MX3 OUT3 GR ltac:(clear; lia)) as (GO & _).
        eapply (relimb_at asegs m2 mm' LB3 dX3 xs' MX3 GO); [rewrite OU1; exact CX5| exact XARR'| clear - LEN' LEN3; lia].
      - rewrite (XNE RN). exact MX3. }
    assert (EAf : md_addr dXf = X) by (unfold dXf; destruct (Z.eq_dec r 0); [cbn [relimb md_addr]; exact OU1| exact OU1]).
    assert (EBf : mpd_blk dXf = mpd_blk dX3) by (unfold dXf; destruct (Z.eq_dec r 0); reflexivity).
    assert (OUTf : mpd_out LB dX LB3 dXf).
    { unfold dXf. destruct (Z.eq_dec r 0); [| exact OUT3]. eapply mpd_out_ext; [exact OUT3| reflexivity| cbn [relimb md_own]; exact OU2| reflexivity]. }
    assert (RRf : reducer_R 16 dX LB r dXf).
    { unfold dXf. destruct (Z.eq_dec r 0) as [R0|RN].
      - subst r. exact (reducer_R_ok 16 dX dX3 LB LB3 xs' 0 asegs m2 MX3 OUT3 GR ltac:(clear; lia) ltac:(split; [clear; lia| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia])).
      - destruct GR as [[(R0 & _)|(RF & EQ)] _]; [exfalso; exact (RN R0)|]. subst r dX3. apply reducer_R_fail. }
    (* [comment removed for export] *)
    pose proof (presW_init_at R HIA h3 _ _ LB3 LF mm' (bv_unsigned sp) (arl_stklo R) [] h HH5
                  ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSh3 HS3 ltac:(clear; lia)) as PRES2.
    eapply (aevtA_cut_evtA_KF asegs R HIA h3 mo0).
    { eapply epi_walk with (h3 := h3) (LBa := mpd_keep LB dX) (LBb := LB3) (r := r);
        first [ exact HH5 | exact HCSh3 | exact PRES5 | exact PRES2 | exact FRSH3 | exact CFB | exact AP | eassumption | reflexivity
              | lazymatch goal with
                | |- fresh_apart _ (mpd_keep LB dX) LF FB 128 => apply fresh_apart_keep; exact FRSH
                | |- forall b', In b' (mpd_keep LB dX) -> In b' LB3 => intros b' Hb; eapply mpd_keep_out; [exact OUT3| exact Hb]
                end
              | match goal with |- ?g => idtac "EPI-PRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    destruct EP as (m9 & h4 & z0' & z1' & z2' & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3' & z4' & z5' & z6'
                    & -> & MI9 & ST9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    apply aevtA_done. intros mo9 [HK9 MF9].
    unfold mpi_binop_postA.
    do 14 eexists. exists m9, mo9, h4, LB3, dXf, r.
    split; [reflexivity|]. split; [exact MI9|]. split; [exact ST9|]. split; [exact MF9|].
    split; [pose proof (presW_presA asegs R HIA h3 _ LF _ _ _ _ _ PRES9) as HPF; rewrite HS3 in HPF; exact HPF|].
    split; [rewrite E4top; exact HT3|]. split; [rewrite E4stk; exact HS3|]. split; [rewrite E4flag; exact HF3|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; exact (HCSh3 x Hx)|].
    split; [rewrite E4vol; exact HV3|].
    split; [rewrite E4fr; unfold red_FRn; exact HFR3|].
    split; [exact HH4|].
    split.
    { flat constr:(MXf) 2%nat. intros FLt3 _. flat constr:(FLt3) 6%nat. flclear FLt3. intros CXf _ _ _ _ OWNf.
      eapply (mpd_at_heap_presx asegs L) with (LBp := LB3 ++ fdata LF) (SP := bv_unsigned sp) (XI := []);
        [exact MXf| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA h3 _ LF _ _ _ _ _ PRES29))| exact MI5| exact MI9| | | exact I| intros _; exact I|].
      - rewrite EAf. eapply client_range_temp; [exact CRXk| clear; lia|].
        intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; eapply mpd_keep_out; [exact OUT3| exact Hb]| right; exact Hb].
      - intros EO. rewrite EO in OWNf. flat constr:(OWNf) 3%nat. flclear OWNf. intros N1 XIN _. eapply client_range_block; [apply in_app_iff; left; exact XIN| clear; lia| clear - N1; lia].
      - intros b' Hb. unfold mpd_blk in Hb. destruct (md_own dXf) eqn:EO; try (destruct Hb; fail). destruct Hb as [<-|[]]. flat constr:(OWNf) 3%nat. flclear OWNf. intros _ XIN _. exact XIN. }
    split; [exact OUTf|].
    split.
    { intros b' Hb. rewrite EBf in Hb. destruct (FRS3 b' Hb) as [K|K]; [left; exact K| right].
      flat constr:(K) 4%nat. flclear K. intros K0 K1 K2 K3. split; [exact K0|]. split; [exact K1|]. split; [exact K2|].
      intros B j HB. apply K3. apply fdata_cons_sub. exact HB. }
    exact RRf.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  End Call.

  Theorem A_ecp_mod_p255_spec_s : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p255 ()) "P,Ph,(3.$4.VR,VHIA,)PLB,(7.$36.)PLF,(7.$36.)Pm,P,(5.&40.)(6.(5.&8.))P,(19.$4.VR,VHIA,R4.R3.R2.R1.)(56.$2.(57.(1;.$2.$2.)$2.(58.$2.$2.)R4.))(59.$4.VR,VHIA,$34.+10.+140.)")
(* [comment removed for export] *).
  Proof.
    intros HND. unfold ecp_reducer_stmtA. intros until d.
    intros HH HK LFB MX NST XW XLS ST LOS SLO TOP SPA TPV MI RAE OXA BUD UW UWX BUDF C24H ->.
    eapply r_main; eassumption.
  Qed.
End RED.

Theorem A_ecp_mod_p255_spec : ltac2:(CDefT.buildp (gd_tbl_A_ecp_mod_p255 ()) "PR,$5:.PHIA,(5;.$4.R1.)P,(5<.(11.R2.))P,(9.$2.(5=.R3.)$5>.)P,(9.$2.(5?.R4.+1.)$60.)P,(15.=(61.R5.))P,(15.=(62.R6.))P,(63.$4.R7.R6.$12.)P,(9.$2.(64.R8.)$65.)P,(8.(15.(66.(67.R9.))(68.(67.R9.)))(15.(69.(67.R9.))(6:.(67.R9.))))P,Ph,(3.$4.R:.R9.)PLB,(7.$36.)PLF,(7.$36.)Pm,P,(5.&40.)(6.(5.&8.))P,(19.$4.R>.R=.R4.R3.R2.R1.)(56.$2.(57.(1;.$2.$2.)$2.(58.$2.$2.)R4.))(59.$4.R;.R:.$34.+10.+140.)")
(* [comment removed for export] *).
Proof. intros. eapply A_ecp_mod_p255_spec_s; eauto. Qed.
