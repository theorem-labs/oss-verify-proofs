(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd RepEcp EcpFacts EcpCurves EcpLoad.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_grow P_mpi_free P_ecp_group_free P_ecp_red P_ecp_mul_mod.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_mpi_stmtA A_mpi_stmtA_sz A_ecp_stmtA A_mpi_opnd A_mpi_journey A_mpi_journey2 A_mpi_copy A_mpi_bitlen A_mpi_init A_mpi_free A_mpi_shift_r A_mpi_add_int A_ecp_mul_mod A_ecp_journey A_ecp_journey2 A_ecp_pair.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt LxAEcpSums.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24 AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXA Require Import LxFlat.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00360b852df98c46 1 2 16 2 20 1 61 1 16 2 60 1 61 1 6 0 1 35 1 44 1 53 1 61 1 62 1P007a6497713366be 1 11 32 2 12 1 96 1 32 2 13 1 95 1 32 2 14 1 95 1 32 2 15 1 96 1 32 2 30 1 95 1 16 3 0 1 96 1 97 1 16 2 2 1 98 1 16 2 11 1 97 1 16 2 24 1 97 1 16 3 61 1 96 1 97 1 16 2 94 1 97 1 4 60 2 95 2 98 2 104 32P00b4b297add5b8cb 1 2 16 2 20 1 61 1 16 2 60 1 61 1 4 0 1 41 1 61 1 62 1N014f9ccddcdf8c40P015cd3dfbdb59c44 1 4 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 5 0 1 55 1 74 1 94 1 95 1P01e09a6481c265d1 1 2 16 2 20 1 61 1 16 2 60 1 61 1 6 0 1 35 1 44 1 53 1 61 1 62 1P021faf2a40aef397 1 4 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 5 0 1 55 1 74 1 94 1 95 1N028b5b977d8e8abbN0332095b3f95da76N037dc3c13624ca81P0393f48f70dc8ec1 1 2 16 2 20 1 61 1 16 2 60 1 61 1 4 0 1 41 1 61 1 62 1P03b063066c39a358 1 2 16 2 20 1 61 1 16 2 60 1 61 1 6 0 1 35 1 44 1 53 1 61 1 62 1N03b8633aa5ef2a8cP03dc295651a727a9 1 5 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 16 6 61 1 62 1 64 1 77 1 86 1 95 1 8 0 1 64 1 75 1 76 1 77 1 86 1 94 1 95 1N0496e7aae8f17d95P054f6d35b9ab7907 1 2 16 2 20 1 61 1 16 2 60 1 61 1 6 0 1 35 1 44 1 53 1 61 1 62 1P05871ade7e48a3cd 1 2 16 2 20 1 61 1 16 2 60 1 61 1 6 0 1 35 1 44 1 53 1 61 1 62 1P06726ba578aca29a 1 4 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 5 0 1 55 1 74 1 94 1 95 1N06b2f8ecbe8c3337P0703886b4e3646a9 1 4 16 2 2 1 104 1 16 2 5 1 103 1 16 2 28 1 103 1 16 2 102 1 103 1 6 0 1 77 1 86 1 95 1 103 1 104 1P07614ba8ece4d4ce 1 4 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 5 0 1 55 1 74 1 94 1 95 1P08424e5b9405c84c 1 13 32 2 4 1 95 1 32 2 5 1 94 1 32 2 6 1 94 1 32 2 7 1 95 1 32 2 32 1 94 1 16 3 0 1 95 1 96 1 16 2 3 1 96 1 16 2 9 1 97 1 16 2 30 1 96 1 16 2 93 1 96 1 32 4 49 1 94 1 97 1 106 16 32 3 31 1 97 1 103 16 512 5 31 16 50 16 95 16 96 16 97 16 4 49 1 94 1 97 1 103 16N095107722d74f0b3P09584ff887511f7d 1 5 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 16 6 61 1 62 1 64 1 77 1 86 1 95 1 8 0 1 64 1 75 1 76 1 77 1 86 1 94 1 95 1P0abdd72458a865f9 1 5 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 16 6 61 1 62 1 64 1 77 1 86 1 95 1 8 0 1 64 1 75 1 76 1 77 1 86 1 94 1 95 1P0ad0c1a537030835 1 5 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 16 6 61 1 62 1 64 1 77 1 86 1 95 1 8 0 1 64 1 75 1 76 1 77 1 86 1 94 1 95 1N0c4ad87c3fc92efdP0c51da9a0397ee70 1 2 16 2 20 1 61 1 16 2 60 1 61 1 4 0 1 41 1 61 1 62 1P0c5600abc4d46018 1 16 64 2 6 1 96 1 64 2 8 1 96 1 64 2 9 1 97 1 64 2 40 1 97 1 16 3 0 1 97 1 98 1 16 3 1 1 96 1 99 1 16 2 3 1 99 1 16 2 12 1 98 1 16 2 25 1 98 1 16 2 95 1 98 1 16 3 15 1 58 1 98 1 4 2 105 1 108 1 64 3 2 1 98 1 105 16 4 2 104 1 106 1 64 10 39 1 70 1 72 1 77 1 78 1 79 1 88 1 96 1 99 1 108 16 1024 11 2 16 39 16 70 16 72 16 77 16 78 16 79 16 88 16 96 16 98 16 99 16 10 39 1 70 1 72 1 77 1 78 1 79 1 88 1 96 1 99 1 104 16P0c84370810bec08b 1 2 16 2 20 1 61 1 16 2 60 1 61 1 8 0 1 35 1 42 1 43 1 44 1 53 1 61 1 62 1P0cf094cc8f06632e 1 7 32 2 7 1 82 1 32 2 8 1 83 1 32 2 9 1 82 1 32 2 11 1 83 1 32 2 32 1 82 1 32 8 0 1 30 1 52 1 63 1 64 1 65 1 74 1 82 1 32 9 38 1 42 1 52 1 54 1 63 1 64 1 65 1 74 1 83 1 9 0 1 38 1 52 1 63 1 64 1 65 1 74 1 82 1 83 1N0d835b0998eb3c5eP0da53000024f55eb 1 2 16 2 20 1 61 1 16 2 60 1 61 1 5 0 1 22 1 41 1 61 1 62 1P0dd88c3e680581fd 1 5 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 16 6 61 1 62 1 64 1 77 1 86 1 95 1 8 0 1 64 1 75 1 76 1 77 1 86 1 94 1 95 1P0dea60aa0d67815d 1 7 32 2 6 1 104 1 32 2 7 1 103 1 32 2 12 1 103 1 32 2 13 1 104 1 32 2 34 1 103 1 32 6 0 1 28 1 77 1 86 1 95 1 103 1 32 9 65 1 71 1 77 1 79 1 84 1 85 1 86 1 95 1 104 1 7 0 1 65 1 77 1 86 1 95 1 103 1 104 1N0e37e212e393013aN0e72d29b9b2188d3P0f5ac9023b71febd 1 2 16 2 20 1 61 1 16 2 60 1 61 1 8 0 1 35 1 42 1 43 1 44 1 53 1 61 1 62 1P100492631d3eec75 1 2 16 2 20 1 61 1 16 2 60 1 61 1 5 0 1 22 1 41 1 61 1 62 1P109b2209717ec6d8 1 5 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 16 6 61 1 62 1 64 1 77 1 86 1 95 1 8 0 1 64 1 75 1 76 1 77 1 86 1 94 1 95 1N11754416d456eb08N11cfdd8b3530ed02P12dc73ee41a944b5 1 7 32 2 12 1 96 1 32 2 13 1 95 1 32 2 14 1 95 1 32 2 15 1 96 1 32 2 30 1 95 1 32 6 0 1 24 1 69 1 78 1 87 1 95 1 32 9 57 1 63 1 69 1 71 1 76 1 77 1 78 1 87 1 96 1 7 0 1 57 1 69 1 78 1 87 1 95 1 96 1P1329b7f1b9d9d74c 1 5 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 16 6 61 1 62 1 64 1 77 1 86 1 95 1 8 0 1 64 1 75 1 76 1 77 1 86 1 94 1 95 1N1343acd4bb841bf8N13a8d2afbd0b6cb3P13dd32d9a938a186 1 5 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 16 6 61 1 62 1 64 1 77 1 86 1 95 1 8 0 1 64 1 75 1 76 1 77 1 86 1 94 1 95 1P140989321afb93f8 1 11 32 2 13 1 97 1 32 2 14 1 96 1 32 2 15 1 96 1 32 2 16 1 97 1 32 2 31 1 96 1 32 3 0 1 96 1 99 1 32 3 1 1 97 1 98 1 64 2 6 1 98 1 64 2 8 1 98 1 64 2 9 1 99 1 64 2 40 1 99 1 2 105 2 106 2P140d93b475697f41 1 13 32 2 4 1 95 1 32 2 5 1 94 1 32 2 6 1 94 1 32 2 7 1 95 1 32 2 32 1 94 1 16 3 0 1 95 1 96 1 16 2 3 1 96 1 16 2 9 1 97 1 16 2 30 1 96 1 16 2 93 1 96 1 32 4 49 1 94 1 97 1 106 16 512 5 31 16 50 16 95 16 96 16 97 16 2 2 103 1 105 1 4 49 1 94 1 97 1 103 16N1417ed358fe7a93cP14e2ff496b166fea 1 3 64 2 0 1 82 1 64 2 1 1 82 1 64 2 49 1 83 1 3 2 1 83 1 84 64P151001b8573aa499 1 2 64 2 1 1 82 1 64 2 49 1 83 1 3 0 1 82 1 85 64P161663c87287c514 1 5 32 2 12 1 96 1 32 2 13 1 95 1 32 2 14 1 95 1 32 2 15 1 96 1 32 2 30 1 95 1 6 0 1 49 1 60 1 75 1 95 1 96 1P169dbd730ae955ec 1 4 64 2 5 1 95 1 64 2 7 1 95 1 64 2 8 1 96 1 64 2 39 1 96 1 3 0 1 96 1 97 64P1753c39fe5859a11 1 2 16 2 20 1 61 1 16 2 60 1 61 1 5 0 1 22 1 41 1 61 1 62 1N175c996f864aac2fP182b64ec12f3ed1b 1 2 16 2 20 1 61 1 16 2 60 1 61 1 5 0 1 22 1 41 1 61 1 62 1N188c4d797da53f61P18aad9681cd3a040 1 3 16 2 0 1 61 1 16 2 20 1 61 1 16 2 60 1 61 1 3 4 1 62 1 63 16P192c0cbaa3ea37c4 1 4 16 2 6 1 83 1 16 2 10 1 82 1 16 2 30 1 82 1 16 2 81 1 82 1 5 0 1 43 1 62 1 82 1 83 1N198bcccad7f3964aP19ce22f6d613d0a4 1 2 16 2 20 1 61 1 16 2 60 1 61 1 5 0 1 22 1 41 1 61 1 62 1P1a52fee3c412e519 0 3 0 1 40 1 46 1N1b165ec6b22b8009P1b5ac7853e209d95 1 2 16 2 20 1 61 1 16 2 60 1 61 1 6 0 1 35 1 44 1 53 1 61 1 62 1P1b62847e9bbb4946 1 2 16 2 20 1 61 1 16 2 60 1 61 1 8 0 1 35 1 42 1 43 1 44 1 53 1 61 1 62 1P1b99b630d6a86493 1 5 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 16 6 61 1 62 1 64 1 77 1 86 1 95 1 8 0 1 64 1 75 1 76 1 77 1 86 1 94 1 95 1P1bbc742bf42b6071 1 2 16 2 20 1 61 1 16 2 60 1 61 1 6 0 1 35 1 44 1 53 1 61 1 62 1N1c0724da98320d78N1c5dfb9894bb81d5P1d0933374665085d 1 11 32 2 6 1 104 1 32 2 7 1 103 1 32 2 12 1 103 1 32 2 13 1 104 1 32 2 34 1 103 1 16 3 0 1 104 1 105 1 16 2 2 1 106 1 16 2 5 1 105 1 16 2 28 1 105 1 16 3 69 1 104 1 105 1 16 2 102 1 105 1 4 68 2 103 2 106 2 112 32P1e3854ed16036592 1 12 32 2 13 1 97 1 32 2 14 1 96 1 32 2 15 1 96 1 32 2 16 1 97 1 32 2 31 1 96 1 16 3 0 1 97 1 98 1 16 3 1 1 96 1 99 1 16 2 3 1 99 1 16 2 12 1 98 1 16 2 25 1 98 1 16 3 62 1 97 1 98 1 16 2 95 1 98 1 4 61 2 96 2 99 2 105 32P1edb254b2413fba7 1 2 16 2 20 1 61 1 16 2 60 1 61 1 4 0 1 41 1 61 1 62 1N1ee75248dad54e1dN1f39dd6e8dad7332P1f86995f0eefb41e 1 14 32 2 12 1 96 1 32 2 13 1 95 1 32 2 14 1 95 1 32 2 15 1 96 1 32 2 30 1 95 1 32 3 0 1 95 1 98 1 64 2 5 1 97 1 64 2 7 1 97 1 64 2 8 1 98 1 64 2 39 1 98 1 32 3 24 1 60 1 95 1 64 9 24 1 38 1 69 1 71 1 76 1 77 1 78 1 87 1 97 1 32 10 38 1 57 1 69 1 71 1 76 1 77 1 78 1 87 1 96 1 97 1 32 9 57 1 63 1 69 1 71 1 76 1 77 1 78 1 87 1 96 1 2 104 2 111 2N1f8abd5972feab6cP1fadadeb1f25f4ad 0 3 0 1 27 1 39 1N206331d00d39bc2eP209b3550f49e9988 1 2 16 2 20 1 61 1 16 2 60 1 61 1 5 0 1 22 1 41 1 61 1 62 1P214faeadec564abf 1 2 16 2 20 1 61 1 16 2 60 1 61 1 6 0 1 35 1 44 1 53 1 61 1 62 1P21a7e928df006800 1 2 64 2 1 1 82 1 64 2 49 1 83 1 3 0 1 83 1 84 64P21c1e936b8928100 1 5 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 16 6 61 1 62 1 64 1 77 1 86 1 95 1 8 0 1 64 1 75 1 76 1 77 1 86 1 94 1 95 1P21ec5583492869a2 1 4 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 5 0 1 55 1 74 1 94 1 95 1N22acea90ee9cc161P22f7848a3998a6db 1 4 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 5 0 1 55 1 74 1 94 1 95 1P234e52394518d4c3 1 2 16 2 20 1 61 1 16 2 60 1 61 1 4 0 16 3 16 61 16 62 16N237f04bf769c7f64P23cb7c5cb638296a 1 2 16 2 20 1 61 1 16 2 60 1 61 1 6 0 1 35 1 44 1 53 1 61 1 62 1P24585f197e302fd1 1 2 16 2 20 1 61 1 16 2 60 1 61 1 4 0 1 41 1 61 1 62 1N249bc18298f29f2aN254641d5c7dab1e7P259e67da6fac26c8 1 4 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 5 0 1 55 1 74 1 94 1 95 1P25c8a3f438ea64e9 1 2 16 2 20 1 61 1 16 2 60 1 61 1 5 0 1 22 1 41 1 61 1 62 1P25e263585e4bea26 1 2 16 2 20 1 61 1 16 2 60 1 61 1 6 0 1 35 1 44 1 53 1 61 1 62 1P26149768d224ee31 1 16 64 2 6 1 96 1 64 2 8 1 96 1 64 2 9 1 97 1 64 2 40 1 97 1 16 3 0 1 97 1 98 1 16 3 1 1 96 1 99 1 16 2 3 1 99 1 16 2 12 1 98 1 16 2 25 1 98 1 16 2 95 1 98 1 16 3 15 1 58 1 98 1 4 2 105 1 108 1 64 3 2 1 98 1 105 16 64 9 64 1 70 1 72 1 77 1 78 1 79 1 88 1 99 1 104 16 64 10 39 1 70 1 72 1 77 1 78 1 79 1 88 1 96 1 99 1 108 16 1024 11 2 16 39 16 70 16 72 16 77 16 78 16 79 16 88 16 96 16 98 16 99 16 10 39 1 70 1 72 1 77 1 78 1 79 1 88 1 96 1 99 1 104 16N26f8ec9d9a163ff1N272f7d25fb787f3cP2744fdd1359ba9a8 1 13 32 2 4 1 95 1 32 2 5 1 94 1 32 2 6 1 94 1 32 2 7 1 95 1 32 2 32 1 94 1 16 3 0 1 95 1 96 1 16 2 3 1 96 1 16 2 9 1 97 1 16 2 30 1 96 1 16 2 93 1 96 1 32 4 49 1 94 1 97 1 106 16 32 3 31 1 97 1 103 16 512 5 31 16 50 16 95 16 96 16 97 16 4 49 1 94 1 97 1 103 16P2791251263f681ea 1 2 16 2 20 1 61 1 16 2 60 1 61 1 5 0 1 22 1 41 1 61 1 62 1P28263e203d6f1d30 1 13 32 2 4 1 95 1 32 2 5 1 94 1 32 2 6 1 94 1 32 2 7 1 95 1 32 2 32 1 94 1 16 3 0 1 95 1 96 1 16 2 3 1 96 1 16 2 9 1 97 1 16 2 30 1 96 1 16 2 93 1 96 1 32 4 49 1 94 1 97 1 106 16 32 3 31 1 97 1 103 16 512 5 31 16 50 16 95 16 96 16 97 16 4 49 1 94 1 97 1 103 16P2862ebf45181c450 1 7 32 2 4 1 95 1 32 2 5 1 94 1 32 2 6 1 94 1 32 2 7 1 95 1 32 2 32 1 94 1 32 6 0 1 30 1 64 1 77 1 86 1 94 1 32 9 50 1 54 1 64 1 66 1 75 1 76 1 77 1 86 1 95 1 7 0 1 50 1 64 1 77 1 86 1 94 1 95 1P29058d85dd1fc099 1 5 16 2 6 1 83 1 16 2 10 1 82 1 16 2 30 1 82 1 16 2 81 1 82 1 16 6 49 1 50 1 52 1 65 1 74 1 83 1 8 0 1 52 1 63 1 64 1 65 1 74 1 82 1 83 1P2a8c64e22e3002f4 1 2 16 2 20 1 61 1 16 2 60 1 61 1 5 0 1 22 1 41 1 61 1 62 1N2a9bb56676fd1a6eP2b1ba3f0972c0489 1 15 32 2 13 1 97 1 32 2 14 1 96 1 32 2 15 1 96 1 32 2 16 1 97 1 32 2 31 1 96 1 32 3 0 1 96 1 99 1 32 3 1 1 97 1 98 1 64 2 6 1 98 1 64 2 8 1 98 1 64 2 9 1 99 1 64 2 40 1 99 1 32 3 25 1 61 1 96 1 64 9 25 1 39 1 70 1 72 1 77 1 78 1 79 1 88 1 98 1 32 10 39 1 58 1 70 1 72 1 77 1 78 1 79 1 88 1 97 1 98 1 32 9 58 1 64 1 70 1 72 1 77 1 78 1 79 1 88 1 97 1 2 105 2 113 2P2b6a6c61540d9d58 1 11 32 2 13 1 97 1 32 2 14 1 96 1 32 2 15 1 96 1 32 2 16 1 97 1 32 2 31 1 96 1 32 3 0 1 96 1 99 1 32 3 1 1 97 1 98 1 64 2 6 1 98 1 64 2 8 1 98 1 64 2 9 1 99 1 64 2 40 1 99 1 2 105 2 106 2P2b7cc7f4e05828e6 1 2 16 2 20 1 61 1 16 2 60 1 61 1 8 0 1 35 1 42 1 43 1 44 1 53 1 61 1 62 1P2ba8bae70749df54 1 4 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 5 0 1 55 1 74 1 94 1 95 1P2beb0b72ce6d5743 1 14 64 2 2 1 83 1 64 2 50 1 84 1 16 3 0 1 84 1 85 1 16 3 1 1 83 1 86 1 16 2 7 1 86 1 16 2 11 1 85 1 16 2 31 1 85 1 16 2 82 1 85 1 16 3 8 1 39 1 85 1 4 2 90 1 93 1 64 3 6 1 85 1 90 16 4 2 89 1 91 1 64 10 49 1 53 1 55 1 64 1 65 1 66 1 75 1 83 1 86 1 93 16 1024 11 6 16 49 16 53 16 55 16 64 16 65 16 66 16 75 16 83 16 85 16 86 16 10 49 1 53 1 55 1 64 1 65 1 66 1 75 1 83 1 86 1 89 16P2c24678eca268f0f 1 7 32 2 12 1 96 1 32 2 13 1 95 1 32 2 14 1 95 1 32 2 15 1 96 1 32 2 30 1 95 1 32 9 57 1 63 1 69 1 71 1 76 1 77 1 78 1 87 1 96 1 32 8 0 1 24 1 69 1 76 1 77 1 78 1 87 1 95 1 9 0 1 57 1 69 1 76 1 77 1 78 1 87 1 95 1 96 1P2cc2137e42c5a7fb 1 5 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 16 6 61 1 62 1 64 1 77 1 86 1 95 1 8 0 1 64 1 75 1 76 1 77 1 86 1 94 1 95 1P2cdeac5dccacf83e 1 2 16 2 20 1 61 1 16 2 60 1 61 1 5 0 1 22 1 41 1 61 1 62 1P2d656e767292da8f 1 2 16 2 20 1 61 1 16 2 60 1 61 1 6 0 1 35 1 44 1 53 1 61 1 62 1P2d6c8a59861e6464 1 4 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 5 0 1 55 1 74 1 94 1 95 1P2dd868c6be1805a2 1 4 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 5 0 1 55 1 74 1 94 1 95 1P2df9ba6ff5bcf781 1 2 16 2 20 1 61 1 16 2 60 1 61 1 4 0 1 41 1 61 1 62 1N2e461e1e41ba955eP2e68fa18b84a8fa1 1 2 16 2 20 1 61 1 16 2 60 1 61 1 4 0 1 41 1 61 1 62 1P2ea535753a097d22 1 14 32 2 12 1 96 1 32 2 13 1 95 1 32 2 14 1 95 1 32 2 15 1 96 1 32 2 30 1 95 1 32 3 0 1 95 1 98 1 64 2 5 1 97 1 64 2 7 1 97 1 64 2 8 1 98 1 64 2 39 1 98 1 32 3 24 1 60 1 95 1 64 9 24 1 38 1 69 1 71 1 76 1 77 1 78 1 87 1 97 1 32 10 38 1 57 1 69 1 71 1 76 1 77 1 78 1 87 1 96 1 97 1 32 9 57 1 63 1 69 1 71 1 76 1 77 1 78 1 87 1 96 1 2 104 2 111 2P2eaf491a7be63e43 1 2 16 2 20 1 61 1 16 2 60 1 61 1 8 0 1 35 1 42 1 43 1 44 1 53 1 61 1 62 1P30b399387677b09b 1 2 16 2 20 1 61 1 16 2 60 1 61 1 6 0 1 35 1 44 1 53 1 61 1 62 1N312b6093f741fd84N31311d3a61e67a56P313763f045690fdb 1 2 16 2 20 1 61 1 16 2 60 1 61 1 4 0 1 41 1 61 1 62 1N3267f2f80f117dd6P327ede608dc95128 1 4 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 5 0 1 55 1 74 1 94 1 95 1N32b44cd3b0b81ac1N32d0ccac28fa7cf9N3300667efb19c5cdN3325bd65fcbe3721P33741f0e563a823e 1 5 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 16 6 61 1 62 1 64 1 77 1 86 1 95 1 8 0 1 64 1 75 1 76 1 77 1 86 1 94 1 95 1N3398a9f25ad8424aP33a87046ff7dcc6d 1 11 32 2 13 1 97 1 32 2 14 1 96 1 32 2 15 1 96 1 32 2 16 1 97 1 32 2 31 1 96 1 32 3 0 1 97 1 98 1 32 3 1 1 96 1 99 1 64 2 6 1 98 1 64 2 8 1 98 1 64 2 9 1 99 1 64 2 40 1 99 1 2 105 2 106 2P340f792c07c60d93 1 2 16 2 20 1 61 1 16 2 60 1 61 1 4 0 1 41 1 61 1 62 1N3435d286a7b13304P345fdc77e6086a22 1 2 16 2 20 1 61 1 16 2 60 1 61 1 8 0 1 35 1 42 1 43 1 44 1 53 1 61 1 62 1P3460319a042c056f 1 2 16 2 20 1 61 1 16 2 60 1 61 1 8 0 1 35 1 42 1 43 1 44 1 53 1 61 1 62 1N34b1b205570ee29fP34b9bbd8f0f2bbe2 1 2 16 2 20 1 61 1 16 2 60 1 61 1 8 0 1 35 1 42 1 43 1 44 1 53 1 61 1 62 1P35208a4f23f52dba 1 9 32 2 8 1 83 1 32 2 9 1 84 1 32 2 10 1 83 1 32 2 12 1 84 1 32 2 33 1 83 1 32 3 0 1 83 1 86 1 32 3 1 1 84 1 85 1 64 2 2 1 85 1 64 2 50 1 86 1 2 92 2 93 2P3555c254caa19cde 1 16 64 2 6 1 96 1 64 2 8 1 96 1 64 2 9 1 97 1 64 2 40 1 97 1 16 3 0 1 97 1 98 1 16 3 1 1 96 1 99 1 16 2 3 1 99 1 16 2 12 1 98 1 16 2 25 1 98 1 16 2 95 1 98 1 16 3 15 1 58 1 98 1 4 2 105 1 108 1 64 3 2 1 98 1 105 16 64 9 64 1 70 1 72 1 77 1 78 1 79 1 88 1 99 1 104 16 64 10 39 1 70 1 72 1 77 1 78 1 79 1 88 1 96 1 99 1 108 16 1024 11 2 16 39 16 70 16 72 16 77 16 78 16 79 16 88 16 96 16 98 16 99 16 10 39 1 70 1 72 1 77 1 78 1 79 1 88 1 96 1 99 1 104 16N361ee9b3bef5f51dP365550e83d9632b5 1 2 16 2 20 1 61 1 16 2 60 1 61 1 4 0 1 41 1 61 1 62 1P365e0436ee317de4 1 2 16 2 20 1 61 1 16 2 60 1 61 1 8 0 1 35 1 42 1 43 1 44 1 53 1 61 1 62 1P36cf4cffcc4c3b67 1 2 16 2 20 1 61 1 16 2 60 1 61 1 8 0 1 35 1 42 1 43 1 44 1 53 1 61 1 62 1P372fb8fe989370bb 1 4 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 5 0 1 55 1 74 1 94 1 95 1P37928e36868884e7 1 15 32 2 13 1 97 1 32 2 14 1 96 1 32 2 15 1 96 1 32 2 16 1 97 1 32 2 31 1 96 1 32 3 0 1 97 1 98 1 32 3 1 1 96 1 99 1 64 2 6 1 98 1 64 2 8 1 98 1 64 2 9 1 99 1 64 2 40 1 99 1 32 3 25 1 61 1 96 1 64 9 25 1 39 1 70 1 72 1 77 1 78 1 79 1 88 1 98 1 32 10 39 1 58 1 70 1 72 1 77 1 78 1 79 1 88 1 97 1 98 1 32 9 58 1 64 1 70 1 72 1 77 1 78 1 79 1 88 1 97 1 2 106 2 113 2P3794656c27272901 1 2 16 2 20 1 61 1 16 2 60 1 61 1 6 0 1 35 1 44 1 53 1 61 1 62 1P37b447f60ef74e04 1 2 16 2 20 1 61 1 16 2 60 1 61 1 5 0 1 22 1 41 1 61 1 62 1P38078e5fb0a46e90 1 2 16 2 20 1 61 1 16 2 60 1 61 1 8 0 1 35 1 42 1 43 1 44 1 53 1 61 1 62 1N39334ecec907c8e3P39869afec0797c41 1 4 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 5 0 1 55 1 74 1 94 1 95 1P3a284f51c6f46bfb 1 2 16 2 20 1 61 1 16 2 60 1 61 1 6 0 1 35 1 44 1 53 1 61 1 62 1P3a28b34e364fee3c 1 2 16 2 20 1 61 1 16 2 60 1 61 1 5 0 1 22 1 41 1 61 1 62 1P3a8e632042603239 1 14 32 2 6 1 104 1 32 2 7 1 103 1 32 2 12 1 103 1 32 2 13 1 104 1 32 2 34 1 103 1 32 3 0 1 103 1 106 1 64 2 3 1 105 1 64 2 4 1 106 1 64 2 8 1 105 1 64 2 47 1 106 1 32 3 28 1 68 1 103 1 64 9 28 1 46 1 77 1 79 1 84 1 85 1 86 1 95 1 105 1 32 10 46 1 65 1 77 1 79 1 84 1 85 1 86 1 95 1 104 1 105 1 32 9 65 1 71 1 77 1 79 1 84 1 85 1 86 1 95 1 104 1 2 112 2 119 2N3ae2a024065ddb7eP3af8cc28a4456889 1 2 16 2 20 1 61 1 16 2 60 1 61 1 4 0 1 41 1 61 1 62 1P3aff721ab49ab207 1 13 64 2 5 1 95 1 64 2 7 1 95 1 64 2 8 1 96 1 64 2 39 1 96 1 16 3 0 1 96 1 97 1 16 2 2 1 98 1 16 2 11 1 97 1 16 2 24 1 97 1 16 2 94 1 97 1 16 3 14 1 57 1 97 1 4 2 103 1 104 1 64 10 38 1 69 1 71 1 76 1 77 1 78 1 87 1 95 1 98 1 106 16 1024 11 1 16 38 16 69 16 71 16 76 16 77 16 78 16 87 16 95 16 97 16 98 16 10 38 1 69 1 71 1 76 1 77 1 78 1 87 1 95 1 98 1 103 16P3b10e937eb37b78f 1 2 16 2 20 1 61 1 16 2 60 1 61 1 4 0 1 41 1 61 1 62 1P3bcc2bcbf5c305a6 1 2 16 2 20 1 61 1 16 2 60 1 61 1 4 0 1 41 1 61 1 62 1P3c50e6487def0948 1 5 16 2 3 1 94 1 16 2 9 1 95 1 16 2 30 1 94 1 16 2 93 1 94 1 16 6 61 1 62 1 64 1 77 1 86 1 95 1 8 0 1 64 1 75 1 76 1 77 1 86 1 94 1 95 1P3cd95bb19c605284 1 2 16 2 20 1 61 1 16 2 60 1 61 1 5 0 1 22 1 41 1 61 1 62 1P3d04045ad0306f8a 1 2 16 2 20 1 61 1 16 2 60 1 61 1 8 0 1 35 1 42 1 43 1 44 1 53 1 61 1 62 1P3d6ce4cecdf8117f 1 7 32 2 12 1 96 1 32 2 13 1 95 1 32 2 14 1 95 1 32 2 15 1 96 1 32 2 30 1 95 1 32 3 24 1 60 1 95 1 32 5 0 1 2 1 55 1 75 1 96 1 6 0 1 55 1 60 1 75 1 95 1 96 1P3d80491400c32bb6 1 2 16 2 20 1 61 1 16 2 60 1 61 1 8 0 1 35 1 42 1 43 1 44 1 53 1 61 1 62 1P3e2da6038499103e 1 7 32 2 7 1 82 1 32 2 8 1 83 1 32 2 9 1 82 1 32 2 11 1 83 1 32 2 32 1 82 1 32 3 30 1 37 1 82 1 32 5 0 1 6 1 43 1 62 1 83 1 6 0 1 37 1 43 1 62 1 82 1 83 1P3eb3715a80aee005 1 2 16 2 20 1 61 1 16 2 60 1 61 1 4 0 1 41 1 61 1 62 1P3ed3c2928b088abc 1 2 16 2 20 1 61 1 16 2 60 1 61 1 5 0 1 22 1 41 1 61 1 62 1P3eda4275f15ff4aa 1 2 16 2 20 1 61 1 16 2 60 1 61 1 8 0 1 35 1 42 1 43 1 44 1 53 1 61 1 62 1P3fe6d058c2f4ca6a 1 5 64 2 0 1 95 1 64 2 5 1 95 1 64 2 7 1 95 1 64 2 8 1 96 1 64 2 39 1 96 1 3 6 1 96 1 97 64P3fe7cded82f60590 1 4 16 2 2 1 96 1 16 2 11 1 95 1 16 2 24 1 95 1 16 2 94 1 95 1 6 0 1 69 1 78 1 87 1 95 1 96 1P3ff536aaa4280455 1 13 64 2 3 1 103 1 64 2 4 1 104 1 64 2 8 1 103 1 64 2 47 1 104 1 16 3 0 1 104 1 105 1 16 2 2 1 106 1 16 2 5 1 105 1 16 2 28 1 105 1 16 2 102 1 105 1 16 3 12 1 65 1 105 1 4 2 111 1 112 1 64 10 46 1 77 1 79 1 84 1 85 1 86 1 95 1 103 1 106 1 114 16 1024 11 1 16 46 16 77 16 79 16 84 16 85 16 86 16 95 16 103 16 105 16 106 16 10 46 1 77 1 79 1 84 1 85 1 86 1 95 1 103 1 106 1 111 16"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
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
Ltac2 gd_tbl_A_ecp_sw_derive_y () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.g_P"; "Corelib.Init.Logic.eq"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_range"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LNull"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.B.AImgGlobals.img_norz"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "DY.Call.S1P"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.A_ECP_SW_DERIVE_Y"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "DY.Call.EPOST"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_mul_mod_postA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.A_MUL_COUNT"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.derive_y_PHIn"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.derive_y_FRn"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_dy_sz"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_pad"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LStatic"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.opp"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.aevtA"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.KF"; "DY.Call.DY_POST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.alloc_ceiling"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.arl_need_ecp"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_journey.ej_ext"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_journey.EJ"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_pair.EPI"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.AVOL_CALL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fr_charge"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.sw_rhs_PHIn"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.sw_rhs_FRn"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.intop_PHIn"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.intop_FRn"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_sz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.exp_mod_PHIn"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.exp_mod_FRn"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.addsub_PHIn"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.addsub_FRn"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.calls_FR"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.Spec.RepEcp.modp_ent"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_uar_got"; "A_UAR_GOT_DY"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_smalloc"; "A_SMALLOC_0_DY"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_smalloc"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_lo"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_data_hi"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.hl_img_hi"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.ro_addr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wa"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_sw_rhs_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.A_ECP_SW_RHS"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_add_int_stmtA_sz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_ADD_INT"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_shift_r.mpi_shift_r_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_shift_r.A_MPI_SHIFT_R_E"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_exp_mod_stmtA_szT"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_EXP_MOD"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA_sz.mpi_sub_mpi_stmtA_sz"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_SUB_MPI"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_free.mpi_free_stmtA"; "RocqVerifyHarness.AgentSubmission.B.A_mpi_stmtA.A_MPI_FREE"; "RocqVerifyHarness.AgentSubmission.B.A_ecp_stmtA.ecp_derive_y_stmtA"].


Definition A_SMALLOC_0_DY : Z := 0x52ef8.          (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_UAR_GOT_DY : Z := 0xf5ea8.           (* [comment removed for export] *) (* [comment removed for export] *)
Section DY.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT_DY.
  Hypothesis SM0 : arl_smalloc R 0 = A_SMALLOC_0_DY.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis HND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis ROIMG : forall a, ro_addr asegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.
  Variable MT : list modp_ent.
  Local Notation MC := A_MUL_COUNT.
  Hypothesis HSR : ecp_sw_rhs_stmtA asegs R HIA MT A_ECP_SW_RHS MC.
  Hypothesis HADDI : mpi_add_int_stmtA_sz asegs R HIA A_MPI_ADD_INT.
  Hypothesis HSHR : mpi_shift_r_stmtA asegs R HIA A_MPI_SHIFT_R_E.
  Hypothesis HEXP : mpi_exp_mod_stmtA_szT asegs R HIA A_MPI_EXP_MOD.
  Hypothesis HSUBM : mpi_sub_mpi_stmtA_sz asegs R HIA A_MPI_SUB_MPI.
  Hypothesis HFREE : mpi_free_stmtA asegs R HIA A_MPI_FREE.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (dX dA : mpd) (G : Z) (g : ecp_grp) (cnt : word) (N lo d slo : Z) (par : word).
  Local Notation Y := (md_addr dX).
  Hypothesis HH : HM asegs R HIA h LB LF m.
  Hypothesis LFB : (length LF + 4 <= 512)%nat.
  Hypothesis GRP : ecp_grp_preA asegs R HIA MT h LB LF m G g MC lo (bv_unsigned sp) d.
  Hypothesis OSEP : ecp_out_sepA dX G MC.
  Hypothesis SGA : md_sg (g_A g) = 1.
  Hypothesis SGB : md_sg (g_B g) = 1.
  Hypothesis VP : 1 <= mpd_val (g_P g).
  Hypothesis P4999 : md_n (g_P g) <= 4999.
  Hypothesis NLE : grp_nle g N.
  Hypothesis NA : md_n dA <= N.
  Hypothesis MX0 : mpd_at asegs m LB dX.
  Hypothesis XNULL : md_own dX = LNull.
  Hypothesis XW : mpd_writableA R LB LF (bv_unsigned sp) (htop asegs R HIA h) dX.
  Hypothesis EXTA : ext_opndA asegs R HIA h LB LF m dX dA MC (bv_unsigned sp) lo d.
  Hypothesis MC0 : rw_cells asegs m MC [C8 cnt].
  Hypothesis MCOK : mc_okA R MC.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 1504 - arl_need_ecp R.
  Hypothesis SSH : sshad asegs AL m slo (bv_unsigned sp).
  Hypothesis SLO1 : arl_stklo R <= slo.
  Hypothesis SLO3 : slo <= lo.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis OXA : mpd_aobjA asegs AL CS m dX.
  Hypothesis BUD : havol asegs R HIA h + derive_y_PHIn N <= AVOL_MAX.
  Hypothesis UW : uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d.
  Hypothesis UWX : uw_obj R Y 16 d.
  Hypothesis BUDF : hfr asegs R HIA h + derive_y_FRn N d <= FR_MAX.
  Hypothesis C24H : cnt24 LB + C24_ECP_DERIVE_Y <= C24MAX.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT_DY in UARG; unfold A_SMALLOC_0_DY in SM0;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (arl_need_ecp_rt R) as NER; pose proof (arl_need_ecp_smalloc R) as NES;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation FSHP :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].
  Local Notation FSHU :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Local Notation dP := (g_P g).

  (* [comment removed for export] *)
  Lemma dy_P_entry : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_derive_y ()) "(0.(1.$2.Vm,VLB,(3.Vg,))(0.(4.$5.(6.(3.Vg,))(7.VG,+8.))(0.(8.(4.$9.(:.(3.Vg,))$;.))(0.(<.(=.VR,)(>.$?.VLB,(10.VLF,))(11.&40.Vsp,)(7.VG,+8.)+10.)(0.P,(8.(4.$9.(:.(3.Vg,))$12.))(0.(13.+1.(14.(3.Vg,)))(0.(15.=(16.(3.Vg,)))(0.(13.(7.(16.(3.Vg,))(17.+4.(14.(3.Vg,))))+65?000.)(4.$18.(19.(16.(3.Vg,))(17.+4.(14.(3.Vg,))))$1:.))))(1;.$2.(1<.VR,)(1=.$2.VR,VHIA,Vh,)Vm,(7.VG,+8.)+10.))))))")
(* [comment removed for export] *).
  Proof.
    flat constr:(GRP) 9%nat. intros GAT GH1 GPS GIMG GCR GSP GMC GOB GUW.
    assert (He : In dP (grp_mpds g)) by (unfold grp_mpds; cbn; left; reflexivity).
    flat constr:(GAT) 14%nat. intros HD GAL POS EP EA EB EN MP MA MB FLt1 MN HT REST. flat constr:(FLt1) 6%nat. flclear FLt1. intros EX EY EZ MXg MYg MZg.
    assert (NH : md_own dP <> LHeap) by (eapply (grp_static_own asegs); [exact GAT| exact GH1| exact He]).
    assert (EIM : mpd_imgA dP) by (unfold grp_imgA in GIMG; rewrite Forall_forall in GIMG; exact (GIMG dP He)).
    split; [split; [exact MP| left; exact GPS]|]. split; [exact EP|]. split; [exact NH|].
    split.
    { intros a Ha. destruct (GCR a ltac:(clear - Ha; lia)) as [S|[D|B]]; [| right; left; exact D| right; right; exact B].
      destruct GSP as [K|K]; [exfalso; clear - S Ha K; lia| left; clear - Ha K; lia]. }
    split.
    { intros NN. flat constr:(MP) 6%nat. intros _ _ _ DHL DHN DHO. unfold mpd_imgA in EIM.
      destruct (md_own dP) eqn:OD; [exfalso; apply NN; reflexivity| exfalso; apply NH; reflexivity|].
      flat constr:(DHO) 5%nat. flclear DHO. intros N1 _ P0 PB PRO.
      flat constr:((AImgGlobals.img_norz_sound _ _ (EIM eq_refl))) 4%nat. intros _ _ IHI _. unfold AImgGlobals.IMG_HI in IHI.
      split; [exact N1|]. split; [exact P0|]. split; [exact IHI| exact (EIM eq_refl)]. }
    eapply aobj_sub; [exact GOB| clear; lia| clear; lia].
  Qed.
  Lemma dy_P_at : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_derive_y ()) "Ph1,(1>.$2.VR,VHIA,)PLFx,(1?.$?.)Pmk,P,(20.&40.)(21.(20.&8.))P,(22.$2.VR,VLB,VLF,(11.&40.Vsp,)(23.VR,)(24.$2.VR,VHIA,Vh,)(25.$26.)Vm,R1.)P,(27.$2.R2.)P,(28.$2.VR,VHIA,R5.VLB,R4.R3.)P,(4.P,$5.Sp(1=.$2.VR,VHIA,R6.)(1=.$2.VR,VHIA,Vh,))(0.(1.$2.R5.VLB,(3.Vg,))(0.(1;.$2.(1<.VR,)(1=.$2.VR,VHIA,Vh,)R5.(7.VG,+8.)+10.)P,(13.+1.(14.(3.Vg,)))(1;.$2.(1<.VR,)(1=.$2.VR,VHIA,Vh,)R6.(16.(3.Vg,))(17.+4.(14.(3.Vg,))))))")
(* [comment removed for export] *).
  Proof.
    intros h1 LFx mk HP MIk HH1 Ehcs. flat constr:(dy_P_entry) 6%nat. flclear dy_P_entry. intros MP EP NH CRS DST OB. rt_facts.
    split.
    { eapply (mpd_at_heap_presx asegs L m mk LB (LB ++ fdata LF) LB (bv_unsigned sp) [] dP MP (presA_presx asegs R _ _ _ _ _ _ _ _ HP) MI MIk);
        [rewrite EP; exact CRS| intros EO; exfalso; exact (NH EO)| exact I| intros _; exact I|].
      intros b Hb. exfalso. unfold mpd_blk in Hb. destruct (md_own dP) eqn:EO; [destruct Hb| exact (NH eq_refl)| destruct Hb]. }
    split.
    { eapply (presA_aobj asegs R); [exact CSOK| exact HP| exact OB| exact CRS| clear - LOS SLO NEEDR NER; lia| intros x Hx; eapply hcs_below_top; exact Hx]. }
    intros N1.
    assert (NN : md_own dP <> LNull).
    { intros C. flat constr:(MP) 2%nat. intros FLt2 _. flat constr:(FLt2) 6%nat. flclear FLt2. intros _ _ _ _ _ OW. rewrite C in OW. flat constr:(OW) 2%nat. flclear OW. intros _ N0'. clear - N0' N1. lia. }
    flat constr:((DST NN)) 4%nat. intros _ _ _ IMGN.
    rewrite <- Ehcs. eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HH1| exact IMGN].
  Qed.

  (* [comment removed for export] *)
  Definition S1P : machine_state -> Prop := fun ms =>
    exists (FB sp1 : Z) (h1 : HST asegs R HIA) (m1 : mem) (early : bool)
           (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s8v : word) (w0 w1 w2 : word) (ecells : list cell),
      ms = MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 FB) (Z_to_bv 64 Y) par (Z_to_bv 64 (md_addr dA)) (Z_to_bv 64 G) (Z_to_bv 64 (-20096)) s8v (Z_to_bv 64 (G + 8))
                   (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
              F (Z_to_bv 64 (if early then 0xcb964 else 0xcb8d4)) fc None m1 (seg_rom asegs)
      /\ (early = false -> s8v = Z_to_bv 64 (FB + 32) /\ exists pad, ecells = mpi_cells 0 (Z_to_bv 64 1) 0 pad)
      /\ bv_unsigned sp - 144 <= sp1 <= bv_unsigned sp - 128 /\ sp1 mod 32 = 0
      /\ HM asegs R HIA h1 LB ((FB, 64) :: LF) m1 /\ hcs asegs R HIA h1 = CS /\ htop asegs R HIA h1 = htop asegs R HIA h
      /\ hstkhi asegs R HIA h1 = hstkhi asegs R HIA h /\ hflag asegs R HIA h1 = hflag asegs R HIA h
      /\ havol asegs R HIA h1 = havol asegs R HIA h /\ hfr asegs R HIA h1 = hfr asegs R HIA h
      /\ (forall mo, HK asegs R HIA h1 mo <-> HK asegs R HIA h mo)
      /\ FB mod 64 = 0 /\ fresh_apart R LB LF FB 64
      /\ rw_cells asegs m1 FB [C8 w0; C8 w1; C8 w2]
      /\ rw_cells asegs m1 (FB + 32) ecells /\ Z.of_nat (cells_size ecells) = 16
      /\ rw_cells asegs m1 (Z.shiftr FB 3 + al_sb AL) (if early then FSHP else FSHU)
      /\ rw_cells asegs m1 (bv_unsigned sp + -104) SAVEL
      /\ rw_cells asegs m1 (sp1 + 16) [C8 (Z_to_bv 64 FB)] /\ stk asegs m1 sp1 (sp1 + 16) /\ stk asegs m1 (sp1 + 24) (bv_unsigned sp + -104)
      /\ stk asegs m1 lo sp1 /\ mem_inv asegs m1
      /\ presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [] m m1
      /\ sshad asegs AL m1 slo (bv_unsigned sp).
  Lemma pro_walk : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_derive_y ()) "Pt0,(20.&40.)Pt1,(20.&40.)Pt2,(20.&40.)Pa4,(20.&40.)Pa5,(20.&40.)Pa6,(20.&40.)Pa7,(20.&40.)Pt3,(20.&40.)Pt4,(20.&40.)Pt5,(20.&40.)Pt6,(20.&40.)P,(29.$2.Vm,Vlo,(11.&40.Vsp,))(2:.$2.(1<.VR,)(1=.$2.VR,VHIA,Vh,)$2;.(2<.(2=.Vra,Vsp,Vgp,Vtp,R<.R;.R:.Vs0,Vs1,(2>.&40.VG,)(2>.&40.(6.VdA,))(2>.&40.(6.VdX,))Vpar,R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(2>.&40.$2?.)Vfc,(30.(20.&40.))Vm,(31.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros ST. unfold A_ECP_SW_DERIVE_Y. rt_facts. pose proof MI as MIe. pose proof HH as HHe.
    pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
    pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
    pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [] HH ltac:(clear; lia)) as PRES.
    flat constr:(IMG') 3%nat. flclear IMG'. intros EGOT ELO EHI.
    (* [comment removed for export] *)
    zstep. carve_frame 128%nat ST.
    (* [comment removed for export] *)
    pose proof HH as HH_lx. lazymatch type of HH with ?T => change (id T) in HH end.
    pose proof MC0 as MC0_lx. lazymatch type of MC0 with ?T => change (id T) in MC0 end.
    pose proof SSH as SSH_lx. lazymatch type of SSH with ?T => change (id T) in SSH end.
    pose proof MI as MI_lx. lazymatch type of MI with ?T => change (id T) in MI end.
    (* [comment removed for export] *)
    pose (lxi := lxA_img (arl_AL R) IMG).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0xcb7bc] [] 60%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    lx_carry.
    lx_align32 sp1.
    match goal with Hm : sp1 mod 32 = 0 |- _ => rename Hm into SP1M end.
    assert (SP1 : bv_unsigned sp - 144 <= sp1 <= bv_unsigned sp - 128)
      by (match goal with H1 : 0 <= sp1 + _, H2 : 0 <= - sp1 + _ |- _ => clear - H1 H2 SP1M SPA SPR end; Z.div_mod_to_equations; lia).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR NER; lia).
    try match goal with H : stk _ _ lo (bv_unsigned sp + -128) |- _ => rename H into ST end.
    (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with HHc : HM _ _ _ h LB LF mc |- _ =>
        pose proof (hm_abase asegs R HIA h LB LF mc HHc) as AB;
        pose proof (abase_got _ _ _ AB) as GOT; pose proof (abase_gsb _ _ _ AB) as GSB;
        (flat constr:((hm_auar asegs R HIA h LB LF mc HHc)) 2%nat; intros UGOT UFLAG);
        pose proof (hm_flag_img asegs R HIA h LB LF mc HHc) as FLIMG
      end end.
    rewrite EGOT in GOT. rewrite UARG in UGOT.
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52ef8; 0x9b9c0; 0x9ba64; 0x9c434; 0x9ccc0; 0x9d670; 0x9eb68; 0xa072c; 0xcede4; 0xcb998; 0xcb8d4; 0xcb8e4; 0xcb8f8; 0xcb908; 0xcb924; 0xcb934; 0xcb94c; 0xcb950; 0xcb958; 0xcb964] [] 400%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : presW _ _ _ _ _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    (* [comment removed for export] *)
    repeat match goal with H : context [al_sb AL + Z.shiftr ?f 3] |- _ => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) in H by (clear; lia) end.
    repeat match goal with |- context [al_sb AL + Z.shiftr ?f 3] => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) by (clear; lia) end.
    repeat match goal with E : md_addr _ = _ |- _ => progress rewrite E end.   (* [comment removed for export] *)
    try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
    destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -128) ST ltac:(clear - SP1 SLO NS1 NES; lia)) as [ST1 ST2]. clear ST.
    replace (Z_to_bv 64 339704) with (Z_to_bv 64 (arl_smalloc R 0)) by (rewrite SM0; reflexivity).
    lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
    callrt sp1 (eapply (art_smalloc asegs R HIA 0) with (lo := lo) (sz := 64); rewrite ?(unsigned_lit sp1) by exact SP1R;
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
    2:{ exfalso. flat constr:(FRSH) 3%nat. intros F0 F1 _.
        try (change 18446744073709551615 with (Z.ones 64) in Kb; rewrite Z.land_ones in Kb by (clear; lia)).
        rewrite ?Z.mod_small in Kb by (clear - F0 F1 ALO ACV LOS SLO SPR NER NEEDR; lia). clear - Kb F0 F1 ALO ACV LOS SLO SPR NER NEEDR. lia. }
    clear Kb.
    change (64 * 2 ^ 0) with 64 in *. change (8 * 2 ^ 0) with 8 in FSH. change (Z.to_nat 64) with 64%nat in FRM. change (Z.to_nat 8) with 8%nat in FSH.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
    (* [comment removed for export] *)
    destruct (frame_factsA R HIA CS h1 LB LF m3 FB 64 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (64 / 8) with 8 in SBND, APS. change (64 - 40) with 24 in IND.
    pose proof (art_stk_high asegs R HIA) as STKH.
    (* [comment removed for export] *)
    lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -128) _ |- _ => chunk_split FRx 2%nat FRa SAVE end.
    replace (bv_unsigned sp + -128 + 24) with (bv_unsigned sp + -104) in SAVE by (clear; lia).
    lazymatch goal with STx : stk _ m3 sp1 (bv_unsigned sp + -128) |- _ => release_frame FRa STx (bv_unsigned sp + -104); rename STx into STJ end.
    destruct (stk_split asegs m3 sp1 (sp1 + 24) (bv_unsigned sp + -104) STJ ltac:(clear - SP1; lia)) as [STlo SThi]. clear STJ.
    destruct (stk_carve asegs m3 sp1 (sp1 + 24) 8 STlo ltac:(clear; lia)) as [STlo' [jslot SLOT]].
    replace (sp1 + 24 - Z.of_nat 8) with (sp1 + 16) in STlo', SLOT by (clear; lia). clear STlo. rename STlo' into STlo.
    cb8_to_c8 SLOT (@nil cell).
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs m3 FB [] 64 junkf [] [8; 8; 8; 8; 16; 16]%nat) in FRM; [| reflexivity].
    cbn [mk_CB_cells app] in FRM.
    chunk_split FRM 3%nat FHD FRM1. chunk_split FRM1 1%nat FLNK FRM2. chunk_split FRM2 1%nat EXB FREST.
    lazymatch type of EXB with rw_cells _ _ ?a _ => replace a with (FB + 32) in EXB by (clear; lia) end.
    lazymatch type of EXB with rw_cells _ _ _ [CB 16 ?j] => set (jex := j) in EXB; clearbody jex end.
    clear FLNK FREST.
    cb8_to_c8 FHD (@nil cell).
    cbn [zcells] in FSH.
    (* [comment removed for export] *)
    flat constr:(dy_P_entry) 6%nat. flclear dy_P_entry. intros _ EPa NHP _ DSTP _.
    flat constr:(GRP) 7%nat. intros _ _ _ _ _ GSPq _.
    pose proof (alloc_ceiling_lo (L := arl_L R)) as ACL.
    pose proof GRP as ((_ & GALy & _) & _).
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52ef8; 0x9b9c0; 0x9ba64; 0x9c434; 0x9ccc0; 0x9d670; 0x9eb68; 0xa072c; 0xcede4; 0xcb998; 0xcb8d4; 0xcb8e4; 0xcb8f8; 0xcb908; 0xcb924; 0xcb934; 0xcb94c; 0xcb950; 0xcb958; 0xcb964] [] 400%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : presW _ _ _ _ _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    (* [comment removed for export] *)
    repeat match goal with H : context [al_sb AL + Z.shiftr ?f 3] |- _ => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) in H by (clear; lia) end.
    repeat match goal with |- context [al_sb AL + Z.shiftr ?f 3] => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) by (clear; lia) end.
    repeat match goal with E : md_addr _ = _ |- _ => progress rewrite E end.   (* [comment removed for export] *)
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSHX end.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mq1 end.
    lazymatch goal with HHc : HM _ _ _ h1 _ _ mq1, MIc : mem_inv _ mq1 |- _ =>
      (flat constr:((dy_P_at h1 _ mq1 (presW_presA asegs R HIA h LB LF _ _ _ m mq1 PRES) MIc HHc Ehcs)) 3%nat; intros MPq OPq OLq);
      pose proof (hm_abase asegs R HIA h1 _ _ mq1 HHc) as ABq end.
    pose proof (A_mpi_get_bit_spec AL IMG) as SPQ. unfold mpi_get_bit_stmtA, mpi_query_stmtA, A_MPI_GET_BIT_Q in SPQ.
    callxA_sp sp1
      (eapply SPQ with (CS := CS) (LB := LB) (dX := dP) (v := 0) (lo := lo);
       rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?EPa;
       first [ exact MPq | exact OPq | exact OLq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | reflexivity | eassumption
             | (intros EO; exfalso; exact (NHP EO))
             | (clear; lia)
             | (clear - LOS ALO ACV; lia)
             | (clear - SLO SP1 NER NEEDR; lia)
             | (clear - SP1M; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia])
             | (clear - GSPq SP1; lia)
             | (intros N1; left; assert (NNq : md_own dP <> LNull) by (intros C; pose proof MPq as [(_ & _ & _ & _ & _ & OW) _]; rewrite C in OW; (flat constr:(OW) 2%nat; flclear OW; intros _ N0'); clear - N0' N1; lia);
                (flat constr:((DSTP NNq)) 4%nat; intros _ _ IHI _); clear - IHI ACL ALO LOS; lia)
             | match goal with |- ?g => idtac "GETBIT-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-GETBIT-SIDE:" g end.
    clear MPq OLq OPq ABq.
    (* [comment removed for export] *)
    do 3 zstep. zstep. if_cases KB1.
    { (* [comment removed for export] *)
      apply evtA_done. unfold S1P.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx, true end.
      do 16 eexists. exists (Z_to_bv 64 1), (Z_to_bv 64 1102416563), (Z_to_bv 64 148429), (Z_to_bv 64 833400), [CB 16 jex].
      split; [reflexivity|]. split; [intros C; discriminate C|].
      split; [exact SP1|]. split; [exact SP1M|].
      split; [eassumption|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
      split; [exact F64|]. split; [exact FRSH|].
      split; [exact FHD|]. split; [exact EXB|]. split; [reflexivity|].
      split; [exact FSHX|].
      split; [exact SAVE|]. split; [exact SLOT|]. split; [exact STlo|]. split; [exact SThi|].
      split; [assumption|]. split; [assumption|]. split; [exact PRES| first [exact SSH | assumption]]. }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52ef8; 0x9b9c0; 0x9ba64; 0x9c434; 0x9ccc0; 0x9d670; 0x9eb68; 0xa072c; 0xcede4; 0xcb998; 0xcb8d4; 0xcb8e4; 0xcb8f8; 0xcb908; 0xcb924; 0xcb934; 0xcb94c; 0xcb950; 0xcb958; 0xcb964] [] 400%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : presW _ _ _ _ _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    (* [comment removed for export] *)
    repeat match goal with H : context [al_sb AL + Z.shiftr ?f 3] |- _ => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) in H by (clear; lia) end.
    repeat match goal with |- context [al_sb AL + Z.shiftr ?f 3] => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) by (clear; lia) end.
    repeat match goal with E : md_addr _ = _ |- _ => progress rewrite E end.   (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mq2 end.
    lazymatch goal with HHc : HM _ _ _ h1 _ _ mq2, MIc : mem_inv _ mq2 |- _ =>
      (flat constr:((dy_P_at h1 _ mq2 (presW_presA asegs R HIA h LB LF _ _ _ m mq2 PRES) MIc HHc Ehcs)) 3%nat; intros MPq OPq OLq);
      pose proof (hm_abase asegs R HIA h1 _ _ mq2 HHc) as ABq end.
    pose proof (A_mpi_get_bit_spec AL IMG) as SPQ. unfold mpi_get_bit_stmtA, mpi_query_stmtA, A_MPI_GET_BIT_Q in SPQ.
    callxA_sp sp1
      (eapply SPQ with (CS := CS) (LB := LB) (dX := dP) (v := 1) (lo := lo);
       rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?EPa;
       first [ exact MPq | exact OPq | exact OLq | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | reflexivity | eassumption
             | (intros EO; exfalso; exact (NHP EO))
             | (clear; lia)
             | (clear - LOS ALO ACV; lia)
             | (clear - SLO SP1 NER NEEDR; lia)
             | (clear - SP1M; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia])
             | (clear - GSPq SP1; lia)
             | (intros N1; left; assert (NNq : md_own dP <> LNull) by (intros C; pose proof MPq as [(_ & _ & _ & _ & _ & OW) _]; rewrite C in OW; (flat constr:(OW) 2%nat; flclear OW; intros _ N0'); clear - N0' N1; lia);
                (flat constr:((DSTP NNq)) 4%nat; intros _ _ IHI _); clear - IHI ACL ALO LOS; lia)
             | match goal with |- ?g => idtac "GETBIT-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-GETBIT-SIDE:" g end.
    clear MPq OLq OPq ABq.
    (* [comment removed for export] *)
    zstep. if_cases KB2.
    { (* [comment removed for export] *)
      apply evtA_done. unfold S1P.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx, true end.
      do 16 eexists. exists (Z_to_bv 64 1), (Z_to_bv 64 1102416563), (Z_to_bv 64 148429), (Z_to_bv 64 833400), [CB 16 jex].
      split; [reflexivity|]. split; [intros C; discriminate C|].
      split; [exact SP1|]. split; [exact SP1M|].
      split; [eassumption|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
      split; [exact F64|]. split; [exact FRSH|].
      split; [exact FHD|]. split; [exact EXB|]. split; [reflexivity|].
      split; [exact FSHX|].
      split; [exact SAVE|]. split; [exact SLOT|]. split; [exact STlo|]. split; [exact SThi|].
      split; [assumption|]. split; [assumption|]. split; [exact PRES| first [exact SSH | assumption]]. }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52ef8; 0x9b9c0; 0x9ba64; 0x9c434; 0x9ccc0; 0x9d670; 0x9eb68; 0xa072c; 0xcede4; 0xcb998; 0xcb8d4; 0xcb8e4; 0xcb8f8; 0xcb908; 0xcb924; 0xcb934; 0xcb94c; 0xcb950; 0xcb958; 0xcb964] [] 400%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : presW _ _ _ _ _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    (* [comment removed for export] *)
    repeat match goal with H : context [al_sb AL + Z.shiftr ?f 3] |- _ => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) in H by (clear; lia) end.
    repeat match goal with |- context [al_sb AL + Z.shiftr ?f 3] => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) by (clear; lia) end.
    repeat match goal with E : md_addr _ = _ |- _ => progress rewrite E end.   (* [comment removed for export] *)
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSHU' end.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mq3 end.
    frame_aobj FSHU' (FB + 32) 2%nat as OEX.
    apply (mpi_cells_of_bytes asegs) in EXB.
    lazymatch goal with HHc : HM _ _ _ h1 _ _ mq3 |- _ => pose proof (hm_abase asegs R HIA h1 _ _ mq3 HHc) as ABq end.
    pose proof (A_mpi_init_spec AL IMG) as SPI. unfold mpi_init_stmtA, A_MPI_INIT_ in SPI.
    callxA_sp sp1
      (eapply SPI with (CS := CS) (X := FB + 32) (lo := lo);
       rewrite ?(unsigned_lit sp1) by exact SP1R;
       first [ exact EXB | exact OEX | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | reflexivity | eassumption
             | (clear - F8; Z.div_mod_to_equations; lia)
             | (clear - F0; lia)
             | (clear - SLO SP1 NER NEEDR; lia)
             | (clear - SP1M; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia])
             | (left; clear - F1 ALO LOS SLO SP1 NER NEEDR; lia)
             | match goal with |- ?g => idtac "INIT-PRE-LEFT:" g end ]).
    clear SPI.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-INIT-SIDE:" g end.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mq4 end.
    match goal with H : rw_cells asegs mq4 (FB + 32) (mpi_cells 0 _ 0 ?pd) |- _ => rename H into EXI; set (padE := pd) in EXI end.
    apply evtA_done. unfold S1P.
    exists FB, sp1, h1, mq4, false.
    do 16 eexists. exists (Z_to_bv 64 (FB + 32)), (Z_to_bv 64 1102416563), (Z_to_bv 64 148429), (Z_to_bv 64 833400), (mpi_cells 0 (Z_to_bv 64 1) 0 padE).
    split; [reflexivity|]. split; [intros _; split; [reflexivity| exists padE; reflexivity]|].
    split; [exact SP1|]. split; [exact SP1M|].
    split; [eassumption|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
    split; [exact F64|]. split; [exact FRSH|].
    split; [exact FHD|]. split; [exact EXI|]. split; [reflexivity|].
    split; [exact FSHU'|].
    split; [exact SAVE|]. split; [exact SLOT|]. split; [exact STlo|]. split; [exact SThi|].
    split; [assumption|]. split; [assumption|]. split; [exact PRES| first [exact SSH | assumption]].
    all: match goal with |- ?g => idtac "PRO-LEFT:" g end.
  Qed.
  Definition EPOST (h3 : HST asegs R HIA) (LBa LBb : list blk) (m0 m2x : mem) (WA WB : list ivl) (r : Z)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_derive_y ()) "Lms,$32.(33.P,(20.&40.)(21.(20.&8.))Lm',P,(20.&40.)(21.(20.&8.))(33.(1>.$2.VR,VHIA,)Lh4,(1>.$2.VR,VHIA,)(33.(20.&40.)Lt0,(20.&40.)(33.(20.&40.)Lt1,(20.&40.)(33.(20.&40.)Lt2,(20.&40.)(33.(20.&40.)La1,(20.&40.)(33.(20.&40.)La2,(20.&40.)(33.(20.&40.)La3,(20.&40.)(33.(20.&40.)La4,(20.&40.)(33.(20.&40.)La5,(20.&40.)(33.(20.&40.)La6,(20.&40.)(33.(20.&40.)La7,(20.&40.)(33.(20.&40.)Lt3,(20.&40.)(33.(20.&40.)Lt4,(20.&40.)(33.(20.&40.)Lt5,(20.&40.)(33.(20.&40.)Lt6,(20.&40.)(0.(4.$32.R11.(2<.(2=.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(2>.&40.O1.)R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(34.Vra,)Vfc,(30.(20.&40.))R10.(31.$2.)))(0.(27.$2.R10.)(0.(29.$2.R10.Vlo,(11.&40.Vsp,))(0.(35.$2.VR,VHIA,O8.O7.VLF,(11.&40.Vsp,)(23.VR,)O3.O5.R10.)(0.(35.$2.VR,VHIA,O8.O6.VLF,(11.&40.Vsp,)(23.VR,)O2.O4.R10.)(0.(4.P,$5.Sp(1=.$2.VR,VHIA,R?.)(1=.$2.VR,VHIA,O8.))(0.(4.$5.(36.$2.VR,VHIA,R?.)(36.$2.VR,VHIA,O8.))(0.(4.$5.(24.$2.VR,VHIA,R?.)(24.$2.VR,VHIA,O8.))(0.(4.$5.(37.$2.VR,VHIA,R?.)(37.$2.VR,VHIA,O8.))(0.(4.$5.(38.$2.VR,VHIA,R?.)(38.$2.VR,VHIA,O8.))(0.(4.$5.(39.$2.VR,VHIA,R?.)(39.$2.VR,VHIA,O8.))(0.Pmo,$3:.(3;.(3<.$2.VR,VHIA,R10.R1.)(3<.$2.VR,VHIA,O8.R1.))(28.$2.VR,VHIA,R?.O6.VLF,R10.)))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_derive_y ()) "Ph3,(1>.$2.VR,VHIA,)PLBa,(1?.$?.)PLBb,(1?.$?.)Pm0,P,(20.&40.)(21.(20.&8.))Pm2x,P,(20.&40.)(21.(20.&8.))Pmm,P,(20.&40.)(21.(20.&8.))PWA,(1?.$26.)PWB,(1?.$26.)PFB,$5.Psp1,$5.Pxra,(20.&40.)Pt0,(20.&40.)Pt1,(20.&40.)Pt2,(20.&40.)Pa0,(20.&40.)Pa1,(20.&40.)Pa2,(20.&40.)Pa3,(20.&40.)Pa4,(20.&40.)Pa5,(20.&40.)Pa6,(20.&40.)Pa7,(20.&40.)Pt3,(20.&40.)Pt4,(20.&40.)Pt5,(20.&40.)Pt6,(20.&40.)Ps3v,(20.&40.)Ps4v,(20.&40.)Ps5v,(20.&40.)Ps6v,(20.&40.)Ps8v,(20.&40.)Ps9v,(20.&40.)Pw0,(20.&40.)Pw1,(20.&40.)Pw2,(20.&40.)Pr,$5.P,(28.$2.VR,VHIA,R24.R22.(3=.(3>.$5.$5.)(3?.$5.$5.R1<.+40.)VLF,)R1?.)P,Px,$5.P,(1=.$2.VR,VHIA,Vh,R1.)(1=.$2.VR,VHIA,R27.R2.)P,(4.$5.(36.$2.VR,VHIA,R26.)(36.$2.VR,VHIA,Vh,))P,(4.$5.(24.$2.VR,VHIA,R27.)(24.$2.VR,VHIA,Vh,))P,(0.(13.(40.(11.&40.Vsp,)+90.)R1?.)(13.R1?.(40.(11.&40.Vsp,)+80.)))P,(4.$5.(41.R20.+20.)=)P,(4.$5.(41.R22.+40.)=)P,(42.VR,R2:.VLF,R23.+40.)P,(42.VR,R2:.VLF,R24.+40.)P,(43.(1=.$2.VR,VHIA,Vh,)R25.+40.)P,PB,$5.Pj,$5.P,(44.(3>.$5.$5.)(3?.$5.$5.R2.R1.)VLF,)(45.(13.(7.R29.+40.)R3.)(13.(7.R3.R2.)R29.))P,Pb',$?.P,(44.$?.R1.R2?.)(44.$?.R2.R2?.)P,(46.$2.R2;.R28.(3=.$47.(48.R10.)(3=.$47.(48.R?.)(3=.$47.(48.R>.)(25.$47.)))))P,(46.$2.R2<.(7.(49.R29.+3.)(4:.(1<.VR,)))(3=.$47.(4;.(2>.&8.+?1.))(3=.$47.(4;.(2>.&8.+?1.))(3=.$47.(4;.(2>.&8.+?1.))(3=.$47.(4;.(2>.&8.+?1.))(3=.$47.(4;.(2>.&8.+?8.))(3=.$47.(4;.(2>.&8.+?8.))(3=.$47.(4;.(2>.&8.+?3.))(3=.$47.(4;.(2>.&8.+?3.))(25.$47.))))))))))P,(46.$2.R2=.(7.(11.&40.Vsp,)-68.)(3=.$47.(48.Vs11,)(3=.$47.(48.Vs10,)(3=.$47.(48.Vs9,)(3=.$47.(48.Vs8,)(3=.$47.(48.Vs7,)(3=.$47.(48.Vs6,)(3=.$47.(48.Vs5,)(3=.$47.(48.Vs4,)(3=.$47.(48.Vs3,)(3=.$47.(48.Vs2,)(3=.$47.(48.Vs1,)(3=.$47.(48.Vs0,)(3=.$47.(48.Vra,)(25.$47.)))))))))))))))P,(46.$2.R2>.(7.R2:.+10.)(3=.$47.(48.(2>.&40.R2;.))(25.$47.)))P,(29.$2.R2?.R2;.(7.R2;.+10.))P,(29.$2.R30.(7.R2<.+18.)(7.(11.&40.Vsp,)-68.))P,(29.$2.R31.Vlo,R2=.)P,(27.$2.R32.)P,(35.$2.VR,VHIA,R38.R37.VLF,(11.&40.Vsp,)(23.VR,)R32.R35.R33.)P,(35.$2.VR,VHIA,R39.R37.VLF,(11.&40.Vsp,)(23.VR,)R32.R35.R34.)(2:.$2.(1<.VR,)(1=.$2.VR,VHIA,R3:.)(4<.R3:.R39.R38.R37.R36.R34.R33.R17.)(2<.(2=.R30.(2>.&40.R31.)Vgp,Vtp,R2?.R2>.R2=.Vsp,(2>.&40.R31.)R2<.R2;.R2:.R29.R28.R27.R26.R25.(2>.&40.R32.)R20.R1?.R1>.R1=.(2>.&40.R17.)R1<.R1;.(2>.&40.(7.(49.R32.+3.)(4:.(1<.VR,))))(2>.&40.R32.)R24.R23.R22.R21.)VF,(2>.&40.+<;964.)Vfc,(30.(20.&40.))R35.(31.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until r. intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB AP SUBK FHD FSH SAVE SLOT ST24 SThi STlo MIq PRES PRES2.
    rt_facts.
    pose proof (hcs_ok asegs R HIA h3) as CSOK3.
    pose proof (hm_top asegs R HIA h3 _ _ _ HH3) as HTOP3. rewrite ET3, ES3 in HTOP3.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR NER; lia).
    assert (CFB3 : crange (hcs asegs R HIA h3) FB 64) by (eapply crange_mono; [exact HCS3| exact CFB]).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NEEDR NER TOP HTOP3; lia]).
    assert (SCS3 : crange (hcs asegs R HIA h3) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCS3| exact SCS]).
    assert (SCS03 : crange (hcs asegs R HIA h3) (arl_stklo R) (hstkhi asegs R HIA h - arl_stklo R)) by (eapply crange_mono; [exact HCS3| exact SCS0]).
    destruct (frame_factsA R HIA (hcs asegs R HIA h3) h3 LBb LF mm FB 64 lo HH3 eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (_ & INF & INH3 & IND3 & _ & _ & F8 & FBLO & SBND & APS). change (64 / 8) with 8 in SBND, APS.
    pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'. flat constr:(FRSH') 4%nat. flclear FRSH'. intros F0 F1 F2 F3.
    pose proof (art_stk_high asegs R HIA) as STKH.
    pose proof (hm_wlow asegs R HIA h3 _ _ _ HH3) as WL3.
    (* [comment removed for export] *)
    pose proof HH as HH_lx. lazymatch type of HH with ?T => change (id T) in HH end.
    pose proof MC0 as MC0_lx. lazymatch type of MC0 with ?T => change (id T) in MC0 end.
    pose proof SSH as SSH_lx. lazymatch type of SSH with ?T => change (id T) in SSH end.
    pose proof MI as MI_lx. lazymatch type of MI with ?T => change (id T) in MI end.
    pose (lxi := lxA_img (arl_AL R) IMG).
    assert (SFF : shadow_free R LBa LF (arl_stklo R) (hstkhi asegs R HIA h3) FB 64)
      by (eapply shadow_free_fresh; [exact FRSH | exact (proj2 (proj2 (proj2 PRES))) | clear; lia | clear; lia | exact ALO | exact AP]).
    assert (SFF2 : shadow_free R LBb LF (arl_stklo R) (hstkhi asegs R HIA h3) FB 64)
      by (eapply shadow_free_fresh; [exact FRSH3 | exact (proj2 (proj2 (proj2 PRES2))) | clear; lia | clear; lia | exact ALO | exact AP]).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52ef8; 0x9b9c0; 0x9ba64; 0x9c434; 0x9ccc0; 0x9d670; 0x9eb68; 0xa072c; 0xcede4; 0xcb998; 0xcb8d4; 0xcb8e4; 0xcb8f8; 0xcb908; 0xcb924; 0xcb934; 0xcb94c; 0xcb950; 0xcb958; 0xcb964] [] 400%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : presW _ _ _ _ _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    (* [comment removed for export] *)
    repeat match goal with H : context [al_sb AL + Z.shiftr ?f 3] |- _ => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) in H by (clear; lia) end.
    repeat match goal with |- context [al_sb AL + Z.shiftr ?f 3] => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) by (clear; lia) end.
    repeat match goal with E : md_addr _ = _ |- _ => progress rewrite E end.   (* [comment removed for export] *)
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
    (* [comment removed for export] *)
    match goal with H : HM _ _ _ h3 _ _ me |- _ => rename H into HHe end.
    destruct (hm_fake_free asegs R HIA h3 LBb ((FB, 64) :: LF) me FB 64 HHe ltac:(left; reflexivity))
      as (p & h4 & ROp & [old Hold] & CRp & NCp & NSp & HM4 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4).
    replace (FB + 64 - 8) with (FB + 56) in ROp by (clear; lia).
    pose proof (rw_cells_bound _ _ _ _ Hold) as PB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
    pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp. clear Hold.
    assert (SUB1 : forall b', In b' (LBa ++ fdata LF) -> In b' (LBb ++ fdata ((FB, 64) :: LF))).
    { intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply SUBK; exact Hb| right].
      eapply fdata_incl; [| exact Hb]. intros fb Hfb. right. exact Hfb. }
    assert (SUB2 : forall b', In b' (LBb ++ fdata LF) -> In b' (LBb ++ fdata ((FB, 64) :: LF))) by (intros b' Hb; apply fdata_cons_sub; exact Hb).
    assert (NP5 : bv_unsigned sp + -104 + 104 <= p \/ p + 1 <= bv_unsigned sp + -104).
    { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; clear - SLO LOS NEEDR NER; lia| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
    assert (NP6 : sp1 + 16 + 8 <= p \/ p + 1 <= sp1 + 16).
    { eapply (nc_apart _ _ _ (arl_stklo R) _ p); [exact NCp| apply client_range_stack; clear - SLO LOS SP1 NEEDR NER; lia| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
    assert (WCp1 : wcover R LBa LF (bv_unsigned sp) WA p 1) by (eapply wcover_nc; [exact NCp| exact SUB1| clear - LOS SLO NEEDR NER; lia]).
    assert (WCp2 : wcover R LBb LF (bv_unsigned sp) WB p 1) by (eapply wcover_nc; [exact NCp| exact SUB2| clear - LOS SLO NEEDR NER; lia]).
    clear HHe NCp NSp FHD.
    repeat match goal with H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL) _ |- _ => clear H | H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL + _) _ |- _ => clear H end.
    zstep. zstep.
    fake_free_done p HSp.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52ef8; 0x9b9c0; 0x9ba64; 0x9c434; 0x9ccc0; 0x9d670; 0x9eb68; 0xa072c; 0xcede4; 0xcb998; 0xcb8d4; 0xcb8e4; 0xcb8f8; 0xcb908; 0xcb924; 0xcb934; 0xcb94c; 0xcb950; 0xcb958; 0xcb964] [] 400%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    all: lx_carry.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) =>   (* [comment removed for export] *)
      repeat match goal with
      | H : HM _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : presW _ _ _ _ _ _ _ _ _ _ ?mo |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u32arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      | H : u8arr _ ?mo _ _ |- _ => lazymatch mo with mx => fail | _ => clear H end
      end end.
    (* [comment removed for export] *)
    repeat match goal with H : context [al_sb AL + Z.shiftr ?f 3] |- _ => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) in H by (clear; lia) end.
    repeat match goal with |- context [al_sb AL + Z.shiftr ?f 3] => replace (al_sb AL + Z.shiftr f 3) with (Z.shiftr f 3 + al_sb AL) by (clear; lia) end.
    repeat match goal with E : md_addr _ = _ |- _ => progress rewrite E end.   (* [comment removed for export] *)
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
  Definition DY_POST := ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_derive_y ()) "(4=.$2.VR,VHIA,VMT,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VdX,VG,Vg,$4>.(4?.VN,)(50.VN,Vd,)(51.VN,)Vlo,Vm,Vmo0,)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Lemma dy_exit : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_derive_y ()) "PFBx,$5.Psp1x,$5.Phk,(1>.$2.VR,VHIA,)PLBk,(1?.$?.)Pmk,P,(20.&40.)(21.(20.&8.))PdYk,$52.Pv,$5.Pf,$5.Pr,$5.Pxra,(20.&40.)Pt0,(20.&40.)Pt1,(20.&40.)Pt2,(20.&40.)Pa0,(20.&40.)Pa1,(20.&40.)Pa2,(20.&40.)Pa3,(20.&40.)Pa4,(20.&40.)Pa5,(20.&40.)Pa6,(20.&40.)Pa7,(20.&40.)Pt3,(20.&40.)Pt4,(20.&40.)Pt5,(20.&40.)Pt6,(20.&40.)Ps3v,(20.&40.)Ps4v,(20.&40.)Ps5v,(20.&40.)Ps6v,(20.&40.)Ps8v,(20.&40.)Ps9v,(20.&40.)Pw0x,(20.&40.)Pw1x,(20.&40.)Pw2x,(20.&40.)P,(0.(13.(40.(11.&40.Vsp,)+90.)R21.)(13.R21.(40.(11.&40.Vsp,)+80.)))P,(4.$5.(41.R22.+20.)=)P,(4.$5.(41.R24.+40.)=)P,(42.VR,VLB,VLF,R25.+40.)P,(43.(1=.$2.VR,VHIA,Vh,)R26.+40.)P,(28.$2.VR,VHIA,R25.R24.(3=.(3>.$5.$5.)(3?.$5.$5.R27.+40.)VLF,)R23.)P,Px,$5.P,(1=.$2.VR,VHIA,Vh,R1.)(1=.$2.VR,VHIA,R28.R2.)P,(4.$5.(36.$2.VR,VHIA,R27.)(36.$2.VR,VHIA,Vh,))P,(4.$5.(24.$2.VR,VHIA,R28.)(24.$2.VR,VHIA,Vh,))P,(4.$5.(37.$2.VR,VHIA,R29.)(37.$2.VR,VHIA,Vh,))P,(13.(38.$2.VR,VHIA,R2:.)(7.(38.$2.VR,VHIA,Vh,)R26.))P,(13.(39.$2.VR,VHIA,R2;.)(7.(39.$2.VR,VHIA,Vh,)R26.))P,(13.R28.(4?.VN,))P,(13.R28.(50.VN,Vd,))P,(46.$2.R2<.R30.(3=.$47.(48.R11.)(3=.$47.(48.R10.)(3=.$47.(48.R?.)(25.$47.)))))P,(46.$2.R2=.(7.(49.R31.+3.)(4:.(1<.VR,)))(3=.$47.(4;.(2>.&8.+?1.))(3=.$47.(4;.(2>.&8.+?1.))(3=.$47.(4;.(2>.&8.+?1.))(3=.$47.(4;.(2>.&8.+?1.))(3=.$47.(4;.(2>.&8.+?8.))(3=.$47.(4;.(2>.&8.+?8.))(3=.$47.(4;.(2>.&8.+?3.))(3=.$47.(4;.(2>.&8.+?3.))(25.$47.))))))))))P,(46.$2.R2>.(7.(11.&40.Vsp,)-68.)(3=.$47.(48.Vs11,)(3=.$47.(48.Vs10,)(3=.$47.(48.Vs9,)(3=.$47.(48.Vs8,)(3=.$47.(48.Vs7,)(3=.$47.(48.Vs6,)(3=.$47.(48.Vs5,)(3=.$47.(48.Vs4,)(3=.$47.(48.Vs3,)(3=.$47.(48.Vs2,)(3=.$47.(48.Vs1,)(3=.$47.(48.Vs0,)(3=.$47.(48.Vra,)(25.$47.)))))))))))))))P,(46.$2.R2?.(7.R32.+10.)(3=.$47.(48.(2>.&40.R33.))(25.$47.)))P,(29.$2.R30.R33.(7.R33.+10.))P,(29.$2.R31.(7.R34.+18.)(7.(11.&40.Vsp,)-68.))P,(29.$2.R32.Vlo,R35.)P,(27.$2.R33.)P,(35.$2.VR,VHIA,R36.VLB,VLF,(11.&40.Vsp,)(23.VR,)(3=.(3>.$5.$5.)(3?.$5.$5.(6.VdX,)(7.(6.VdX,)+10.))(3=.(3>.$5.$5.)(3?.$5.$5.$4>.(7.$4>.+8.))(25.(3>.$5.$5.))))Vm,R34.)P,Pb,$?.P,(44.$?.R1.VLB,)(44.$?.R2.R38.)P,Pb,$?.P,(44.$?.R1.R38.)(45.(44.$?.R2.VLB,)(44.$?.R2.(53.R37.)))P,(1.$2.R37.R38.R36.)P,(4.$5.(6.R37.)(6.VdX,))P,(4.(20.&40.)(54.R38.)(54.VdX,))P,(8.(4.$9.(:.R39.)$55.))P,Pb,$?.P,(44.$?.R1.(53.R3;.))(0.(8.(44.$?.R2.VLB,))(42.VR,VLB,VLF,(56.$5.$5.R2.)(57.$5.$5.R2.)))P,(33.(20.&40.)Lc,(20.&40.)(46.$2.R3=.$4>.(3=.$47.(48.R1.)(25.$47.))))P,(0.(15.(58.(59.+2.+1?.))R39.)(13.R39.=))P,(13.(14.R3=.)(51.VN,))(5:.$2.(5;.$2.VR,VHIA,R41.Vmo0,)$5<.(2<.(2=.R3:.(2>.&40.R42.)Vgp,Vtp,R39.R38.R37.Vsp,(2>.&40.R42.)R36.R35.R34.R33.R32.R31.R30.R2?.(2>.&40.R43.)R2:.R29.R28.R27.(2>.&40.R3;.)R26.R25.(2>.&40.(7.(49.R43.+3.)(4:.(1<.VR,))))(2>.&40.R43.)R2>.R2=.R2<.R2;.)VF,(2>.&40.+<;964.)Vfc,(30.(20.&40.))R3?.(31.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until w2x. intros SP1x SP1Mx F64x FRSHx CFB HHk HCSk HTk HSk HFk HVk HFRk HVB HFB FHDk FSHk SAVEk SLOTk ST16k SThik STlok MIk PRESa SUBk COVk MYk EAk PADk NSk FRSk [ck MCk] HR SZk.
    rt_facts. pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    flat constr:(XW) 2%nat. intros XCW XP.
    assert (CRXs : client_range L (LB ++ fdata LF) (bv_unsigned sp) Y 16) by (eapply client_range_of_w; exact XCW).
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk LBk LF mk FBx 64 lo HHk eq_refl (fresh_apart_relist R HIA hk LB LBk LF mk FBx 64 FRSHx HHk) F64x ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & _ & _ & _ & APk & _).
    pose proof (presW_init_at R HIA hk _ _ LBk LF mk (bv_unsigned sp) (arl_stklo R) [] h HHk
                  ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSk HSk ltac:(clear; lia)) as PRES2.
    eapply (aevtA_cut_evtA_KF asegs R HIA hk mo0).
    { eapply epi_walk with (h3 := hk) (LBa := LB) (LBb := LBk) (r := r);
        first [ exact HHk | exact HCSk | exact PRESa | exact PRES2 | exact FRSHx | exact CFB | exact APk | exact SUBk | eassumption | reflexivity
              | exact (fresh_apart_relist R HIA hk LB LBk LF mk FBx 64 FRSHx HHk)
              | match goal with |- ?g => idtac "EPI-PRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    destruct EP as (m9 & h4 & z0' & z1' & z2' & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3' & z4' & z5' & z6'
                    & -> & MI9 & ST9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    apply aevtA_done. intros mo9 [HK9 MF9].
    unfold DY_POST, ecp_mul_mod_postA.
    do 14 eexists. exists m9, mo9, h4, LBk, dYk, r, ck.
    split; [reflexivity|]. split; [exact MI9|]. split; [exact ST9|]. split; [exact MF9|].
    split; [unfold mpd_keep; rewrite XNULL; pose proof (presW_presA asegs R HIA hk _ LF _ _ _ _ _ PRES9) as HPF; rewrite HSk in HPF; exact HPF|].
    split; [rewrite E4top; exact HTk|]. split; [rewrite E4stk; exact HSk|]. split; [rewrite E4flag; exact HFk|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; exact (HCSk x Hx)|].
    split; [rewrite E4vol; clear - HVk HVB; lia|].
    split; [rewrite E4fr; clear - HFRk HFB; lia|].
    split; [exact HH4|].
    pose proof (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA hk _ LF _ _ _ _ _ PRES29)) as PX29.
    split.
    { flat constr:(MYk) 2%nat. intros FLt3 _. flat constr:(FLt3) 6%nat. flclear FLt3. intros CXf _ _ _ _ OWNf.
      eapply (mpd_at_heap_presx asegs L) with (LBp := LBk ++ fdata LF) (SP := bv_unsigned sp) (XI := []);
        [exact MYk| exact PX29| exact MIk| exact MI9| | | exact I| intros _; exact I|].
      - rewrite EAk. eapply client_range_temp; [exact CRXs| clear; lia|].
        intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; exact (SUBk _ Hb)| right; exact Hb].
      - intros EO. rewrite EO in OWNf. flat constr:(OWNf) 3%nat. flclear OWNf. intros N1 XIN _. eapply client_range_block; [apply in_app_iff; left; exact XIN| clear; lia| clear - N1; lia].
      - intros b' Hb. unfold mpd_blk in Hb. destruct (md_own dYk) eqn:EO; try (destruct Hb; fail). destruct Hb as [<-|[]]. flat constr:(OWNf) 3%nat. flclear OWNf. intros _ XIN _. exact XIN. }
    split.
    { unfold mpd_out. split; [exact EAk|]. split; [exact NSk|]. split; [exact COVk|]. split; [intros b Hb _; exact (SUBk b Hb)|].
      intros b Hb. unfold mpd_blk in Hb. rewrite XNULL in Hb. destruct Hb. }
    split.
    { intros b Hb. right. unfold mpd_keep. rewrite XNULL. exact (proj2 (FRSk b Hb)). }
    split.
    { flat constr:(GRP) 9%nat. intros GAT GH1 GPS GIMG GCR GSP GMC GOB GUW. flat constr:(OSEP) 3%nat. intros OS1 _ _.
      assert (CRS : client_range L (LB ++ fdata LF) (bv_unsigned sp) G 192).
      { intros a Ha. destruct (GCR a Ha) as [S|[D|B]]; [| right; left; exact D| right; right; exact B].
        destruct GSP as [K|K]; [exfalso; clear - S Ha K; lia| left; clear - Ha K; lia]. }
      pose proof (ecp_group_at_LB_any asegs MT m LB (LB ++ fdata LF) G g GAT GH1) as GAT0.
      eapply (ecp_group_at_presx asegs L MT m m9 _ LBk (bv_unsigned sp) [(Y, Y + 16); (MC, MC + 8)] G g GAT0);
        [exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA hk _ LF _ _ _ _ _ PRES9))| exact MI| exact MI9| exact CRS| |].
      - cbn [disjoint_from fst snd]. split; [clear - OS1; lia|]. split; [clear - GMC; lia| exact I].
      - intros e He EO. exfalso. exact (grp_static_own asegs MT m LB G g e GAT GH1 He EO). }
    split.
    { flat constr:(MCOK) 4%nat. intros MC1 MC2 MC3 _.
      eapply (heap_presx_rw_cells asegs L); [exact PX29| exact MCk| | exact I].
      cbn [cells_size csize Nat.add]. intros x Hx. right. left. split; [clear - Hx MC1 MC2; lia| apply MC3; exact Hx]. }
    split; [| exact SZk].
    split; [exact HR|]. unfold binop_keep. split; [exact EAk|]. split; [exact PADk|].
    split; [intros b Hb; right; exact (proj1 (FRSk b Hb))|].
    flat constr:(MX0) 2%nat. intros FLt4 _. flat constr:(FLt4) 6%nat. flclear FLt4. intros _ _ _ _ _ OW0. rewrite XNULL in OW0. flat constr:(OW0) 2%nat. flclear OW0. intros _ N0'.
    flat constr:(MYk) 2%nat. intros FLt5 _. flat constr:(FLt5) 6%nat. flclear FLt5. intros _ _ _ _ _ OWk. destruct (md_own dYk); [(flat constr:(OWk) 2%nat; flclear OWk; intros _ K); clear - K N0'; lia| (flat constr:(OWk) 2%nat; flclear OWk; intros K _); clear - K N0'; lia| exfalso; exact (NSk eq_refl)].
    all: match goal with |- ?g => idtac "EXIT-LEFT:" g end.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section J.
  Variables (FB sp1 : Z) (h1 : HST asegs R HIA) (m1 : mem) (padE w0 w1 w2 : word) (j0 : list byte).
  Local Notation LF' := ((FB, 64) :: LF).
  Local Notation E := (FB + 32).
  Local Notation SPv := (sp1 + 24).
  Local Notation XO := [(Y, Y + 16); (E, E + 16); (MC, MC + 8)].
  Local Notation FRAME := [CB 16 j0; C8 (Z_to_bv 64 FB)].
  Local Notation dE0 := (mkMPD E 1 0 0 [] padE LNull).
  Hypothesis SP1 : bv_unsigned sp - 144 <= sp1 <= bv_unsigned sp - 128.
  Hypothesis SP1M : sp1 mod 32 = 0.
  Hypothesis HH1 : HM asegs R HIA h1 LB LF' m1.
  Hypothesis Ehcs : hcs asegs R HIA h1 = CS.
  Hypothesis Ehtop : htop asegs R HIA h1 = htop asegs R HIA h.
  Hypothesis Estk : hstkhi asegs R HIA h1 = hstkhi asegs R HIA h.
  Hypothesis Eflag : hflag asegs R HIA h1 = hflag asegs R HIA h.
  Hypothesis Evol : havol asegs R HIA h1 = havol asegs R HIA h.
  Hypothesis Efr : hfr asegs R HIA h1 = hfr asegs R HIA h.
  Hypothesis F64 : FB mod 64 = 0.
  Hypothesis FRSH : fresh_apart R LB LF FB 64.
  Hypothesis FHD : rw_cells asegs m1 FB [C8 w0; C8 w1; C8 w2].
  Hypothesis EXI : rw_cells asegs m1 E (mpi_cells 0 (Z_to_bv 64 1) 0 padE).
  Hypothesis FSH : rw_cells asegs m1 (Z.shiftr FB 3 + al_sb AL) FSHU.
  Hypothesis SAVE : rw_cells asegs m1 (bv_unsigned sp + -104) SAVEL.
  Hypothesis FRM : rw_cells asegs m1 sp1 FRAME.
  Hypothesis SThi : stk asegs m1 SPv (bv_unsigned sp + -104).
  Hypothesis STlo : stk asegs m1 lo sp1.
  Hypothesis MI1 : mem_inv asegs m1.
  Hypothesis PRES0 : presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [] m m1.
  Hypothesis SSH1 : sshad asegs AL m1 slo (bv_unsigned sp).

  Lemma dy_base : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_derive_y ()) "(0.(13.=Vlo,)(0.(13.(23.VR,)Vlo,)(0.(13.(5=.(=.VR,))(23.VR,))(0.(13.Vlo,(40.(40.Vsp1,+540.)(5>.VR,)))(0.(13.=(5>.VR,))(0.(13.=Vsp1,)(0.(13.(7.(7.Vsp1,+18.)+10.)(40.(11.&40.Vsp,)+58.))(0.(15.(11.&40.Vsp,)(59.+2.+40.))(0.(13.(7.$4>.+8.)Vlo,)(0.(15.=VFB,)(0.(13.(7.VFB,+40.)(5=.(=.VR,)))(0.(4.$5.(41.VFB,+8.)=)(0.(45.(13.(7.(6.VdX,)+10.)Vlo,)(13.(11.&40.Vsp,)(6.VdX,)))(0.(45.(13.(7.VFB,+40.)(6.VdX,))(13.(7.(6.VdX,)+10.)VFB,))(0.(15.=(6.VdX,))(0.(13.(7.(6.VdX,)+10.)(59.+2.+40.))(45.(13.(7.VFB,+40.)VG,)(13.(7.VG,+<0.)VFB,))))))))))))))))))")
(* [comment removed for export] *).
  Proof.
    rt_facts. pose proof (art_data_lo asegs R HIA) as DLO. flat constr:(MCOK) 3%nat. intros MC1 MC2 _.
    flat constr:(FRSH) 4%nat. intros F0 F1 F2 F3. flat constr:(XW) 2%nat. intros XCW XP.
    flat constr:(MX0) 2%nat. intros FLt6 _. flat constr:(FLt6) 4%nat. flclear FLt6. intros CX _ X0 _. pose proof (rw_cells_bound _ _ _ _ CX) as XB. unfold mpi_cells in XB. cbn [cells_size csize Nat.add] in XB.
    pose proof (client_wrange_where_A asegs R HIA h LB LF m LB (bv_unsigned sp) Y 16 lo HH ltac:(intros b' Hb; exact Hb) XCW ltac:(clear; lia) LOS ltac:(clear - SLO NEEDR NER; lia)) as XS.
    pose proof (frame_apart_obj R HIA LB LF (bv_unsigned sp) _ Y 16 FB 64 FRSH XCW ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - LOS SLO NEEDR NER; lia)) as APY.
    flat constr:(GRP) 6%nat. intros _ _ _ _ GCR _.
    pose proof (fresh_apart_client R LB LF lo G 192 FB 64 FRSH GCR ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as APG.
    repeat split; try assumption;
      first [ clear - LOS ALO ACV; lia | clear - SLO SP1 NER NEEDR; lia | clear - NER NEEDR; lia | clear - SLO SP1 NER NEEDR LOS ALO ACV; lia | clear - SP1; lia | clear - SPR; lia
            | clear - MC2 DLO ALO LOS; lia | clear - F64; Z.div_mod_to_equations; lia | clear - XB; lia | clear - APG; lia | idtac ].
    all: match goal with |- ?g => idtac "BASE-LEFT:" g end.
  Qed.

  Lemma dy_ec : ECA R HIA h1 LB LF' m1 SPv lo 24 FRAME XO MC.
  Proof.
    flat constr:(dy_base) 10%nat. flclear dy_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO _.
    constructor; try assumption; try reflexivity.
    - clear; lia.
    - clear - LOSP NE0; lia.
    - rewrite Ehtop. clear - SPV TOP. lia.
    - intros a Ha. cbn [outside fst snd] in Ha. clear - Ha. lia.
  Qed.
  Local Notation HP01 := (presW_presA asegs R HIA h LB LF _ _ _ m m1 PRES0).

  Lemma dy_lfsub : forall b, In b (LB ++ fdata LF) -> In b (LB ++ fdata LF').
  Proof. intros b Hb. apply fdata_cons_sub. exact Hb. Qed.

  Lemma dy_topcs : forall x, CS x -> x < hstkhi asegs R HIA h.
  Proof. intros x Hx. eapply hcs_below_top. exact Hx. Qed.

  Lemma dy_grp : ecp_grp_preA asegs R HIA MT h1 LB LF' m1 G g MC lo SPv (d + 1).
  Proof.
    flat constr:(dy_base) 10%nat. flclear dy_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO _. pose proof (hcs_ok asegs R HIA h) as CSOK.
    flat constr:(GRP) 9%nat. intros GAT GH1 GPS GIMG GCR GSP GMC GOB GUW.
    assert (CRS : client_range L (LB ++ fdata LF) (bv_unsigned sp) G 192).
    { intros a Ha. destruct (GCR a Ha) as [S|[D|B]]; [| right; left; exact D| right; right; exact B].
      destruct GSP as [K|K]; [exfalso; clear - S Ha K; lia| left; clear - Ha K; lia]. }
    unfold ecp_grp_preA. split.
    { pose proof (ecp_group_at_LB_any asegs MT m LB (LB ++ fdata LF) G g GAT GH1) as GAT0.
      eapply (ecp_group_at_presx asegs L MT m m1 _ LB (bv_unsigned sp) [] G g GAT0); [exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP01)| exact MI| exact MI1| exact CRS| exact I|].
      intros e He EO. exfalso. exact (grp_static_own asegs MT m LB G g e GAT GH1 He EO). }
    split; [exact GH1|]. split; [exact GPS|]. split; [exact GIMG|].
    split; [intros a Ha; destruct (GCR a Ha) as [S|[D|(b & Hb & Hr)]]; [left; exact S| right; left; exact D| right; right; exists b; split; [exact (dy_lfsub b Hb)| exact Hr]]|].
    split; [clear - GSP SPV; lia|]. split; [exact GMC|].
    split; [| eapply uw_obj_mono_d; [exact GUW| clear; lia]].
    rewrite Ehcs. eapply (presA_aobj asegs R); [exact CSOK| exact HP01| exact GOB| exact CRS| clear - LOS' LOSP SPV NE0; lia| exact dy_topcs].
  Qed.

  Lemma dy_dxg : disjoint_from XO G 192.
  Proof.
    flat constr:(dy_base) 17%nat. flclear dy_base. intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ APG.
    flat constr:(OSEP) 3%nat. intros OS1 _ _. flat constr:(GRP) 8%nat. intros _ _ _ _ _ _ GMC _.
    cbn [disjoint_from fst snd]. split; [clear - OS1; lia|]. split; [clear - APG; lia|]. split; [clear - GMC; lia| exact I].
  Qed.

  Lemma dy_slotY : eslot R HIA h1 LB LF' SPv lo XO MC Y.
  Proof.
    flat constr:(dy_base) 17%nat. flclear dy_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 F8 XS APY Y0 Y16 APG.
    flat constr:(XW) 2%nat. intros XCW XP. flat constr:(OSEP) 3%nat. intros _ _ OS3. unfold eslot.
    split; [rewrite Ehtop; eapply client_wrange_sp_mono; [| eapply client_wrange_mono; [exact XCW| exact dy_lfsub]]; clear - SPV; lia|].
    split; [clear - XS SPV; lia|].
    split; [intros x Hx; cbn [outside fst snd] in *; split; [exact (proj1 Hx)| exact I]| exact OS3].
  Qed.

  Lemma dy_slotE : eslot R HIA h1 LB LF' SPv lo XO MC E.
  Proof.
    flat constr:(dy_base) 17%nat. flclear dy_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 F8 XS APY Y0 Y16 APG.
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 64 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (_ & _ & F2 & F3) & _ & FBLO & SBND & APS). change (64 - 40) with 24 in IND.
    flat constr:(MCOK) 3%nat. intros MC1 MC2 _. unfold eslot.
    split; [eapply client_wrange_block; [exact IND| clear; lia| clear; lia]|].
    split; [left; clear - FBLO; lia|].
    split; [intros x Hx; cbn [outside fst snd] in *; split; [exact (proj1 (proj2 Hx))| exact I]| clear - F2 MC1 MC2; lia].
  Qed.

  Lemma dy_tmpY : ejtmp R HIA LB LF' h1 LB m1 Y dX.
  Proof.
    flat constr:(dy_base) 17%nat. flclear dy_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 F8 XS APY Y0 Y16 APG. pose proof (hcs_ok asegs R HIA h) as CSOK.
    flat constr:(XW) 2%nat. intros XCW XP.
    assert (CRXs : client_range L (LB ++ fdata LF) (bv_unsigned sp) Y 16) by (eapply client_range_of_w; exact XCW).
    unfold ejtmp.
    split.
    { eapply (mpd_at_heap_presx asegs L); [exact MX0| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP01)| exact MI| exact MI1| exact CRXs| intros EO; rewrite XNULL in EO; discriminate EO| exact I| intros _; exact I|].
      intros b Hb. unfold mpd_blk in Hb. rewrite XNULL in Hb. destruct Hb. }
    split; [reflexivity|]. split; [rewrite XNULL; discriminate|].
    split; [intros b Hb; unfold mpd_blk in Hb; rewrite XNULL in Hb; destruct Hb|].
    rewrite Ehcs. eapply (presA_aobj asegs R); [exact CSOK| exact HP01| exact (proj1 OXA)| exact CRXs| clear - LOS' LOSP SPV NE0; lia| exact dy_topcs].
  Qed.

  Lemma dy_tmpE : ejtmp R HIA LB LF' h1 LB m1 E dE0.
  Proof.
    flat constr:(dy_base) 17%nat. flclear dy_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 F8 XS APY Y0 Y16 APG.
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 64 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS) as (CFB & _).
    pose proof (hcs_ok asegs R HIA h) as CSOK.
    unfold ejtmp. cbn [md_addr md_own mpd_blk].
    split.
    { unfold mpd_at, mpi_at. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [| left; reflexivity]. split; [exact EXI|]. split; [clear - F8; Z.div_mod_to_equations; lia|]. split; [clear - F0; lia|]. split; [reflexivity|].
      split; [unfold MPI_MAX_LIMBS; clear; lia| split; reflexivity]. }
    split; [reflexivity|]. split; [discriminate|]. split; [intros b []|].
    rewrite Ehcs. frame_aobj FSH E 2%nat as OEX. exact OEX.
  Qed.
  (* [comment removed for export] *)
  Lemma dy_extX : ej_ext R HIA h1 LB LF' m1 SPv lo XO Y dA.
  Proof.
    flat constr:(dy_base) 17%nat. flclear dy_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 F8 XS APY Y0 Y16 APG. pose proof (hcs_ok asegs R HIA h) as CSOK.
    flat constr:(EXTA) 9%nat. intros ME SEPs FLt7 CR CRL MCs (AOs & AOl) IM UWa. flat constr:(FLt7) 5%nat. flclear FLt7. intros OS1 OS2 OS3 OS4 OS5.
    flat constr:(ME) 2%nat. intros FLt8 _. flat constr:(FLt8) 6%nat. flclear FLt8. intros _ _ E0 _ _ EOW.
    assert (CRS : client_range L (LB ++ fdata LF) (bv_unsigned sp) (md_addr dA) 16).
    { intros a Ha. destruct (CR a Ha) as [S|[D|B]]; [| right; left; exact D| right; right; exact B].
      destruct OS4 as [K|K]; [exfalso; clear - S Ha K; lia| left; clear - Ha K; lia]. }
    assert (CRLS : md_own dA = LHeap -> client_range L (LB ++ fdata LF) (bv_unsigned sp) (md_p dA) (4 * md_n dA)).
    { intros EO a Ha. destruct (CRL EO a Ha) as [S|[D|B]]; [| right; left; exact D| right; right; exact B].
      destruct (OS5 ltac:(rewrite EO; discriminate)) as [K|K]; [exfalso; clear - S Ha K; lia| left; clear - Ha K; lia]. }
    assert (N1 : md_own dA = LHeap -> 1 <= md_n dA /\ In (md_p dA, 4 * md_n dA) LB) by (intros EO; rewrite EO in EOW; (flat constr:(EOW) 3%nat; flclear EOW; intros K1 K2 _); exact (conj K1 K2)).
    unfold ej_ext.
    split.
    { eapply (mpd_at_heap_presx asegs L); [exact ME| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP01)| exact MI| exact MI1| exact CRS| exact CRLS| exact I| intros _; exact I|].
      intros b Hb. flat constr:((mpd_blk_heapE _ _ Hb)) 2%nat. intros EO ->. exact (proj2 (N1 EO)). }
    split; [intros a Ha; destruct (CR a Ha) as [S|[D|(b & Hb & Hr)]]; [left; exact S| right; left; exact D| right; right; exists b; split; [exact (dy_lfsub b Hb)| exact Hr]]|].
    split; [clear - OS4 SPV; lia|].
    split; [intros NN; destruct (OS5 NN) as [K|K]; [left; exact K| right; clear - K SPV; lia]|].
    split.
    { pose proof (fresh_apart_client R LB LF lo (md_addr dA) 16 FB 64 FRSH CR ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS'; lia)) as K.
      cbn [disjoint_from fst snd]. split; [clear - SEPs; lia|]. split; [clear - K; lia|]. split; [clear - MCs; lia| exact I]. }
    split.
    { intros EO. flat constr:((N1 EO)) 2%nat. intros N1' IN.
      pose proof (fresh_apart_client R LB LF lo (md_p dA) (4 * md_n dA) FB 64 FRSH (CRL EO) ltac:(clear - N1'; lia) ltac:(clear; lia) ltac:(clear - ALO LOS'; lia)) as K.
      flat constr:((hm_apart asegs R HIA h LB LF m HH)) 2%nat. intros HF _. rewrite Forall_forall in HF.
      destruct (HF _ ltac:(apply in_app_iff; left; exact IN)) as (_ & _ & _ & BI). cbn [fst snd] in BI.
      flat constr:(MCOK) 3%nat. intros MC1 MC2 _. flat constr:(DIMG) 2%nat. intros DI1 DI2.
      cbn [disjoint_from fst snd]. split; [destruct (OS1 ltac:(rewrite EO; discriminate)) as [K1|K1]; clear - K1; lia|]. split; [clear - K; lia|]. split; [clear - BI MC1 MC2 DI1 DI2; lia| exact I]. }
    split; [exact SEPs|]. split; [exact OS1|].
    split; [| exact IM].
    split.
    - rewrite Ehcs. eapply (presA_aobj asegs R); [exact CSOK| exact HP01| exact AOs| exact CRS| clear - LOS' LOSP SPV NE0; lia| exact dy_topcs].
    - intros ES. eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HH1| exact (IM ES)].
    all: match goal with |- ?g => idtac "EXTX-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  Lemma dy_extP : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_derive_y ()) "PA,$5.Pcs,(1?.$47.)P,(45.(13.(7.R2.+10.)VG,)(13.(7.VG,+<0.)R2.))P,(46.$2.Vm1,R3.R2.)P,(4.$5.(5?.(60.R3.))+10.)(61.VR,VHIA,Vh1,VLB,(3=.(3>.$5.$5.)(3?.$5.$5.VFB,+40.)VLF,)Vm1,(7.Vsp1,+18.)Vlo,(3=.(3>.$5.$5.)(3?.$5.$5.(6.VdX,)(7.(6.VdX,)+10.))(3=.(3>.$5.$5.)(3?.$5.$5.(7.VFB,+20.)(7.(7.VFB,+20.)+10.))(3=.(3>.$5.$5.)(3?.$5.$5.$4>.(7.$4>.+8.))(25.(3>.$5.$5.)))))R5.(3.Vg,))")
(* [comment removed for export] *).
  Proof.
    intros A cs AG CA CSZ. flat constr:(dy_P_entry) 3%nat. flclear dy_P_entry. intros _ EPa _.
    eapply (ej_grp_ext R HIA IMG h1 LB LF' m1 SPv lo 24 FRAME XO MC dy_ec MT G g (d + 1) A dP 8 cs dy_grp dy_dxg);
      [unfold grp_mpds; cbn; left; reflexivity| exact EPa| clear; lia| clear; lia| left; (flat constr:(GRP) 4%nat; intros _ _ GPS _); exact GPS| exact AG| exact CA| exact CSZ].
  Qed.

  Lemma dy_uw0 : uwc asegs m1 (arl_stklo R) (hstkhi asegs R HIA h1) (bv_unsigned sp) SPv (d + 1).
  Proof.
    flat constr:(dy_base) 10%nat. flclear dy_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO _.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    assert (UW1 : uwc asegs m1 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
    { eapply (uwc_presA R); [exact HP01| exact UW| clear; lia| intros a Ha; exact I| clear - LOS' LOSP SPV NE0 LO0; lia| apply hstkhi_le64; clear - LOS' LOSP SPV NE0 SP64 LO0; lia]. }
    rewrite Estk.
    pose proof SAVE as SV. chunk_split SV 11%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
    replace (bv_unsigned sp + -104 + 88) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
    eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UW1| clear - SPV; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0].
  Qed.

  Lemma dy_xouw : 28 <= d + 1 \/ forall a, SPv <= a < hstkhi asegs R HIA h1 -> outside XO a.
  Proof.
    flat constr:(dy_base) 12%nat. flclear dy_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 _.
    destruct UWX as [[U1 _]|U28]; [right| left; clear - U28; lia].
    intros a Ha. cbn [outside fst snd]. split; [clear - Ha U1 LOS' LOSP NE0; lia|]. split; [clear - Ha F1 ALO LOS' LOSP NE0; lia|]. split; [clear - Ha MCLO LOSP NE0; lia| exact I].
  Qed.

  Lemma dy_ssh : sshad asegs AL m1 slo SPv.
  Proof.
    flat constr:(dy_base) 10%nat. flclear dy_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO _.
    exact (proj1 (sshad_split asegs AL m1 slo SPv (bv_unsigned sp) SSH1 ltac:(clear - SLO3 LOSP NE0 SPV; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia))).
  Qed.

  Lemma dy_mc1 : rw_cells asegs m1 MC [C8 cnt].
  Proof.
    flat constr:(MCOK) 4%nat. intros MC1 MC2 MC3 _.
    eapply (presA_rw_cells asegs R); [exact HP01| exact MC0| | exact I].
    cbn [cells_size csize Nat.add]. intros x Hx. right. left. split; [clear - Hx MC1 MC2; lia| apply MC3; exact Hx].
  Qed.
  Local Notation EPIJ := (EPI R HIA h1 LB LF' m1 SPv lo 24 FRAME XO MC (d + 1)).
  Local Notation EJJ := (EJ R HIA h1 LB LF' m1 SPv lo 24 FRAME XO MC).

  Lemma dy_spe : sp1 + 24 - 24 = sp1.
  Proof. clear. lia. Qed.

  Lemma dy_start : EPIJ 0 0 h1 LB m1 Y dX E dE0.
  Proof.
    flat constr:(dy_base) 17%nat. flclear dy_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 F8 XS APY Y0 Y16 APG.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    unfold EPI. split.
    { eapply (ej_start R HIA h1 LB LF' m1 SPv lo 24 FRAME XO MC dy_ec m1 cnt (munch_refl _ _) (wmono_refl _ _) HH1 MI1); [rewrite dy_spe; exact STlo| rewrite dy_spe; exact FRM| exact dy_mc1]. }
    split.
    { unfold epair. split; [exact dy_tmpY|]. split; [exact dy_tmpE|]. split; [intros O1; rewrite XNULL in O1; discriminate O1| intros b Hb; left; exact Hb]. }
    split; [exact dy_slotY|]. split; [exact dy_slotE|]. split; [clear - APY; lia|].
    split; [eapply uw_obj_mono_d; [exact UWX| clear; lia]|].
    left. split; [clear - F1 ALO; lia| clear - D0; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma dy_k_d0 : 0 <= d + 1.
  Proof. pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0. clear - D0. lia. Qed.
  Lemma dy_k_sp64 : SPv < 2^64.
  Proof. flat constr:(dy_base) 9%nat. flclear dy_base. intros _ _ _ _ _ _ SPV SP64 _. clear - SPV SP64. lia. Qed.
  Lemma dy_k_spa : (SPv - 24) mod 16 = 0.
  Proof. rewrite dy_spe. clear - SP1M. Z.div_mod_to_equations. lia. Qed.
  Lemma dy_k_slok : lo <= SPv - 24 - 1344 - arl_need_ecp R.
  Proof. flat constr:(dy_base) 5%nat. flclear dy_base. intros _ _ _ LOSP _. rewrite dy_spe. exact LOSP. Qed.

  Ltac kit_side :=
    first [ exact dy_ec | exact TPV | exact dy_k_d0 | exact dy_k_sp64 | exact dy_k_spa | exact dy_k_slok | exact dy_uw0 | exact dy_xouw | exact dy_ssh
          | exact SLO1 | exact SLO3 | exact dy_grp | exact dy_dxg | exact IMG | (clear; lia) ].

  (* [comment removed for export] *)
  Lemma dy_frame_k : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_derive_y ()) "Pv,$5.Pf,$5.Phk,(1>.$2.VR,VHIA,)PLBk,(1?.$?.)Pmk,P,(20.&40.)(21.(20.&8.))P,(62.VR,VHIA,Vh1,VLB,(3=.(3>.$5.$5.)(3?.$5.$5.VFB,+40.)VLF,)Vm1,(7.Vsp1,+18.)Vlo,+18.(3=.$47.(63.#10.Vj0,)(3=.$47.(48.(2>.&40.VFB,))(25.$47.)))(3=.(3>.$5.$5.)(3?.$5.$5.(6.VdX,)(7.(6.VdX,)+10.))(3=.(3>.$5.$5.)(3?.$5.$5.(7.VFB,+20.)(7.(7.VFB,+20.)+10.))(3=.(3>.$5.$5.)(3?.$5.$5.$4>.(7.$4>.+8.))(25.(3>.$5.$5.)))))$4>.R5.R4.R3.R2.R1.)(0.(46.$2.R2.VFB,(3=.$47.(48.Vw0,)(3=.$47.(48.Vw1,)(3=.$47.(48.Vw2,)(25.$47.)))))(0.(46.$2.R2.(7.(49.VFB,+3.)(4:.(1<.VR,)))(3=.$47.(4;.(2>.&8.+?1.))(3=.$47.(4;.(2>.&8.+?1.))(3=.$47.(4;.(2>.&8.+?1.))(3=.$47.(4;.(2>.&8.+?1.))(3=.$47.(4;.(2>.&8.=))(3=.$47.(4;.(2>.&8.=))(3=.$47.(4;.(2>.&8.+?3.))(3=.$47.(4;.(2>.&8.+?3.))(25.$47.))))))))))(0.(46.$2.R2.(7.(11.&40.Vsp,)-68.)(3=.$47.(48.Vs11,)(3=.$47.(48.Vs10,)(3=.$47.(48.Vs9,)(3=.$47.(48.Vs8,)(3=.$47.(48.Vs7,)(3=.$47.(48.Vs6,)(3=.$47.(48.Vs5,)(3=.$47.(48.Vs4,)(3=.$47.(48.Vs3,)(3=.$47.(48.Vs2,)(3=.$47.(48.Vs1,)(3=.$47.(48.Vs0,)(3=.$47.(48.Vra,)(25.$47.)))))))))))))))(0.(29.$2.R2.(7.Vsp1,+18.)(7.(11.&40.Vsp,)-68.))(0.(35.$2.VR,VHIA,R4.VLB,VLF,(11.&40.Vsp,)(23.VR,)(3=.(3>.$5.$5.)(3?.$5.$5.(6.VdX,)(7.(6.VdX,)+10.))(3=.(3>.$5.$5.)(3?.$5.$5.$4>.(7.$4>.+8.))(25.(3>.$5.$5.))))Vm,R2.)(0.Px,$5.P,(1=.$2.VR,VHIA,Vh,R1.)(1=.$2.VR,VHIA,R6.R2.)(4.$5.(24.$2.VR,VHIA,R4.)(24.$2.VR,VHIA,Vh,))))))))")
(* [comment removed for export] *).
  Proof.
    flat constr:(dy_base) 17%nat. flclear dy_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 F8 XS APY Y0 Y16 APG.
    intros v f hk LBk mk J. pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 64 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (_ & _ & F2 & F3) & _ & FBLO & SBND & APS).
    pose proof (hcs_ok asegs R HIA h) as CSOK. flat constr:(MCOK) 3%nat. intros MC1 MC2 _.
    assert (DJ : forall A k, (A + k <= Y \/ Y + 16 <= A) -> (A + k <= E \/ E + 16 <= A) -> A + k <= lo \/ lo <= A -> MC + 8 <= A \/ A + k <= MC -> disjoint_from XO A k).
    { intros A k H1 H2 _ H4. cbn [disjoint_from fst snd]. split; [clear - H1; lia|]. split; [clear - H2; lia|]. split; [clear - H4; lia| exact I]. }
    split.
    { eapply (presA_rw_cells asegs R); [exact PXk| exact FHD| |].
      - cbn [cells_size csize Nat.add]. eapply client_range_block; [exact INH| clear; lia| clear; lia].
      - cbn [cells_size csize Nat.add]. apply DJ; [clear - APY; lia| clear; lia| left; clear - FBLO; lia| clear - F2 MC1 MC2; lia]. }
    split.
    { rewrite <- Ehcs in CSOK.
      eapply (presA_shadow_cells_sh asegs R (hcs asegs R HIA h1) LB LF' SPv (arl_stklo R) (hstkhi asegs R HIA h1) XO m1 mk FB _ CSOK); [| exact F8| clear - F0; lia| exact PXk| exact FSH|].
      - cbn [cells_size csize Nat.add]. rewrite Ehcs. eapply crange_sub; [exact CFB| clear; lia| clear; lia].
      - cbn [cells_size csize Nat.add]. intros c Hc. right; right; left. exists (FB, 64). split; [left; reflexivity| cbn [fst snd]; clear - Hc; lia]. }
    split.
    { eapply (presA_rw_cells asegs R); [exact PXk| exact SAVE| |].
      - apply client_range_stack. clear - SPV. lia.
      - cbn [cells_size csize Nat.add]. apply DJ; [clear - XS SPV LOSP NE0; lia| right; clear - FBLO LOSP NE0 SPV; lia| right; clear - LOSP NE0 SPV; lia| left; clear - MCLO LOSP NE0 SPV; lia]. }
    split.
    { eapply (presA_stk asegs R); [exact PXk| exact SThi| clear; lia|].
      apply DJ; [clear - XS SPV LOSP NE0; lia| right; clear - FBLO LOSP NE0 SPV; lia| right; clear - LOSP NE0 SPV; lia| left; clear - MCLO LOSP NE0 SPV; lia]. }
    assert (HCS' : forall x, CS x -> hcs asegs R HIA hk x) by (intros x Hx; apply HCSk; rewrite Ehcs; exact Hx).
    assert (HS' : hstkhi asegs R HIA hk = hstkhi asegs R HIA h) by (rewrite HSk; exact Estk).
    split; [| split; [exact HCS'| exact HS']].
    eapply (presW_hmono R HIA h hk); [| exact HCS'| exact HS'].
    flat constr:(PRES0) 2%nat. intros P0 C123. split; [| exact C123].
    eapply presA_trans.
    - eapply presA_weaken; [exact P0| intros b Hb; exact Hb| intros b Hb; exact Hb| apply Z.le_refl| apply Z.le_refl| apply Z.le_refl| intros x _; exact I].
    - eapply (presA_drop_fresh_gen R LB LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) _ FB 64 E (E + 16)); [| exact FRSH| clear; lia| clear; lia| clear - ALO LOS' LOSP NE0 SPV; lia].
      rewrite <- Estk.
      eapply presA_weaken; [exact PXk| intros b Hb; exact Hb| intros b Hb; right; exact Hb| clear - SPV; lia| apply Z.le_refl| apply Z.le_refl|].
      intros x Hx. first [clear - Hx; cbn [outside fst snd] in *; tauto | cbn [outside fst snd] in *; tauto]. (* [comment removed for export] *)
    all: match goal with |- ?g => idtac "FRAMEK-LEFT:" g end.
  Qed.
  (* [comment removed for export] *)
  Lemma dy_fin : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_derive_y ()) "Pv,$5.Pf,$5.Phk,(1>.$2.VR,VHIA,)PLBk,(1?.$?.)Pmk,P,(20.&40.)(21.(20.&8.))PdYk,$52.PdEk,$52.Pr,$5.Pxra,(20.&40.)Pt0,(20.&40.)Pt1,(20.&40.)Pt2,(20.&40.)Pa0,(20.&40.)Pa1,(20.&40.)Pa2,(20.&40.)Pa3,(20.&40.)Pa4,(20.&40.)Pa5,(20.&40.)Pa6,(20.&40.)Pa7,(20.&40.)Pt3,(20.&40.)Pt4,(20.&40.)Pt5,(20.&40.)Pt6,(20.&40.)P,(64.VR,VHIA,Vh1,VLB,(3=.(3>.$5.$5.)(3?.$5.$5.VFB,+40.)VLF,)Vm1,(7.Vsp1,+18.)Vlo,+18.(3=.$47.(63.#10.Vj0,)(3=.$47.(48.(2>.&40.VFB,))(25.$47.)))(3=.(3>.$5.$5.)(3?.$5.$5.(6.VdX,)(7.(6.VdX,)+10.))(3=.(3>.$5.$5.)(3?.$5.$5.(7.VFB,+20.)(7.(7.VFB,+20.)+10.))(3=.(3>.$5.$5.)(3?.$5.$5.$4>.(7.$4>.+8.))(25.(3>.$5.$5.)))))$4>.(7.Vd,+1.)R18.R17.R16.R15.R14.(6.VdX,)R13.(7.VFB,+20.)R12.)P,(4.(20.&40.)(54.R14.)(54.VdX,))P,(0.(15.(58.(59.+2.+1?.))R13.)(13.R13.=))P,(13.(14.R16.)(51.VN,))P,(13.(7.R1<.$65.)(4?.VN,))P,(13.(7.R1<.(66.(7.Vd,+1.)))(50.VN,Vd,))(5:.$2.(5;.$2.VR,VHIA,R1<.Vmo0,)$5<.(2<.(2=.R16.(2>.&40.Vsp1,)Vgp,Vtp,R15.R14.R13.Vsp,(2>.&40.Vsp1,)R12.R11.R10.R?.R>.R=.R<.R;.(2>.&40.VFB,)(2>.&40.(6.VdX,))Vpar,(2>.&40.(6.VdA,))(2>.&40.VG,)(2>.&40.R17.)(2>.&40.(7.VFB,+20.))(2>.&40.(7.VG,+8.))(2>.&40.(7.(49.VFB,+3.)(4:.(1<.VR,))))(2>.&40.VFB,)R:.R9.R8.R7.)VF,(2>.&40.+<;950.)Vfc,(30.(20.&40.))R1:.(31.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros S PADk HR SZk HVB HFB.
    flat constr:(dy_base) 17%nat. flclear dy_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 F8 XS APY Y0 Y16 APG.
    pose proof (conj S I) as Sbox. clear S.
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    (* [comment removed for export] *)
    zstep. zstep.
    flat constr:(Sbox) 2%nat. flclear Sbox. intros S _. clear MU WM LAWS KINV.
    rewrite <- dy_spe.
    eapply ep_free with (h := h1) (LB := LB) (LF := LF') (m := m1) (SP := SPv) (lo := lo) (FR := 24) (FRAME := FRAME) (XO := XO) (MC := MC)
                        (dd := d + 1) (STKMAX := 1344) (A1 := E) (d1 := dEk) (A2 := Y) (d2 := dYk) (v := v) (f := f) (RET := 0xcb958);
      first [ kit_side | exact HFREE | exact (epi_swap R HIA h1 LB LF' m1 SPv lo 24 FRAME XO MC (d + 1) _ _ _ _ _ _ _ _ _ S) | reflexivity
            | (rewrite Evol; clear - BUD HVB; lia) | (rewrite Efr; clear - BUDF HFB; lia) | idtac ].
    all: match goal with |- forall _, _ => idtac | |- ?g => idtac "FIN-FREE-LEFT:" g end.
    intros h' LB' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' S'. rewrite dy_spe.
    flat constr:((epi_swap R HIA h1 LB LF' m1 SPv lo 24 FRAME XO MC (d + 1) _ _ _ _ _ _ _ _ _ S')) 3%nat. intros J' P' _.
    flat constr:((dy_frame_k _ _ h' LB' m' J')) 7%nat. intros FHD' FSH' SAVE' SThi' PRESa HCS' HS'.
    pose proof J' as [HH' SUB' PX' MI' HT' HSk' HF' HCSk' HV' HFR' [ck MC'] ST' FR'].
    flat constr:(P') 4%nat. intros TY TE DIS COV. flat constr:(TY) 5%nat. intros MYk EAk NSk FRSk OAk.
    rewrite dy_spe in ST', FR'.
    chunk_split FR' 1%nat STA SLOT'.
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 64 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & _ & _ & AP & _ & _ & FBLO & SBND & APS). change (64 / 8) with 8 in SBND, APS.
    pose proof (hcs_ok asegs R HIA h') as CSOK'.
    assert (CFB' : crange (hcs asegs R HIA h') FB 64) by (eapply crange_mono; [exact HCS'| exact CFB]).
    pose proof (hcs_stack asegs R HIA h') as SCS0'. rewrite HS' in SCS0'.
    pose proof (hm_top asegs R HIA h _ _ _ HH) as HTOPe.
    assert (SCS' : crange (hcs asegs R HIA h') lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0'| clear - LOS'; lia| clear - TOP HTOPe; lia]).
    (* [comment removed for export] *)
    assert (DYS : disjoint_from [(Z.shiftr FB 3 + al_sb AL, Z.shiftr FB 3 + al_sb AL + 8)] Y 16).
    { pose proof (apart_client_shadow AL (hcs asegs R HIA h') Y 16 FB (Z.shiftr FB 3 + al_sb AL) 8 CSOK' (aobj_crange _ _ _ _ _ _ OAk) CFB' ltac:(shadow_addr_eq) ltac:(clear; lia) ltac:(clear; lia)) as K.
      cbn [disjoint_from fst snd]. split; [clear - K; lia| exact I]. }
    assert (DLS : md_own dYk <> LNull -> disjoint_from [(Z.shiftr FB 3 + al_sb AL, Z.shiftr FB 3 + al_sb AL + 8)] (md_p dYk) (4 * md_n dYk)).
    { intros ON. assert (EO : md_own dYk = LHeap) by (destruct (md_own dYk); [exfalso; exact (ON eq_refl)| reflexivity| exfalso; exact (NSk eq_refl)]).
      flat constr:((ejtmp_blk R HIA h1 LB LF' m1 SPv lo 24 FRAME XO MC _ _ h' LB' m' Y dYk J' TY EO)) 3%nat. intros IN N1 _.
      pose proof (apart_client_shadow AL (hcs asegs R HIA h') (md_p dYk) (4 * md_n dYk) FB (Z.shiftr FB 3 + al_sb AL) 8 CSOK'
                    (aobj_crange _ _ _ _ _ _ (hm_aobj_block asegs R HIA h' _ _ _ _ _ HH' IN)) CFB' ltac:(shadow_addr_eq) ltac:(clear - N1; lia) ltac:(clear; lia)) as K.
      cbn [disjoint_from fst snd]. split; [clear - K; lia| exact I]. }
    assert (DMS : disjoint_from [(Z.shiftr FB 3 + al_sb AL, Z.shiftr FB 3 + al_sb AL + 8)] MC 8).
    { flat constr:(MCOK) 3%nat. intros _ MC2 _. cbn [disjoint_from fst snd]. split; [left; clear - MC2 SBND; lia| exact I]. }
    pose proof (munch_refl [(Z.shiftr FB 3 + al_sb AL, Z.shiftr FB 3 + al_sb AL + 8)] m') as MUs. pose proof (wmono_refl asegs m') as WMs.
    pose proof (conj MC' I) as MCb. clear MC'.
    pose proof (AIh_laws asegs R HIA h') as LAWS. pose proof (KF_kinv asegs R HIA h' mo0) as KINV.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSH9 end.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    flat constr:(MCb) 2%nat. flclear MCb. intros MC' _.
    pose proof (mpd_at_munch_any asegs m' m9 LB' dYk _ MYk MUs WMs ltac:(rewrite EAk; exact DYS) DLS) as MY9.
    pose proof (rw_cells_transport asegs _ _ _ _ _ MC' MUs WMs DMS) as MC9.
    chunk_to_stk STA.
    eapply dy_exit with (FBx := FB) (sp1x := sp1) (hk := h') (LBk := LB') (dYk := dYk) (v := v + AVOL_CALL) (f := f + fr_charge (d + 1));
      first [ exact SP1 | exact SP1M | exact F64 | exact FRSH | exact CFB | exact HCS' | exact HS' | exact HVB | exact HFB | exact MY9 | exact EAk | exact PADk | exact NSk | exact HR | exact SZk
            | exact SUB' | (exists ck; exact MC9) | eassumption
            | (rewrite HT'; exact Ehtop) | (rewrite HF'; exact Eflag) | (rewrite <- Evol; exact HV') | (rewrite <- Efr; exact HFR')
            | (intros b Hb; destruct (COV b Hb) as [K|K]; [left; exact K| right; apply in_app_iff in K; destruct K as [K|K]; [exact K| cbn in K; destruct K]])
            | (intros b Hb; (let flt14 := fresh "FLt" in flat constr:((FRSk b Hb)) 2%nat; intros K1 flt14; flat constr:(flt14) 4%nat; flclear flt14; intros G0 G1 G2 G3); split; [exact K1|]; split; [exact G0|]; split; [exact G1|]; split; [exact G2|];
               intros B j HB; apply G3; exact (dy_lfsub _ HB))
            | idtac ].
    all: match goal with |- ?g => idtac "FIN-LEFT:" g end.
  Qed.
  Lemma dy_budget : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_derive_y ()) "(0.(13.+1.VN,)(0.(0.(13.+1.(14.(3.Vg,)))(13.(14.(3.Vg,))VN,))(0.(13.=(67.VN,))(0.(13.=(68.VN,(7.Vd,+1.)))(0.(0.(13.=(69.(14.(3.Vg,))))(13.(69.(14.(3.Vg,)))(69.VN,)))(0.(13.=(6:.(7.Vd,+1.)))(0.Pa,$5.Pe,$5.Pn,$5.P,(0.(13.=R3.)(13.R3.(6;.VN,)))P,(0.(13.=R2.)(13.R2.VN,))P,(13.R4.(7.VN,+1.))(0.(0.(13.=(6<.R6.R5.R4.))(13.(6<.R6.R5.R4.)(6<.(6;.VN,)(7.VN,+1.)VN,)))(0.(13.=(6=.R6.R5.R4.(7.Vd,+1.)))(13.(6=.R6.R5.R4.(7.Vd,+1.))(6=.(6;.VN,)(7.VN,+1.)VN,(7.Vd,+1.)))))(0.Pa,$5.Pb,$5.P,(0.(13.=R2.)(13.R2.(51.VN,)))P,(0.(13.=R2.)(13.R2.(51.VN,)))(0.(13.=(6>.R4.R3.))(13.(6>.R4.R3.)(6>.(51.VN,)(51.VN,))))(0.(13.=(6?.(7.Vd,+1.)))(0.(4.$5.(66.(7.Vd,+1.))(70.+1.(7.Vd,+1.)))(13.=(66.(7.Vd,+1.)))))))))))))")
(* [comment removed for export] *).
  Proof.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0. flat constr:(NLE) 3%nat. intros NP _ _.
    flat constr:(dy_P_entry) 6%nat. flclear dy_P_entry. intros MP _ _ _ DST _.
    assert (NP1 : 1 <= md_n dP).
    { destruct (md_own dP) eqn:EO; [| (flat constr:((DST ltac:(discriminate))) 2%nat; intros K _); exact K| (flat constr:((DST ltac:(discriminate))) 2%nat; intros K _); exact K].
      exfalso. flat constr:(MP) 2%nat. intros FLt9 _. flat constr:(FLt9) 6%nat. flclear FLt9. intros _ _ _ LLEN _ OW. rewrite EO in OW. flat constr:(OW) 2%nat. flclear OW. intros _ N0'.
      assert (EL : md_limbs dP = []) by (destruct (md_limbs dP); [reflexivity| cbn [length] in LLEN; clear - LLEN N0'; lia]).
      unfold mpd_val in VP. rewrite EL in VP. cbn in VP. clear - VP. lia. }
    assert (N1 : 1 <= N) by (clear - NP NP1; lia).
    split; [exact N1|]. split; [split; [exact NP1| exact NP]|].
    split.
    { unfold sw_rhs_PHIn, mm_PHIn, red_PHIn, mul_mpi_PHIn, addsub_PHIn, intop_PHIn, grow_PHI, ecp_sz. unfold AVOL_CALL.
      pose proof (mod_mpi_PHIn_nonneg (mul_mpi_nz (3 * N + 9) (3 * N + 9) (3 * N + 9)) N ltac:(unfold mul_mpi_nz; clear - N1; lia) ltac:(clear - N1; lia)) as K. clear - K N1. lia. }
    split.
    { unfold sw_rhs_FRn, mm_FRn, red_FRn, mul_mpi_FRn, addsub_FRn, intop_FRn.
      pose proof (mod_mpi_FRn_nonneg (mul_mpi_nz (ecp_sz N) (ecp_sz N) (ecp_sz N)) N (d + 1) ltac:(unfold mul_mpi_nz, ecp_sz; clear - N1; lia) ltac:(clear - D0; lia)) as K1.
      unfold calls_FR, fr_charge. clear - K1 D0. lia. }
    split; [split; [unfold intop_PHIn, grow_PHI; unfold AVOL_CALL; clear - NP1; lia| apply intop_PHIn_mono; exact NP]|].
    split; [unfold intop_FRn, calls_FR, fr_charge; clear - D0; lia|].
    split.
    { intros a e n Ha Hn He. split; (split; [| first [apply exp_mod_PHIn_mono | apply exp_mod_FRn_mono]; first [exact He | clear - Ha Hn D0; lia]]).
      - apply exp_mod_PHIn_nonneg; clear - Ha Hn; lia.
      - apply exp_mod_FRn_nonneg; clear - Ha D0; lia. }
    split; [intros a b Ha Hb; split; [unfold addsub_PHIn, grow_PHI; unfold AVOL_CALL; clear - Ha Hb; lia| apply addsub_PHIn_mono; [exact (proj2 Ha)| exact (proj2 Hb)]]|].
    split; [unfold addsub_FRn, calls_FR, fr_charge; clear - D0; lia|].
    split; [unfold calls_FR; clear; lia| unfold fr_charge; clear - D0; lia].
    all: match goal with |- ?g => idtac "BUDGET-LEFT:" g end.
  Qed.

  (* [comment removed for export] *)
  Lemma dy_fail : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_derive_y ()) "Pv,$5.Pf,$5.Phk,(1>.$2.VR,VHIA,)PLBk,(1?.$?.)Pmk,P,(20.&40.)(21.(20.&8.))PdYk,$52.PdEk,$52.Pr,$5.Pxra,(20.&40.)Pt0,(20.&40.)Pt1,(20.&40.)Pt2,(20.&40.)Pa1,(20.&40.)Pa2,(20.&40.)Pa3,(20.&40.)Pa4,(20.&40.)Pa5,(20.&40.)Pa6,(20.&40.)Pa7,(20.&40.)Pt3,(20.&40.)Pt4,(20.&40.)Pt5,(20.&40.)Pt6,(20.&40.)Ps7v,(20.&40.)P,(64.VR,VHIA,Vh1,VLB,(3=.(3>.$5.$5.)(3?.$5.$5.VFB,+40.)VLF,)Vm1,(7.Vsp1,+18.)Vlo,+18.(3=.$47.(63.#10.Vj0,)(3=.$47.(48.(2>.&40.VFB,))(25.$47.)))(3=.(3>.$5.$5.)(3?.$5.$5.(6.VdX,)(7.(6.VdX,)+10.))(3=.(3>.$5.$5.)(3?.$5.$5.(7.VFB,+20.)(7.(7.VFB,+20.)+10.))(3=.(3>.$5.$5.)(3?.$5.$5.$4>.(7.$4>.+8.))(25.(3>.$5.$5.)))))$4>.(7.Vd,+1.)R18.R17.R16.R15.R14.(6.VdX,)R13.(7.VFB,+20.)R12.)P,(4.(20.&40.)(54.R14.)(54.VdX,))P,(0.(15.(58.(59.+2.+1?.))R13.)(13.R13.=))P,(13.(14.R16.)(51.VN,))P,(13.(7.R1<.$65.)(4?.VN,))P,(13.(7.R1<.(66.(7.Vd,+1.)))(50.VN,Vd,))(5:.$2.(5;.$2.VR,VHIA,R1<.Vmo0,)$5<.(2<.(2=.R16.(2>.&40.Vsp1,)Vgp,Vtp,R15.R14.R13.Vsp,(2>.&40.Vsp1,)(2>.&40.R17.)R12.R11.R10.R?.R>.R=.R<.(2>.&40.VFB,)(2>.&40.(6.VdX,))Vpar,(2>.&40.(6.VdA,))(2>.&40.VG,)R7.(2>.&40.(7.VFB,+20.))(2>.&40.(7.VG,+8.))(2>.&40.(7.(49.VFB,+3.)(4:.(1<.VR,))))(2>.&40.VFB,)R;.R:.R9.R8.)VF,(2>.&40.+<;94<.)Vfc,(30.(20.&40.))R1:.(31.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until s7v. intros S PADk HR SZk HVB HFB.
    pose proof (conj S I) as Sbox; clear S. pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    zstep.
    flat constr:(Sbox) 2%nat. flclear Sbox. intros S _. clear MU WM LAWS KINV.
    eapply dy_fin; eassumption.
  Qed.
  (* [comment removed for export] *)
  Lemma dy_body : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_derive_y ()) "Pxra,(20.&40.)Pt0,(20.&40.)Pt1,(20.&40.)Pt2,(20.&40.)Pa0,(20.&40.)Pa1,(20.&40.)Pa2,(20.&40.)Pa3,(20.&40.)Pa4,(20.&40.)Pa5,(20.&40.)Pa6,(20.&40.)Pa7,(20.&40.)Pt3,(20.&40.)Pt4,(20.&40.)Pt5,(20.&40.)Pt6,(20.&40.)(5:.$2.(5;.$2.VR,VHIA,Vh1,Vmo0,)$5<.(2<.(2=.R10.(2>.&40.Vsp1,)Vgp,Vtp,R?.R>.R=.Vsp,(2>.&40.Vsp1,)R<.R;.R:.R9.R8.R7.R6.R5.(2>.&40.VFB,)(2>.&40.(6.VdX,))Vpar,(2>.&40.(6.VdA,))(2>.&40.VG,)(2>.&40.-4>80.)(2>.&40.(7.VFB,+20.))(2>.&40.(7.VG,+8.))(2>.&40.(7.(49.VFB,+3.)(4:.(1<.VR,))))(2>.&40.VFB,)R4.R3.R2.R1.)VF,(2>.&40.+<;8=4.)Vfc,(30.(20.&40.))Vm1,(31.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6.
    flat constr:(dy_base) 17%nat. flclear dy_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 F8 XS APY Y0 Y16 APG.
    flat constr:(dy_budget) 11%nat. flclear dy_budget. intros N1 (NP1 & NPN) SWP0 SWF0 (IP0 & IPN) IF0 EXPB ASB ASF0 FRC1 FRC0.
    flat constr:(EXTA) 9%nat. intros _ _ _ _ _ AMCs _ _ AUW. flat constr:(OSEP) 3%nat. intros OS1 _ _.
    unfold derive_y_PHIn in BUD. unfold derive_y_FRn in BUDF.
    destruct (EXPB (ecp_sz N) (N + 1) N ltac:(unfold ecp_sz; clear - N1; lia) ltac:(clear - N1; lia) ltac:(clear; lia)) as [[EP0 _] [EF0 _]].
    destruct (ASB (ecp_dy_sz N) (ecp_dy_sz N) ltac:(unfold ecp_dy_sz, ecp_sz; clear - N1; lia) ltac:(unfold ecp_dy_sz, ecp_sz; clear - N1; lia)) as [AP0 _].
    pose proof dy_start as S0.
    pose proof (conj S0 I) as Sbox; clear S0. pose proof (AIh_laws asegs R HIA h1) as LAWS. pose proof (KF_kinv asegs R HIA h1 mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    (* [comment removed for export] *)
    do 4 zstep.
    flat constr:(Sbox) 2%nat. flclear Sbox. intros S0 _. clear MU WM LAWS KINV.
    rewrite <- dy_spe.
    eapply ep_rhs with (h := h1) (LB := LB) (LF := LF') (m := m1) (SP := SPv) (lo := lo) (FR := 24) (FRAME := FRAME) (XO := XO) (MC := MC)
                       (dd := d + 1) (slo := slo) (STKMAX := 1344) (G := G) (g := g) (A1 := Y) (d1 := dX) (A2 := E) (d2 := dE0) (eA := dA) (N := N) (v := 0) (f := 0) (RET := 0xcb8e4);
      first [ kit_side | exact HSR | exact S0 | exact dy_extX | reflexivity | exact XNULL | exact SGA | exact SGB | exact VP | exact NLE | exact NA | exact AMCs | exact OS1
            | exact SWP0 | exact SWF0
            | (eapply uw_obj_mono_d; [exact AUW| clear; lia])
            | (cbn [length]; clear - LFB; lia)
            | (rewrite Evol; clear - BUD SWP0 IP0 IPN EP0 AP0; unfold AVOL_CALL in *; lia)
            | (rewrite Efr; clear - BUDF SWF0 IF0 EF0 ASF0 FRC0 FRC1; lia)
            | (unfold C24_ECP_SW_RHS; unfold C24_ECP_DERIVE_Y in C24H; clear - C24H; lia)
            | idtac ].
    all: match goal with |- forall _, _ => idtac | |- ?g => idtac "RHS-CALL-LEFT:" g end.
    intros h2 LB2 m2 dY1 r1 t0_1 t1_1 t2_1 a1_1 a2_1 a3_1 a4_1 a5_1 a6_1 a7_1 t3_1 t4_1 t5_1 t6_1 S1 [RR1 BK1] SZ1. rewrite dy_spe.
    flat constr:(BK1) 4%nat. intros _ PAD1 _ NY1. flat constr:(MX0) 2%nat. intros FLt10 _. flat constr:(FLt10) 6%nat. flclear FLt10. intros _ _ _ _ _ OW0. rewrite XNULL in OW0. flat constr:(OW0) 2%nat. flclear OW0. intros _ NX0. rewrite NX0 in NY1.
    assert (AGE : E + 16 <= G \/ G + 192 <= E) by (clear - APG; lia).
    assert (UWP : uw_obj R (md_addr dP) 16 (d + 1)).
    { flat constr:(dy_P_entry) 3%nat. flclear dy_P_entry. intros _ EPa _. rewrite EPa. destruct GRP as (_ & _ & _ & _ & _ & _ & _ & _ & [[GU1 GU2]|GU]); [left; split; [clear - GU1; lia| clear - GU2; lia]| right; clear - GU; lia]. }
    assert (UWY : uw_obj R Y 16 (d + 1)) by (eapply uw_obj_mono_d; [exact UWX| clear; lia]).
    assert (UWE : uw_obj R E 16 (d + 1)) by (left; split; [clear - F1 ALO; lia| exact dy_k_d0]).
    flat constr:(dy_P_entry) 3%nat. flclear dy_P_entry. intros _ EPa _.
    pose proof (conj S1 I) as Sbox; clear S1. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. if_cases KR1; zify_cond KR1.
    { flat constr:(Sbox) 2%nat. flclear Sbox. intros S1 _. clear MU WM LAWS KINV.
      eapply (dy_fail _ _ h2 LB2 m2 dY1 dE0 r1); [exact S1| exact PAD1| exact RR1| unfold ecp_dy_sz; clear - SZ1; lia
        | unfold derive_y_PHIn; clear - SWP0 IP0 IPN EP0 AP0 ; unfold AVOL_CALL in *; lia| unfold derive_y_FRn; clear - SWF0 IF0 EF0 ASF0 FRC0 FRC1 ; lia]. }
    (* [comment removed for export] *)
    do 4 zstep.
    flat constr:(Sbox) 2%nat. flclear Sbox. intros S1 _. clear MU WM LAWS KINV.
    rewrite <- dy_spe.
    eapply ep_intop with (h := h1) (LB := LB) (LF := LF') (m := m1) (SP := SPv) (lo := lo) (FR := 24) (FRAME := FRAME) (XO := XO) (MC := MC) (dd := d + 1) (STKMAX := 1344) (ENTRY := A_MPI_ADD_INT) (A1 := E) (d1 := dE0) (A2 := Y) (d2 := dY1) (eA := dP) (b := 1)
                         (v := 0 + sw_rhs_PHIn N) (f := 0 + sw_rhs_FRn N (d + 1)) (RET := 0xcb8f8);
      first [ kit_side | exact HADDI | exact (epi_swap R HIA h1 LB LF' m1 SPv lo 24 FRAME XO MC (d + 1) _ _ _ _ _ _ _ _ _ S1) | exact UWP | reflexivity | exact IF0
            | exact (or_intror (or_intror (dy_extP E _ AGE EXI eq_refl)))
            | (rewrite EPa; reflexivity)
            | (cbv beta; exact IP0)
            | (cbn [length]; clear - LFB; lia)
            | (cbv beta; rewrite Evol; clear - BUD SWP0 IP0 IPN EP0 AP0; unfold AVOL_CALL in *; lia)
            | (rewrite Efr; clear - BUDF SWF0 IF0 EF0 ASF0 FRC0 FRC1; lia)
            | (unfold C24_INTOP; unfold C24_ECP_DERIVE_Y in C24H; clear - C24H; lia)
            | idtac ].
    all: match goal with |- forall _, _ => idtac | |- ?g => idtac "ADDINT-CALL-LEFT:" g end.
    cbv beta. intros h3 LB3 m3 dE2 r2 t0_2 t1_2 t2_2 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 t3_2 t4_2 t5_2 t6_2 S2 [[RV2 BK2] SZ2]. rewrite dy_spe.
    assert (NE2 : md_n dE2 <= N + 1) by (unfold intop_nz in SZ2; cbn [md_n] in SZ2; clear - SZ2 NP1 NPN; lia).
    assert (HR2 : -2^31 < r2 <= 0) by (destruct RV2 as [(R0 & _)|RF]; subst r2; [clear; lia| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia]).
    pose proof (conj S2 I) as Sbox; clear S2. pose proof (AIh_laws asegs R HIA h3) as LAWS. pose proof (KF_kinv asegs R HIA h3 mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    (* [comment removed for export] *)
    zstep. if_cases KR2; zify_cond KR2.
    { flat constr:(Sbox) 2%nat. flclear Sbox. intros S2 _. clear MU WM LAWS KINV.
      eapply (dy_fail _ _ h3 LB3 m3 dY1 dE2 r2); [exact (epi_swap R HIA h1 LB LF' m1 SPv lo 24 FRAME XO MC (d + 1) _ _ _ _ _ _ _ _ _ S2)| exact PAD1| exact HR2| unfold ecp_dy_sz; clear - SZ1; lia
        | unfold derive_y_PHIn; clear - SWP0 IP0 IPN EP0 AP0 ; unfold AVOL_CALL in *; lia| unfold derive_y_FRn; clear - SWF0 IF0 EF0 ASF0 FRC0 FRC1 ; lia]. }
    (* [comment removed for export] *)
    do 3 zstep.
    flat constr:(Sbox) 2%nat. flclear Sbox. intros S2 _. clear MU WM LAWS KINV.
    rewrite <- dy_spe.
    eapply ep_shift_r with (h := h1) (LB := LB) (LF := LF') (m := m1) (SP := SPv) (lo := lo) (FR := 24) (FRAME := FRAME) (XO := XO) (MC := MC) (dd := d + 1) (STKMAX := 1344) (ENTRY := A_MPI_SHIFT_R_E) (A1 := E) (d1 := dE2) (A2 := Y) (d2 := dY1) (count := 2) (RET := 0xcb908);
      first [ exact S2 | exact HSHR | kit_side | reflexivity | idtac ].
    all: match goal with |- forall _, _ => idtac | |- ?g => idtac "SHIFTR-CALL-LEFT:" g end.
    intros m4 dE3 t0_3 t1_3 t2_3 a1_3 a2_3 a3_3 a4_3 a5_3 a6_3 a7_3 t3_3 t4_3 t5_3 t6_3 S3 NE3 OE3. rewrite dy_spe. rewrite <- NE3 in NE2.
    pose proof (conj S3 I) as Sbox; clear S3. pose proof (AIh_laws asegs R HIA h3) as LAWS. pose proof (KF_kinv asegs R HIA h3 mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    do 6 zstep.
    flat constr:(Sbox) 2%nat. flclear Sbox. intros S3 _. clear MU WM LAWS KINV.
    flat constr:(S3) 3%nat. intros _ FLt11 _. flat constr:(FLt11) 3%nat. flclear FLt11. intros (_ & EAE3 & _) (_ & EAY1 & _) _.
    flat constr:(dy_tmpY) 2%nat. flclear dy_tmpY. intros ((CYo & _) & _) _.
    assert (AGY : Y + 16 <= G \/ G + 192 <= Y) by exact OS1.
    destruct (EXPB (md_n dY1) (md_n dE3) (md_n dP) ltac:(clear - NY1 SZ1; lia) ltac:(clear - NP1 NPN; lia) NE2) as [[EPk0 EPkN] [EFk0 EFkN]].
    rewrite <- dy_spe.
    eapply ep_expmod with (h := h1) (LB := LB) (LF := LF') (m := m1) (SP := SPv) (lo := lo) (FR := 24) (FRAME := FRAME) (XO := XO) (MC := MC) (dd := d + 1) (STKMAX := 1344) (slo := slo) (ENTRY := A_MPI_EXP_MOD) (A1 := Y) (d1 := dY1) (A2 := E) (d2 := dE3) (eA := dY1) (eE := dE3) (eN := dP)
                          (v := (0 + sw_rhs_PHIn N + intop_PHIn (md_n dP))) (f := (0 + sw_rhs_FRn N (d + 1) + intop_FRn (d + 1))) (RET := 0xcb924);
      first [ exact HEXP | exact (epi_swap R HIA h1 LB LF' m1 SPv lo 24 FRAME XO MC (d + 1) _ _ _ _ _ _ _ _ _ S3) | kit_side | exact UWP | exact P4999 | exact EPk0 | exact EFk0 | reflexivity
            | (apply Z.le_refl)
            | exact (or_introl eq_refl) | exact (or_intror (or_introl eq_refl))
            | exact (or_intror (or_intror (dy_extP Y _ AGY CYo eq_refl)))
            | (rewrite EAY1; exact UWY) | (rewrite EAE3; exact UWE) | (rewrite EAY1; reflexivity) | (rewrite EAE3; reflexivity)
            | (rewrite EPa; reflexivity)
            | (intros C; rewrite C in EAE3; rewrite EAY1 in EAE3; clear - EAE3 APY; lia)
            | (intros C; rewrite <- C in EAY1; rewrite EPa in EAY1; clear - EAY1 OS1; lia)
            | (cbn [length]; clear - LFB; lia)
            | (rewrite Evol; clear - BUD SWP0 IP0 IPN EPk0 EPkN AP0; unfold AVOL_CALL in *; lia)
            | (rewrite Efr; clear - BUDF SWF0 IF0 EFk0 EFkN ASF0 FRC0 FRC1; lia)
            | (unfold C24_EXP_MOD; unfold C24_ECP_DERIVE_Y in C24H; clear - C24H; lia)
            | idtac ].
    all: match goal with |- forall _, _ => idtac | |- ?g => idtac "EXPMOD-CALL-LEFT:" g end.
    intros h5 LB5 m5 dY5 r5 t0_5 t1_5 t2_5 a1_5 a2_5 a3_5 a4_5 a5_5 a6_5 a7_5 t3_5 t4_5 t5_5 t6_5 S5 [[RR5 BK5] SZ5]. rewrite dy_spe.
    flat constr:(BK5) 4%nat. intros _ PAD5 _ NY5. rewrite PAD1 in PAD5.
    assert (SZ5' : md_n dY5 <= ecp_sz N + 3) by (unfold exp_mod_nz in SZ5; unfold ecp_sz in *; clear - SZ5 SZ1 NPN N1; lia).
    pose proof (conj S5 I) as Sbox; clear S5. pose proof (AIh_laws asegs R HIA h5) as LAWS. pose proof (KF_kinv asegs R HIA h5 mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m5) as MU. pose proof (wmono_refl asegs m5) as WM.
    (* [comment removed for export] *)
    zstep. if_cases KR5; zify_cond KR5.
    { flat constr:(Sbox) 2%nat. flclear Sbox. intros S5 _. clear MU WM LAWS KINV.
      eapply (dy_fail _ _ h5 LB5 m5 dY5 dE3 r5); [exact S5| exact PAD5| exact RR5| unfold ecp_dy_sz; clear - SZ5'; lia
        | unfold derive_y_PHIn; clear - SWP0 IP0 IPN EP0 AP0 EPk0 EPkN; unfold AVOL_CALL in *; lia| unfold derive_y_FRn; clear - SWF0 IF0 EF0 ASF0 FRC0 FRC1 EFk0 EFkN; lia]. }
    (* [comment removed for export] *)
    do 3 zstep.
    flat constr:(Sbox) 2%nat. flclear Sbox. intros S5 _. clear MU WM LAWS KINV.
    rewrite <- dy_spe.
    eapply ep_query with (h := h1) (LB := LB) (LF := LF') (m := m1) (SP := SPv) (lo := lo) (FR := 24) (FRAME := FRAME) (XO := XO) (MC := MC) (dd := d + 1) (STKMAX := 1344) (ENTRY := A_MPI_GET_BIT_Q) (A1 := Y) (d1 := dY5) (A2 := E) (d2 := dE3) (z := 0) (RET := 0xcb934);
      first [ exact (A_mpi_get_bit_spec AL IMG) | exact S5 | kit_side | reflexivity | (cbv beta; clear; lia) | idtac ].
    all: match goal with |- forall _, _ => idtac | |- ?g => idtac "GETBIT-CALL-LEFT:" g end.
    cbv beta. intros m6 r6 t0_6 t1_6 t2_6 a1_6 a2_6 a3_6 a4_6 a5_6 a6_6 a7_6 t3_6 t4_6 t5_6 t6_6 S6 RQ6. rewrite dy_spe.
    pose proof (conj S6 I) as Sbox; clear S6. pose proof (AIh_laws asegs R HIA h5) as LAWS. pose proof (KF_kinv asegs R HIA h5 mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m6) as MU. pose proof (wmono_refl asegs m6) as WM.
    (* [comment removed for export] *)
    zstep. zstep. if_cases KPAR.
    { flat constr:(Sbox) 2%nat. flclear Sbox. intros S6 _. clear MU WM LAWS KINV.
      eapply (dy_fin _ _ h5 LB5 m6 dY5 dE3 0); [exact S6| exact PAD5| clear; lia| unfold ecp_dy_sz; clear - SZ5'; lia
        | unfold derive_y_PHIn; clear - SWP0 IP0 IPN EP0 AP0 EPk0 EPkN; unfold AVOL_CALL in *; lia| unfold derive_y_FRn; clear - SWF0 IF0 EF0 ASF0 FRC0 FRC1 EFk0 EFkN; lia]. }
    (* [comment removed for export] *)
    do 4 zstep.
    flat constr:(Sbox) 2%nat. flclear Sbox. intros S6 _. clear MU WM LAWS KINV.
    flat constr:(S6) 3%nat. intros _ FLt12 _. flat constr:(FLt12) 2%nat. flclear FLt12. intros (_ & EAY5 & _) _.
    destruct (ASB (md_n dP) (md_n dY5) ltac:(unfold ecp_dy_sz, ecp_sz; clear - NP1 NPN; lia) ltac:(unfold ecp_dy_sz; clear - NY5 NY1 SZ5'; lia)) as [APk0 APkN].
    rewrite <- dy_spe.
    eapply ep_binop with (h := h1) (LB := LB) (LF := LF') (m := m1) (SP := SPv) (lo := lo) (FR := 24) (FRAME := FRAME) (XO := XO) (MC := MC) (dd := d + 1) (STKMAX := 1344) (slo := slo) (ENTRY := A_MPI_SUB_MPI) (STACK := MPI_ADD_SUB_STACK_A) (NF := 0%nat) (C24 := C24_ADDSUB)
                         (PHI := fun dX dA dB => addsub_PHIn (md_n dA) (md_n dB)) (FRC := fun _ _ _ d => addsub_FRn d) (Rr := sub_mpi_Rsz)
                         (A1 := Y) (d1 := dY5) (A2 := E) (d2 := dE3) (eA := dP) (eB := dY5)
                         (v := (0 + sw_rhs_PHIn N + intop_PHIn (md_n dP) + exp_mod_PHIn (md_n dY1) (md_n dE3) (md_n dP))) (f := (0 + sw_rhs_FRn N (d + 1) + intop_FRn (d + 1) + exp_mod_FRn (md_n dY1) (md_n dE3) (md_n dP) (d + 1))) (RET := 0xcb94c);
      first [ exact HSUBM | exact S6 | kit_side | exact UWP | exact ASF0 | reflexivity
            | exact (or_introl eq_refl)
            | exact (or_intror (or_intror (dy_extP Y _ AGY CYo eq_refl)))
            | (rewrite EAY5; exact UWY) | (rewrite EAY5; reflexivity)
            | (rewrite EPa; reflexivity)
            | (right; rewrite EPa, EAY5; clear - OS1; lia)
            | (cbv beta; exact APk0)
            | (cbn [length]; clear - LFB; lia)
            | (cbv beta; rewrite Evol; clear - BUD SWP0 IP0 IPN EPk0 EPkN APk0 APkN; unfold AVOL_CALL in *; lia)
            | (cbv beta; rewrite Efr; clear - BUDF SWF0 IF0 EFk0 EFkN ASF0 FRC0 FRC1; lia)
            | (unfold C24_ADDSUB; unfold C24_ECP_DERIVE_Y in C24H; clear - C24H; lia)
            | idtac ].
    all: match goal with |- forall _, _ => idtac | |- ?g => idtac "SUBMPI-CALL-LEFT:" g end.
    cbv beta. intros h7 LB7 m7 dY7 r7 t0_7 t1_7 t2_7 a1_7 a2_7 a3_7 a4_7 a5_7 a6_7 a7_7 t3_7 t4_7 t5_7 t6_7 S7 [[RV7 BK7] SZ7]. rewrite dy_spe.
    flat constr:(BK7) 3%nat. intros _ PAD7 _. rewrite PAD5 in PAD7.
    assert (HR7 : -2^31 < r7 <= 0) by (destruct RV7 as [(R0 & _)|RF]; subst r7; [clear; lia| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia]).
    eapply (dy_fail _ _ h7 LB7 m7 dY7 dE3 r7); [exact S7| exact PAD7| exact HR7| unfold addsub_nz in SZ7; clear - SZ7 SZ5' NPN N1; unfold ecp_dy_sz, ecp_sz in *; lia
      | unfold derive_y_PHIn; clear - SWP0 IP0 IPN EP0 AP0 EPk0 EPkN APk0 APkN; unfold AVOL_CALL in *; lia| unfold derive_y_FRn; clear - SWF0 IF0 EF0 ASF0 FRC0 FRC1 EFk0 EFkN; lia].
    all: match goal with |- ?g => idtac "BODY-LEFT:" g end.
  Qed.
  End J.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma dy_main : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_derive_y ()) "Pt0,(20.&40.)Pt1,(20.&40.)Pt2,(20.&40.)Pa4,(20.&40.)Pa5,(20.&40.)Pa6,(20.&40.)Pa7,(20.&40.)Pt3,(20.&40.)Pt4,(20.&40.)Pt5,(20.&40.)Pt6,(20.&40.)P,(3<.$2.VR,VHIA,Vh,Vmo0,)P,(29.$2.Vm,Vlo,(11.&40.Vsp,))(71.$2.$5<.(72.(2<.(2=.Vra,Vsp,Vgp,Vtp,R=.R<.R;.Vs0,Vs1,(2>.&40.VG,)(2>.&40.(6.VdA,))(2>.&40.(6.VdX,))Vpar,R:.R9.R8.R7.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.R5.R4.R3.)VF,(2>.&40.$2?.)Vfc,(30.(20.&40.))Vm,(31.$2.))Vmo0,))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros HK0 ST.
    apply (aevtA_enter asegs (KF asegs R HIA h mo0) _ _ _ (conj HK0 (mo_frame_refl mo0))).
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo0).
    { eapply pro_walk; exact ST. }
    intros ms1 P1.
    destruct P1 as (FB & sp1 & h1 & m1 & early & xra & y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & s8v & w0 & w1 & w2 & ecells
                   & Ems & EARLY & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & EXB & ESZ & FSH & SAVE & SLOT & ST16 & SThi & STlo & MI1 & PRES0 & SSH1).
    subst ms1.
    unfold aevtA. intros mo1 [HK1 MF1].
    apply (aevtA_enter asegs (KF asegs R HIA h1 mo0) _ _ mo1 (conj (proj2 (HKI mo1) HK1) MF1)).
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 64 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS) as (CFB & _).
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0. pose proof (hcs_ok asegs R HIA h) as CSOK.
    destruct early.
    - (* [comment removed for export] *)
      flat constr:(XW) 2%nat. intros XCW XP.
      assert (CRXs : client_range L (LB ++ fdata LF) (bv_unsigned sp) Y 16) by (eapply client_range_of_w; exact XCW).
      pose proof (presW_presA asegs R HIA h LB LF _ _ _ m m1 PRES0) as HP01.
      flat constr:(MX0) 2%nat. intros FLt13 _. flat constr:(FLt13) 6%nat. flclear FLt13. intros _ _ _ _ _ OW0. rewrite XNULL in OW0. flat constr:(OW0) 2%nat. flclear OW0. intros _ NX0.
      assert (N0 : 0 <= N) by ((flat constr:(NLE) 2%nat; intros NP _); (flat constr:(dy_P_entry) 2%nat; flclear dy_P_entry; intros MPe _); pose proof MPe as [(_ & _ & _ & _ & NRP & OWP) _];
                               destruct (md_own dP); [(flat constr:(OWP) 2%nat; flclear OWP; intros _ K)| (flat constr:(OWP) 2%nat; flclear OWP; intros K _)| (flat constr:(OWP) 2%nat; flclear OWP; intros K _)]; clear - K NP; lia).
      eapply dy_exit with (FBx := FB) (sp1x := sp1) (hk := h1) (LBk := LB) (dYk := dX) (v := 0) (f := 0) (r := -20096);
        first [ exact SP1 | exact SP1M | exact F64 | exact FRSH | exact CFB | exact HH1 | exact Ehtop | exact Estk | exact Eflag | exact FHD | exact FSH | exact SAVE | exact SLOT
              | exact ST16 | exact SThi | exact STlo | exact MI1 | reflexivity
              | (rewrite Ehcs; intros x Hx; exact Hx) | (rewrite Evol; clear; lia) | (rewrite Efr; clear; lia)
              | (intros b Hb; exact Hb) | (intros b Hb; left; exact Hb)
              | (rewrite XNULL; discriminate)
              | (intros b Hb; unfold mpd_blk in Hb; rewrite XNULL in Hb; destruct Hb)
              | (clear; lia) | (rewrite NX0; unfold ecp_dy_sz, ecp_sz; clear - N0; lia)
              | idtac ].
      + (* [comment removed for export] *)
        unfold derive_y_PHIn, sw_rhs_PHIn, mm_PHIn, red_PHIn, mul_mpi_PHIn, addsub_PHIn, intop_PHIn, exp_mod_PHIn, grow_PHI, ecp_dy_sz, ecp_sz. unfold AVOL_CALL.
        pose proof (mod_mpi_PHIn_nonneg (mul_mpi_nz (3 * N + 9) (3 * N + 9) (3 * N + 9)) N ltac:(unfold mul_mpi_nz; clear - N0; lia) N0) as K. clear - K N0. lia.
      + unfold derive_y_FRn, sw_rhs_FRn, mm_FRn, red_FRn, mul_mpi_FRn, addsub_FRn, intop_FRn.
        pose proof (mod_mpi_FRn_nonneg (mul_mpi_nz (ecp_sz N) (ecp_sz N) (ecp_sz N)) N (d + 1) ltac:(unfold mul_mpi_nz, ecp_sz; clear - N0; lia) ltac:(clear - D0; lia)) as K1.
        pose proof (exp_mod_FRn_nonneg (ecp_sz N) (N + 1) N (d + 1) ltac:(unfold ecp_sz; clear - N0; lia) ltac:(clear - D0; lia)) as K2.
        unfold calls_FR, fr_charge. clear - K1 K2 D0. lia.
      + (* [comment removed for export] *)
        eapply (presW_hmono R HIA h h1); [| rewrite Ehcs; intros x Hx; exact Hx| exact Estk].
        flat constr:(PRES0) 2%nat. intros P0 C123. split; [| exact C123].
        eapply presA_weaken; [exact P0| intros b Hb; exact Hb| intros b Hb; exact Hb| apply Z.le_refl| apply Z.le_refl| apply Z.le_refl| intros x _; exact I].
      + eapply (mpd_at_heap_presx asegs L); [exact MX0| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP01)| exact MI| exact MI1| exact CRXs| intros EO; rewrite XNULL in EO; discriminate EO| exact I| intros _; exact I|].
        intros b Hb. unfold mpd_blk in Hb. rewrite XNULL in Hb. destruct Hb.
      + exists cnt. flat constr:(MCOK) 4%nat. intros MC1 MC2 MC3 _.
        eapply (presA_rw_cells asegs R); [exact HP01| exact MC0| | exact I].
        cbn [cells_size csize Nat.add]. intros x Hx. right. left. split; [clear - Hx MC1 MC2; lia| apply MC3; exact Hx].
    - (* [comment removed for export] *)
      flat constr:((EARLY eq_refl)) 3%nat. intros -> padE ->. cbv iota in FSH.
      destruct (stk_carve asegs m1 sp1 (sp1 + 16) 16 ST16 ltac:(clear; lia)) as [_ [j0 CH]].
      replace (sp1 + 16 - Z.of_nat 16) with sp1 in CH by (clear; lia).
      assert (FRM : rw_cells asegs m1 sp1 [CB 16 j0; C8 (Z_to_bv 64 FB)]).
      { change [CB 16 j0; C8 (Z_to_bv 64 FB)] with ([CB 16 j0] ++ [C8 (Z_to_bv 64 FB)]). apply rw_cells_app. split; [exact CH|].
        cbn [cells_size csize Nat.add]. replace (sp1 + Z.of_nat 16) with (sp1 + 16) by (clear; lia). exact SLOT. }
      eapply (dy_body FB sp1 h1 m1 padE w0 w1 w2 j0); eassumption.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  End Call.

  Theorem A_ecp_sw_derive_y_spec_s : ecp_derive_y_stmtA asegs R HIA MT A_ECP_SW_DERIVE_Y MC.
  Proof.
    unfold ecp_derive_y_stmtA, ecp_rhs_stmtA. intros until slo. cbv iota.
    intros HH HK LFB GRP OSEP SGA SGB VP P4999 NLE NA MX EO XW EXTA MC0 MCOK ST LOS SLO SSH SLO1 SLO3 TOP SPA TPV MI RAE OXA BUD UW UWX BUDF C24H -> [-> ->].
    eapply dy_main with (cnt := cnt) (N := N) (d := d) (slo := slo); first [ eassumption | exact (P4999 eq_refl) | idtac ].
    all: match goal with |- ?g => idtac "SPEC-LEFT:" g end.
  Qed.
End DY.

Theorem A_ecp_sw_derive_y_spec : ltac2:(CDefT.buildp (gd_tbl_A_ecp_sw_derive_y ()) "PR,$73.PHIA,(74.$2.R1.)PMT,(1?.$75.)P,(76.(1<.R3.))P,(4.$5.(77.R4.)$78.)P,(4.$5.(79.R5.=)$7:.)P,(13.=(7;.R6.))P,(13.=(7<.R7.))P,Ph,(1>.$2.R8.R7.)PLB,(1?.$?.)PLF,(1?.$?.)Pm,P,(20.&40.)(21.(20.&8.))P,(28.$2.R<.R;.R4.R3.R2.R1.)(7=.$5.(7>.(3>.$5.$5.)$5.(56.$5.$5.)R4.))P,(0.(13.(7?.(=.R9.))(80.(=.R9.)))(13.(81.(=.R9.))(82.(=.R9.))))P,Pa,$5.P,(4.$18.(83.$2.(84.R1.))$1:.)P,(0.(13.=R2.)(15.R2.(59.+2.+40.)))(0.(13.(7?.(=.R=.))R3.)(15.R3.(82.(=.R=.))))P,(85.$2.R;.R:.R9.$86.$4>.)P,(87.$2.R<.R;.$88.)P,(89.$2.R=.R<.$8:.)P,(8;.$2.R>.R=.$8<.)P,(8=.$2.R?.R>.$8>.)P,(8?.$2.R10.R?.$90.)(91.$2.R11.R10.R?.$2?.$4>.)")
(* [comment removed for export] *).
Proof. intros. eapply A_ecp_sw_derive_y_spec_s; eauto. Qed.
