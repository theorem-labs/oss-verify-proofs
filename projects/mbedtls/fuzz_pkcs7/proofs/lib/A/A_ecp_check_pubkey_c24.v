(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux Asn1Aux ZBridge.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts MpiVal MpiFacts MpiOpnd RepEcp EcpFacts EcpCurves EcpLoad.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_addsub P_mpi_grow P_mpi_free P_mpi_copy P_ecp_group_free P_ecp_red P_ecp_mul_mod P_ecp_sw_rhs P_ecp_check_pubkey.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import AImg AImgGlobals AImgRT A_rt_facts A_alloc_lib A_mpi_read_binary_stmt A_mpi_stmtA A_mpi_stmtA_sz A_mpi_stmtA_ng_sz A_ecp_stmtA
     A_mpi_opnd A_mpi_journey A_mpi_journey2 A_mpi_copy A_mpi_bitlen A_mpi_init A_mpi_free A_mpi_cmp_mpi A_mpi_cmp_int A_mpi_add_int A_ecp_mul_mod A_ecp_sw_rhs A_ecp_journey A_ecp_journey2 A_ecp_pair A_ecp_one.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require Import A_mpi_stmtA_c24 A_mpi_copy_c24.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.A Require A_ecp_one_c24.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
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
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00c79acaec3d3b81 0 7 0 1 47 1 72 1 93 1 102 1 110 1 111 1P00d1b41d3fa7d320 0 6 0 1 46 1 67 1 76 1 84 1 85 1P00f59f6e1d03dae5 0 4 0 1 64 1 84 1 85 1P00f9ea9fc4105201 0 4 0 1 64 1 84 1 85 1P0131952bb4808f91 1 1 16 3 0 1 106 1 107 1 10 47 1 67 1 69 1 86 1 87 1 88 1 97 1 105 1 108 1 109 16P0189a64b75a7017d 0 4 0 1 64 1 84 1 85 1P01bd46969f28e010 1 1 16 3 0 1 105 1 106 1 4 58 2 104 2 107 2 108 32P0246e6e8bdac52b3 0 7 0 1 41 1 66 1 87 1 96 1 104 1 105 1P0294a874b34f232b 0 6 0 1 46 1 67 1 76 1 84 1 85 1P02ce7d0c83eb627a 1 1 16 3 0 1 111 1 112 1 10 52 1 72 1 74 1 91 1 92 1 93 1 102 1 110 1 113 1 114 16P03041492c2d64d19 1 1 16 3 1 1 35 1 85 1 9 47 1 49 1 50 1 66 1 67 1 68 1 77 1 86 1 87 16P0352ffa69653c1f6 1 1 16 3 0 1 111 1 112 1 4 64 1 110 1 113 1 114 16P03caa56a1e77c461 1 1 16 4 1 1 37 1 39 1 85 1 9 47 1 49 1 50 1 66 1 67 1 68 1 77 1 86 1 87 16P041e7751124d6712 0 6 0 1 72 1 93 1 102 1 110 1 111 1P04c3b11e5deabeb5 0 8 0 1 46 1 65 1 66 1 67 1 76 1 84 1 85 1P04d81b3970cecabd 0 8 0 1 62 1 73 1 74 1 75 1 84 1 92 1 93 1P053f902dcd184b55 1 1 16 4 1 1 37 1 39 1 85 1 9 47 1 49 1 50 1 66 1 67 1 68 1 77 1 86 1 87 16P0601b6a773aeacaf 0 6 0 1 46 1 67 1 76 1 84 1 85 1P060f6971ccbf518c 1 1 16 3 0 1 111 1 112 1 4 64 2 110 2 113 2 114 32P066de345ba68de24 1 1 16 3 0 1 111 1 112 1 4 64 2 110 2 113 2 114 32P06909c9a8d7cc137 1 2 16 2 0 1 86 1 16 2 1 1 85 1 2 87 1 88 1P0700146e197a7f0c 0 6 0 1 46 1 67 1 76 1 84 1 85 1P0711667c4ec4a68f 0 8 0 1 46 1 65 1 66 1 67 1 76 1 84 1 85 1P07e504a354ac9244 1 1 32 3 0 1 104 1 107 1 11 41 2 46 2 66 2 68 2 85 2 86 2 87 2 96 2 105 2 106 2 108 64P08876f02795d0ddb 0 5 0 1 32 1 64 1 84 1 85 1P08dd86eddab5b90b 1 1 16 3 0 1 127 1 128 1 10 68 1 88 1 90 1 107 1 108 1 109 1 118 1 126 1 129 1 130 16P097ef827d08a9b74 0 4 0 1 64 1 84 1 85 1P09f4cf0c61b4a8f2 0 5 0 1 32 1 64 1 84 1 85 1P0a824d2eca0bd6aa 0 8 0 1 46 1 65 1 66 1 67 1 76 1 84 1 85 1P0aae4d87fdbd4752 0 8 0 1 62 1 73 1 74 1 75 1 84 1 92 1 93 1P0ab374ae83da4cc7 1 2 16 2 0 1 86 1 16 2 1 1 85 1 2 87 1 88 1P0adf499ffcffd3d7 1 1 16 4 1 1 37 1 39 1 85 1 9 47 1 49 1 50 1 66 1 67 1 68 1 77 1 86 1 87 16P0b1fce2352cf3e6b 0 8 0 1 62 1 73 1 74 1 75 1 84 1 92 1 93 1P0bacaba97de0affa 0 7 0 1 63 1 88 1 109 1 118 1 126 1 127 1P0be5c58afbf3890f 0 5 0 1 32 1 64 1 84 1 85 1P0be6cf24ea2a83e4 0 8 0 1 62 1 73 1 74 1 75 1 84 1 92 1 93 1P0c330159bb30ae05 1 2 32 3 0 1 105 1 108 1 32 3 1 1 106 1 107 1 2 109 2 110 2P0c778db16e4bff0d 1 1 16 3 0 1 111 1 112 1 10 52 1 72 1 74 1 91 1 92 1 93 1 102 1 110 1 113 1 114 16P0c7dcedece78bfd8 0 7 0 1 47 1 72 1 93 1 102 1 110 1 111 1P0cff021328b6bb32 1 2 32 3 0 1 105 1 108 1 32 3 1 1 106 1 107 1 2 109 2 110 2P0d381d6627286484 0 5 0 1 53 1 72 1 92 1 93 1P0d6f01a60ecc1021 1 1 16 3 0 1 111 1 112 1 4 64 1 110 1 113 1 114 16P0dc0a738c32cb2b8 1 1 16 3 0 1 111 1 112 1 4 64 1 110 1 113 1 114 16P0e5506f09a6eb9d1 1 1 32 3 0 1 110 1 113 1 11 47 2 52 2 72 2 74 2 91 2 92 2 93 2 102 2 111 2 112 2 114 64P0e7e64872ee2d9c1 0 6 0 1 46 1 67 1 76 1 84 1 85 1P0f0f126a51f78a7a 0 3 0 1 43 1 46 1P0f6f53b05cc7ad35 1 1 64 2 1 1 80 1 3 0 1 81 1 82 64P0fdcdb11ebc5b389 0 5 0 1 53 1 72 1 92 1 93 1P0fe0c532b67b2159 0 8 0 1 46 1 65 1 66 1 67 1 76 1 84 1 85 1P0feb61f5740d7658 1 1 32 3 0 1 81 1 84 1 11 37 2 47 2 51 2 53 2 62 2 63 2 64 2 73 2 82 2 83 2 85 64P1002b5b1885a7830 0 4 0 1 64 1 84 1 85 1P108e4047441bd830 1 1 16 3 1 1 35 1 85 1 9 47 1 49 1 50 1 66 1 67 1 68 1 77 1 86 1 87 16P10c48c6678d68707 0 7 0 1 47 1 72 1 93 1 102 1 110 1 111 1P10c6f1db3c9a4e55 0 7 0 1 48 1 62 1 75 1 84 1 92 1 93 1P11d336c01944c2ca 0 8 0 1 46 1 65 1 66 1 67 1 76 1 84 1 85 1P1216ec105577e837 1 1 16 2 1 1 85 1 9 47 1 49 1 50 1 66 1 67 1 68 1 77 1 86 1 87 16P12285f28a776c9ff 1 1 32 3 0 1 110 1 113 1 11 47 2 52 2 72 2 74 2 91 2 92 2 93 2 102 2 111 2 112 2 114 64P123bb76e9143b5fa 1 1 32 3 0 1 104 1 107 1 11 41 2 46 2 66 2 68 2 85 2 86 2 87 2 96 2 105 2 106 2 108 64P1318e013491e35a8 1 1 32 3 0 1 110 1 113 1 11 47 2 52 2 72 2 74 2 91 2 92 2 93 2 102 2 111 2 112 2 114 64P139e1ed1b03c5de8 1 2 16 2 0 1 86 1 16 2 1 1 85 1 2 87 1 88 1P13afb7bb6535410b 1 2 16 3 1 1 35 1 85 1 16 3 0 1 36 1 86 1 2 87 1 88 1P13c7c034f3b9acb9 1 1 32 3 1 1 105 1 108 1 11 42 2 47 2 67 2 69 2 86 2 87 2 88 2 97 2 106 2 107 2 109 64P13cab8ba004a134b 0 4 0 1 64 1 84 1 85 1P13e7eddb311e0812 1 2 8 2 0 1 126 1 8 2 49 1 127 1 2 128 1 129 1P13e8edbc76505536 0 6 0 1 46 1 67 1 76 1 84 1 85 1P140bd4d5917dc23b 1 1 16 3 1 1 35 1 85 1 9 47 1 49 1 50 1 66 1 67 1 68 1 77 1 86 1 87 16P14992e2fb73fb3a0 0 4 0 1 64 1 84 1 85 1P14efa9a2c86b9f70 0 6 0 1 46 1 67 1 76 1 84 1 85 1P158a8cbde582d4a9 1 1 16 3 0 1 93 1 94 1 4 47 1 92 1 95 1 96 16P15a3e75878ad740d 1 2 16 2 0 1 86 1 16 2 1 1 85 1 2 87 1 88 1P1650806b328dae45 0 6 0 1 46 1 67 1 76 1 84 1 85 1P1690bb91b77815d3 1 1 16 4 1 1 37 1 39 1 85 1 9 47 1 49 1 50 1 66 1 67 1 68 1 77 1 86 1 87 16P18535cbbf11a39fd 1 1 32 3 0 1 105 1 108 1 11 42 2 47 2 67 2 69 2 86 2 87 2 88 2 97 2 106 2 107 2 109 64P18e85b433b0db499 1 1 16 2 1 1 85 1 9 47 1 49 1 50 1 66 1 67 1 68 1 77 1 86 1 87 16P1910206498516f42 0 9 0 1 41 1 66 1 85 1 86 1 87 1 96 1 104 1 105 1P195520e0cc726242 0 6 0 1 57 1 58 1 84 1 104 1 105 1P195d81f4c1ef1641 0 5 0 1 32 1 64 1 84 1 85 1P19a982c23e2bafc2 0 6 0 1 72 1 93 1 102 1 110 1 111 1P1a2044dd5f0ec645 0 5 0 1 53 1 72 1 92 1 93 1P1adeb589d680dd54 0 6 0 1 46 1 67 1 76 1 84 1 85 1P1af0bba5751cce7a 0 8 0 1 46 1 65 1 66 1 67 1 76 1 84 1 85 1P1b20261d31aca15b 1 1 16 4 1 1 37 1 39 1 85 1 9 47 1 49 1 50 1 66 1 67 1 68 1 77 1 86 1 87 16P1b4c368e6d80b938 0 4 0 1 64 1 84 1 85 1P1b4d6f8ecbd65743 1 1 32 3 0 1 110 1 113 1 11 47 2 52 2 72 2 74 2 91 2 92 2 93 2 102 2 111 2 112 2 114 64P1b6ae581ddfd85f2 1 1 32 3 0 1 110 1 113 1 11 47 2 52 2 72 2 74 2 91 2 92 2 93 2 102 2 111 2 112 2 114 64P1bc7cf72ce525420 0 8 0 1 50 1 61 1 62 1 63 1 72 1 80 1 81 1P1c1ef8d963d8b2a6 1 1 16 2 1 1 85 1 9 47 1 49 1 50 1 66 1 67 1 68 1 77 1 86 1 87 16P1c3d90b1c7371313 0 6 0 1 46 1 67 1 76 1 84 1 85 1P1c827fa11eebf551 0 4 0 1 64 1 84 1 85 1P1cc76356996378e7 0 8 0 1 62 1 73 1 74 1 75 1 84 1 92 1 93 1P1d5c9ce031f02017 1 1 16 3 1 1 35 1 85 1 9 47 1 49 1 50 1 66 1 67 1 68 1 77 1 86 1 87 16P1dfaa64b0adf8cbd 1 1 16 3 0 1 93 1 94 1 4 47 1 92 1 95 1 96 16P1e3169e65ae816c1 1 1 16 4 1 1 37 1 39 1 85 1 9 47 1 49 1 50 1 66 1 67 1 68 1 77 1 86 1 87 16P1e757236ddb476fd 0 5 0 1 53 1 72 1 92 1 93 1P1ebdb57d57b525ad 1 1 16 2 1 1 85 1 9 47 1 49 1 50 1 66 1 67 1 68 1 77 1 86 1 87 16P1f5572021ca799a1 1 1 16 2 1 1 85 1 9 47 1 49 1 50 1 66 1 67 1 68 1 77 1 86 1 87 16P1fa72a6e531bfad0 1 2 16 3 1 1 35 1 85 1 16 3 0 1 36 1 86 1 2 87 1 88 1P202c04352395696b 1 1 16 3 0 1 106 1 107 1 10 47 1 67 1 69 1 86 1 87 1 88 1 97 1 105 1 108 1 109 16P2053207788bdc331 0 2 0 1 126 1P2091004764456983 1 1 64 2 0 1 80 1 3 2 1 81 1 82 64P216454af9c77b14e 0 4 0 1 64 1 84 1 85 1P2179acf526d68519 1 2 16 3 1 1 35 1 85 1 16 3 0 1 36 1 86 1 2 87 1 88 1P21b2cf77a11de76a 1 1 16 3 0 1 106 1 107 1 4 59 2 105 2 108 2 109 32P226f0ccf0aec32ec 0 6 0 1 46 1 67 1 76 1 84 1 85 1P22cd6e89ba58433c 0 5 0 1 32 1 64 1 84 1 85 1P238cd8a0583e0fb0 1 1 16 3 0 1 111 1 112 1 10 52 1 72 1 74 1 91 1 92 1 93 1 102 1 110 1 113 1 114 16P2393824aaa282da4 0 5 0 1 32 1 64 1 84 1 85 1P23b58ec26ec39c36 1 1 16 3 0 1 111 1 112 1 10 52 1 72 1 74 1 91 1 92 1 93 1 102 1 110 1 113 1 114 16P23f00d010c935315 1 1 64 2 9 1 104 1 3 0 1 105 1 106 64P241f73253f6f81e3 0 8 0 1 62 1 73 1 74 1 75 1 84 1 92 1 93 1P2475c4ae020f4a56 0 5 0 1 32 1 64 1 84 1 85 1P2514651135cd745b 0 8 0 1 62 1 73 1 74 1 75 1 84 1 92 1 93 1P258147a858da449e 1 1 32 3 1 1 105 1 108 1 11 42 2 47 2 67 2 69 2 86 2 87 2 88 2 97 2 106 2 107 2 109 64P26488798703557ab 0 4 0 16 3 16 84 16 85 16P2689da3687cadd2d 1 1 16 3 1 1 35 1 85 1 9 47 1 49 1 50 1 66 1 67 1 68 1 77 1 86 1 87 16P276abd161943beeb 0 8 0 1 46 1 65 1 66 1 67 1 76 1 84 1 85 1P28438c53642a3e74 0 7 0 1 47 1 72 1 93 1 102 1 110 1 111 1P28bb95cadd8a5674 0 5 0 1 53 1 72 1 92 1 93 1P294c311a507d8f53 1 1 16 3 0 1 105 1 106 1 10 46 1 66 1 68 1 85 1 86 1 87 1 96 1 104 1 107 1 108 16P294e0071282b0370 1 2 16 2 0 1 86 1 16 2 1 1 85 1 2 87 1 88 1P299fd8da5fbe9143 0 5 0 1 32 1 64 1 84 1 85 1P2a1a077802f52990 0 6 0 1 72 1 93 1 102 1 110 1 111 1P2a6a1b26d1486873 1 1 16 4 1 1 37 1 39 1 85 1 9 47 1 49 1 50 1 66 1 67 1 68 1 77 1 86 1 87 16P2ab7018983e3676c 0 8 0 1 62 1 73 1 74 1 75 1 84 1 92 1 93 1P2b510075073eb224 0 5 0 1 53 1 72 1 92 1 93 1P2b7677cf8528dd1f 1 2 16 3 1 1 35 1 85 1 16 3 0 1 36 1 86 1 2 87 1 88 1P2ba6c973e8fbd1c9 0 5 0 1 32 1 64 1 84 1 85 1P2bc09b3fca4651ab 0 8 0 1 46 1 65 1 66 1 67 1 76 1 84 1 85 1P2c1deb11692eed4e 0 4 0 1 64 1 84 1 85 1P2c3e4e764709c30d 1 1 32 3 1 1 105 1 108 1 11 42 2 47 2 67 2 69 2 86 2 87 2 88 2 97 2 106 2 107 2 109 64P2ccaffdba4f8781d 1 1 16 4 1 1 37 1 39 1 85 1 9 47 1 49 1 50 1 66 1 67 1 68 1 77 1 86 1 87 16P2cd89cce6e4b33dd 1 1 32 3 1 1 105 1 108 1 11 42 2 47 2 67 2 69 2 86 2 87 2 88 2 97 2 106 2 107 2 109 64P2cfebf57d26de877 0 5 0 1 41 1 60 1 80 1 81 1P2dd15b360fbf681b 1 1 16 3 0 1 106 1 107 1 10 47 1 67 1 69 1 86 1 87 1 88 1 97 1 105 1 108 1 109 16P2eb3dc078ee6af17 0 6 0 1 66 1 87 1 96 1 104 1 105 1P2ebc628785003f8a 0 5 0 1 53 1 72 1 92 1 93 1P2ed6ce69dd38bf94 0 6 0 1 72 1 93 1 102 1 110 1 111 1P2eda9b3aae94b574 1 1 32 3 0 1 126 1 129 1 11 63 2 68 2 88 2 90 2 107 2 108 2 109 2 118 2 127 2 128 2 130 64P2f4e8b0feedc6bd8 0 7 0 1 47 1 72 1 93 1 102 1 110 1 111 1P2fb4f67013a8cc3d 1 1 16 4 1 1 37 1 39 1 85 1 9 47 1 49 1 50 1 66 1 67 1 68 1 77 1 86 1 87 16P30fbecbf121852ad 1 2 16 3 1 1 35 1 85 1 16 3 0 1 36 1 86 1 2 87 1 88 1P324167d6a9822a47 0 8 0 1 46 1 65 1 66 1 67 1 76 1 84 1 85 1P3273b4ce887e88d3 0 6 0 1 46 1 67 1 76 1 84 1 85 1P32c6d8ef9ab3b54d 0 8 0 1 62 1 73 1 74 1 75 1 84 1 92 1 93 1P3345ba90bfaf159d 1 1 16 3 0 1 127 1 128 1 4 80 2 126 2 129 2 130 32P334bdcd97116f372 1 2 16 3 1 1 35 1 85 1 16 3 0 1 36 1 86 1 2 87 1 88 1P340e87d4a74acdfa 0 7 0 1 48 1 62 1 75 1 84 1 92 1 93 1P3488f4a6f882291a 1 1 16 4 1 1 37 1 39 1 85 1 9 47 1 49 1 50 1 66 1 67 1 68 1 77 1 86 1 87 16P34defcb442ce9d61 0 5 0 1 53 1 72 1 92 1 93 1P35d9ed0c41b31574 0 6 0 1 88 1 109 1 118 1 126 1 127 1P364cf18475900476 1 1 16 4 1 1 37 1 39 1 85 1 9 47 1 49 1 50 1 66 1 67 1 68 1 77 1 86 1 87 16P36dae0536cf3f1f4 0 3 0 1 40 1 42 1P3712ebef0d9cc1d4 0 8 0 1 46 1 65 1 66 1 67 1 76 1 84 1 85 1P3728d5fc13ebf94d 0 5 0 1 32 1 64 1 84 1 85 1P375349989bcb1b0d 0 4 0 8 48 8 126 8 127 8P379a70885cb90e7c 1 1 16 3 0 1 111 1 112 1 10 52 1 72 1 74 1 91 1 92 1 93 1 102 1 110 1 113 1 114 16P37d3a215d379cb72 0 8 0 1 62 1 73 1 74 1 75 1 84 1 92 1 93 1P37e47a0e91377a59 1 1 16 2 0 1 84 1 3 4 1 85 1 86 16P3961bb4fc08f22e9 0 5 0 1 32 1 64 1 84 1 85 1P399976cb314e99b7 0 6 0 1 35 1 41 1 60 1 80 1 81 1P3a2c3bb833f5cdfa 1 1 64 2 47 1 81 1 3 0 1 80 1 82 64P3afed6b2e8916aef 0 5 0 1 53 1 72 1 92 1 93 1P3b2dc25b0af8f280 1 2 16 2 0 1 86 1 16 2 1 1 85 1 2 87 1 88 1P3bca4d5eb62e58ab 0 4 0 1 64 1 84 1 85 1P3be2e0e07760c35f 1 1 16 3 1 1 35 1 85 1 9 47 1 49 1 50 1 66 1 67 1 68 1 77 1 86 1 87 16P3c04253e6cedbf67 1 1 16 2 1 1 85 1 9 47 1 49 1 50 1 66 1 67 1 68 1 77 1 86 1 87 16P3cad1965e668e40f 0 5 0 1 32 1 64 1 84 1 85 1P3d834e00d949c9ea 0 8 0 1 46 1 65 1 66 1 67 1 76 1 84 1 85 1P3df4073f09e7dd87 1 1 16 3 0 1 82 1 83 1 10 47 1 51 1 53 1 62 1 63 1 64 1 73 1 81 1 84 1 85 16P3e2b34e64e06bafd 1 1 16 4 1 1 37 1 39 1 85 1 9 47 1 49 1 50 1 66 1 67 1 68 1 77 1 86 1 87 16P3ed8ee8cf2c8db21 1 1 64 2 0 1 104 1 3 6 1 105 1 106 64P3ef4e51e7ef1bc3a 0 5 0 1 53 1 72 1 92 1 93 1P3f8eb6cd33891f6c 0 9 0 1 36 1 50 1 61 1 62 1 63 1 72 1 80 1 81 1P3f93f04d5db9c071 0 6 0 1 39 1 58 1 84 1 104 1 105 1P3f987e224fb4d639 0 8 0 1 62 1 73 1 74 1 75 1 84 1 92 1 93 1P3fb28022aac4cd39 0 8 0 1 46 1 65 1 66 1 67 1 76 1 84 1 85 1P3fbcaf3e71d0e7ab 0 6 0 1 72 1 93 1 102 1 110 1 111 1P3fdae4f5adad4c6f 0 5 0 1 53 1 72 1 92 1 93 1N00054e12ec3a9689N0058b0752d05bb95N00949081ba7f9762N00dee43153c8bf44N01487d3bd5758b37N01f0bfd96a889948N0204362e5a5c00e9N024ef7f1128db5e0N02aa45ab724f4810N02cc948e602ddb08N031f4ef79d71029bN0355d1c1bf73146fN035d8f85db0ac4e4N0367f6c76c79c367N03d93bf1bf33daf6N03f53a9515ca6917N0552b57e2c730f27N0618c761b606be11N062bd1716e6c0720N065e04c0ddcb3e60N0660c1fece28b6bfN06911fc82c3903f5N06a0eae6f7ec66aeN06c60e945fdd7dbfN06e3c3fbb53ca1c5N070ba56c7a3d6764N0730a5b1d111e622N07ad08b66536b777N07e59bf3d5f057f0N08298a161b5d1512N085e0fa8ecf5c60aN0864f94249f250e6N08a6cf1706df1c56N08bee128431185e1N08c054d76160ea80N09b6275af1516a5cN09eb6f259dec8af2N0a1179c65890ad1dN0b04fa232a3abec5N0b62b02120363b65N0b97fdf7c6f63ebaN0c4754f9fb94c92eN0c49adfe36362b12N0c6082a7b98d5217N0d6c2777ef9e68ddN0d76eac70db41670N0dd1e05eea120c60N0e29750f547e5841N0e7f467e57b9806dN0ed3af4cd481b3f0N0f37dd518b886bbeN0f6fcfde99c9e702N0fdae6116a5e7eb8N11950fe6ad46ac90N120b4e48ba836d78N122cf0bdc14e6f9eN124deed4e27c401fN12731df69efc5f9aN12af2dd5cb0b46d1N132989e8ee2d63cbN1396b9e9f3ac83ffN1461d1d66095eecfN1465d47ebb7ecaa4N148fb989953a80d8N1523eaee78f8f8a6N153c4d399190bc63N15526447e36e9cd2N168a10eb42b95376N169530775012abf4N169f24fe1531ba01N1765eac7ad846cf3N17b813ee9b202b16N19376672f86ca691N19e3ddc1176ff818N1b13089c23e8bf72N1ba875b3345452faN1c145fa17bc46d0aN1c2e93d58c94a582N1c6c13117ff3a601N1cd4bc1122ae83b9N1cdbe2c94d49e1eeN1d38b5f5d6200ac7N1d689051cdc2bd4aN1dcf172ca836c6e6N1dee349c8bd4113fN1f02a0e1382f7648N1f18f9350ca54623N1f257f7ca033a160N1f4476368ca78f35N1f44bfb6ae755441N1ff53b99cece302dN20387fcac2d72146N2064207c23b004e9N20984f936cd7e592N20ae99ef1cb09c98N20bf5dc67bfd15feN20c46f4b829bc626N20fb746ab72a391bN211b1ca4ed3550bbN217f787a1eaf8b55N21f1039b06733b9fN21f5d4754ba99845N2233fda4c78f947fN22ac1ebd566e0ec6N22da3bb41baa4866N22ff927ede40104aN233e9c8f872a56efN2465fd329dd407e2N24dc2aa533d409c0N24de1df36594e1bfN25477ff50e5b0e12N254bae1a296844eeN2554bc691ad8f10aN2563a2f381c50880N257d01b4d0977240N259919b2aee0b75eN25cc04c0839d0347N25f3eca1c8646f51N2679c8e20a06d586N26b2d87f5eff3f74N26ea119dc48df5dcN27b914cc84375c80N2833a6f41a10015dN2856a06198d59f30N2939438e7ffce18aN297f16e452ca5a8bN29bf0b45d2cc5d95N2a0c406417822b20N2ae9104f6265e912N2b0877eab2f3f63cN2b3decc066ecda61N2c494dfccb5303dfN2c4ed887d6369404N2c7ed505318ce79dN2cd0ca893bbf4587N2d813c72def44f60N2ea3bcd47a6ffb42N2f2c26fb46bc583fN2f51385a945b0641N306668be2607193cN306e94b595e9c1d2N30a9a0817eefca4bN30bfcb3d7adf3f57N310d484405c2feb9N320143c8cd39b6dbN320b6c95e29c6622N32fb49955d3a8f68N33411e5cedadbd0eN3412830433c8c4aeN34be67314c23fe18N35ccdce6cbbf4df6N36a7fae34dda9eb7N374dc2a7dd2a8da7N37602723b1ffe18dN383f0368304d8351N385f454e873b72dbN38cf50a631e0c3baN39ccfa1d5687f6feN3a1bc865787e2fd8N3a660eb31ee072b5N3abf507a3df6d2e1N3acca0ea172ad382N3b66e34e947df670N3be16a94bac52078N3c7cfe54ebf1b0feN3ca936667800d89cN3d35d8ea3f7212e0N3d66908de26f730fN3ddde1be17527c6bN3df1dd872389ac76N3ea53622848e7bccN3f5dbc75eceb6376"%lxh.
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
Ltac2 gd_tbl_A_ecp_check_pubkey_c24 () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Spec.RepEcp.modp_ent"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Lib.HeapIface.blk"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Spec.RepEcp.ecp_grp"; "OSSVerify.KrLib.Spec.RepEcp.ecp_group_at"; "OSSVerify.KrLib.A.AImg.asegs"; "OSSVerify.KrLib.Spec.MpiVal.mpd"; "Stdlib.Lists.List.In"; "OSSVerify.KrLib.Spec.RepEcp.grp_mpds"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Spec.Rep.limb_own"; "OSSVerify.KrLib.Spec.MpiVal.md_own"; "OSSVerify.KrLib.Spec.Rep.LHeap"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Spec.MpiVal.md_p"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Spec.MpiVal.md_n"; "OSSVerify.KrLib.Spec.RepEcp.ecp_pt"; "OSSVerify.KrLib.Spec.RepEcp.ecp_point_at"; "OSSVerify.KrLib.Spec.RepEcp.pt_mpds"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.of_nat"; "OSSVerify.KrLib.Lib.Cells.cells_size"; "OSSVerify.KrLib.Lib.Mem.wa"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.sgn"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Spec.RepEcp.g_h"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Spec.RepEcp.pt_X"; "OSSVerify.KrLib.Spec.RepEcp.g_G"; "OSSVerify.KrLib.Spec.RepEcp.pt_Y"; "OSSVerify.KrLib.Spec.MpiVal.mpd_at"; "OSSVerify.KrLib.Lib.HeapIface.client_range"; "OSSVerify.KrLib.LibA.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.LibA.ARt.fdata"; "OSSVerify.KrLib.Spec.MpiVal.md_addr"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.A.A_ecp_stmtA.A_MUL_COUNT"; "OSSVerify.KrLib.LibA.AShadow.aobj"; "OSSVerify.KrLib.LibA.ARt.arl_AL"; "OSSVerify.KrLib.LibA.ARt.hcs"; "OSSVerify.KrLib.A.A_mpi_stmtA_sz.mpd_imgA"; "OSSVerify.KrLib.A.A_alloc_lib.uw_obj"; "OSSVerify.KrLib.Lib.HeapIface.alloc_ceiling"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_img_hi"; "OSSVerify.KrLib.Spec.RepEcp.mpdr_at"; "CK.Call.ck_op"; "OSSVerify.KrLib.Spec.Rep.LStatic"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.LibA.ARt.HST"; "OSSVerify.KrLib.LibA.ARt.presA"; "OSSVerify.KrLib.LibA.ARt.arl_stklo"; "OSSVerify.KrLib.LibA.ARt.hstkhi"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.ivl"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.LibA.ARt.HM"; "OSSVerify.KrLib.Spec.RepEcp.grp_head_cells"; "OSSVerify.KrLib.Spec.Rep.mpi_cells"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Spec.MpiVal.md_sg"; "OSSVerify.KrLib.Spec.MpiVal.md_pad"; "OSSVerify.KrLib.Spec.RepEcp.grp_tail_cells"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "OSSVerify.KrLib.Spec.RepEcp.g_P"; "OSSVerify.KrLib.A.A_ecp_stmtA.mm_PHIn"; "OSSVerify.KrLib.A.A_ecp_stmtA.mm_FRn"; "OSSVerify.KrLib.A.A_ecp_stmtA.sw_rhs_PHIn"; "OSSVerify.KrLib.A.A_ecp_stmtA.sw_rhs_FRn"; "OSSVerify.KrLib.LibA.ARt.fr_charge"; "OSSVerify.KrLib.A.A_mpi_stmtA.calls_FR"; "OSSVerify.KrLib.A.A_mpi_stmtA.grow_PHI"; "OSSVerify.KrLib.A.A_mpi_stmtA_sz.intop_PHIn"; "OSSVerify.KrLib.A.A_mpi_stmtA_sz.intop_FRn"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.LibA.AEvtA.evtA"; "CK.Call.S1P"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.A.A_ecp_stmtA.A_ECP_CHECK_PUBKEY"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "OSSVerify.KrLib.Lib.MState.ret_pc"; "OSSVerify.KrLib.LibA.ARt.presW"; "OSSVerify.KrLib.LibA.ARt.htop"; "OSSVerify.KrLib.LibA.ARt.hflag"; "OSSVerify.KrLib.LibA.ARt.havol"; "OSSVerify.KrLib.LibA.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "OSSVerify.KrLib.LibA.ARt.HK"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.LibA.ARt.fresh_apart"; "OSSVerify.KrLib.LibA.ALazy.crange"; "OSSVerify.KrLib.Lib.Cells.C8"; "Stdlib.ZArith.BinInt.Z.shiftr"; "OSSVerify.KrLib.LibA.ALazy.al_sb"; "OSSVerify.KrLib.Lib.Cells.C1"; "CK.Call.EPOST"; "OSSVerify.KrLib.A.A_ecp_stmtA.ecp_check_postA"; "OSSVerify.KrLib.A.A_ecp_stmtA.check_pubkey_PHIn"; "OSSVerify.KrLib.A.A_ecp_stmtA.check_pubkey_FRn"; "Stdlib.ZArith.BinInt.Z.opp"; "OSSVerify.KrLib.LibA.AEvtA.aevtA"; "OSSVerify.KrLib.LibA.ARt.KF"; "CK.Call.CK_POST"; "OSSVerify.KrLib.P.P_ecp_check_pubkey.bad_point_ok"; "A_BAD_POINTS"; "OSSVerify.KrLib.A.A_mpi_stmtA_sz.arl_need_ecp"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_lo"; "OSSVerify.KrLib.Lib.HeapIface.hl_data_hi"; "OSSVerify.KrLib.A.A_ecp_journey.ejtmp"; "OSSVerify.KrLib.Spec.MpiVal.mkMPD"; "OSSVerify.KrLib.Spec.Rep.LNull"; "OSSVerify.KrLib.A.A_ecp_journey.ej_ext"; "OSSVerify.KrLib.A.A_ecp_journey.EJ"; "OSSVerify.KrLib.A.A_ecp_pair.EPI"; "OSSVerify.KrLib.LibA.ARt.AVOL_CALL"; "OSSVerify.KrLib.A.A_ecp_one.e1_rdable"; "OSSVerify.KrLib.A.A_ecp_one.E1I"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Peano.lt"; "Stdlib.ZArith.BinInt.Z.to_nat"; "OSSVerify.KrLib.Spec.MpiVal.mpd_val"; "OSSVerify.KrLib.LibA.AEvtS.aevtS"; "LinuxProcessSemantics.LinuxProcessSem.Run.mkCfg"; "OSSVerify.KrLib.LibA.ARt.art_layout"; "OSSVerify.KrLib.LibA.ARt.artA"; "OSSVerify.KrLib.A.AImg.asan_img_ok"; "OSSVerify.KrLib.LibA.ARt.arl_uar_got"; "A_UAR_GOT_CK"; "OSSVerify.KrLib.LibA.ARt.arl_smalloc"; "A_SMALLOC_1_CK"; "OSSVerify.KrLib.LibA.ARt.arl_need_smalloc"; "OSSVerify.KrLib.A.A_mpi_read_binary_stmt.arl_need_rt"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.bool"; "OSSVerify.KrLib.Lib.Mem.ro_addr"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.LibA.ARt.arl_rtc"; "OSSVerify.KrLib.A.AImgRT.asan_rtc"; "OSSVerify.KrLib.A.A_ecp_stmtA.ecp_mul_mod_stmtA"; "OSSVerify.KrLib.A.A_ecp_stmtA.A_ECP_MUL_MOD"; "OSSVerify.KrLib.A.A_ecp_stmtA.ecp_sw_rhs_stmtA"; "OSSVerify.KrLib.A.A_ecp_stmtA.A_ECP_SW_RHS"; "OSSVerify.KrLib.A.A_mpi_copy_c24.mpi_copy_stmtA_c"; "OSSVerify.KrLib.A.A_mpi_stmtA.A_MPI_COPY"; "OSSVerify.KrLib.A.A_mpi_stmtA_ng_sz.mpi_sub_mpi_ng_stmtA_sz"; "OSSVerify.KrLib.A.A_mpi_stmtA.A_MPI_SUB_MPI"; "OSSVerify.KrLib.A.A_mpi_stmtA_sz.mpi_add_int_stmtA_sz"; "OSSVerify.KrLib.A.A_mpi_stmtA.A_MPI_ADD_INT"; "OSSVerify.KrLib.A.A_mpi_free.mpi_free_stmtA"; "OSSVerify.KrLib.A.A_mpi_stmtA.A_MPI_FREE"; "OSSVerify.KrLib.A.A_ecp_stmtA.ecp_check_pubkey_stmtA"].


Definition A_SMALLOC_1_CK : Z := 0x52af8.          (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_UAR_GOT_CK : Z := 0x0f2ae8.           (* [comment removed for export] *) (* [comment removed for export] *)
Definition A_BAD_POINTS : Z := 0x0ef080.           (* [comment removed for export] *) (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ck_group_LB_sub : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "PMT,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PLB,(0.$4.)PLB',(0.(5.$6.$6.))PG,$6.Pg,$7.P,(8.$9.R6.R5.R4.R2.R1.)P,Pe,$:.P,(;.$:.R1.(<.R3.))P,(=.$>.(?.R2.)$10.)(;.(5.$6.$6.)(11.$6.$6.(12.R3.)(13.+4.(14.R3.)))R7.)(8.$9.R8.R7.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros MT m LB LB' G g HG HB.
  flat constr:(HG) 13%nat. flclear HG. intros HD AL POS EP EA EB EN MP MA MB FLt1 MN REST. flat constr:(FLt1) 6%nat. flclear FLt1. intros EX EY EZ MX MY MZ.
  pose proof (fun e He Hm => mpdr_at_LB_one asegs m LB LB' e Hm (HB e He)) as RB.
  unfold grp_mpds, pt_mpds in RB. cbn [app In] in RB.
  refine (conj HD (conj AL (conj POS (conj EP (conj EA (conj EB (conj EN _))))))).
  split; [apply RB; [tauto| exact MP]|]. split; [apply RB; [tauto| exact MA]|]. split; [apply RB; [tauto| exact MB]|].
  split; [refine (conj EX (conj EY (conj EZ _))); split; [apply RB; [tauto| exact MX]| split; [apply RB; [tauto| exact MY]| apply RB; [tauto| exact MZ]]]|].
  split; [apply RB; [tauto| exact MN]| exact REST].
Qed.
Lemma ck_point_LB_sub : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Pm,P,(2.&40.)(3.(2.&8.))PLB,(0.$4.)PLB',(0.(5.$6.$6.))PQ,$6.Pp,$15.P,(16.$9.R5.R4.R2.R1.)P,Pe,$:.P,(;.$:.R1.(17.R3.))P,(=.$>.(?.R2.)$10.)(;.(5.$6.$6.)(11.$6.$6.(12.R3.)(13.+4.(14.R3.)))R7.)(16.$9.R7.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros m LB LB' Q p (EX & EY & EZ & MX & MY & MZ) HB.
  pose proof (fun e He Hm => mpdr_at_LB_one asegs m LB LB' e Hm (HB e He)) as RB.
  unfold pt_mpds in RB. cbn [In] in RB.
  refine (conj EX (conj EY (conj EZ _))); split; [apply RB; [tauto| exact MX]| split; [apply RB; [tauto| exact MY]| apply RB; [tauto| exact MZ]]].
Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L38465438810.1500000=S2cs3LEN1i2Hi". (* [comment removed for export] *)
Lemma ck_rw_cells_same : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Pma,P,(2.&40.)(3.(2.&8.))Pmb,P,(2.&40.)(3.(2.&8.))PA,$6.Pcs,(0.$18.)P,(19.$9.R4.R2.R1.)P,Pi,$6.P,(1:.(1;.=R1.)(1<.R1.(1=.(1>.R3.))))(=.(3.(2.&8.))A1.R6.(1?.(20.R5.R2.))A1.R7.(1?.(20.R5.R2.)))(19.$9.R5.R4.R3.)")
(* [comment removed for export] *).
Proof.
  intros ma mb A cs [[WF (B0 & B1 & BR)] (W0 & W1 & WR)] EQ.
  pose proof (cells_bytes_length cs WF) as LEN.
  split.
  - split; [exact WF|]. split; [exact B0|]. split; [exact B1|].
    intros i Hi. rewrite <- (BR i Hi). unfold mrd. rewrite (EQ (Z.of_nat i)) by (rewrite LEN in Hi; lia). reflexivity.
  - split; [exact W0|]. split; [exact W1|]. intros i Hi. specialize (WR i Hi). unfold wview in *. rewrite (EQ i Hi). exact WR.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L4338898938.3000005S1a1b". (* [comment removed for export] *)
Lemma sgn3 : forall a b, Z.sgn (a - b) = -1 \/ Z.sgn (a - b) = 0 \/ Z.sgn (a - b) = 1.
Proof. intros a b. pose proof (Z.sgn_spec (a - b)). clear - H. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac ck_s3_lit z :=
  lazymatch goal with |- _ (MS ?RR _ _ _ _ _ _) => let v0 := getx RR 19%positive in replace v0 with (Z_to_bv 64 z) by (apply bv_eq; vm_compute; reflexivity) end.
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L45310031223.3000005S1a1b". (* [comment removed for export] *)
Lemma sgn_ord : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Pa,$6.Pb,$6.(21.(1:.(=.$6.(22.(23.R2.R1.))-1.)(1<.R2.R1.))(21.(1:.(=.$6.(22.(23.R2.R1.))=)(=.$6.R2.R1.))(1:.(=.$6.(22.(23.R2.R1.))+1.)(1<.R1.R2.))))")
(* [comment removed for export] *).
Proof. intros a b. pose proof (Z.sgn_spec (a - b)) as H. clear - H. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Section CK.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT_CK.
  Hypothesis SM1 : arl_smalloc R 1 = A_SMALLOC_1_CK.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NEEDR : 0 <= arl_need_rt R.
  Hypothesis HND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis ROIMG : forall a, ro_addr asegs (wa a) = true -> 0 <= a < 2^64 -> hl_img_lo L <= a < hl_img_hi L.
  Hypothesis RTCL : forall m, arl_rtc R m -> asan_rtc m.
  Variable MT : list modp_ent.
  Local Notation MC := A_MUL_COUNT.
  Local Notation BP := A_BAD_POINTS.
  Hypothesis HMM : ecp_mul_mod_stmtA asegs R HIA MT A_ECP_MUL_MOD MC.
  Hypothesis HSR : ecp_sw_rhs_stmtA asegs R HIA MT A_ECP_SW_RHS MC.
  Hypothesis HCOPY : mpi_copy_stmtA_c asegs R HIA A_MPI_COPY.
  Hypothesis HSUBNG : mpi_sub_mpi_ng_stmtA_sz asegs R HIA A_MPI_SUB_MPI.
  Hypothesis HADDI : mpi_add_int_stmtA_sz asegs R HIA A_MPI_ADD_INT.
  Hypothesis HFREE : mpi_free_stmtA asegs R HIA A_MPI_FREE.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (G Q : Z) (g : ecp_grp) (p : ecp_pt) (cnt : word) (bp1 bp2 : mpd) (N lo d slo : Z).
  Hypothesis HH : HM asegs R HIA h LB LF m.
  Hypothesis LFB : (length LF + 3 <= 512)%nat.
  Hypothesis GAT : ecp_group_at asegs MT m LB G g.
  Hypothesis GKIND : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "(21.(1:.(=.$6.(24.Vg,)+1.)(1:.(25.(=.$6.(12.(26.(27.Vg,)))=))(25.(=.$6.(12.(28.(27.Vg,)))=))))(1:.(=.$6.(24.Vg,)+2.)(=.$6.(12.(28.(27.Vg,)))=)))")
(* [comment removed for export] *).
  Hypothesis GPS : md_sg (g_P g) = 1.
  Hypothesis SGA : md_sg (g_A g) = 1.
  Hypothesis SGB : md_sg (g_B g) = 1.
  Hypothesis VP : 1 <= mpd_val (g_P g).
  Hypothesis GIMG : grp_imgA g.
  Hypothesis NLE : grp_nle g N.
  Hypothesis GCR : client_range L (LB ++ fdata LF) lo G 192.
  Hypothesis GSP : G + 192 <= lo \/ bv_unsigned sp <= G.
  Hypothesis GMC : MC + 8 <= G \/ G + 192 <= MC.
  Hypothesis GOB : aobj asegs AL CS m G 192.
  Hypothesis GUW : uw_obj R G 192 d.
  Hypothesis PAT : ecp_point_at asegs m LB Q p.
  Hypothesis PFREE : pt_freeable p.
  Hypothesis PSG : Forall (fun e => md_sg e = 1 \/ md_sg e = -1) (pt_mpds p).
  Hypothesis PNLE : Forall (fun e => md_n e <= N) (pt_mpds p).
  Hypothesis QCR : client_range L (LB ++ fdata LF) lo Q 48.
  Hypothesis QSP : Q + 48 <= lo \/ bv_unsigned sp <= Q.
  Hypothesis QMC : MC + 8 <= Q \/ Q + 48 <= MC.
  Hypothesis QOB : aobj asegs AL CS m Q 48.
  Hypothesis QUW : uw_obj R Q 48 d.
  Hypothesis MC0 : rw_cells asegs m MC [C8 cnt].
  Hypothesis MCOK : mc_okA R MC.
  Hypothesis BP1 : bad_point_ok asegs m LB BP bp1.
  Hypothesis BP2 : bad_point_ok asegs m LB (BP + 32) bp2.
  Hypothesis BI1 : mpd_imgA bp1.
  Hypothesis BI2 : mpd_imgA bp2.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 976 - arl_need_ecp R.
  Hypothesis SSH : sshad asegs AL m slo (bv_unsigned sp).
  Hypothesis SLO1 : arl_stklo R <= slo.
  Hypothesis SLO3 : slo <= lo.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis RAE : bv_unsigned ra mod 2 = 0.
  Hypothesis BUD : havol asegs R HIA h + check_pubkey_PHIn N <= AVOL_MAX.
  Hypothesis UW : uwc asegs m (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d.
  Hypothesis BUDF : hfr asegs R HIA h + check_pubkey_FRn N d <= FR_MAX.
  Hypothesis C24H : cnt24 LB + C24_ECP_CHECK_PUBKEY <= C24MAX.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT_CK in UARG; unfold A_SMALLOC_1_CK in SM1;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (arl_need_ecp_rt R) as NER; pose proof (arl_need_ecp_smalloc R) as NES;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Notation b8 x := (C1 (Z_to_bv 8 x)).
  Local Notation FSHP := [b8 241; b8 241; b8 241; b8 241; b8 248; b8 248; b8 242; b8 242; b8 248; b8 248; b8 242; b8 242; b8 248; b8 248; b8 243; b8 243].
  Local Notation FSHSW := [b8 241; b8 241; b8 241; b8 241; b8 0; b8 0; b8 242; b8 242; b8 0; b8 0; b8 242; b8 242; b8 248; b8 248; b8 243; b8 243].
  Local Notation FSHMX := [b8 241; b8 241; b8 241; b8 241; b8 248; b8 248; b8 242; b8 242; b8 248; b8 248; b8 242; b8 242; b8 0; b8 0; b8 243; b8 243].
  Local Notation SAVEL := [C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Local Notation dP := (g_P g).
  (* [comment removed for export] *)
  Definition ck_op (e : mpd) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "(1:.(29.$9.Vm,VLB,O1.)(1:.(2:.(2;.VR,)(2<.$4.VLB,(2=.VLF,))Vlo,(2>.O1.)+10.)(1:.(21.(1;.(20.(2>.O1.)+10.)Vlo,)(1;.(2?.&40.Vsp,)(2>.O1.)))(1:.(21.(1;.(20.$30.+8.)(2>.O1.))(1;.(20.(2>.O1.)+10.)$30.))(1:.(31.$9.(32.VR,)(33.$9.VR,VHIA,Vh,)Vm,(2>.O1.)+10.)(1:.(34.O1.)(1:.(35.VR,(2>.O1.)+10.Vd,)P,(=.$>.(?.O1.)$10.)(1:.(1;.+1.(14.O1.))(1:.(;.(5.$6.$6.)(11.$6.$6.(12.O1.)(13.+4.(14.O1.)))VLB,)(1:.(1<.=(12.O1.))(1:.(1;.(20.(12.O1.)(13.+4.(14.O1.)))(36.(2;.VR,)))(21.(1;.(20.(12.O1.)(13.+4.(14.O1.)))(37.(2;.VR,)))(1;.(38.(2;.VR,))(12.O1.))))))))))))))")
(* [comment removed for export] *).

  Lemma ck_blk : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Pe,$:.P,(39.$9.Vm,VLB,R1.)P,(=.$>.(?.R2.)$10.)(1:.(1;.+1.(14.R3.))(1:.(;.(5.$6.$6.)(11.$6.$6.(12.R3.)(13.+4.(14.R3.)))VLB,)(1:.(1<.=(12.R3.))(1:.(1;.(20.(12.R3.)(13.+4.(14.R3.)))(36.(2;.VR,)))(21.(1;.(20.(12.R3.)(13.+4.(14.R3.)))(37.(2;.VR,)))(1;.(38.(2;.VR,))(12.R3.)))))))")
(* [comment removed for export] *).
  Proof.
    intros e (_ & _ & _ & _ & _ & EOW) EO. rewrite EO in EOW. flat constr:(EOW) 3%nat. flclear EOW. intros K1 K2 _.
    flat constr:((hm_apart asegs R HIA h LB LF m HH)) 2%nat. intros HF _. rewrite Forall_forall in HF.
    destruct (HF _ ltac:(apply in_app_iff; left; exact K2)) as (B0 & _ & B2 & B3). cbn [fst snd] in B0, B2, B3.
    split; [exact K1|]. split; [exact K2|]. split; [exact B0|]. split; [exact B2| exact B3].
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0>L11560304158.1L11823214551.3L22286003249.5L22397150714.5L27822275849.6L34152658942.0L51070401118.0L51167666686.0L54613150751.4L65703549191.300000300>00N00^01301401501601E01PS1QS1Q3off3OFFS1Q3off3OFF1a2HaS1R1Q3off3OFF2U1S2sp1Q2lo3QSP3off3OFFSSSS1Q3QMC3off3OFFS1Q3off3OFF". (* [comment removed for export] *)
  Lemma ck_op_pt : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Pe,$:.P,(;.$:.R1.(17.Vp,))(1:.(3:.R2.)(1:.(25.(=.$>.(?.R2.)$3;.))(1:.(1;.(14.R2.)VN,)(3<.$6.Loff,$6.(1:.(=.$6.(2>.R3.)(20.VQ,R1.))(1:.(1;.=R1.)(1;.R1.+20.)))))))")
(* [comment removed for export] *).
  Proof.
    intros e He.
    assert (SGe : md_sg e = 1 \/ md_sg e = -1) by (rewrite Forall_forall in PSG; exact (PSG e He)).
    assert (NSe : md_own e <> LStatic) by (unfold pt_freeable in PFREE; rewrite Forall_forall in PFREE; exact (PFREE e He)).
    assert (NNe : md_n e <= N) by (rewrite Forall_forall in PNLE; exact (PNLE e He)).
    flat constr:(PAT) 6%nat. intros EX EY EZ MX MY MZ.
    assert (K : exists off, md_addr e = Q + off /\ 0 <= off <= 32 /\ mpdr_at asegs m LB e).
    { unfold pt_mpds in He. cbn [In] in He. destruct He as [<-|[<-|[<-|[]]]];
        [exists 0; split; [rewrite EX; clear; lia| split; [clear; lia| exact MX]]
        | exists 16; split; [exact EY| split; [clear; lia| exact MY]]
        | exists 32; split; [exact EZ| split; [clear; lia| exact MZ]]]. }
    flat constr:(K) 4%nat. flclear K. intros off EA OFF ME.
    split; [| split; [exact NSe| split; [exact NNe| exists off; split; [exact EA| exact OFF]]]].
    unfold ck_op. rewrite EA.
    split; [split; [exact ME| exact SGe]|].
    split; [intros a Ha; apply QCR; clear - Ha OFF; lia|].
    split; [clear - QSP OFF; lia|]. split; [clear - QMC OFF; lia|].
    split; [eapply aobj_sub; [exact QOB| clear - OFF; lia| clear - OFF; lia]|].
    split; [intros ES; exfalso; exact (NSe ES)|].
    split; [destruct QUW as [[U1 U2]|U28]; [left; split; [clear - U1 OFF; lia| exact U2]| right; exact U28]|].
    exact (ck_blk e ME).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma ck_P_own : md_own dP <> LHeap.
  Proof.
    flat constr:(GAT) 14%nat. intros _ _ _ _ _ _ _ _ _ _ _ _ _ REST.
    flat constr:(REST) 13%nat. flclear REST. intros _ _ _ _ _ _ _ _ _ _ _ KEPT _.
    unfold grp_kept_mpds in KEPT. rewrite Forall_forall in KEPT. apply KEPT.
    destruct GKIND as [(E & _)|(E & _)]; rewrite E; cbn [Z.eqb Pos.eqb]; [unfold grp_mpds; cbn; left; reflexivity| left; reflexivity].
  Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L23661207263.4L48815712669.3L52314013762.1L58759752384.2L59447693810.3L62065999094.100000=00E00H00O00W00ZS2sp1G2lo3GSPS1G1a2HaS1GS1G3GMCS1R1G2U1S1G". (* [comment removed for export] *)
  Lemma ck_op_P : ck_op dP /\ md_addr dP = G + 8.
  Proof.
    flat constr:(GAT) 9%nat. intros HD GAL POS EP EA EB EN MP _.
    assert (He : In dP (grp_mpds g)) by (unfold grp_mpds; cbn; left; reflexivity).
    split; [| exact EP]. unfold ck_op. rewrite EP.
    split; [split; [exact MP| left; exact GPS]|].
    split; [intros a Ha; apply GCR; clear - Ha; lia|].
    split; [clear - GSP; lia|]. split; [clear - GMC; lia|].
    split; [eapply aobj_sub; [exact GOB| clear; lia| clear; lia]|].
    split; [unfold grp_imgA in GIMG; rewrite Forall_forall in GIMG; exact (GIMG dP He)|].
    split; [destruct GUW as [[U1 U2]|U28]; [left; split; [clear - U1; lia| exact U2]| right; exact U28]|].
    intros EO. exfalso. exact (ck_P_own EO).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0090>L14714406535.1L18545962062.6L31102187327.1L50790761713.7L52618119093.5L59237492752.6L59239732521.7L59310643402.3L59315317366.600000300I00L00g01401G01_01i028S1eS2sp2lo1e3SEP3SPc4HSPcS1eS1R5NEEDR2sp2lo3LOS3SLO3NERS2sp1e1K1a2HaS1R2lo3LOS1e3ALO2B2S1R2lo3LOS1e3ALO3ACL3IHIS1e2N13N0'S2lo1e1K1a2Ha1S". (* [comment removed for export] *)
  Lemma ck_op_at : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Pe,$:.P,(3:.R1.)Ph1,(3=.$9.VR,VHIA,)PLFx,(0.$4.)Pmk,P,(2.&40.)(3.(2.&8.))PSPc,$6.P,(3>.$9.VR,VLB,VLF,(2?.&40.Vsp,)(3?.VR,)(40.$9.VR,VHIA,Vh,)(41.$42.)Vm,R2.)P,(43.$9.R3.)P,(44.$9.VR,VHIA,R6.VLB,R5.R4.)P,(=.P,$6.Sp(33.$9.VR,VHIA,R7.)(33.$9.VR,VHIA,Vh,))P,(1;.R5.(2?.&40.Vsp,))(1:.(29.$9.R7.VLB,R;.)(1:.(31.$9.(32.VR,)(33.$9.VR,VHIA,Vh,)R7.(2>.R;.)+10.)(1:.P,(1;.+1.(14.R;.))(31.$9.(32.VR,)(33.$9.VR,VHIA,Vh,)R8.(12.R<.)(13.+4.(14.R<.)))(1:.P,(=.$>.(?.R;.)$10.)(1<.=(12.R<.))(1:.(21.(1;.(20.(2>.R;.)+10.)Vlo,)(1;.R6.(2>.R;.)))P,(1;.+1.(14.R;.))(21.(1;.(20.(12.R<.)(13.+4.(14.R<.)))Vlo,)(1;.R7.(12.R<.))))))))")
(* [comment removed for export] *).
  Proof.
    intros e (ME & CR & SEP & MCs & OB & IM & UWe & BLK0) h1 LFx mk SPc HP MIk HH1 Ehcs HSPc. rt_facts.
    pose proof (alloc_ceiling_lo (L := arl_L R)) as ACL.
    flat constr:(ME) 2%nat. intros FLt2 _. flat constr:(FLt2) 6%nat. flclear FLt2. intros _ _ _ _ _ EOW.
    assert (CRS : client_range L (LB ++ fdata LF) (bv_unsigned sp) (md_addr e) 16).
    { intros a Ha. destruct (CR a Ha) as [S|[D|B]]; [| right; left; exact D| right; right; exact B].
      destruct SEP as [K|K]; [exfalso; clear - S Ha K; lia| left; clear - Ha K; lia]. }
    assert (BLK : md_own e = LHeap -> 1 <= md_n e /\ In (md_p e, 4 * md_n e) LB /\ 0 < md_p e /\ md_p e + 4 * md_n e <= alloc_ceiling).
    { intros EO. flat constr:((BLK0 EO)) 5%nat. intros K1 K2 B0 B2 _. split; [exact K1|]. split; [exact K2|]. split; [exact B0| exact B2]. }
    split.
    { eapply (mpd_at_heap_presx asegs L m mk LB (LB ++ fdata LF) LB (bv_unsigned sp) [] e ME (presA_presx asegs R _ _ _ _ _ _ _ _ HP) MI MIk);
        [exact CRS| | exact I| intros _; exact I|].
      - intros EO. flat constr:((BLK EO)) 3%nat. intros _ IN _. eapply client_range_block; [apply in_app_iff; left; exact IN| clear; lia| clear; lia].
      - intros b Hb. flat constr:((mpd_blk_heapE _ _ Hb)) 2%nat. intros EO ->. exact (proj1 (proj2 (BLK EO))). }
    split.
    { eapply (presA_aobj asegs R); [exact CSOK| exact HP| exact OB| exact CRS| clear - LOS SLO NEEDR NER; lia| intros x Hx; eapply hcs_below_top; exact Hx]. }
    split.
    { intros N1. destruct (md_own e) eqn:EO.
      - exfalso. flat constr:(EOW) 2%nat. flclear EOW. intros _ N0'. clear - N0' N1. lia.
      - flat constr:((BLK eq_refl)) 3%nat. intros _ IN _. rewrite <- Ehcs. exact (hm_aobj_block asegs R HIA h1 _ _ _ _ _ HH1 IN).
      - rewrite <- Ehcs. eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HH1| exact (IM EO)]. }
    split; [intros EO; exact (proj1 (proj2 (proj2 (BLK EO))))|].
    split; [clear - SEP HSPc; lia|].
    intros N1. left. destruct (md_own e) eqn:EO.
    - exfalso. flat constr:(EOW) 2%nat. flclear EOW. intros _ N0'. clear - N0' N1. lia.
    - flat constr:((BLK eq_refl)) 4%nat. intros _ _ _ B2. clear - B2 ALO LOS. lia.
    - flat constr:((AImgGlobals.img_norz_sound _ _ (IM EO))) 4%nat. intros _ _ IHI _. unfold AImgGlobals.IMG_HI in IHI. clear - IHI ACL ALO LOS. lia.
    all: match goal with |- ?g => idtac "OPAT-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Notation GX := (pt_X (g_G g)).
  Local Notation GY := (pt_Y (g_G g)).
  Local Ltac2 Set LiaOrc.tbl := fun () => "00>0>L16030265732.2L16194418498.1L22311177741.1L23897287043.1L24788440086.1L38400154755.1L4157873218.1 L48815712669.7L50790761713.7L52615975131.5L55383576707.1L55516431550.1L59314923118.6L64350575426.100000700:00=00@00C00F00I00[01601C01F01I01X01[S1G3GHIS1GS1GS1GS1GS1GS1GS1G1A1n2H12H21a2HaS1R5NEEDR2sp2lo3LOS3SLO3NERS2sp1G1a2Ha1KS1GS1GS1G2lo1a2Ha1S1KS1G". (* [comment removed for export] *)
  Lemma ck_G_at : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Ph1,(3=.$9.VR,VHIA,)PLFx,(0.$4.)Pmk,P,(2.&40.)(3.(2.&8.))P,(3>.$9.VR,VLB,VLF,(2?.&40.Vsp,)(3?.VR,)(40.$9.VR,VHIA,Vh,)(41.$42.)Vm,R1.)P,(43.$9.R2.)P,(44.$9.VR,VHIA,R5.VLB,R4.R3.)P,(=.P,$6.Sp(33.$9.VR,VHIA,R6.)(33.$9.VR,VHIA,Vh,))(1:.(31.$9.(32.VR,)(33.$9.VR,VHIA,Vh,)R5.VG,+<0.)(1:.(19.$9.R5.VG,(45.Vg,))(1:.(19.$9.R5.(20.VG,+38.)(46.(12.(26.(27.Vg,)))(47.&40.(48.(26.(27.Vg,))))(14.(26.(27.Vg,)))(49.(26.(27.Vg,)))))(1:.(19.$9.R5.(20.VG,+48.)(46.(12.(28.(27.Vg,)))(47.&40.(48.(28.(27.Vg,))))(14.(28.(27.Vg,)))(49.(28.(27.Vg,)))))(1:.(19.$9.R5.(20.VG,+78.)(4:.Vg,))(1:.(1:.(1;.=(12.(26.(27.Vg,))))(1<.(12.(26.(27.Vg,)))(4;.+2.+40.)))(1:.(1:.(1;.=(12.(28.(27.Vg,))))(1<.(12.(28.(27.Vg,)))(4;.+2.+40.)))(1:.(1<.=VG,)(1:.(1;.(20.VG,+<0.)(4;.+2.+40.))(=.$6.(4<.VG,+8.)=))))))))))")
(* [comment removed for export] *).
  Proof.
    intros h1 LFx mk HP MIk HH1 Ehcs. rt_facts.
    assert (CRS : client_range L (LB ++ fdata LF) (bv_unsigned sp) G 192).
    { intros a Ha. destruct (GCR a Ha) as [S|[D|B]]; [| right; left; exact D| right; right; exact B].
      destruct GSP as [K|K]; [exfalso; clear - S Ha K; lia| left; clear - Ha K; lia]. }
    flat constr:(GAT) 14%nat. intros HD GAL GPOS _ _ _ _ _ _ _ FLt3 _ GTL _. flat constr:(FLt3) 6%nat. flclear FLt3. intros EGX EGY _ MGX MGY _.
    pose proof (mpdr_p_range _ _ _ _ MGX) as GXR. pose proof (mpdr_p_range _ _ _ _ MGY) as GYR.
    flat constr:(MGX) 2%nat. intros CGX _. flat constr:(MGY) 2%nat. intros CGY _. rewrite EGX in CGX. rewrite EGY in CGY.
    replace (G + 56 + 16) with (G + 72) in CGY by (clear; lia).
    pose proof (rw_cells_bound _ _ _ _ GTL) as GHI. unfold grp_tail_cells in GHI. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in GHI.
    assert (SUBR : forall A n, G <= A -> A + n <= G + 192 -> client_range L (LB ++ fdata LF) (bv_unsigned sp) A n) by (intros A n H1 H2 a Ha; apply CRS; clear - Ha H1 H2; lia).
    split; [eapply (presA_aobj asegs R); [exact CSOK| exact HP| exact GOB| exact CRS| clear - LOS SLO NEEDR NER; lia| intros x Hx; eapply hcs_below_top; exact Hx]|].
    split; [eapply (presA_rw_cells asegs R); [exact HP| exact HD| apply SUBR; cbn; clear; lia| exact I]|].
    split; [eapply (presA_rw_cells asegs R); [exact HP| exact CGX| apply SUBR; cbn; clear; lia| exact I]|].
    split; [eapply (presA_rw_cells asegs R); [exact HP| exact CGY| apply SUBR; cbn; clear; lia| exact I]|].
    split; [eapply (presA_rw_cells asegs R); [exact HP| exact GTL| apply SUBR; cbn; clear; lia| exact I]|].
    split; [exact GXR|]. split; [exact GYR|]. split; [exact GPOS|]. split; [clear - GHI; lia| exact GAL].
    all: match goal with |- ?g => idtac "GAT-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00F0>L10719636406.2L13447073583.2L19806888736.3L22890275614.2L25562269484.1L266194112.2  L266206690.4  L31101877504.4L334984919.6  L36128645576.2L44921588402.0L4781719053.2 L4788524121.1 L48303896707.2L49429114339.3L50181574798.3L50181574798.8L50534718477.3L59070582403.4L61227600606.3L66254874338.1L8969490626.1 00000600<00D00J00M00S00^00i01701<01=01C01D01J01R01Z01n02602A02I02L02OS1d2D0S1g2NRS1N1a2HaS1d2D0S1dS1N2N0S1g1N2NP2NRS1N1d2D02K1S1g1d2D01a1b1KS1a1bSS1d2D0FS1N2N0S1N1a2HaS1N2N01KS1g1N2NR1a1b2Ha2Hb1KS1N1a2HaS1g1N2NP2NRS1N1a2HaS1dS1d". (* [comment removed for export] *)
  Lemma ck_budget : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "(1:.(1;.=VN,)(1:.(1:.(1;.=(14.(4=.Vg,)))(1;.(14.(4=.Vg,))VN,))(1:.(1;.=Vd,)(1:.Pa,$6.Pb,$6.P,(1:.(1;.=R2.)(1;.R2.VN,))P,(1:.(1;.=R2.)(1;.R2.VN,))(1:.(1:.(1;.=(4>.=R4.R3.(14.(4=.Vg,))))(1;.(4>.=R4.R3.(14.(4=.Vg,)))(4>.=VN,VN,VN,)))(1:.(1;.=(4?.=R4.R3.(14.(4=.Vg,))(20.Vd,+1.)))(1;.(4?.=R4.R3.(14.(4=.Vg,))(20.Vd,+1.))(4?.=VN,VN,VN,(20.Vd,+1.)))))(1:.(1;.=(50.VN,))(1:.(1;.=(51.VN,(20.Vd,+1.)))(1:.(1;.=(52.(20.Vd,+1.)))(1:.(=.$6.(52.(20.Vd,+1.))(53.+1.(20.Vd,+1.)))(1:.Pa,$6.P,(1:.(1;.=R1.)(1;.R1.VN,))(1:.(1:.(1;.=(54.R2.))(1;.(54.R2.)(54.VN,)))(1:.(1;.=(55.R2.))(1;.(55.R2.)(55.VN,))))(1:.(1;.=(56.(20.Vd,+1.)))(1:.(=.$6.(53.+3.(20.Vd,+1.))(13.+3.(52.(20.Vd,+1.))))(=.$6.(53.+2.(20.Vd,+1.))(13.+2.(52.(20.Vd,+1.)))))))))))))))")
(* [comment removed for export] *).
  Proof.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0. flat constr:(NLE) 3%nat. intros NP _ _.
    flat constr:(GAT) 9%nat. intros _ _ _ _ _ _ _ MP _. flat constr:(MP) 6%nat. intros _ _ _ _ NR _.
    assert (N0 : 0 <= N) by (clear - NP NR; lia).
    split; [exact N0|]. split; [clear - NP NR; lia|]. split; [exact D0|].
    split.
    { intros a b Ha Hb. split; split.
      - unfold mm_PHIn, red_PHIn, mul_mpi_PHIn, grow_PHI. unfold AVOL_CALL.
        pose proof (mod_mpi_PHIn_nonneg (mul_mpi_nz 0 a b) (md_n dP) ltac:(unfold mul_mpi_nz; clear; lia) ltac:(clear - NR; lia)) as K. clear - K Ha Hb NR. lia.
      - apply mm_PHIn_mono; first [ apply Z.le_refl | exact (proj2 Ha) | exact (proj2 Hb) | exact NP ].
      - unfold mm_FRn, red_FRn, mul_mpi_FRn.
        pose proof (mod_mpi_FRn_nonneg (mul_mpi_nz 0 a b) (md_n dP) (d + 1) ltac:(unfold mul_mpi_nz; clear; lia) ltac:(clear - D0; lia)) as K.
        unfold calls_FR, fr_charge. clear - K D0. lia.
      - apply A_ecp_sw_rhs.mm_FRn_mono; first [ exact Ha | exact Hb | exact NP | (clear; lia) | (clear - D0; lia) ]. }
    split.
    { unfold sw_rhs_PHIn, mm_PHIn, red_PHIn, mul_mpi_PHIn, addsub_PHIn, intop_PHIn, grow_PHI, ecp_sz. unfold AVOL_CALL.
      pose proof (mod_mpi_PHIn_nonneg (mul_mpi_nz (3 * N + 9) (3 * N + 9) (3 * N + 9)) N ltac:(unfold mul_mpi_nz; clear - N0; lia) ltac:(clear - N0; lia)) as K. clear - K N0. lia. }
    split.
    { unfold sw_rhs_FRn, mm_FRn, red_FRn, mul_mpi_FRn, addsub_FRn, intop_FRn.
      pose proof (mod_mpi_FRn_nonneg (mul_mpi_nz (ecp_sz N) (ecp_sz N) (ecp_sz N)) N (d + 1) ltac:(unfold mul_mpi_nz, ecp_sz; clear - N0; lia) ltac:(clear - D0; lia)) as K1.
      unfold calls_FR, fr_charge. clear - K1 D0. lia. }
    split; [unfold fr_charge; clear - D0; lia|]. split; [unfold calls_FR; clear; lia|].
    split; [intros a Ha; split; split; first [ (unfold intop_PHIn, grow_PHI; unfold AVOL_CALL; clear - Ha; lia) | (apply grow_PHI_mono; exact (proj2 Ha)) | (apply intop_PHIn_mono; exact (proj2 Ha)) ]|].
    split; [unfold intop_FRn, calls_FR, fr_charge; clear - D0; lia|].
    split; unfold calls_FR; clear; lia.
    all: match goal with |- ?g => idtac "BUDGET-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition S1P : machine_state -> Prop := fun ms =>
    exists (FB sp1 : Z) (h1 : HST asegs R HIA) (m1 : mem) (kind r : Z)
           (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s3v s4v s5v s6v s7v : word) (w0 w1 w2 : word),
      ms = MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 FB) s3v s4v s5v s6v s7v (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 (if kind =? 0 then 0xcbc44 else if kind =? 1 then 0xcbf60 else 0xcbe6c)) fc None m1 (seg_rom asegs)
      /\ (kind = 0 \/ kind = 1 \/ kind = 2)
      /\ (kind = 0 -> a0 = Z_to_bv 64 r /\ -2^31 < r <= 0)
      /\ (kind = 1 -> g_h g = 1 /\ s3v = Z_to_bv 64 Q /\ s4v = Z_to_bv 64 G /\ s5v = Z_to_bv 64 (FB + 64) /\ s6v = Z_to_bv 64 (FB + 32) /\ s7v = Z_to_bv 64 (Q + 16)
                      /\ exists padY padR, rw_cells asegs m1 (FB + 32) (mpi_cells 0 (Z_to_bv 64 1) 0 padY) /\ rw_cells asegs m1 (FB + 64) (mpi_cells 0 (Z_to_bv 64 1) 0 padR))
      /\ (kind = 2 -> g_h g = 2 /\ s3v = Z_to_bv 64 Q /\ s4v = Z_to_bv 64 G /\ s5v = Z_to_bv 64 (FB + 96)
                      /\ exists padX, rw_cells asegs m1 (FB + 96) (mpi_cells 0 (Z_to_bv 64 1) 0 padX))
      /\ bv_unsigned sp - 112 <= sp1 <= bv_unsigned sp - 96 /\ sp1 mod 32 = 0
      /\ HM asegs R HIA h1 LB ((FB, 128) :: LF) m1 /\ hcs asegs R HIA h1 = CS /\ htop asegs R HIA h1 = htop asegs R HIA h
      /\ hstkhi asegs R HIA h1 = hstkhi asegs R HIA h /\ hflag asegs R HIA h1 = hflag asegs R HIA h
      /\ havol asegs R HIA h1 = havol asegs R HIA h /\ hfr asegs R HIA h1 = hfr asegs R HIA h
      /\ (forall mo, HK asegs R HIA h1 mo <-> HK asegs R HIA h mo)
      /\ FB mod 64 = 0 /\ fresh_apart R LB LF FB 128
      /\ rw_cells asegs m1 FB [C8 w0; C8 w1; C8 w2]
      /\ rw_cells asegs m1 (Z.shiftr FB 3 + al_sb AL) (if kind =? 0 then FSHP else if kind =? 1 then FSHSW else FSHMX)
      /\ rw_cells asegs m1 (bv_unsigned sp + -88) SAVEL
      /\ rw_cells asegs m1 sp1 [C8 (Z_to_bv 64 FB)] /\ stk asegs m1 (sp1 + 8) (bv_unsigned sp + -88)
      /\ stk asegs m1 lo sp1 /\ mem_inv asegs m1
      /\ presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [] m m1
      /\ sshad asegs AL m1 slo (bv_unsigned sp).
  Local Ltac2 Set LiaOrc.tbl := fun () => "0:50@C17025492443.267C17025492443.308C17025492443.310C17025492443.356C17027589631.287C17027589631.290C17027589631.336C18973515380.312C23922862675.351C60407910007.355D11893914199.312D13777365766.190D13777365766.191D13777365766.192D14430362432.312D16060100967.351D16069757089.312D16069757090.355D16071854214.351D18607476203.189D2455419791.355 D2457697672.234 D29566955331.355D29569067332.234D32456773204.355D32458983507.234D32604263313.235D3386269615.233 D45702641182.233D50254960491.190D50626680716.312D560335984.163  D56536395888.351D58077997354.190D5984197035.351 D59959467330.190D59959467330.191D59959467330.192D60109446735.267D60109446735.308D60109446735.310D60109446735.356D60111543915.287D60111543915.290D60111543915.336D62011770186.235D62012280210.163D62151899352.267D62151899352.308D62151899352.310D62151899352.356D62153996540.287D62153996540.290D62153996540.336D68221095944.351D68223193132.355D68223193135.312D68409558508.233D6897506281.233 K21212095580.267K21212095580.308K21212095580.310K21212095580.356K21214192760.287K21214192760.290K21214192760.336K8075921457.267 K8075921457.308 K8075921457.310 K8075921457.356 K8078018581.287 K8078018581.290 K8078018581.336 L10041968289.0  L11007094131.261L11007094131.263L1136325469.2   L11454114216.2  L12772973345.0  L12860309875.260L13062538913.0  L13176305223.2  L13422353014.212L1488493345.0   L14918541047.1  L1540877545.3   L15629995721.2  L15903991350.8  L15904519734.2  L15904519734.6  L16236701943.1  L18457785511.0  L19548981075.212L19556266785.0  L19980016842.11 L19980537034.6  L20407710113.0  L20438928296.5  L20438928296.8  L20439456680.10 L20441738155.7  L20441966894.13 L20441966894.14 L21218866939.2  L21262024435.12 L21652990240.300L21654730866.2  L220710108.3    L2275137097.0   L23268210308.0  L23305025156.0  L2411933138.260 L24133462173.207L24344722227.2  L25543464460.2  L25637237043.2  L2621559066.1   L27188209011.238L27832565024.343L27843863047.1  L27938631989.4  L27938665392.11 L27940405558.8  L27940933942.2  L27940933942.6  L29428324941.5  L29431152682.1  L29738741675.1  L29936708385.0  L31270623479.1  L31521299904.3  L32120604860.9  L32120615310.3  L32120648459.10 L32752941754.2  L33312313103.2  L33312345482.9  L33316942617.2  L33483560980.12 L33485826452.1  L33485826452.3  L33811788193.0  L34785771955.3  L3482791583.8   L3483319967.1   L3483319967.6   L3484573340.3   L35228767239.1  L359902451.12   L36180999398.148L36376992499.12 L38235734261.1  L38691415991.0  L3876079316.8   L39235458958.3  L39235464892.9  L39235491083.10 L3983061409.0   L40596013857.0  L41406233680.3  L41507998455.1  L42397870617.2  L43061657906.146L43188064477.3  L43495095303.1  L44657693404.3  L45445121012.1  L45921596632.2  L46944522740.1  L47228624632.207L47663688086.1  L47871884617.2  L48117620911.142L48119718060.208L48132302231.228L48132302231.229L48132302231.244L48132302231.261L48132302231.265L48132302231.278L48132302231.295L48312170508.2  L49367084.2     L49426765047.1  L50204818630.3  L50388565080.1  L50924091066.2  L51462947882.279L51609971903.210L51660505024.3  L51874217988.1  L52255793882.213L52944289203.3  L53133840792.280L54437155233.0  L55048118260.1  L55351494680.13 L55891255044.1  L55981025728.3  L56545819383.1  L56853899255.21 L56916433924.1  L57355539152.195L57387013391.2  L57387243402.9  L57397793035.10 L57397957518.3  L57397963452.9  L58036821178.2  L58077947190.214L58093455155.2  L58360691959.1  L58789625892.5  L58790154276.11 L59308586248.2  L59308677456.14 L59670431479.1  L60054938547.3  L61437265048.2  L61568739314.279L62018535662.1  L6292090588.3   L64886557444.1  L65337788402.259L65479729911.1  L66151427842.16 L66151427842.17 L66937561129.339L6910010090.207 L7960697356.2   L8081644182.3   L881835912.0    L9080220944.4   L9243491210.9   L9243719951.2   L9356559645.12  O10565637740.355O10567734856.351O11932660723.307O17025492443.267O17025492443.308O17025492443.310O17025492443.356O17027589631.287O17027589631.290O17027589631.336O17215019116.355O17215019119.312O18024077878.346O18024077878.348O18024077878.350O18024077878.351O18024077878.353O20099309002.350O20101406189.312O20101406190.354O28722692754.267O28722692754.308O28722692754.310O28722692754.356O28724789942.287O28724789942.290O28724789942.336O30393275641.307O3078286936.351 O32535777407.311O426448880.344  O42788551567.350O42893338165.309O42893338165.310O4492316913.308 O4492316913.310 O4492316913.356 O44938202843.351O44940300028.311O44940300031.355O4494414037.290 O4494414037.336 O47782918454.345O47782918454.347O47782918454.349O47782918454.352O47782918454.354O48978854641.308O48978854641.310O48978854641.356O48980951765.290O48980951765.336O49699726460.355O50702732434.267O50702732434.308O50702732434.310O50702732434.356O50704829622.287O50704829622.290O50704829622.336O52495902430.349O55209884805.350O55211981985.344O55211981986.307O55518239188.350O56414299794.267O56414299794.308O56414299794.310O56414299794.356O56416396982.287O56416396982.290O56416396982.336O58924527866.344O59623432085.287O59623432085.290O59623432085.336O59625529265.267O59625529265.308O59625529265.310O59625529265.356O61019287979.354O6131873077.308 O6131873077.311 O65961212488.351O65963309679.312O66637284776.312O67605037642.287O67605037642.290O67605037642.336O67607134830.267O67607134830.308O67607134830.310O67607134830.356P1129456122.350 P1131553245.312 P1131553246.354 P14904348592.188P16083265164.188P21212095580.267P21212095580.308P21212095580.310P21212095580.356P21214192760.287P21214192760.290P21214192760.336P21647862485.350P21649959665.344P21649959666.307P232935242.350  P24359170178.312P25541729725.311P25650051749.350P31511107185.307P32763785480.355P32765882668.351P33303880090.290P33303880090.336P33305977278.308P33305977278.310P33305977278.356P34787641857.287P34787641857.290P34787641857.336P34789739045.267P34789739045.308P34789739045.310P34789739045.356P41419110342.267P41419110342.308P41419110342.310P41419110342.356P41421207522.287P41421207522.290P41421207522.336P42409982106.290P42409982106.336P42412079294.308P42412079294.310P42412079294.356P44647045485.307P47874275064.311P47874275067.355P47876372191.351P48308204442.351P50927926572.351P50930023691.312P51672855638.349P51859704758.345P51859704758.347P51859704758.349P51859704758.352P51859704758.354P52938159617.287P52938159617.290P52938159617.336P52940256805.267P52940256805.308P52940256805.310P52940256805.356P55893644470.346P55893644470.348P55893644470.350P55893644470.351P55893644470.353P55975027314.344P56918693813.308P56918693813.311P58043275016.355P58043275019.312P58087328897.354P60050384933.267P60050384933.308P60050384933.310P60050384933.356P60052482049.287P60052482049.290P60052482049.336P6306932078.344 P64884818101.309P64884818101.310P7962563006.355 Q10253831745.168Q10533598597.165Q10592386194.239Q10594630297.355Q10598680976.343Q13237513883.287Q1530342990.190 Q15766564435.267Q15766564435.308Q15766564435.310Q15766564435.356Q15768661623.287Q15768661623.290Q15768661623.336Q17135859835.355Q17197838715.287Q17210756979.286Q19548733779.339Q19561460314.300Q19561460314.343Q21765573509.312Q21765573510.355Q21767670690.351Q22307111700.167Q23890796818.267Q23893092665.269Q23927511190.169Q23937998252.165Q24107313779.168Q24133462173.240Q24137657765.238Q24137657789.242Q25394246591.312Q26130505906.286Q27853555832.312Q27942454161.351Q27944551349.355Q27944551350.312Q2803826605.351 Q2805923721.355 Q2805923722.312 Q29775981542.351Q29778078657.312Q29778078658.355Q29784271951.287Q30220517308.355Q30223088055.239Q31021924279.188Q32437204119.351Q32440833928.238Q33135353568.312Q33135353571.355Q33137450695.351Q33228740307.343Q33656017904.267Q33658051547.269Q34667424921.339Q34669522109.351Q34964382778.267Q34964382778.308Q34964382778.310Q34964382778.356Q34966479902.287Q34966479902.290Q34966479902.336Q35346075610.339Q35653441506.141Q38248387216.267Q38248387216.308Q38248387216.310Q38248387216.356Q38248895665.170Q38250484404.287Q38250484404.290Q38250484404.336Q40271359350.190Q4153679096.269 Q4155597051.268 Q4155597051.270 Q4155970771.267 Q42437284299.262Q42437284299.269Q42437284299.279Q42437284299.281Q42437284299.301Q42437284299.309Q42437284299.321Q42437284299.341Q42439168719.188Q42439168719.267Q42439168719.308Q42439168719.310Q42439168719.351Q42439168719.356Q42439382255.171Q42441265896.312Q42441265899.287Q42441265899.290Q42441265899.336Q42441265899.355Q42441479406.244Q43880146029.170Q47241206720.165Q47433032799.351Q48117620900.239Q48118064779.351Q48120161964.312Q48120161967.355Q48132302231.238Q48358016498.287Q48358016498.290Q48358016498.336Q48360113622.267Q48360113622.308Q48360113622.310Q48360113622.356Q49730396883.300Q51218566552.351Q55394062898.266Q55514504784.286Q55964990415.268Q55964990415.270Q56531220664.239Q56533073587.355Q58741773978.312Q58746365328.300Q59310664043.165Q59310664043.238Q59321150552.239Q59321559671.267Q59321559671.308Q59321559671.310Q59321559671.351Q59321559671.356Q59323656784.312Q59323656787.287Q59323656787.290Q59323656787.336Q59323656787.355Q59394051867.267Q59865520176.171Q59865603600.267Q59865603600.308Q59865603600.310Q59865603600.351Q59865603600.356Q59867617329.244Q59867700788.287Q59867700788.290Q59867700788.336Q59867700788.355Q59867700791.312Q59871812884.262Q59871812884.269Q59871812884.279Q59871812884.281Q59871812884.301Q59871812884.309Q59871812884.321Q59871812884.341Q60109315147.141Q6192914196.188 Q62011770190.169Q62012212072.190Q62022254708.165Q63581199056.266Q6399114492.167 Q64344283635.266Q64356526075.267Q64619154459.268Q64619154459.270Q64681502663.244Q64681845185.312Q64681845186.287Q64681845186.290Q64681845186.336Q64681845186.355Q64683599814.171Q64683942374.267Q64683942374.308Q64683942374.310Q64683942374.351Q64683942374.356Q64685695714.262Q64685695714.269Q64685695714.279Q64685695714.281Q64685695714.301Q64685695714.309Q64685695714.321Q64685695714.341Q67038703949.188Q6897428426.242 Q6897428434.238 Q6910010090.240 Q7661097679.267 Q8360723120.312 Q9090756535.267 Q9090756535.308 Q9090756535.310 Q9090756535.356 Q9092853651.287 Q9092853651.290 Q9092853651.336 Q9356559653.303 Q9356559653.342 Q9356559653.346 Q9356559677.248 Q9356559677.267 Q9356559677.271 Q9356559677.289 Q9356559677.291 Q9356559677.317 Q9356559677.337 Q9356560156.171 Q9633962917.300 Q9633962917.343 Q9644583048.267 Q9644583048.308 Q9644583048.310 Q9644583048.351 Q9644583048.356 Q9646680236.287 Q9646680236.290 Q9646680236.336 Q9646680236.339 Q9646680236.355 Q9646680239.312 00000100200300400500600700;00?00C00a01A01B01C01a02?03A04C05E05F05G05H05f06@06^07807[07\08608708808S09109L09M09m09n09o0:R0;90;^0<E0<j0=O0>40>P0>e0?f0@k0An0C30D60E90F<0G>0H@0IB0IC0I]0I^0I_0I`0Ia0Ib0Ic0Id0J?0J^0K;0KZ0L70LT0M10M20MP0Mn0Mo0N70N80NV0NW0N_0OH0OI0OM0OY0Oa0P@0PA0PB0PF0PG0Pk0Pl0QD0QE0QF0QG0QH0QI0QJ0QK0QL0QM0R:0RX0RY0RZ0R[0R\0R]0SD0ST0SU0SV0SW0S\0T;0TY0T]0T^0T_0U>0U?0U@0UR0US0UW0UX0U\0U]0U^0U_0U`0Ua0Uh0Ui0Uj0Uk0Ul0Um0Un0Uo0V00V10V20V30V70Vd0W20W_0Wc0Wd0XA0XB0XC0XD0XE0XF0XG0XH0XI0YB0YM0YQ0YR0YV0Y^0Yb0Z50Z:0Z;0Zd0[O0\:0\e0]R0^=0^j0_U0`@0`A0`G0`K0`W0`\0`]0`^0aC0aD0aE0a_0a`0b>0b?0bC0bS0bT0bU0bV0c>0c?0c@0cG0cH0cI0cJ0cK0cL0cj0ck0co0d00dI0dO0dY0d]0d^0df0eM0eP0eQ0eR0f90f:0f\0f]0g;0gK0gL0gM0gN0g]0g^0ge0hT0hU0hV0hW0hX0hY0hZ0h[0h\0h]0h^0h_0h`0ha0hb0hc0hd0he0hf0hg0hh0hi0hj0hk0hl0hm0hn0ho0i00i10i20i30i40i50i60i70i80i90i:0i;0i<0i=0i>0i?0i@0iA0iB0iC0iD0iE0iF0iG0iH0iI0iJ0iK0iL0iM0iN0iO0iP0iQ0iR0iS0iT0iU0iV0iW0iX0iY0iZ0i[0i\0i]0i^0i_0i`0ia0ib0ic0id0ie0if0ig0ih0ii0ij0ik0il0im0in0io0j00j10jM0ji0kE0kf0lG0lH0lI0lJ0lK0lL0lM0lN0lO0lP0lQ0m10mf0n\0oQ10M11C12912\13?13d14G14l15J15h16F16b17B17`18@18\19<19Z1::1:X1;61;T1<71<Z1=?1=b1>G1>g1?]1@S1AI1B?1C51Ck1Dg1Dh1Di1Dj1Dk1Dl1EJ1Eh1FF1Fb1GB1G`1H@1HA1HB1HC1HD1HE1IA1IB1IC1J91Jo1Kd1L@1L`1M>1M^1N<1NZ1O81OX1OY1OZ1PP1P_1Q11QA1QU1Qi1R]1S51SO1Sm1TI1Tj1UF1Ub1V>1VR1Vc1W41W\1XD1Xl1Y`1ZT1[H1[W1[h1\91\N1\o1]>1]N1]^1]n1^B1^S1^g1_S1`?1`k1a@1aU1aj1bF1bb1c>1cO1cc1d31dT1dU1dV1e51eT1f31fG1fX1fi1g=1gQ1h91he1iO1j;1je1kO1l91lM1ll1m<1mP1mb1n61nF1nX1nj1o<1oQ1ob20320D20U20o21I21e22?22Y23523Q23m24E24]25925S25o26K26c27?27Y28328M28i29A29T29g2:;2:f2;U2<D2=32=^2>;2>X2?52?P2?o2@L2@k2A?2AS2Ad2B52BF2BW2BX2BY2Bm2CA2CB2CC2CD2CE2CF2CG2CH2CI2CJ2CK2CL2CM2CN2DB2DC2DD2DE2DF2DG2DH2DI2DJ2DK2DL2DM2DN2DO2DP2DQ2DR2DS2DT2DU2DV2Dg2E82EG2EV2Ee2F62FE2FV2Fg2G[2HO2I22IY2J>2Jc2KH2L22LW2M:2Ma2NF2O02OZ2P?2Pd2QK2R02RU2S<2Sf2TP2U=2UM2U]2Um2V>2V?2VZ2W92WV2X52XR2Xo2YL2Yf2Z@2ZZ2[02[H2[`2\:2\R2\j2]D2]Z2^12^H2^[2_22_G2_^2`52`J2`_2a42aK2ab2b9FFFFFFFS2FBS2FBS2FBS2LF2ra2sp1g1p3LFB4lxHn3sp12FBS2LF2ra2sp1Q3LFB4lxHn3sp13x142HxFFS2LF2ra2sp1g1p3LFB4lxHn3sp12FBS2LF2ra2sp1g1p3LFB4lxHn3sp12FBS1R3NS12LF2ra2sp1g1p2lo3LFB3LOS3SLO3NES3SPR4lxHn3sp14SP1R2FB2F02H2S1R3NS12LF2ra2sp1g1p2lo3LFB3LOS3SLO3NES3SPR4lxHn3sp14SP1R2FB2F02H2S1R3NS12LF2ra2sp1g1p2lo3LFB3LOS3SLO3NES3SPR4lxHn3sp14SP1R2FB2F02H2FFFS2LF2ra2sp1g1p3LFB4lxHn3sp12FBS2LF2ra2sp3LFB4lxHn3sp12FBS2LF2ra2sp1g1p3LFB4lxHn3sp12FBS2LF2ra2sp3LFB4lxHn3sp12FBS1R3HIA2LF2ra2sp3LFB4lxHn3sp12h12FBFS2LF2ra2sp3LFB4lxHn3sp12FBFFS1R3HIA1h2LF2ra2sp3LFB4lxHnS2LF2ra2sp1g1p3LFB4lxHn3sp12FBS2LF2ra2sp3LFB4lxHn3sp13H15FS2LF2ra2sp1G3LFB4lxHn3sp13x142HxFFS1R2LF2ra2sp2lo3LFB3LOS4lxHn3sp12FBS1R2LF2ra2sp1g1p2lo3LFB3LOS4lxHn3sp12FBS1R2LF2ra2sp1p2lo3LFB3LOS4lxHn3sp12FBS1R2LF2ra2sp1g1p2lo3LFB3LOS4lxHn3sp12FBS1R2LF2ra2sp1p2lo3LFB3LOS4lxHn3sp12FBS1R2LF2ra2sp1p2lo3LFB3LOS4lxHn3sp12FBS1R2LF2ra2sp1p2lo3LFB3LOS4lxHn3sp12FBS1R2LF2ra2sp3LFB4lxHn3sp12FBS1R2LF2ra2sp3LFB4lxHnS1R3HIA1h2LF2ra2sp2lo3LFB3TOP3SPR4lxHn3sp14SP1R2h15Ehtop2FB2F02H3S1R3HIA1h2LF2ra2sp1g1p2lo3LFB3TOP3SPR4lxHn3sp14SP1R2h15Ehtop2FB2F02H3S1R3HIA1h2LF2ra2sp1p2lo3LFB3TOP3SPR4lxHn3sp14SP1R2h15Ehtop2FB2F02H3S1R3HIA1h2LF2ra2sp1g1p2lo3LFB3TOP3SPR4lxHn3sp14SP1R2h15Ehtop2FB2F02H3S1R3HIA1h2LF2ra2sp1p2lo3LFB3TOP3SPR4lxHn3sp14SP1R2h15Ehtop2FB2F02H3S1R3HIA1h2LF2ra2sp1p2lo3LFB3TOP3SPR4lxHn3sp14SP1R2h15Ehtop2FB2F02H3S1R3HIA1h2LF2ra2sp1p2lo3LFB3TOP3SPR4lxHn3sp14SP1R2h15Ehtop2FB2F02H3S1R3HIA1h2LF2ra2sp1g1p3LFB3TOP3SPR4lxHn3sp14SP1R2h15Ehtop2FB2F02H3S1R3HIA1h2LF2ra2sp1g1p3LFB3TOP3SPR4lxHn3sp14SP1R2h15Ehtop2FB2F02H3S1R3HIA1h2LF2ra2sp1g1p3LFB3TOP3SPR4lxHn3sp14SP1R2h15Ehtop2FB2F02H3FS2LF2ra2sp3LFB4lxHn3sp12FBFFFFFFFS2LF2sp2lo3LFB4lxHn3sp13H15S2LF2sp1g1p2lo3LFB4lxHn3sp13H15S2LF2sp1p2lo3LFB4lxHn3sp13H15S2LF2sp1g1p2lo3LFB4lxHn3sp13H15S2LF2sp1p2lo3LFB4lxHn3sp13H15S2LF2sp1p2lo3LFB4lxHn3sp13H15S2LF2sp1p2lo3LFB4lxHn3sp13H15SS2LF2ra2sp1G1p3LFB4lxHn3sp12FBS2LF2ra2sp1G1p3LFB4lxHn3sp12FBFS2LF3LFBSS2LF2ra2sp1G1p3LFB4lxHn3sp12FBSS2lo3sp1S2LF2ra2sp3LFB3SPR4lxHn3sp14SP1R2FB2F02F8SS2FBS2sp3sp13SP1S2LF3LFBS1R5NEEDR2sp2lo3SLO3NER3sp13SP1FFS2FBSS2LF2ra2sp3LFB3SPR4lxHn3sp12FB2F02F8SS1R3HIA1h2sp3TOP3sp13SP1FSFFFFFFFS1R5NEEDR2sp2lo3LOS3SLO3ALO3NER3sp13SP12FB2F1S2LF2ra2sp1g1p3LFB4lxHn3sp12FBFFSSSS2LF2ra2sp1G1p3LFB4lxHn3sp12FB4GPOS3GHIS2LF3LFB4lxHn2FBFFFS3sp1S2LF2ra2sp3LFB4lxHn3sp12FB1c2HcS2LF2ra2sp1g1p3LFB4lxHn3sp12FBS2FBFFS1R5NEEDR2sp2lo3SLO3NER3sp13SP1FFS1R2lo3LOS3ALO3ACVFS2FBSS2FBFFFFFS2FB2F0FFFFFSFFFFFS2spS1R5NEEDR2sp2lo3LOS3SLO3ALO3NER3sp13SP12FB2F1S2LF2ra2sp3LFBS1R5NEEDR2sp2lo3LOS3SLO3ALO3NER3sp13SP12FB2F1S2loSS1R3NS12sp2lo3SLO3NES3sp13SP1FFFSSFFFS1R5NEEDR2LF2ra2sp1G1Q2lo3LFB3GSP3GMC3QSP3QMC3SLO3NER3SPRS2sp2lo3sp1S2FBFS2FBS2sp3sp1S2FBS1R2LF3LFB3ALO4lxHnS3sp1FS1R3NS12LF2sp2lo3LFB3LOS3SLO3ALO3NES4lxHnS1R5NEEDR2LF2sp2lo3LFB3LOS3SLO3ALO3NER4lxHnS1R5NEEDR2LF2sp2lo3LFB3LOS3SLO3ALO3NER4lxHnS1R5NEEDR2LF2sp2lo3LFB3LOS3SLO3ALO3NER4lxHnS1R5NEEDR2LF2sp2lo3LFB3LOS3SLO3ALO3NER4lxHn1pS1R5NEEDR2LF2sp2lo3LFB3LOS3SLO3ALO3NER4lxHnS1R5NEEDR2LF2sp1p2lo3LFB3LOS3SLO3ALO3NER4lxHnS1R5NEEDR2LF2sp2lo3LFB3LOS3SLO3ALO3NER4lxHnS1R5NEEDR2LF2sp2lo3LFB3LOS3SLO3ALO3NER4lxHnFS1R2FBS2FBS2sp3sp13SP1S3sp1FFS1R2LF2sp3slo3LFB4SLO13ALO4lxHn2FB2F1FFS2LF2ra2sp3LFB4lxHn3sp12FBFS2LF2ra2sp1G1p3LFB4lxHn3sp12FBSS2FBS1R3ACV2FB2F02F1FFFS2sp2r03SPA3sp11r4SP1M3H143H151q1H2q02H4FFS2FB2F0FFFFFS2LF2ra2sp3LFB4lxHn3sp13H152FBFS2FBFS1R2sp2lo3SLO3NES3sp13SP1S1i2HiS2FB2Kb2F0S2FBFS2LF3LFBS2LF2ra2sp1G1p3LFB4lxHn3sp12FB4GPOS3GHIS1RFFS2LF2ra2sp1G1p3LFB4lxHn3sp12FB4GPOS3GHIFS3sp12r04SP1M1q1r1H2H02q02H42FB2F8FS2LF2ra2sp1g1p3LFB4lxHn3sp12FBS2LF3LFB4lxHn2FBFFSS2sp2lo3sp13SP1FS2FB2F0S1R5NEEDR2sp2lo3LOS3SLO3ALO3ACV3NER3SPR3sp13SP1FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFS2LF2sp1g1p3LFB4lxHn3sp13H15S2LF2sp1g1p3LFB4lxHn3sp13H15S2LF2sp1g1p3LFB4lxHn3sp13H15S2LF2sp1Q2lo3LFB3QSP4lxHn3sp13SP1S2LF2sp1G2lo3LFB3GSP4lxHn3sp13SP1FFFFFFFFFFS2LF1g1p2lo3LFB4lxHn3sp12FB4FBLOS1R5NEEDR2LF2sp1g1p2lo3LFB3LOS3SLO3ALO3NER4lxHn2FB2F1S1R5NEEDR2LF2sp1g1p2lo3LFB3SLO3NER4lxHn3sp12FB4FBLO2H2S1R5NEEDR2LF2sp1g1p2lo3LFB3LOS3SLO3ALO3NER4lxHn2FB2F1S1R5NEEDR2LF2sp1g1p2lo3LFB3LOS3SLO3ALO3NER4lxHn3sp12FB2F12H2S1R5NEEDR2LF2sp1g1p2lo3LFB3SLO3NER4lxHn3sp12FB4FBLO2H2S1R5NEEDR2LF2sp1g1p2lo3LFB3SLO3NER4lxHn3sp12FB4FBLO2H2S1R2LF1p2lo3LFB3LOS3ALO4lxHn3sp12H6S1R2LF1p2lo3LFB3LOS3ALO4lxHn3sp12H6S1R2LF1g1p2lo3LFB3LOS3ALO4lxHn3sp12H6S1R2LF1p2lo3LFB3LOS3ALO4lxHn3sp12H6S1R2LF1g1p2lo3LFB3LOS3ALO4lxHn3sp12H6S2LF1p2lo3LFB4lxHn3sp12FB4FBLOS2LF1p2lo3LFB4lxHn3sp12FB4FBLOS2LF1p2lo3LFB4lxHn3sp12FB4FBLOS2LF2lo3LFB4lxHn3sp12FB4FBLOS2LF1g1p2lo3LFB4lxHn3sp12FB4FBLOS2LF1p2lo3LFB4lxHn3sp12FB4FBLOS2LF1g1p2lo3LFB4lxHn3sp12FB4FBLOS2LF2lo3LFB4lxHn3sp12FB4FBLOS2LF1g1p2lo3LFB4lxHn3sp12FB4FBLOS2LF1p2lo3LFB4lxHn3sp12FB4FBLOS2LF1g1p2lo3LFB4lxHn3sp12FB4FBLOS2LF1p2lo3LFB4lxHn3sp12FB4FBLOS2LF1p2lo3LFB4lxHn3sp12FB4FBLOS2LF1p2lo3LFB4lxHn3sp12FB4FBLOS1R2LF1p2lo3LFB3LOS3ALO4lxHn3sp12H6S1R2LF1p2lo3LFB3LOS3ALO4lxHn3sp12H6S1R2LF1g1p2lo3LFB3LOS3ALO4lxHn3sp12H6S1R2LF1p2lo3LFB3LOS3ALO4lxHn3sp12H6S1R2LF1g1p2lo3LFB3LOS3ALO4lxHn3sp12H6S2LF1g1p2lo3LFB4lxHn3sp12FB4FBLOS1R5NEEDR2LF2sp1g1p2lo3LFB3SLO3NER4lxHn3sp12FB4FBLO2H2S1R5NEEDR2LF2sp1g1p2lo3LFB3SLO3NER4lxHn3sp12FB4FBLO2H2S1R5NEEDR2LF2sp1g1p2lo3LFB3SLO3NER4lxHn3sp12FB4FBLO2H2S1R5NEEDR2LF2sp1g1p2lo3LFB3SLO3NER4lxHn3sp12FB4FBLO2H2S1R5NEEDR2LF2sp1g1p2lo3LFB3SLO3NER4lxHn3sp12FB4FBLO2H2S1R5NEEDR2LF2sp1g1p2lo3LFB3SLO3NER4lxHn3sp12FB4FBLO2H2S1R5NEEDR2LF2sp1g1p2lo3LFB3LOS3SLO3ALO3NER4lxHn3sp12FB2F12H2FFFFFS2LF1p2lo3LFB4lxHn3sp12FB4FBLOS2LF1p2lo3LFB4lxHn3sp12FB4FBLOS2LF1p2lo3LFB4lxHn3sp12FB4FBLOS2LF2lo3LFB4lxHn3sp12FB4FBLOS2LF1g1p2lo3LFB4lxHn3sp12FB4FBLOS2LF1p2lo3LFB4lxHn3sp12FB4FBLOS2LF1g1p2lo3LFB4lxHn3sp12FB4FBLOFFFFFS1R5NEEDR2LF2sp1g1p2lo3LFB3LOS3SLO3ALO3NER4lxHn3sp12FB2F12H2FFS1R5NEEDR2LF2sp1g1p2lo3LFB3SLO3NER4lxHn3sp12FB4FBLO2H2S1R5NEEDR2LF2sp1g1p2lo3LFB3SLO3NER4lxHn3sp12FB4FBLO2H2S1R5NEEDR2LF2sp1g1p2lo3LFB3LOS3SLO3ALO3NER4lxHn2FB2F1S2LF2lo3LFB4lxHn3sp12FB4FBLOS2LF1g1p2lo3LFB4lxHn3sp12FB4FBLOS2LF1p2lo3LFB4lxHn3sp12FB4FBLOS2LF1g1p2lo3LFB4lxHn3sp12FB4FBLOS2LF1p2lo3LFB4lxHn3sp12FB4FBLOS2LF1p2lo3LFB4lxHn3sp12FB4FBLOS2LF1p2lo3LFB4lxHn3sp12FB4FBLOS2LF1g1p2lo3LFB4lxHn3sp12FB4FBLOFFS1R5NEEDR2LF2sp1g1p2lo3LFB3SLO3NER4lxHn3sp12FB4FBLO2H2S2LF1Q3LFB4lxHnS1R2LF2sp3LFB4lxHnS2LF3LFB4lxHn2FBS2LF1g1p3LFB4lxHn2FBS2LF1g1p3LFB4lxHn2FBS2LF2ra2sp1G1p3LFB3SPR4lxHn3sp14SP1R2FB2F04GPOS4GAL8S2LF2sp3LFB4lxHn3sp13H15S1R2LF2lo3LFB3LOS3ALO4lxHnS1R2LF1g1p2lo3LFB3LOS3ALO4lxHnS1R2LF1p2lo3LFB3LOS3ALO4lxHnS1R2LF1g1p2lo3LFB2VP3LOS3ALO4lxHnS1R2LF1p2lo3LFB3LOS3ALO4lxHnS1R2LF1p2lo3LFB3LOS3ALO4lxHnS1R2LF1p2lo3LFB3LOS3ALO4lxHnS2LF1g1p3LFB4lxHn2FBS2LF1G1p3LFB4lxHnS2LF1G1p3LFB4lxHnS2LF2ra2sp1g1p3LFB3SPR4lxHn3sp12FB2F02F8S2LF2ra2sp1g1p3LFB3SPR4lxHn3sp12FB2F02F8S2LF2ra2sp1g1p3LFB3SPR4lxHn3sp12FB2F02F8S1R3NS12LF2sp1g1p2lo3LFB3LOS3SLO3ALO3NES4lxHn3sp12H2S1R3NS12LF2sp1g1p2lo3LFB3LOS3SLO3ALO3NES4lxHn3sp12H2S1R3NS12LF2sp1g1p2lo3LFB3LOS3SLO3ALO3NES4lxHn3sp12H2S2LF1G3LFB4lxHnS2LF1G1p3LFB4lxHnS2LF1G1p3LFB4lxHnS1R3HIA1h2LF3LFB4lxHnS1R3HIA1h2LF2sp3LFB3TOP4HTOP4lxHnS2LF1Q3LFB4lxHnS2LF3LFB4lxHn2FBS2LF3LFB4lxHn2FBS2LF3LFB4lxHn2FBS2LF1g1p3LFB4lxHn2FBS2LF1G1p3LFB4lxHnS2LF1g1p3LFB4lxHn2FBS1R3NS12LF2sp1g1p2lo3LFB3SLO3NES4lxHn3sp12H2S1R3NS12LF2sp1g1p2lo3LFB3SLO3NES4lxHn3sp12H2S1R3NS12LF2sp1g1p2lo3LFB3SLO3NES4lxHn3sp12H2S2LF1g1p3LFB4lxHn3sp1S2LF1g1p3LFB4lxHn3sp1S2LF1g1p3LFB4lxHn3sp1S2LF2sp1g1p3LFB4lxHn3sp13H15S2LF2sp1g1p3LFB4lxHn3sp13H15S2LF2sp1g1p3LFB4lxHn3sp13H15S2LF1G1p3LFB4lxHnS2LF1g1p3LFB4lxHn2FBS2LF3LFB4lxHn2FBS1R3HIA1h2LF2sp3LFB3TOP4HTOP4lxHnFFS2LF2sp1g1p2lo3LFB4lxHn3sp13H15S2LF2sp1g1p2lo3LFB4lxHn3sp13H15S2LF2sp1g1p2lo3LFB4lxHn3sp13H15S2LF1g1p3LFB4lxHn2FBS2LF1G1p3LFB4lxHnS2LF1G1p3LFB4lxHnS2LF1g1p3LFB4lxHn2FBS2LF1g1p3LFB4lxHn2FBS1R3NS12LF2sp2lo3LFB3SLO3NES4lxHn3sp12H2S1R3NS12LF2sp1g1p2lo3LFB3SLO3NES4lxHn3sp12H2S1R3NS12LF2sp1p2lo3LFB3SLO3NES4lxHn3sp12H2S1R3NS12LF2sp1g1p2lo3LFB3SLO3NES4lxHn3sp12H2S1R3NS12LF2sp1p2lo3LFB3SLO3NES4lxHn3sp12H2S1R3NS12LF2sp1p2lo3LFB3SLO3NES4lxHn3sp12H2S1R3NS12LF2sp1p2lo3LFB3SLO3NES4lxHn3sp12H2S2LF1g1p3LFB4lxHn2FBS1R3HIA1h2LF2sp2lo3LFB3TOP4HTOPS2LF2lo3LFB4lxHnS2LF1g1p2lo3LFB4lxHnS2LF1p2lo3LFB4lxHnS2LF1g1p2lo3LFB4lxHnS2LF2lo3LFB4lxHnS2LF1p2lo3LFB4lxHnS2LF1p2lo3LFB4lxHnS2LF1p2lo3LFB4lxHnS1R3HIA1h2LF3LFB4lxHnS2LF1G1p3LFB4lxHnS2LF1G1p3LFB4lxHnS2LF1G1p3LFB4lxHnS2LF1G1p3LFB4lxHnS1R2LF1p3slo3LFB4SLO14lxHnS1R2LF1p3slo3LFB4SLO14lxHnS1R2LF1g1p3slo3LFB4SLO14lxHnS1R2LF1p3slo3LFB4SLO14lxHnS1R2LF1p3slo3LFB4SLO14lxHnS1R2LF1g1p3slo3LFB4SLO14lxHnS1R2LF1g1p3slo3LFB4SLO14lxHnS1R2LF1g1p3slo3LFB4SLO14lxHnS1R2LF3slo3LFB4SLO14lxHnS1R2LF3slo3LFB4SLO14lxHnS1R2LF1g1p3slo3LFB4SLO14lxHnS1R2LF1p3slo3LFB4SLO14lxHnS1R2LF1g1p3slo3LFB4SLO14lxHnS1R2LF1g1p3slo3LFB4SLO14lxHnS1R2LF3slo3LFB4SLO14lxHnS1R2LF1g1p3slo3LFB4SLO14lxHnS1R2LF1p3slo3LFB4SLO14lxHnS1R2LF1p3slo3LFB4SLO14lxHnS1R2LF1p3slo3LFB4SLO14lxHnS1R2LF1g1p3slo3LFB4SLO14lxHnS1R2LF3slo3LFB4SLO14lxHnS2LF2sp2lo3LFB4lxHnS1R2LF3LFB3ALO4lxHnS2LF1g1p3LFB4lxHn2FBS1R5NEEDR2LF2sp2lo3LFB3LOS3SLO3ALO3NER4lxHnS1R5NEEDR2LF2sp1g1p2lo3LFB3LOS3SLO3ALO3NER4lxHnS1R5NEEDR2LF2sp1g1p2lo3LFB3LOS3SLO3ALO3NER4lxHnS1R5NEEDR2LF2sp1g1p2lo3LFB3LOS3SLO3ALO3NER4lxHnS1R5NEEDR2LF2sp2lo3LFB3LOS3SLO3ALO3NER4lxHnS2LF2sp1p2lo3LFB4lxHn3sp13H15S2LF2sp1p2lo3LFB4lxHn3sp13H15S2LF2sp1p2lo3LFB4lxHn3sp13H15S2LF2sp2lo3LFB4lxHn3sp13H15S2LF2sp1g1p2lo3LFB4lxHn3sp13H15S2LF2sp1p2lo3LFB4lxHn3sp13H15S2LF2sp1g1p2lo3LFB4lxHn3sp13H15S2LF1g1p3LFB4lxHn2FBS2LF1g1p3LFB4lxHn2FBS2LF1G1p3LFB4lxHnS2LF1G1p3LFB4lxHnS2LF1G1p3LFB4lxHnS2LF1G1p3LFB4lxHnFFS2LF1g1p3LFB4lxHn2FBS2LF1g1p3LFB4lxHn2FBFFFFFFFFFFFFFS2LF2ra2sp1G1p3LFB3SPR4lxHn3sp14SP1R2FB2F04GPOS4GAL8FFFFFFFFFFFFFFFFFFFFS1R2LF2lo3LFB3LOSS2LF3LFB4lxHn3sp1S1R2LF3LFB4lxHnS1R2LF3LFB4lxHnS1R2LF3LFB4lxHnS2LF1G1p3LFB4lxHnS2LF1G3LFB4lxHnS2LF1G1p3LFB4lxHnS2LF1G1p3LFB4lxHnS2LF2ra2sp1G1p3LFB3SPR4lxHn3sp14SP1R2FB2F04GPOS4GAL8S2LF2ra2sp1G1p3LFB3SPR4lxHn3sp14SP1R2FB2F04GPOS4GAL8S1R3HIA1h2LF2sp3slo3LFB3TOP4lxHn2H5S1R3HIA1h2LF2sp1g1p3slo3LFB3TOP4lxHn2H5S1R3HIA1h2LF2sp1p3slo3LFB3TOP4lxHn2H5S1R3HIA1h2LF2sp1p3slo3LFB3TOP4lxHn2H5S1R3HIA1h2LF2sp1p3slo3LFB3TOP4lxHn2H5S1R3HIA1h2LF2sp1g1p3slo3LFB2VP3TOP4lxHn2H5S1R3HIA1h2LF2sp3slo3LFB3TOP4HTOP4lxHnS1R3HIA1h2LF2sp3slo3LFB3TOP4lxHn2H5S1R3HIA1h2LF2sp1g1p3slo3LFB3TOP4lxHn2H5S1R3HIA1h2LF2sp1p3slo3LFB3TOP4lxHn2H5S1R3HIA1h2LF2sp1g1p3slo3LFB2VP3TOP4lxHn2H5S1R3HIA1h2LF2sp1g1p3slo3LFB2VP3TOP4lxHn2H5S1R3HIA1h2LF2sp1p3slo3LFB3TOP4lxHn2H5S1R3HIA1h2LF2sp1p3slo3LFB3TOP4lxHn2H5S1R3HIA1h2LF2sp1g1p3slo3LFB3TOP4lxHn2H5S1R3HIA1h2LF2sp1p3slo3LFB3TOP4lxHn2H5S1R3HIA1h2LF2sp1p3slo3LFB3TOP4lxHn2H5S1R3HIA1h2LF2sp1g1p3slo3LFB3TOP4lxHn2H5S1R3HIA1h2LF2sp1g1p3slo3LFB2VP3TOP4lxHn2H5S1R3HIA1h2LF2sp1g1p3slo3LFB2VP3TOP4lxHn2H5S1R3NS12LF2sp2lo3LFB3LOS3SLO3NES4lxHn3sp13SP1S2LF3LFB4lxHn2FBS2LF3LFB4lxHn2FBS2LF3LFB4lxHn2FBS2LF1G1p3LFB4lxHnFS2LF2sp2lo3LFB4lxHn3sp13H15S2LF2sp1g1p2lo3LFB4lxHn3sp13H15S2LF2sp1p2lo3LFB4lxHn3sp13H15S2LF2sp1g1p2lo3LFB4lxHn3sp13H15S2LF2sp1p2lo3LFB4lxHn3sp13H15S2LF2sp1p2lo3LFB4lxHn3sp13H15S2LF2sp1p2lo3LFB4lxHn3sp13H15S2LF1g1p3LFB4lxHn3sp14SP1RS2LF1g1p3LFB4lxHn3sp14SP1RS2LF1g1p3LFB4lxHn3sp14SP1RS2LF3LFB4lxHn3sp14SP1RS2LF1p3LFB4lxHn3sp14SP1RS2LF1p3LFB4lxHn3sp14SP1RS2LF1g1p3LFB4lxHn3sp14SP1RS2LF1p3LFB4lxHn3sp14SP1RS2LF1p3LFB4lxHn3sp14SP1RS2LF1g1p3LFB4lxHn3sp14SP1RS2LF3LFB4lxHn3sp14SP1RS2LF1g1p3LFB4lxHn2FB2F0S2LF1g1p3LFB4lxHn2FB2F0S2LF3LFB4lxHn2FB2F0S2LF1g1p3LFB4lxHn2FB2F0S2LF1p3LFB4lxHn2FB2F0S2LF1g1p3LFB4lxHn2FB2F0S2LF1g1p3LFB4lxHn2FB2F0S2LF1p3LFB4lxHn2FB2F0S2LF1p3LFB4lxHn2FB2F0S2LF1p3LFB4lxHn2FB2F0S2LF1g1p3LFB4lxHn2FB2F0S2LF1g1p3LFB4lxHn2FB2F0S2LF1g1p3LFB4lxHn2FB2F0". (* [comment removed for export] *)
  Lemma pro_walk : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(57.$9.Vm,Vlo,(2?.&40.Vsp,))(58.$9.(32.VR,)(33.$9.VR,VHIA,Vh,)$59.(5:.(5;.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(47.&40.VG,)(47.&40.VQ,)R;.R:.R9.R8.R7.R6.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R5.R4.R3.R2.)VF,(47.&40.$5<.)Vfc,(5=.(2.&40.))Vm,(5>.$9.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros ST. unfold A_ECP_CHECK_PUBKEY.
    destruct (ck_op_pt (pt_X p) ltac:(left; reflexivity)) as (OPX & NSX & NNX & _).
    destruct (ck_op_pt (pt_Y p) ltac:(right; left; reflexivity)) as (OPY & NSY & NNY & _).
    destruct (ck_op_pt (pt_Z p) ltac:(right; right; left; reflexivity)) as (OPZ & NSZ & NNZ & _).
    flat constr:(ck_op_P) 2%nat. flclear ck_op_P. intros OPP EAP.
    flat constr:(PAT) 4%nat. intros EAX EAY EAZ _.
    pose proof ck_G_at as GATK.
    pose proof (alloc_ceiling_lo (L := arl_L R)) as ACL.
    rt_facts. pose proof MI as MIe. pose proof HH as HHe.
    pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| qlia| qlia]).
    pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
    pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (arl_stklo R) [] HH ltac:(clear; lia)) as PRES.
    flat constr:(IMG') 3%nat. flclear IMG'. intros EGOT ELO EHI.
    (* [comment removed for export] *)
    zstep. carve_frame 96%nat ST.
    (* [comment removed for export] *)
    pose proof HH as HH_lx. lazymatch type of HH with ?T => change (id T) in HH end.
    pose proof GOB as GOB_lx. lazymatch type of GOB with ?T => change (id T) in GOB end.
    pose proof QOB as QOB_lx. lazymatch type of QOB with ?T => change (id T) in QOB end.
    pose proof MC0 as MC0_lx. lazymatch type of MC0 with ?T => change (id T) in MC0 end.
    pose proof SSH as SSH_lx. lazymatch type of SSH with ?T => change (id T) in SSH end.
    pose proof MI as MI_lx. lazymatch type of MI with ?T => change (id T) in MI end.
    (* [comment removed for export] *)
    pose proof (hm_abase asegs R HIA h LB LF m HH) as AB.
    pose proof (abase_got _ _ _ AB) as GOT; pose proof (abase_gsb _ _ _ AB) as GSB.
    flat constr:((hm_auar asegs R HIA h LB LF m HH)) 2%nat. intros UGOT UFLAG.
    pose proof (hm_flag_img asegs R HIA h LB LF m HH) as FLIMG.
    rewrite EGOT in GOT. rewrite UARG in UGOT.
    pose (lxi := lxA_img (arl_AL R) IMG).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52af8] [] 80%N). lx_tree.
    all: lxr_leaf; lxe_leaf_gc.
    lx_carry. try clear GOT GSB UGOT UFLAG AB FLIMG.
    lx_align32 sp1.
    match goal with Hm : sp1 mod 32 = 0 |- _ => rename Hm into SP1M end.
    assert (SP1 : bv_unsigned sp - 112 <= sp1 <= bv_unsigned sp - 96)
      by (match goal with H1 : 0 <= sp1 + _, H2 : 0 <= - sp1 + _ |- _ => clear - H1 H2 SP1M SPA SPR end; Z.div_mod_to_equations; lia).
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NEEDR NER; lia).
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
    try match goal with H : stk _ m1 lo (bv_unsigned sp + -96) |- _ => rename H into ST end.
    destruct (stk_split asegs m1 lo sp1 (bv_unsigned sp + -96) ST ltac:(clear - SP1 SLO NS1 NES; lia)) as [ST1 ST2]. clear ST.
    replace (Z_to_bv 64 338680) with (Z_to_bv 64 (arl_smalloc R 1)) by (rewrite SM1; reflexivity).
    lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
    callrt sp1 (eapply (art_smalloc asegs R HIA 1) with (lo := lo) (sz := 128); rewrite ?(unsigned_lit sp1) by exact SP1R;
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
    change (64 * 2 ^ 1) with 128 in *. change (8 * 2 ^ 1) with 16 in FSH. change (Z.to_nat 128) with 128%nat in FRM. change (Z.to_nat 16) with 16%nat in FSH.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
    (* [comment removed for export] *)
    destruct (frame_factsA R HIA CS h1 LB LF m3 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (128 / 8) with 16 in SBND, APS. change (128 - 40) with 88 in IND.
    pose proof (art_stk_high asegs R HIA) as STKH.
    (* [comment removed for export] *)
    lazymatch goal with FRx : rw_cells _ m3 (bv_unsigned sp + -96) _ |- _ => chunk_split FRx 1%nat FRa SAVE end.
    replace (bv_unsigned sp + -96 + 8) with (bv_unsigned sp + -88) in SAVE by (clear; lia).
    lazymatch goal with STx : stk _ m3 sp1 (bv_unsigned sp + -96) |- _ => release_frame FRa STx (bv_unsigned sp + -88); rename STx into STJ end.
    destruct (stk_split asegs m3 sp1 (sp1 + 8) (bv_unsigned sp + -88) STJ ltac:(clear - SP1; lia)) as [STlo SThi]. clear STJ.
    destruct (stk_carve asegs m3 sp1 (sp1 + 8) 8 STlo ltac:(clear; lia)) as [_ [jslot SLOT]].
    replace (sp1 + 8 - Z.of_nat 8) with sp1 in SLOT by (clear; lia). clear STlo.
    cb8_to_c8 SLOT (@nil cell).
    (* [comment removed for export] *)
    apply (rw_cells_split_CB asegs m3 FB [] 128 junkf [] [8; 8; 8; 8; 16; 16; 16; 16; 16; 16]%nat) in FRM; [| reflexivity].
    cbn [mk_CB_cells app] in FRM.
    chunk_split FRM 3%nat FHD FRM1. chunk_split FRM1 1%nat FLNK FRM2. chunk_split FRM2 1%nat YYB FRM3. chunk_split FRM3 1%nat RZ1 FRM4.
    chunk_split FRM4 1%nat RHB FRM5. chunk_split FRM5 1%nat RZ2 FRM6. chunk_split FRM6 1%nat XMB FREST.
    lazymatch type of YYB with rw_cells _ _ ?a _ => replace a with (FB + 32) in YYB by (clear; lia) end.
    lazymatch type of RHB with rw_cells _ _ ?a _ => replace a with (FB + 64) in RHB by (clear; lia) end.
    lazymatch type of XMB with rw_cells _ _ ?a _ => replace a with (FB + 96) in XMB by (clear; lia) end.
    lazymatch type of YYB with rw_cells _ _ _ [CB 16 ?j] => set (jyy := j) in YYB; clearbody jyy end.
    lazymatch type of RHB with rw_cells _ _ _ [CB 16 ?j] => set (jrh := j) in RHB; clearbody jrh end.
    lazymatch type of XMB with rw_cells _ _ _ [CB 16 ?j] => set (jxm := j) in XMB; clearbody jxm end.
    clear FLNK FREST RZ1 RZ2.
    cb8_to_c8 FHD (@nil cell).
    cbn [zcells] in FSH.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52af8; 0x9b904; 0x9b998; 0x9bcf4; 0x9c740; 0x9cbec; 0x9d5b4; 0x9d8bc; 0x9e720; 0xcc838; 0xcc9dc; 0xcbc98; 0xcbc44; 0xcbe6c; 0xcbe78; 0xcbe80; 0xcbe8c; 0xcbea0; 0xcbecc; 0xcbed8; 0xcbef4; 0xcbf10; 0xcbf14; 0xcbf24; 0xcbf2c; 0xcbf34; 0xcbf60; 0xcbf74; 0xcbf88; 0xcbf90; 0xcbf98; 0xcbfa0; 0xcbfc0; 0xcbfe4] [(0xcbcb4, DJoin); (0xcbcd0, DJoin); (0xcbcd8, DJoin); (0xcbce0, DJoin); (0xcbe08, DJoin); (0xcbe50, DJoin)] 400%N). lx_tree.
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
    repeat match goal with H : context [al_sb AL + Z.shiftr FB 3] |- _ => replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) in H by (clear; lia) end.
    try replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) by (clear; lia).
    try rewrite ?EAX; try rewrite ?EAY; try rewrite ?EAZ.
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSHX end.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mq1 end.
    lazymatch goal with HHc : HM _ _ _ h1 _ _ mq1, MIc : mem_inv _ mq1 |- _ =>
      destruct (ck_op_at (pt_Z p) OPZ h1 _ mq1 sp1 (presW_presA asegs R HIA h LB LF _ _ _ m mq1 PRES) MIc HHc Ehcs ltac:(clear - SP1; lia)) as (Ma & Oa & OLa & PPa & SSa & SLa);
      pose proof (hm_abase asegs R HIA h1 _ _ mq1 HHc) as ABq end.
    rewrite EAZ in Oa, SSa.
    pose proof (A_mpi_cmp_int_spec AL IMG) as SPQ. unfold mpi_cmp_int_stmtA, A_MPI_CMP_INT_E in SPQ.
    callxA_sp sp1
      (eapply SPQ with (CS := CS) (LB := LB) (dX := (pt_Z p)) (z := 1) (lo := lo);
       rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?EAZ;
       first [ exact Ma | exact Oa | exact OLa | exact PPa | exact SSa | exact SLa | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | reflexivity | eassumption
             | (clear; lia)
             | (clear - LOS ALO ACV; lia)
             | (clear - SLO SP1 NER NEEDR; lia)
             | (clear - SP1M; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia])
             | (f_equal; clear; lia)
             | match goal with |- ?g => idtac "CMPZ-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-CMPZ-SIDE:" g end.
    clear Ma Oa OLa PPa SSa SLa ABq.
    (* [comment removed for export] *)
    zstep. if_cases KZ.
    2:{ (* [comment removed for export] *)
      zstep. zstep.
      apply evtA_done. unfold S1P.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx, 0, (-19584) end.
      do 24 eexists.
      split; [reflexivity|]. split; [left; reflexivity|]. split; [intros _; split; [apply bv_eq; vm_compute; reflexivity| clear; lia]|].
      split; [intros C; discriminate C|]. split; [intros C; discriminate C|].
      split; [exact SP1|]. split; [exact SP1M|].
      split; [eassumption|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
      split; [exact F64|]. split; [exact FRSH|].
      split; [exact FHD|]. split; [exact FSHX|].
      split; [exact SAVE|]. split; [exact SLOT|]. split; [exact SThi|].
      split; [assumption|]. split; [assumption|]. split; [exact PRES| first [exact SSH | assumption]]. }
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg end.
    lazymatch goal with HHc : HM _ _ _ h1 _ _ mg, MIc : mem_inv _ mg |- _ =>
      (flat constr:((GATK h1 _ mg (presW_presA asegs R HIA h LB LF _ _ _ m mg PRES) MIc HHc Ehcs)) 10%nat; intros GOBg GHDg CGX CGY GTLg GXR GYR GPOS GHI GAL8) end.
    unfold mpi_cells in CGX, CGY. unfold grp_head_cells in GHDg. unfold grp_tail_cells in GTLg.
    (* [comment removed for export] *)
    do 6 zstep.
    zstep. if_cases KX; zify_cond KX; rewrite ?Z.mod_small in KX by exact GXR.
    { (* [comment removed for export] *)
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52af8; 0x9b904; 0x9b998; 0x9bcf4; 0x9c740; 0x9cbec; 0x9d5b4; 0x9d8bc; 0x9e720; 0xcc838; 0xcc9dc; 0xcbc98; 0xcbc44; 0xcbe6c; 0xcbe78; 0xcbe80; 0xcbe8c; 0xcbea0; 0xcbecc; 0xcbed8; 0xcbef4; 0xcbf10; 0xcbf14; 0xcbf24; 0xcbf2c; 0xcbf34; 0xcbf60; 0xcbf74; 0xcbf88; 0xcbf90; 0xcbf98; 0xcbfa0; 0xcbfc0; 0xcbfe4] [(0xcbcb4, DJoin); (0xcbcd0, DJoin); (0xcbcd8, DJoin); (0xcbce0, DJoin); (0xcbe08, DJoin); (0xcbe50, DJoin)] 400%N). lx_tree.
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
    repeat match goal with H : context [al_sb AL + Z.shiftr FB 3] |- _ => replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) in H by (clear; lia) end.
    try replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) by (clear; lia).
    try rewrite ?EAX; try rewrite ?EAY; try rewrite ?EAZ.
      apply evtA_done. unfold S1P.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx, 0, (-20352) end.
      do 24 eexists.
      split; [reflexivity|]. split; [left; reflexivity|]. split; [intros _; split; [apply bv_eq; vm_compute; reflexivity| clear; lia]|].
      split; [intros C; discriminate C|]. split; [intros C; discriminate C|].
      split; [exact SP1|]. split; [exact SP1M|].
      split; [eassumption|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
      split; [exact F64|]. split; [exact FRSH|].
      split; [exact FHD|]. split; [exact FSHX|].
      split; [exact SAVE|]. split; [exact SLOT|]. split; [exact SThi|].
      split; [assumption|]. split; [assumption|]. split; [exact PRES| first [exact SSH | assumption]]. }
    (* [comment removed for export] *)
    do 6 zstep.
    zstep. if_cases KY; zify_cond KY; rewrite ?Z.mod_small in KY by exact GYR.
    2:{
    assert (GH1 : g_h g = 1) by (destruct GKIND as [(E & _)|(_ & E)]; [exact E| exfalso; exact (KY E)]).
    (* [comment removed for export] *)
    do 4 zstep.
    zstep. if_cases KY2; zify_cond KY2; rewrite ?Z.mod_small in KY2 by exact GYR; [exfalso; exact (KY KY2)|].
    clear GOBg GHDg CGX CGY GTLg GXR GYR GPOS GHI GAL8.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52af8; 0x9b904; 0x9b998; 0x9bcf4; 0x9c740; 0x9cbec; 0x9d5b4; 0x9d8bc; 0x9e720; 0xcc838; 0xcc9dc; 0xcbc98; 0xcbc44; 0xcbe6c; 0xcbe78; 0xcbe80; 0xcbe8c; 0xcbea0; 0xcbecc; 0xcbed8; 0xcbef4; 0xcbf10; 0xcbf14; 0xcbf24; 0xcbf2c; 0xcbf34; 0xcbf60; 0xcbf74; 0xcbf88; 0xcbf90; 0xcbf98; 0xcbfa0; 0xcbfc0; 0xcbfe4] [(0xcbcb4, DJoin); (0xcbcd0, DJoin); (0xcbcd8, DJoin); (0xcbce0, DJoin); (0xcbe08, DJoin); (0xcbe50, DJoin)] 400%N). lx_tree.
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
    repeat match goal with H : context [al_sb AL + Z.shiftr FB 3] |- _ => replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) in H by (clear; lia) end.
    try replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) by (clear; lia).
    try rewrite ?EAX; try rewrite ?EAY; try rewrite ?EAZ.
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSHS end.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mq2 end.
    lazymatch goal with HHc : HM _ _ _ h1 _ _ mq2, MIc : mem_inv _ mq2 |- _ =>
      destruct (ck_op_at (pt_X p) OPX h1 _ mq2 sp1 (presW_presA asegs R HIA h LB LF _ _ _ m mq2 PRES) MIc HHc Ehcs ltac:(clear - SP1; lia)) as (Ma & Oa & OLa & PPa & SSa & SLa);
      pose proof (hm_abase asegs R HIA h1 _ _ mq2 HHc) as ABq end.
    rewrite EAX in Oa, SSa.
    pose proof (A_mpi_cmp_int_spec AL IMG) as SPQ. unfold mpi_cmp_int_stmtA, A_MPI_CMP_INT_E in SPQ.
    callxA_sp sp1
      (eapply SPQ with (CS := CS) (LB := LB) (dX := (pt_X p)) (z := 0) (lo := lo);
       rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?EAX;
       first [ exact Ma | exact Oa | exact OLa | exact PPa | exact SSa | exact SLa | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | reflexivity | eassumption
             | (clear; lia)
             | (clear - LOS ALO ACV; lia)
             | (clear - SLO SP1 NER NEEDR; lia)
             | (clear - SP1M; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia])
             | (f_equal; clear; lia)
             | match goal with |- ?g => idtac "CMPX0-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-CMPX0-SIDE:" g end.
    clear Ma Oa OLa PPa SSa SLa ABq.
    (* [comment removed for export] *)
    zstep. if_cases K1.
    {
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52af8; 0x9b904; 0x9b998; 0x9bcf4; 0x9c740; 0x9cbec; 0x9d5b4; 0x9d8bc; 0x9e720; 0xcc838; 0xcc9dc; 0xcbc98; 0xcbc44; 0xcbe6c; 0xcbe78; 0xcbe80; 0xcbe8c; 0xcbea0; 0xcbecc; 0xcbed8; 0xcbef4; 0xcbf10; 0xcbf14; 0xcbf24; 0xcbf2c; 0xcbf34; 0xcbf60; 0xcbf74; 0xcbf88; 0xcbf90; 0xcbf98; 0xcbfa0; 0xcbfc0; 0xcbfe4] [(0xcbcb4, DJoin); (0xcbcd0, DJoin); (0xcbcd8, DJoin); (0xcbce0, DJoin); (0xcbe08, DJoin); (0xcbe50, DJoin)] 400%N). lx_tree.
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
    repeat match goal with H : context [al_sb AL + Z.shiftr FB 3] |- _ => replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) in H by (clear; lia) end.
    try replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) by (clear; lia).
    try rewrite ?EAX; try rewrite ?EAY; try rewrite ?EAZ.
      match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSHR end.
      apply evtA_done. unfold S1P.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx, 0, (-19584) end.
      do 24 eexists.
      split; [reflexivity|]. split; [left; reflexivity|]. split; [intros _; split; [apply bv_eq; vm_compute; reflexivity| clear; lia]|].
      split; [intros C; discriminate C|]. split; [intros C; discriminate C|].
      split; [exact SP1|]. split; [exact SP1M|].
      split; [eassumption|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
      split; [exact F64|]. split; [exact FRSH|].
      split; [exact FHD|]. split; [exact FSHR|].
      split; [exact SAVE|]. split; [exact SLOT|]. split; [exact SThi|].
      split; [assumption|]. split; [assumption|]. split; [exact PRES| first [exact SSH | assumption]]. }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52af8; 0x9b904; 0x9b998; 0x9bcf4; 0x9c740; 0x9cbec; 0x9d5b4; 0x9d8bc; 0x9e720; 0xcc838; 0xcc9dc; 0xcbc98; 0xcbc44; 0xcbe6c; 0xcbe78; 0xcbe80; 0xcbe8c; 0xcbea0; 0xcbecc; 0xcbed8; 0xcbef4; 0xcbf10; 0xcbf14; 0xcbf24; 0xcbf2c; 0xcbf34; 0xcbf60; 0xcbf74; 0xcbf88; 0xcbf90; 0xcbf98; 0xcbfa0; 0xcbfc0; 0xcbfe4] [(0xcbcb4, DJoin); (0xcbcd0, DJoin); (0xcbcd8, DJoin); (0xcbce0, DJoin); (0xcbe08, DJoin); (0xcbe50, DJoin)] 400%N). lx_tree.
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
    repeat match goal with H : context [al_sb AL + Z.shiftr FB 3] |- _ => replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) in H by (clear; lia) end.
    try replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) by (clear; lia).
    try rewrite ?EAX; try rewrite ?EAY; try rewrite ?EAZ.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mq3 end.
    lazymatch goal with HHc : HM _ _ _ h1 _ _ mq3, MIc : mem_inv _ mq3 |- _ =>
      destruct (ck_op_at (pt_Y p) OPY h1 _ mq3 sp1 (presW_presA asegs R HIA h LB LF _ _ _ m mq3 PRES) MIc HHc Ehcs ltac:(clear - SP1; lia)) as (Ma & Oa & OLa & PPa & SSa & SLa);
      pose proof (hm_abase asegs R HIA h1 _ _ mq3 HHc) as ABq end.
    rewrite EAY in Oa, SSa.
    pose proof (A_mpi_cmp_int_spec AL IMG) as SPQ. unfold mpi_cmp_int_stmtA, A_MPI_CMP_INT_E in SPQ.
    callxA_sp sp1
      (eapply SPQ with (CS := CS) (LB := LB) (dX := (pt_Y p)) (z := 0) (lo := lo);
       rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?EAY;
       first [ exact Ma | exact Oa | exact OLa | exact PPa | exact SSa | exact SLa | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | reflexivity | eassumption
             | (clear; lia)
             | (clear - LOS ALO ACV; lia)
             | (clear - SLO SP1 NER NEEDR; lia)
             | (clear - SP1M; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia])
             | (f_equal; clear; lia)
             | match goal with |- ?g => idtac "CMPY0-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-CMPY0-SIDE:" g end.
    clear Ma Oa OLa PPa SSa SLa ABq.
    (* [comment removed for export] *)
    do 3 zstep. zstep. if_cases K2.
    {
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52af8; 0x9b904; 0x9b998; 0x9bcf4; 0x9c740; 0x9cbec; 0x9d5b4; 0x9d8bc; 0x9e720; 0xcc838; 0xcc9dc; 0xcbc98; 0xcbc44; 0xcbe6c; 0xcbe78; 0xcbe80; 0xcbe8c; 0xcbea0; 0xcbecc; 0xcbed8; 0xcbef4; 0xcbf10; 0xcbf14; 0xcbf24; 0xcbf2c; 0xcbf34; 0xcbf60; 0xcbf74; 0xcbf88; 0xcbf90; 0xcbf98; 0xcbfa0; 0xcbfc0; 0xcbfe4] [(0xcbcb4, DJoin); (0xcbcd0, DJoin); (0xcbcd8, DJoin); (0xcbce0, DJoin); (0xcbe08, DJoin); (0xcbe50, DJoin)] 400%N). lx_tree.
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
    repeat match goal with H : context [al_sb AL + Z.shiftr FB 3] |- _ => replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) in H by (clear; lia) end.
    try replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) by (clear; lia).
    try rewrite ?EAX; try rewrite ?EAY; try rewrite ?EAZ.
      match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSHR end.
      apply evtA_done. unfold S1P.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx, 0, (-19584) end.
      do 24 eexists.
      split; [reflexivity|]. split; [left; reflexivity|]. split; [intros _; split; [apply bv_eq; vm_compute; reflexivity| clear; lia]|].
      split; [intros C; discriminate C|]. split; [intros C; discriminate C|].
      split; [exact SP1|]. split; [exact SP1M|].
      split; [eassumption|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
      split; [exact F64|]. split; [exact FRSH|].
      split; [exact FHD|]. split; [exact FSHR|].
      split; [exact SAVE|]. split; [exact SLOT|]. split; [exact SThi|].
      split; [assumption|]. split; [assumption|]. split; [exact PRES| first [exact SSH | assumption]]. }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52af8; 0x9b904; 0x9b998; 0x9bcf4; 0x9c740; 0x9cbec; 0x9d5b4; 0x9d8bc; 0x9e720; 0xcc838; 0xcc9dc; 0xcbc98; 0xcbc44; 0xcbe6c; 0xcbe78; 0xcbe80; 0xcbe8c; 0xcbea0; 0xcbecc; 0xcbed8; 0xcbef4; 0xcbf10; 0xcbf14; 0xcbf24; 0xcbf2c; 0xcbf34; 0xcbf60; 0xcbf74; 0xcbf88; 0xcbf90; 0xcbf98; 0xcbfa0; 0xcbfc0; 0xcbfe4] [(0xcbcb4, DJoin); (0xcbcd0, DJoin); (0xcbcd8, DJoin); (0xcbce0, DJoin); (0xcbe08, DJoin); (0xcbe50, DJoin)] 400%N). lx_tree.
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
    repeat match goal with H : context [al_sb AL + Z.shiftr FB 3] |- _ => replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) in H by (clear; lia) end.
    try replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) by (clear; lia).
    try rewrite ?EAX; try rewrite ?EAY; try rewrite ?EAZ.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mq4 end.
    lazymatch goal with HHc : HM _ _ _ h1 _ _ mq4, MIc : mem_inv _ mq4 |- _ =>
      destruct (ck_op_at (pt_X p) OPX h1 _ mq4 sp1 (presW_presA asegs R HIA h LB LF _ _ _ m mq4 PRES) MIc HHc Ehcs ltac:(clear - SP1; lia)) as (Ma & Oa & OLa & PPa & SSa & SLa);
      pose proof (hm_abase asegs R HIA h1 _ _ mq4 HHc) as ABq end.
    rewrite EAX in Oa, SSa.
    lazymatch goal with HHc : HM _ _ _ h1 _ _ mq4, MIc : mem_inv _ mq4 |- _ =>
      destruct (ck_op_at dP OPP h1 _ mq4 sp1 (presW_presA asegs R HIA h LB LF _ _ _ m mq4 PRES) MIc HHc Ehcs ltac:(clear - SP1; lia)) as (Mb & Ob & OLb & PPb & SSb & SLb) end.
    rewrite EAP in Ob, SSb.
    pose proof (A_mpi_cmp_mpi_spec AL IMG) as SPQ. unfold mpi_cmp_mpi_stmtA, A_MPI_CMP_MPI_E in SPQ.
    callxA_sp sp1
      (eapply SPQ with (CS := CS) (LB := LB) (dX := (pt_X p)) (dY := dP) (lo := lo);
       rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?EAX, ?EAP;
       first [ exact Ma | exact Oa | exact OLa | exact PPa | exact SSa | exact SLa | exact Mb | exact Ob | exact OLb | exact PPb | exact SSb | exact SLb
             | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | reflexivity | eassumption
             | (clear; lia)
             | (clear - LOS ALO ACV; lia)
             | (clear - SLO SP1 NER NEEDR; lia)
             | (clear - SP1M; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia])
             | (f_equal; clear; lia)
             | match goal with |- ?g => idtac "CMPXP-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-CMPXP-SIDE:" g end.
    clear Ma Oa OLa PPa SSa SLa Mb Ob OLb PPb SSb SLb ABq.
    (* [comment removed for export] *)
    do 2 zstep. zstep. if_cases K3.
    {
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52af8; 0x9b904; 0x9b998; 0x9bcf4; 0x9c740; 0x9cbec; 0x9d5b4; 0x9d8bc; 0x9e720; 0xcc838; 0xcc9dc; 0xcbc98; 0xcbc44; 0xcbe6c; 0xcbe78; 0xcbe80; 0xcbe8c; 0xcbea0; 0xcbecc; 0xcbed8; 0xcbef4; 0xcbf10; 0xcbf14; 0xcbf24; 0xcbf2c; 0xcbf34; 0xcbf60; 0xcbf74; 0xcbf88; 0xcbf90; 0xcbf98; 0xcbfa0; 0xcbfc0; 0xcbfe4] [(0xcbcb4, DJoin); (0xcbcd0, DJoin); (0xcbcd8, DJoin); (0xcbce0, DJoin); (0xcbe08, DJoin); (0xcbe50, DJoin)] 400%N). lx_tree.
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
    repeat match goal with H : context [al_sb AL + Z.shiftr FB 3] |- _ => replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) in H by (clear; lia) end.
    try replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) by (clear; lia).
    try rewrite ?EAX; try rewrite ?EAY; try rewrite ?EAZ.
      match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSHR end.
      apply evtA_done. unfold S1P.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx, 0, (-19584) end.
      do 24 eexists.
      split; [reflexivity|]. split; [left; reflexivity|]. split; [intros _; split; [apply bv_eq; vm_compute; reflexivity| clear; lia]|].
      split; [intros C; discriminate C|]. split; [intros C; discriminate C|].
      split; [exact SP1|]. split; [exact SP1M|].
      split; [eassumption|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
      split; [exact F64|]. split; [exact FRSH|].
      split; [exact FHD|]. split; [exact FSHR|].
      split; [exact SAVE|]. split; [exact SLOT|]. split; [exact SThi|].
      split; [assumption|]. split; [assumption|]. split; [exact PRES| first [exact SSH | assumption]]. }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52af8; 0x9b904; 0x9b998; 0x9bcf4; 0x9c740; 0x9cbec; 0x9d5b4; 0x9d8bc; 0x9e720; 0xcc838; 0xcc9dc; 0xcbc98; 0xcbc44; 0xcbe6c; 0xcbe78; 0xcbe80; 0xcbe8c; 0xcbea0; 0xcbecc; 0xcbed8; 0xcbef4; 0xcbf10; 0xcbf14; 0xcbf24; 0xcbf2c; 0xcbf34; 0xcbf60; 0xcbf74; 0xcbf88; 0xcbf90; 0xcbf98; 0xcbfa0; 0xcbfc0; 0xcbfe4] [(0xcbcb4, DJoin); (0xcbcd0, DJoin); (0xcbcd8, DJoin); (0xcbce0, DJoin); (0xcbe08, DJoin); (0xcbe50, DJoin)] 400%N). lx_tree.
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
    repeat match goal with H : context [al_sb AL + Z.shiftr FB 3] |- _ => replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) in H by (clear; lia) end.
    try replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) by (clear; lia).
    try rewrite ?EAX; try rewrite ?EAY; try rewrite ?EAZ.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mq5 end.
    lazymatch goal with HHc : HM _ _ _ h1 _ _ mq5, MIc : mem_inv _ mq5 |- _ =>
      destruct (ck_op_at (pt_Y p) OPY h1 _ mq5 sp1 (presW_presA asegs R HIA h LB LF _ _ _ m mq5 PRES) MIc HHc Ehcs ltac:(clear - SP1; lia)) as (Ma & Oa & OLa & PPa & SSa & SLa);
      pose proof (hm_abase asegs R HIA h1 _ _ mq5 HHc) as ABq end.
    rewrite EAY in Oa, SSa.
    lazymatch goal with HHc : HM _ _ _ h1 _ _ mq5, MIc : mem_inv _ mq5 |- _ =>
      destruct (ck_op_at dP OPP h1 _ mq5 sp1 (presW_presA asegs R HIA h LB LF _ _ _ m mq5 PRES) MIc HHc Ehcs ltac:(clear - SP1; lia)) as (Mb & Ob & OLb & PPb & SSb & SLb) end.
    rewrite EAP in Ob, SSb.
    pose proof (A_mpi_cmp_mpi_spec AL IMG) as SPQ. unfold mpi_cmp_mpi_stmtA, A_MPI_CMP_MPI_E in SPQ.
    callxA_sp sp1
      (eapply SPQ with (CS := CS) (LB := LB) (dX := (pt_Y p)) (dY := dP) (lo := lo);
       rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?EAY, ?EAP;
       first [ exact Ma | exact Oa | exact OLa | exact PPa | exact SSa | exact SLa | exact Mb | exact Ob | exact OLb | exact PPb | exact SSb | exact SLb
             | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | reflexivity | eassumption
             | (clear; lia)
             | (clear - LOS ALO ACV; lia)
             | (clear - SLO SP1 NER NEEDR; lia)
             | (clear - SP1M; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia])
             | (f_equal; clear; lia)
             | match goal with |- ?g => idtac "CMPYP-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-CMPYP-SIDE:" g end.
    clear Ma Oa OLa PPa SSa SLa Mb Ob OLb PPb SSb SLb ABq.
    (* [comment removed for export] *)
    zstep. if_cases K4.
    2:{
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52af8; 0x9b904; 0x9b998; 0x9bcf4; 0x9c740; 0x9cbec; 0x9d5b4; 0x9d8bc; 0x9e720; 0xcc838; 0xcc9dc; 0xcbc98; 0xcbc44; 0xcbe6c; 0xcbe78; 0xcbe80; 0xcbe8c; 0xcbea0; 0xcbecc; 0xcbed8; 0xcbef4; 0xcbf10; 0xcbf14; 0xcbf24; 0xcbf2c; 0xcbf34; 0xcbf60; 0xcbf74; 0xcbf88; 0xcbf90; 0xcbf98; 0xcbfa0; 0xcbfc0; 0xcbfe4] [(0xcbcb4, DJoin); (0xcbcd0, DJoin); (0xcbcd8, DJoin); (0xcbce0, DJoin); (0xcbe08, DJoin); (0xcbe50, DJoin)] 400%N). lx_tree.
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
    repeat match goal with H : context [al_sb AL + Z.shiftr FB 3] |- _ => replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) in H by (clear; lia) end.
    try replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) by (clear; lia).
    try rewrite ?EAX; try rewrite ?EAY; try rewrite ?EAZ.
      match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSHR end.
      apply evtA_done. unfold S1P.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx, 0, (-19584) end.
      do 24 eexists.
      split; [reflexivity|]. split; [left; reflexivity|]. split; [intros _; split; [apply bv_eq; vm_compute; reflexivity| clear; lia]|].
      split; [intros C; discriminate C|]. split; [intros C; discriminate C|].
      split; [exact SP1|]. split; [exact SP1M|].
      split; [eassumption|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
      split; [exact F64|]. split; [exact FRSH|].
      split; [exact FHD|]. split; [exact FSHR|].
      split; [exact SAVE|]. split; [exact SLOT|]. split; [exact SThi|].
      split; [assumption|]. split; [assumption|]. split; [exact PRES| first [exact SSH | assumption]]. }
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52af8; 0x9b904; 0x9b998; 0x9bcf4; 0x9c740; 0x9cbec; 0x9d5b4; 0x9d8bc; 0x9e720; 0xcc838; 0xcc9dc; 0xcbc98; 0xcbc44; 0xcbe6c; 0xcbe78; 0xcbe80; 0xcbe8c; 0xcbea0; 0xcbecc; 0xcbed8; 0xcbef4; 0xcbf10; 0xcbf14; 0xcbf24; 0xcbf2c; 0xcbf34; 0xcbf60; 0xcbf74; 0xcbf88; 0xcbf90; 0xcbf98; 0xcbfa0; 0xcbfc0; 0xcbfe4] [(0xcbcb4, DJoin); (0xcbcd0, DJoin); (0xcbcd8, DJoin); (0xcbce0, DJoin); (0xcbe08, DJoin); (0xcbe50, DJoin)] 400%N). lx_tree.
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
    repeat match goal with H : context [al_sb AL + Z.shiftr FB 3] |- _ => replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) in H by (clear; lia) end.
    try replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) by (clear; lia).
    try rewrite ?EAX; try rewrite ?EAY; try rewrite ?EAZ.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mi1 end.
    frame_aobj FSHS (FB + 32) 2%nat as OEX.
    apply (mpi_cells_of_bytes asegs) in YYB.
    lazymatch goal with HHc : HM _ _ _ h1 _ _ mi1 |- _ => pose proof (hm_abase asegs R HIA h1 _ _ mi1 HHc) as ABq end.
    pose proof (A_mpi_init_spec AL IMG) as SPI. unfold mpi_init_stmtA, A_MPI_INIT_ in SPI.
    callxA_sp sp1
      (eapply SPI with (CS := CS) (X := FB + 32) (lo := lo);
       rewrite ?(unsigned_lit sp1) by exact SP1R;
       first [ exact YYB | exact OEX | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | reflexivity | eassumption
             | (clear - F8; Z.div_mod_to_equations; lia)
             | (clear - F0; lia)
             | (clear - SLO SP1 NER NEEDR; lia)
             | (clear - SP1M; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia])
             | (left; clear - F1 ALO LOS SLO SP1 NER NEEDR; lia)
             | match goal with |- ?g => idtac "INIT-PRE-LEFT:" g end ]).
    clear SPI.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-INIT-SIDE:" g end.
    clear OEX ABq.
    match goal with H : rw_cells asegs _ (FB + 32) (mpi_cells 0 _ 0 ?pd) |- _ => rename H into YYBI; set (padY := pd) in YYBI end.
    (* [comment removed for export] *)
    do 2 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mi2 end.
    frame_aobj FSHS (FB + 64) 2%nat as OEX.
    apply (mpi_cells_of_bytes asegs) in RHB.
    lazymatch goal with HHc : HM _ _ _ h1 _ _ mi2 |- _ => pose proof (hm_abase asegs R HIA h1 _ _ mi2 HHc) as ABq end.
    pose proof (A_mpi_init_spec AL IMG) as SPI. unfold mpi_init_stmtA, A_MPI_INIT_ in SPI.
    callxA_sp sp1
      (eapply SPI with (CS := CS) (X := FB + 64) (lo := lo);
       rewrite ?(unsigned_lit sp1) by exact SP1R;
       first [ exact RHB | exact OEX | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | reflexivity | eassumption
             | (clear - F8; Z.div_mod_to_equations; lia)
             | (clear - F0; lia)
             | (clear - SLO SP1 NER NEEDR; lia)
             | (clear - SP1M; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia])
             | (left; clear - F1 ALO LOS SLO SP1 NER NEEDR; lia)
             | match goal with |- ?g => idtac "INIT-PRE-LEFT:" g end ]).
    clear SPI.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-INIT-SIDE:" g end.
    clear OEX ABq.
    match goal with H : rw_cells asegs _ (FB + 64) (mpi_cells 0 _ 0 ?pd) |- _ => rename H into RHBI; set (padR := pd) in RHBI end.
    apply evtA_done. unfold S1P.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx, 1, 0 end.
    do 24 eexists.
    split; [reflexivity|]. split; [right; left; reflexivity|]. split; [intros C; discriminate C|].
    split; [intros _; split; [exact GH1|]; do 5 (split; [reflexivity|]); exists padY, padR; split; [exact YYBI| exact RHBI]|]. split; [intros C; discriminate C|].
    split; [exact SP1|]. split; [exact SP1M|].
    split; [eassumption|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
    split; [exact F64|]. split; [exact FRSH|].
    split; [exact FHD|]. split; [exact FSHS|].
    split; [exact SAVE|]. split; [exact SLOT|]. split; [exact SThi|].
    split; [assumption|]. split; [assumption|]. split; [exact PRES| first [exact SSH | assumption]].
    all: match goal with |- ?g => idtac "SW-LEFT:" g end.
    }
    assert (GH2 : g_h g = 2) by (destruct GKIND as [(_ & _ & E)|(E & _)]; [exfalso; exact (E KY)| exact E]).
    clear GOBg GHDg CGX CGY GTLg GXR GYR GPOS GHI GAL8.
    (* [comment removed for export] *)
    do 2 zstep.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mq6 end.
    lazymatch goal with HHc : HM _ _ _ h1 _ _ mq6, MIc : mem_inv _ mq6 |- _ =>
      destruct (ck_op_at (pt_X p) OPX h1 _ mq6 sp1 (presW_presA asegs R HIA h LB LF _ _ _ m mq6 PRES) MIc HHc Ehcs ltac:(clear - SP1; lia)) as (Ma & Oa & OLa & PPa & SSa & SLa);
      pose proof (hm_abase asegs R HIA h1 _ _ mq6 HHc) as ABq end.
    rewrite EAX in Oa, SSa.
    pose proof (A_mpi_size_spec AL IMG) as SPQ. unfold mpi_size_stmtA, mpi_query_stmtA, A_MPI_SIZE_Q in SPQ.
    callxA_sp sp1
      (eapply SPQ with (CS := CS) (LB := LB) (dX := (pt_X p)) (lo := lo);
       rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?EAX;
       first [ exact Ma | exact Oa | exact OLa | exact PPa | exact SSa | exact SLa | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | exact I | reflexivity | eassumption
             | (clear; lia)
             | (clear - LOS ALO ACV; lia)
             | (clear - SLO SP1 NER NEEDR; lia)
             | (clear - SP1M; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia])
             | (f_equal; clear; lia)
             | match goal with |- ?g => idtac "SIZEX-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-SIZEX-SIDE:" g end.
    clear Ma Oa OLa PPa SSa SLa ABq.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg2 end.
    lazymatch goal with HHc : HM _ _ _ h1 _ _ mg2, MIc : mem_inv _ mg2 |- _ =>
      (flat constr:((GATK h1 _ mg2 (presW_presA asegs R HIA h LB LF _ _ _ m mg2 PRES) MIc HHc Ehcs)) 10%nat; intros GOBg GHDg CGX CGY GTLg GXR GYR GPOS GHI GAL8) end.
    unfold mpi_cells in CGX, CGY. unfold grp_head_cells in GHDg. unfold grp_tail_cells in GTLg.
    (* [comment removed for export] *)
    do 11 zstep.
    zstep. if_cases KSZ.
    {
      apply evtA_done. unfold S1P.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx, 0, (-19584) end.
      do 24 eexists.
      split; [reflexivity|]. split; [left; reflexivity|]. split; [intros _; split; [apply bv_eq; vm_compute; reflexivity| clear; lia]|].
      split; [intros C; discriminate C|]. split; [intros C; discriminate C|].
      split; [exact SP1|]. split; [exact SP1M|].
      split; [eassumption|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
      split; [exact F64|]. split; [exact FRSH|].
      split; [exact FHD|]. split; [exact FSHX|].
      split; [exact SAVE|]. split; [exact SLOT|]. split; [exact SThi|].
      split; [assumption|]. split; [assumption|]. split; [exact PRES| first [exact SSH | assumption]]. }
    clear GOBg GHDg CGX CGY GTLg GXR GYR GPOS GHI GAL8.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52af8; 0x9b904; 0x9b998; 0x9bcf4; 0x9c740; 0x9cbec; 0x9d5b4; 0x9d8bc; 0x9e720; 0xcc838; 0xcc9dc; 0xcbc98; 0xcbc44; 0xcbe6c; 0xcbe78; 0xcbe80; 0xcbe8c; 0xcbea0; 0xcbecc; 0xcbed8; 0xcbef4; 0xcbf10; 0xcbf14; 0xcbf24; 0xcbf2c; 0xcbf34; 0xcbf60; 0xcbf74; 0xcbf88; 0xcbf90; 0xcbf98; 0xcbfa0; 0xcbfc0; 0xcbfe4] [(0xcbcb4, DJoin); (0xcbcd0, DJoin); (0xcbcd8, DJoin); (0xcbce0, DJoin); (0xcbe08, DJoin); (0xcbe50, DJoin)] 400%N). lx_tree.
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
    repeat match goal with H : context [al_sb AL + Z.shiftr FB 3] |- _ => replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) in H by (clear; lia) end.
    try replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) by (clear; lia).
    try rewrite ?EAX; try rewrite ?EAY; try rewrite ?EAZ.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mq7 end.
    lazymatch goal with HHc : HM _ _ _ h1 _ _ mq7, MIc : mem_inv _ mq7 |- _ =>
      destruct (ck_op_at (pt_X p) OPX h1 _ mq7 sp1 (presW_presA asegs R HIA h LB LF _ _ _ m mq7 PRES) MIc HHc Ehcs ltac:(clear - SP1; lia)) as (Ma & Oa & OLa & PPa & SSa & SLa);
      pose proof (hm_abase asegs R HIA h1 _ _ mq7 HHc) as ABq end.
    rewrite EAX in Oa, SSa.
    pose proof (A_mpi_cmp_int_spec AL IMG) as SPQ. unfold mpi_cmp_int_stmtA, A_MPI_CMP_INT_E in SPQ.
    callxA_sp sp1
      (eapply SPQ with (CS := CS) (LB := LB) (dX := (pt_X p)) (z := 0) (lo := lo);
       rewrite ?(unsigned_lit sp1) by exact SP1R; rewrite ?EAX;
       first [ exact Ma | exact Oa | exact OLa | exact PPa | exact SSa | exact SLa | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | reflexivity | eassumption
             | (clear; lia)
             | (clear - LOS ALO ACV; lia)
             | (clear - SLO SP1 NER NEEDR; lia)
             | (clear - SP1M; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia])
             | (f_equal; clear; lia)
             | match goal with |- ?g => idtac "CMPX0M-PRE-LEFT:" g end ]).
    clear SPQ.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-CMPX0M-SIDE:" g end.
    clear Ma Oa OLa PPa SSa SLa ABq.
    (* [comment removed for export] *)
    do 2 zstep. zstep. if_cases KNEG.
    {
      apply evtA_done. unfold S1P.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx, 0, (-19584) end.
      do 24 eexists.
      split; [reflexivity|]. split; [left; reflexivity|]. split; [intros _; split; [apply bv_eq; vm_compute; reflexivity| clear; lia]|].
      split; [intros C; discriminate C|]. split; [intros C; discriminate C|].
      split; [exact SP1|]. split; [exact SP1M|].
      split; [eassumption|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
      split; [exact F64|]. split; [exact FRSH|].
      split; [exact FHD|]. split; [exact FSHX|].
      split; [exact SAVE|]. split; [exact SLOT|]. split; [exact SThi|].
      split; [assumption|]. split; [assumption|]. split; [exact PRES| first [exact SSH | assumption]]. }
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mg3 end.
    lazymatch goal with HHc : HM _ _ _ h1 _ _ mg3, MIc : mem_inv _ mg3 |- _ =>
      (flat constr:((GATK h1 _ mg3 (presW_presA asegs R HIA h LB LF _ _ _ m mg3 PRES) MIc HHc Ehcs)) 10%nat; intros GOBg GHDg CGX CGY GTLg GXR GYR GPOS GHI GAL8) end.
    unfold mpi_cells in CGX, CGY. unfold grp_head_cells in GHDg. unfold grp_tail_cells in GTLg.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52af8; 0x9b904; 0x9b998; 0x9bcf4; 0x9c740; 0x9cbec; 0x9d5b4; 0x9d8bc; 0x9e720; 0xcc838; 0xcc9dc; 0xcbc98; 0xcbc44; 0xcbe6c; 0xcbe78; 0xcbe80; 0xcbe8c; 0xcbea0; 0xcbecc; 0xcbed8; 0xcbef4; 0xcbf10; 0xcbf14; 0xcbf24; 0xcbf2c; 0xcbf34; 0xcbf60; 0xcbf74; 0xcbf88; 0xcbf90; 0xcbf98; 0xcbfa0; 0xcbfc0; 0xcbfe4] [(0xcbcb4, DJoin); (0xcbcd0, DJoin); (0xcbcd8, DJoin); (0xcbce0, DJoin); (0xcbe08, DJoin); (0xcbe50, DJoin)] 400%N). lx_tree.
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
    repeat match goal with H : context [al_sb AL + Z.shiftr FB 3] |- _ => replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) in H by (clear; lia) end.
    try replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) by (clear; lia).
    try rewrite ?EAX; try rewrite ?EAY; try rewrite ?EAZ.
    try clear GOBg. try clear GHDg. try clear CGX. try clear CGY. try clear GTLg. try clear GXR. try clear GYR. try clear GPOS. try clear GHI. try clear GAL8.
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSHM end.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into mi3 end.
    frame_aobj FSHM (FB + 96) 2%nat as OEX.
    apply (mpi_cells_of_bytes asegs) in XMB.
    lazymatch goal with HHc : HM _ _ _ h1 _ _ mi3 |- _ => pose proof (hm_abase asegs R HIA h1 _ _ mi3 HHc) as ABq end.
    pose proof (A_mpi_init_spec AL IMG) as SPI. unfold mpi_init_stmtA, A_MPI_INIT_ in SPI.
    callxA_sp sp1
      (eapply SPI with (CS := CS) (X := FB + 96) (lo := lo);
       rewrite ?(unsigned_lit sp1) by exact SP1R;
       first [ exact XMB | exact OEX | exact ABq | exact CSOK | exact (art_alwf asegs R HIA) | reflexivity | eassumption
             | (clear - F8; Z.div_mod_to_equations; lia)
             | (clear - F0; lia)
             | (clear - SLO SP1 NER NEEDR; lia)
             | (clear - SP1M; Z.div_mod_to_equations; lia)
             | (eapply crange_sub; [exact SCS| clear; lia| clear - SP1; lia])
             | (left; clear - F1 ALO LOS SLO SP1 NER NEEDR; lia)
             | match goal with |- ?g => idtac "INIT-PRE-LEFT:" g end ]).
    clear SPI.
    all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "AFTER-INIT-SIDE:" g end.
    clear OEX ABq.
    match goal with H : rw_cells asegs _ (FB + 96) (mpi_cells 0 _ 0 ?pd) |- _ => rename H into XMBI; set (padX := pd) in XMBI end.
    apply evtA_done. unfold S1P.
    lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx, 2, 0 end.
    do 24 eexists.
    split; [reflexivity|]. split; [right; right; reflexivity|]. split; [intros C; discriminate C|]. split; [intros C; discriminate C|].
    split; [intros _; split; [exact GH2|]; do 3 (split; [reflexivity|]); exists padX; exact XMBI|].
    split; [exact SP1|]. split; [exact SP1M|].
    split; [eassumption|]. split; [exact Ehcs|]. split; [exact Ehtop|]. split; [exact Estk|]. split; [exact Eflag|]. split; [exact Evol|]. split; [exact Efr|]. split; [exact HKI|].
    split; [exact F64|]. split; [exact FRSH|].
    split; [exact FHD|]. split; [exact FSHM|].
    split; [exact SAVE|]. split; [exact SLOT|]. split; [exact SThi|].
    split; [assumption|]. split; [assumption|]. split; [exact PRES| first [exact SSH | assumption]].
    all: match goal with |- ?g => idtac "PRO-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Definition EPOST (h3 : HST asegs R HIA) (LBa LBb : list blk) (m0 m2x : mem) (WA WB : list ivl) (r : Z)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Lms,$5?.(3<.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(3<.(3=.$9.VR,VHIA,)Lh4,(3=.$9.VR,VHIA,)(3<.(2.&40.)Lt0,(2.&40.)(3<.(2.&40.)Lt1,(2.&40.)(3<.(2.&40.)Lt2,(2.&40.)(3<.(2.&40.)La1,(2.&40.)(3<.(2.&40.)La2,(2.&40.)(3<.(2.&40.)La3,(2.&40.)(3<.(2.&40.)La4,(2.&40.)(3<.(2.&40.)La5,(2.&40.)(3<.(2.&40.)La6,(2.&40.)(3<.(2.&40.)La7,(2.&40.)(3<.(2.&40.)Lt3,(2.&40.)(3<.(2.&40.)Lt4,(2.&40.)(3<.(2.&40.)Lt5,(2.&40.)(3<.(2.&40.)Lt6,(2.&40.)(1:.(=.$5?.R11.(5:.(5;.Vra,Vsp,Vgp,Vtp,R>.R=.R<.Vs0,Vs1,(47.&40.O1.)R;.R:.R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)VF,(60.Vra,)Vfc,(5=.(2.&40.))R10.(5>.$9.)))(1:.(43.$9.R10.)(1:.(57.$9.R10.Vlo,(2?.&40.Vsp,))(1:.(61.$9.VR,VHIA,O8.O7.VLF,(2?.&40.Vsp,)(3?.VR,)O3.O5.R10.)(1:.(61.$9.VR,VHIA,O8.O6.VLF,(2?.&40.Vsp,)(3?.VR,)O2.O4.R10.)(1:.(=.P,$6.Sp(33.$9.VR,VHIA,R?.)(33.$9.VR,VHIA,O8.))(1:.(=.$6.(62.$9.VR,VHIA,R?.)(62.$9.VR,VHIA,O8.))(1:.(=.$6.(40.$9.VR,VHIA,R?.)(40.$9.VR,VHIA,O8.))(1:.(=.$6.(63.$9.VR,VHIA,R?.)(63.$9.VR,VHIA,O8.))(1:.(=.$6.(64.$9.VR,VHIA,R?.)(64.$9.VR,VHIA,O8.))(1:.(=.$6.(65.$9.VR,VHIA,R?.)(65.$9.VR,VHIA,O8.))(1:.Pmo,$66.(67.(68.$9.VR,VHIA,R10.R1.)(68.$9.VR,VHIA,O8.R1.))(44.$9.VR,VHIA,R?.O6.VLF,R10.)))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01L0@D10777814275.209D2459732106.233 D2459793318.209 D32452690557.209D3376374386.208 D3386269609.233 D38320100959.233D43016287773.210D45717900227.208D62011770188.210D62022316105.233D68407932977.208D6911601204.208 L13312155929.225L13424450162.182L13424450175.186L17832996913.236L19546883927.182L19546883930.186L2275137097.0   L24131365012.181L24131365017.177L27188209011.213L308693591.2    L35655538631.10 L39332637397.0  L39540652971.1  L40100639701.0  L4022451686.1   L42411609006.0  L47798928549.201L47798928552.199L47801036031.199L48117620903.182L48117620904.178L48132302223.200L48132302231.199L49367084.2     L50790761713.7  L60098763854.3  L62018535662.1  L66571902283.7  L67028580427.9  L6899380056.1   L6912107235.181 L6912107246.177 L9356559676.12  P313166160.235  Q10592386204.214Q10592386207.218Q16052366068.234Q16834586315.236Q16834586323.235Q21715049793.236Q21715049817.235Q21721340005.215Q21721340008.219Q22358563588.217Q24131365012.219Q24131365017.215Q24137657765.213Q24137657789.217Q30132769282.236Q30147450662.215Q30223088057.214Q30223088058.218Q30871588746.233Q31314676345.213Q34796740410.218Q38360946328.233Q48117620905.218Q48117620906.214Q48132302223.217Q48132302231.213Q52741535643.233Q59666529497.235Q59668625896.219Q60382659730.219Q60382659743.215Q60397339043.235Q60397339067.236Q60976432811.232Q64326673371.234Q67397950268.214Q6897428426.217 Q6897428434.213 Q6912107235.219 Q6912107246.215 Q7902384038.235 Q7902384062.236 Q7917062807.219 Q7917062810.215 00000J00K00L00f00g00h01K01n02H02d03@03A03[04;04d05M05N06206V06W06g07707V07W08008108508608:08;08<08=08>08i09T0:?0:j0;00;K0;U0;X0<30<V0<Z0<j0=:0=i0=j0>:0>J0>]0>^0>_0>`0>a0>b0>c0>d0?40?D0?T0?d0?e0?f0@60@F0@\0@]0@^0A10A\0BG0C20C]0D30D40D50D60D70D80D90DL0D_0D`0E00E@0EP0E`0F90FR0Fk0GDS2LF2ra2sp3LFB2FB3sp14lxHnFFS2LF2ra2sp3LFB2FB3sp14lxHnFFS1R3HIA2LF2ra2sp3LFB2FB3sp14lxHn2h4S1R3HIA2LF2ra2sp3LFB2h32FB3sp14lxHnS2LF2ra2sp3LFB2FB3sp14lxHnS1R2LF2ra2sp3LFB2FB3sp14lxHnS1R2LF2ra2sp3LFB2FB3sp14lxHnFS2LF2ra2sp3LFB2FB3sp14lxHnS2LF2ra2sp3LFB2FB3sp14lxHn2pq2PBS2LF2ra2sp3LFB2FB3sp13SPR4SP1R2F82F04lxHnS2LF2ra2sp3LFB2FB3sp13SPR4SP1R2F82F04lxHnFS2LF2ra2sp3LFB2FB3sp13SPR2F82F04lxHnS2LF2ra2sp3LFB2FB3sp13SPR2F82F04lxHnSS2LF3LFB2FB4lxHnS2LF3LFB2FB4lxHnS2LF2ra2sp3LFB2FB3sp14lxHn1c2HcFS1R3HIA1h2sp2lo3TOP5HTOP3SS2FBSS2FBSFFFS1R5NEEDR2LF2sp2lo3LFB3LOS3SLO3ALO3NER4lxHnS1R5NEEDR2LF2sp2lo3LFB3LOS3SLO3ALO3NER4lxHnS1R5NEEDR2LF2sp2lo3LFB3LOS3SLO3ALO3NER4lxHnS1R5NEEDR2LF2sp2lo3LFB3LOS3SLO3ALO3NER4lxHnS1R2FBS1R5NEEDR2sp2lo3LOS3SLO3NERS1R2lo3LOSS1RS1R5NEEDR2sp2lo3LOS3SLO3NERS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13NERS2FBS2LF3LFB2FB4lxHnS2LF3LFB2FB4lxHnS1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3NER3SPRFS2LF3LFB2FB4lxHnS2LF3LFB2FB4lxHnS2LF3LFB4lxHn2pq2PBFFFFFFFS2LF3LFB2FB4lxHnS2LF3LFB2FB4lxHnS2LF3LFB2FB4lxHnS2LF3LFB2FB4lxHnFFS2LF3LFB2FB4lxHnS2LF3LFB2FB4lxHnS2LF3LFB2FB4lxHn2pq2PBFFS2LF3LFB4lxHn2pq2PBS1R5NEEDR2LF2sp2lo3LFB3LOS3SLO3ALO3NER4lxHnS1R5NEEDR2LF2sp2lo3LFB3LOS3SLO3ALO3NER4lxHnS1R5NEEDR2LF2sp2lo3LFB3LOS3SLO3ALO3NER4lxHnS1R5NEEDR2LF2sp2lo3LFB3LOS3SLO3ALO3NER4lxHnS2LF3LFB2FB4lxHn2pq2PBFFFFFFS2LF3LFB4lxHn2pq2PBS2LF3LFB4lxHn2pq2PBFS2LF3LFB2FB4lxHnS2LF3LFB2FB4lxHnS2LF3LFB2FB4lxHnS2LF3LFB2FB4lxHnS1R2LF3LFB2FB3ALO2F14lxHnS1R2LF3LFB2FB3ALO2F14lxHnS1R2LF3LFB2FB3ALO2F14lxHnS1R2LF3LFB2FB3ALO2F14lxHn". (* [comment removed for export] *)
  Lemma epi_walk : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Ph3,(3=.$9.VR,VHIA,)PLBa,(0.$4.)PLBb,(0.$4.)Pm0,P,(2.&40.)(3.(2.&8.))Pm2x,P,(2.&40.)(3.(2.&8.))Pmm,P,(2.&40.)(3.(2.&8.))PWA,(0.$42.)PWB,(0.$42.)PFB,$6.Psp1,$6.Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Ps3v,(2.&40.)Ps4v,(2.&40.)Ps5v,(2.&40.)Ps6v,(2.&40.)Ps7v,(2.&40.)Pw0,(2.&40.)Pw1,(2.&40.)Pw2,(2.&40.)Pr,$6.P,(44.$9.VR,VHIA,R22.R20.(69.(5.$6.$6.)(11.$6.$6.R1:.+80.)VLF,)R1=.)P,Px,$6.P,(33.$9.VR,VHIA,Vh,R1.)(33.$9.VR,VHIA,R25.R2.)P,(=.$6.(62.$9.VR,VHIA,R24.)(62.$9.VR,VHIA,Vh,))P,(=.$6.(40.$9.VR,VHIA,R25.)(40.$9.VR,VHIA,Vh,))P,(1:.(1;.(23.(2?.&40.Vsp,)+70.)R1=.)(1;.R1=.(23.(2?.&40.Vsp,)+60.)))P,(=.$6.(4<.R1>.+20.)=)P,(=.$6.(4<.R20.+40.)=)P,(6:.VR,R28.VLF,R21.+80.)P,(6:.VR,R28.VLF,R22.+80.)P,(6;.(33.$9.VR,VHIA,Vh,)R23.+80.)P,PB,$6.Pj,$6.P,(;.(5.$6.$6.)(11.$6.$6.R2.R1.)VLF,)(21.(1;.(20.R27.+80.)R3.)(1;.(20.R3.R2.)R27.))P,Pb',$4.P,(;.$4.R1.R2=.)(;.$4.R2.R2=.)P,(19.$9.R29.R26.(69.$18.(6<.R10.)(69.$18.(6<.R?.)(69.$18.(6<.R>.)(41.$18.)))))P,(19.$9.R2:.(20.(6=.R27.+3.)(6>.(32.VR,)))(69.$18.(6?.(47.&8.+?1.))(69.$18.(6?.(47.&8.+?1.))(69.$18.(6?.(47.&8.+?1.))(69.$18.(6?.(47.&8.+?1.))(69.$18.(6?.(47.&8.+?8.))(69.$18.(6?.(47.&8.+?8.))(69.$18.(6?.(47.&8.+?2.))(69.$18.(6?.(47.&8.+?2.))(69.$18.(6?.(47.&8.+?8.))(69.$18.(6?.(47.&8.+?8.))(69.$18.(6?.(47.&8.+?2.))(69.$18.(6?.(47.&8.+?2.))(69.$18.(6?.(47.&8.+?8.))(69.$18.(6?.(47.&8.+?8.))(69.$18.(6?.(47.&8.+?3.))(69.$18.(6?.(47.&8.+?3.))(41.$18.))))))))))))))))))P,(19.$9.R2;.(20.(2?.&40.Vsp,)-58.)(69.$18.(6<.Vs9,)(69.$18.(6<.Vs8,)(69.$18.(6<.Vs7,)(69.$18.(6<.Vs6,)(69.$18.(6<.Vs5,)(69.$18.(6<.Vs4,)(69.$18.(6<.Vs3,)(69.$18.(6<.Vs2,)(69.$18.(6<.Vs1,)(69.$18.(6<.Vs0,)(69.$18.(6<.Vra,)(41.$18.)))))))))))))P,(19.$9.R2<.R28.(69.$18.(6<.(47.&40.R29.))(41.$18.)))P,(57.$9.R2=.(20.R29.+8.)(20.(2?.&40.Vsp,)-58.))P,(57.$9.R2>.Vlo,R2:.)P,(43.$9.R2?.)P,(61.$9.VR,VHIA,R35.R34.VLF,(2?.&40.Vsp,)(3?.VR,)R2?.R32.R30.)P,(61.$9.VR,VHIA,R36.R34.VLF,(2?.&40.Vsp,)(3?.VR,)R2?.R32.R31.)(58.$9.(32.VR,)(33.$9.VR,VHIA,R37.)(70.R37.R36.R35.R34.R33.R31.R30.R16.)(5:.(5;.R2=.(47.&40.R2>.)Vgp,Vtp,R2<.R2;.R2:.Vsp,(47.&40.R2>.)(47.&40.R16.)R29.R28.R27.R26.R25.R24.R23.(47.&40.R2?.)R1>.R1=.R1<.R1;.R1:.(47.&40.(20.(6=.R2?.+3.)(6>.(32.VR,))))(47.&40.R2?.)Vs10,Vs11,R22.R21.R20.R1?.)VF,(47.&40.+<;<44.)Vfc,(5=.(2.&40.))R32.(5>.$9.)))")
(* [comment removed for export] *).
  Proof.
    intros until r. intros HH3 HCS3 ET3 ES3 SP1 SP1M F64 FRSH FRSH3 CFB AP SUBK FHD FSH SAVE SLOT SThi STlo MIq PRES PRES2.
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
    pose proof HH as HH_lx. lazymatch type of HH with ?T => change (id T) in HH end.
    pose proof GOB as GOB_lx. lazymatch type of GOB with ?T => change (id T) in GOB end.
    pose proof QOB as QOB_lx. lazymatch type of QOB with ?T => change (id T) in QOB end.
    pose proof MC0 as MC0_lx. lazymatch type of MC0 with ?T => change (id T) in MC0 end.
    pose proof SSH as SSH_lx. lazymatch type of SSH with ?T => change (id T) in SSH end.
    pose proof MI as MI_lx. lazymatch type of MI with ?T => change (id T) in MI end.
    pose (lxi := lxA_img (arl_AL R) IMG).
    assert (SFF : shadow_free R LBa LF (arl_stklo R) (hstkhi asegs R HIA h3) FB 128)
      by (eapply shadow_free_fresh; [exact FRSH | exact (proj2 (proj2 (proj2 PRES))) | clear; lia | clear; lia | exact ALO | exact AP]).
    assert (SFF2 : shadow_free R LBb LF (arl_stklo R) (hstkhi asegs R HIA h3) FB 128)
      by (eapply shadow_free_fresh; [exact FRSH3 | exact (proj2 (proj2 (proj2 PRES2))) | clear; lia | clear; lia | exact ALO | exact AP]).
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52af8; 0x9b904; 0x9b998; 0x9bcf4; 0x9c740; 0x9cbec; 0x9d5b4; 0x9d8bc; 0x9e720; 0xcc838; 0xcc9dc; 0xcbc98; 0xcbc44; 0xcbe6c; 0xcbe78; 0xcbe80; 0xcbe8c; 0xcbea0; 0xcbecc; 0xcbed8; 0xcbef4; 0xcbf10; 0xcbf14; 0xcbf24; 0xcbf2c; 0xcbf34; 0xcbf60; 0xcbf74; 0xcbf88; 0xcbf90; 0xcbf98; 0xcbfa0; 0xcbfc0; 0xcbfe4] [(0xcbcb4, DJoin); (0xcbcd0, DJoin); (0xcbcd8, DJoin); (0xcbce0, DJoin); (0xcbe08, DJoin); (0xcbe50, DJoin)] 400%N). lx_tree.
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
    repeat match goal with H : context [al_sb AL + Z.shiftr FB 3] |- _ => replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) in H by (clear; lia) end.
    try replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) by (clear; lia).
    try rewrite ?EAX; try rewrite ?EAY; try rewrite ?EAZ.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into me end.
    (* [comment removed for export] *)
    match goal with H : HM _ _ _ h3 _ _ me |- _ => rename H into HHe end.
    destruct (hm_fake_free asegs R HIA h3 LBb ((FB, 128) :: LF) me FB 128 HHe ltac:(left; reflexivity))
      as (pq & h4 & ROp & [old Hold] & CRp & NCp & NSp & HM4 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4).
    replace (FB + 128 - 8) with (FB + 120) in ROp by (clear; lia).
    pose proof (rw_cells_bound _ _ _ _ Hold) as PB. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PB.
    pose proof (store_ok_of_rw1 _ _ _ _ Hold) as HSp. clear Hold.
    assert (SUB1 : forall b', In b' (LBa ++ fdata LF) -> In b' (LBb ++ fdata ((FB, 128) :: LF))).
    { intros b' Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply SUBK; exact Hb| right].
      eapply fdata_incl; [| exact Hb]. intros fb Hfb. right. exact Hfb. }
    assert (SUB2 : forall b', In b' (LBb ++ fdata LF) -> In b' (LBb ++ fdata ((FB, 128) :: LF))) by (intros b' Hb; apply fdata_cons_sub; exact Hb).
    assert (NP5 : bv_unsigned sp + -88 + 88 <= pq \/ pq + 1 <= bv_unsigned sp + -88).
    { eapply (nc_apart _ _ _ (arl_stklo R) _ pq); [exact NCp| apply client_range_stack; clear - SLO LOS NEEDR NER; lia| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
    assert (NP6 : sp1 + 8 <= pq \/ pq + 1 <= sp1).
    { eapply (nc_apart _ _ _ (arl_stklo R) _ pq); [exact NCp| apply client_range_stack; clear - SLO LOS SP1 NEEDR NER; lia| intros b' Hb; exact Hb| clear; lia| clear; lia]. }
    assert (WCp1 : wcover R LBa LF (bv_unsigned sp) WA pq 1) by (eapply wcover_nc; [exact NCp| exact SUB1| clear - LOS SLO NEEDR NER; lia]).
    assert (WCp2 : wcover R LBb LF (bv_unsigned sp) WB pq 1) by (eapply wcover_nc; [exact NCp| exact SUB2| clear - LOS SLO NEEDR NER; lia]).
    clear HHe NCp NSp FHD.
    repeat match goal with H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL) _ |- _ => clear H | H : rw_cells _ me (Z.shiftr FB 3 + al_sb AL + _) _ |- _ => clear H end.
    zstep. zstep.
    fake_free_done pq HSp.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    repeat match goal with H : context [Z.of_nat ?n] |- _ => let v := eval cbv in (Z.of_nat n) in lazymatch v with Z0 => idtac | Zpos _ => idtac end; progress change (Z.of_nat n) with v in H end.
    try (repeat match goal with H : (?a <= ?b) /\ (?c <= ?d) |- _ => lazymatch goal with _ : c <= d |- _ => fail | _ => pose proof (proj1 H); pose proof (proj2 H) end end).
    lx_mkR. lx_pre. lxe_pose. lx_run_tac (PLAN [0x52af8; 0x9b904; 0x9b998; 0x9bcf4; 0x9c740; 0x9cbec; 0x9d5b4; 0x9d8bc; 0x9e720; 0xcc838; 0xcc9dc; 0xcbc98; 0xcbc44; 0xcbe6c; 0xcbe78; 0xcbe80; 0xcbe8c; 0xcbea0; 0xcbecc; 0xcbed8; 0xcbef4; 0xcbf10; 0xcbf14; 0xcbf24; 0xcbf2c; 0xcbf34; 0xcbf60; 0xcbf74; 0xcbf88; 0xcbf90; 0xcbf98; 0xcbfa0; 0xcbfc0; 0xcbfe4] [(0xcbcb4, DJoin); (0xcbcd0, DJoin); (0xcbcd8, DJoin); (0xcbce0, DJoin); (0xcbe08, DJoin); (0xcbe50, DJoin)] 400%N). lx_tree.
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
    repeat match goal with H : context [al_sb AL + Z.shiftr FB 3] |- _ => replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) in H by (clear; lia) end.
    try replace (al_sb AL + Z.shiftr FB 3) with (Z.shiftr FB 3 + al_sb AL) by (clear; lia).
    try rewrite ?EAX; try rewrite ?EAY; try rewrite ?EAZ.
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
  Definition CK_POST := ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "(71.$9.VR,VHIA,VMT,Vra,Vsp,Vgp,Vtp,Vs0,Vs1,Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,VF,Vfc,Vh,VLB,VLF,VG,Vg,VQ,Vp,$30.VN,Vlo,Vd,Vm,Vmo0,)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Lemma ck_grp_blk : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Pe,$:.P,(;.$:.R1.(<.Vg,))P,(=.$>.(?.R2.)$10.)(1:.(;.(5.$6.$6.)(11.$6.$6.(12.R3.)(13.+4.(14.R3.)))VLB,)(1:.(1;.+1.(14.R3.))(21.(1;.(20.(12.R3.)(13.+4.(14.R3.)))(37.(2;.VR,)))(1;.(38.(2;.VR,))(12.R3.)))))")
(* [comment removed for export] *).
  Proof.
    intros e He EO.
    assert (MR : mpdr_at asegs m LB e).
    { flat constr:(GAT) 14%nat. intros HD GAL POS EP EA EB EN MP MA MB FLt4 MN HT REST. flat constr:(FLt4) 6%nat. flclear FLt4. intros EX EY EZ MX MY MZ.
      unfold grp_mpds in He. cbn in He. destruct He as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]; assumption. }
    flat constr:((ck_blk e MR EO)) 5%nat. intros K1 K2 _ _ K5. split; [exact K2|]. split; [exact K1| exact K5].
  Qed.
  Lemma ck_pt_blk : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Pe,$:.P,(;.$:.R1.(17.Vp,))P,(=.$>.(?.R2.)$10.)(1:.(;.(5.$6.$6.)(11.$6.$6.(12.R3.)(13.+4.(14.R3.)))VLB,)(1:.(1;.+1.(14.R3.))(21.(1;.(20.(12.R3.)(13.+4.(14.R3.)))(37.(2;.VR,)))(1;.(38.(2;.VR,))(12.R3.)))))")
(* [comment removed for export] *).
  Proof.
    intros e He EO. flat constr:((ck_op_pt e He)) 2%nat. intros FLt5 _. flat constr:(FLt5) 8%nat. flclear FLt5. intros _ _ _ _ _ _ _ BLK0.
    flat constr:((BLK0 EO)) 5%nat. intros K1 K2 _ _ K5. split; [exact K2|]. split; [exact K1| exact K5].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0>L2275137097.0 L34409126551.5L35693534892.2L36647717812.2L36674788178.8L37869493781.8L52615975131.5L59314923118.6L61056762637.9L62018535662.100000100A00H00O00g01A01P01a02<02?SS1R3MC13MC21x2HxS1G3GMCS1Q3QMCS1R3HIA1h1N2hk1v3HVk3HVBS1R3MC13MC23DI13DI21P1k2HOS2sp1G1a2Ha1K1QS1G2lo1a2Ha1S1K1QS1R3HIA1h1N1d2hk1f4HFRk3HFBS1R". (* [comment removed for export] *)
  Lemma ck_exit : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "PFBx,$6.Psp1x,$6.Phk,(3=.$9.VR,VHIA,)PLBk,(0.$4.)Pmk,P,(2.&40.)(3.(2.&8.))Pv,$6.Pf,$6.Pr,$6.Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Ps3v,(2.&40.)Ps4v,(2.&40.)Ps5v,(2.&40.)Ps6v,(2.&40.)Ps7v,(2.&40.)Pw0x,(2.&40.)Pw1x,(2.&40.)Pw2x,(2.&40.)P,(1:.(1;.(23.(2?.&40.Vsp,)+70.)R1>.)(1;.R1>.(23.(2?.&40.Vsp,)+60.)))P,(=.$6.(4<.R1?.+20.)=)P,(=.$6.(4<.R21.+40.)=)P,(6:.VR,VLB,VLF,R22.+80.)P,(6;.(33.$9.VR,VHIA,Vh,)R23.+80.)P,(44.$9.VR,VHIA,R22.R21.(69.(5.$6.$6.)(11.$6.$6.R24.+80.)VLF,)R20.)P,Px,$6.P,(33.$9.VR,VHIA,Vh,R1.)(33.$9.VR,VHIA,R25.R2.)P,(=.$6.(62.$9.VR,VHIA,R24.)(62.$9.VR,VHIA,Vh,))P,(=.$6.(40.$9.VR,VHIA,R25.)(40.$9.VR,VHIA,Vh,))P,(=.$6.(63.$9.VR,VHIA,R26.)(63.$9.VR,VHIA,Vh,))P,(1;.(64.$9.VR,VHIA,R27.)(20.(64.$9.VR,VHIA,Vh,)R24.))P,(1;.(65.$9.VR,VHIA,R28.)(20.(65.$9.VR,VHIA,Vh,)R24.))P,(1;.R26.(72.VN,))P,(1;.R26.(73.VN,Vd,))P,(19.$9.R29.R2=.(69.$18.(6<.R11.)(69.$18.(6<.R10.)(69.$18.(6<.R?.)(41.$18.)))))P,(19.$9.R2:.(20.(6=.R2>.+3.)(6>.(32.VR,)))(69.$18.(6?.(47.&8.+?1.))(69.$18.(6?.(47.&8.+?1.))(69.$18.(6?.(47.&8.+?1.))(69.$18.(6?.(47.&8.+?1.))(69.$18.(6?.(47.&8.+?8.))(69.$18.(6?.(47.&8.+?8.))(69.$18.(6?.(47.&8.+?2.))(69.$18.(6?.(47.&8.+?2.))(69.$18.(6?.(47.&8.+?8.))(69.$18.(6?.(47.&8.+?8.))(69.$18.(6?.(47.&8.+?2.))(69.$18.(6?.(47.&8.+?2.))(69.$18.(6?.(47.&8.+?8.))(69.$18.(6?.(47.&8.+?8.))(69.$18.(6?.(47.&8.+?3.))(69.$18.(6?.(47.&8.+?3.))(41.$18.))))))))))))))))))P,(19.$9.R2;.(20.(2?.&40.Vsp,)-58.)(69.$18.(6<.Vs9,)(69.$18.(6<.Vs8,)(69.$18.(6<.Vs7,)(69.$18.(6<.Vs6,)(69.$18.(6<.Vs5,)(69.$18.(6<.Vs4,)(69.$18.(6<.Vs3,)(69.$18.(6<.Vs2,)(69.$18.(6<.Vs1,)(69.$18.(6<.Vs0,)(69.$18.(6<.Vra,)(41.$18.)))))))))))))P,(19.$9.R2<.R2?.(69.$18.(6<.(47.&40.R30.))(41.$18.)))P,(57.$9.R2=.(20.R30.+8.)(20.(2?.&40.Vsp,)-58.))P,(57.$9.R2>.Vlo,R31.)P,(43.$9.R2?.)P,(61.$9.VR,VHIA,R32.VLB,VLF,(2?.&40.Vsp,)(3?.VR,)(69.(5.$6.$6.)(11.$6.$6.$30.(20.$30.+8.))(41.(5.$6.$6.)))Vm,R30.)P,Pb,$4.P,(;.$4.R1.VLB,)(;.$4.R2.R34.)P,Pb,$4.P,(;.$4.R1.R34.)(;.$4.R2.VLB,)P,(3<.(2.&40.)Lc,(2.&40.)(19.$9.R34.$30.(69.$18.(6<.R1.)(41.$18.))))P,(1:.(1<.(74.(4;.+2.+1?.))R31.)(1;.R31.=))(75.$9.(76.$9.VR,VHIA,R37.Vmo0,)$77.(5:.(5;.R31.(47.&40.R38.)Vgp,Vtp,R30.R2?.R2>.Vsp,(47.&40.R38.)(47.&40.R32.)R2=.R2<.R2;.R2:.R29.R28.R27.(47.&40.R39.)R22.R21.R20.R1?.R1>.(47.&40.(20.(6=.R39.+3.)(6>.(32.VR,))))(47.&40.R39.)Vs10,Vs11,R26.R25.R24.R23.)VF,(47.&40.+<;<44.)Vfc,(5=.(2.&40.))R35.(5>.$9.)))")
(* [comment removed for export] *).
  Proof.
    intros until w2x. intros SP1x SP1Mx F64x FRSHx CFB HHk HCSk HTk HSk HFk HVk HFRk HVB HFB FHDk FSHk SAVEk SLOTk SThik STlok MIk PRESa SUBk COVk [ck MCk] HR.
    rt_facts. pose proof (hcs_ok asegs R HIA hk) as CSOKk.
    destruct (frame_factsA R HIA (hcs asegs R HIA hk) hk LBk LF mk FBx 128 lo HHk eq_refl (fresh_apart_relist R HIA hk LB LBk LF mk FBx 128 FRSHx HHk) F64x ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBk & _ & _ & _ & APk & _).
    pose proof (presW_init_at R HIA hk _ _ LBk LF mk (bv_unsigned sp) (arl_stklo R) [] h HHk
                  ltac:(intros b' Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSk HSk ltac:(clear; lia)) as PRES2.
    eapply (aevtA_cut_evtA_KF asegs R HIA hk mo0).
    { eapply epi_walk with (h3 := hk) (LBa := LB) (LBb := LBk) (r := r);
        first [ exact HHk | exact HCSk | exact PRESa | exact PRES2 | exact FRSHx | exact CFB | exact APk | exact SUBk | eassumption | reflexivity
              | exact (fresh_apart_relist R HIA hk LB LBk LF mk FBx 128 FRSHx HHk)
              | match goal with |- ?g => idtac "EPI-PRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    destruct EP as (m9 & h4 & z0' & z1' & z2' & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3' & z4' & z5' & z6'
                    & -> & MI9 & ST9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4).
    apply aevtA_done. intros mo9 [HK9 MF9].
    unfold CK_POST, ecp_check_postA.
    do 14 eexists. exists m9, mo9, h4, LBk, r, ck.
    split; [reflexivity|]. split; [exact MI9|]. split; [exact ST9|]. split; [exact MF9|].
    pose proof (presW_presA asegs R HIA hk _ LF _ _ _ _ _ PRES9) as HPF. rewrite HSk in HPF.
    split; [exact HPF|].
    split; [rewrite E4top; exact HTk|]. split; [rewrite E4stk; exact HSk|]. split; [rewrite E4flag; exact HFk|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; exact (HCSk x Hx)|].
    split; [rewrite E4vol; clear - HVk HVB; lia|].
    split; [rewrite E4fr; clear - HFRk HFB; lia|].
    split; [exact HH4|].
    split; [intros b; split; [exact (COVk b)| exact (SUBk b)]|].
    pose proof (presA_presx asegs R _ _ _ _ _ _ _ _ HPF) as PXF.
    flat constr:(MCOK) 4%nat. intros MC1 MC2 MC3 _. flat constr:(DIMG) 2%nat. intros DI1 DI2.
    assert (DJB : forall P k, (P + k <= hl_img_lo L \/ hl_img_hi L <= P) -> disjoint_from [(MC, MC + 8)] P k).
    { intros P k HO. cbn [disjoint_from fst snd]. split; [clear - HO MC1 MC2 DI1 DI2; lia| exact I]. }
    split.
    { assert (CRS : client_range L (LB ++ fdata LF) (bv_unsigned sp) G 192).
      { intros a Ha. destruct (GCR a Ha) as [S|[D|B]]; [| right; left; exact D| right; right; exact B].
        destruct GSP as [K|K]; [exfalso; clear - S Ha K; lia| left; clear - Ha K; lia]. }
      pose proof (ck_group_LB_sub MT m LB (LB ++ fdata LF) G g GAT ltac:(intros e He EO; apply in_app_iff; left; exact (proj1 (ck_grp_blk e He EO)))) as GAT0.
      eapply (ecp_group_at_presx asegs L MT m m9 _ LBk (bv_unsigned sp) [(MC, MC + 8)] G g GAT0 PXF MI MI9 CRS);
        [cbn [disjoint_from fst snd]; split; [clear - GMC; lia| exact I]|].
      intros e He EO. flat constr:((ck_grp_blk e He EO)) 3%nat. intros IN _ OUT. split; [exact (SUBk _ IN)| exact (DJB _ _ OUT)]. }
    split.
    { assert (CRS : client_range L (LB ++ fdata LF) (bv_unsigned sp) Q 48).
      { intros a Ha. destruct (QCR a Ha) as [S|[D|B]]; [| right; left; exact D| right; right; exact B].
        destruct QSP as [K|K]; [exfalso; clear - S Ha K; lia| left; clear - Ha K; lia]. }
      pose proof (ck_point_LB_sub m LB (LB ++ fdata LF) Q p PAT ltac:(intros e He EO; apply in_app_iff; left; exact (proj1 (ck_pt_blk e He EO)))) as PAT0.
      eapply (ecp_point_at_presx asegs L m m9 _ LBk (bv_unsigned sp) [(MC, MC + 8)] Q p PAT0 PXF MI MI9 CRS);
        [cbn [disjoint_from fst snd]; split; [clear - QMC; lia| exact I]|].
      intros e He EO. flat constr:((ck_pt_blk e He EO)) 3%nat. intros IN _ OUT. split; [exact (SUBk _ IN)| exact (DJB _ _ OUT)]. }
    split; [| exact HR].
    pose proof (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA hk _ LF _ _ _ _ _ PRES29)) as PX29.
    eapply (heap_presx_rw_cells asegs L); [exact PX29| exact MCk| | exact I].
    cbn [cells_size csize Nat.add]. intros x Hx. right. left. split; [clear - Hx MC1 MC2; lia| apply MC3; exact Hx].
    all: match goal with |- ?g => idtac "EXIT-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060>L22040850830.5L30324303808.7L36134086745.2L47909269.3   L56470958949.4L8324453143.5 00000B00[00a00i01501GS1R2lo3LOS3ALO3ACLS1R2lo3LOS2bp3ALO3ACL3IHIS1a2HaS1A1i2HiS2bp2LL1i2HiS1R2lo3LOS3ALO3ACL". (* [comment removed for export] *)
  Lemma ck_bp_at : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Pbp,$:.PA,$6.P,(78.$9.Vm,VLB,R1.R2.)P,(34.R3.)P,(21.(=.$6.R3.$79.)(=.$6.R3.(20.$79.+20.)))Phk,(3=.$9.VR,VHIA,)PLBk,(0.$4.)PLFx,(0.$4.)Pmk,P,(2.&40.)(3.(2.&8.))P,(44.$9.VR,VHIA,R4.R3.R2.R1.)P,(43.$9.R2.)(1:.(29.$9.R3.R5.R;.)(1:.(=.$>.(?.R;.)$3;.)(1:.(=.$6.(2>.R;.)R:.)(1:.(31.$9.(32.VR,)(33.$9.VR,VHIA,R6.)R3.R:.+10.)(1:.P,(1;.+1.(14.R;.))(31.$9.(32.VR,)(33.$9.VR,VHIA,R7.)R4.(12.R<.)(13.+4.(14.R<.)))(1:.(1;.(20.R:.+10.)Vlo,)P,(1;.+1.(14.R;.))(1;.(20.(12.R<.)(13.+4.(14.R<.)))Vlo,)))))))")
(* [comment removed for export] *).
  Proof.
    intros bp A (MB & EA & EO & SG) IM HA hk LBk LFx mk HHk MIk. rt_facts.
    pose proof (alloc_ceiling_lo (L := arl_L R)) as ACL.
    flat constr:((RTCL m (hm_rtc asegs R HIA h LB LF m HH))) 2%nat. intros _ PR0. flat constr:((RTCL mk (hm_rtc asegs R HIA hk LBk LFx mk HHk))) 2%nat. intros _ PRk.
    assert (PRI : forall a, A <= a < A + 16 -> rtc_prist a).
    { intros a Ha. unfold rtc_prist. eapply (in_ranges_b_sound rtc_pristine BP (BP + 48)); [vm_compute; reflexivity|].
      unfold A_BAD_POINTS in *. destruct HA as [-> | ->]; clear - Ha; lia. }
    flat constr:(MB) 2%nat. flclear MB. intros FLt6 SGN. flat constr:(FLt6) 6%nat. flclear FLt6. intros CX AL8 POS LL NR OW. rewrite EO in OW. flat constr:(OW) 5%nat. flclear OW. intros N1 P4 P0 PB PRO.
    flat constr:((AImgGlobals.img_norz_sound _ _ (IM EO))) 4%nat. intros _ _ IHI _. unfold AImgGlobals.IMG_HI in IHI.
    split.
    { split; [| exact SGN]. split.
      - eapply ck_rw_cells_same; [exact CX|]. unfold mpi_cells. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
        intros i Hi. rewrite EA. assert (HAi : A <= A + i < A + 16) by (clear - Hi; lia). rewrite (PRk (A + i) (PRI (A + i) HAi)), (PR0 (A + i) (PRI (A + i) HAi)). reflexivity.
      - split; [exact AL8|]. split; [exact POS|]. split; [exact LL|]. split; [exact NR|]. rewrite EO.
        split; [exact N1|]. split; [exact P4|]. split; [exact P0|]. split; [| exact PRO].
        eapply MpiFacts.static_limbs_any_mem; [exact MI| exact MIk| exact PB|]. rewrite u32s_length. intros i Hi. apply PRO. clear - Hi LL. lia. }
    split; [exact EO|]. split; [exact EA|].
    split.
    { eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHk|].
      unfold A_BAD_POINTS in *. destruct HA as [-> | ->]; vm_compute; reflexivity. }
    split.
    { intros _. eapply (AImgGlobals.aobj_img asegs AL); [apply (A_mpi_copy.hcs_img_cs_cp R HIA IMG)| eapply (hm_img_shadow asegs R HIA); exact HHk| exact (IM EO)]. }
    split; [unfold A_BAD_POINTS in *; destruct HA as [-> | ->]; clear - ACL ALO LOS; lia|].
    intros _. clear - IHI ACL ALO LOS. lia.
    all: match goal with |- ?g => idtac "BPAT-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section JSW.
  Variables (FB sp1 : Z) (h1 : HST asegs R HIA) (m1 : mem) (padY padR w0 w1 w2 : word).
  Local Notation LF' := ((FB, 128) :: LF).
  Local Notation YY := (FB + 32).
  Local Notation RH := (FB + 64).
  Local Notation SPv := (sp1 + 8).
  Local Notation XO := [(YY, YY + 16); (RH, RH + 16); (MC, MC + 8)].
  Local Notation FRAME := [C8 (Z_to_bv 64 FB)].
  Local Notation dY0 := (mkMPD YY 1 0 0 [] padY LNull).
  Local Notation dR0 := (mkMPD RH 1 0 0 [] padR LNull).
  Hypothesis GH1 : g_h g = 1.
  Hypothesis SP1 : bv_unsigned sp - 112 <= sp1 <= bv_unsigned sp - 96.
  Hypothesis SP1M : sp1 mod 32 = 0.
  Hypothesis HH1 : HM asegs R HIA h1 LB LF' m1.
  Hypothesis Ehcs : hcs asegs R HIA h1 = CS.
  Hypothesis Ehtop : htop asegs R HIA h1 = htop asegs R HIA h.
  Hypothesis Estk : hstkhi asegs R HIA h1 = hstkhi asegs R HIA h.
  Hypothesis Eflag : hflag asegs R HIA h1 = hflag asegs R HIA h.
  Hypothesis Evol : havol asegs R HIA h1 = havol asegs R HIA h.
  Hypothesis Efr : hfr asegs R HIA h1 = hfr asegs R HIA h.
  Hypothesis F64 : FB mod 64 = 0.
  Hypothesis FRSH : fresh_apart R LB LF FB 128.
  Hypothesis FHD : rw_cells asegs m1 FB [C8 w0; C8 w1; C8 w2].
  Hypothesis YYI : rw_cells asegs m1 YY (mpi_cells 0 (Z_to_bv 64 1) 0 padY).
  Hypothesis RHI : rw_cells asegs m1 RH (mpi_cells 0 (Z_to_bv 64 1) 0 padR).
  Hypothesis FSH : rw_cells asegs m1 (Z.shiftr FB 3 + al_sb AL) FSHSW.
  Hypothesis SAVE : rw_cells asegs m1 (bv_unsigned sp + -88) SAVEL.
  Hypothesis FRM : rw_cells asegs m1 sp1 FRAME.
  Hypothesis SThi : stk asegs m1 SPv (bv_unsigned sp + -88).
  Hypothesis STlo : stk asegs m1 lo sp1.
  Hypothesis MI1 : mem_inv asegs m1.
  Hypothesis PRES0 : presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [] m m1.
  Hypothesis SSH1 : sshad asegs AL m1 slo (bv_unsigned sp).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00S0?L15756354262.4 L19002855022.8 L19003035498.5 L19561366480.4 L19561366513.3 L19561531729.7 L19561547889.12L19561547889.4 L19561547889.9 L19561597301.6 L23372865473.7 L23372914373.8 L28516788675.4 L28516788706.3 L28516819778.6 L28516868706.11L28516868706.4 L28516868706.8 L28517016422.5 L29428324941.5 L37156630869.0 L38180633941.0 L43781740152.6 L43781953404.11L43781953404.4 L43781953404.8 L43782036701.3 L43782036732.2 L55616076308.8 L55616092944.6 L66151427842.16L9840374859.11 L9840374859.4  L9840374859.8  L9840620879.6  00000>00K00L00M00N00O00P00Q00R00S00T00`00a00b01801901:01;01<01N01O01P01Q01R01S01T01U01]02202302M03803903:03;S1R2lo3LOS3ALOS1R5NEEDR3NERFFFFFFFFFS2sp3sp13SP1FFS1R2lo3LOS3ALO3DLO3MC2FFFFS1R2lo3LOS3ALO3ACVSSFFFFFS2sp3SPRS1R2sp2lo3SLO3sp13SP1FS2FB2r03F641q1r1H2H02q02H4S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3NERFFF". (* [comment removed for export] *)
  Lemma sw_base : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "(1:.(1;.=Vlo,)(1:.(1;.(3?.VR,)Vlo,)(1:.(1;.(36.(2;.VR,))(3?.VR,))(1:.(1;.Vlo,(23.(23.Vsp1,+350.)(7:.VR,)))(1:.(1;.=(7:.VR,))(1:.(1;.=Vsp1,)(1:.(1;.(20.Vsp1,+8.)(23.(2?.&40.Vsp,)+58.))(1:.(1<.(2?.&40.Vsp,)(4;.+2.+40.))(1:.(1;.(20.$30.+8.)Vlo,)(1:.(1<.=VFB,)(1:.(1;.(20.VFB,+80.)(36.(2;.VR,)))(1:.(=.$6.(4<.VFB,+8.)=)(1:.(21.(1;.(20.VFB,+80.)VG,)(1;.(20.VG,+<0.)VFB,))(21.(1;.(20.VFB,+80.)(7;.(2;.VR,)))(1;.(7<.(2;.VR,))VFB,)))))))))))))))")
(* [comment removed for export] *).
  Proof.
    rt_facts. pose proof (art_data_lo asegs R HIA) as DLO. flat constr:(MCOK) 3%nat. intros MC1 MC2 _.
    flat constr:(FRSH) 4%nat. intros F0 F1 F2 F3.
    pose proof (fresh_apart_client R LB LF lo G 192 FB 128 FRSH GCR ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as APG.
    repeat split; try assumption;
      first [ clear - LOS ALO ACV; lia | clear - SLO SP1 NER NEEDR; lia | clear - NER NEEDR; lia | clear - SLO SP1 NER NEEDR LOS ALO ACV; lia | clear - SP1; lia | clear - SPR; lia
            | clear - MC2 DLO ALO LOS; lia | clear - F64; Z.div_mod_to_equations; lia | clear - APG; lia | idtac ].
    all: match goal with |- ?g => idtac "BASE-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L27883368372.3L39332637397.0L45513781034.5L6737722458.7 00000900:00M00eS2FB1a2HaSS1R2lo3sp14LOSP3NE0S1R3HIA1h2sp3TOP3sp13SPV". (* [comment removed for export] *)
  Lemma sw_ec : ECA R HIA h1 LB LF' m1 SPv lo 8 FRAME XO MC.
  Proof.
    flat constr:(sw_base) 10%nat. flclear sw_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO _.
    constructor; try assumption; try reflexivity.
    - clear; lia.
    - clear - LOSP NE0; lia.
    - rewrite Ehtop. clear - SPV TOP. lia.
    - intros a Ha. cbn [outside fst snd] in Ha. clear - Ha. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Notation HP01 := (presW_presA asegs R HIA h LB LF _ _ _ m m1 PRES0).

  Lemma sw_lfsub : forall b, In b (LB ++ fdata LF) -> In b (LB ++ fdata LF').
  Proof. intros b Hb. apply fdata_cons_sub. exact Hb. Qed.

  Lemma sw_topcs : forall x, CS x -> x < hstkhi asegs R HIA h.
  Proof. intros x Hx. eapply hcs_below_top. exact Hx. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L27626315921.6L3617752057.1 L50790584181.8L52615975131.5L59314923118.600000E00H00g01401CS2sp1G2lo3GSP3sp13SPVS1dS1R2sp2lo3sp14LOS'4LOSP3NE03SPVS2sp1G1a2Ha1KS1G2lo1a2Ha1S1K". (* [comment removed for export] *)
  Lemma sw_grp : ecp_grp_preA asegs R HIA MT h1 LB LF' m1 G g MC lo SPv (d + 1).
  Proof.
    flat constr:(sw_base) 10%nat. flclear sw_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO _. pose proof (hcs_ok asegs R HIA h) as CSOK.
    assert (CRS : client_range L (LB ++ fdata LF) (bv_unsigned sp) G 192).
    { intros a Ha. destruct (GCR a Ha) as [S|[D|B]]; [| right; left; exact D| right; right; exact B].
      destruct GSP as [K|K]; [exfalso; clear - S Ha K; lia| left; clear - Ha K; lia]. }
    unfold ecp_grp_preA. split.
    { pose proof (ecp_group_at_LB_any asegs MT m LB (LB ++ fdata LF) G g GAT GH1) as GAT0.
      eapply (ecp_group_at_presx asegs L MT m m1 _ LB (bv_unsigned sp) [] G g GAT0); [exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP01)| exact MI| exact MI1| exact CRS| exact I|].
      intros e He EO. exfalso. exact (grp_static_own asegs MT m LB G g e GAT GH1 He EO). }
    split; [exact GH1|]. split; [exact GPS|]. split; [exact GIMG|].
    split; [intros a Ha; destruct (GCR a Ha) as [S|[D|(b & Hb & Hr)]]; [left; exact S| right; left; exact D| right; right; exists b; split; [exact (sw_lfsub b Hb)| exact Hr]]|].
    split; [clear - GSP SPV; lia|]. split; [exact GMC|].
    split; [| eapply uw_obj_mono_d; [exact GUW| clear; lia]].
    rewrite Ehcs. eapply (presA_aobj asegs R); [exact CSOK| exact HP01| exact GOB| exact CRS| clear - LOS' LOSP SPV NE0; lia| exact sw_topcs].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L35693534892.2L55010346807.3L7377303863.3 00000700A00KS1G3GMCS1G2FB3APGS1G2FB3APG". (* [comment removed for export] *)
  Lemma sw_dxg : disjoint_from XO G 192.
  Proof.
    flat constr:(sw_base) 14%nat. flclear sw_base. intros _ _ _ _ _ _ _ _ _ _ _ _ APG _.
    cbn [disjoint_from fst snd]. split; [clear - APG; lia|]. split; [clear - APG; lia|]. split; [clear - GMC; lia| exact I].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L14152318755.7L2275137097.0 L30005700953.3L41135643578.5L63981324195.300000H00I00R00c00lS1R2FB1A2HA4FDAT3MC13MC2SS2FB1A2HAS2lo2FB1A2HA4FBLOS2FB1A2HA". (* [comment removed for export] *)
  Lemma sw_slot : forall A, (A = YY \/ A = RH) -> eslot R HIA h1 LB LF' SPv lo XO MC A.
  Proof.
    intros A HA.
    flat constr:(sw_base) 14%nat. flclear sw_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 F8 APG FDAT.
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & _ & _ & FBLO & SBND & APS). change (128 - 40) with 88 in IND.
    flat constr:(MCOK) 3%nat. intros MC1 MC2 _. unfold eslot.
    split; [eapply client_wrange_block; [exact IND| clear - HA; lia| clear - HA; lia]|].
    split; [left; clear - FBLO HA; lia|].
    split; [intros x Hx; cbn [outside fst snd] in *; split; [| exact I]; destruct HA as [-> | ->]; [exact (proj1 Hx)| exact (proj1 (proj2 Hx))]|].
    clear - FDAT MC1 MC2 HA. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0@L2275137097.0   L24931897273.4  L27817790484.146L30741553502.0  L59308586248.2  L66151427842.18 L66939970068.146Q10592319652.146Q19546948462.146Q33226532839.146Q34669211300.146Q35348450791.146Q9644305041.146 00000100=00W00X00^01<01V01a02A02L02W02b030SS2FB1A2HA2F0S2LF2ra2sp3LFB2FB3sp14SP10SS1i2HiS2FB1A2HA2r02F81q1r1H2H02q02H4S2LF2ra2sp3LFB2FB3sp14SP10S2LF3LFB2FBS2LF2ra2sp3LFB2FB3sp14SP102F02F8S2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FB2F0". (* [comment removed for export] *)
  Lemma sw_tmp : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "PA,$6.Ppad,(2.&40.)P,(21.(=.$6.R2.(20.VFB,+20.))(=.$6.R2.(20.VFB,+40.)))P,(19.$9.Vm1,R3.(46.=(47.&40.+1.)=R2.))(7=.VR,VHIA,VLB,(69.(5.$6.$6.)(11.$6.$6.VFB,+80.)VLF,)Vh1,VLB,Vm1,R4.(7>.R4.+1.==(41.(2.&40.))R3.$7?.))")
(* [comment removed for export] *).
  Proof.
    intros A pad HA CA.
    flat constr:(sw_base) 14%nat. flclear sw_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 F8 APG FDAT.
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS) as (CFB & _).
    pose proof (hcs_ok asegs R HIA h) as CSOK.
    unfold ejtmp. cbn [md_addr md_own mpd_blk].
    split.
    { unfold mpd_at, mpi_at. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [| left; reflexivity]. split; [exact CA|]. split; [clear - F8 HA; Z.div_mod_to_equations; lia|]. split; [clear - F0 HA; lia|]. split; [reflexivity|].
      split; [unfold MPI_MAX_LIMBS; clear; lia| split; reflexivity]. }
    split; [reflexivity|]. split; [discriminate|]. split; [intros b []|].
    rewrite Ehcs. destruct HA as [-> | ->]; [frame_aobj FSH YY 2%nat as OEX| frame_aobj FSH RH 2%nat as OEX]; exact OEX.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0>L11737279543.2L14887477089.3L15756354262.4L17617857471.5L18466806200.3L21617968149.3L33974372705.3L35269534236.5L37155769272.3L37156630869.0L38948636245.0L39595656495.7L59237258151.600000700@00O00]00f01201;01I01R01S01T01l02@S1e3MCsS2FB1e2KFS1R2lo4LOS'3ALOS2FB1e1A2HA2KSS2FB1e2KSS2sp3sp13SPVS2FB1e2KFS2FB1e1A2HA2KFS2FB1e2KSSSS1R1e3MC13MC23DI13DI22KIS1R2lo1e4LOS'3ALO2PC". (* [comment removed for export] *)
  Lemma sw_ext : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Pe,$:.PA,$6.P,(3:.R2.)P,(25.(=.$>.(?.R3.)$3;.))P,(21.(=.$6.R3.(20.VFB,+20.))(=.$6.R3.(20.VFB,+40.)))(80.VR,VHIA,Vh1,VLB,(69.(5.$6.$6.)(11.$6.$6.VFB,+80.)VLF,)Vm1,(20.Vsp1,+8.)Vlo,(69.(5.$6.$6.)(11.$6.$6.(20.VFB,+20.)(20.(20.VFB,+20.)+10.))(69.(5.$6.$6.)(11.$6.$6.(20.VFB,+40.)(20.(20.VFB,+40.)+10.))(69.(5.$6.$6.)(11.$6.$6.$30.(20.$30.+8.))(41.(5.$6.$6.)))))R4.R5.)")
(* [comment removed for export] *).
  Proof.
    intros e A OPe NSe HA.
    flat constr:(sw_base) 14%nat. flclear sw_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 F8 APG FDAT. pose proof (hcs_ok asegs R HIA h) as CSOK.
    destruct (ck_op_at e OPe h1 LF' m1 SPv HP01 MI1 HH1 Ehcs ltac:(clear - SPV; lia)) as (ME1 & OB1 & OL1 & PP1 & SS1 & SL1).
    flat constr:(OPe) 8%nat. flclear OPe. intros ME CR SEP MCs OB IM UWe BLK0.
    flat constr:(ME) 2%nat. intros FLt7 _. flat constr:(FLt7) 6%nat. flclear FLt7. intros _ _ E0 _ _ EOW.
    pose proof (fresh_apart_client R LB LF lo (md_addr e) 16 FB 128 FRSH CR ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS'; lia)) as KS.
    assert (KL : md_own e = LHeap -> 1 <= md_n e /\ (FB + 128 <= md_p e \/ md_p e + 4 * md_n e <= FB) /\ md_p e + 4 * md_n e <= lo
                                     /\ (md_p e + 4 * md_n e <= hl_img_lo L \/ hl_img_hi L <= md_p e)).
    { intros EO. flat constr:((BLK0 EO)) 5%nat. intros N1 IN P0 PC PIMG. flat constr:(FRSH) 4%nat. intros _ _ _ F3.
      specialize (F3 _ _ ltac:(apply in_app_iff; left; exact IN)). split; [exact N1|]. split; [exact F3|]. split; [clear - PC ALO LOS'; lia| exact PIMG]. }
    assert (OWH : md_own e <> LNull -> md_own e = LHeap) by (destruct (md_own e); [intros C; exfalso; exact (C eq_refl)| reflexivity| intros _; exfalso; exact (NSe eq_refl)]).
    flat constr:(MCOK) 3%nat. intros MC1 MC2 _. flat constr:(DIMG) 2%nat. intros DI1 DI2.
    unfold ej_ext.
    split; [exact ME1|].
    split; [intros a Ha; destruct (CR a Ha) as [S|[D|(b & Hb & Hr)]]; [left; exact S| right; left; exact D| right; right; exists b; split; [exact (sw_lfsub b Hb)| exact Hr]]|].
    split; [exact SS1|].
    split; [intros NN; left; exact (proj1 (proj2 (proj2 (KL (OWH NN)))))|].
    split; [cbn [disjoint_from fst snd]; split; [clear - KS; lia|]; split; [clear - KS; lia|]; split; [clear - MCs; lia| exact I]|].
    split.
    { intros EO. flat constr:((KL EO)) 4%nat. intros N1 KF _ KI. cbn [disjoint_from fst snd]. split; [clear - KF; lia|]. split; [clear - KF; lia|]. split; [clear - KI MC1 MC2 DI1 DI2; lia| exact I]. }
    split; [clear - KS HA; lia|].
    split; [intros NN; (flat constr:((KL (OWH NN))) 3%nat; intros _ KF _); clear - KF HA; lia|].
    split; [| exact IM].
    split; [rewrite Ehcs; exact OB1| intros ES; exfalso; exact (NSe ES)].
    all: match goal with |- ?g => idtac "EXT-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L13935699136.3 L26892418956.1 L41272413965.1 L62030908141.10L66151427842.16L696052597.9   00000<00@00D00h01B01`S2sp3sp13SPVS2spS2spS1R2sp2lo3sp14LOS'4LOSP3NE03SPV4SP64S2sp2r03SPA1q1r1H2H02q02H4S1R2sp2lo3sp13LO04LOSP3NE03SPV". (* [comment removed for export] *)
  Lemma sw_uw0 : uwc asegs m1 (arl_stklo R) (hstkhi asegs R HIA h1) (bv_unsigned sp) SPv (d + 1).
  Proof.
    flat constr:(sw_base) 10%nat. flclear sw_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO _.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    assert (UW1 : uwc asegs m1 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
    { eapply (uwc_presA R); [exact HP01| exact UW| clear; lia| intros a Ha; exact I| clear - LOS' LOSP SPV NE0 LO0; lia| apply hstkhi_le64; clear - LOS' LOSP SPV NE0 SP64 LO0; lia]. }
    rewrite Estk.
    pose proof SAVE as SV. chunk_split SV 9%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
    replace (bv_unsigned sp + -88 + 72) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
    eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UW1| clear - SPV; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L27883368372.10L52101693566.1300000T01BS1R3HIA2lo3sp12h14LOSP3NE04MCLO1a2HaS1R3HIA2lo2FB3sp12h14LOS'3ALO4LOSP3NE02F11a2Ha". (* [comment removed for export] *)
  Lemma sw_xouw : 28 <= d + 1 \/ forall a, SPv <= a < hstkhi asegs R HIA h1 -> outside XO a.
  Proof.
    flat constr:(sw_base) 12%nat. flclear sw_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 _.
    right. intros a Ha. cbn [outside fst snd]. split; [clear - Ha F1 ALO LOS' LOSP NE0; lia|]. split; [clear - Ha F1 ALO LOS' LOSP NE0; lia|]. split; [clear - Ha MCLO LOSP NE0; lia| exact I].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L31409498968.9 L66151427842.1600000S00oS1R2sp2lo3slo4SLO33sp14LOSP3NE03SPVS3sp12r04SP1M1q1r1H2H02q02H4". (* [comment removed for export] *)
  Lemma sw_ssh : sshad asegs AL m1 slo SPv.
  Proof.
    flat constr:(sw_base) 10%nat. flclear sw_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO _.
    exact (proj1 (sshad_split asegs AL m1 slo SPv (bv_unsigned sp) SSH1 ltac:(clear - SLO3 LOSP NE0 SPV; lia) ltac:(clear - SP1M; Z.div_mod_to_equations; lia))).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L34409126551.500000@S1R3MC13MC21x2Hx". (* [comment removed for export] *)
  Lemma sw_mc1 : rw_cells asegs m1 MC [C8 cnt].
  Proof.
    flat constr:(MCOK) 4%nat. intros MC1 MC2 MC3 _.
    eapply (presA_rw_cells asegs R); [exact HP01| exact MC0| | exact I].
    cbn [cells_size csize Nat.add]. intros x Hx. right. left. split; [clear - Hx MC1 MC2; lia| apply MC3; exact Hx].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Notation EPIJ := (EPI R HIA h1 LB LF' m1 SPv lo 8 FRAME XO MC (d + 1)).
  Local Notation EJJ := (EJ R HIA h1 LB LF' m1 SPv lo 8 FRAME XO MC).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L44158973781.1000005S3sp1". (* [comment removed for export] *)
  Lemma sw_spe : sp1 + 8 - 8 = sp1.
  Proof. clear. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L18915067017.4L28287220361.4L4781719053.2 L65232285359.100000=00J00P00TS1R2FB3ALO2F1S1R2FB3ALO2F1S1d2D0S2FB". (* [comment removed for export] *)
  Lemma sw_start : EPIJ 0 0 h1 LB m1 YY dY0 RH dR0.
  Proof.
    flat constr:(sw_base) 14%nat. flclear sw_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 F8 APG FDAT.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    unfold EPI. split.
    { eapply (ej_start R HIA h1 LB LF' m1 SPv lo 8 FRAME XO MC sw_ec m1 cnt (munch_refl _ _) (wmono_refl _ _) HH1 MI1); [rewrite sw_spe; exact STlo| rewrite sw_spe; exact FRM| exact sw_mc1]. }
    split.
    { unfold epair. split; [exact (sw_tmp YY padY (or_introl eq_refl) YYI)|]. split; [exact (sw_tmp RH padR (or_intror eq_refl) RHI)|].
      split; [intros O1; discriminate O1| intros b Hb; left; exact Hb]. }
    split; [exact (sw_slot YY (or_introl eq_refl))|]. split; [exact (sw_slot RH (or_intror eq_refl))|]. split; [left; clear; lia|].
    split; [left; split; [clear - F1 ALO; lia| clear - D0; lia]|].
    left. split; [clear - F1 ALO; lia| clear - D0; lia].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L4781719053.2000006S1d2D0". (* [comment removed for export] *)
  Lemma sw_k_d0 : 0 <= d + 1.
  Proof. pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0. clear - D0. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L51187461261.400000AS2sp3sp13SPV4SP64". (* [comment removed for export] *)
  Lemma sw_k_sp64 : SPv < 2^64.
  Proof. flat constr:(sw_base) 9%nat. flclear sw_base. intros _ _ _ _ _ _ SPV SP64 _. clear - SPV SP64. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L66151427842.1600000LS3sp12r04SP1M1q1r1H2H02q02H4". (* [comment removed for export] *)
  Lemma sw_k_spa : (SPv - 8) mod 16 = 0.
  Proof. rewrite sw_spe. clear - SP1M. Z.div_mod_to_equations. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma sw_k_slok : lo <= SPv - 8 - 848 - arl_need_ecp R.
  Proof. flat constr:(sw_base) 5%nat. flclear sw_base. intros _ _ _ LOSP _. rewrite sw_spe. exact LOSP. Qed.

  Ltac kit_side :=
    first [ exact sw_ec | exact TPV | exact sw_k_d0 | exact sw_k_sp64 | exact sw_k_spa | exact sw_k_slok | exact sw_uw0 | exact sw_xouw | exact sw_ssh
          | exact SLO1 | exact SLO3 | exact sw_grp | exact sw_dxg | exact IMG | (clear; lia) ].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00J0>L10596430123.1L12877541958.9L17080320687.1L18401844088.8L21617968149.3L22526773547.4L2275137097.0 L24128180555.1L26726941871.1L27188209011.3L28390317327.1L30353617105.9L30826141493.8L34673485611.1L34896805551.3L42101657670.9L46944522740.1L48132760585.9L55048118260.1L60326494657.1L60878866887.5L63062044369.9L64448757674.4L6899380056.1 L8402599844.3 L9631767084.2 00000400V00Z01201>01I01J01N01R01[01_02:02Y02]02i03K03O04204604;04N04i05405805@05GS2FBS1R2sp2lo2FB3sp14LOSP3NE03SPV4FBLOS2FBS1R2lo3sp14LOSP3NE04MCLOS2sp3sp13SPVS2FB1A1k2H2SS2FBS2FBS2FB1c2HcS2FBS1R2lo2FB3sp14LOSP3NE04FBLOS1R2sp2lo3sp14LOSP3NE03SPV4MCLOS2FBS2sp3sp13SPVS1R2sp2lo2FB3sp14LOSP3NE03SPV4FBLOS2FBS1R2sp2lo3sp14LOS'3ALO4LOSP3NE03SPVS2FBS3sp1S1R2FB4FDAT3MC13MC2S1R2lo2FB3sp14LOSP3NE04FBLOS2FB1A1k2H1S2FBS1A1k2H4S2FB2F0". (* [comment removed for export] *)
  Lemma sw_frame_k : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Pv,$6.Pf,$6.Phk,(3=.$9.VR,VHIA,)PLBk,(0.$4.)Pmk,P,(2.&40.)(3.(2.&8.))P,(81.VR,VHIA,Vh1,VLB,(69.(5.$6.$6.)(11.$6.$6.VFB,+80.)VLF,)Vm1,(20.Vsp1,+8.)Vlo,+8.(69.$18.(6<.(47.&40.VFB,))(41.$18.))(69.(5.$6.$6.)(11.$6.$6.(20.VFB,+20.)(20.(20.VFB,+20.)+10.))(69.(5.$6.$6.)(11.$6.$6.(20.VFB,+40.)(20.(20.VFB,+40.)+10.))(69.(5.$6.$6.)(11.$6.$6.$30.(20.$30.+8.))(41.(5.$6.$6.)))))$30.R5.R4.R3.R2.R1.)(1:.(19.$9.R2.VFB,(69.$18.(6<.Vw0,)(69.$18.(6<.Vw1,)(69.$18.(6<.Vw2,)(41.$18.)))))(1:.(19.$9.R2.(20.(6=.VFB,+3.)(6>.(32.VR,)))(69.$18.(6?.(47.&8.+?1.))(69.$18.(6?.(47.&8.+?1.))(69.$18.(6?.(47.&8.+?1.))(69.$18.(6?.(47.&8.+?1.))(69.$18.(6?.(47.&8.=))(69.$18.(6?.(47.&8.=))(69.$18.(6?.(47.&8.+?2.))(69.$18.(6?.(47.&8.+?2.))(69.$18.(6?.(47.&8.=))(69.$18.(6?.(47.&8.=))(69.$18.(6?.(47.&8.+?2.))(69.$18.(6?.(47.&8.+?2.))(69.$18.(6?.(47.&8.+?8.))(69.$18.(6?.(47.&8.+?8.))(69.$18.(6?.(47.&8.+?3.))(69.$18.(6?.(47.&8.+?3.))(41.$18.))))))))))))))))))(1:.(19.$9.R2.(20.(2?.&40.Vsp,)-58.)(69.$18.(6<.Vs9,)(69.$18.(6<.Vs8,)(69.$18.(6<.Vs7,)(69.$18.(6<.Vs6,)(69.$18.(6<.Vs5,)(69.$18.(6<.Vs4,)(69.$18.(6<.Vs3,)(69.$18.(6<.Vs2,)(69.$18.(6<.Vs1,)(69.$18.(6<.Vs0,)(69.$18.(6<.Vra,)(41.$18.)))))))))))))(1:.(57.$9.R2.(20.Vsp1,+8.)(20.(2?.&40.Vsp,)-58.))(1:.(61.$9.VR,VHIA,R4.VLB,VLF,(2?.&40.Vsp,)(3?.VR,)(69.(5.$6.$6.)(11.$6.$6.$30.(20.$30.+8.))(41.(5.$6.$6.)))Vm,R2.)(1:.Px,$6.P,(33.$9.VR,VHIA,Vh,R1.)(33.$9.VR,VHIA,R6.R2.)(=.$6.(40.$9.VR,VHIA,R4.)(40.$9.VR,VHIA,Vh,))))))))")
(* [comment removed for export] *).
  Proof.
    flat constr:(sw_base) 14%nat. flclear sw_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 F8 APG FDAT.
    intros v f hk LBk mk J. pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & _ & _ & FBLO & SBND & APS).
    pose proof (hcs_ok asegs R HIA h) as CSOK. flat constr:(MCOK) 3%nat. intros MC1 MC2 _.
    assert (DJ : forall A k, (A + k <= YY \/ YY + 16 <= A) -> (A + k <= RH \/ RH + 16 <= A) -> MC + 8 <= A \/ A + k <= MC -> disjoint_from XO A k).
    { intros A k H1 H2 H4. cbn [disjoint_from fst snd]. split; [clear - H1; lia|]. split; [clear - H2; lia|]. split; [clear - H4; lia| exact I]. }
    split.
    { eapply (presA_rw_cells asegs R); [exact PXk| exact FHD| |].
      - cbn [cells_size csize Nat.add]. eapply client_range_block; [exact INH| clear; lia| clear; lia].
      - cbn [cells_size csize Nat.add]. apply DJ; [clear; lia| clear; lia| clear - FDAT MC1 MC2; lia]. }
    split.
    { rewrite <- Ehcs in CSOK.
      eapply (presA_shadow_cells_sh asegs R (hcs asegs R HIA h1) LB LF' SPv (arl_stklo R) (hstkhi asegs R HIA h1) XO m1 mk FB _ CSOK); [| exact F8| clear - F0; lia| exact PXk| exact FSH|].
      - cbn [cells_size csize Nat.add]. rewrite Ehcs. eapply crange_sub; [exact CFB| clear; lia| clear; lia].
      - cbn [cells_size csize Nat.add]. intros c Hc. right; right; left. exists (FB, 128). split; [left; reflexivity| cbn [fst snd]; clear - Hc; lia]. }
    split.
    { eapply (presA_rw_cells asegs R); [exact PXk| exact SAVE| |].
      - apply client_range_stack. clear - SPV. lia.
      - cbn [cells_size csize Nat.add]. apply DJ; [right; clear - FBLO LOSP NE0 SPV; lia| right; clear - FBLO LOSP NE0 SPV; lia| left; clear - MCLO LOSP NE0 SPV; lia]. }
    split.
    { eapply (presA_stk asegs R); [exact PXk| exact SThi| clear; lia|].
      apply DJ; [right; clear - FBLO LOSP NE0 SPV; lia| right; clear - FBLO LOSP NE0 SPV; lia| left; clear - MCLO LOSP NE0 SPV; lia]. }
    assert (HCS' : forall x, CS x -> hcs asegs R HIA hk x) by (intros x Hx; apply HCSk; rewrite Ehcs; exact Hx).
    assert (HS' : hstkhi asegs R HIA hk = hstkhi asegs R HIA h) by (rewrite HSk; exact Estk).
    split; [| split; [exact HCS'| exact HS']].
    eapply (presW_hmono R HIA h hk); [| exact HCS'| exact HS'].
    flat constr:(PRES0) 2%nat. intros P0 C123. split; [| exact C123].
    eapply presA_trans.
    - eapply presA_weaken; [exact P0| intros b Hb; exact Hb| intros b Hb; exact Hb| apply Z.le_refl| apply Z.le_refl| apply Z.le_refl| intros x _; exact I].
    - eapply (presA_drop_fresh_gen R LB LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) _ FB 128 RH (RH + 16)); [| exact FRSH| clear; lia| clear; lia| clear - ALO LOS' LOSP NE0 SPV; lia].
      eapply (presA_drop_fresh_gen R LB LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) _ FB 128 YY (YY + 16)); [| exact FRSH| clear; lia| clear; lia| clear - ALO LOS' LOSP NE0 SPV; lia].
      rewrite <- Estk.
      eapply presA_weaken; [exact PXk| intros b Hb; exact Hb| intros b Hb; right; exact Hb| clear - SPV; lia| apply Z.le_refl| apply Z.le_refl|].
      intros x Hx. first [clear - Hx; cbn [outside fst snd] in *; tauto | cbn [outside fst snd] in *; tauto]. (* [comment removed for export] *)
    all: match goal with |- ?g => idtac "FRAMEK-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01E0@L10719636406.2  L139395489.0    L16096065997.4  L1685717371.0   L17377056818.7  L19617214306.42 L22396302793.0  L2275137097.0   L2330751324.250 L2330751324.251 L24023900370.0  L24041496642.9  L25123160167.4  L27560104668.7  L32508069537.0  L32555661832.0  L35340800220.3  L35655538581.7  L35742342723.1  L35876627029.0  L39607668974.2  L42411609006.0  L43182968046.5  L43182968046.6  L47303665221.5  L47303667269.4  L47660518203.5  L57048595011.1  L60109250162.3  L64148832490.250L64148832490.251L64581097568.9  L6504494751.5   L65137213576.0  L8747829433.4   Q10057262476.251Q10604220239.251Q11799173861.256Q11799173861.257Q12288179942.251Q12452402922.247Q12452533583.251Q12452615637.251Q14100645190.251Q17841111252.253Q18376606873.252Q19278887980.251Q2447754665.252 Q24629685439.251Q26760028061.252Q29742860821.251Q33422860542.252Q3436595000.251 Q34966617690.251Q37347831926.251Q39078748811.252Q40354196046.256Q40354196046.257Q40360481330.248Q40360481330.252Q4133274111.251 Q43207879522.251Q44298944140.248Q44298944140.252Q44301027056.256Q44301027056.257Q47079640488.251Q47228431932.256Q47228431932.257Q47812103402.247Q48119910507.256Q48119910507.257Q54783643045.251Q5596578838.256 Q5596578838.257 Q57570454300.251Q59619599055.251Q59619648085.251Q63435846322.252Q64228675114.255Q64228675114.256Q64751009820.251Q6560739173.251 Q67892150791.252Q6912043754.253 00000600700800900N00O00P00Q00R00S00T00l01;01P01Q01R01[02402502602702802902:02;02F02G02H02S03O04K04h04i04j04k04l04m05O06106206=06H06S06T07007Z07[07\07]08?08J08K08L09>09?09@09b0:D0:T0:d0:o0;00;@0;P0<20<T0<U0=;0=a0=l0>e0?^0?i0?j0?k0@U0@V0@W0@X0Ab0Bl0Bm0Bn0Bo0CKS1d2D0SFSS1R3HIA1h1N3BUD1v3HVBFSSFFSS1R3HIA1h1N1d4BUDF1f3HFBS1R2FB4SBND3MC2S1R3HIA1h1N3BUD1v3HVBSSS1N1v3HVBS1R3HIA1h2sp2lo3TOP5HTOPeFSFSFFFS1N1d1f3HFBFFS1R2lo4LOS'S1R2LF2ra2sp3LFB2FB3sp14SP102HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2LF2ra2sp3LFB2FB3sp14SP102HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R3HIA1h1N1d4BUDF1f3HFB4FRC0FSFFFS1R2LF3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3LFB2FB2HB5Ha_st5Hl_st5SAEstFS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBFS1R2LF3LFB2FB2HB5Ha_st5Hl_stS1R2LF2sp2lo3LFB3SLO2FB3NE02HB5Ha_st5Hl_stFFFS1R2LF2sp2lo3LFB2FB2HB5Ha_st5Hl_stS2LF3LFB2FBFFS1R2LF2sp2lo3LFB3SLO2FB3sp13SP13NE02HB5Ha_st5Hl_stFFS1R2LF3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3LFB2FB2HBS1R2LF3LFB2FB2HBS2LF3LFB2FBFS1R2LF3LFB2FB2HBS1R2LF3LFB2FB2HBS1R2LF3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3LFB2FB2HB5Ha_st5Hl_st5SAEstFS1R2LF3LFB2FB3ALO2HB5Ha_st5Hl_st5SAEstS1R2LF3LFB2FB3ALO2HB5Ha_st5Hl_st5SAEstS2LF3LFB2FBS1R2LF2sp2lo3LFB3SLO2FB4LOS'3ALO3NE02HB5Ha_st5Hl_st5SAEstS1R2LF2sp2lo3LFB3SLO2FB4LOS'3ALO3NE02HB5Ha_st5Hl_st5SAEstS2LF3LFB2FBFFS1R2LF2sp2lo3LFB2FB3sp13SP12HB5Ha_st5Hl_stFFFS1R2LF2ra2sp2lo3LFB3SLO3SPA2FB3sp13LO03NE04SP102F02F82HB5Ha_st5Hl_st5SAEstS1R2LF2ra2sp2lo3LFB3SLO3SPA2FB3sp13LO03NE04SP102F02F82HB5Ha_st5Hl_st5SAEstFFFS1R2LF3LFB2FB2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  Lemma sw_fin : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Pv,$6.Pf,$6.Phk,(3=.$9.VR,VHIA,)PLBk,(0.$4.)Pmk,P,(2.&40.)(3.(2.&8.))PdYk,$:.PdRk,$:.Pr,$6.Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(82.VR,VHIA,Vh1,VLB,(69.(5.$6.$6.)(11.$6.$6.VFB,+80.)VLF,)Vm1,(20.Vsp1,+8.)Vlo,+8.(69.$18.(6<.(47.&40.VFB,))(41.$18.))(69.(5.$6.$6.)(11.$6.$6.(20.VFB,+20.)(20.(20.VFB,+20.)+10.))(69.(5.$6.$6.)(11.$6.$6.(20.VFB,+40.)(20.(20.VFB,+40.)+10.))(69.(5.$6.$6.)(11.$6.$6.$30.(20.$30.+8.))(41.(5.$6.$6.)))))$30.(20.Vd,+1.)R18.R17.R16.R15.R14.(20.VFB,+20.)R13.(20.VFB,+40.)R12.)P,(1:.(1<.(74.(4;.+2.+1?.))R12.)(1;.R12.=))P,(1;.(20.R1:.(13.+2.$83.))(72.VN,))P,(1;.(20.R1:.(13.+2.(52.(20.Vd,+1.))))(73.VN,Vd,))(75.$9.(76.$9.VR,VHIA,R1:.Vmo0,)$77.(5:.(5;.R14.(47.&40.Vsp1,)Vgp,Vtp,R13.R12.R11.Vsp,(47.&40.Vsp1,)R10.R?.R>.R=.R<.R;.R:.R9.(47.&40.VFB,)(47.&40.R15.)(47.&40.VG,)(47.&40.(20.VFB,+40.))(47.&40.(20.VFB,+20.))(47.&40.(20.VQ,+10.))(47.&40.(20.(6=.VFB,+3.)(6>.(32.VR,))))(47.&40.VFB,)Vs10,Vs11,R8.R7.R6.R5.)VF,(47.&40.+<;?90.)Vfc,(5=.(2.&40.))R18.(5>.$9.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros S HR HVB HFB.
    flat constr:(sw_base) 14%nat. flclear sw_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 F8 APG FDAT.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    assert (FRC0 : 0 <= fr_charge (d + 1)) by (unfold fr_charge; clear - D0; lia).
    pose proof (conj S I) as Sbox. clear S.
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    (* [comment removed for export] *)
    zstep. zstep.
    flat constr:(Sbox) 2%nat. flclear Sbox. intros S _. clear MU WM LAWS KINV.
    rewrite <- sw_spe.
    eapply ep_free with (h := h1) (LB := LB) (LF := LF') (m := m1) (SP := SPv) (lo := lo) (FR := 8) (FRAME := FRAME) (XO := XO) (MC := MC)
                        (dd := d + 1) (STKMAX := 848) (A1 := YY) (d1 := dYk) (A2 := RH) (d2 := dRk) (v := v) (f := f) (RET := 0xcbf98);
      first [ kit_side | exact HFREE | exact S | reflexivity
            | (rewrite Evol; unfold AVOL_CALL in *; clear - BUD HVB; lia) | (rewrite Efr; clear - BUDF HFB FRC0; lia) | idtac ].
    all: match goal with |- forall _, _ => idtac | |- ?g => idtac "FIN-FREE1-LEFT:" g end.
    intros h' LB' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' S'. rewrite sw_spe.
    pose proof (conj S' I) as Sbox. clear S'.
    pose proof (AIh_laws asegs R HIA h') as LAWS. pose proof (KF_kinv asegs R HIA h' mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m') as MU. pose proof (wmono_refl asegs m') as WM.
    (* [comment removed for export] *)
    zstep. zstep.
    flat constr:(Sbox) 2%nat. flclear Sbox. intros S' _. clear MU WM LAWS KINV.
    rewrite <- sw_spe.
    eapply ep_free with (h := h1) (LB := LB) (LF := LF') (m := m1) (SP := SPv) (lo := lo) (FR := 8) (FRAME := FRAME) (XO := XO) (MC := MC)
                        (dd := d + 1) (STKMAX := 848) (A1 := RH) (d1 := dRk) (A2 := YY) (v := v + AVOL_CALL) (f := f + fr_charge (d + 1)) (RET := 0xcbfa0);
      first [ kit_side | exact HFREE | exact (epi_swap R HIA h1 LB LF' m1 SPv lo 8 FRAME XO MC (d + 1) _ _ _ _ _ _ _ _ _ S') | reflexivity
            | (rewrite Evol; unfold AVOL_CALL in *; clear - BUD HVB; lia) | (rewrite Efr; clear - BUDF HFB FRC0; lia) | idtac ].
    all: match goal with |- forall _, _ => idtac | |- ?g => idtac "FIN-FREE2-LEFT:" g end.
    intros h'' LB'' m'' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' S''. rewrite sw_spe.
    flat constr:(S'') 3%nat. intros J' P' _.
    flat constr:((sw_frame_k _ _ h'' LB'' m'' J')) 7%nat. intros FHD' FSH' SAVE' SThi' PRESa HCS' HS'.
    pose proof J' as [HH' SUB' PX' MI' HT' HSk' HF' HCSk' HV' HFR' [ck MC'] ST' FR'].
    flat constr:(P') 4%nat. intros _ _ _ COV.
    rewrite sw_spe in ST', FR'.
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & _ & _ & AP & _ & _ & FBLO & SBND & APS). change (128 / 8) with 16 in SBND, APS.
    pose proof (hcs_ok asegs R HIA h'') as CSOK'.
    assert (CFB' : crange (hcs asegs R HIA h'') FB 128) by (eapply crange_mono; [exact HCS'| exact CFB]).
    pose proof (hcs_stack asegs R HIA h'') as SCS0'. rewrite HS' in SCS0'.
    pose proof (hm_top asegs R HIA h _ _ _ HH) as HTOPe.
    assert (SCS' : crange (hcs asegs R HIA h'') lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0'| clear - LOS'; lia| clear - TOP HTOPe; lia]).
    assert (DMS : disjoint_from [(Z.shiftr FB 3 + al_sb AL, Z.shiftr FB 3 + al_sb AL + 16)] MC 8).
    { flat constr:(MCOK) 3%nat. intros _ MC2 _. cbn [disjoint_from fst snd]. split; [left; clear - MC2 SBND; lia| exact I]. }
    pose proof (munch_refl [(Z.shiftr FB 3 + al_sb AL, Z.shiftr FB 3 + al_sb AL + 16)] m'') as MUs. pose proof (wmono_refl asegs m'') as WMs.
    pose proof (conj MC' I) as MCb. clear MC'. clear S'' J' P'.
    pose proof (AIh_laws asegs R HIA h'') as LAWS. pose proof (KF_kinv asegs R HIA h'' mo0) as KINV.
    (* [comment removed for export] *)
    do 8 zstep.
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSH9 end.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    flat constr:(MCb) 2%nat. flclear MCb. intros MC' _.
    pose proof (rw_cells_transport asegs _ _ _ _ _ MC' MUs WMs DMS) as MC9.
    eapply ck_exit with (FBx := FB) (sp1x := sp1) (hk := h'') (LBk := LB'') (v := v + AVOL_CALL + AVOL_CALL) (f := f + fr_charge (d + 1) + fr_charge (d + 1));
      first [ exact SP1 | exact SP1M | exact F64 | exact FRSH | exact CFB | exact HCS' | exact HS' | exact HR
            | exact SUB' | (exists ck; exact MC9) | eassumption
            | (rewrite HT'; exact Ehtop) | (rewrite HF'; exact Eflag) | (rewrite <- Evol; exact HV') | (rewrite <- Efr; exact HFR')
            | (clear - HVB; lia) | (clear - HFB; lia)
            | (intros b Hb; destruct (COV b Hb) as [K|K]; [exact K| cbn in K; destruct K])
            | idtac ].
    all: match goal with |- ?g => idtac "FIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "01N0@L10759442451.11 L11804947146.2  L12772973345.0  L1384220320.234 L1509615061.253 L17715532577.0  L18138771336.0  L18200506632.4  L18202523651.2  L18815086793.0  L19612793763.40 L19612793763.41 L19612794658.41 L19613236761.40 L19627664386.39 L19627664386.40 L19701203543.3  L20201646333.1  L21270536508.2  L21272684599.3  L21662842952.0  L22180421418.7  L22948774624.1  L23268210308.0  L2397676628.0   L24028928706.11 L24029158082.14 L26083066526.2  L26460285062.11 L27172298953.0  L28147100002.2  L28170680517.6  L28185076439.4  L28370701879.3  L28372846396.2  L29892234441.0  L35742342723.1  L35876627029.0  L3617752057.1   L37163373328.4  L37163587611.5  L37166975074.2  L37178305050.4  L39330890445.10 L40280805793.0  L40647720021.3  L41233509830.14 L41233608134.11 L42452947324.10 L42452947324.7  L42452947324.8  L42452947324.9  L42455321454.10 L42455321454.9  L48055636600.7  L48447136048.1  L49129880301.1  L50187955763.2  L50434476514.2  L5044772985.2   L51766526058.2  L52061118241.253L52321282603.2  L52520404101.253L53512949285.253L5367507532.1   L54665455956.2  L54943646869.3  L57048595011.1  L59068485258.4  L59425782813.210L5965930676.2   L60192626018.10 L60928256768.10 L61279635374.1  L61281732014.3  L61281816229.4  L6506486858.6   L6506486858.7   L6506486858.8   L6506486858.9   L6509260272.10  L6509260272.9   L65199732229.12 L65988345860.2  L67549518805.4  L67555566303.4  L67555781076.5  L67560749485.2  L68543245747.7  L68544542625.5  L68661285192.0  L8226051974.1   L8505146808.1   00000100:00;00<00=00>00?00@00A00B00C00D00E00F00G00H00I00J00K00U00V00i00j00k00l01F01l02402502602702802902C02D02E02F02G02J02K02L02M02N02O02P02Q03<03[03\03]03^03_03`03a03o04004104704804904B04C04I05105Y05Z05[05\05]05j05k05l06E06Y06Z06[06\06]06^06_06`06a06b06c06d06e06f06g06h06i06j06k06l06mFS2LB4C24HSFFSSFFSFFFFFFFFFS1G2FB3APGSS1g1p1N4SWP03MPN2G0FSSS1R3HIA1h1g1p1N3BUD3MPN2G0S1R3HIA1h1g1p1N1d4BUDF4FRC03CF23MFN2I0S2LF3LFBFSFFFS1G2FB3APGFSFSS1dFFFFFSFS1R3HIA1h1g1p1N1d4BUDF4SWF04FRC03CF23MFN2I0S1R3HIA1h1g1p1N3BUD4SWP03MPN2G0FFFFFFS1g1p1N3MPN2G0FFS1N2N0FFS2LB4C24HFS1d2D0S2LF2ra2sp3LFB2FB3sp14SP103dY12r13dR22r2S2LF2ra2sp3LFB2FB3sp14SP103dY12r13dR22r2FFFFS1p1N3NNY3NRYFFS1g1p1N1d4SWF03CF23MFN2I0S1g1p1N1d3CF23MFN2I0FFFFFFFFFFFFFFFFFSFF". (* [comment removed for export] *)
  Lemma sw_body : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)(75.$9.(76.$9.VR,VHIA,Vh1,Vmo0,)$77.(5:.(5;.R10.(47.&40.Vsp1,)Vgp,Vtp,R?.R>.R=.Vsp,(47.&40.Vsp1,)R<.R;.R:.R9.R8.R7.R6.R5.(47.&40.VFB,)(47.&40.VQ,)(47.&40.VG,)(47.&40.(20.VFB,+40.))(47.&40.(20.VFB,+20.))(47.&40.(20.VQ,+10.))(47.&40.(20.(6=.VFB,+3.)(6>.(32.VR,))))(47.&40.VFB,)Vs10,Vs11,R4.R3.R2.R1.)VF,(47.&40.+<;?60.)Vfc,(5=.(2.&40.))Vm1,(5>.$9.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6.
    flat constr:(sw_base) 14%nat. flclear sw_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 F8 APG FDAT.
    flat constr:(ck_budget) 12%nat. flclear ck_budget. intros N0 (NP0 & NPN) D0 MMB SWP0 SWF0 FRC0 FRC1 _ _ _ CF2.
    destruct (ck_op_pt (pt_X p) ltac:(left; reflexivity)) as (OPX & NSX & NNX & _).
    destruct (ck_op_pt (pt_Y p) ltac:(right; left; reflexivity)) as (OPY & NSY & NNY & _).
    flat constr:(PAT) 6%nat. intros EAX EAY _ MXr MYr _.
    flat constr:(MXr) 6%nat. intros _ _ _ _ NRX _. flat constr:(MYr) 6%nat. intros _ _ _ _ NRY _.
    flat constr:(OPX) 8%nat. intros _ _ _ XMC _ _ XUW _. flat constr:(OPY) 8%nat. intros _ _ _ YMC _ _ YUW _.
    destruct (MMB (md_n (pt_Y p)) (md_n (pt_Y p)) ltac:(clear - NRY NNY; lia) ltac:(clear - NRY NNY; lia)) as [[MP0 MPN] [MF0 MFN]].
    unfold check_pubkey_PHIn in BUD. unfold check_pubkey_FRn in BUDF.
    assert (G0 : 0 <= grow_PHI N + intop_PHIn N) by (unfold intop_PHIn, grow_PHI; unfold AVOL_CALL; clear - N0; lia).
    assert (I0 : 0 <= intop_FRn (d + 1) + calls_FR 3 (d + 1)) by (unfold intop_FRn, calls_FR, fr_charge; clear - D0; lia).
    pose proof sw_start as S0.
    pose proof (conj S0 I) as Sbox; clear S0. pose proof (AIh_laws asegs R HIA h1) as LAWS. pose proof (KF_kinv asegs R HIA h1 mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    (* [comment removed for export] *)
    do 5 zstep.
    flat constr:(Sbox) 2%nat. flclear Sbox. intros S0 _. clear MU WM LAWS KINV.
    rewrite <- sw_spe.
    eapply ep_mulmod with (h := h1) (LB := LB) (LF := LF') (m := m1) (SP := SPv) (lo := lo) (FR := 8) (FRAME := FRAME) (XO := XO) (MC := MC)
                          (dd := d + 1) (slo := slo) (STKMAX := 848) (G := G) (g := g) (A1 := YY) (d1 := dY0) (A2 := RH) (d2 := dR0)
                          (eA := pt_Y p) (eB := pt_Y p) (v := 0) (f := 0) (RET := 0xcbf74);
      first [ kit_side | exact HMM | exact S0 | exact YMC | reflexivity
            | exact (or_intror (or_intror (sw_ext (pt_Y p) YY OPY NSY (or_introl eq_refl))))
            | (left; reflexivity)
            | (eapply uw_obj_mono_d; [exact YUW| clear; lia])
            | (clear - APG; lia)
            | (cbn [md_n]; exact MP0) | (cbn [md_n]; exact MF0)
            | (cbn [length]; clear - LFB; lia)
            | (cbn [md_n]; rewrite Evol; clear - BUD MP0 MPN SWP0 G0; unfold AVOL_CALL in *; lia)
            | (cbn [md_n]; rewrite Efr; clear - BUDF MF0 MFN SWF0 I0 FRC0 CF2; lia)
            | (unfold C24_ECP_MUL_MOD; unfold C24_ECP_CHECK_PUBKEY in C24H; clear - C24H; lia)
            | (rewrite EAY; reflexivity)
            | idtac ].
    all: match goal with |- forall _, _ => idtac | |- ?g => idtac "MULMOD-CALL-LEFT:" g end.
    cbn [md_n]. intros h2 LB2 m2 dY1 r1 t0_1 t1_1 t2_1 a1_1 a2_1 a3_1 a4_1 a5_1 a6_1 a7_1 t3_1 t4_1 t5_1 t6_1 S1 [RR1 BK1] SZ1. rewrite sw_spe.
    pose proof (conj S1 I) as Sbox; clear S1. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. if_cases KR1; zify_cond KR1.
    { zstep. flat constr:(Sbox) 2%nat. flclear Sbox. intros S1 _. clear MU WM LAWS KINV.
      eapply (sw_fin _ _ h2 LB2 m2 dY1 dR0 r1); [exact S1| exact RR1
        | unfold check_pubkey_PHIn; clear - MP0 MPN SWP0 G0; unfold AVOL_CALL in *; lia| unfold check_pubkey_FRn; clear - MF0 MFN SWF0 I0 FRC0 CF2; lia]. }
    (* [comment removed for export] *)
    do 4 zstep.
    flat constr:(Sbox) 2%nat. flclear Sbox. intros S1 _. clear MU WM LAWS KINV.
    rewrite <- sw_spe.
    eapply ep_rhs with (h := h1) (LB := LB) (LF := LF') (m := m1) (SP := SPv) (lo := lo) (FR := 8) (FRAME := FRAME) (XO := XO) (MC := MC)
                       (dd := d + 1) (slo := slo) (STKMAX := 848) (G := G) (g := g) (A1 := RH) (d1 := dR0) (A2 := YY) (d2 := dY1) (eA := pt_X p) (N := N)
                       (v := 0 + mm_PHIn 0 (md_n (pt_Y p)) (md_n (pt_Y p)) (md_n dP)) (f := 0 + mm_FRn 0 (md_n (pt_Y p)) (md_n (pt_Y p)) (md_n dP) (d + 1)) (RET := 0xcbf88);
      first [ kit_side | exact HSR | exact (epi_swap R HIA h1 LB LF' m1 SPv lo 8 FRAME XO MC (d + 1) _ _ _ _ _ _ _ _ _ S1)
            | exact (sw_ext (pt_X p) RH OPX NSX (or_intror eq_refl)) | reflexivity | exact SGA | exact SGB | exact VP | exact NLE | exact NNX | exact XMC
            | exact SWP0 | exact SWF0
            | (eapply uw_obj_mono_d; [exact XUW| clear; lia])
            | (clear - APG; lia)
            | (cbn [length]; clear - LFB; lia)
            | (rewrite Evol; clear - BUD MP0 MPN SWP0 G0; unfold AVOL_CALL in *; lia)
            | (rewrite Efr; clear - BUDF MF0 MFN SWF0 I0 FRC0 CF2; lia)
            | (unfold C24_ECP_SW_RHS; unfold C24_ECP_CHECK_PUBKEY in C24H; clear - C24H; lia)
            | (rewrite EAX; reflexivity)
            | idtac ].
    all: match goal with |- forall _, _ => idtac | |- ?g => idtac "RHS-CALL-LEFT:" g end.
    intros h3 LB3 m3 dR2 r2 t0_2 t1_2 t2_2 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 t3_2 t4_2 t5_2 t6_2 S2 [RR2 BK2] SZ2. rewrite sw_spe.
    pose proof (conj S2 I) as Sbox; clear S2. pose proof (AIh_laws asegs R HIA h3) as LAWS. pose proof (KF_kinv asegs R HIA h3 mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    (* [comment removed for export] *)
    zstep. if_cases KR2; zify_cond KR2.
    2:{ zstep. flat constr:(Sbox) 2%nat. flclear Sbox. intros S2 _. clear MU WM LAWS KINV.
      eapply (sw_fin _ _ h3 LB3 m3 dY1 dR2 r2); [exact (epi_swap R HIA h1 LB LF' m1 SPv lo 8 FRAME XO MC (d + 1) _ _ _ _ _ _ _ _ _ S2)| exact RR2
        | unfold check_pubkey_PHIn; clear - MP0 MPN SWP0 G0; unfold AVOL_CALL in *; lia| unfold check_pubkey_FRn; clear - MF0 MFN SWF0 I0 FRC0 CF2; lia]. }
    (* [comment removed for export] *)
    do 3 zstep.
    flat constr:(Sbox) 2%nat. flclear Sbox. intros S2 _. clear MU WM LAWS KINV.
    flat constr:(S2) 3%nat. intros _ FLt8 _. flat constr:(FLt8) 3%nat. flclear FLt8. intros (_ & EAR2 & _) (_ & EAY1 & _) _.
    rewrite <- sw_spe.
    eapply ep_cmp with (h := h1) (LB := LB) (LF := LF') (m := m1) (SP := SPv) (lo := lo) (FR := 8) (FRAME := FRAME) (XO := XO) (MC := MC)
                       (dd := d + 1) (STKMAX := 848) (ENTRY := A_MPI_CMP_MPI_E) (A1 := RH) (d1 := dR2) (A2 := YY) (d2 := dY1) (eX := dY1) (eY := dR2) (RET := 0xcbfe4);
      first [ kit_side | exact (A_mpi_cmp_mpi_spec AL IMG) | exact S2 | reflexivity
            | exact (or_intror (or_introl eq_refl)) | exact (or_introl eq_refl)
            | (rewrite EAY1; reflexivity) | (rewrite EAR2; reflexivity)
            | idtac ].
    all: match goal with |- forall _, _ => idtac | |- ?g => idtac "CMP-CALL-LEFT:" g end.
    intros m4 t0_3 t1_3 t2_3 a1_3 a2_3 a3_3 a4_3 a5_3 a6_3 a7_3 t3_3 t4_3 t5_3 t6_3 S3. rewrite sw_spe.
    pose proof (conj S3 I) as Sbox; clear S3. pose proof (AIh_laws asegs R HIA h3) as LAWS. pose proof (KF_kinv asegs R HIA h3 mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) m4) as MU. pose proof (wmono_refl asegs m4) as WM.
    (* [comment removed for export] *)
    destruct (sgn3 (mpd_val dY1) (mpd_val dR2)) as [E|[E|E]]; rewrite E.
    all: do 6 zstep.
    all: (flat constr:(Sbox) 2%nat; flclear Sbox; intros S3 _); clear MU WM LAWS KINV.
    1: ck_s3_lit (-19584). 2: ck_s3_lit 0. 3: ck_s3_lit (-19584).
    all: eapply (sw_fin _ _ h3 LB3 m4 dY1 dR2); [exact (epi_swap R HIA h1 LB LF' m1 SPv lo 8 FRAME XO MC (d + 1) _ _ _ _ _ _ _ _ _ S3)| clear; lia
        | unfold check_pubkey_PHIn; clear - MP0 MPN SWP0 G0; unfold AVOL_CALL in *; lia| unfold check_pubkey_FRn; clear - MF0 MFN SWF0 I0 FRC0 CF2; lia].
    all: match goal with |- ?g => idtac "BODY-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End JSW.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section JMX.
  Variables (FB sp1 : Z) (h1 : HST asegs R HIA) (m1 : mem) (padX w0 w1 w2 s6v s7v : word).
  Local Notation LF' := ((FB, 128) :: LF).
  Local Notation XM := (FB + 96).
  Local Notation SPv := (sp1 + 8).
  Local Notation XO := [(XM, XM + 16); (MC, MC + 8)].
  Local Notation FRAME := [C8 (Z_to_bv 64 FB)].
  Local Notation dX0 := (mkMPD XM 1 0 0 [] padX LNull).
  Hypothesis GH2 : g_h g = 2.
  Hypothesis SP1 : bv_unsigned sp - 112 <= sp1 <= bv_unsigned sp - 96.
  Hypothesis SP1M : sp1 mod 32 = 0.
  Hypothesis HH1 : HM asegs R HIA h1 LB LF' m1.
  Hypothesis Ehcs : hcs asegs R HIA h1 = CS.
  Hypothesis Ehtop : htop asegs R HIA h1 = htop asegs R HIA h.
  Hypothesis Estk : hstkhi asegs R HIA h1 = hstkhi asegs R HIA h.
  Hypothesis Eflag : hflag asegs R HIA h1 = hflag asegs R HIA h.
  Hypothesis Evol : havol asegs R HIA h1 = havol asegs R HIA h.
  Hypothesis Efr : hfr asegs R HIA h1 = hfr asegs R HIA h.
  Hypothesis F64 : FB mod 64 = 0.
  Hypothesis FRSH : fresh_apart R LB LF FB 128.
  Hypothesis FHD : rw_cells asegs m1 FB [C8 w0; C8 w1; C8 w2].
  Hypothesis XMI : rw_cells asegs m1 XM (mpi_cells 0 (Z_to_bv 64 1) 0 padX).
  Hypothesis FSH : rw_cells asegs m1 (Z.shiftr FB 3 + al_sb AL) FSHMX.
  Hypothesis SAVE : rw_cells asegs m1 (bv_unsigned sp + -88) SAVEL.
  Hypothesis FRM : rw_cells asegs m1 sp1 FRAME.
  Hypothesis SThi : stk asegs m1 SPv (bv_unsigned sp + -88).
  Hypothesis STlo : stk asegs m1 lo sp1.
  Hypothesis MI1 : mem_inv asegs m1.
  Hypothesis PRES0 : presW asegs R HIA h LB LF (bv_unsigned sp) (arl_stklo R) [] m m1.
  Hypothesis SSH1 : sshad asegs AL m1 slo (bv_unsigned sp).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00S0?L15756354262.4 L19002855022.8 L19003035498.5 L19561366480.4 L19561366513.3 L19561531729.7 L19561547889.12L19561547889.4 L19561547889.9 L19561597301.6 L23372865473.7 L23372914373.8 L28516788675.4 L28516788706.3 L28516819778.6 L28516868706.11L28516868706.4 L28516868706.8 L28517016422.5 L29428324941.5 L37156630869.0 L38180633941.0 L43781740152.6 L43781953404.11L43781953404.4 L43781953404.8 L43782036701.3 L43782036732.2 L55616076308.8 L55616092944.6 L66151427842.16L9840374859.11 L9840374859.4  L9840374859.8  L9840620879.6  00000>00K00L00M00N00O00P00Q00R00S00T00`00a00b01801901:01;01<01N01O01P01Q01R01S01T01U01]02202302M03803903:03;S1R2lo3LOS3ALOS1R5NEEDR3NERFFFFFFFFFS2sp3sp13SP1FFS1R2lo3LOS3ALO3DLO3MC2FFFFS1R2lo3LOS3ALO3ACVSSFFFFFS2sp3SPRS1R2sp2lo3SLO3sp13SP1FS2FB2r03F641q1r1H2H02q02H4S1R5NEEDR2sp2lo3LOS3SLO3sp13SP13ALO3ACV3NERFFF". (* [comment removed for export] *)
  Lemma mx_base : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "(1:.(1;.=Vlo,)(1:.(1;.(3?.VR,)Vlo,)(1:.(1;.(36.(2;.VR,))(3?.VR,))(1:.(1;.Vlo,(23.(23.Vsp1,+350.)(7:.VR,)))(1:.(1;.=(7:.VR,))(1:.(1;.=Vsp1,)(1:.(1;.(20.Vsp1,+8.)(23.(2?.&40.Vsp,)+58.))(1:.(1<.(2?.&40.Vsp,)(4;.+2.+40.))(1:.(1;.(20.$30.+8.)Vlo,)(1:.(1<.=VFB,)(1:.(1;.(20.VFB,+80.)(36.(2;.VR,)))(1:.(=.$6.(4<.VFB,+8.)=)(1:.(21.(1;.(20.VFB,+80.)VG,)(1;.(20.VG,+<0.)VFB,))(21.(1;.(20.VFB,+80.)(7;.(2;.VR,)))(1;.(7<.(2;.VR,))VFB,)))))))))))))))")
(* [comment removed for export] *).
  Proof.
    rt_facts. pose proof (art_data_lo asegs R HIA) as DLO. flat constr:(MCOK) 3%nat. intros MC1 MC2 _.
    flat constr:(FRSH) 4%nat. intros F0 F1 F2 F3.
    pose proof (fresh_apart_client R LB LF lo G 192 FB 128 FRSH GCR ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS; lia)) as APG.
    repeat split; try assumption;
      first [ clear - LOS ALO ACV; lia | clear - SLO SP1 NER NEEDR; lia | clear - NER NEEDR; lia | clear - SLO SP1 NER NEEDR LOS ALO ACV; lia | clear - SP1; lia | clear - SPR; lia
            | clear - MC2 DLO ALO LOS; lia | clear - F64; Z.div_mod_to_equations; lia | clear - APG; lia | idtac ].
    all: match goal with |- ?g => idtac "BASE-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L27883368372.3L39332637397.0L45513781034.5L6737722458.7 00000900:00M00eS2FB1a2HaSS1R2lo3sp14LOSP3NE0S1R3HIA1h2sp3TOP3sp13SPV". (* [comment removed for export] *)
  Lemma mx_ec : ECA R HIA h1 LB LF' m1 SPv lo 8 FRAME XO MC.
  Proof.
    flat constr:(mx_base) 10%nat. flclear mx_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO _.
    constructor; try assumption; try reflexivity.
    - clear; lia.
    - clear - LOSP NE0; lia.
    - rewrite Ehtop. clear - SPV TOP. lia.
    - intros a Ha. cbn [outside fst snd] in Ha. clear - Ha. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Notation HP01 := (presW_presA asegs R HIA h LB LF _ _ _ m m1 PRES0).

  Lemma mx_lfsub : forall b, In b (LB ++ fdata LF) -> In b (LB ++ fdata LF').
  Proof. intros b Hb. apply fdata_cons_sub. exact Hb. Qed.

  Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L10512659994.5L11879002598.1L2275137097.0 L38961761872.3L55557728744.100000C00G00H00T00XS1R2FB4FDAT3MC13MC2S2FBSS2lo2FB4FBLOS2FB". (* [comment removed for export] *)
  Lemma mx_slot : eslot R HIA h1 LB LF' SPv lo XO MC XM.
  Proof.
    flat constr:(mx_base) 14%nat. flclear mx_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 F8 APG FDAT.
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & _ & _ & FBLO & SBND & APS). change (128 - 40) with 88 in IND.
    flat constr:(MCOK) 3%nat. intros MC1 MC2 _. unfold eslot.
    split; [eapply client_wrange_block; [exact IND| clear; lia| clear; lia]|].
    split; [left; clear - FBLO; lia|].
    split; [intros x Hx; cbn [outside fst snd] in *; split; [exact (proj1 Hx)| exact I]|].
    clear - FDAT MC1 MC2. lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00:0@L21650774036.144L2275137097.0   L30741553502.0  L59308586248.2  L66151427842.16 L9243719951.2   Q19546948462.144Q49740993511.144Q58744149156.144Q9644305041.144 00000J00K00L00R00k01201R01]01h026S2LF2ra2sp3LFB2FB3sp14SP10SSS1i2HiS2FB2r02F81q1r1H2H02q02H4S2FB2F0S2LF2ra2sp3LFB2FB3sp14SP102F02F8S2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FB2F0". (* [comment removed for export] *)
  Lemma mx_tmp : ejtmp R HIA LB LF' h1 LB m1 XM dX0.
  Proof.
    flat constr:(mx_base) 14%nat. flclear mx_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 F8 APG FDAT.
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS) as (CFB & _).
    pose proof (hcs_ok asegs R HIA h) as CSOK.
    unfold ejtmp. cbn [md_addr md_own mpd_blk].
    split.
    { unfold mpd_at, mpi_at. cbn [md_addr md_sg md_n md_p md_limbs md_pad md_own].
      split; [| left; reflexivity]. split; [exact XMI|]. split; [clear - F8; Z.div_mod_to_equations; lia|]. split; [clear - F0; lia|]. split; [reflexivity|].
      split; [unfold MPI_MAX_LIMBS; clear; lia| split; reflexivity]. }
    split; [reflexivity|]. split; [discriminate|]. split; [intros b []|].
    rewrite Ehcs. frame_aobj FSH XM 2%nat as OEX. exact OEX.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0>L11737279543.2L15756354262.4L1685717371.0 L21617968149.3L33997745137.3L33997906151.3L36453385976.3L37156630869.0L38948636245.0L39595656495.7L40267257272.3L44566137697.3L59237258151.6L59239732521.7L9216278189.2 00000700F00G00S00\00e00n00o01001H01Q01Z01n02G02MS1e3MCsS1R2lo4LOS'3ALOSS2sp3sp13SPVS2FB1e2KFS2FB1e2APS2FB1e2KSSSS1R1e3MC13MC23DI13DI22KIS2FB1e2KSS2FB1e2KFS1R2lo1e4LOS'3ALO2PCS1R2lo1e4LOS'3ALO3ACL3IHIS1e2N1". (* [comment removed for export] *)
  Lemma mx_ext : forall e, ck_op e -> ej_ext R HIA h1 LB LF' m1 SPv lo XO XM e.
  Proof.
    intros e OPe.
    flat constr:(mx_base) 14%nat. flclear mx_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 F8 APG FDAT. pose proof (hcs_ok asegs R HIA h) as CSOK.
    pose proof (alloc_ceiling_lo (L := arl_L R)) as ACL.
    destruct (ck_op_at e OPe h1 LF' m1 SPv HP01 MI1 HH1 Ehcs ltac:(clear - SPV; lia)) as (ME1 & OB1 & OL1 & PP1 & SS1 & SL1).
    flat constr:(OPe) 8%nat. flclear OPe. intros ME CR SEP MCs OB IM UWe BLK0.
    flat constr:(ME) 2%nat. intros FLt9 _. flat constr:(FLt9) 6%nat. flclear FLt9. intros _ _ E0 _ _ EOW.
    pose proof (fresh_apart_client R LB LF lo (md_addr e) 16 FB 128 FRSH CR ltac:(clear; lia) ltac:(clear; lia) ltac:(clear - ALO LOS'; lia)) as KS.
    assert (KL : md_own e = LHeap -> 1 <= md_n e /\ (FB + 128 <= md_p e \/ md_p e + 4 * md_n e <= FB) /\ md_p e + 4 * md_n e <= lo
                                     /\ (md_p e + 4 * md_n e <= hl_img_lo L \/ hl_img_hi L <= md_p e)).
    { intros EO. flat constr:((BLK0 EO)) 5%nat. intros N1 IN P0 PC PIMG. flat constr:(FRSH) 4%nat. intros _ _ _ F3.
      specialize (F3 _ _ ltac:(apply in_app_iff; left; exact IN)). split; [exact N1|]. split; [exact F3|]. split; [clear - PC ALO LOS'; lia| exact PIMG]. }
    assert (KST : md_own e = LStatic -> 1 <= md_n e /\ md_p e + 4 * md_n e <= lo /\ (XM + 16 <= md_p e \/ md_p e + 4 * md_n e <= XM)).
    { intros ES. rewrite ES in EOW. flat constr:(EOW) 5%nat. flclear EOW. intros N1 _ P0 PB PRO.
      flat constr:((AImgGlobals.img_norz_sound _ _ (IM ES))) 4%nat. intros _ _ IHI _. unfold AImgGlobals.IMG_HI in IHI.
      split; [exact N1|]. split; [clear - IHI ACL ALO LOS'; lia|].
      pose proof (P_ecp_mul_mod.rw_ro_apart asegs m1 _ _ (md_p e) (4 * md_n e) MI1 XMI ltac:(cbn; clear; lia) ltac:(clear - N1; lia) PRO) as AP.
      cbn [cells_size csize Nat.add mpi_cells Z.of_nat Pos.of_succ_nat Pos.succ] in AP. clear - AP. lia. }
    flat constr:(MCOK) 3%nat. intros MC1 MC2 _. flat constr:(DIMG) 2%nat. intros DI1 DI2.
    unfold ej_ext.
    split; [exact ME1|].
    split; [intros a Ha; destruct (CR a Ha) as [S|[D|(b & Hb & Hr)]]; [left; exact S| right; left; exact D| right; right; exists b; split; [exact (mx_lfsub b Hb)| exact Hr]]|].
    split; [exact SS1|].
    split; [intros NN; left; destruct (md_own e) eqn:EO; [exfalso; exact (NN eq_refl)| exact (proj1 (proj2 (proj2 (KL eq_refl))))| exact (proj1 (proj2 (KST eq_refl)))]|].
    split; [cbn [disjoint_from fst snd]; split; [clear - KS; lia|]; split; [clear - MCs; lia| exact I]|].
    split.
    { intros EO. flat constr:((KL EO)) 4%nat. intros N1 KF _ KI. cbn [disjoint_from fst snd]. split; [clear - KF; lia|]. split; [clear - KI MC1 MC2 DI1 DI2; lia| exact I]. }
    split; [clear - KS; lia|].
    split; [intros NN; destruct (md_own e) eqn:EO; [exfalso; exact (NN eq_refl)| (flat constr:((KL eq_refl)) 3%nat; intros _ KF _); clear - KF; lia| exact (proj2 (proj2 (KST eq_refl)))]|].
    split; [| exact IM].
    split; [rewrite Ehcs; exact OB1|].
    intros ES. rewrite Ehcs. apply OL1. rewrite ES in EOW. exact (proj1 EOW).
    all: match goal with |- ?g => idtac "EXT-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L13935699136.3 L26892418956.1 L41272413965.1 L62030908141.10L66151427842.16L696052597.9   00000<00@00D00h01B01`S2sp3sp13SPVS2spS2spS1R2sp2lo3sp14LOS'4LOSP3NE03SPV4SP64S2sp2r03SPA1q1r1H2H02q02H4S1R2sp2lo3sp13LO04LOSP3NE03SPV". (* [comment removed for export] *)
  Lemma mx_uw0 : uwc asegs m1 (arl_stklo R) (hstkhi asegs R HIA h1) (bv_unsigned sp) SPv (d + 1).
  Proof.
    flat constr:(mx_base) 10%nat. flclear mx_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO _.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    assert (UW1 : uwc asegs m1 (arl_stklo R) (hstkhi asegs R HIA h) (bv_unsigned s0) (bv_unsigned sp) d).
    { eapply (uwc_presA R); [exact HP01| exact UW| clear; lia| intros a Ha; exact I| clear - LOS' LOSP SPV NE0 LO0; lia| apply hstkhi_le64; clear - LOS' LOSP SPV NE0 SP64 LO0; lia]. }
    rewrite Estk.
    pose proof SAVE as SV. chunk_split SV 9%nat SVa SVb. chunk_split SVb 1%nat SV0 SVr. clear SVa SVr.
    replace (bv_unsigned sp + -88 + 72) with (bv_unsigned sp - 16) in SV0 by (clear; lia).
    eapply (uwc_frame_save R); [exact (proj1 SV0)| exact UW1| clear - SPV; lia| clear - SPA; Z.div_mod_to_equations; lia| exact D0].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L27883368372.10L52101693566.1300000T01BS1R3HIA2lo3sp12h14LOSP3NE04MCLO1a2HaS1R3HIA2lo2FB3sp12h14LOS'3ALO4LOSP3NE02F11a2Ha". (* [comment removed for export] *)
  Lemma mx_xouw : 28 <= d + 1 \/ forall a, SPv <= a < hstkhi asegs R HIA h1 -> outside XO a.
  Proof.
    flat constr:(mx_base) 12%nat. flclear mx_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 _.
    right. intros a Ha. cbn [outside fst snd]. split; [clear - Ha F1 ALO LOS' LOSP NE0; lia|]. split; [clear - Ha MCLO LOSP NE0; lia| exact I].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L34409126551.500000@S1R3MC13MC21x2Hx". (* [comment removed for export] *)
  Lemma mx_mc1 : rw_cells asegs m1 MC [C8 cnt].
  Proof.
    flat constr:(MCOK) 4%nat. intros MC1 MC2 MC3 _.
    eapply (presA_rw_cells asegs R); [exact HP01| exact MC0| | exact I].
    cbn [cells_size csize Nat.add]. intros x Hx. right. left. split; [clear - Hx MC1 MC2; lia| apply MC3; exact Hx].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Notation E1J := (E1I R HIA h1 LB LF' m1 SPv lo 8 FRAME XO MC (d + 1)).
  Local Notation EJJ := (EJ R HIA h1 LB LF' m1 SPv lo 8 FRAME XO MC).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L44158973781.1000005S3sp1". (* [comment removed for export] *)
  Lemma mx_spe : sp1 + 8 - 8 = sp1.
  Proof. clear. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L4781719053.2 L64060059785.400000600CS1d2D0S1R2FB3ALO2F1". (* [comment removed for export] *)
  Lemma mx_start : E1J 0 0 h1 LB m1 XM dX0.
  Proof.
    flat constr:(mx_base) 14%nat. flclear mx_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 F8 APG FDAT.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    unfold E1I. split.
    { eapply (ej_start R HIA h1 LB LF' m1 SPv lo 8 FRAME XO MC mx_ec m1 cnt (munch_refl _ _) (wmono_refl _ _) HH1 MI1); [rewrite mx_spe; exact STlo| rewrite mx_spe; exact FRM| exact mx_mc1]. }
    split; [exact mx_tmp|]. split; [exact mx_slot|].
    split; [left; split; [clear - F1 ALO; lia| clear - D0; lia]|].
    intros b Hb. left. exact Hb.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010=L4781719053.2000006S1d2D0". (* [comment removed for export] *)
  Lemma mx_k_d0 : 0 <= d + 1.
  Proof. pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0. clear - D0. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L51187461261.400000AS2sp3sp13SPV4SP64". (* [comment removed for export] *)
  Lemma mx_k_sp64 : SPv < 2^64.
  Proof. flat constr:(mx_base) 9%nat. flclear mx_base. intros _ _ _ _ _ _ SPV SP64 _. clear - SPV SP64. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L66151427842.1600000LS3sp12r04SP1M1q1r1H2H02q02H4". (* [comment removed for export] *)
  Lemma mx_k_spa : (SPv - 8) mod 16 = 0.
  Proof. rewrite mx_spe. clear - SP1M. Z.div_mod_to_equations. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma mx_k_slok : lo <= SPv - 8 - 848 - arl_need_ecp R.
  Proof. flat constr:(mx_base) 5%nat. flclear mx_base. intros _ _ _ LOSP _. rewrite mx_spe. exact LOSP. Qed.

  Ltac kit_side_mx :=
    first [ exact mx_ec | exact TPV | exact mx_k_d0 | exact mx_k_sp64 | exact mx_k_spa | exact mx_k_slok | exact mx_uw0 | exact mx_xouw | exact IMG | (clear; lia) ].
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00D0>L15244926161.9L18401844088.8L21617968149.3L2275137097.0 L24128180555.1L27188209011.3L28390317327.1L30826141493.8L34896805551.3L38459104170.4L45445121012.1L48132760585.9L57387068486.9L58748427563.1L60326494657.1L60878866887.5L66002855599.1L6899380056.1 L8402599844.3 L9631767084.2 00000K00c00o01001401=01A01`01l02702;02^03@03D03I03\03`03d03l043S1R2lo2FB3sp14LOSP3NE04FBLOS1R2lo3sp14LOSP3NE04MCLOS2sp3sp13SPVSS2FBS2FB1c2HcS2FBS1R2sp2lo3sp14LOSP3NE03SPV4MCLOS2sp3sp13SPVS2FB1A1k2H1S2FBS1R2sp2lo3sp14LOS'3ALO4LOSP3NE03SPVS1R2sp2lo2FB3sp14LOSP3NE03SPV4FBLOS2FBS3sp1S1R2FB4FDAT3MC13MC2S2FBS2FBS1A1k2H4S2FB2F0". (* [comment removed for export] *)
  Lemma mx_frame_k : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Pv,$6.Pf,$6.Phk,(3=.$9.VR,VHIA,)PLBk,(0.$4.)Pmk,P,(2.&40.)(3.(2.&8.))P,(81.VR,VHIA,Vh1,VLB,(69.(5.$6.$6.)(11.$6.$6.VFB,+80.)VLF,)Vm1,(20.Vsp1,+8.)Vlo,+8.(69.$18.(6<.(47.&40.VFB,))(41.$18.))(69.(5.$6.$6.)(11.$6.$6.(20.VFB,+60.)(20.(20.VFB,+60.)+10.))(69.(5.$6.$6.)(11.$6.$6.$30.(20.$30.+8.))(41.(5.$6.$6.))))$30.R5.R4.R3.R2.R1.)(1:.(19.$9.R2.VFB,(69.$18.(6<.Vw0,)(69.$18.(6<.Vw1,)(69.$18.(6<.Vw2,)(41.$18.)))))(1:.(19.$9.R2.(20.(6=.VFB,+3.)(6>.(32.VR,)))(69.$18.(6?.(47.&8.+?1.))(69.$18.(6?.(47.&8.+?1.))(69.$18.(6?.(47.&8.+?1.))(69.$18.(6?.(47.&8.+?1.))(69.$18.(6?.(47.&8.+?8.))(69.$18.(6?.(47.&8.+?8.))(69.$18.(6?.(47.&8.+?2.))(69.$18.(6?.(47.&8.+?2.))(69.$18.(6?.(47.&8.+?8.))(69.$18.(6?.(47.&8.+?8.))(69.$18.(6?.(47.&8.+?2.))(69.$18.(6?.(47.&8.+?2.))(69.$18.(6?.(47.&8.=))(69.$18.(6?.(47.&8.=))(69.$18.(6?.(47.&8.+?3.))(69.$18.(6?.(47.&8.+?3.))(41.$18.))))))))))))))))))(1:.(19.$9.R2.(20.(2?.&40.Vsp,)-58.)(69.$18.(6<.Vs9,)(69.$18.(6<.Vs8,)(69.$18.(6<.Vs7,)(69.$18.(6<.Vs6,)(69.$18.(6<.Vs5,)(69.$18.(6<.Vs4,)(69.$18.(6<.Vs3,)(69.$18.(6<.Vs2,)(69.$18.(6<.Vs1,)(69.$18.(6<.Vs0,)(69.$18.(6<.Vra,)(41.$18.)))))))))))))(1:.(57.$9.R2.(20.Vsp1,+8.)(20.(2?.&40.Vsp,)-58.))(1:.(61.$9.VR,VHIA,R4.VLB,VLF,(2?.&40.Vsp,)(3?.VR,)(69.(5.$6.$6.)(11.$6.$6.$30.(20.$30.+8.))(41.(5.$6.$6.)))Vm,R2.)(1:.Px,$6.P,(33.$9.VR,VHIA,Vh,R1.)(33.$9.VR,VHIA,R6.R2.)(=.$6.(40.$9.VR,VHIA,R4.)(40.$9.VR,VHIA,Vh,))))))))")
(* [comment removed for export] *).
  Proof.
    flat constr:(mx_base) 14%nat. flclear mx_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 F8 APG FDAT.
    intros v f hk LBk mk J. pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & INH & IND & AP & _ & _ & FBLO & SBND & APS).
    pose proof (hcs_ok asegs R HIA h) as CSOK. flat constr:(MCOK) 3%nat. intros MC1 MC2 _.
    assert (DJ : forall A k, (A + k <= XM \/ XM + 16 <= A) -> MC + 8 <= A \/ A + k <= MC -> disjoint_from XO A k).
    { intros A k H1 H4. cbn [disjoint_from fst snd]. split; [clear - H1; lia|]. split; [clear - H4; lia| exact I]. }
    split.
    { eapply (presA_rw_cells asegs R); [exact PXk| exact FHD| |].
      - cbn [cells_size csize Nat.add]. eapply client_range_block; [exact INH| clear; lia| clear; lia].
      - cbn [cells_size csize Nat.add]. apply DJ; [clear; lia| clear - FDAT MC1 MC2; lia]. }
    split.
    { rewrite <- Ehcs in CSOK.
      eapply (presA_shadow_cells_sh asegs R (hcs asegs R HIA h1) LB LF' SPv (arl_stklo R) (hstkhi asegs R HIA h1) XO m1 mk FB _ CSOK); [| exact F8| clear - F0; lia| exact PXk| exact FSH|].
      - cbn [cells_size csize Nat.add]. rewrite Ehcs. eapply crange_sub; [exact CFB| clear; lia| clear; lia].
      - cbn [cells_size csize Nat.add]. intros c Hc. right; right; left. exists (FB, 128). split; [left; reflexivity| cbn [fst snd]; clear - Hc; lia]. }
    split.
    { eapply (presA_rw_cells asegs R); [exact PXk| exact SAVE| |].
      - apply client_range_stack. clear - SPV. lia.
      - cbn [cells_size csize Nat.add]. apply DJ; [right; clear - FBLO LOSP NE0 SPV; lia| left; clear - MCLO LOSP NE0 SPV; lia]. }
    split.
    { eapply (presA_stk asegs R); [exact PXk| exact SThi| clear; lia|].
      apply DJ; [right; clear - FBLO LOSP NE0 SPV; lia| left; clear - MCLO LOSP NE0 SPV; lia]. }
    assert (HCS' : forall x, CS x -> hcs asegs R HIA hk x) by (intros x Hx; apply HCSk; rewrite Ehcs; exact Hx).
    assert (HS' : hstkhi asegs R HIA hk = hstkhi asegs R HIA h) by (rewrite HSk; exact Estk).
    split; [| split; [exact HCS'| exact HS']].
    eapply (presW_hmono R HIA h hk); [| exact HCS'| exact HS'].
    flat constr:(PRES0) 2%nat. intros P0 C123. split; [| exact C123].
    eapply presA_trans.
    - eapply presA_weaken; [exact P0| intros b Hb; exact Hb| intros b Hb; exact Hb| apply Z.le_refl| apply Z.le_refl| apply Z.le_refl| intros x _; exact I].
    - eapply (presA_drop_fresh_gen R LB LF (bv_unsigned sp) (arl_stklo R) (hstkhi asegs R HIA h) _ FB 128 XM (XM + 16)); [| exact FRSH| clear; lia| clear; lia| clear - ALO LOS' LOSP NE0 SPV; lia].
      rewrite <- Estk.
      eapply presA_weaken; [exact PXk| intros b Hb; exact Hb| intros b Hb; right; exact Hb| clear - SPV; lia| apply Z.le_refl| apply Z.le_refl|].
      intros x Hx. first [clear - Hx; cbn [outside fst snd] in *; tauto | cbn [outside fst snd] in *; tauto]. (* [comment removed for export] *)
    all: match goal with |- ?g => idtac "FRAMEK-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma mx_bp : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Pbp,$:.PA,$6.P,(78.$9.Vm,VLB,R1.R2.)P,(34.R3.)P,(21.(=.$6.R3.$79.)(=.$6.R3.(20.$79.+20.)))Pv,$6.Pf,$6.Phk,(3=.$9.VR,VHIA,)PLBk,(0.$4.)Pmk,P,(2.&40.)(3.(2.&8.))P,(81.VR,VHIA,Vh1,VLB,(69.(5.$6.$6.)(11.$6.$6.VFB,+80.)VLF,)Vm1,(20.Vsp1,+8.)Vlo,+8.(69.$18.(6<.(47.&40.VFB,))(41.$18.))(69.(5.$6.$6.)(11.$6.$6.(20.VFB,+60.)(20.(20.VFB,+60.)+10.))(69.(5.$6.$6.)(11.$6.$6.$30.(20.$30.+8.))(41.(5.$6.$6.))))$30.R5.R4.R3.R2.R1.)(1:.(84.VR,VHIA,(20.Vsp1,+8.)Vlo,+8.R4.R3.R2.R;.)(=.$6.(2>.R;.)R:.))")
(* [comment removed for export] *).
  Proof.
    intros bp A HB IM HA v f hk LBk mk J. pose proof J as [HHk SUBk PXk MIk HTk HSk HFk HCSk HVk HFRk MCk STk FRk].
    flat constr:((ck_bp_at bp A HB IM HA hk LBk LF' mk HHk MIk)) 7%nat. intros MB EO EA OS OL SS SL.
    split; [| exact EA]. unfold e1_rdable.
    split; [exact MB|]. split; [intros C; rewrite EO in C; discriminate C|]. split; [rewrite EA; exact OS|]. split; [exact OL|].
    split; [left; rewrite EA; exact SS| intros N1; left; exact (SL N1)].
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00m0@L10719636406.2  L1685717371.0   L19612994662.44 L22396302793.0  L2275137097.0   L24023900370.0  L25123160167.4  L27560104668.7  L35655538581.7  L35876627029.0  L39607668974.2  L42411609006.0  L47052517724.231L47052517724.232L47660518203.5  L54435792200.0  L60109250162.3  L62718247713.0  L64148832490.231L64148832490.232L64581097568.9  L65349652035.1  L8747829433.4   Q11799173861.237Q11799173861.238Q12452402922.228Q12452533583.232Q15010535807.232Q17841111252.234Q18376606873.233Q2447754665.233 Q24975809734.232Q26760028061.233Q32347280354.232Q33422860542.233Q34966617690.232Q39078748811.233Q40354196046.237Q40354196046.238Q40360481330.229Q40360481330.233Q44298944140.229Q44298944140.233Q44301027056.237Q44301027056.238Q47228431932.237Q47228431932.238Q48119910507.237Q48119910507.238Q5596578838.237 Q5596578838.238 Q57570454300.232Q58653435242.228Q59619599055.232Q63435846322.233Q64228675114.236Q64228675114.237Q64438491109.232Q67892150791.233Q6912043754.234 Q8433083564.232 00000600700800900:00;00J00_01801901:01;01<01=01>01?01J01K02G03C03[03\03]04?04a04l05705B05^06H06I06J06l06m06n07`07a08C08e09509E09U09e0:G0:i0;O0<50<n0=g0=h0=i0>S0>^0>_0>`0?j0A40A50A60AR0ASS1d2D0SFSSSS1R2FB4SBND3MC2S1R3HIA1h1N3BUD1v3HVBS1R3HIA1h2sp2lo3TOP5HTOPeSFSFFFSS1R2lo4LOS'SS1R2LF2ra2sp3LFB2FB3sp14SP102HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R2LF2ra2sp3LFB2FB3sp14SP102HB5Ha_st5Hl_st5SAEst5CM8st1x2HxS1R3HIA1h1N1d4BUDF1f3HFBFFS1R2LF3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3LFB2FB2HB5Ha_st5Hl_st5SAEstS2LF3LFB2FBS2LF3LFB2FBS2LF3LFB2FBS1R2LF3LFB2FB2HB5Ha_st5Hl_stS1R2LF2sp2lo3LFB3SLO2FB3NE02HB5Ha_st5Hl_stFFS1R2LF2sp2lo3LFB2FB2HB5Ha_st5Hl_stFFS1R2LF2sp2lo3LFB3SLO2FB3sp13SP13NE02HB5Ha_st5Hl_stFS1R2LF3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3LFB2FB2HBS1R2LF3LFB2FB2HBS1R2LF3LFB2FB2HBS1R2LF3LFB2FB2HBS1R2LF3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3LFB2FB2HB5Ha_st5Hl_st5SAEstS1R2LF3LFB2FB3ALO2HB5Ha_st5Hl_st5SAEstS1R2LF3LFB2FB3ALO2HB5Ha_st5Hl_st5SAEstS1R2LF2sp2lo3LFB3SLO2FB4LOS'3ALO3NE02HB5Ha_st5Hl_st5SAEstS1R2LF2sp2lo3LFB3SLO2FB4LOS'3ALO3NE02HB5Ha_st5Hl_st5SAEstFFS1R2LF2sp2lo3LFB2FB3sp13SP12HB5Ha_st5Hl_stS2LF3LFB2FBFFS1R2LF2ra2sp2lo3LFB3SLO3SPA2FB3sp13LO03NE04SP102F02F82HB5Ha_st5Hl_st5SAEstS1R2LF2ra2sp2lo3LFB3SLO3SPA2FB3sp13LO03NE04SP102F02F82HB5Ha_st5Hl_st5SAEstFFS1R2LF3LFB2FB2HB5Ha_st5Hl_stF". (* [comment removed for export] *)
  Lemma mx_fin : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Pv,$6.Pf,$6.Phk,(3=.$9.VR,VHIA,)PLBk,(0.$4.)Pmk,P,(2.&40.)(3.(2.&8.))PdXk,$:.Pr,$6.Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Ps4v,(2.&40.)P,(85.VR,VHIA,Vh1,VLB,(69.(5.$6.$6.)(11.$6.$6.VFB,+80.)VLF,)Vm1,(20.Vsp1,+8.)Vlo,+8.(69.$18.(6<.(47.&40.VFB,))(41.$18.))(69.(5.$6.$6.)(11.$6.$6.(20.VFB,+60.)(20.(20.VFB,+60.)+10.))(69.(5.$6.$6.)(11.$6.$6.$30.(20.$30.+8.))(41.(5.$6.$6.))))$30.(20.Vd,+1.)R18.R17.R16.R15.R14.(20.VFB,+60.)R13.)P,(1:.(1<.(74.(4;.+2.+1?.))R13.)(1;.R13.=))P,(1;.(20.R1:.$83.)(72.VN,))P,(1;.(20.R1:.(52.(20.Vd,+1.)))(73.VN,Vd,))(75.$9.(76.$9.VR,VHIA,R1:.Vmo0,)$77.(5:.(5;.R15.(47.&40.Vsp1,)Vgp,Vtp,R14.R13.R12.Vsp,(47.&40.Vsp1,)R11.R10.R?.R>.R=.R<.R;.R:.(47.&40.VFB,)(47.&40.R16.)R5.(47.&40.(20.VFB,+60.))Vs6v,Vs7v,(47.&40.(20.(6=.VFB,+3.)(6>.(32.VR,))))(47.&40.VFB,)Vs10,Vs11,R9.R8.R7.R6.)VF,(47.&40.+<;?2<.)Vfc,(5=.(2.&40.))R18.(5>.$9.)))")
(* [comment removed for export] *).
  Proof.
    intros until s4v. intros S HR HVB HFB.
    flat constr:(mx_base) 14%nat. flclear mx_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 F8 APG FDAT.
    pose proof (uwc_nonneg _ _ _ _ _ _ _ UW) as D0.
    assert (FRC0 : 0 <= fr_charge (d + 1)) by (unfold fr_charge; clear - D0; lia).
    pose proof (conj S I) as Sbox. clear S.
    pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV.
    pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    (* [comment removed for export] *)
    zstep. zstep.
    flat constr:(Sbox) 2%nat. flclear Sbox. intros S _. clear MU WM LAWS KINV.
    rewrite <- mx_spe.
    eapply e1_free with (h := h1) (LB := LB) (LF := LF') (m := m1) (SP := SPv) (lo := lo) (FR := 8) (FRAME := FRAME) (XO := XO) (MC := MC)
                        (dd := d + 1) (STKMAX := 848) (A1 := XM) (d1 := dXk) (v := v) (f := f) (RET := 0xcbf34);
      first [ kit_side_mx | exact HFREE | exact S | reflexivity
            | (rewrite Evol; unfold AVOL_CALL in *; clear - BUD HVB; lia) | (rewrite Efr; clear - BUDF HFB FRC0; lia) | idtac ].
    all: match goal with |- forall _, _ => idtac | |- ?g => idtac "MXFIN-FREE-LEFT:" g end.
    intros h' LB' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' S'. rewrite mx_spe.
    flat constr:(S') 5%nat. intros J' _ _ _ COV.
    flat constr:((mx_frame_k _ _ h' LB' m' J')) 7%nat. intros FHD' FSH' SAVE' SThi' PRESa HCS' HS'.
    pose proof J' as [HH' SUB' PX' MI' HT' HSk' HF' HCSk' HV' HFR' [ck MC'] ST' FR'].
    rewrite mx_spe in ST', FR'.
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFB & INF & _ & _ & AP & _ & _ & FBLO & SBND & APS). change (128 / 8) with 16 in SBND, APS.
    pose proof (hcs_ok asegs R HIA h') as CSOK'.
    assert (CFB' : crange (hcs asegs R HIA h') FB 128) by (eapply crange_mono; [exact HCS'| exact CFB]).
    pose proof (hcs_stack asegs R HIA h') as SCS0'. rewrite HS' in SCS0'.
    pose proof (hm_top asegs R HIA h _ _ _ HH) as HTOPe.
    assert (SCS' : crange (hcs asegs R HIA h') lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0'| clear - LOS'; lia| clear - TOP HTOPe; lia]).
    assert (DMS : disjoint_from [(Z.shiftr FB 3 + al_sb AL, Z.shiftr FB 3 + al_sb AL + 16)] MC 8).
    { flat constr:(MCOK) 3%nat. intros _ MC2 _. cbn [disjoint_from fst snd]. split; [left; clear - MC2 SBND; lia| exact I]. }
    pose proof (munch_refl [(Z.shiftr FB 3 + al_sb AL, Z.shiftr FB 3 + al_sb AL + 16)] m') as MUs. pose proof (wmono_refl asegs m') as WMs.
    pose proof (conj MC' I) as MCb. clear MC'. clear S' J'.
    pose proof (AIh_laws asegs R HIA h') as LAWS. pose proof (KF_kinv asegs R HIA h' mo0) as KINV.
    (* [comment removed for export] *)
    do 5 zstep.
    match goal with H : rw_cells _ _ (Z.shiftr FB 3 + al_sb AL) _ |- _ => norm_b8 H; rename H into FSH9 end.
    lazymatch goal with |- _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    flat constr:(MCb) 2%nat. flclear MCb. intros MC' _.
    pose proof (rw_cells_transport asegs _ _ _ _ _ MC' MUs WMs DMS) as MC9.
    eapply ck_exit with (FBx := FB) (sp1x := sp1) (hk := h') (LBk := LB') (v := v + AVOL_CALL) (f := f + fr_charge (d + 1));
      first [ exact SP1 | exact SP1M | exact F64 | exact FRSH | exact CFB | exact HCS' | exact HS' | exact HR
            | exact SUB' | (exists ck; exact MC9) | eassumption
            | (rewrite HT'; exact Ehtop) | (rewrite HF'; exact Eflag) | (rewrite <- Evol; exact HV') | (rewrite <- Efr; exact HFR')
            | exact HVB | exact HFB
            | (intros b Hb; destruct (COV b Hb) as [K|K]; [exact K| cbn in K; destruct K])
            | idtac ].
    all: match goal with |- ?g => idtac "MXFIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Notation KIT1 := (E1I R HIA h1 LB LF' m1 SPv lo 8 FRAME XO MC (d + 1)).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00\0@L11967210160.6  L1409191888.1   L1509615061.222 L18457785511.0  L19612793378.46 L19612994790.44 L19612994790.45 L20201646333.1  L21959505626.0  L23268210308.0  L2397676628.0   L25442915336.0  L25628089406.5  L27172298953.0  L28823705696.7  L29956516996.0  L32854200822.10 L33473450441.0  L35876627029.0  L37546314368.4  L38492666657.0  L39827504200.0  L41549879758.10 L44368066569.8  L46469563331.3  L47303667269.4  L47660518203.5  L47660518203.7  L51578261130.2  L52061118241.222L52520404101.222L53512949285.222L56086640162.8  L56233996468.2  L56247323031.1  L58415340642.2  L61279635374.1  L61281732014.3  L61386852240.2  L62263889493.2  L64587471328.10 L65349652035.1  L8201234081.0   L8475647278.2   00000A00B00C00D00E00F00G00H00I00J00K00L00M00N00O00P00Q00R00S00b00c00d01A01B01C01N01O01P01Y01Z02:02Z02[02\02]02^02_02`02a02i03F03G03H03IS1N1v3dXk3HVB3IPNFFSFFFFFSSSFSFSFSSS1N3dXk3HSZ3NRkSSS1R3HIA1h1N3BUD1v3dXk3HVB3IPNFFS1N1d1f3HFBFFS2LB4C24HFS2LF2ra2sp1g3LFB2FB3sp14SP103dX2S2LF2ra2sp1g3LFB2FB3sp14SP103dX2FFFFFFFS2LF3LFBS1R3HIA1h1N1d4BUDF1f3HFB4FRC0FSF". (* [comment removed for export] *)
  Lemma mx_addint : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Pv,$6.Pf,$6.Phk,(3=.$9.VR,VHIA,)PLBk,(0.$4.)Pmk,P,(2.&40.)(3.(2.&8.))PdXk,$:.Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)Ps3v,(2.&40.)P,(85.VR,VHIA,Vh1,VLB,(69.(5.$6.$6.)(11.$6.$6.VFB,+80.)VLF,)Vm1,(20.Vsp1,+8.)Vlo,+8.(69.$18.(6<.(47.&40.VFB,))(41.$18.))(69.(5.$6.$6.)(11.$6.$6.(20.VFB,+60.)(20.(20.VFB,+60.)+10.))(69.(5.$6.$6.)(11.$6.$6.$30.(20.$30.+8.))(41.(5.$6.$6.))))$30.(20.Vd,+1.)R17.R16.R15.R14.R13.(20.VFB,+60.)R12.)P,(1;.(14.R13.)VN,)P,(1;.(20.(20.R19.(55.VN,))$83.)(72.VN,))P,(1;.(20.(20.R19.(56.(20.Vd,+1.)))(52.(20.Vd,+1.)))(73.VN,Vd,))(75.$9.(76.$9.VR,VHIA,R19.Vmo0,)$77.(5:.(5;.R15.(47.&40.Vsp1,)Vgp,Vtp,R14.R13.R12.Vsp,(47.&40.Vsp1,)R11.R10.R?.R>.R=.R<.R;.R:.(47.&40.VFB,)R5.(47.&40.(20.VG,+8.))(47.&40.(20.VFB,+60.))Vs6v,Vs7v,(47.&40.(20.(6=.VFB,+3.)(6>.(32.VR,))))(47.&40.VFB,)Vs10,Vs11,R9.R8.R7.R6.)VF,(47.&40.+<;?14.)Vfc,(5=.(2.&40.))R17.(5>.$9.)))")
(* [comment removed for export] *).
  Proof.
    intros until s3v. intros S HSZ HVB HFB.
    flat constr:(mx_base) 14%nat. flclear mx_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 F8 APG FDAT.
    flat constr:(ck_budget) 12%nat. flclear ck_budget. intros N0 (NP0 & NPN) D0 _ _ _ FRC0 _ GIB IF0 _ _.
    flat constr:(ck_op_P) 2%nat. flclear ck_op_P. intros OPP EAP.
    flat constr:(S) 5%nat. intros _ (MXk & EAk & _) _ U1 _. flat constr:(MXk) 2%nat. intros FLt10 _. flat constr:(FLt10) 6%nat. flclear FLt10. intros _ _ _ _ NRk _.
    destruct (GIB (md_n dXk) ltac:(clear - NRk HSZ; lia)) as [_ [IP0 IPN]].
    pose proof (conj S I) as Sbox; clear S. pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV. pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    (* [comment removed for export] *)
    do 4 zstep.
    flat constr:(Sbox) 2%nat. flclear Sbox. intros S _. clear MU WM LAWS KINV. rewrite <- mx_spe.
    eapply e1_intop with (h := h1) (LB := LB) (LF := LF') (m := m1) (SP := SPv) (lo := lo) (FR := 8) (FRAME := FRAME) (XO := XO) (MC := MC)
                         (dd := d + 1) (STKMAX := 848) (ENTRY := A_MPI_ADD_INT) (A1 := XM) (d1 := dXk) (eA := dXk) (b := 1) (v := v) (f := f) (RET := 0xcbf24);
      first [ kit_side_mx | exact HADDI | exact S | reflexivity | exact IF0
            | exact (or_introl eq_refl)
            | (rewrite EAk; exact U1) | (rewrite EAk; reflexivity)
            | (cbv beta; exact IP0)
            | (cbn [length]; clear - LFB; lia)
            | (cbv beta; rewrite Evol; unfold AVOL_CALL in *; clear - BUD HVB IP0 IPN; lia)
            | (rewrite Efr; clear - BUDF HFB IF0 FRC0; lia)
            | (unfold C24_INTOP; unfold C24_ECP_CHECK_PUBKEY in C24H; clear - C24H; lia)
            | idtac ].
    all: match goal with |- forall _, _ => idtac | |- ?g => idtac "ADDINT-CALL-LEFT:" g end.
    cbv beta. intros h2 LB2 m2 dX2 r2 t0_2 t1_2 t2_2 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 t3_2 t4_2 t5_2 t6_2 S2 [[RV2 BK2] SZ2]. rewrite mx_spe.
    pose proof (conj S2 I) as Sbox; clear S2. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo0) as KINV. pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    destruct RV2 as [(-> & _) | ->].
    2:{ (* [comment removed for export] *)
      unfold MBEDTLS_ERR_MPI_ALLOC_FAILED. do 2 zstep. flat constr:(Sbox) 2%nat. flclear Sbox. intros S2 _. clear MU WM LAWS KINV.
      eapply (mx_fin _ _ h2 LB2 m2 dX2 (-16)); [exact S2| clear; lia| unfold AVOL_CALL in *; clear - HVB IP0 IPN; lia| clear - HFB; lia]. }
    (* [comment removed for export] *)
    do 4 zstep.
    flat constr:(Sbox) 2%nat. flclear Sbox. intros S2 _. clear MU WM LAWS KINV. rewrite <- mx_spe.
    pose proof (e1_rd R HIA IMG h1 LB LF' m1 SPv lo 8 FRAME XO MC mx_ec (d + 1) 848 mx_k_sp64 mx_k_spa mx_k_slok ltac:(clear; lia) _ _ h2 LB2 m2 XM dX2 dX2 S2 (or_introl eq_refl)) as RDX.
    pose proof (e1_rd R HIA IMG h1 LB LF' m1 SPv lo 8 FRAME XO MC mx_ec (d + 1) 848 mx_k_sp64 mx_k_spa mx_k_slok ltac:(clear; lia) _ _ h2 LB2 m2 XM dX2 dP S2 (or_intror (mx_ext dP OPP))) as RDP.
    flat constr:(S2) 3%nat. intros _ (_ & EA2 & _) _.
    eapply e1_cmp with (h := h1) (LB := LB) (LF := LF') (m := m1) (SP := SPv) (lo := lo) (FR := 8) (FRAME := FRAME) (XO := XO) (MC := MC)
                       (dd := d + 1) (STKMAX := 848) (ENTRY := A_MPI_CMP_MPI_E) (A1 := XM) (d1 := dX2) (eX := dX2) (eY := dP) (RET := 0xcbfc0);
      first [ kit_side_mx | exact (A_mpi_cmp_mpi_spec AL IMG) | exact S2 | exact RDX | exact RDP | reflexivity
            | (rewrite EA2; reflexivity) | (rewrite EAP; reflexivity) | idtac ].
    all: match goal with |- forall _, _ => idtac | |- ?g => idtac "ADDINT-CMP-LEFT:" g end.
    intros m3 t0_3 t1_3 t2_3 a1_3 a2_3 a3_3 a4_3 a5_3 a6_3 a7_3 t3_3 t4_3 t5_3 t6_3 S3. rewrite mx_spe.
    pose proof (conj S3 I) as Sbox; clear S3. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo0) as KINV. pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    (* [comment removed for export] *)
    destruct (sgn3 (mpd_val dX2) (mpd_val dP)) as [E|[E|E]]; rewrite E.
    all: do 6 zstep.
    all: (flat constr:(Sbox) 2%nat; flclear Sbox; intros S3 _). clear MU WM LAWS KINV.
    1: ck_s3_lit 0. 2: ck_s3_lit (-19584). 3: ck_s3_lit 0.
    all: eapply (mx_fin _ _ h2 LB2 m3 dX2); [exact S3| clear; lia| unfold AVOL_CALL in *; clear - HVB IP0 IPN; lia| clear - HFB; lia].
    all: match goal with |- ?g => idtac "ADDINT-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Ltac mx_rd RDn hk LBk mk dk e SE Sx :=
    pose proof (e1_rd R HIA IMG h1 LB LF' m1 SPv lo 8 FRAME XO MC mx_ec (d + 1) 848 mx_k_sp64 mx_k_spa mx_k_slok ltac:(clear; lia) _ _ hk LBk mk XM dk e Sx SE) as RDn.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00I0?L10643229832.0 L1175044806.5  L15772483268.8 L18457785511.0 L19612793469.44L19612793469.45L20201646333.1 L21886542088.0 L21959505626.0 L23120258322.8 L23268210308.0 L27172298953.0 L29725558155.1 L35876627029.0 L36122690258.8 L36271130952.0 L4671374506.8  L49939585185.0 L5000864057.2  L50646084385.0 L55649616831.4 L5856141729.0  L61386852240.2 L66486717505.8 L8720406107.1  00000100@00A00B00C00D00E00F00G00H00I00J00K00L00M00N00O00P00V00W00d00e00f00g00hSS1N1d1f3HFB3IF0FSFFFSFFSSFSFSFSS1N2N0SS1N1v3HVB3IN0SFFF". (* [comment removed for export] *)
  Lemma mx_tail : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Pv,$6.Pf,$6.Phk,(3=.$9.VR,VHIA,)PLBk,(0.$4.)Pmk,P,(2.&40.)(3.(2.&8.))PdXk,$:.Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(85.VR,VHIA,Vh1,VLB,(69.(5.$6.$6.)(11.$6.$6.VFB,+80.)VLF,)Vm1,(20.Vsp1,+8.)Vlo,+8.(69.$18.(6<.(47.&40.VFB,))(41.$18.))(69.(5.$6.$6.)(11.$6.$6.(20.VFB,+60.)(20.(20.VFB,+60.)+10.))(69.(5.$6.$6.)(11.$6.$6.$30.(20.$30.+8.))(41.(5.$6.$6.))))$30.(20.Vd,+1.)R16.R15.R14.R13.R12.(20.VFB,+60.)R11.)P,(1;.(14.R12.)VN,)P,(1;.(20.(20.R18.(55.VN,))$83.)(72.VN,))P,(1;.(20.(20.R18.(56.(20.Vd,+1.)))(52.(20.Vd,+1.)))(73.VN,Vd,))(75.$9.(76.$9.VR,VHIA,R18.Vmo0,)$77.(5:.(5;.R14.(47.&40.Vsp1,)Vgp,Vtp,R13.R12.R11.Vsp,(47.&40.Vsp1,)R10.R?.R>.R=.R<.R;.R:.R9.(47.&40.VFB,)(47.&40.VQ,)(47.&40.(20.VG,+8.))(47.&40.(20.VFB,+60.))Vs6v,Vs7v,(47.&40.(20.(6=.VFB,+3.)(6>.(32.VR,))))(47.&40.VFB,)Vs10,Vs11,R8.R7.R6.R5.)VF,(47.&40.+<;><<.)Vfc,(5=.(2.&40.))R16.(5>.$9.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros S HSZ HVB HFB.
    flat constr:(ck_budget) 12%nat. flclear ck_budget. intros N0 (NP0 & NPN) D0 _ _ _ FRC0 _ GIB IF0 _ _.
    destruct (GIB N ltac:(clear - N0; lia)) as [_ [IN0 _]].
    assert (HVF : v + AVOL_CALL <= check_pubkey_PHIn N) by (clear - HVB IN0; lia).
    assert (HFF : f + fr_charge (d + 1) <= check_pubkey_FRn N d) by (clear - HFB IF0; lia).
    flat constr:(S) 3%nat. intros _ (_ & EAk & _) _.
    mx_rd RDX hk LBk mk dXk dXk (@or_introl (dXk = dXk) (ej_ext R HIA h1 LB LF' m1 SPv lo XO XM dXk) eq_refl) S.
    pose proof (conj S I) as Sbox; clear S. pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV. pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    (* [comment removed for export] *)
    do 3 zstep.
    flat constr:(Sbox) 2%nat. flclear Sbox. intros S _. clear MU WM LAWS KINV. rewrite <- mx_spe.
    eapply e1_cmpint with (h := h1) (LB := LB) (LF := LF') (m := m1) (SP := SPv) (lo := lo) (FR := 8) (FRAME := FRAME) (XO := XO) (MC := MC)
                          (dd := d + 1) (STKMAX := 848) (ENTRY := A_MPI_CMP_INT_E) (A1 := XM) (d1 := dXk) (eX := dXk) (z := 1) (RET := 0xcbed8);
      first [ kit_side_mx | exact (A_mpi_cmp_int_spec AL IMG) | exact S | exact RDX | reflexivity | (rewrite EAk; reflexivity) | idtac ].
    all: match goal with |- forall _, _ => idtac | |- ?g => idtac "TAIL-CMPINT-LEFT:" g end.
    intros m2 t0_2 t1_2 t2_2 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 t3_2 t4_2 t5_2 t6_2 S2. rewrite mx_spe. clear RDX.
    flat constr:(S2) 2%nat. intros J2 _.
    flat constr:((mx_bp bp1 BP BP1 BI1 (or_introl eq_refl) _ _ hk LBk m2 J2)) 2%nat. intros RB1 EB1.
    mx_rd RDX2 hk LBk m2 dXk dXk (@or_introl (dXk = dXk) (ej_ext R HIA h1 LB LF' m1 SPv lo XO XM dXk) eq_refl) S2.
    pose proof (conj S2 I) as Sbox; clear S2. pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV. pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    destruct (sgn3 (mpd_val dXk) 1) as [E|[E|E]]; rewrite E.
    1, 2: do 4 zstep; (flat constr:(Sbox) 2%nat; flclear Sbox; intros S2 _); clear MU WM LAWS KINV; ck_s3_lit (-19584);
          (eapply (mx_fin _ _ hk LBk m2 dXk); [exact S2| clear; lia| exact HVF| exact HFF]).
    (* [comment removed for export] *)
    do 2 zstep. zstep. if_cases KID.
    { flat constr:(Sbox) 2%nat. flclear Sbox. intros S2 _. clear MU WM LAWS KINV. eapply (mx_addint _ _ hk LBk m2 dXk); [exact S2| exact HSZ| exact HVB| exact HFB]. }
    (* [comment removed for export] *)
    do 4 zstep.
    flat constr:(Sbox) 2%nat. flclear Sbox. intros S2 _. clear MU WM LAWS KINV. rewrite <- mx_spe.
    eapply e1_cmp with (h := h1) (LB := LB) (LF := LF') (m := m1) (SP := SPv) (lo := lo) (FR := 8) (FRAME := FRAME) (XO := XO) (MC := MC)
                       (dd := d + 1) (STKMAX := 848) (ENTRY := A_MPI_CMP_MPI_E) (A1 := XM) (d1 := dXk) (eX := dXk) (eY := bp1) (RET := 0xcbef4);
      first [ kit_side_mx | exact (A_mpi_cmp_mpi_spec AL IMG) | exact S2 | exact RDX2 | exact RB1 | reflexivity
            | (rewrite EAk; reflexivity) | (rewrite EB1; reflexivity) | idtac ].
    all: match goal with |- forall _, _ => idtac | |- ?g => idtac "TAIL-CMPB1-LEFT:" g end.
    intros m3 t0_3 t1_3 t2_3 a1_3 a2_3 a3_3 a4_3 a5_3 a6_3 a7_3 t3_3 t4_3 t5_3 t6_3 S3. rewrite mx_spe. clear RDX2 RB1.
    flat constr:(S3) 2%nat. intros J3 _.
    flat constr:((mx_bp bp2 (BP + 32) BP2 BI2 (or_intror eq_refl) _ _ hk LBk m3 J3)) 2%nat. intros RB2 EB2.
    mx_rd RDX3 hk LBk m3 dXk dXk (@or_introl (dXk = dXk) (ej_ext R HIA h1 LB LF' m1 SPv lo XO XM dXk) eq_refl) S3.
    pose proof (conj S3 I) as Sbox; clear S3. pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV. pose proof (munch_refl ([] : list ivl) m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    (* [comment removed for export] *)
    destruct (sgn3 (mpd_val dXk) (mpd_val bp1)) as [E1|[E1|E1]]; rewrite E1.
    2:{ do 3 zstep. flat constr:(Sbox) 2%nat. flclear Sbox. intros S3 _. clear MU WM LAWS KINV. ck_s3_lit (-19584).
        eapply (mx_fin _ _ hk LBk m3 dXk); [exact S3| clear; lia| exact HVF| exact HFF]. }
    (* [comment removed for export] *)
    all: do 3 zstep; do 4 zstep.
    all: (flat constr:(Sbox) 2%nat; flclear Sbox; intros S3 _); clear MU WM LAWS KINV; rewrite <- mx_spe.
    all: eapply e1_cmp with (h := h1) (LB := LB) (LF := LF') (m := m1) (SP := SPv) (lo := lo) (FR := 8) (FRAME := FRAME) (XO := XO) (MC := MC)
                       (dd := d + 1) (STKMAX := 848) (ENTRY := A_MPI_CMP_MPI_E) (A1 := XM) (d1 := dXk) (eX := dXk) (eY := bp2) (RET := 0xcbf10);
      first [ kit_side_mx | exact (A_mpi_cmp_mpi_spec AL IMG) | exact S3 | exact RDX3 | exact RB2 | reflexivity
            | (rewrite EAk; reflexivity) | (rewrite EB2; reflexivity) | idtac ].
    all: match goal with |- forall _, _ => idtac | |- ?g => idtac "TAIL-CMPB2-LEFT:" g end.
    all: intros m4 t0_4 t1_4 t2_4 a1_4 a2_4 a3_4 a4_4 a5_4 a6_4 a7_4 t3_4 t4_4 t5_4 t6_4 S4; rewrite mx_spe.
    all: pose proof (conj S4 I) as Sbox; clear S4; pose proof (AIh_laws asegs R HIA hk) as LAWS; pose proof (KF_kinv asegs R HIA hk mo0) as KINV; pose proof (munch_refl ([] : list ivl) m4) as MU; pose proof (wmono_refl asegs m4) as WM.
    (* [comment removed for export] *)
    all: destruct (sgn3 (mpd_val dXk) (mpd_val bp2)) as [E2|[E2|E2]]; rewrite E2.
    all: zstep; (flat constr:(Sbox) 2%nat; flclear Sbox; intros S4 _); clear MU WM LAWS KINV.
    2, 5: ck_s3_lit (-19584); (eapply (mx_fin _ _ hk LBk m4 dXk); [exact S4| clear; lia| exact HVF| exact HFF]).
    all: eapply (mx_addint _ _ hk LBk m4 dXk); [exact S4| exact HSZ| exact HVB| exact HFB].
    all: match goal with |- ?g => idtac "TAIL-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00V0?L11363440624.4 L1175044806.5  L15580355017.0 L17352774880.11L19612793469.43L19612793469.44L20201646333.1 L21800167073.0 L22135776033.0 L23120258322.8 L26404040710.5 L26602079951.9 L27172298953.0 L28616493576.0 L2967792479.7  L29956516996.0 L32854200822.10L35876627029.0 L3617752057.1  L41032781264.4 L42848431250.4 L46469563331.3 L46821704760.6 L47905764921.2 L5000864057.2  L51213051206.3 L53861599688.0 L55649616831.4 L59315053158.6 L59321114998.2 L60935591404.8 L61386852240.2 L64264716105.2 L6515011069.3  L6515043962.3  L65349652035.1 L66634545723.3 L8475647278.2  00000100@00A00B00C00D00E00F00G00H00[01801901:01O01P01Q01R01U01V01c01d02802902?02@02A02N02c02m02n02o03003:03D03E03O03PFS1N1d1f3HFB3IF0SFFFFSSFS1N3dXk3HSZ3dX33SZ3S1R3HIA1h1N1d4BUDF1f4FRC03HFFSSS1R3HIA1h1N3BUD1v3HVFSFSS1dFS1g2VP3dXk2GEFS1g2VP1n3dXk4MEAS2GEFS1N2N0FSS1N1v3HVB3IN0S1g3dXk2GE3VPA4XABS1CS3dXk4MEASFFFS1g3dXk2EQS1g3dXk2GTFS1G2FB3APGF". (* [comment removed for export] *)
  Lemma mx_loop : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Pn,$86.Pv,$6.Pf,$6.Phk,(3=.$9.VR,VHIA,)PLBk,(0.$4.)Pmk,P,(2.&40.)(3.(2.&8.))PdXk,$:.Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(85.VR,VHIA,Vh1,VLB,(69.(5.$6.$6.)(11.$6.$6.VFB,+80.)VLF,)Vm1,(20.Vsp1,+8.)Vlo,+8.(69.$18.(6<.(47.&40.VFB,))(41.$18.))(69.(5.$6.$6.)(11.$6.$6.(20.VFB,+60.)(20.(20.VFB,+60.)+10.))(69.(5.$6.$6.)(11.$6.$6.$30.(20.$30.+8.))(41.(5.$6.$6.))))$30.(20.Vd,+1.)R16.R15.R14.R13.R12.(20.VFB,+60.)R11.)P,(1;.(14.R12.)VN,)P,(87.(88.(89.R13.))R19.)P,(1;.(20.(20.R19.(55.VN,))$83.)(72.VN,))P,(1;.(20.(20.R19.(56.(20.Vd,+1.)))(52.(20.Vd,+1.)))(73.VN,Vd,))(75.$9.(76.$9.VR,VHIA,R19.Vmo0,)$77.(5:.(5;.R15.(47.&40.Vsp1,)Vgp,Vtp,R14.R13.R12.Vsp,(47.&40.Vsp1,)R11.R10.R?.R>.R=.R<.R;.R:.(47.&40.VFB,)(47.&40.VQ,)(47.&40.(20.VG,+8.))(47.&40.(20.VFB,+60.))Vs6v,Vs7v,(47.&40.(20.(6=.VFB,+3.)(6>.(32.VR,))))(47.&40.VFB,)Vs10,Vs11,R9.R8.R7.R6.)VF,(47.&40.+<;>80.)Vfc,(5=.(2.&40.))R17.(5>.$9.)))")
(* [comment removed for export] *).
  Proof.
    induction n as [|n IH]; intros until t6; intros S HSZ MEAS HVB HFB; [exfalso; clear - MEAS; lia|].
    flat constr:(mx_base) 14%nat. flclear mx_base. intros LO0 LOS' ALO LOSP NE0 SP10 SPV SP64 MCLO F0 F1 F8 APG FDAT.
    flat constr:(ck_budget) 12%nat. flclear ck_budget. intros N0 (NP0 & NPN) D0 _ _ _ FRC0 _ GIB IF0 _ _.
    destruct (GIB N ltac:(clear - N0; lia)) as [_ [IN0 _]].
    assert (HVF : v + AVOL_CALL <= check_pubkey_PHIn N) by (clear - HVB IN0; lia).
    assert (HFF : f + fr_charge (d + 1) <= check_pubkey_FRn N d) by (clear - HFB IF0; lia).
    flat constr:(ck_op_P) 2%nat. flclear ck_op_P. intros OPP EAP. flat constr:(OPP) 8%nat. intros _ _ _ _ _ _ PUW _.
    flat constr:(S) 5%nat. intros _ (MXk & EAk & _) _ U1 _.
    mx_rd RDX hk LBk mk dXk dXk (@or_introl (dXk = dXk) (ej_ext R HIA h1 LB LF' m1 SPv lo XO XM dXk) eq_refl) S.
    mx_rd RDP hk LBk mk dXk (g_P g) (@or_intror (g_P g = dXk) (ej_ext R HIA h1 LB LF' m1 SPv lo XO XM (g_P g)) (mx_ext (g_P g) OPP)) S.
    pose proof (conj S I) as Sbox; clear S. pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV. pose proof (munch_refl ([] : list ivl) mk) as MU. pose proof (wmono_refl asegs mk) as WM.
    (* [comment removed for export] *)
    do 3 zstep.
    flat constr:(Sbox) 2%nat. flclear Sbox. intros S _. clear MU WM LAWS KINV. rewrite <- mx_spe.
    eapply e1_cmp with (h := h1) (LB := LB) (LF := LF') (m := m1) (SP := SPv) (lo := lo) (FR := 8) (FRAME := FRAME) (XO := XO) (MC := MC)
                       (dd := d + 1) (STKMAX := 848) (ENTRY := A_MPI_CMP_MPI_E) (A1 := XM) (d1 := dXk) (eX := dXk) (eY := dP) (RET := 0xcbe8c);
      first [ kit_side_mx | exact (A_mpi_cmp_mpi_spec AL IMG) | exact S | exact RDX | exact RDP | reflexivity
            | (rewrite EAk; reflexivity) | (rewrite EAP; reflexivity) | idtac ].
    all: match goal with |- forall _, _ => idtac | |- ?g => idtac "LOOP-CMP-LEFT:" g end.
    intros m2 t0_2 t1_2 t2_2 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 t3_2 t4_2 t5_2 t6_2 S2. rewrite mx_spe. clear RDX RDP.
    pose proof (conj S2 I) as Sbox; clear S2. pose proof (AIh_laws asegs R HIA hk) as LAWS. pose proof (KF_kinv asegs R HIA hk mo0) as KINV. pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    destruct (sgn_ord (mpd_val dXk) (mpd_val dP)) as [[SG LT]|[[SG EQ]|[SG GT]]]; rewrite SG.
    1:{ zstep. flat constr:(Sbox) 2%nat. flclear Sbox. intros S2 _. clear MU WM LAWS KINV. eapply (mx_tail _ _ hk LBk m2 dXk); [exact S2| exact HSZ| exact HVB| exact HFB]. }
    (* [comment removed for export] *)
    all: assert (GE : mpd_val dP <= mpd_val dXk) by (first [clear - EQ; lia | clear - GT; lia]); clear SG.
    all: do 5 zstep.
    all: (flat constr:(Sbox) 2%nat; flclear Sbox; intros S2 _); clear MU WM LAWS KINV; rewrite <- mx_spe.
    all: pose proof (P_ecp_sw_rhs.mpd_val_sg1 dP GPS) as VPA.
    all: destruct (P_ecp_sw_rhs.mpd_val_pos_abs dXk (proj2 MXk) ltac:(clear - VP GE; lia)) as [XABS XSG].
    all: eapply e1_binop_ng with (h := h1) (LB := LB) (LF := LF') (m := m1) (SP := SPv) (lo := lo) (FR := 8) (FRAME := FRAME) (XO := XO) (MC := MC)
                         (dd := d + 1) (STKMAX := 848) (ENTRY := A_MPI_SUB_MPI) (STACK := MPI_ADD_SUB_STACK_A)
                         (A1 := XM) (d1 := dXk) (eA := dXk) (eB := dP) (v := v) (f := f) (RET := 0xcbea0);
      first [ kit_side_mx | exact HSUBNG | exact S2 | reflexivity
            | exact (or_introl eq_refl) | exact (or_intror (mx_ext dP OPP))
            | (right; rewrite EAk, EAP; clear - APG; lia)
            | (cbv beta; split; [rewrite GPS, XSG; reflexivity| split; [intros _; apply Z.le_refl| intros C; exfalso; clear - C XABS VPA GE; lia]])
            | (rewrite EAk; exact U1) | (rewrite EAk; reflexivity) | (rewrite EAP; reflexivity)
            | (eapply uw_obj_mono_d; [exact PUW| clear; lia])
            | (rewrite Evol; unfold AVOL_CALL in *; clear - BUD HVF; lia) | (rewrite Efr; clear - BUDF HFF FRC0; lia)
            | idtac ].
    all: match goal with |- forall _, _ => idtac | |- ?g => idtac "LOOP-SUB-LEFT:" g end.
    all: intros h3 LB3 m3 dX3 r3 t0_3 t1_3 t2_3 a1_3 a2_3 a3_3 a4_3 a5_3 a6_3 a7_3 t3_3 t4_3 t5_3 t6_3 S3 [[RV3 BK3] SZ3]; rewrite mx_spe.
    all: rewrite !Z.add_0_r in S3.
    all: pose proof (conj S3 I) as Sbox; clear S3; pose proof (AIh_laws asegs R HIA h3) as LAWS; pose proof (KF_kinv asegs R HIA h3 mo0) as KINV; pose proof (munch_refl ([] : list ivl) m3) as MU; pose proof (wmono_refl asegs m3) as WM.
    (* [comment removed for export] *)
    all: destruct RV3 as [(-> & VAL3) | ->].
    1, 3: zstep; (flat constr:(Sbox) 2%nat; flclear Sbox; intros S3 _); clear MU WM LAWS KINV;
          (eapply (IH v f h3 LB3 m3 dX3); [exact S3| clear - SZ3 HSZ; lia| rewrite VAL3; clear - MEAS VP GE; lia| exact HVB| exact HFB]).
    all: unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; do 3 zstep; (flat constr:(Sbox) 2%nat; flclear Sbox; intros S3 _); clear MU WM LAWS KINV.
    all: eapply (mx_fin _ _ h3 LB3 m3 dX3 (-16)); [exact S3| clear; lia| exact HVF| exact HFF].
    all: match goal with |- ?g => idtac "LOOP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00Q0?L10452285129.0 L10985005736.4 L13738328481.0 L13764063034.2 L1947681563.11 L19612994278.40L19612994278.41L22482349068.5 L23700557476.1 L2397676628.0  L27445912660.4 L27445912660.6 L29956516996.0 L32781056652.1 L35876627029.0 L35920637576.0 L37166975074.2 L39280637297.0 L41231340152.11L41231341304.10L42457021140.4 L43857236013.4 L44771130997.6 L44921588402.0 L470223081.7   L4781719053.2  L5000864057.2  L53862240067.1 L59068485257.4 L59382642534.4 L61279635374.1 L64664317652.2 L65349652035.1 00000100<00=00F00G00H00I00V00W00X00d01601701:01;01<01=01>01`02D02E02S02f02g03903?03E03J03W03e03f03g03hSS1g1N3MM01KSS2LB4C24HFFFS1g1N1d3MF01KFSS1N2N03dX11KS1p1N2N03NNX3dX11KSS1NSSFSS1R3HIA1h1p1N3BUD4SWP03GPN3IN03MMNS1R3HIA1h1N1d4BUDF4SWF04FRC03IF03MFNFS1p1N3IN04HVB1S1N1d4SWF04FRC03MFNSS1p1N4SWP03GPN3MMNS1d2D0S1N2N0S3dX1S1p1N3NNX3NRXS1N1d3IF04HFB1FFF". (* [comment removed for export] *)
  Lemma mx_body : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Pxra,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)(75.$9.(76.$9.VR,VHIA,Vh1,Vmo0,)$77.(5:.(5;.R10.(47.&40.Vsp1,)Vgp,Vtp,R?.R>.R=.Vsp,(47.&40.Vsp1,)R<.R;.R:.R9.R8.R7.R6.R5.(47.&40.VFB,)(47.&40.VQ,)(47.&40.VG,)(47.&40.(20.VFB,+60.))Vs6v,Vs7v,(47.&40.(20.(6=.VFB,+3.)(6>.(32.VR,))))(47.&40.VFB,)Vs10,Vs11,R4.R3.R2.R1.)VF,(47.&40.+<;>6<.)Vfc,(5=.(2.&40.))Vm1,(5>.$9.)))")
(* [comment removed for export] *).
  Proof.
    intros until t6.
    flat constr:(ck_budget) 12%nat. flclear ck_budget. intros N0 (NP0 & NPN) D0 MMB SWP0 SWF0 FRC0 FRC1 GIB IF0 CF3 CF2.
    destruct (ck_op_pt (pt_X p) ltac:(left; reflexivity)) as (OPX & NSX & NNX & _).
    flat constr:(PAT) 5%nat. intros EAX _ _ MXr _. flat constr:(MXr) 6%nat. intros _ _ _ _ NRX _.
    destruct (GIB (md_n (pt_X p)) ltac:(clear - NRX NNX; lia)) as [[GP0 GPN] _].
    destruct (GIB N ltac:(clear - N0; lia)) as [_ [IN0 _]].
    destruct (MMB N N ltac:(clear - N0; lia) ltac:(clear - N0; lia)) as [[MM0 _] [MF0 _]].
    assert (MMN : 0 <= mm_PHIn 0 N N N) by ((flat constr:(NLE) 2%nat; intros NP _); pose proof (mm_PHIn_mono 0 N N (md_n dP) 0 N N N ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) NP) as K; clear - K MM0; lia).
    assert (MFN : 0 <= mm_FRn 0 N N N (d + 1)).
    { flat constr:(NLE) 2%nat. intros NP _. pose proof (A_ecp_sw_rhs.mm_FRn_mono 0 N N (md_n dP) (d + 1) 0 N N N ltac:(clear; lia) ltac:(clear - N0; lia) ltac:(clear - N0; lia) NP ltac:(clear - D0; lia)) as K. clear - K MF0. lia. }
    assert (CFR : copy_FR (d + 1) = 2 * fr_charge (d + 1)) by (unfold copy_FR; exact CF2).
    pose proof mx_start as S0.
    pose proof (conj S0 I) as Sbox; clear S0. pose proof (AIh_laws asegs R HIA h1) as LAWS. pose proof (KF_kinv asegs R HIA h1 mo0) as KINV. pose proof (munch_refl ([] : list ivl) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    (* [comment removed for export] *)
    do 3 zstep.
    flat constr:(Sbox) 2%nat. flclear Sbox. intros S0 _. clear MU WM LAWS KINV. rewrite <- mx_spe.
    eapply A_ecp_one_c24.e1_copy with (h := h1) (LB := LB) (LF := LF') (m := m1) (SP := SPv) (lo := lo) (FR := 8) (FRAME := FRAME) (XO := XO) (MC := MC)
                        (dd := d + 1) (STKMAX := 848) (ENTRY := A_MPI_COPY) (A1 := XM) (d1 := dX0) (eY := pt_X p) (v := 0) (f := 0) (RET := 0xcbe78);
      first [ kit_side_mx | exact HCOPY | exact S0 | reflexivity
            | exact (or_intror (mx_ext (pt_X p) OPX))
            | (unfold copy_PHI; exact GP0)
            | (unfold copy_PHI; rewrite Evol; unfold check_pubkey_PHIn in BUD; unfold AVOL_CALL in *; clear - BUD GP0 GPN MMN SWP0 IN0; lia)
            | (rewrite Efr, CFR; unfold check_pubkey_FRn in BUDF; rewrite CF3, CF2 in BUDF; clear - BUDF MFN SWF0 IF0 FRC0; lia)
            | (rewrite EAX; reflexivity)
            | (unfold C24_COPY_c; unfold C24_ECP_CHECK_PUBKEY in C24H; clear - C24H; lia)
            | idtac ].
    all: match goal with |- forall _, _ => idtac | |- ?g => idtac "COPY-CALL-LEFT:" g end.
    intros h2 LB2 m2 dX1 r1 t0_1 t1_1 t2_1 a1_1 a2_1 a3_1 a4_1 a5_1 a6_1 a7_1 t3_1 t4_1 t5_1 t6_1 S1 CR1. rewrite mx_spe.
    assert (HSZ1 : md_n dX1 <= N).
    { destruct CR1 as ([(_ & _ & K)|(_ & K & _)] & _); cbn [md_n] in K; [clear - K NNX N0; lia| clear - K N0; lia]. }
    assert (HR1 : -2^31 < r1 <= 0) by (destruct CR1 as ([(K & _)|(K & _)] & _); subst r1; [clear; lia| unfold MBEDTLS_ERR_MPI_ALLOC_FAILED; clear; lia]).
    assert (HVB1 : 0 + copy_PHI (pt_X p) + intop_PHIn N + AVOL_CALL <= check_pubkey_PHIn N).
    { unfold copy_PHI, check_pubkey_PHIn. unfold AVOL_CALL in *. clear - GP0 GPN MMN SWP0 IN0. lia. }
    assert (HFB1 : 0 + copy_FR (d + 1) + intop_FRn (d + 1) + fr_charge (d + 1) <= check_pubkey_FRn N d).
    { unfold check_pubkey_FRn. rewrite CFR, CF3, CF2. clear - MFN SWF0 IF0 FRC0. lia. }
    pose proof (conj S1 I) as Sbox; clear S1. pose proof (AIh_laws asegs R HIA h2) as LAWS. pose proof (KF_kinv asegs R HIA h2 mo0) as KINV. pose proof (munch_refl ([] : list ivl) m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    (* [comment removed for export] *)
    zstep. if_cases KR1.
    { zstep. flat constr:(Sbox) 2%nat. flclear Sbox. intros S1 _. clear MU WM LAWS KINV.
      eapply (mx_fin _ _ h2 LB2 m2 dX1 r1); [exact S1| exact HR1| clear - HVB1 IN0; lia| clear - HFB1 IF0; lia]. }
    (* [comment removed for export] *)
    zstep. flat constr:(Sbox) 2%nat. flclear Sbox. intros S1 _. clear MU WM LAWS KINV.
    eapply (mx_loop (S (Z.to_nat (mpd_val dX1))) _ _ h2 LB2 m2 dX1); [exact S1| exact HSZ1| clear; lia| exact HVB1| exact HFB1].
    all: match goal with |- ?g => idtac "MXBODY-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End JMX.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00<0>L10985005736.4L19808940493.6L22482349068.5L2275137097.0 L31660992939.5L32781056652.1L34409126551.5L39280637297.0L44921588402.0L4781719053.2 L5000864057.2 L64630569949.300000;00R00_00`01401701G01H01I01O01U01^S1g1N3MM01KS1N1d4SWF04FRC03IF03MFNS1g1N1d3MF01KSS1N4SWP03GN03IN03MMNS1NS1R3MC13MC21x2HxSSS1d2D0S1N2N0S1R3HIA1h". (* [comment removed for export] *)
  Lemma ck_main : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)P,(68.$9.VR,VHIA,Vh,Vmo0,)P,(57.$9.Vm,Vlo,(2?.&40.Vsp,))(8:.$9.$77.(8;.(5:.(5;.Vra,Vsp,Vgp,Vtp,R?.R>.R=.Vs0,Vs1,(47.&40.VG,)(47.&40.VQ,)R<.R;.R:.R9.R8.R7.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R6.R5.R4.R3.)VF,(47.&40.$5<.)Vfc,(5=.(2.&40.))Vm,(5>.$9.))Vmo0,))")
(* [comment removed for export] *).
  Proof.
    intros until t6. intros HK0 ST.
    apply (aevtA_enter asegs (KF asegs R HIA h mo0) _ _ _ (conj HK0 (mo_frame_refl mo0))).
    eapply (aevtA_cut_evtA_KF asegs R HIA h mo0).
    { eapply pro_walk; exact ST. }
    intros ms1 P1.
    destruct P1 as (FB & sp1 & h1 & m1 & kind & r & xra & y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & s3v & s4v & s5v & s6v & s7v & w0 & w1 & w2
                   & Ems & KIND & K0 & K1 & K2 & SP1 & SP1M & HH1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & F64 & FRSH & FHD & FSH & SAVE & SLOT & SThi & STlo & MI1 & PRES0 & SSH1).
    subst ms1.
    unfold aevtA. intros mo1 [HK1 MF1].
    apply (aevtA_enter asegs (KF asegs R HIA h1 mo0) _ _ mo1 (conj (proj2 (HKI mo1) HK1) MF1)).
    destruct (frame_factsA R HIA CS h1 LB LF m1 FB 128 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS) as (CFB & _).
    destruct KIND as [-> | [-> | ->]].
    - (* [comment removed for export] *)
      flat constr:((K0 eq_refl)) 2%nat. intros -> HR. change (0 =? 0) with true in FSH |- *. cbv iota in FSH |- *.
      flat constr:(ck_budget) 12%nat. flclear ck_budget. intros N0 (NP0 & NPN) D0 MMB SWP0 SWF0 FRC0 FRC1 GIB IF0 CF3 CF2.
      destruct (GIB N ltac:(clear - N0; lia)) as [[GN0 _] [IN0 _]].
      destruct (MMB N N ltac:(clear - N0; lia) ltac:(clear - N0; lia)) as [[MM0 _] [MF0 _]].
      assert (MMN : 0 <= mm_PHIn 0 N N N) by ((flat constr:(NLE) 2%nat; intros NP _); pose proof (mm_PHIn_mono 0 N N (md_n dP) 0 N N N ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) NP) as K; clear - K MM0; lia).
      assert (MFN : 0 <= mm_FRn 0 N N N (d + 1)).
      { flat constr:(NLE) 2%nat. intros NP _. pose proof (A_ecp_sw_rhs.mm_FRn_mono 0 N N (md_n dP) (d + 1) 0 N N N ltac:(clear; lia) ltac:(clear - N0; lia) ltac:(clear - N0; lia) NP ltac:(clear - D0; lia)) as K. clear - K MF0. lia. }
      pose proof (presW_presA asegs R HIA h LB LF _ _ _ m m1 PRES0) as HP01.
      eapply ck_exit with (FBx := FB) (sp1x := sp1) (hk := h1) (LBk := LB) (v := 0) (f := 0) (r := r);
        first [ exact SP1 | exact SP1M | exact F64 | exact FRSH | exact CFB | exact HH1 | exact Ehtop | exact Estk | exact Eflag | exact FHD | exact FSH | exact SAVE | exact SLOT
              | exact SThi | exact STlo | exact MI1 | exact HR
              | (rewrite Ehcs; intros x Hx; exact Hx) | (rewrite Evol; clear; lia) | (rewrite Efr; clear; lia)
              | (intros b Hb; exact Hb)
              | idtac ].
      + unfold check_pubkey_PHIn. unfold AVOL_CALL. clear - MMN SWP0 GN0 IN0. lia.
      + unfold check_pubkey_FRn. rewrite CF3, CF2. clear - MFN SWF0 IF0 FRC0. lia.
      + eapply (presW_hmono R HIA h h1); [| rewrite Ehcs; intros x Hx; exact Hx| exact Estk].
        flat constr:(PRES0) 2%nat. intros P0 C123. split; [| exact C123].
        eapply presA_weaken; [exact P0| intros b Hb; exact Hb| intros b Hb; exact Hb| apply Z.le_refl| apply Z.le_refl| apply Z.le_refl| intros x _; exact I].
      + exists cnt. flat constr:(MCOK) 4%nat. intros MC1 MC2 MC3 _.
        eapply (presA_rw_cells asegs R); [exact HP01| exact MC0| | exact I].
        cbn [cells_size csize Nat.add]. intros x Hx. right. left. split; [clear - Hx MC1 MC2; lia| apply MC3; exact Hx].
    - (* [comment removed for export] *)
      flat constr:((K1 eq_refl)) 10%nat. intros GH1 -> -> -> -> -> padY padR YYI RHI.
      change (1 =? 0) with false in FSH |- *. change (1 =? 1) with true in FSH |- *. cbv iota in FSH |- *.
      eapply (sw_body FB sp1 h1 m1 padY padR w0 w1 w2); eassumption.
    - (* [comment removed for export] *)
      flat constr:((K2 eq_refl)) 6%nat. intros GH2 -> -> -> padX XMI.
      change (2 =? 0) with false in FSH |- *. change (2 =? 1) with false in FSH |- *. cbv iota in FSH |- *.
      eapply (mx_body FB sp1 h1 m1 padX w0 w1 w2 s6v s7v); eassumption.
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.

  Theorem A_ecp_check_pubkey_spec_s_c : ecp_check_pubkey_stmtA asegs R HIA MT A_ECP_CHECK_PUBKEY MC BP.
  Proof.
    unfold ecp_check_pubkey_stmtA. intros until slo.
    intros HH HK LFB GAT GKIND GPS SGA SGB VP GIMG NLE GCR GSP GMC GOB GUW PAT PFREE PSG PNLE QCR QSP QMC QOB QUW MC0 MCOK BP1 BP2 BI1 BI2 _ _ _
           ST LOS SLO SSH SLO1 SLO3 TOP SPA TPV MI RAE BUD UW BUDF C24H -> ->.
    eapply ck_main with (cnt := cnt) (bp1 := bp1) (bp2 := bp2) (N := N) (d := d) (slo := slo); first [ eassumption | idtac ].
    all: match goal with |- ?g => idtac "SPEC-LEFT:" g end.
  Qed.
End CK.

Theorem A_ecp_check_pubkey_spec_c : ltac2:(CDefT.buildp (gd_tbl_A_ecp_check_pubkey_c24 ()) "PR,$8<.PHIA,(8=.$9.R1.)PMT,(0.$1.)P,(8>.(32.R3.))P,(=.$6.(8?.R4.)$90.)P,(=.$6.(91.R5.+1.)$92.)P,(1;.=(93.R6.))P,(1;.=(94.R7.))P,Ph,(3=.$9.R8.R7.)PLB,(0.$4.)PLF,(0.$4.)Pm,P,(2.&40.)(3.(2.&8.))P,(44.$9.R<.R;.R4.R3.R2.R1.)(95.$6.(96.(5.$6.$6.)$6.(97.$6.$6.)R4.))P,(1:.(1;.(37.(2;.R9.))(7;.(2;.R9.)))(1;.(7<.(2;.R9.))(38.(2;.R9.))))P,Pa,$6.P,(=.$98.(99.$9.(1?.R1.))$9:.)P,(1:.(1;.=R2.)(1<.R2.(4;.+2.+40.)))(1:.(1;.(37.(2;.R=.))R3.)(1<.R3.(38.(2;.R=.))))P,Pm,P,(2.&40.)(3.(2.&8.))P,(9;.R<.R1.)(9<.R2.)P,(9=.$9.R<.R;.R:.$9>.$30.)P,(9?.$9.R=.R<.R;.$:0.$30.)P,(:1.$9.R>.R=.$:2.)P,(:3.$9.R?.R>.$:4.)P,(:5.$9.R10.R?.$:6.)P,(:7.$9.R11.R10.$:8.)(:9.$9.R12.R11.R10.$5<.$30.$79.)")
(* [comment removed for export] *).
Proof. intros. eapply A_ecp_check_pubkey_spec_s_c; eauto. Qed.
