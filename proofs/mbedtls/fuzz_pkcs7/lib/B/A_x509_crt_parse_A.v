(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_crt_parse_stmts A_pkcs7_cinfo A_asn1_get_tag_stmt A_asn1_get_tag A_oid A_mpi_stmtA A_x509_seq_stmts A_crt_parse_stmt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_get_san_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
Local Ltac lxg_b8u := repeat match goal with H : context [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 ?z))] |- _ => let k := eval vm_compute in (Z.modulo (bv_unsigned (Z_to_bv 64 z)) 256) in replace (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))) with (Z_to_bv 8 k) in H by (apply bv_eq; vm_compute; reflexivity) end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00033f1cfbf177b2 0 8 0 1 53 1 54 1 55 1 60 1 61 1 68 1 69 1P00515ae56da96925 0 8 0 1 4 1 39 1 53 1 60 1 61 1 68 1 69 1P00569fdf92ad8115 0 5 0 1 33 1 52 1 68 1 69 1P00b32cd6899532b1 0 4 0 1 52 1 68 1 69 1P00ec1af4b07885f3 0 8 0 1 53 1 54 1 55 1 60 1 61 1 68 1 69 1P01096dc083c3aa3a 0 8 0 1 4 1 39 1 53 1 60 1 61 1 68 1 69 1P01183774cebe3204 0 4 0 1 52 1 68 1 69 1P0119c13c531f89ac 0 4 0 1 52 1 68 1 69 1P0179a31126707567 1 2 16 2 0 1 70 1 16 2 1 1 69 1 2 71 1 72 1P01814a7d8f6a6242 0 6 0 1 53 1 60 1 61 1 68 1 69 1P019fc9437d3e08a3 0 8 0 1 53 1 54 1 55 1 60 1 61 1 68 1 69 1P01ab42a98dd9ef45 0 4 0 1 52 1 68 1 69 1P020fbdbc48b63b1c 0 4 0 1 52 1 68 1 69 1P0285582bdf91f25b 1 1 16 4 1 1 36 1 45 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P0309512036931ec9 1 1 16 4 1 1 36 1 45 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P033267b80bde4ed6 0 8 0 1 38 1 77 1 80 1 84 1 85 1 92 1 93 1P0370ca37f1c044c8 0 8 0 1 53 1 54 1 55 1 60 1 61 1 68 1 69 1P03e0d92bc9b6d38b 1 2 16 2 0 1 70 1 16 2 1 1 69 1 2 71 1 72 1P03f6fffe27c7662d 1 1 16 3 1 1 43 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P0531e75b63a1d22c 0 7 2 1 41 1 55 1 62 1 63 1 70 1 71 1P05d17be29ce4c468 0 7 1 1 54 1 57 1 61 1 62 1 69 1 70 1P05df802670d3a783 0 7 0 1 40 1 62 1 69 1 70 1 77 1 78 1P0630e1d391959c07 0 6 0 1 53 1 60 1 61 1 68 1 69 1P06413c4b03974ecc 0 4 0 1 52 1 68 1 69 1P06b9aeeec53bc34a 0 8 0 1 4 1 39 1 53 1 60 1 61 1 68 1 69 1P0736d384d1cf7267 1 1 16 3 0 1 94 1 95 1 7 44 4 78 4 85 4 86 4 93 4 96 4 97 64P0747d3e645471ea3 1 2 16 3 1 1 43 1 69 1 16 3 0 1 44 1 70 1 2 71 1 72 1P077d55627dce37d2 1 2 32 9 41 1 48 1 51 1 63 1 64 1 65 1 70 1 71 1 79 1 32 4 1 1 39 1 54 1 78 1 2 80 1 81 1P07c812b007efb745 0 12 0 1 10 1 40 1 50 1 59 1 62 1 63 1 64 1 69 1 70 1 77 1 78 1P07fbeae73b9d9a3d 0 7 1 1 54 1 57 1 61 1 62 1 69 1 70 1P0807dadf92f15ee7 1 1 16 3 0 1 78 1 79 1 4 43 2 77 2 80 2 81 32P080b9e3fcf079080 1 2 16 2 0 1 70 1 16 2 1 1 69 1 2 71 1 72 1P0812ff5d90b97843 1 2 16 3 1 1 43 1 69 1 16 3 0 1 44 1 70 1 2 71 1 72 1P08635da1724534aa 1 1 16 3 1 1 43 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P08833e4812f63960 0 8 0 1 4 1 39 1 53 1 60 1 61 1 68 1 69 1P089c1eae6f54a7f4 1 1 16 3 0 1 94 1 95 1 7 44 4 78 4 85 4 86 4 93 4 96 4 97 64P08a3ddaaaaef9256 1 1 16 4 1 1 36 1 45 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P08bd843c88823337 1 2 32 3 1 1 93 1 96 1 32 10 39 1 45 1 66 1 78 1 79 1 80 1 85 1 86 1 94 1 95 1 2 97 2 98 2P08c21b8db75ddb58 0 8 0 1 4 1 39 1 53 1 60 1 61 1 68 1 69 1P08f58c5fdc0f6322 0 4 0 1 52 1 68 1 69 1P0a8fcf367eaa20ce 0 7 0 1 53 1 56 1 60 1 61 1 68 1 69 1P0aa6628a40f12866 1 2 32 2 0 1 79 1 32 2 1 1 78 1 2 80 1 81 1P0aae364ca5ad40c9 1 2 16 2 0 1 70 1 16 2 1 1 69 1 2 71 1 72 1P0b3fb0083c2ae01f 0 5 0 1 33 1 52 1 68 1 69 1P0c64ab45d0622621 0 7 1 1 54 1 57 1 61 1 62 1 69 1 70 1P0d59f910ce620c40 1 1 64 2 0 1 92 1 3 14 1 93 1 94 64P0d7957d64153c4ef 0 4 0 1 52 1 68 1 69 1P0e18b825118f6fb8 1 1 16 3 0 1 79 1 80 1 4 44 2 78 2 81 2 82 32P0e51c38eba215e3b 0 4 0 1 52 1 68 1 69 1P0ebab6edbff5ed19 1 1 16 4 1 1 36 1 45 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P0edf54ed0ab5a48e 1 2 16 3 1 1 43 1 69 1 16 3 0 1 44 1 70 1 2 71 1 72 1P0f215f2dea4f6a76 1 1 16 2 1 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P0f556f15b0651c3e 0 7 2 1 41 1 55 1 62 1 63 1 70 1 71 1P104b98950caf4476 1 2 32 3 0 1 92 1 95 1 32 10 38 1 44 1 65 1 77 1 78 1 79 1 84 1 85 1 93 1 94 1 2 96 2 97 2P107d97345149c6c3 1 1 16 3 0 1 93 1 94 1 7 43 4 77 4 84 4 85 4 92 4 95 4 96 64P10d8aa1a35df5a05 0 7 1 1 54 1 57 1 61 1 62 1 69 1 70 1P10f5d06ac5cb32fa 0 7 1 1 54 1 57 1 61 1 62 1 69 1 70 1P116034c9d54b96e0 0 8 0 1 4 1 39 1 53 1 60 1 61 1 68 1 69 1P11760f943eae03b6 0 7 1 1 54 1 57 1 61 1 62 1 69 1 70 1P11766890363fa646 1 1 16 4 1 1 36 1 45 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P11fc4a633220bd23 0 4 0 1 52 1 68 1 69 1P11fda7299c658ed0 1 1 16 2 1 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P12bf23b7f5303496 0 5 0 1 43 1 61 1 77 1 78 1P1322012b3b5e8b5e 1 1 16 4 1 1 36 1 45 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P132a5055f43009f8 0 8 0 1 4 1 39 1 53 1 60 1 61 1 68 1 69 1P1375182f2b46650d 0 4 0 1 52 1 68 1 69 1P139840fbad76b93e 0 7 0 1 53 1 56 1 60 1 61 1 68 1 69 1P13b6553a2c5e786d 0 5 0 1 33 1 52 1 68 1 69 1P13db5fed1539a5dd 0 5 0 1 33 1 52 1 68 1 69 1P14219c2411396338 0 9 0 1 38 1 77 1 78 1 79 1 84 1 85 1 92 1 93 1P14670bb19dc581f8 0 6 0 1 53 1 60 1 61 1 68 1 69 1P14d7897395640278 0 8 0 1 4 1 39 1 53 1 60 1 61 1 68 1 69 1P14dd5a93c6bae98a 0 8 0 1 53 1 54 1 55 1 60 1 61 1 68 1 69 1P15088d0f5601b8d5 0 8 0 1 53 1 54 1 55 1 60 1 61 1 68 1 69 1P1525797682e37696 0 8 0 1 53 1 54 1 55 1 60 1 61 1 68 1 69 1P158c398aad468236 1 1 16 2 0 1 68 1 3 9 1 69 1 70 16P158e57a980b7c305 0 7 0 1 53 1 56 1 60 1 61 1 68 1 69 1P159b36a8d19a2422 1 2 32 3 0 1 93 1 96 1 32 10 39 1 45 1 66 1 78 1 79 1 80 1 85 1 86 1 94 1 95 1 2 97 2 98 2P15fe5f3ce1b01d8c 1 2 16 3 1 1 43 1 69 1 16 3 0 1 44 1 70 1 2 71 1 72 1P160093dc7ba60a83 0 8 0 1 4 1 39 1 53 1 60 1 61 1 68 1 69 1P1615c663e0fd6b18 0 7 2 1 41 1 55 1 62 1 63 1 70 1 71 1P1619b9bc6ae0588b 0 7 0 1 53 1 56 1 60 1 61 1 68 1 69 1P161dfadae1bbe916 0 6 0 1 53 1 60 1 61 1 68 1 69 1P16e69d9d8205e6d6 0 6 0 1 53 1 60 1 61 1 68 1 69 1P1713920f123f47ee 1 2 32 9 41 1 48 1 51 1 63 1 64 1 65 1 70 1 71 1 79 1 32 3 1 1 52 1 78 1 2 80 1 81 1P1718c66af6627d59 1 1 16 4 1 1 36 1 45 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P176dafc6958fdc77 1 2 16 2 0 1 70 1 16 2 1 1 69 1 2 71 1 72 1P177af68a16391c9e 0 7 1 1 54 1 57 1 61 1 62 1 69 1 70 1P179c8ee90ce9c5f5 0 6 0 1 53 1 60 1 61 1 68 1 69 1P17bd789204614b62 0 9 0 1 40 1 62 1 63 1 64 1 69 1 70 1 77 1 78 1P1803c82e0e778b8a 0 8 0 1 53 1 54 1 55 1 60 1 61 1 68 1 69 1P1816aebb13d09808 1 1 16 4 1 1 36 1 45 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P18256f89a69f54e1 1 1 16 3 0 1 93 1 94 1 4 58 1 92 1 95 1 96 16P18bf1645b55cba69 0 7 2 1 41 1 55 1 62 1 63 1 70 1 71 1P19192b55b0e4d4d1 0 6 0 1 53 1 60 1 61 1 68 1 69 1P1960cdc2d120e102 0 8 0 1 4 1 39 1 53 1 60 1 61 1 68 1 69 1P196743b5afc85248 0 8 0 1 4 1 39 1 53 1 60 1 61 1 68 1 69 1P19c17e1796b43413 0 7 0 1 38 1 77 1 84 1 85 1 92 1 93 1P1a414142e3485cb8 0 8 0 1 53 1 54 1 55 1 60 1 61 1 68 1 69 1P1b4e3e78db8522a2 0 8 0 1 53 1 54 1 55 1 60 1 61 1 68 1 69 1P1c437eaa05d62ad4 0 8 0 1 40 1 62 1 65 1 69 1 70 1 77 1 78 1P1c826d1bf5eb3351 0 11 2 1 40 1 67 1 76 1 79 1 80 1 81 1 86 1 87 1 94 1 95 1P1ca6c98a3c4c592a 0 7 0 1 53 1 56 1 60 1 61 1 68 1 69 1P1cadae203612b1ee 1 1 64 2 15 1 92 1 3 0 1 93 1 94 64P1cf1709180a239f5 1 1 16 3 1 1 43 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P1ded0ea60b40437a 0 7 2 1 41 1 55 1 62 1 63 1 70 1 71 1P1e0c2d55d190620a 1 2 16 3 1 1 43 1 69 1 16 3 0 1 44 1 70 1 2 71 1 72 1P1f489b04b1c4339d 0 4 0 1 52 1 68 1 69 1P1f6b07234d82a1c1 0 7 1 1 54 1 57 1 61 1 62 1 69 1 70 1P1fed561786c191ab 0 7 2 1 41 1 55 1 62 1 63 1 70 1 71 1P204f955c8bdf4bed 0 5 0 1 33 1 52 1 68 1 69 1P20e3ed0806e69ef4 1 1 16 3 1 1 43 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P20f3a3d355198014 0 7 2 1 41 1 55 1 62 1 63 1 70 1 71 1P225613bebde1d7b7 0 8 0 1 53 1 54 1 55 1 60 1 61 1 68 1 69 1P22a881eeb8ab4461 0 8 0 1 53 1 54 1 55 1 60 1 61 1 68 1 69 1P22c458930d1f6821 0 6 0 1 53 1 60 1 61 1 68 1 69 1P2347f832eb4491f9 0 7 0 1 53 1 56 1 60 1 61 1 68 1 69 1P235a76a0339667da 0 5 0 1 33 1 52 1 68 1 69 1P23db688e642b2832 1 2 32 3 0 1 93 1 96 1 32 10 39 1 45 1 66 1 78 1 79 1 80 1 85 1 86 1 94 1 95 1 2 97 2 98 2P2585c58370fa5804 0 8 1 1 39 1 78 1 81 1 85 1 86 1 93 1 94 1P258da3708fa16848 1 1 16 3 0 1 94 1 95 1 4 59 1 93 1 96 1 97 16P25bca3ae9864610a 1 1 16 2 1 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P25f25c537975288a 1 1 16 4 1 1 36 1 45 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P26984f82c81366be 0 11 2 1 42 1 52 1 61 1 64 1 65 1 66 1 71 1 72 1 79 1 80 1P2741c0d01e2d7714 0 6 0 1 53 1 60 1 61 1 68 1 69 1P275ab923aa517e99 0 7 1 1 54 1 57 1 61 1 62 1 69 1 70 1P27f5233b26ad37f8 1 2 16 3 1 1 43 1 69 1 16 3 0 1 44 1 70 1 2 71 1 72 1P284950933a04d926 0 5 0 1 33 1 52 1 68 1 69 1P285048c551787afd 1 2 16 2 0 1 70 1 16 2 1 1 69 1 2 71 1 72 1P28b530dbe5e1838f 0 5 0 1 33 1 52 1 68 1 69 1P28dddc5841bb8f00 1 2 16 3 1 1 43 1 69 1 16 3 0 1 44 1 70 1 2 71 1 72 1P2971d099ef6615b7 0 6 0 1 53 1 60 1 61 1 68 1 69 1P29bdce4234ce5c08 0 6 0 1 53 1 60 1 61 1 68 1 69 1P2a6fc48355a3d179 0 8 0 1 53 1 54 1 55 1 60 1 61 1 68 1 69 1P2a7820087d6455ed 0 7 0 1 53 1 56 1 60 1 61 1 68 1 69 1P2a8258d01d9a3325 1 1 16 3 1 1 43 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P2b0132570bf77920 0 4 0 1 52 1 68 1 69 1P2b2b887eba63dcb1 1 1 16 2 1 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P2b5ea3faa735c38d 0 6 0 1 36 1 43 1 61 1 77 1 78 1P2b84afcb6a90737d 0 7 0 1 53 1 56 1 60 1 61 1 68 1 69 1P2b8b0ba508770fe0 0 7 1 1 54 1 57 1 61 1 62 1 69 1 70 1P2bebd0967604ff03 0 3 0 1 38 1 53 1P2c705954d523fee0 1 1 16 2 1 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P2c7851f8e6331c30 0 7 2 1 41 1 55 1 62 1 63 1 70 1 71 1P2dd94b6f517deb4f 1 1 16 3 1 1 43 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P2e56808b59ac39a6 0 3 0 1 39 1 56 1P2f10db286dffd5d3 1 1 16 4 1 1 36 1 45 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P2f1bae8c44e89c97 1 1 16 2 1 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P2fd95d87f41284ca 0 7 0 1 53 1 56 1 60 1 61 1 68 1 69 1P2fdbab0649767aba 0 7 2 1 41 1 55 1 62 1 63 1 70 1 71 1P2fdd9de968fc22fb 1 1 16 4 1 1 36 1 45 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P302cf4dc6deace20 1 2 32 3 0 1 93 1 96 1 32 10 39 1 45 1 66 1 78 1 79 1 80 1 85 1 86 1 94 1 95 1 2 97 2 98 2P30bd6132addc983e 0 4 0 16 51 16 68 16 69 16P31a8d5e74d130885 0 6 0 1 53 1 60 1 61 1 68 1 69 1P31e277c7f90a6c81 0 5 0 1 33 1 52 1 68 1 69 1P32c4902ee376f528 1 2 32 3 0 1 92 1 95 1 32 10 38 1 44 1 65 1 77 1 78 1 79 1 84 1 85 1 93 1 94 1 2 96 2 97 2P32ca7386e5b5a403 0 7 0 1 53 1 56 1 60 1 61 1 68 1 69 1P32fd260d7bc7370e 0 7 0 1 38 1 77 1 84 1 85 1 92 1 93 1P331425c16c303889 1 1 16 4 1 1 36 1 45 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P34156f8948ded8c3 0 6 0 1 77 1 84 1 85 1 92 1 93 1P3446f0f3d59a9ac4 0 8 0 1 4 1 39 1 53 1 60 1 61 1 68 1 69 1P34768ac4a7dddf6b 1 1 16 2 1 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P34c6a43c8613f037 0 8 0 1 53 1 54 1 55 1 60 1 61 1 68 1 69 1P35852831e9c5e836 1 2 32 3 0 1 92 1 95 1 32 10 38 1 44 1 65 1 77 1 78 1 79 1 84 1 85 1 93 1 94 1 2 96 2 97 2P35970f8aee855c3d 0 8 0 1 4 1 39 1 53 1 60 1 61 1 68 1 69 1P35fa7e475cf0bc86 0 5 0 1 33 1 52 1 68 1 69 1P3601d35871a67922 0 7 0 1 53 1 56 1 60 1 61 1 68 1 69 1P367d047fbe0a9553 0 5 0 1 33 1 52 1 68 1 69 1P3681f86f9eb0a2b0 0 7 1 1 54 1 57 1 61 1 62 1 69 1 70 1P36dab0783ecae418 0 7 2 1 41 1 55 1 62 1 63 1 70 1 71 1P36f3160a083e6ca8 1 1 16 3 0 1 94 1 95 1 7 44 4 78 4 85 4 86 4 93 4 96 4 97 64P37bba9927d57f6b9 0 6 0 1 36 1 58 1 76 1 92 1 93 1P37c0ced9920e0535 1 1 16 4 1 1 36 1 45 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P37db1e893a8db2f2 0 5 0 1 33 1 52 1 68 1 69 1P37f2f04d10c56bf9 0 6 0 1 53 1 60 1 61 1 68 1 69 1P3801f5a9ed0cc3ca 0 4 0 1 52 1 68 1 69 1P380c5f06f08f0362 1 2 32 3 1 1 93 1 96 1 32 10 39 1 45 1 66 1 78 1 79 1 80 1 85 1 86 1 94 1 95 1 2 97 2 98 2P396648d47184908d 0 8 1 1 41 1 63 1 66 1 70 1 71 1 78 1 79 1P3978c8fbbfcb8bce 1 1 16 3 1 1 43 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P39d92ae2ff5ccfde 0 7 2 1 41 1 55 1 62 1 63 1 70 1 71 1P3a14d45d3e7b8797 0 7 2 1 41 1 55 1 62 1 63 1 70 1 71 1P3a3cad58c3f0be7a 0 6 0 1 53 1 60 1 61 1 68 1 69 1P3a928bc1b3bfb322 0 7 0 1 53 1 56 1 60 1 61 1 68 1 69 1P3aa22addddf99ef8 0 7 1 1 54 1 57 1 61 1 62 1 69 1 70 1P3aefca9653bc1a0d 1 1 16 4 1 1 36 1 45 1 69 1 9 39 1 42 1 54 1 55 1 56 1 61 1 62 1 70 1 71 16P3b1aea49a1f70a7c 0 7 0 1 53 1 56 1 60 1 61 1 68 1 69 1P3c12ee5dec17b736 0 12 0 1 7 1 38 1 65 1 74 1 77 1 78 1 79 1 84 1 85 1 92 1 93 1P3c93a4f2ae4dbb96 0 7 1 1 54 1 57 1 61 1 62 1 69 1 70 1P3d57bdd71ffcdb6a 1 2 16 2 0 1 70 1 16 2 1 1 69 1 2 71 1 72 1P3d7e7e0ba0f633b3 0 7 2 1 41 1 55 1 62 1 63 1 70 1 71 1P3db0a1325463ac4f 0 7 2 1 41 1 55 1 62 1 63 1 70 1 71 1P3e3e297968469799 0 8 0 1 4 1 39 1 53 1 60 1 61 1 68 1 69 1P3e5e047b2bf56a7a 0 5 0 1 33 1 52 1 68 1 69 1P3ea0e963f6fb7337 0 5 0 1 33 1 52 1 68 1 69 1P3f0cb5dbbe2f8864 0 7 0 1 53 1 56 1 60 1 61 1 68 1 69 1P3f2dce7cd21b96df 0 7 1 1 54 1 57 1 61 1 62 1 69 1 70 1P3f88baa9b96c4f10 0 6 0 1 55 1 58 1 76 1 92 1 93 1N004d763252602702N007c9d252f5d8e03N017ae1f14a564ffcN018905b55354d211N027f98e91d08a947N03209aba73280a98N03959aba42237739N03f7722195157e95N0422bdee13e11947N042509b8ad6f0379N04430d22ef2b0b04N04a492e7c8c01e06N05ba98872c86efe4N05bf5915df2a2246N05e546900d3aa48dN063d6883c36d5ff0N069798a401602225N06daaa8001f8bef1N082ed91ef6039ffaN08d651c42d2e1ef2N0b2e5e7cbe51ed97N0c10ca8fb58610a6N0c77e7f2417c9f2eN0ccec9323f277e30N0cd32041ebdb78f4N0ce603cd7a2607aaN0dc318de826c2c12N0e0cb58102617305N0edffd245b0363a6N0ef2f1c811003506N0f933987a487f26cN0ff55d14d886788fN1116251dea8dd338N11ba164c0523b309N11bf671317f05e4cN11fd7c33a8191be4N121cbf699c554547N123b3d374554d0ebN124dd8e99b238578N1309c57e4d89d7c8N13e9b1cc5c8ef5a6N1482295a288b5822N15152f6b24365843N1524edfaeded6bb4N1559b78d7153dab5N15a70122ed204c74N15c84b67567f7ea1N1612fd8e494a435fN1648b509017bad45N1852a4f9a9b5126eN18577e84c5790bf1N19ac3f548f0e4165N19c147cf888d4d09N1ac58f0507572d0bN1adebac0c76c6dd3N1b0bf6c946010212N1b539def1e0152b3N1bd79b6722a44373N1dcf3f177551916bN1dd9922622770ea4N1e0632825d560f6cN1e30a5d456c8e3eaN1e48608e25a1b32bN1eeaa069b02411b5N1f5d84427f391f80N2128faf648caf1d1N21a344a142645f0fN21db6c5ba7cfb62fN223d035d6754a42aN223fa02d392f949cN22a2fe3bd08097f7N22c4908c97d51226N23937993253ad857N23ae32fe610c417fN23c1a314c9186dc4N240b510274c0cf19N246f576a3bddbaadN24da30ca08a81172N258025dec9eb7ec5N268fd40e86742fbcN27cd4f86d1f4b567N27d117caf495ad08N2923516f6c1b6001N29798415094db057N29880888375bca49N29dd1e518709aff6N2addeb7a43bf2629N2b2258ac43a2991bN2bb6d762c609fa2bN2c65d5cf5ae8d0bbN2d40611126ee9903N2d54977edcc070eaN2dea100f392d26acN2e2afc9cbff865a2N2edff187ad4cc2bfN2fc9cf43e00a567bN2fd496814f0ce569N304750d94440c685N30c254a71a6dcbd5N30efd255139a2afcN318a448e07c76d80N3279c05a55f1f561N32aaacc35d14c3e0N32dfa7b1088dc677N32e52b671265c245N33cd75fcf1866ea7N33fc70cf7bc58718N341823767718beeaN341de1c6aa24efe4N3491b3c3273b3027N34bbe89609b4fed8N34e955b1789600b5N34fbc0e5da8d0a4fN357798dc1c308907N35ad685848085ed2N363a69caa63bdf13N36899cfbe88b4c60N36a3112faedc5404N370a0dde07ac51daN38f4069b06bc3e47N395434da8b1617b8N39b99ff064047621N39c5c6b7b11e3200N3b2f0485db0483b2N3b7b681bda39a0e3N3d1aaa542bfb9838N3d7bac78dc4af44fN3ddf039dd8e7074dN3df5a9325a4e60ecN3e1c1b5a03074c25N3ef12638bcb8ec09"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import LiaOrcFF5. (* [comment removed for export] *)
Local Ltac lia_t12 ::= orc_lia_t12. (* [comment removed for export] *)
Local Ltac ff5_rlia ::= orc_ff5_rlia. (* [comment removed for export] *)
Local Ltac ff5_overlap_ctx A2 n2 a len ::= orc_ff5_overlap_ctx A2 n2 a len. (* [comment removed for export] *)
Local Ltac ff5_overlap A2 n2 a len ::= orc_ff5_overlap A2 n2 a len. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_ff5_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
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
Ltac2 gd_tbl_A_x509_crt_parse_A () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Spec.RepCrt.zeros"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Walk.Call.S1P"; "A_X509_CRT_PARSE_INT"].


Definition A_X509_CRT_PARSE_INT : Z := 0xa9270.       (* [comment removed for export] *)

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM3 : arl_smalloc R 3 = 0x53398.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Variable STKc : Z.   (* [comment removed for export] *)
  Hypothesis STKc0 : 0 <= STKc.

  (* [comment removed for export] *)
  Definition STKx : Z := 272 + 48 + STKc + arl_need_smalloc R.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (CRT Q blen BUF lo slo : Z) (bs : list byte) (WS : list ivl).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF < 511)%nat.
  Hypothesis BIN : In (BUF, n) LB.
  Hypothesis B1 : BUF <= Q. Hypothesis B2 : 0 <= blen. Hypothesis B3 : Q + blen <= BUF + n. Hypothesis B47 : BUF + n < 2^47. Hypothesis B5 : 0 < BUF.
  Hypothesis ALC : CRT mod 8 = 0.
  Hypothesis CRT0 : 0 < CRT.
  Hypothesis CWX : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) CRT 744.
  Hypothesis CRTLO : CRT + 744 <= lo.
  Hypothesis DXB : CRT + 744 <= BUF \/ BUF + n <= CRT.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKx.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT in UARG; unfold STKx in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation W := ((CRT, CRT + 744) :: WS).
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.
  Local Notation FSHP := [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Ltac cb8_at H i :=
    lazymatch type of H with rw_cells _ _ _ ?cs => let pre := eval cbv beta iota delta [firstn] in (firstn i cs) in cb8_to_c8 H pre end.

  (* [comment removed for export] *)
  Definition S1P (a3e a4e a5e : word) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_parse_A ()) "Lms,$0.(1.$2.LFB,$2.(1.$2.Lsp1,$2.(1.(3.$4.VR,VHIA,)Lh1,(3.$4.VR,VHIA,)(1.P,(5.&40.)(6.(5.&8.))Lm1,P,(5.&40.)(6.(5.&8.))(1.(5.&40.)Lx5,(5.&40.)(1.(5.&40.)Lx6,(5.&40.)(1.(5.&40.)Lx7,(5.&40.)(1.(5.&40.)Lx10,(5.&40.)(1.(5.&40.)Lx11,(5.&40.)(1.(5.&40.)Lx12,(5.&40.)(1.(5.&40.)Lx13,(5.&40.)(1.(5.&40.)Lx14,(5.&40.)(1.(5.&40.)Lx15,(5.&40.)(1.(5.&40.)Lx16,(5.&40.)(1.(5.&40.)Lx17,(5.&40.)(1.(5.&40.)Lxs10,(5.&40.)(1.(5.&40.)Lx28,(5.&40.)(1.(5.&40.)Lx29,(5.&40.)(1.(5.&40.)Lx30,(5.&40.)(1.(5.&40.)Lx31,(5.&40.)(1.(5.&40.)Lw0,(5.&40.)(1.(5.&40.)Lw1,(5.&40.)(1.(5.&40.)Lw2,(5.&40.)(1.(7.(5.&8.))Ljloc,(7.(5.&8.))(1.(7.(5.&8.))Lja,(7.(5.&8.))(1.(7.(5.&8.))Ljb,(7.(5.&8.))(1.(5.&40.)Lk24,(5.&40.)(1.(5.&40.)Lk32,(5.&40.)(1.(5.&40.)Lk40,(5.&40.)(1.(5.&40.)Lk48,(5.&40.)(1.(5.&40.)Lk56,(5.&40.)(1.(5.&40.)Lk64,(5.&40.)(1.(5.&40.)Lk72,(5.&40.)(1.(5.&40.)Lk80,(5.&40.)(1.(5.&40.)Lk88,(5.&40.)(1.(5.&40.)Lk96,(5.&40.)(1.(5.&40.)Lk104,(5.&40.)(1.(5.&40.)Lk112,(5.&40.)(8.(9.$0.R27.(:.(;.(<.&40.+:92?4.)(<.&40.R25.)Vgp,Vtp,R22.R21.R20.Vsp,(<.&40.R25.)R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.(<.&40.(=.(>.R26.+3.)(?.(10.VR,))))(<.&40.R26.)O1.(<.&40.VCRT,)(<.&40.(?.(10.VR,)))(<.&40.VQ,)(<.&40.R26.)O3.R17.(<.&40.Vblen,)R16.R15.R14.R13.)VF,(<.&40.+:9414.)Vfc,(11.(5.&40.))R23.(12.$4.)))(8.(8.(13.(14.(15.&40.Vsp,)+110.)R25.)(13.R25.(14.(15.&40.Vsp,)+100.)))(8.(9.$2.(16.R25.+20.)=)(8.(17.$4.VR,VHIA,R24.VLB,(18.(19.$2.$2.)(1:.$2.$2.R26.+200.)VLF,)R23.)(8.(9.P,$2.Sp(1;.$4.VR,VHIA,R24.)(1;.$4.VR,VHIA,Vh,))(8.(9.$2.(1<.$4.VR,VHIA,R24.)(1<.$4.VR,VHIA,Vh,))(8.(9.$2.(1=.$4.VR,VHIA,R24.)(1=.$4.VR,VHIA,Vh,))(8.(9.$2.(1>.$4.VR,VHIA,R24.)(1>.$4.VR,VHIA,Vh,))(8.(9.$2.(1?.$4.VR,VHIA,R24.)(1?.$4.VR,VHIA,Vh,))(8.(9.$2.(20.$4.VR,VHIA,R24.)(20.$4.VR,VHIA,Vh,))(8.Pmo,$21.(22.(23.$4.VR,VHIA,R25.R1.)(23.$4.VR,VHIA,Vh,R1.))(8.(9.$2.(16.R26.+40.)=)(8.(24.VR,VLB,VLF,R26.+200.)(8.(25.$4.R23.R26.(18.$26.(27.R12.)(18.$26.(27.R11.)(18.$26.(27.R10.)(28.$26.)))))(8.(25.$4.R23.(=.R26.+20.)(18.$26.(29.#1=8.R?.)(28.$26.)))(8.(25.$4.R23.(=.(>.R26.+3.)(?.(10.VR,)))(18.$26.(2:.(<.&8.+?1.))(18.$26.(2:.(<.&8.+?1.))(18.$26.(2:.(<.&8.+?1.))(18.$26.(2:.(<.&8.+?1.))(18.$26.(2:.(<.&8.+?8.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?8.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?8.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?8.))(18.$26.(2:.(<.&8.+?8.))(18.$26.(2:.(<.&8.+?8.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?8.))(18.$26.(2:.(<.&8.+?8.))(18.$26.(2:.(<.&8.+?8.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?2.))(18.$26.(2:.(<.&8.+?8.))(18.$26.(2:.(<.&8.+?8.))(18.$26.(2:.(<.&8.+?8.))(18.$26.(2:.(<.&8.+?3.))(18.$26.(2:.(<.&8.+?3.))(18.$26.(2:.(<.&8.+?3.))(18.$26.(2:.(<.&8.+?3.))(18.$26.(2:.(<.&8.+?3.))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(18.$26.(2:.(<.&8.=))(28.$26.))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))(8.(25.$4.R23.(=.(15.&40.Vsp,)-68.)(18.$26.(27.Vs11,)(18.$26.(27.Vs10,)(18.$26.(27.Vs9,)(18.$26.(27.Vs8,)(18.$26.(27.Vs7,)(18.$26.(27.Vs6,)(18.$26.(27.Vs5,)(18.$26.(27.Vs4,)(18.$26.(27.Vs3,)(18.$26.(27.Vs2,)(18.$26.(27.Vs1,)(18.$26.(27.Vs0,)(18.$26.(27.Vra,)(28.$26.)))))))))))))))(8.(25.$4.R23.R25.(18.$26.(29.#18.R>.)(18.$26.(27.R<.)(18.$26.(27.R;.)(18.$26.(27.R:.)(18.$26.(27.R9.)(18.$26.(27.R8.)(18.$26.(27.R7.)(18.$26.(27.R6.)(18.$26.(27.R5.)(18.$26.(27.R4.)(18.$26.(27.R3.)(18.$26.(27.R2.)(18.$26.(27.R1.)(18.$26.(27.O2.)(18.$26.(29.#10.R=.)(18.$26.(27.(<.&40.R26.))(28.$26.))))))))))))))))))(8.(2;.$4.R23.(=.R25.+98.)(=.(15.&40.Vsp,)-68.))(8.(2;.$4.R23.Vlo,R25.)(8.(2<.$4.R23.)(8.(25.$4.R23.VCRT,(18.$26.(29.#2>8.(2=.#2>8.))(28.$26.)))(8.(2>.$4.R23.VBUF,Vbs,)(8.(2?.$4.(10.VR,)(1;.$4.VR,VHIA,Vh,)R23.VCRT,+2>8.)(8.(2?.$4.(10.VR,)(1;.$4.VR,VHIA,Vh,)R23.VBUF,(30.(31.(5.&8.)Vbs,)))(8.(32.(13.(=.R26.+200.)VCRT,)(13.(=.VCRT,+2>8.)R26.))(8.(33.$4.VR,VHIA,Vh,VLB,VLF,(15.&40.Vsp,)(15.&40.Vsp,)(18.(19.$2.$2.)(1:.$2.$2.VCRT,(=.VCRT,+2>8.))VWS,)Vm,R23.)(8.(34.$4.(10.VR,)R23.Vslo,R25.)(34.$4.(10.VR,)R23.R25.(15.&40.Vsp,))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 ALC; try lx_pin1 B5; try lx_pin1 B2; try lx_pin1 B1; try lx_pin1 WS.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02K0@D10823604468.144D12658639931.102D12660902694.144D1699716194.103 D1706006080.176 D18607476203.145D18607476203.149D20553579080.146D20553579080.147D20553579080.148D2457697671.175 D31412296985.176D31526457809.102D31538959723.174D32458983516.175D3254889317.144 D32606360471.177D33194539134.102D33271305925.174D3386124079.174 D37929882811.174D39411162312.145D39411162312.149D39745574690.175D40202443482.176D45702483614.174D50254960491.146D50254960491.147D50254960491.148D52056129450.149D54544308936.174D560907438.104  D60098680296.174D60098777666.103D60109264992.176D6192914196.149 D62009673036.177D62011770188.104D65215601097.176D65226085355.103D68409458028.174D6897397609.174 D9107052239.176 L10087043225.150L15173828345.155L19548981079.155L19931907068.127L19980016842.12 L21889685938.9  L2330740866.128 L2333531081.144 L2333536794.144 L24973438614.1  L26163319614.144L26163329773.144L2676383091.180 L29604608213.0  L29738741675.1  L31012612437.0  L32040257543.1  L32969851384.12 L33472729358.111L33485826452.1  L33485826452.13 L35653441506.11 L39618635427.2  L40228640085.0  L43055154860.98 L44795638106.104L48117620906.90 L48119718056.151L48119718059.150L48132302231.106L50790731766.11 L54336156040.9  L55229739634.155L56380976587.10 L567271841.0    L57355539152.155L57355539152.157L57714139801.12 L58790154276.12 L59308634497.16 L60098763854.6  L60754583113.0  L61437265048.2  L6302880071.144 L6302890132.144 L63324633318.100L65391155889.153L6910010094.150 L7040749983.105 L9356559645.16  L9873114841.11  P30296383852.144P30296383852.149Q10087043225.182Q10099627429.180Q10099627453.184Q10523111615.107Q10594483356.181Q12660624646.110Q13367393091.107Q1530342990.149 Q1699713899.109 Q1699713907.106 Q23927511187.111Q23927511190.107Q26032252593.186Q29717295545.181Q31021924279.144Q32440833928.180Q32738464549.106Q33196749123.110Q33271078526.180Q34966725143.186Q38248895666.112Q40271359350.149Q42437284299.134Q42439168719.144Q42439382242.113Q42441479395.188Q43880146030.112Q44927014883.106Q44927014883.133Q44927014883.180Q46648903583.181Q47230721786.107Q47313632828.106Q47313632828.133Q47313632828.180Q48119718058.181Q48132302231.180Q50796826103.149Q53579321455.144Q56533317814.181Q58741084399.180Q59865520189.113Q59867617340.188Q59871812884.134Q62011770187.111Q62011770190.107Q64683599819.113Q64685695714.134Q65226087650.109Q65226087674.106Q67038703949.144Q67517027822.106Q67517027822.133Q67517027822.180Q6897428426.184 Q6897428434.180 Q6910010094.182 Q8701272485.188 Q9350548487.130 00000O00a01@01R02402502602702802902:02;02<02=02[02\03C03U03V03W03X03Y03Z04804904W04X04Y04Z05905:05P06706N07507P08008@08b09409509S09T09g0:P0;80;N0;f0<J0=<0==0=>0=C0=D0=E0=h0=i0=m0=n0>20>30>40>50>60>N0>X0>Y0?L0@60@d0AW0BJ0C80CX0D<0Dd0E=0E>0E?0Em0En0FN0FX0Fb0Fc0Fk0Fl0Fm0G?0H:0HM0Hk0I_0JL0Jm0KN0Ka0L40LG0LW0Lj0M90M:0MU0Md0N30NF0Ne0O?0OR0P60P70PI0PX0PY0QL0QZ0R20RH0Rc0S90ST0Se0Sf0Sg0Sh0Si0T:0T;0T<0T=0U00Uc0VR0Vf0Vg0Vh0Vi0Vj0Vk0W80WE0Wh0XK0XZ0Xi0Y`0Ya0Yb0Yc0Z60ZI0Z\0[L0[hS2LF2sp3BUF2bs3LFB3sp13H204LFB'S2LF2sp3BUF2bs3LFBS2LF2sp3BUF2bs3LFB3sp13H204LFB'S2LF2sp3CRT2bs3LFBS2LF2sp3CRT2bs3LFB3sp13H204LFB'2FBFFFFFFFFFS2LF2sp2bs3LFB3sp13H204LFB'2FBFS1R3HIA2LF2sp2bs3LFB3sp13H204LFB'2h12FBS2LF2sp3BUF2bs3LFBFFFFFS2LF2sp2bs3LFB3sp13H204LFB'2FBFS2LF2sp2bs3LFB3sp13H204LFB'2FBFFFS2LF2sp2bs3LFB3sp13H183H204LFB'FS1R3HIA1h2LF2sp2bs3LFBS1R2LF2sp2lo2bs3LFB3LOS3sp13H204LFB'2FBS1R2LF2sp2lo2bs3LFB3LOSS1R2LF2sp2lo2bs3LFB3LOS3sp13H204LFB'2FBS2LF2sp2bs3LFB3sp13H204LFB'S1R2LF2sp2bs3LFB3sp13H204LFB'2FBS1R2LF2sp2bs3LFBS2LF2sp3CRT2bs3LFB3sp13H204LFB'2FBS2LF2sp3CRT2bs3LFBFS2LF2sp2bs3LFB3sp13H204LFB'2FBFS2LF2bs3LFB4LFB'2FBS1R2LF3slo2bs3LFB4SLOS3ALO3sp14LFB'2FB2F1S2LF2sp2bs3LFB3SPR3sp13H204LFB'2FB2F02F8S2LF2sp2bs3LFB3sp13H20S1R3HIA1h2sp3TOP3sp13SP1S1R3NS14STKc5STKc02sp2lo3SLO3sp13SP1S1R3NS14STKc5STKc02LF2sp2lo2bs3LFB3SLO3SPR3sp13H20FFS3sp1FFS2LF2sp2bs3LFB3sp13H204LFB'2FB1c2HcSS2FBSS2spSFFFS1R3HIA1h2sp2lo3TOP4HTOPS3sp14SP1MSS1R3NS14STKc5STKc02LF2sp3CRT2lo2bs3LFB4CRT03SLO3SPRS2LF2sp2bs3LFB3SPA3SPR3sp13H163H173H183H20S1R3NS14STKc5STKc02LF2sp2lo2bs3LFB3SLO3LOS3ALOS1R3NS14STKc5STKc02LF2sp2lo2bs3LFB3SLO3LOS3ALO4LFB'S1R3NS14STKc5STKc02LF2sp2lo2bs3LFB3SLO3LOS3ALO4LFB'S1R3NS14STKc5STKc02LF2sp2lo2bs3LFB3SLO3LOS3ALOS1R3NS14STKc5STKc02sp2lo3SLO3LOSS1R3NS14STKc5STKc02sp2lo3SLO3sp13SP1S2LF2sp2bs3LFB3SPR3sp13H204LFB'2FB2F02F8S1R3BUF2lo2bs3LOS3BCE3ALOSFS1R2LF2sp2bs3LFB3ACV3SPR3sp13H204LFB'2FB2F02F1SS1R4STKc5STKc02sp2lo3SLO3sp13SP1S2FB2F02KbS1R2lo3LOSSS2LF3LFBFFS2LF2sp3CRT2bs3LFBS1R3NS14STKc5STKc02LF2sp2lo2bs3LFB3SLO3sp13SP14LFB'2FB4FBLOS2LF2bs3LFB4LFB'2FBS2LF2sp2bs3LFB3SPR3sp13H163H20S1R3NS14STKc5STKc02sp2lo3SLO3LOS3ALO3ACV3SPR3sp13SP1S1R3NS14STKc5STKc02sp2lo3slo4SLOL3SLO3sp13SP1S2LF3CRT2lo2bs3LFB5CRTLO3sp14LFB'S2LF3CRT2lo2bs3LFB5CRTLO3sp14LFB'S2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS1R2LF2sp2bs3LFBS2LF2bs3LFB4LFB'2FBS2LF3BUF2bs3LFBFS2LF2sp2bs3LFB3sp13H184LFB'S2LF3CRT2bs3LFBS2LF3CRT2bs3LFBS1R3HIA1h2LF2bs3LFBS1R3HIA1h2LF2sp2bs3LFB3TOP4HTOPS2LF2sp2lo2bs3LFB3sp14LFB'S2LF2bs3LFB4LFB'2FBS1R3HIA1h2LF2sp2bs3LFB3TOP4HTOP4LFB'FS2LF3CRT2bs2WS3LFBS2LF3BUF2bs3LFBFS1R3NS14STKc5STKc02LF2sp2lo2bs3LFB3SLO3sp13SP14LFB'S2LF2lo2bs3LFBS1R3HIA1h2LF2bs3LFB4LFB'S1R2LF3slo2bs3LFB4SLOSS1R2LF3slo2bs3LFB4SLOS4LFB'S1R2LF3slo2bs3LFB4SLOSS1R2LF3slo2bs3LFB4SLOS4LFB'S2LF2sp2lo2bs3LFBFFFFS1R2LF2bs3LFB3ALOFFFS1R3NS14STKc5STKc02LF2sp2lo2bs3LFB3SLO3LOS3ALO4LFB'S1R3NS14STKc5STKc02LF2sp2lo2bs3LFB3SLO3LOS3ALO4LFB'S1R3NS14STKc5STKc02LF2sp2lo2bs3LFB3SLO3LOS4LFB'S2LF2bs3LFB3sp14LFB'FFFFFS1R2LF2bs3LFBS1R2LF2bs3LFBS1R3HIA1h2LF2sp3slo2bs3LFB3TOP4HTOPS1R3HIA1h2LF2sp3slo2bs3LFB3TOP4HTOPS2LF3CRT2bs3LFBS2LF3CRT2bs3LFBS1R3NS14STKc5STKc02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP14LFB'FFFS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS1R3HIA1h2LF2sp3slo2bs3LFB3TOP4HTOP3sp13SP14LFB'S2LF2bs3LFB3sp13H193H204LFB'". (* [comment removed for export] *)
  #[using="LOS TPV SPH SPA TOP SLO SLOL SLOS DXB CRTLO CWX CRT0 B47 B3 BIN LFB STKc0 STKc NS1 SM3 UARG IMG"]
  Lemma pro_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_crt_parse_A ()) "Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Pa3,(5.&40.)Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)P,(17.$4.VR,VHIA,Vh,VLB,VLF,Vm,)P,(25.$4.Vm,VCRT,(18.$26.(29.#2>8.(2=.#2>8.))(28.$26.)))P,(2>.$4.Vm,VBUF,Vbs,)P,(2;.$4.Vm,Vlo,(15.&40.Vsp,))P,(34.$4.(10.VR,)Vm,Vslo,(15.&40.Vsp,))P,(2<.$4.Vm,)P,(2?.$4.(10.VR,)(1;.$4.VR,VHIA,Vh,)Vm,VCRT,+2>8.)P,(2?.$4.(10.VR,)(1;.$4.VR,VHIA,Vh,)Vm,VBUF,(30.(31.(5.&8.)Vbs,)))(35.$4.(10.VR,)(1;.$4.VR,VHIA,Vh,)(36.R11.R10.R?.)(:.(;.Vra,Vsp,Vgp,Vtp,R14.R13.R12.Vs0,Vs1,(<.&40.VCRT,)(<.&40.VQ,)(<.&40.Vblen,)R11.R10.R?.R>.R=.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R<.R;.R:.R9.)VF,(<.&40.$37.)Vfc,(11.(5.&40.))Vm,(12.$4.)))")
(* [comment removed for export] *).
  Proof.
  intros until t6.
  intros HH HCRT HBUF ST SS MI OCRT OBUF.
  unfold A_X509_CRT_PARSE_INT.
  pose proof (blocks_below_hm R HIA h LB LF m LB HH ltac:(intros b Hb; exact Hb)) as BB0.
  destruct (BB0 _ BIN) as [_ BCE].
  cbn [fst snd] in BCE.
  clear BB0.
  assert (BINA : In (BUF, n) (LB ++ fdata LF)) by (apply in_app_iff; left; exact BIN).
  rt_facts.
  assert (BUFLO : BUF + n <= lo) by (first [ clear - BCE ALO LOS; lia | lx_side_lia ]).
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| first [ clear - LOS; lia | lx_side_lia ]| first [ clear - SLO NS1 STKc0 TOP HTOP; lia | lx_side_lia ]]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (bv_unsigned sp) W HH ltac:(first [ clear - LOS SLO NS1 STKc0; lia | lx_side_lia ])) as PRES.
  destruct IMG' as (EGOT & ELO & EHI & EGSB).
  carve_frame 256%nat ST.
  (* [comment removed for export] *)
  idtac "T-SAVED".
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
  lazymatch goal with HHc : HM _ _ _ h LB LF mc |- _ =>
  pose proof (hm_abase asegs R HIA h LB LF mc HHc) as AB;
  pose proof (abase_got _ _ _ AB) as GOT; pose proof (abase_gsb _ _ _ AB) as GSB;
  destruct (hm_auar asegs R HIA h LB LF mc HHc) as [UGOT UFLAG];
  pose proof (hm_flag_img asegs R HIA h LB LF mc HHc) as FLIMG
  end end.
  rewrite EGOT in GOT.
  rewrite UARG in UGOT.
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0xa92b4] [] 848%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).   (* [comment removed for export] *)
  lxr_leaf. lx_carry.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 272 <= sp1 <= bv_unsigned sp - 256) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  assert (SP1R : 0 <= sp1 < 2^64) by (first [ clear - SP1 SPR SLO LOS ALO ACV NS1 STKc0; lia | lx_side_lia ]).
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m0 end.
  lazymatch goal with FRx : rw_cells _ m0 (bv_unsigned sp + -256) _ |- _ => chunk_split FRx 2%nat FRa SAVE end.
  replace (bv_unsigned sp + -256 + 152) with (bv_unsigned sp + -104) in SAVE by (clear; lia).
  lazymatch goal with STx : stk _ m0 lo (bv_unsigned sp + -256) |- _ => release_frame FRa STx (bv_unsigned sp + -104); rename STx into STJ end.
  destruct (stk_split asegs m0 lo (sp1 + 152) (bv_unsigned sp + -104) STJ ltac:(first [ clear - SP1 SLO NS1 STKc0; lia | lx_side_lia ])) as [STlo SThi].
  destruct (stk_carve asegs m0 lo (sp1 + 152) 152 STlo ltac:(first [ clear - SP1 SLO NS1 STKc0; lia | lx_side_lia ])) as [ST1 [jrs RSL]].
  replace (sp1 + 152 - Z.of_nat 152) with sp1 in RSL, ST1 by (clear; lia).
  apply (rw_cells_split_CB asegs m0 sp1 [] 152 jrs [] [24; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 16; 8]%nat) in RSL; [| reflexivity].
  cbn [mk_CB_cells app] in RSL.
  cb8_at RSL 1%nat.
  cb8_at RSL 2%nat.
  cb8_at RSL 3%nat.
  cb8_at RSL 4%nat.
  cb8_at RSL 5%nat.
  cb8_at RSL 6%nat.
  cb8_at RSL 7%nat.
  cb8_at RSL 8%nat.
  cb8_at RSL 9%nat.
  cb8_at RSL 10%nat.
  cb8_at RSL 11%nat.
  cb8_at RSL 12%nat.
  cb8_at RSL 13%nat.
  cb8_at RSL 15%nat.
  idtac "T-RSL".
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x53398] [] 848%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  try clear STJ.
  try clear STlo.
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      replace (Z_to_bv 64 340888 (* [comment removed for export] *)) with (Z_to_bv 64 (arl_smalloc R 3)) by (rewrite SM3; reflexivity).
      assert (LFB' : (length LF < 512)%nat) by (first [ clear - LFB; lia | lx_side_lia ]).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 3) with (lo := lo) (sz := 320); rewrite ?(unsigned_lit sp1) by exact SP1R;
                  first [ exact HHc | exact LFB' | reflexivity | exact TPV | exact LOS | exact ST1
                  | first [ clear - SLO SP1 TOP NS1 STKc0; lia | lx_side_lia ]
                  | clear; lia
                  | assumption | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "SMPRE-LEFT:" g end ])
      end.
      all: match goal with |- evtA _ _ _ _ _ => idtac | |- ?g => idtac "SMALLOC-LEFT:" g end.
      clear ST1.
      lazymatch goal with H : presA _ _ _ _ _ _ _ _ m1 ?m2 |- _ => rename H into HP1; rename m2 into m2' end.
      clear HH.
      presA_transport HP1. clear HP1.
      lazymatch goal with H : exists h' : HST _ _ _, _ |- _ =>
        destruct H as (h1 & Ehcs & Ehtop & Estk & Eflag & Evol & Efr & HKI & SMC) end.
      destruct SMC as (FB & junkf & Ea0 & F64 & FRSH & HH1 & FRM & FSH). lazymatch type of Ea0 with ?x = _ => subst x end.
      replace (Z.to_nat (8 * 2 ^ 3)) with 64%nat in FSH by reflexivity.
      replace (Z.to_nat (64 * 2 ^ 3)) with 512%nat in FRM by reflexivity.
      replace (64 * 2 ^ 3) with 512 in FRSH, HH1 by reflexivity.
      cbn [zcells] in FSH.
      idtac "T-SMALLOC".
      (* [comment removed for export] *)
      zstep. zstep.
      zstep. if_cases Kb; zify_cond Kb.
      2:{ exfalso. destruct FRSH as (F0 & F1 & _). try kland Kb.
          rewrite ?Z.mod_small in Kb by (first [ clear - F0 F1 ALO ACV LOS SLO SPR; lia | lx_side_lia ]). clear - Kb F0 F1 ALO ACV LOS SLO SPR. lia. }
      clear Kb.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      destruct (frame_factsA R HIA CS h1 LB LF m3 FB 512 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
        as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (512 / 8) with 64 in SBND, APS.
      pose proof (frame_apart_obj R HIA LB LF lo _ CRT 744 FB 512 FRSH CWX ltac:(clear; lia) ltac:(clear; lia) LOS) as APC.
      assert (APB : FB + 512 <= BUF \/ BUF + n <= FB) by (apply F3; apply in_app_iff; left; exact BIN).
      pose proof (art_stk_high asegs R HIA) as STKH.
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs m3 FB [] 512 junkf [] [8; 8; 8; 8; 472; 8]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      chunk_split FRM 3%nat FHD FRM1. chunk_split FRM1 1%nat FLNK FRM2. chunk_split FRM2 1%nat HLOC FREST.
      lazymatch type of HLOC with rw_cells _ _ ?a _ => replace a with (FB + 32) in HLOC by (clear; lia) end.
      clear FLNK FREST.
      cb8_to_c8 FHD (@nil cell).
      lazymatch type of FHD with rw_cells _ _ _ (?c1 :: _) => cb8_to_c8 FHD [c1] end.
      lazymatch type of FHD with rw_cells _ _ _ (?c1 :: ?c2 :: _) => cb8_to_c8 FHD [c1; c2] end.
      lazymatch goal with SSx : sshad _ _ m3 slo (bv_unsigned sp) |- _ =>
        destruct (sshad_split asegs AL m3 slo sp1 (bv_unsigned sp) SSx ltac:(first [ clear - SP1 SLO SLOL NS1 STKc0; lia | lx_side_lia ]) ltac:(first [ clear - SP1M; lia | lx_side_lia ])) as [SS1 SS2]; clear SSx end.
      idtac "T-FRAME".
      (* [comment removed for export] *)
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) =>
        lazymatch goal with HHc : HM _ _ _ h1 _ _ mc |- _ => pose proof (hm_abase asegs R HIA h1 _ _ mc HHc) as AB1 end end.
  (* [comment removed for export] *)
  idtac "S1P".
  lx_mkR. lxr_pose. try lxg_b8u.
  lx_pre. lx_run_tac (PLAN [0xa9414] [] 848%N). lx_tree. all: try (let f := fresh "lxh" in rename H into f).
  lxr_leaf. lx_carry.
  apply evtA_done. unfold S1P.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx end.
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [ first [ reflexivity | apply lx_MS_regs; apply mkR_eq31; first [ reflexivity | (f_equal; lia) | (apply bv_eq; rewrite ?Z_to_bv_unsigned; cbn; lia) ] ] | ]. spine; first [ eassumption | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "S1P-LEFT:" g end ].
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
