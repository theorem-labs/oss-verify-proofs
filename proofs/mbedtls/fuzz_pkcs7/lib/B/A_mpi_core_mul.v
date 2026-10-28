(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_core_mul.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT A_rt_facts A_mpi_core_mla.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import HeapIface.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX Require Import LxSum.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt LxAMpiTac LxAMpiSums.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0046c0b41cdef334 1 1 4 3 0 1 78 1 81 1 4 3 4 79 4 80 4 82 16P007866e4d584ce54 1 1 4 1 0 1 2 37 1 88 1P008a28fbb394e831 0 5 0 1 50 1 70 1 75 1 76 1P00a40a0a5570d59e 1 1 16 2 0 1 75 1 3 10 1 76 1 77 16P00d433d7cbc6918a 0 5 0 1 50 1 70 1 75 1 76 1P015710f747e5f6d1 0 5 0 1 50 1 70 1 75 1 76 1P01646049e5a662e8 0 5 0 1 74 1 82 1 89 1 90 1P019c92e9feeb4a80 0 7 0 4 10 4 29 16 41 16 72 16 82 4 83 4P01af9875cca8e912 2 51 1 1 4 3 3 1 79 1 80 1 6 0 1 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P02712fda4f221f7e 0 4 0 1 35 1 37 1 46 1P029c83fbac63a50b 0 5 0 1 50 1 70 1 75 1 76 1P02c4906eef83ed5e 0 5 0 1 53 1 73 1 78 1 79 1P030bae8999a30e8f 0 5 0 1 50 1 70 1 75 1 76 1P03a764ae5f5fea60 0 2 0 1 2 1P03bd79294320e5c9 0 5 0 1 73 1 81 1 88 1 89 1P04add5aca07e3b24 0 6 0 1 50 1 51 1 70 1 75 1 76 1P04cd9075ec9943b0 2 53 1 1 4 3 3 1 79 1 80 1 9 0 4 7 16 45 16 47 16 53 4 73 4 78 4 81 4 82 16 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P05d41dd616df7ccf 0 4 0 1 49 1 75 1 76 1P05eee091a4201b39 0 5 0 1 74 1 82 1 89 1 90 1P05f213061217d004 0 2 0 1 1 1P0600c150dacc233e 2 53 1 1 4 3 3 1 79 1 80 1 7 0 1 45 4 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 6 0 4 63 16 64 16 79 4 80 4 82 16P0660e1d6a921204d 2 52 1 1 4 3 3 1 79 1 80 1 6 0 1 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P0670c0cf99acf0ce 1 1 4 1 0 1 2 47 1 90 1P069235647c60504b 1 1 4 3 0 1 79 1 80 1 7 3 1 7 4 45 4 47 4 78 1 81 1 82 4P07af179b15c37f68 0 5 0 1 74 1 82 1 89 1 90 1P07d34830610da984 0 5 0 1 74 1 82 1 89 1 90 1P080ef836a5f399d4 2 53 1 1 4 3 3 1 79 1 80 1 7 0 1 45 4 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 6 0 4 63 16 64 16 79 4 80 4 82 16P0838cab9493117fc 0 4 0 1 37 4 45 4 69 4P0841dc99eb427898 0 4 0 16 12 16 88 16 89 16P08750f3667a7b4f2 0 2 0 1 45 1P092588ff4bb184f3 0 5 0 1 50 1 70 1 75 1 76 1P0a3606a71c542667 0 3 0 1 61 1 63 1P0af413cd7f7d05ef 1 1 4 3 1 1 91 1 92 1 5 2 4 48 16 90 4 93 4 94 16P0b587d00cdb90426 0 3 0 1 34 1 78 1P0b958a82566cf921 0 5 0 1 74 1 82 1 89 1 90 1P0bb7bbf8233bbaea 0 5 0 1 74 1 82 1 89 1 90 1P0bce68938e1287f5 0 5 0 1 50 1 70 1 75 1 76 1P0be9299fa2257a87 1 1 4 1 0 1 2 46 1 88 1P0c79d4d129dd8f23 1 1 4 1 0 1 2 44 1 75 1P0dd65b8cbf39a854 0 5 0 1 53 1 73 1 78 1 79 1P0e103827a2ca3140 0 5 0 1 50 1 70 1 75 1 76 1P0e84d57fbcb2af73 2 51 1 1 4 3 3 1 79 1 80 1 6 0 1 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P0e9539a0b6bec859 1 1 4 4 1 1 3 1 78 1 79 1 2 45 1 82 1P0eabe3d5aa828675 1 1 4 3 1 1 90 1 93 1 5 2 4 48 16 91 4 92 4 94 16P0ece9ed9e84cdb75 2 52 1 1 4 3 3 1 79 1 80 1 6 0 1 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P0f4a48d4b65a49e2 1 1 4 3 1 1 92 1 93 1 7 3 1 60 4 76 1 84 1 91 1 94 1 95 4P0f5018cc31a4266c 2 51 1 1 4 3 3 1 79 1 80 1 6 0 1 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P0f7f2f447393d322 0 4 0 1 49 1 75 1 76 1P103596f371608fdf 0 4 0 1 35 1 37 1 46 1P108fe34837e18fcd 1 1 4 3 1 1 77 1 80 1 4 2 1 78 1 79 1 81 4P10bb8dd8fa4d0d15 2 51 1 1 4 3 3 1 79 1 80 1 6 0 1 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P11d7acfaf07a711f 0 4 0 1 35 1 45 1 46 1P11ef8093f58515c8 0 5 0 1 50 1 70 1 75 1 76 1P11f1242b8f54cd8d 0 4 0 1 72 1 88 1 89 1P11f1596242a23e6a 0 3 0 1 37 4 46 4P125a53a025593970 0 5 0 1 53 1 73 1 78 1 79 1P1267169184b272bf 0 5 0 1 73 1 81 1 88 1 89 1P1297d99d9afc8d83 2 51 1 1 4 3 3 1 79 1 80 1 6 0 1 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P129d6cdd7d075292 0 4 0 1 49 1 75 1 76 1P12abf7936d528806 0 5 0 1 50 1 70 1 75 1 76 1P13191358aa05fe5c 2 53 1 1 4 3 3 1 79 1 80 1 9 0 4 7 16 45 16 47 16 53 4 73 4 78 4 81 4 82 16 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P132643ccf9b34486 0 4 0 1 49 1 75 1 76 1P13b24e11b7222596 0 5 0 1 74 1 82 1 89 1 90 1P1507f4468d91e4f3 2 51 1 1 4 3 3 1 79 1 80 1 6 0 1 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P1550de73581115f8 1 1 4 1 0 1 4 31 1 43 1 74 1 86 1P158591fc30805575 0 5 0 1 50 1 70 1 75 1 76 1P15d56308493dd13c 2 53 1 1 4 3 3 1 79 1 80 1 7 0 1 45 4 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 6 0 4 63 16 64 16 79 4 80 4 82 16P15efad0f1c9e74a1 1 1 4 3 0 1 92 1 93 1 6 3 1 41 4 48 4 91 1 94 1 95 4P16a622301d691991 0 4 0 1 49 1 75 1 76 1P16b33b08ab0a8c1a 0 2 0 1 1 1P16bd2d8fa72735f2 1 1 4 4 0 1 2 1 92 1 93 1 3 40 1 47 1 94 1P16c95942a956f282 2 53 1 1 4 3 3 1 79 1 80 1 7 0 1 45 4 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 6 0 4 63 16 64 16 79 4 80 4 82 16P1732f3fb1e44c2f7 1 1 4 1 0 1 2 43 1 86 1P175731448ab8bc20 0 6 0 1 50 1 51 1 70 1 75 1 76 1P1767fb6e77778c70 0 2 0 1 2 1P17bb24d1f85052c5 0 5 0 1 50 1 70 1 75 1 76 1P17ef4a45e9bd22d9 0 4 0 1 50 1 75 1 76 1P17ef622259518c3b 0 2 0 1 37 4P185262c4babeca3d 1 1 4 2 39 1 88 1 6 0 1 9 4 57 4 68 4 89 1 90 4P1860a52b937dc17b 0 5 0 1 50 1 70 1 75 1 76 1P18e41040b8aef9d8 1 1 4 1 0 1 2 45 1 85 1P1916220cd202d145 1 1 4 1 0 1 2 44 1 85 1P1917cf1ced9c91a8 1 1 4 3 1 1 78 1 79 1 4 2 4 77 4 80 4 81 16P194b461cfbe78655 0 5 0 1 37 4 38 4 45 4 58 4P196347e78b36555d 0 6 0 1 50 1 51 1 70 1 75 1 76 1P1a024fbeed51733e 0 2 0 1 2 1P1a362507f2fee65b 1 1 4 4 0 1 79 4 90 1 93 1 4 2 1 91 1 92 1 94 4P1a3826cc5d86c948 2 53 1 1 4 3 3 1 79 1 80 1 7 0 1 45 4 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 6 0 4 63 16 64 16 79 4 80 4 82 16P1a7457ab5a23e1ab 0 4 0 1 49 1 75 1 76 1P1ab12454d932f3e7 1 1 4 3 0 1 92 1 93 1 6 3 1 41 4 48 4 91 1 94 1 95 4P1b217be591f127e1 0 5 0 1 53 1 73 1 78 1 79 1P1b626fbde598a468 1 1 4 1 0 1 2 45 1 88 1P1b994e5939cddd2e 0 5 0 1 2 1 79 4 92 1 93 1P1bd2ed4d77c9e3c6 0 2 0 1 2 1P1c2f248395b2d379 2 52 1 1 4 3 3 1 79 1 80 1 6 0 1 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P1c37ec1732e90105 2 53 1 1 4 3 3 1 79 1 80 1 7 0 1 45 4 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 6 0 4 63 16 64 16 79 4 80 4 82 16P1c59ed564c17c6aa 0 2 0 1 44 1P1c6b1fc11d6c484c 0 3 0 1 61 1 63 1P1c913315570f4e81 0 2 0 1 62 1P1cc8a4d794e32f08 2 53 1 1 4 3 3 1 79 1 80 1 9 0 4 7 16 45 16 47 16 53 4 73 4 78 4 81 4 82 16 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P1cd8b9417453bb0a 1 1 4 3 0 1 91 1 94 1 4 3 4 92 4 93 4 95 16P1d285b31e11aaec5 1 1 4 3 0 1 79 1 80 1 7 3 1 7 4 45 4 47 4 78 1 81 1 82 4P1d9bbba46e5be5ce 1 1 4 1 0 1 2 2 1 75 1P1d9d1a4cc67f2cd8 2 51 1 1 4 3 3 1 79 1 80 1 6 0 1 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P1db6e045b6f2ae0c 0 5 0 1 53 1 73 1 78 1 79 1P1e599b03df1623b4 1 1 4 4 1 1 80 4 91 1 94 1 5 3 1 49 4 92 1 93 1 95 4P1f16d16fefb07dc0 0 5 0 1 50 1 70 1 75 1 76 1P2105a082b00bc87b 1 1 4 1 0 1 2 42 1 82 1P218a293b2011f124 0 5 0 1 74 1 82 1 89 1 90 1P21efb1af5c11145e 0 2 0 1 2 1P224081ae841322de 0 2 0 1 62 1P22441e07dc301270 2 53 1 1 4 3 3 1 79 1 80 1 9 0 4 7 16 45 16 47 16 53 4 73 4 78 4 81 4 82 16 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P22635bd5141028b0 2 52 1 1 4 3 3 1 79 1 80 1 6 0 1 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P22977464581665e2 0 2 0 1 41 4P2327808e442f197e 2 52 1 1 4 3 3 1 79 1 80 1 6 0 1 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P2364f2d433e49c2d 0 5 0 1 50 1 70 1 75 1 76 1P23fb70ac27ddcf70 0 2 0 1 51 1P243331d8658522f9 1 1 4 2 0 1 85 1 4 43 1 45 4 86 1 87 4P246b0f442e8d85aa 1 1 4 3 0 1 91 1 92 1 9 2 4 11 16 47 16 59 16 75 4 83 4 90 4 93 4 94 16P24c8f0741a91ae6f 1 1 4 4 1 1 80 4 92 1 93 1 6 3 1 76 1 84 1 91 1 94 1 95 4P2586a3109c1b4cbb 1 1 4 1 0 1 2 44 1 86 1P258a4a0abf969fb7 0 4 0 1 49 1 75 1 76 1P25b5a69e795ccaed 1 1 4 1 0 1 3 45 1 69 1 88 1P25f16300ccae30c8 1 1 4 1 0 1 2 44 1 86 1P26be3eeeee836040 1 1 4 3 1 1 78 1 81 1 4 3 1 79 1 80 1 82 4P2706dbb9a6353ad4 2 53 1 1 4 3 3 1 79 1 80 1 9 0 4 7 16 45 16 47 16 53 4 73 4 78 4 81 4 82 16 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P27c8ca52b2fc415f 0 4 0 1 49 1 75 1 76 1P28260ced0b55cdfa 0 5 0 1 50 1 70 1 75 1 76 1P282fe600640d86b2 1 1 4 3 1 1 78 1 81 1 4 3 1 79 1 80 1 82 4P283a457da2246b2a 0 2 0 1 37 1P284c32eb05d6dfaa 2 53 1 1 4 3 3 1 79 1 80 1 7 0 1 45 4 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 6 0 4 63 16 64 16 79 4 80 4 82 16P2867e3845d65a723 0 2 0 1 41 4P28a3dda2138a99da 1 1 4 4 1 1 78 4 91 1 94 1 5 3 1 49 4 92 1 93 1 95 4P28bc6f997cb9fb3d 2 53 1 1 4 3 3 1 79 1 80 1 9 0 4 7 16 45 16 47 16 53 4 73 4 78 4 81 4 82 16 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P28bf81b8cfbb2a01 0 5 0 1 53 1 73 1 78 1 79 1P28f70f32f52dad31 2 53 1 1 4 3 3 1 79 1 80 1 7 0 1 45 4 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 6 0 4 63 16 64 16 79 4 80 4 82 16P292e5042b24fded1 0 5 0 1 53 1 73 1 78 1 79 1P294310de1a097a9b 0 6 0 1 50 1 51 1 70 1 75 1 76 1P29f55f557dec9d11 1 1 4 4 1 1 78 4 92 1 93 1 6 3 1 76 1 84 1 91 1 94 1 95 4P29faca3a7a2ec3b6 0 2 0 1 1 1P2a1ab45dd2fa0fde 0 4 0 1 49 1 75 1 76 1P2a612fd34ebec289 1 1 4 6 0 1 2 1 11 4 59 4 92 1 93 1 2 70 1 94 1P2aa34aac2a1c6daf 1 1 4 2 41 1 88 1 4 0 1 77 4 89 1 90 4P2ab67c3fb8da600d 0 2 0 1 45 1P2b975fcaed12f829 0 3 0 1 37 4 46 4P2c00436dfd0717e8 2 51 1 1 4 3 3 1 79 1 80 1 6 0 1 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P2c6a56527e169222 1 1 4 2 0 1 82 1 4 40 1 42 4 83 1 84 4P2c9eaffc4218b014 0 4 1 1 3 1 78 1 79 1P2d18a3b4adeb0afd 0 4 0 1 37 4 45 4 69 4P2d869df7b702be3d 1 1 4 1 0 1 2 44 1 75 1P2ddb96531471426f 1 1 4 2 40 1 89 1 3 0 1 88 1 90 4P2dea3509e2ac2df0 0 5 0 1 73 1 81 1 88 1 89 1P2e1a194b62541128 0 5 0 1 53 1 73 1 78 1 79 1P2e5d7f4582b130f0 0 4 0 1 49 1 75 1 76 1P2ebf51385d233658 0 6 0 1 50 1 51 1 70 1 75 1 76 1P2ed6148f994b68b9 2 52 1 1 4 3 3 1 79 1 80 1 6 0 1 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P2f35b6828417f1b2 2 51 1 1 4 3 3 1 79 1 80 1 6 0 1 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P2f37493fb345403e 0 5 0 1 50 1 70 1 75 1 76 1P2f482c18b8ca3960 1 1 4 3 0 1 91 1 94 1 4 3 4 92 4 93 4 95 16P2f61938444c990a9 2 52 1 1 4 3 3 1 79 1 80 1 6 0 1 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P2f681624a2fd7cdb 0 2 0 1 45 1P2fbbce56d1fa5f4b 1 1 4 3 1 1 91 1 92 1 4 2 4 90 4 93 4 94 16P2fe70f3130fa4d3c 1 1 16 2 74 1 75 1 3 0 1 76 1 77 16P303f0eba10ecbb5a 0 6 0 1 50 1 51 1 70 1 75 1 76 1P3093d55543581743 1 1 4 1 0 1 2 46 1 77 1P30c31ca8b00fd31d 0 5 0 1 74 1 82 1 89 1 90 1P3146b3fe76dbf9a5 0 5 0 1 50 1 70 1 75 1 76 1P316ca82bf21f32aa 0 2 0 1 62 1P31a88c9b117a50ed 1 1 4 3 1 1 91 1 92 1 4 2 4 90 4 93 4 94 16P31dab3b6aa45bfdf 0 4 0 1 49 1 75 1 76 1P32447d74fb9193c8 0 2 0 1 45 1P324546ecb7d672f7 0 6 0 1 50 1 51 1 70 1 75 1 76 1P32bfebec2daf2200 0 5 0 1 50 1 70 1 75 1 76 1P32d00b817802b36b 0 4 1 1 3 1 78 1 79 1P3307165592c81079 1 1 4 1 0 1 2 45 1 75 1P33936c85291357e2 1 1 4 6 0 1 2 1 6 4 44 4 79 1 80 1 2 46 1 81 1P33f17e5f4ead31b6 0 2 0 1 51 1P33f6bf90a01c1432 0 6 0 1 50 1 51 1 70 1 75 1 76 1P340c6470bebee7d9 2 53 1 1 4 3 3 1 79 1 80 1 9 0 4 7 16 45 16 47 16 53 4 73 4 78 4 81 4 82 16 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P340cf46b64c21b8a 0 2 0 1 37 1P340e79b8a05ac4bd 1 1 4 3 1 1 91 1 92 1 7 2 1 11 4 59 4 70 4 90 1 93 1 94 4P34b1be15fb7ac69c 1 1 4 3 0 1 78 1 81 1 6 3 4 63 16 64 16 79 4 80 4 82 16P357c23bf5544cd58 0 5 0 1 53 1 73 1 78 1 79 1P358bb5c2e61647f8 2 52 1 1 4 3 3 1 79 1 80 1 6 0 1 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P35da76bc3816f292 1 1 4 1 0 1 2 42 1 82 1P36080f225177c3d1 0 5 0 1 73 1 81 1 88 1 89 1P36d6ec9818004dc4 1 1 4 1 0 1 2 45 1 88 1P386c3751f2c45b26 1 1 4 3 0 1 78 1 79 1 9 2 4 6 16 44 16 46 16 52 4 72 4 77 4 80 4 81 16P38e1635fa52d031e 1 1 4 2 2 1 91 1 3 1 1 90 1 92 4P39e1a71228a36c28 0 6 0 1 50 1 51 1 70 1 75 1 76 1P3a5de3107a989dcf 1 1 4 1 0 1 2 46 1 88 1P3a63712facdd0544 0 5 0 1 74 1 82 1 89 1 90 1P3b60b7e4ae3620b6 1 1 4 1 0 1 2 44 1 75 1P3b8033acc2fb66d0 2 52 1 1 4 3 3 1 79 1 80 1 6 0 1 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P3b8552c3938b37c3 1 1 4 3 0 1 91 1 94 1 6 3 4 39 16 40 16 92 4 93 4 95 16P3c7979ab85ccdbdb 0 3 0 1 44 1 59 1P3c89e57e16e9c40a 2 53 1 1 4 3 3 1 79 1 80 1 9 0 4 7 16 45 16 47 16 53 4 73 4 78 4 81 4 82 16 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P3cbafb391d502d4a 1 1 4 3 0 1 78 1 81 1 4 3 4 79 4 80 4 82 16P3cbdedde8e758202 0 3 0 1 35 1 36 1P3cd83733d4bbe8be 2 53 1 1 4 3 3 1 79 1 80 1 9 0 4 7 16 45 16 47 16 53 4 73 4 78 4 81 4 82 16 1 1 4 3 2 1 78 1 81 1 4 0 1 79 1 80 1 82 4P3d69394a86f662b5 0 5 0 1 37 4 45 4 46 4 69 4P3d7cc5023f7e39e8 0 5 0 1 50 1 70 1 75 1 76 1P3de5501c7b8048a1 1 1 4 1 0 1 2 45 1 88 1P3e3b2a10e420d2ca 0 5 0 1 53 1 73 1 78 1 79 1P3e3e9e13f33ecc26 0 5 0 1 50 1 70 1 75 1 76 1P3e5dabeb78602210 1 1 16 2 0 1 88 1 3 13 1 89 1 90 16P3ee7ced90d8dd5f5 0 6 0 1 73 1 74 1 81 1 88 1 89 1P3f096e67083a031b 2 53 1 1 4 3 3 1 79 1 80 1 7 0 1 45 4 53 1 73 1 78 1 81 1 82 4 1 1 4 3 2 1 78 1 81 1 6 0 4 63 16 64 16 79 4 80 4 82 16P3ff60983b6c9dfe4 1 1 4 1 0 1 2 46 1 88 1N0009fd2728fc0f8dN000cb050051f3950N00dcdc3bde627003N0122ea87e6e6386aN0152aa567b66b213N01a650e5f9bddf5aN024558ba9945dd01N02694d31cc4562ceN026fed99efa4246bN02b4c30de3edc2f5N02d1e8f38525e5c6N02fe623c5f7d845cN0314cc430ce71ffaN032f5dd9b69dd683N03f5c2a0d23fabd6N044a982f5159d98eN044d584006aa701bN049efd655e270a9dN04eb112b915db583N05c3fb033836dc5fN0602cf8a0cf4eb1dN077cc39e90f176a2N0788fb9f9f1f8bddN07afd889c64d34f5N07b9a09e7971cb2cN07d622e54ed2b03fN07e35e18d03082b3N07e93468ffb77457N080b0633f749c249N080c894835627fd5N08107f92c69f0feeN082b64c58c075a2cN087476848ab28105N08ec5ef37b333b6dN09118fb967b0f102N0993c7cf5460f989N09ce4377a6c0a238N09e975aa4c655badN0a7c0e6b31746287N0b402358b076a3d0N0b996aeb5b841793N0ba435190a4ba1a0N0beb91475dc9de4fN0bf9465697941717N0c2cb7d0bce927e4N0c7ae38063ff1f1cN0cb57dc5961476ccN0cd45313d9365efdN0dcd8abe18f2ecacN0e782b6632cbd68bN0fbe6bb14703f742N0fecf9c9c6f43180N10342a5dddfa9a42N10920fc6ca4fda72N12a3445a04ab0171N12bf2c6fcaff11baN1361005ef216815bN13f721177d841ae1N14341aeddaad04aaN1438ef5e7eee8ebbN147a5dbaefe0ab68N157a4d0a5d41f1bcN1629ad91fe97df98N171ebf1e630c877fN174196e3b0b7fdaaN174349dde95c8bbdN17d43b958d6fff68N17ee24b61c294d0aN18c033011f89679fN195c6f67855621daN1b05e974087fa6a0N1b3467ebfc3f6d57N1b542983ba84b217N1bc0935b60740cf2N1c844be9f62093f0N1d7264e751332f51N1d74bea40dfa9171N1d7b2c2ac9370fdbN1e2e2647d05d338fN1e7dc4b2b617dfb6N1e967697a0066c03N1ec104cbbf3805beN1ee0bcf509fe23b3N1fc81fc82335c47dN202bae59edcf0c37N208ce7750da6e7caN210bb5ad501a5cabN21a687c3365bfc79N22511573111dd2d5N2255d065fa23ec53N22a35050c91aba54N22abd07225b0b4a1N22bfca583c469c47N22c11313876262c7N22c59b1adae78dd3N22ce7bdc52415724N23b66fea0c2da556N244479e8f7876a30N2486c71bb3c4dd4fN24ff06712b258b1fN2504de364531f469N250ba170b077ef62N2517fc2a3d03713bN255c6bc43cb4313cN2567c1bd93678192N25a7429f5f40e4a7N26931efdf585fe36N26a04a36f6f311b1N26b45bb64e515ec5N274cdcbebc7f6da6N27d3cf4be4129319N280b642157b3f3c3N281dff10e1462b3bN285800f8fa778a8bN289c3e641cfb0c51N2932a77c007fa816N29c5c3d95c9d0b3cN2a1c42de7c18cef0N2a4a112f48555a7fN2ab453fb9a959339N2ab97fc9f9826eeeN2afcfca4191c39adN2be2f799f37843d1N2c0f8367950f93f5N2c5a51c2614364ffN2cfbd084aebb0dc6N2d39324a7eef2076N2e6d178ccb59ac94N2e856f13df323c08N2f17017f9b131ff5N2f5efbc7b8a110cbN3035a59ca542791fN305435651d9862e1N30e4781fdff2df5eN31455c7970bb0a7fN318d18eb9766079eN31b9528907763b10N31c6731c55e70558N32162fe2e9242cadN3286020cd4ca21d2N328f18973a84db99N32f629706e8d3427N33a941b12e6cc5bdN34815d549f8dab8dN3500c02a683cf036N354caf1b17015e0bN35c69a3be47abd0bN35d8317da16c08faN35f2fa3efe15dfbeN36240e44666d46fbN365746a6d47d3505N366ef32884cece20N3682857f65da3b7bN3703d1a438b746a6N375319540d18928cN375db221711bbaeeN3778c784b44feff3N38349196cc25a0e6N38c6be3392300675N396559da19c3b267N3995b3cefc234ce1N3a1e191e22c58466N3a350f168d75f308N3a64532e738b5847N3b3c7fdd9df06540N3be3dba69e4f8078N3c1be186512ab132N3d300d678156eafbN3d5ee976231b0df4N3e0545e6e459bb81N3ecab23f6211f76eN3ecfb1e55648ed3eN3ed0588a02287c1fN3f7d53b67f8f3d9fN3fa2a77cd5d6e0e3N3fc611f16cdc7edbN3fef3038acf41df7N3ffc8aa576989079"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
Ltac2 gd_tbl_A_mpi_core_mul () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_stklo"; "Stdlib.ZArith.BinInt.Z.sub"; "MPI_CORE_MUL_STACK_A"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_need_amem"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.client_wrange"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_L"; "Corelib.Init.Datatypes.app"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fdata"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "mpi_core_mul_postA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.art_layout"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.artA"; "RocqVerifyHarness.AgentSubmission.B.AImg.asan_img_ok"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_amemset"; "A_ASAN_MEMSET"; "mpi_core_mul_stmtA"; "A_MPI_CORE_MUL"].


Definition A_MPI_CORE_MUL : Z := 0xa52a8.
Definition A_ASAN_MEMSET : Z := 0x68258.
(* [comment removed for export] *)
Definition MPI_CORE_MUL_STACK_A : Z := 240.

Definition mpi_core_mul_postA (segs : list Segment) (R : art_layout) (HIA : artA segs R)
    (h : HST segs R HIA) (LB LF : list blk)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X n : Z) (xs : list word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_mul ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Lxs',(4.(2.&40.))(5.(6.$0.R12.(7.(8.O17.O16.O15.O14.R11.R10.R?.O13.O12.R>.R=.R<.R;.R:.R9.R8.R7.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.R6.R5.R4.R3.)O7.(9.O17.)O6.(:.(2.&40.))R2.(;.O1=.)))(5.(<.(=.(>.$?.$?.)(10.$?.$?.O5.(11.O5.(12.+4.O4.)))(=.(>.$?.$?.)(10.$?.$?.O2.(13.&40.O16.))(14.(>.$?.$?.))))O1.R2.)(5.(15.O1=.O1.R2.)(5.(16.O1=.R2.)(5.(17.O1=.R2.O5.R1.)(5.(6.$18.(19.(2.&40.)R1.)(19.(2.&40.)O3.))(5.(6.(4.(2.&40.))(1:.(2.&40.)(1;.O4.)R1.)(1:.(2.&40.)(1;.O4.)O3.))(5.(1<.O1=.R2.O2.(13.&40.O16.))(1=.O1=.O1<.O1;.O1:.O19.O18.R2.))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_mul_stmtA (segs : list Segment) (R : art_layout) (HIA : artA segs R) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_mul ()) "Ph,(1>.O4.O3.O2.)PLB,(4.$1?.)PLF,(4.$1?.)Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(20.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PX,$?.PA,$?.Pan,$?.PB,$?.Pbn,$?.Plo,$?.Pxs,(4.(2.&40.))Pys,(4.(2.&40.))Pzs,(4.(2.&40.))P,(1=.O4.O3.O2.R2>.R2=.R2<.R:.)P,(17.O4.R;.R:.R4.)P,(21.O4.R<.R:.(22.R4.))P,(21.O4.R=.R9.(22.R4.))P,(23.=R;.)P,(23.=R:.)P,(23.(11.R=.R;.)+2710.)P,(23.(11.R>.R<.)(24.(19.(2.&40.)R:.)))P,(23.R?.(24.(19.(2.&40.)R:.)))P,(23.R>.(24.(19.(2.&40.)R:.)))P,(25.(23.(11.R12.(12.+4.(24.(19.(2.&40.)R<.))))R13.)(23.(11.R13.(12.+4.(24.(19.(2.&40.)R=.))))R12.))P,(25.(23.(11.R11.(12.+4.(24.(19.(2.&40.)R<.))))R14.)(23.(11.R14.(12.+4.(24.(19.(2.&40.)R>.))))R11.))P,(6.$?.(26.R15.+4.)=)P,(6.$?.(26.R15.+4.)=)P,(6.$?.(26.R14.+4.)=)P,(27.=R18.)P,(25.(6.$?.R17.=)(27.=R18.))P,(25.(6.$?.R16.=)(27.=R17.))P,(27.(11.R1;.(12.+4.(24.(19.(2.&40.)R15.))))(28.+2.+40.))P,(27.(11.R1;.(12.+4.(24.(19.(2.&40.)R15.))))(28.+2.+40.))P,(27.(11.R1:.(12.+4.(24.(19.(2.&40.)R15.))))(28.+2.+40.))P,(1<.O4.R1?.R19.(13.&40.R3?.))P,(23.(29.O3.)R1:.)P,(23.R1;.(2:.(2:.(13.&40.R41.)$2;.)(2<.O3.)))P,(23.(13.&40.R42.)(2=.O4.O3.O2.R46.))P,(6.$?.(26.(13.&40.R43.)+10.)=)P,(25.(23.(11.R23.(12.+4.(24.(19.(2.&40.)R1=.))))R1>.)(23.(13.&40.R44.)R23.))P,(25.(23.(11.R23.(12.+4.(24.(19.(2.&40.)R1=.))))R1?.)(23.(13.&40.R45.)R23.))P,(25.(23.(11.R22.(12.+4.(24.(19.(2.&40.)R1=.))))R20.)(23.(13.&40.R46.)R22.))P,(2>.(2?.O3.)(30.$1?.R4:.(31.R49.))(29.O3.)(2=.O4.O3.O2.R4;.)R26.(12.+4.(11.R24.R22.)))P,(16.O4.R28.)P,(6.$?.(26.(13.&40.R4:.)+2.)=)P,(32.O4.(33.O3.)(34.O4.O3.O2.R4>.)R2:.R29.(12.+4.(11.R27.R25.)))P,(32.O4.(33.O3.)(34.O4.O3.O2.R4?.)R2;.R29.(12.+4.R28.))P,(32.O4.(33.O3.)(34.O4.O3.O2.R50.)R2<.R28.(12.+4.R27.))P,(6.(2.&40.)R45.(35.&40.R2<.))P,(6.(2.&40.)R45.(35.&40.R2<.))P,(6.(2.&40.)R45.(35.&40.R2<.))P,(6.(2.&40.)R45.(35.&40.R2<.))P,(6.(2.&40.)R45.(35.&40.R2<.))(36.O4.(33.O3.)(34.O4.O3.O2.R56.)(37.O4.O3.O2.R56.R55.R54.R53.R52.R51.R50.R4<.R4;.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R34.R33.R31.(11.R2?.R2=.)R2;.R2<.R32.)(7.(8.R53.R52.R51.R50.R4?.R4>.R4=.R4<.R4;.R4:.R49.R48.R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.)R34.(35.&40.O1.)R33.(:.(2.&40.))R32.(;.O4.)))")
(* [comment removed for export] *).

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.
  Hypothesis AMS : arl_amemset R = A_ASAN_MEMSET.
  Hypothesis NEED0 : 0 <= arl_need_amem R.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X A an B bn lx la lb lo : Z) (xs0 ys zs : list word).
  Hypothesis Han : 0 <= an /\ 0 <= bn /\ an + bn <= 10000.
  Hypothesis Ln : an + bn <= lx /\ an <= la /\ bn <= lb.
  Hypothesis L0 : Z.of_nat (length xs0) = lx.
  Hypothesis LA : Z.of_nat (length ys) = la.
  Hypothesis LB' : Z.of_nat (length zs) = lb.
  Hypothesis DA : A + 4 * la <= X \/ X + 4 * lx <= A.
  Hypothesis DB : B + 4 * lb <= X \/ X + 4 * lx <= B.
  Hypothesis XB : 0 < X /\ X + 4 * lx < 2^64.
  Hypothesis AB : 0 <= A /\ A + 4 * la < 2^64.
  Hypothesis BB : 0 <= B /\ B + 4 * lb < 2^64.
  Hypothesis NZA : an = 0 \/ 0 < A.
  Hypothesis NZB : bn = 0 \/ 0 < B.
  Hypothesis ALX : X mod 4 = 0.
  Hypothesis ALA : A mod 4 = 0.
  Hypothesis ALB : B mod 4 = 0.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis LOS : arl_stklo R <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - 240 - arl_need_amem R.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SX : X + 4 * lx <= lo \/ bv_unsigned sp <= X.
  Hypothesis SA : A + 4 * la <= lo \/ bv_unsigned sp <= A.
  Hypothesis SBB : B + 4 * lb <= lo \/ bv_unsigned sp <= B.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis CWX : client_wrange L (LB ++ fdata LF) (arl_stklo R) (htop asegs R HIA h) X (4 * (an + bn)).
  Hypothesis HA0 : bytes_at asegs m A (u32s ys).
  Hypothesis HB0 : bytes_at asegs m B (u32s zs).

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof alloc_ceiling_pos as ACP;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR'; unfold bv_modulus in SPR'; cbn [Z.pow Z.of_N Pos.pow] in SPR';
    match goal with HH : HM _ _ _ h LB LF _ |- _ =>
      pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP;
      assert (LO0 : 0 <= lo) by (clear - LOS ALO ACP; klia);
      assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; klia| clear - TOP HTOP; klia])
    end.

  Notation POST := (mpi_core_mul_postA asegs R HIA h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X (an + bn) xs0 lo m).
  Notation W := [(X, X + 4 * (an + bn)); (lo, bv_unsigned sp)].
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -128)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation FRAME mm := (rw_cells asegs mm (bv_unsigned sp + -128) [C8 SB; C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 an); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  (* [comment removed for export] *)
  Notation DINV mm xs := (u32arr asegs mm X xs /\ Z.of_nat (length xs) = an + bn
                          /\ u32arr asegs mm (X + 4 * (an + bn)) (skipn (Z.to_nat (an + bn)) xs0)
                          /\ munch W m mm /\ wmono asegs m mm /\ mem_inv asegs mm /\ stk asegs mm lo (bv_unsigned sp + -128)
                          /\ HM asegs R HIA h LB LF mm).
  Notation SUMS := [SUM_amemsetWA 4 5; SUM_mlawA 4].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00P0@D30427090302.120D5485600298.120 D563007111.121  D62022258533.121L10264762537.6  L18575562516.121L18576006449.69 L18576006449.71 L19145947143.78 L19786351046.79 L19990126689.9  L20904623524.4  L27049754983.6  L29428324939.5  L29431152682.2  L32619083732.71 L32619083732.72 L35653441506.7  L38607101113.2  L47252709405.5  L51209618996.122L51211784070.69 L51211784070.71 L57144356162.3  L59895784800.7  L60098763854.3  L63134936305.6  L63141749551.4  L67039502374.121L67040867990.63 L8787000245.78  L8918007599.5   00000W01>01m02V02n04U04V04W04\04b05D05Q05i06;06<06=06>06V06]06k08S08T08U08^09809B09Z09[0:h0:i0:n0;8S2ra2sp1X1A2an1B2bn3xs02ys2zs1k1i2xs2HkS2ra2sp1X1A2an1B2bn3xs02ys2zs1k1i2xs2HkS1R3HIA1h2ra2sp1X1A2an1B2bn3xs02ys2zs1k1i2xs2HkS1R2ra2sp1X1A2an1B2bn3xs02ys2zs1k1i2xs2HkS2an2bn2xs2LX3lxl6LXlen2S1R5NEED02ra2sp1X1A2an1B2bn2lx2la2lb2lo3xs02ys2zs2Ln2L02LA2DA2DB2XB2AB2BB3SPR2LO2SX2SA3SBB1k1i2xs2Hk2HiFFS1X1iS2bn1iS2an2bn2lx3xs02xs2LX2LT3lxl6LXlen2S2bn1i2Hi3H13S2an2bn2xs2LX3lxl6LXlen2S1R2lo3LOS3ALO3ACPFFFS1R3HIA1h2sp2lo3TOP4HTOPS2an2bnS2bn1k1i2Hk2HiS1R5NEED02ra2sp1X1A2an1B2bn2lx2la2lb2lo3xs02ys2zs2Ln2L03LB'2DA2DB2XB2AB2BB3SPR2LO2SX2SA3SBB1k1i2xs2Hk2HiFFS1X2an2bnS1X2an2bn2xs2LX3lxl6LXlen2S1R2lo3LOSS2an2bn2xs2LX3lxl6LXlen2FS2ra2sp1X1A2an1B2bn2lx2la2lb3xs02ys2zs3Han2Ln2L02XB2AB2BB3SPR1k1i2xs2Hk2Hi2LXFS1B1iS1A2an3NZA". (* [comment removed for export] *)
  Lemma loop_walk : forall (k : nat) (i : Z) (xs : list word) (mm : mem)
      (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 wpb wpx wi : word),
      Z.to_nat (bn - i) = k -> 0 <= i < bn ->
      wpb = Z_to_bv 64 (B + 4 * i) -> wpx = Z_to_bv 64 (X + 4 * i) -> wi = Z_to_bv 64 i ->
      DINV mm xs -> FRAME mm ->
      aobj asegs AL CS mm X (4 * (an + bn)) -> aobj asegs AL CS mm A (4 * an) -> aobj asegs AL CS mm B (4 * bn) ->
      evtA asegs AL CS POST
        (MS (mkR xra SP' gp tp xt0 xt1 xt2 (Z_to_bv 64 B) wpb xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                 (Z_to_bv 64 bn) (Z_to_bv 64 1) wpx (Z_to_bv 64 (an + 1)) wpb wpx (Z_to_bv 64 X) wi
                 (Z_to_bv 64 1) (Z_to_bv 64 1) xt3 xt4 xt5 xt6)
            F (Z_to_bv 64 0xa5350) fc None mm (seg_rom asegs))
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros i xs mm xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 wpb wpx wi Hk Hi Epb Epx Ei
      (HX & LX & HT & MU & WM & MI & ST & HH) FR OX OA OB; [klia|]. rt_facts.
    pose proof (u32ro_transport _ _ _ _ _ _ HB0 MU ltac:(cbn [disjoint_from]; rewrite LB'; klia)) as HB.
    pose proof (u32ro_transport _ _ _ _ _ _ HA0 MU ltac:(cbn [disjoint_from]; rewrite LA; klia)) as HA.
    assert (LT : Z.of_nat (length (skipn (Z.to_nat (an + bn)) xs0)) = lx - (an + bn)) by (rewrite skipn_length; klia).
    assert (NZA' : an <= 0 \/ 1 <= A) by (clear - NZA Han; lia).
    assert (BPOS : 1 <= B) by (clear - NZB Hi; lia).
    pose proof (hm_abase asegs R HIA h LB LF mm HH) as ABm.
    subst wpb wpx wi.
    (* [comment removed for export] *)
    lx_pre. lxr_pose. lxm_sums [SUM_amemsetWA 4 5; SUM_mlawA 4] [X; an + bn].
    lx_pre. lx_run_tac (PLANS [0xa5350] [(0xa5388, DJoin)] 70%N [SUM_amemsetWA 4 5; SUM_mlawA 4]). lx_tree.
    all: lxr_leaf.
    all: match goal with K : aobj asegs AL CS ?mx X ?n |- _ => replace n with (4 * (an + bn)) in K by (clear; lia) end.
    all: match goal with K : u32arr asegs ?mx (X + ?d) _ |- context [MS _ _ _ _ _ ?mx _] => replace (X + d) with (X + 4 * (an + bn)) in K by (clear; lia) end.
    all: match goal with K : munch [(X, X + ?d); _] m ?mx |- _ => replace (X + d) with (X + 4 * (an + bn)) in K by (clear; lia) end.
    - (* [comment removed for export] *)
      match goal with K : u32arr asegs ?mx X ?l, KL : Z.of_nat (length ?l) = _, BR : 0 <= bn + _ |- context [MS _ _ _ _ _ ?mx _] =>
        eapply (IH (i + 1) l); [ clear - Hk Hi; klia | clear - Hi BR; klia | f_equal; klia | f_equal; klia | f_equal; klia
                               | split; [exact K|]; split; [clear - KL LX; klia| split; [eassumption | split; [eassumption | split; [eassumption| split; [eassumption| split; [eassumption|eassumption]]]]]]
                               | eassumption | eassumption | eassumption | eassumption ] end.
    - (* [comment removed for export] *)
      match goal with K : u32arr asegs ?mx X ?l, K2 : u32arr asegs ?mx (X + ?d) ?t, KL : Z.of_nat (length ?l) = _ |- context [MS _ _ _ _ _ ?mx _] =>
        assert (HXF : u32arr asegs mx X (l ++ t)) by (apply u32arr_app; split; [exact K | replace (X + 4 * Z.of_nat (length l)) with (X + d) by (clear - KL LX; lia); exact K2]);
        assert (LXF : Z.of_nat (length (l ++ t)) = lx) by (rewrite app_length; clear - KL LX LT; lia);
        assert (SKF : skipn (Z.to_nat (an + bn)) (l ++ t) = skipn (Z.to_nat (an + bn)) xs0) by (rewrite skipn_app; replace (Z.to_nat (an + bn) - length l)%nat with 0%nat by (clear - KL LX; lia); rewrite skipn_all2 by (clear - KL LX; lia); reflexivity);
        clear K K2 end.
      lx_post; [> exact HXF | rewrite <- (Nat2Z.id (length _)), LXF, <- L0, Nat2Z.id; reflexivity | exact SKF | .. ].
    all: match goal with |- ?g => idtac "LOOP-LEFT:" g end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Local Ltac2 Set LiaOrc.tbl := fun () => "00\0@D30427090173.107D5485600681.107 D563007111.108  D62022258533.108L10264762537.6  L19633509530.3  L21516708649.65 L27049754983.6  L28131301963.146L28131301963.150L28131804941.64 L29308029871.146L29308029871.150L29308606185.65 L29428551881.90 L29429056688.45 L31138385959.67 L3233760397.67  L35668187074.59 L37439666136.7  L37456714203.65 L40374333670.104L42755647107.49 L43059679021.102L43287214712.67 L47283676745.63 L48381404225.65 L50639571839.50 L50953998301.75 L52516413313.7  L56527057692.67 L5700290288.144 L5700290288.150 L5700803510.64  L57144356162.3  L59904179906.5  L60098763883.54 L60291650033.65 L62074012967.144L62074012967.150L62074109372.65 L63134936305.6  L63141749551.4  L63188864469.64 00000P01001X02:02R02[02c03;03<03=03>03?03@03A04604704C04O04k05E05M05m06B07H07[07_07c08308M08h09509609709809A09P09Z09]09^09_09`0:80:90:<S2ra2sp1X1A2an1B2bn2xs2ys2zs3SPRS2ra2sp1X1A2an1B2bn2xs2ys2zs3SPRS1R3HIA1h2ra2sp1X1A2an1B2bn2xs2ys2zs3SPRS1R2ra2sp1X1A2an1B2bn2xs2ys2zs3SPRS2an2bn2xs2LP3lxl6LXlen2S1X2an2bnS2bn3H12S2an2bn2xs2LP3lxl6LXlen2FFFFFFS1R2ra2sp1X1A1B2lo2xs2ys2zs3NZX3LOS3ALO3ACP2AB2BB3SPRFS1B2zs2BT2BBS1A2ys2AT2ABS1R3HIA1h2sp2lo3TOP4HTOP3SPRS1X2an2bn2xs2LP3lxl6LXlen2S2bn3H12S2ra2sp1X1A2an1B2bn2xs2ys2zs3SPRS2an2bn2xs3Han3Hbn2LXS1R5NEED02ra2sp1X1A2an1B2bn2lo2xs2ys2zs3NZX3NZA3NZB2LO2AB2BB3SPR2LP2LTS2an2bn3Han3Hbn3HabS2xsS2bnS2an2bn2xs2LX2LPS2an2bn2xs2ys2zs2LX2LA3LBzS2an2bn2xs2LP2LT3lxl6LXlen2S1X2xs3NZX2XTFFFS1X2an2bnS1X2an2bn2xs2LPS1R2lo3LOSS1XFFFS2an2bn2xs2LP3lxl6LXlen2FS1B". (* [comment removed for export] *)
Lemma A_mpi_core_mul_spec : ltac2:(CDefT.buildp (gd_tbl_A_mpi_core_mul ()) "PR,$3>.PHIA,(3?.$38.R1.)P,(40.(33.R2.))P,(6.$?.(41.R3.)$42.)P,(23.=(2<.R4.))(43.$38.R5.R4.$44.)")
(* [comment removed for export] *).
Proof.
  intros R HIA IMG AMS NEED0. unfold mpi_core_mul_stmtA, A_MPI_CORE_MUL.
  intros until zs. intros HH HX HA HB Han Hbn Hab LX LA LBz DA DB ALX ALA ALB NZX NZA NZB XT AT BT ST LOS LO TOP SPA SX SA SB CWX MI RA OX OA OB -> -> -> -> ->.
  unfold MPI_CORE_MUL_STACK_A in *.
  pose (lxi := lxA_img (arl_AL R) IMG).
  pose proof (hcs_ok asegs R HIA h) as CSOK. pose proof (cs_ok_sb _ _ CSOK) as SB64.
  pose proof (art_alwf asegs R HIA) as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
  pose proof (art_lo asegs R HIA) as ALO. pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP.
  pose proof (hcs_stack asegs R HIA h) as SCS0. pose proof (hm_top asegs R HIA h LB LF m HH) as HTOP.
  pose proof (u32arr_bound _ _ _ _ HX) as XB. pose proof (u32ro_bound _ _ _ _ HA) as AB. pose proof (u32ro_bound _ _ _ _ HB) as BB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (LO0 : 0 <= lo) by klia.
  assert (SCS : crange (hcs asegs R HIA h) lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| klia| klia]).
  pose proof (munch_refl [(X, X + 4 * (an + bn)); (lo, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (hm_abase asegs R HIA h LB LF m HH) as ABS.
  (* [comment removed for export] *)
  pose proof (firstn_skipn (Z.to_nat (an + bn)) xs) as EY. symmetry in EY.
  assert (LP : Z.of_nat (length (firstn (Z.to_nat (an + bn)) xs)) = an + bn) by (rewrite length_firstn; klia).
  rewrite EY in HX. apply u32arr_app in HX. destruct HX as [HXB HXC].
  replace (X + 4 * Z.of_nat (length (firstn (Z.to_nat (an + bn)) xs))) with (X + 4 * (an + bn)) in HXC by (clear - LP; lia).
  assert (LT : Z.of_nat (length (skipn (Z.to_nat (an + bn)) xs)) = Z.of_nat (length xs) - (an + bn)) by (rewrite skipn_length; klia).
  clear EY.
  carve_frame 128%nat ST.
  destruct (Z_le_gt_dec bn 0) as [BN0 | BN0]; [|assert (BN1 : 0 < bn) by (clear - BN0; lia); assert (BPOS : 1 <= B) by (clear - NZB BN0; lia); clear BN0].
  (* [comment removed for export] *)
  all: lx_pre; lxr_pose; lxm_sums [SUM_amemsetWA 4 5; SUM_mlawA 4] [X; an + bn].
  all: lx_pre; lx_run_tac (PLANS [0xa5350] [] 60%N [SUM_amemsetWA 4 5; SUM_mlawA 4]); lx_tree.
  all: lxr_leaf.
  - (* [comment removed for export] *)
    match goal with K : u32arr asegs ?mx X ?l, K2 : u32arr asegs ?mx (X + ?d) ?t, KL : Z.of_nat (length ?l) = _ |- context [MS _ _ _ _ _ ?mx _] =>
      assert (HXF : u32arr asegs mx X (l ++ t)) by (apply u32arr_app; split; [exact K | replace (X + 4 * Z.of_nat (length l)) with (X + d) by (clear - KL LP; lia); exact K2]);
      assert (LXF : length (l ++ t) = length xs) by (rewrite app_length; clear - KL LP LT; lia);
      assert (SKF : skipn (Z.to_nat (an + bn)) (l ++ t) = skipn (Z.to_nat (an + bn)) xs) by (rewrite skipn_app; replace (Z.to_nat (an + bn) - length l)%nat with 0%nat by (clear - KL LP; lia); rewrite skipn_all2 by (clear - KL LP; lia); reflexivity);
      clear K K2 end.
    match goal with K : munch [(X, X + ?d); _] m ?mx |- _ => replace (X + d) with (X + 4 * (an + bn)) in K by (clear; lia) end.
    lx_post; [> exact HXF | exact LXF | exact SKF | .. ].
    all: match goal with |- ?g => idtac "RET-LEFT:" g end.
  - (* [comment removed for export] *)
    match goal with K : u32arr asegs ?mx (X + ?d) _ |- context [MS _ _ _ _ _ ?mx _] => replace (X + d) with (X + 4 * (an + bn)) in K by (clear; lia) end.
    match goal with K : munch [(X, X + ?d); _] m ?mx |- _ => replace (X + d) with (X + 4 * (an + bn)) in K by (clear; lia) end.
    lazymatch goal with K : munch ?Wm m ?mx |- context [MS _ _ _ _ _ ?my _] =>
      assert (WCL : w_client (hcs asegs R HIA h) Wm)
        by (apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]; cbn [fst snd];
            [ replace (X + 4 * (an + bn) - X) with (4 * (an + bn)) by (clear; lia); eapply aobj_crange; exact OX | exact SCS ]);
      pose proof (aobj_munch asegs (arl_AL R) (hcs asegs R HIA h) CSOK Wm m mx X (4 * (an + bn)) WCL K OX) as OX';
      pose proof (aobj_munch asegs (arl_AL R) (hcs asegs R HIA h) CSOK Wm m mx A (4 * an) WCL K OA) as OA';
      pose proof (aobj_munch asegs (arl_AL R) (hcs asegs R HIA h) CSOK Wm m mx B (4 * bn) WCL K OB) as OB' end.
    lazymatch goal with K : u32arr asegs ?mx X ?l |- context [MS _ _ _ _ _ ?my _] =>
    lazymatch goal with KL : Z.of_nat (length l) = _ |- _ =>
    eapply (loop_walk R HIA IMG AMS NEED0 h LB LF) with (k := Z.to_nat bn) (i := 0) (lx := Z.of_nat (length xs)) (la := Z.of_nat (length ys)) (lb := Z.of_nat (length zs)) (xs0 := xs) (xs := l);
      [ .. | split; [exact K|]; split; [clear - KL LP; klia| split; [eassumption | split; [eassumption | split; [eassumption| split; [eassumption| split; [eassumption|eassumption]]]]]]
        | first [eassumption | lx_rw_sub] | exact OX' | exact OA' | exact OB' ] end end.
    all: try eassumption; try klia; try (f_equal; klia).
    all: match goal with |- ?g => idtac "MAIN-LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
