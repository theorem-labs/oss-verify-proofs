(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts CrtParseStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oid P_asn1_get_mpi P_x509_get_hash_alg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_rt_facts A_alloc_lib A_crt_parse_stmts A_pkcs7_cinfo A_asn1_get_tag_stmt A_asn1_get_tag A_oid A_mpi_stmtA A_x509_seq_stmts A_asn1_trav.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_get_san_A.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P000b1f4352652af1 0 8 0 1 55 1 62 1 64 1 65 1 66 1 73 1 74 1P00383dc36636cca7 0 8 1 1 56 1 63 1 65 1 66 1 67 1 74 1 75 1P008ecf2c45d0d632 1 1 16 3 1 1 45 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P00a49443c627e2b1 0 7 0 1 55 1 64 1 65 1 66 1 73 1 74 1P00b64dc6e29781e0 0 9 0 1 6 1 41 1 55 1 64 1 65 1 66 1 73 1 74 1P00d55efb2b4bb5c2 1 1 16 3 0 1 94 1 95 1 4 56 1 93 1 96 1 97 16P01c9f4ff6c57161b 0 8 0 1 55 1 62 1 64 1 65 1 66 1 73 1 74 1P032dbf533a62f7d7 0 9 0 1 55 1 56 1 57 1 64 1 65 1 66 1 73 1 74 1P0358fcaa6e93f270 0 8 1 1 56 1 63 1 65 1 66 1 67 1 74 1 75 1P0384542b35737968 0 9 1 1 37 1 76 1 79 1 85 1 86 1 87 1 94 1 95 1P03d13c92a28507cf 1 1 16 3 0 1 94 1 95 1 8 41 4 75 4 84 4 85 4 86 4 93 4 96 4 97 64P0428ddfc384a6863 0 4 0 1 54 1 73 1 74 1P04453c8ff3b855ae 1 1 16 3 1 1 45 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P0456e357a2f0d5d0 1 1 16 4 1 1 38 1 47 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P0471facb17fb26c9 0 8 1 1 56 1 63 1 65 1 66 1 67 1 74 1 75 1P04d02e919d6760ad 0 10 0 1 36 1 75 1 76 1 77 1 84 1 85 1 86 1 93 1 94 1P04d92fd2f9d92613 1 1 16 3 1 1 45 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P04dd05700cfc9646 0 8 2 1 43 1 57 1 66 1 67 1 68 1 75 1 76 1P04dece8752f7a69e 1 2 16 3 1 1 45 1 74 1 16 3 0 1 46 1 75 1 2 76 1 77 1P052ce2c0b4ea3c14 0 8 1 1 56 1 59 1 65 1 66 1 67 1 74 1 75 1P05730c3a052810df 0 9 0 1 6 1 41 1 55 1 64 1 65 1 66 1 73 1 74 1P05ea4e92f61c76c3 1 2 32 3 0 1 93 1 96 1 32 11 36 1 42 1 63 1 75 1 76 1 77 1 84 1 85 1 86 1 94 1 95 1 2 97 2 98 2P05faf7f3d0c02770 0 8 1 1 56 1 59 1 65 1 66 1 67 1 74 1 75 1P0631fe216003571f 0 8 2 1 43 1 57 1 66 1 67 1 68 1 75 1 76 1P065e0397b3e71c58 1 1 16 4 1 1 38 1 47 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P0698d02c841a4d6c 1 2 32 3 0 1 93 1 96 1 32 11 36 1 42 1 63 1 75 1 76 1 77 1 84 1 85 1 86 1 94 1 95 1 2 97 2 98 2P071b93f3446b2323 0 4 0 1 54 1 73 1 74 1P07422e24b9fee23e 0 9 0 1 6 1 41 1 55 1 64 1 65 1 66 1 73 1 74 1P079c21cb18d542e8 0 8 0 1 55 1 58 1 64 1 65 1 66 1 73 1 74 1P08db33bbe16a7c5b 0 6 0 1 34 1 56 1 74 1 93 1 94 1P0904b08ca5d1f5be 0 8 0 1 55 1 62 1 64 1 65 1 66 1 73 1 74 1P0932ceb1509fe39e 1 1 16 2 1 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P0952218ff851a9d0 1 1 16 3 0 1 95 1 96 1 8 42 4 76 4 85 4 86 4 87 4 94 4 97 4 98 64P0956a58c125e5e84 0 8 0 1 55 1 58 1 64 1 65 1 66 1 73 1 74 1P0a020af7970d2a26 0 9 1 1 37 1 76 1 83 1 85 1 86 1 87 1 94 1 95 1P0a32f9737a49a31f 0 8 1 1 56 1 59 1 65 1 66 1 67 1 74 1 75 1P0a75445bd5764dcb 0 8 2 1 43 1 57 1 66 1 67 1 68 1 75 1 76 1P0af95094b000bc1b 0 8 1 1 56 1 59 1 65 1 66 1 67 1 74 1 75 1P0b19e7102cc9a11f 0 12 2 1 38 1 65 1 74 1 77 1 78 1 79 1 86 1 87 1 88 1 95 1 96 1P0b24cf66551136f7 1 2 32 3 0 1 94 1 97 1 32 11 37 1 43 1 64 1 76 1 77 1 78 1 85 1 86 1 87 1 95 1 96 1 2 98 2 99 2P0bbce7670eed22d0 1 1 16 3 0 1 95 1 96 1 8 42 4 76 4 85 4 86 4 87 4 94 4 97 4 98 64P0c748ccf8e07e26f 0 8 2 1 43 1 57 1 66 1 67 1 68 1 75 1 76 1P0cbbc4c13ee183e4 0 9 0 1 55 1 56 1 57 1 64 1 65 1 66 1 73 1 74 1P0cd0684d27915c57 1 2 32 3 0 1 95 1 96 1 32 3 1 1 94 1 97 1 2 98 2 99 2P0cd806d8c136feb0 0 8 0 1 36 1 75 1 84 1 85 1 86 1 93 1 94 1P0d5525c3869ef254 0 7 0 1 55 1 64 1 65 1 66 1 73 1 74 1P0d771b99a38b1229 0 8 0 1 55 1 62 1 64 1 65 1 66 1 73 1 74 1P0d7ac6f7105e879e 1 2 32 3 0 1 93 1 96 1 32 11 36 1 42 1 63 1 75 1 76 1 77 1 84 1 85 1 86 1 94 1 95 1 2 97 2 98 2P0d7f546580618a43 0 8 1 1 56 1 63 1 65 1 66 1 67 1 74 1 75 1P0e0c978db0548e47 1 2 32 3 0 1 93 1 96 1 32 11 36 1 42 1 63 1 75 1 76 1 77 1 84 1 85 1 86 1 94 1 95 1 2 97 2 98 2P0e257c43a84300b3 0 8 1 1 56 1 59 1 65 1 66 1 67 1 74 1 75 1P0e35a0825e64a490 0 9 0 1 6 1 41 1 55 1 64 1 65 1 66 1 73 1 74 1P0e3be0f7cc0171e0 0 4 0 1 54 1 73 1 74 1P0f375e730fdf7072 0 4 0 1 54 1 73 1 74 1P0fe8b4f73b1fe455 0 8 0 1 36 1 75 1 84 1 85 1 86 1 93 1 94 1P1119efa91137eb8f 0 6 0 1 53 1 56 1 74 1 93 1 94 1P119f35189131ae38 0 8 2 1 43 1 57 1 66 1 67 1 68 1 75 1 76 1P11ba12d55716c848 1 1 16 3 0 1 95 1 96 1 4 57 1 94 1 97 1 98 16P11d12e0dcfa1ec23 0 8 2 1 43 1 57 1 66 1 67 1 68 1 75 1 76 1P1278c3272197f17c 0 8 1 1 56 1 63 1 65 1 66 1 67 1 74 1 75 1P12a8ade2eb199160 1 2 16 2 0 1 75 1 16 2 1 1 74 1 2 76 1 77 1P12d54a24dcae7ce6 0 8 2 1 43 1 57 1 66 1 67 1 68 1 75 1 76 1P12e64472d19fc8e3 1 1 16 3 1 1 45 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P1308fc53d763af34 0 8 0 1 55 1 58 1 64 1 65 1 66 1 73 1 74 1P130d5944d6535968 0 8 2 1 43 1 57 1 66 1 67 1 68 1 75 1 76 1P135e15ede8466cba 0 9 0 1 6 1 41 1 55 1 64 1 65 1 66 1 73 1 74 1P138849e2e392aea7 0 8 0 1 55 1 62 1 64 1 65 1 66 1 73 1 74 1P145c9192ca6e68f9 0 6 0 1 34 1 56 1 74 1 93 1 94 1P149499c874b721fd 0 8 0 1 55 1 58 1 64 1 65 1 66 1 73 1 74 1P14cc0fc3abcd52b0 0 9 1 1 37 1 76 1 83 1 85 1 86 1 87 1 94 1 95 1P14decfc5684b930d 1 2 32 3 0 1 95 1 96 1 32 3 1 1 94 1 97 1 2 98 2 99 2P14efecdb080f0ce9 0 9 0 1 36 1 75 1 82 1 84 1 85 1 86 1 93 1 94 1P152f3bd9562f1e47 0 5 0 1 35 1 54 1 73 1 74 1P15444e5cc7d54f41 0 8 0 1 55 1 58 1 64 1 65 1 66 1 73 1 74 1P1579b5fcf94e9327 1 1 16 2 1 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P15d9750bbee573b0 0 5 0 1 35 1 54 1 73 1 74 1P16129edf44ddf6f6 0 9 0 1 55 1 56 1 57 1 64 1 65 1 66 1 73 1 74 1P162de4de2df62a6d 0 8 0 1 55 1 62 1 64 1 65 1 66 1 73 1 74 1P1663034e6d0e378a 0 8 0 1 55 1 58 1 64 1 65 1 66 1 73 1 74 1P166622b9a13f2f2a 1 1 16 4 1 1 38 1 47 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P169fdafde3c17fd1 1 1 16 4 1 1 38 1 47 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P16fcca30b1e5afc3 1 1 16 3 1 1 45 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P172b1434b671bfd5 1 2 32 3 1 1 94 1 97 1 32 11 37 1 43 1 64 1 76 1 77 1 78 1 85 1 86 1 87 1 95 1 96 1 2 98 2 99 2P17754f0ae79c4459 0 9 0 1 55 1 56 1 57 1 64 1 65 1 66 1 73 1 74 1P1799c4e53cad4139 0 8 1 1 56 1 63 1 65 1 66 1 67 1 74 1 75 1P17a3a07545ca3f35 0 8 1 1 56 1 63 1 65 1 66 1 67 1 74 1 75 1P17f2e67995ad450a 0 8 2 1 43 1 57 1 66 1 67 1 68 1 75 1 76 1P17f513ad35064ee4 0 7 0 1 55 1 64 1 65 1 66 1 73 1 74 1P1805970a1b1b35ea 0 8 1 1 56 1 63 1 65 1 66 1 67 1 74 1 75 1P18192d442848b76e 0 4 0 1 54 1 73 1 74 1P1856de04eaf46ca6 0 8 0 1 55 1 62 1 64 1 65 1 66 1 73 1 74 1P187241b12cc9ab65 0 8 0 1 55 1 58 1 64 1 65 1 66 1 73 1 74 1P189870238156962e 1 1 16 4 1 1 38 1 47 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P192c0d095749e5ae 1 1 16 4 1 1 38 1 47 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P193c03c4739f94ca 1 1 16 2 1 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P19e944bc349858d2 0 4 0 1 54 1 73 1 74 1P19edd65c27ced0a9 1 1 16 3 1 1 45 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P19f355fbeb37f5a9 0 9 0 1 36 1 75 1 78 1 84 1 85 1 86 1 93 1 94 1P1a335dee2a918ac6 0 9 0 1 6 1 41 1 55 1 64 1 65 1 66 1 73 1 74 1P1a720df02c20fb43 0 9 0 1 55 1 56 1 57 1 64 1 65 1 66 1 73 1 74 1P1a7943d8f00aa170 0 9 0 1 36 1 75 1 78 1 84 1 85 1 86 1 93 1 94 1P1a8284f3afbfcdc3 0 8 1 1 56 1 59 1 65 1 66 1 67 1 74 1 75 1P1aa2cc4a16a2f4c4 0 7 0 1 55 1 64 1 65 1 66 1 73 1 74 1P1b2ad123f7fd3065 0 8 0 1 55 1 58 1 64 1 65 1 66 1 73 1 74 1P1b607729fd5d67fc 1 2 32 3 0 1 93 1 96 1 32 11 36 1 42 1 63 1 75 1 76 1 77 1 84 1 85 1 86 1 94 1 95 1 2 97 2 98 2P1b9c0b2f0aefc2b7 0 8 2 1 43 1 57 1 66 1 67 1 68 1 75 1 76 1P1ba2be88b2e55a5f 1 2 32 3 0 1 93 1 96 1 32 11 36 1 42 1 63 1 75 1 76 1 77 1 84 1 85 1 86 1 94 1 95 1 2 97 2 98 2P1c1ff6dc8d8f876c 0 8 0 1 36 1 75 1 84 1 85 1 86 1 93 1 94 1P1c89aee2d6ddbc82 0 8 0 1 55 1 62 1 64 1 65 1 66 1 73 1 74 1P1ca53e8480842d51 0 8 2 1 43 1 57 1 66 1 67 1 68 1 75 1 76 1P1d3a4566e02cbb17 1 1 16 3 0 1 95 1 96 1 8 42 4 76 4 85 4 86 4 87 4 94 4 97 4 98 64P1dd18b2441c859c1 1 1 16 4 1 1 38 1 47 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P1e0e3b385626cd24 1 1 16 2 1 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P1e637f483e619df8 0 7 0 1 55 1 64 1 65 1 66 1 73 1 74 1P1e7f84f7c5cf7a4d 0 9 1 1 37 1 76 1 83 1 85 1 86 1 87 1 94 1 95 1P1e802a2c839ffc50 0 4 0 1 54 1 73 1 74 1P1f0f35dfe1969205 0 8 2 1 43 1 57 1 66 1 67 1 68 1 75 1 76 1P1f9f928b64be8dbe 0 8 0 1 55 1 58 1 64 1 65 1 66 1 73 1 74 1P1fb86118b5f75d88 0 5 0 1 35 1 54 1 73 1 74 1P1fe7bc7d5e59e8e6 1 2 16 2 0 1 75 1 16 2 1 1 74 1 2 76 1 77 1P2030e91b2bf74b1e 1 2 32 3 0 1 95 1 96 1 32 3 1 1 94 1 97 1 2 98 2 99 2P2055ea20b9d085f3 1 2 16 2 0 1 75 1 16 2 1 1 74 1 2 76 1 77 1P2064b6677d88a916 0 7 0 1 55 1 64 1 65 1 66 1 73 1 74 1P207860d6bc4109bc 0 9 0 1 6 1 41 1 55 1 64 1 65 1 66 1 73 1 74 1P20a283148217f945 1 1 16 4 1 1 38 1 47 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P20ad8afe11f4d15b 0 9 0 1 6 1 41 1 55 1 64 1 65 1 66 1 73 1 74 1P20b60b5449c0e1b4 0 4 0 1 54 1 73 1 74 1P21929ca21fb972e9 1 1 16 3 0 1 95 1 96 1 4 57 1 94 1 97 1 98 16P21fe380002b869dc 0 8 0 1 55 1 58 1 64 1 65 1 66 1 73 1 74 1P222c3b9cde76fdbc 1 2 16 2 0 1 75 1 16 2 1 1 74 1 2 76 1 77 1P2246f739ceea7980 0 6 0 1 53 1 56 1 74 1 93 1 94 1P229ca5283cdfb4e3 0 7 0 1 55 1 64 1 65 1 66 1 73 1 74 1P22a5cedf1f2439ca 0 8 2 1 43 1 57 1 66 1 67 1 68 1 75 1 76 1P22c9006a51f055a9 0 9 0 1 55 1 56 1 57 1 64 1 65 1 66 1 73 1 74 1P22ce156b47c2a346 1 1 16 3 0 1 95 1 96 1 4 57 1 94 1 97 1 98 16P22dd94acdb53043d 1 1 16 3 1 1 45 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P2392d75e8ad7b574 0 3 0 1 40 1 55 1P23bc83b12d52c42b 0 7 0 1 55 1 64 1 65 1 66 1 73 1 74 1P23d2b6daea3fa4d9 0 8 1 1 56 1 63 1 65 1 66 1 67 1 74 1 75 1P240cf221299b5b17 0 9 0 1 36 1 75 1 78 1 84 1 85 1 86 1 93 1 94 1P2484a36708b1493e 1 2 32 3 1 1 94 1 97 1 32 11 37 1 43 1 64 1 76 1 77 1 78 1 85 1 86 1 87 1 95 1 96 1 2 98 2 99 2P2491fcbffa437b88 0 5 0 1 35 1 54 1 73 1 74 1P24a06098eae472a3 0 4 0 1 54 1 73 1 74 1P24f3e31f0d91ef73 0 10 0 1 36 1 75 1 76 1 77 1 84 1 85 1 86 1 93 1 94 1P251d3f2d70801ba9 1 1 16 2 1 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P254a4dcf09c96dde 0 9 0 1 6 1 41 1 55 1 64 1 65 1 66 1 73 1 74 1P2603f9a72330f5ad 0 13 0 1 9 1 36 1 63 1 72 1 75 1 76 1 77 1 84 1 85 1 86 1 93 1 94 1P26320874b5c00ab7 0 9 0 1 55 1 56 1 57 1 64 1 65 1 66 1 73 1 74 1P26792f3fc1ff15e6 0 9 0 1 6 1 41 1 55 1 64 1 65 1 66 1 73 1 74 1P26a92be22c641922 1 2 16 3 1 1 45 1 74 1 16 3 0 1 46 1 75 1 2 76 1 77 1P26cd1d00c3e32037 1 2 16 2 0 1 75 1 16 2 1 1 74 1 2 76 1 77 1P273d0044fde866ee 0 7 0 1 55 1 64 1 65 1 66 1 73 1 74 1P2774fce6d8867bea 0 6 0 1 34 1 56 1 74 1 93 1 94 1P27fbfa64dea3c7f4 0 4 0 1 54 1 73 1 74 1P2824878132190abd 0 9 0 1 55 1 56 1 57 1 64 1 65 1 66 1 73 1 74 1P2851f779b738dfae 1 2 32 3 0 1 94 1 97 1 32 11 37 1 43 1 64 1 76 1 77 1 78 1 85 1 86 1 87 1 95 1 96 1 2 98 2 99 2P28aed399dbe3fa65 0 4 0 1 54 1 73 1 74 1P28b1a7daf772043b 1 1 16 4 1 1 38 1 47 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P28c5b2b1a3b33833 1 2 16 3 1 1 45 1 74 1 16 3 0 1 46 1 75 1 2 76 1 77 1P28fc6c4a8fc00367 0 9 0 1 55 1 56 1 57 1 64 1 65 1 66 1 73 1 74 1P2949d6b99c63e2e6 0 8 0 1 36 1 75 1 84 1 85 1 86 1 93 1 94 1P296968c1c8922303 0 5 0 1 35 1 54 1 73 1 74 1P299b36452e28859b 0 9 0 1 55 1 56 1 57 1 64 1 65 1 66 1 73 1 74 1P29ba2327d6570c0c 1 1 16 2 1 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P29cef2162958821d 0 9 0 1 6 1 41 1 55 1 64 1 65 1 66 1 73 1 74 1P29d36982bfeef9c7 1 1 16 2 1 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P29f2b8a84f031a71 1 2 32 3 0 1 94 1 97 1 32 11 37 1 43 1 64 1 76 1 77 1 78 1 85 1 86 1 87 1 95 1 96 1 2 98 2 99 2P2a10f156423a3bf0 0 12 2 1 38 1 65 1 74 1 77 1 78 1 79 1 86 1 87 1 88 1 95 1 96 1P2a9a320b7b776b4c 0 8 0 1 55 1 62 1 64 1 65 1 66 1 73 1 74 1P2ab97c68c68f3827 0 8 0 1 55 1 58 1 64 1 65 1 66 1 73 1 74 1P2acc71ba8519c1c4 0 9 1 1 37 1 76 1 79 1 85 1 86 1 87 1 94 1 95 1P2b0fcfd4d1cb7feb 0 8 0 1 55 1 58 1 64 1 65 1 66 1 73 1 74 1P2b1c5a86ffd92c98 1 2 32 3 1 1 94 1 97 1 32 11 37 1 43 1 64 1 76 1 77 1 78 1 85 1 86 1 87 1 95 1 96 1 2 98 2 99 2P2b40a85a577c00a9 1 1 16 4 1 1 38 1 47 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P2b51df33a443b36c 0 5 0 1 35 1 54 1 73 1 74 1P2c9396b8ff42542a 1 2 16 3 1 1 45 1 74 1 16 3 0 1 46 1 75 1 2 76 1 77 1P2d1d18156c827dfa 0 4 0 1 54 1 73 1 74 1P2d7d02985d6ce290 0 8 1 1 56 1 59 1 65 1 66 1 67 1 74 1 75 1P2d82d5b4666ccb9c 1 1 16 4 1 1 38 1 47 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P2d8d204aa34046dd 1 1 16 4 1 1 38 1 47 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P2e638e4714b49633 0 9 0 1 55 1 56 1 57 1 64 1 65 1 66 1 73 1 74 1P2ea8b4a2dfa60742 1 1 16 2 0 1 73 1 3 11 1 74 1 75 16P2eb3ed926a83b11e 0 8 0 1 55 1 58 1 64 1 65 1 66 1 73 1 74 1P2ecbb70f7253c3cf 0 8 1 1 56 1 63 1 65 1 66 1 67 1 74 1 75 1P2ed519baffa8a476 1 2 16 3 1 1 45 1 74 1 16 3 0 1 46 1 75 1 2 76 1 77 1P2f1584e71a18ed2d 0 8 1 1 56 1 63 1 65 1 66 1 67 1 74 1 75 1P2f1931b5909c9530 0 10 0 1 36 1 75 1 76 1 77 1 84 1 85 1 86 1 93 1 94 1P2f8bd2bda310a168 0 5 0 1 35 1 54 1 73 1 74 1P2fb3a8db55abf292 1 1 16 4 1 1 38 1 47 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P2fc3a5f8181c953c 0 5 0 1 35 1 54 1 73 1 74 1P2ff3e458c1fbb61d 0 7 0 1 75 1 84 1 85 1 86 1 93 1 94 1P2ff9a5d68efcba07 0 8 1 1 56 1 59 1 65 1 66 1 67 1 74 1 75 1P301c9f036a161169 0 5 0 1 35 1 54 1 73 1 74 1P301ccbfadfae3ed4 0 9 0 1 55 1 56 1 57 1 64 1 65 1 66 1 73 1 74 1P3058afd105002d4e 1 1 64 2 0 1 93 1 3 16 1 94 1 95 64P30701cc6ea40009e 0 8 1 1 56 1 59 1 65 1 66 1 67 1 74 1 75 1P314834d2e46f5741 0 12 2 1 38 1 65 1 74 1 77 1 78 1 79 1 86 1 87 1 88 1 95 1 96 1P31d356eea16a6613 0 4 0 1 54 1 73 1 74 1P31f3cc19c85d299c 1 1 16 3 0 1 94 1 95 1 4 56 1 93 1 96 1 97 16P320ab9d185cdc343 0 8 1 1 56 1 59 1 65 1 66 1 67 1 74 1 75 1P323f32a3a1eb6c68 0 5 0 1 35 1 54 1 73 1 74 1P3392b03a2f867475 0 4 0 1 54 1 73 1 74 1P340330dbe1a23f9a 0 13 0 1 9 1 36 1 63 1 72 1 75 1 76 1 77 1 84 1 85 1 86 1 93 1 94 1P34514a571fb07a58 1 1 64 2 15 1 93 1 3 0 1 94 1 95 64P345e01d062404051 0 6 0 1 53 1 56 1 74 1 93 1 94 1P345f0e1c184c8fb7 0 8 0 1 55 1 58 1 64 1 65 1 66 1 73 1 74 1P349453c43d677656 0 8 1 1 56 1 59 1 65 1 66 1 67 1 74 1 75 1P34c553a803d62978 0 8 1 1 56 1 59 1 65 1 66 1 67 1 74 1 75 1P35053cc2e9055db4 1 1 16 3 0 1 94 1 95 1 4 56 1 93 1 96 1 97 16P3521a336f1586996 0 7 0 1 55 1 64 1 65 1 66 1 73 1 74 1P353a397bc2e5b8f1 0 3 0 1 41 1 58 1P35b02e044d2b7bb2 0 9 0 1 36 1 75 1 82 1 84 1 85 1 86 1 93 1 94 1P35e30c54ab3faf39 1 2 16 2 0 1 75 1 16 2 1 1 74 1 2 76 1 77 1P35e8552584fde464 0 9 0 1 36 1 75 1 82 1 84 1 85 1 86 1 93 1 94 1P36415a5557526a71 0 8 1 1 56 1 63 1 65 1 66 1 67 1 74 1 75 1P3654b8604543f44a 0 7 0 1 55 1 64 1 65 1 66 1 73 1 74 1P36fc2b271512c1fc 0 13 0 1 9 1 36 1 63 1 72 1 75 1 76 1 77 1 84 1 85 1 86 1 93 1 94 1P37fda2bf4b452769 0 9 0 1 6 1 41 1 55 1 64 1 65 1 66 1 73 1 74 1P38103dfab2b0d64a 0 5 0 1 35 1 54 1 73 1 74 1P388234401556ec17 0 7 0 1 55 1 64 1 65 1 66 1 73 1 74 1P3882cd87818b73ec 0 8 0 1 55 1 62 1 64 1 65 1 66 1 73 1 74 1P38ee3aa2c352ce08 0 8 0 1 55 1 62 1 64 1 65 1 66 1 73 1 74 1P38f3405229ed4362 0 8 0 1 55 1 62 1 64 1 65 1 66 1 73 1 74 1P39a125e26879ea47 0 8 1 1 56 1 63 1 65 1 66 1 67 1 74 1 75 1P39bd5b48003ecdde 0 8 1 1 56 1 59 1 65 1 66 1 67 1 74 1 75 1P3b5571aba022c333 0 8 0 1 55 1 62 1 64 1 65 1 66 1 73 1 74 1P3b9cbc3f2dbb7288 0 5 0 1 35 1 54 1 73 1 74 1P3bb52ddf1566fb8a 0 5 0 1 35 1 54 1 73 1 74 1P3bbb823ec835ebee 0 9 1 1 37 1 76 1 79 1 85 1 86 1 87 1 94 1 95 1P3c4793651d494b62 0 8 0 1 55 1 62 1 64 1 65 1 66 1 73 1 74 1P3c89bdbbfd3e6c8a 1 2 16 3 1 1 45 1 74 1 16 3 0 1 46 1 75 1 2 76 1 77 1P3c9ccc03c09f2941 0 8 1 1 56 1 63 1 65 1 66 1 67 1 74 1 75 1P3cce142374ae0827 1 2 16 2 0 1 75 1 16 2 1 1 74 1 2 76 1 77 1P3cf8cac58f97bd4b 1 2 16 3 1 1 45 1 74 1 16 3 0 1 46 1 75 1 2 76 1 77 1P3cfbfd34b2ef1b86 0 9 0 1 55 1 56 1 57 1 64 1 65 1 66 1 73 1 74 1P3d84f55a56fbe164 0 4 0 16 53 16 73 16 74 16P3d874633a45bb413 1 1 16 4 1 1 38 1 47 1 74 1 10 41 1 44 1 56 1 57 1 58 1 65 1 66 1 67 1 75 1 76 16P3dbe642da989beed 0 7 0 1 55 1 64 1 65 1 66 1 73 1 74 1P3eca8ede6f2ced6a 0 5 0 1 35 1 54 1 73 1 74 1P3f013c5f11b84117 0 9 0 1 6 1 41 1 55 1 64 1 65 1 66 1 73 1 74 1P3f12b82362bb2384 0 9 0 1 6 1 41 1 55 1 64 1 65 1 66 1 73 1 74 1P3f23d370791c77d8 0 8 1 1 56 1 59 1 65 1 66 1 67 1 74 1 75 1P3f49bf53dd2460bd 0 8 2 1 43 1 57 1 66 1 67 1 68 1 75 1 76 1P3f51463464ab1eac 0 9 0 1 55 1 56 1 57 1 64 1 65 1 66 1 73 1 74 1P3fe09c1cd484a129 0 7 0 1 55 1 64 1 65 1 66 1 73 1 74 1N00208c3fd116ef38N00faccf12f793b2cN01393ead15bcfc8cN0148c51fedd6ab4fN0227cbd4f6874f42N025eb5405d65cc6bN040aa96ac57bb3faN061789c55cfab779N06a0e2d7a1b934dbN0a73181b24470893N0c04d831e8beadddN0c32a8f90b9fa48eN0d6a5a3d92911624N0d77432a1458cc4eN0d78121959dc8425N0dd1542b30fdf4c0N109c21193a49c0caN10bfdf00c49daec3N110fc0b74e132095N1119fe54b0353a2eN113c22a2fd4a6378N11ba2fe16d1862c5N11f87d06782bd61aN1269703f4a0a9929N12c4001f08beed8aN131246a978328171N14dffb3aa13b482aN16da4f5d34f0dfd3N170db06260b5ca45N17312ef27495fa9eN1755f4621e8af7a8N1853bb2f0b05803aN19000b760bc43b03N194c4e7bd6484ab1N1a2ba7da4e2b59ddN1baad16607775bf8N1bfe0de54593237dN1c4eb9dad3709c3eN1c50b0e569a5d8abN1c88c7a5aafda444N1cc32d5ec48d9307N1d23fe344c70ec35N1d924bae637b293fN1e706d80fcd51c5aN1e867c7236e02219N1ecb854a54ed9363N1f9b053ca3bae7b8N1f9e681ebd1e34c6N20c9babd54d1c150N20fc79eb82126407N23e0886bda816952N241a64c625610610N243cf561bf362062N24c09d1474755770N2502f4daff18635aN26795eb9a7ecafb8N27bebfa5ef24cb1aN281dcd1172944b9dN282ccbd92e82dfa6N285dccc9138aefefN28c1fd1e87eac3ffN29335a06bf9ff38cN2a01f48f1803b9baN2a4093f09a621b1cN2a50cdec8bfa434cN2a618763b1f043c8N2a7dbc84e90907feN2c21ebe883999764N2c58a1c6e992303dN2dadea998854852dN2e962dd1db829077N2e9b8d96ec8ed48cN2ec7ba699eede1b0N2f9581899dca9325N30047e13f3bb213cN3183a77c78995d2eN31e6b5e2d496d7daN323b51478dc335d7N32fac2da605751d0N32fbc21423e5f235N3302aa1bc53b97b2N338654d9df348c45N33cf4bc4f789c953N33f7f7213e0ec5c6N341ca7111f5dd5f1N35f5f76f1cdd3bf5N365f6c64a0ade3c9N36db5d75555ac42dN36f4718b394f9f2eN37693cf6a146252fN3841aa851b7e45e1N390fa80b3dbf9d12N39dfe36b2751752eN3a50c434e4ddbee7N3ab470176e55a248N3b33ac3eb5827033N3b33dc8a1108075eN3d65c4c78afc194eN3d8edd9fd976b40eN3da5d67fe1b9fde7N3eaf0f140994f2caN3ed35d61c2ffcb40N3f595f4c42021b9e"%lxh.
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
Ltac2 gd_tbl_A_x509_policies_A () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HST"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.arl_AL"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.shiftr"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HM"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hcs"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.htop"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hstkhi"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hflag"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.havol"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.hfr"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.iff"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.HK"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.fresh_apart"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Spec.RepFacts.seq_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.presW"; "RocqVerifyHarness.AgentSubmission.LibB.ARt.sshad"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "Walk.Call.S1P"; "A_X509_POLICIES"].


Definition A_X509_POLICIES : Z := 0xab9cc.       (* [comment removed for export] *)

Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM0 : arl_smalloc R 0 = A_SMALLOC_0G.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis NB1 : 0 <= arl_need_bcmp R.
  Hypothesis NEED0 : 0 <= arl_need_malloc R.
  Hypothesis CALLOC : arl_calloc R = 0x69484.
  Hypothesis GT : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG.
  Hypothesis OIDH : oid_rt_hyps R HIA.

  (* [comment removed for export] *)
  Definition STKpol : Z := 240 + 48 + arl_need_smalloc R + arl_need_bcmp R + arl_need_malloc R.

  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP CUR P END BUF lo slo : Z) (bs : list byte) (ct cpad : word).
  Local Notation n := (Z.of_nat (length bs)).
  Hypothesis LFB : (length LF < 511)%nat.
  Hypothesis ALP : PP mod 8 = 0.
  Hypothesis PP0 : 0 < PP.
  Hypothesis CWP : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) PP 8.
  Hypothesis PPLO : PP + 8 <= lo.
  Hypothesis BIN : In (BUF, n) LB.
  Hypothesis B1 : BUF <= P. Hypothesis B2 : P <= END. Hypothesis B3 : END <= BUF + n. Hypothesis B47 : BUF + n < 2^47. Hypothesis B5 : 0 < BUF.
  Hypothesis DPB : PP + 8 <= BUF \/ BUF + n <= PP.
  Hypothesis ALC : CUR mod 8 = 0.
  Hypothesis CUR0 : 0 < CUR.
  Hypothesis CWC : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) CUR 32.
  Hypothesis CURLO : CUR + 32 <= lo.
  Hypothesis DCB : CUR + 32 <= BUF \/ BUF + n <= CUR.
  Hypothesis D1 : PP + 8 <= CUR \/ CUR + 32 <= PP.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKpol.
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
    unfold A_UAR_GOT in UARG; unfold A_SMALLOC_0G in SM0; unfold STKpol in SLO;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  Local Notation W := [(PP, PP + 8); (CUR, CUR + 32)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Ltac spine := lazymatch goal with |- _ /\ _ => split; [| spine] | _ => idtac end.

  Local Notation FSHG := [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
                          C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243)].

  (* [comment removed for export] *)
  Definition S1P : machine_state -> Prop :=
    fun ms => exists (FB sp1 : Z) (h1 : HST asegs R HIA) (m1 : mem)
      (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 w0 w1 w2 lenj : word) (ja jb : list byte),
      ms = MS (mkR (Z_to_bv 64 0xaba48) (Z_to_bv 64 sp1) gp tp x5 x6 x7 sp (Z_to_bv 64 sp1) x10 x11 x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 FB) (Z_to_bv 64 END) (Z_to_bv 64 PP) (Z_to_bv 64 CUR) (Z_to_bv 64 (FB + 32))
                   (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 (al_sb AL)) s9 s10 (Z_to_bv 64 FB) x28 x29 x30 x31)
              F (Z_to_bv 64 0xabae0) fc None m1 (seg_rom asegs) /\
      bv_unsigned sp - 208 <= sp1 <= bv_unsigned sp - 192 /\
      sp1 mod 32 = 0 /\
      HM asegs R HIA h1 LB ((FB, 64) :: LF) m1 /\
      hcs asegs R HIA h1 = hcs asegs R HIA h /\
      htop asegs R HIA h1 = htop asegs R HIA h /\
      hstkhi asegs R HIA h1 = hstkhi asegs R HIA h /\
      hflag asegs R HIA h1 = hflag asegs R HIA h /\
      havol asegs R HIA h1 = havol asegs R HIA h /\
      hfr asegs R HIA h1 = hfr asegs R HIA h /\
      (forall mo : Model, HK asegs R HIA h1 mo <-> HK asegs R HIA h mo) /\
      FB mod 64 = 0 /\
      fresh_apart R LB LF FB 64 /\
      rw_cells asegs m1 FB [C8 w0; C8 w1; C8 w2] /\
      rw_cells asegs m1 (FB + 32) [C8 lenj] /\
      rw_cells asegs m1 (Z.shiftr FB 3 + al_sb AL) FSHG /\
      rw_cells asegs m1 (bv_unsigned sp + -104) SAVEL /\
      rw_cells asegs m1 sp1 [CB 56 ja; C8 (Z_to_bv 64 (al_sb AL)); CB 16 jb; C8 (Z_to_bv 64 FB)] /\
      stk asegs m1 (sp1 + 88) (bv_unsigned sp + -104) /\
      stk asegs m1 lo sp1 /\
      mem_inv asegs m1 /\
      rw_cells asegs m1 PP [C8 (Z_to_bv 64 P)] /\
      rw_cells asegs m1 CUR (seq_cells ct cpad 0 0 0) /\
      bytes_at asegs m1 BUF bs /\
      aobj asegs AL CS m1 PP 8 /\
      aobj asegs AL CS m1 CUR 32 /\
      aobj asegs AL CS m1 BUF n /\
      (FB + 64 <= PP \/ PP + 8 <= FB) /\
      (FB + 64 <= CUR \/ CUR + 32 <= FB) /\
      presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) W m m1 /\
      sshad asegs AL m1 slo sp1 /\
      sshad asegs AL m1 sp1 (bv_unsigned sp)
(* [comment removed for export] *).

  Ltac cb8_at H i :=
    lazymatch type of H with rw_cells _ _ _ ?cs => let pre := eval cbv beta iota delta [firstn] in (firstn i cs) in cb8_to_c8 H pre end.

  (* [comment removed for export] *)
  #[local] Ltac lx_pins_hook ::= try lx_pin1 D1; try lx_pin1 ALC; try lx_pin1 B5; try lx_pin1 B2; try lx_pin1 B1; try lx_pin1 ALP; try lx_pin1 OIDH; try lx_pin1 GT; try lx_pin1 CALLOC.   (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "02[0@D10639180168.188D10651765667.111D10823604468.156D12562073422.186D12658639931.110D12660902694.156D14194668100.188D18607476203.157D18607476203.161D20553579080.158D20553579080.159D20553579080.160D22855098056.189D22857195213.112D2455600524.187 D29850139295.189D31526457809.110D31538732778.186D3160262663.188 D32456886359.187D32465422351.189D32467519498.112D3254889317.156 D32606360467.190D33194539134.110D33271012676.186D3385896110.186 D36104740330.188D39411162312.157D39411162312.161D45702186271.186D46793187693.188D46805773126.111D50254960491.158D50254960491.159D50254960491.160D52056129450.161D52461811354.189D54544601417.186D560907437.113  D59043122836.186D60098777666.111D60098977385.186D60109265003.112D60111362153.188D60111362158.189D6192914196.161 D62009673032.190D62011770191.113D62182462905.189D65010535209.187D68409226989.186D6897100008.186 L10116530568.9  L12808385313.0  L17607390846.165L1832968857.12  L19548981083.165L19980016842.12 L2333530698.151 L2333536794.153 L26163319485.151L26163329773.153L28987030758.113L29738741675.1  L31170831509.160L32929385090.139L33485826452.1  L33485826452.13 L35653441506.11 L38692635477.0  L39332637397.0  L39618635427.2  L40228640085.0  L42196131762.9  L42402910215.1  L43055154860.111L43202358967.163L4472687353.165 L45298099350.1  L45363093875.193L48117620904.97 L48119718052.161L48119718055.160L48132302231.114L49130057368.12 L50790731766.11 L5325812058.112 L56380976587.10 L57355539152.166L57355539152.169L58790154276.12 L59308634497.15 L60098763854.6  L61437265048.2  L6302879940.151 L6302890132.153 L67922604617.0  L68343892476.138L6910010082.160 L7040749983.113 L9356559645.16  L9873114841.11  P1056307012.156 P1056307012.161 P51023938008.156P51023938008.161Q10523111609.117Q10594483344.194Q10651763882.119Q10651763890.115Q12660624651.121Q1530342990.161 Q1897072239.156 Q22857195208.116Q22857195211.120Q23216651701.194Q23927511184.117Q23927511196.122Q26032252603.199Q31021924279.156Q31158247845.193Q31158247869.197Q31170831509.195Q32440833928.193Q32467519500.120Q32467519503.116Q32679790552.194Q32681887701.117Q33196749134.121Q33271078526.193Q34966725149.199Q38248895679.123Q40216052035.193Q40271359350.161Q42437284299.145Q42439168719.156Q42441479401.201Q42441479403.124Q43351262911.115Q43351262911.144Q43351262911.193Q43880146019.123Q46805771343.119Q46805771351.115Q47230721788.117Q47313632828.115Q47313632828.144Q47313632828.193Q48119718054.194Q48132302231.193Q50796826103.161Q56533317818.194Q59867617332.124Q59867617334.201Q59871812884.145Q60460432782.116Q60740903729.115Q62011770180.122Q62011770184.117Q64681502658.124Q64685695714.145Q67038703949.156Q67517027822.115Q67517027822.144Q67517027822.193Q6897428426.197 Q6897428434.193 Q6910010082.195 Q8701272495.201 Q9350548487.142 00000Q00b01A01B01T02302402502602702802902[02m02n02o03003103203P04204D04E04l05>05?05@05A05B05C05a06B06S06T06U06V07507607707M07N07e08L08c09J0:10:L0:l0;<0;=0;[0;\0<:0<]0<^0=F0=G0=o0>G0>H0>I0>J0>K0>`0>d0?70?h0?i0?j0@B0@C0@D0@N0@O0A20A60Ao0Bo0CX0C]0D@0Dm0E_0FQ0G>0G?0G^0HH0Ha0Hb0IP0Io0J90JC0JK0JL0JM0JN0Jd0K70KU0LH0M40MS0N20NS0O40OD0OW0Oe0P30PB0P]0Q10Q@0QO0Qb0RA0RT0Rn0SR0Se0T80TK0TL0T[0Tj0Tk0Tl0U;0U<0Un0V<0V=0VU0Vk0WF0Wa0X70X80X90X:0XK0XY0Xg0Y80Y90Y:0Y;0Ym0Z_0[M0[N0[O0[P0[Q0[c0\50\B0\O0]20]U0^K0^L0^M0^N0^a0_40_G0`70`SS2LF2sp2PP2bs3LFB3sp13H224LFB'2FBS2LF2sp2PP2bs3LFBS2LF2sp3BUF2bs3LFB3sp13H224LFB'FS2LF2sp3BUF2bs3LFBS2LF2sp3BUF2bs3LFB3sp13H224LFB'FFFFFFS2LF2sp3CUR2bs3LFB3sp13H224LFB'2FBS2LF2sp3CUR2bs3LFBFFFFFS2LF2sp2bs3LFB3sp13H224LFB'2FBS2LF2sp3CUR2bs3LFB3sp13H224LFB'2FBS2LF2sp3CUR2bs3LFBFS1R3HIA2LF2sp2bs3LFB3sp13H224LFB'2h12FBS2LF2sp3BUF2bs3LFBFFFFFS2LF2sp2bs3LFB3sp13H224LFB'2FBS2LF2sp2PP2bs3LFB3sp13H224LFB'2FBS2LF2sp2PP2bs3LFBFFFS2LF2sp2bs3LFB3sp13H203H224LFB'FFS1R3HIA1h2LF2sp2bs3LFBFS1R2LF2sp2lo2bs3LFB3LOSS1R2LF2sp2lo2bs3LFB3LOS3sp13H224LFB'2FBS1R2LF2sp2lo2bs3LFB3LOSS1R2LF2sp2lo2bs3LFB3LOS3sp13H224LFB'2FBS1R2LF2sp2lo2bs3LFB3LOS3sp13H224LFB'2FBS2LF2sp2bs3LFB3sp13H224LFB'S1R2LF2sp2bs3LFB3sp13H224LFB'2FBS1R2LF2sp2bs3LFBFS2LF2sp2bs3LFB3sp13H224LFB'2FBFS2LF2sp2bs3LFB3sp13H224LFB'2FBS1R3NS13NB15NEED02sp2lo3SLO3sp13SP1SS2LF2sp2bs3LFB3SPR3sp13H224LFB'2FB2F02F8SS2LF2sp2bs3LFB3SPR3sp13H224LFB'2FB2F02F8S1R3HIA1h2sp3TOP3sp13SP1FFFFS2LF2sp2PP3CUR2bs3LFBS2FBS2LF2bs3LFB4LFB'2FBS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3SPR3sp13H22FFS1R3HIA1h2sp2lo3TOP4HTOPSSS3sp14SP1MSS1R3NS13NB15NEED02sp2lo3SLO3sp13SP1S2spS1R3NS13NB15NEED02LF2sp2PP3CUR2lo2bs3LFB3PP04CUR03SLO3SPRS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3ALO3sp13SP14LFB'2FB2F1S1R2LF3slo2bs3LFB4SLOS3ALO3sp14LFB'2FB2F1S3sp1S2LF2sp2bs3LFB3sp13H224LFB'2FB1c2HcS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3ALOS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3ALO4LFB'S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3ALO4LFB'S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3ALOSS1R3NS13NB15NEED02sp2lo3SLO3LOSS2LF2sp2bs3LFB3SPA3SPR3sp13H183H193H203H22S1R3BUF2lo2bs3LOS3BCE3ALOFS1R2LF2sp2bs3LFB3ACV3SPR3sp13H224LFB'2FB2F02F1S1R3NB15NEED02sp2lo3SLO3sp13SP1S2FB2F02KbS1R2lo3LOSS2LF3LFBFFSS2LF2sp2bs3LFB3sp13H22S2LF2bs3LFB4LFB'2FBS2LF2sp2bs3LFB3SPR3sp13H183H22S1R3NS13NB15NEED02sp2lo3SLO3LOS3ALO3ACV3SPR3sp13SP1S1R3NS13NB15NEED02sp2lo3slo4SLOL3SLO3sp13SP1S2LF2PP2lo2bs3LFB4PPLO3sp14LFB'S2LF2PP2lo2bs3LFB4PPLO3sp14LFB'S2LF3CUR2lo2bs3LFB5CURLO3sp14LFB'S2LF3CUR2lo2bs3LFB5CURLO3sp14LFB'S1R2LF2sp2bs3LFBS2LF2bs3LFB4LFB'2FBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS2LF3BUF2bs3LFBS2LF2sp2bs3LFB3sp13H204LFB'S2LF2bs3LFB3sp14LFB'S2LF3CUR2bs3LFBS2LF3CUR2bs3LFBS2LF2bs3LFB4LFB'2FBS1R3HIA1h2LF2sp2bs3LFB3TOP4HTOPS1R3HIA1h2LF2bs3LFBS2LF2sp2lo2bs3LFB3sp14LFB'S1R3HIA1h2LF2sp2bs3LFB3TOP4HTOP4LFB'S2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBFS2LF3CUR2bs3LFBS2LF3CUR2bs3LFBFFS2LF3BUF2bs3LFBFS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3sp13SP14LFB'S2LF2lo2bs3LFBFS1R3HIA1h2LF2bs3LFB4LFB'S1R2LF3slo2bs3LFB4SLOSS1R2LF3slo2bs3LFB4SLOS4LFB'S1R2LF3slo2bs3LFB4SLOS4LFB'S1R2LF3slo2bs3LFB4SLOSFFFS2LF2sp2lo2bs3LFBS2LF2PP2bs3LFBS2LF2PP2bs3LFBS1R2LF2bs3LFB3ALOFFFS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3ALO4LFB'S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3ALO4LFB'S1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS4LFB'FFFFS2LF2PP3CUR2bs3LFBS2LF2PP3CUR2bs3LFBS1R2LF2bs3LFBS1R2LF2bs3LFBS1R3HIA1h2LF2sp3slo2bs3LFB3TOP4HTOPS1R3HIA1h2LF2sp3slo2bs3LFB3TOP4HTOPS1R3NS13NB15NEED02LF2sp2lo2bs3LFB3SLO3LOS3sp13SP14LFB'FFFS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS2LF2bs3LFB4LFB'2FBS1R3HIA1h2LF2sp3slo2bs3LFB3TOP4HTOP3sp13SP14LFB'S2LF2bs3LFB3sp13H213H224LFB'". (* [comment removed for export] *)
  #[using="LOS TPV SPH SPA TOP SLO SLOL SLOS DCB CURLO CWC CUR0 DPB B47 B3 BIN PPLO CWP PP0 LFB NEED0 NB1 NS1 SM0 UARG IMG"]
  Lemma pro_walk : ltac2:(CDefT.buildp (gd_tbl_A_x509_policies_A ()) "Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Pa3,(5.&40.)Pa4,(5.&40.)Pa5,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)P,(17.$4.VR,VHIA,Vh,VLB,VLF,Vm,)P,(25.$4.Vm,VPP,(18.$26.(27.(<.&40.VP,))(28.$26.)))P,(25.$4.Vm,VCUR,(2=.Vct,Vcpad,===))P,(2>.$4.Vm,VBUF,Vbs,)P,(2;.$4.Vm,Vlo,(15.&40.Vsp,))P,(34.$4.(>.VR,)Vm,Vslo,(15.&40.Vsp,))P,(2<.$4.Vm,)P,(2?.$4.(>.VR,)(1;.$4.VR,VHIA,Vh,)Vm,VPP,+8.)P,(2?.$4.(>.VR,)(1;.$4.VR,VHIA,Vh,)Vm,VCUR,+20.)P,(2?.$4.(>.VR,)(1;.$4.VR,VHIA,Vh,)Vm,VBUF,(30.(31.(5.&8.)Vbs,)))(35.$4.(>.VR,)(1;.$4.VR,VHIA,Vh,)$36.(:.(;.Vra,Vsp,Vgp,Vtp,R16.R15.R14.Vs0,Vs1,(<.&40.VPP,)(<.&40.VEND,)(<.&40.VCUR,)R13.R12.R11.R10.R?.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R>.R=.R<.R;.)VF,(<.&40.$37.)Vfc,(11.(5.&40.))Vm,(12.$4.)))")
(* [comment removed for export] *).
  Proof.
  intros until t6.
  intros HH HPP HCUR HBUF ST SS MI OPP OCUR OBUF.
  unfold A_X509_POLICIES.
  unfold seq_cells in HCUR.
  pose proof (blocks_below_hm R HIA h LB LF m LB HH ltac:(intros b Hb; exact Hb)) as BB0.
  destruct (BB0 _ BIN) as [_ BCE].
  cbn [fst snd] in BCE.
  clear BB0.
  assert (BINA : In (BUF, n) (LB ++ fdata LF)) by (apply in_app_iff; left; exact BIN).
  rt_facts.
  assert (BUFLO : BUF + n <= lo) by (clear - BCE ALO LOS; lia).
  pose proof (hm_top asegs R HIA h LB LF _ HH) as HTOP.
  assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 NB1 NEED0 TOP HTOP; lia]).
  pose proof (hm_wlow asegs R HIA h LB LF m HH) as WL.
  pose proof (presW_init asegs R HIA h LB LF m (bv_unsigned sp) (bv_unsigned sp) W HH ltac:(clear - LOS SLO NS1 NB1 NEED0; lia)) as PRES.
  destruct IMG' as (EGOT & ELO & EHI & EGSB).
  carve_frame 192%nat ST.
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
  lx_pre. lx_run_tac (PLAN [0xaba10] [] 311%N). lx_tree.   (* [comment removed for export] *)
  lxr_leaf. lx_carry.
  lx_align32 sp1.
  assert (SP1 : bv_unsigned sp - 208 <= sp1 <= bv_unsigned sp - 192) by (lx_prune; clear_disj; lia).
  assert (SP1M : sp1 mod 32 = 0) by (lx_prune; clear_disj; lia).
  assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 NB1 NEED0; lia).
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m0 end.
  lazymatch goal with FRx : rw_cells _ m0 (bv_unsigned sp + -192) _ |- _ => chunk_split FRx 2%nat FRa SAVE end.
  replace (bv_unsigned sp + -192 + 88) with (bv_unsigned sp + -104) in SAVE by (clear; lia).
  lazymatch goal with STx : stk _ m0 lo (bv_unsigned sp + -192) |- _ => release_frame FRa STx (bv_unsigned sp + -104); rename STx into STJ end.
  destruct (stk_split asegs m0 lo (sp1 + 88) (bv_unsigned sp + -104) STJ ltac:(clear - SP1 SLO NS1 NB1 NEED0; lia)) as [STlo SThi].
  destruct (stk_carve asegs m0 lo (sp1 + 88) 88 STlo ltac:(clear - SP1 SLO NS1 NB1 NEED0; lia)) as [ST1 [jrs RSL]].
  replace (sp1 + 88 - Z.of_nat 88) with sp1 in RSL, ST1 by (clear; lia).
  apply (rw_cells_split_CB asegs m0 sp1 [] 88 jrs [] [56; 8; 16; 8]%nat) in RSL; [| reflexivity].
  cbn [mk_CB_cells app] in RSL.
  cb8_at RSL 1%nat.
  cb8_at RSL 3%nat.
  idtac "T-RSL".
  lxr_pose.
  lx_pre. lx_run_tac (PLAN [0x52ef8] [] 311%N). lx_tree.
  lxr_leaf. lx_carry.
  try clear STJ.
  try clear STlo.
  try clear GOT. try clear GSB. try clear UGOT. try clear UFLAG. try clear AB. try clear FLIMG.
  (* [comment removed for export] *)
  lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m1 end.
      replace (Z_to_bv 64 339704 (* [comment removed for export] *)) with (Z_to_bv 64 (arl_smalloc R 0)) by (rewrite SM0; reflexivity).
      assert (LFB' : (length LF < 512)%nat) by (clear - LFB; lia).
      lazymatch goal with HHc : HM _ _ _ h LB LF m1 |- _ =>
      callrt sp1 (eapply (art_smalloc asegs R HIA 0) with (lo := lo) (sz := 64); rewrite ?(unsigned_lit sp1) by exact SP1R;
                  first [ exact HHc | exact LFB' | reflexivity | exact TPV | exact LOS | exact ST1
                  | clear - SLO SP1 TOP NS1 NB1 NEED0; lia
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
      replace (Z.to_nat (8 * 2 ^ 0)) with 8%nat in FSH by reflexivity.
      replace (Z.to_nat (64 * 2 ^ 0)) with 64%nat in FRM by reflexivity.
      replace (64 * 2 ^ 0) with 64 in FRSH, HH1 by reflexivity.
      cbn [zcells] in FSH.
      idtac "T-SMALLOC".
      (* [comment removed for export] *)
      zstep. zstep.
      zstep. if_cases Kb; zify_cond Kb.
      2:{ exfalso. destruct FRSH as (F0 & F1 & _). try kland Kb.
          rewrite ?Z.mod_small in Kb by (clear - F0 F1 ALO ACV LOS SLO SPR; lia). clear - Kb F0 F1 ALO ACV LOS SLO SPR. lia. }
      clear Kb.
      lazymatch goal with |- _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      destruct (frame_factsA R HIA CS h1 LB LF m3 FB 64 lo HH1 Ehcs FRSH F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
        as (CFB & INF & INH & IND & AP & (F0 & F1 & F2 & F3) & F8 & FBLO & SBND & APS). change (64 / 8) with 8 in SBND, APS.
      pose proof (frame_apart_obj R HIA LB LF lo _ PP 8 FB 64 FRSH CWP ltac:(clear; lia) ltac:(clear; lia) LOS) as APP.
      pose proof (frame_apart_obj R HIA LB LF lo _ CUR 32 FB 64 FRSH CWC ltac:(clear; lia) ltac:(clear; lia) LOS) as APC.
      assert (APB : FB + 64 <= BUF \/ BUF + n <= FB) by (apply F3; apply in_app_iff; left; exact BIN).
      pose proof (art_stk_high asegs R HIA) as STKH.
      (* [comment removed for export] *)
      apply (rw_cells_split_CB asegs m3 FB [] 64 junkf [] [8; 8; 8; 8; 8; 24]%nat) in FRM; [| reflexivity].
      cbn [mk_CB_cells app] in FRM.
      chunk_split FRM 3%nat FHD FRM1. chunk_split FRM1 1%nat FLNK FRM2. chunk_split FRM2 1%nat HLEN FREST.
      lazymatch type of HLEN with rw_cells _ _ ?a _ => replace a with (FB + 32) in HLEN by (clear; lia) end.
      clear FLNK FREST.
      cb8_to_c8 FHD (@nil cell).
      lazymatch type of FHD with rw_cells _ _ _ (?c1 :: _) => cb8_to_c8 FHD [c1] end.
      lazymatch type of FHD with rw_cells _ _ _ (?c1 :: ?c2 :: _) => cb8_to_c8 FHD [c1; c2] end.
      cb8_to_c8 HLEN (@nil cell).
      lazymatch goal with SSx : sshad _ _ m3 slo (bv_unsigned sp) |- _ =>
        destruct (sshad_split asegs AL m3 slo sp1 (bv_unsigned sp) SSx ltac:(clear - SP1 SLO SLOL NS1 NB1 NEED0; lia) ltac:(clear - SP1M; lia)) as [SS1 SS2]; clear SSx end.
  (* [comment removed for export] *)
  lx_mkR. lxr_pose.
  lx_pre. lx_run_tac (PLAN [0xabae0] [] 311%N). lx_tree.
  lxr_leaf. lx_carry.
  lazymatch goal with H : rw_cells _ ?mxc CUR _ |- _ => change (rw_cells asegs mxc CUR (seq_cells ct cpad 0 0 0)) in H end.
      idtac "S1P".
      apply evtA_done. unfold S1P.
      lazymatch goal with |- context [MS _ _ _ _ _ ?mx _] => exists FB, sp1, h1, mx end.
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [reflexivity|]. spine; first [ eassumption | assumption | reflexivity | lx_arith | lx_side_lia | lx_app | match goal with |- ?g => idtac "S1P-LEFT:" g end ].
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Call.
End Walk.
